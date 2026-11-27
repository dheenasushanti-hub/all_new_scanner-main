#!/usr/bin/env python3
"""NIFTY options reference-alert scanner, Python 3.11.

Production entry points implement the existing Cloudflare/GitHub Actions and
state/outbox interfaces. Structure, paired OI, contract quotes and position
management are independent decision stages. Historical market data is never
substituted for a live quote. Regression tests run separately from the scheduled scanner.
"""

from __future__ import annotations
import argparse
import copy
import fcntl
import gzip
import hashlib
import json
import math
import os
import smtplib
import ssl
import sys
import tempfile
import time
from contextlib import contextmanager
from dataclasses import dataclass, asdict, replace
from datetime import datetime, date, timedelta, timezone
from email.message import EmailMessage
from pathlib import Path
from statistics import median
from typing import Any
from urllib.parse import urlencode, quote
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError

VERSION = "139.0.0"
AUDIT_RELEASE = "v139"
IST = timezone(timedelta(hours=5, minutes=30))
INDEX = "NSE_INDEX|Nifty 50"
ALERT_KINDS = frozenset({"ENTRY", "EXIT", "ADJUST_SL", "T1", "T2"})
ENTRY_START = (9, 21)
ENTRY_END = (15, 5)
HARD_EXIT = (15, 15)


class ScannerError(RuntimeError):
    pass


class ProviderError(ScannerError):
    pass


class DataError(ScannerError):
    pass


def finite_json_float(value: Any) -> float:
    f = float(value)
    if not math.isfinite(f):
        raise ValueError("nonfinite value")
    return f


def timestamp(value: Any) -> datetime:
    if isinstance(value, bool) or value is None:
        raise DataError("Invalid timestamp")
    try:
        if isinstance(value, (int, float)) or (isinstance(value, str) and value.isdigit()):
            n = float(value)
            if not math.isfinite(n):
                raise ValueError("nonfinite timestamp")
            dt = datetime.fromtimestamp(n / 1000 if n > 1e11 else n, timezone.utc)
        else:
            dt = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
        if dt.tzinfo is None:
            raise ValueError("timezone absent")
        return dt.astimezone(IST)
    except (ValueError, OverflowError, TypeError) as exc:
        raise DataError("Invalid timestamp") from exc


def read_number(value: Any, name: str, *, positive=False, nonnegative=False) -> float:
    if isinstance(value, bool):
        raise DataError("Boolean numeric field " + name)
    try:
        n = float(value)
    except (ValueError, TypeError) as exc:
        raise DataError("Invalid numeric field " + name) from exc
    if not math.isfinite(n) or (positive and n <= 0) or (nonnegative and n < 0):
        raise DataError("Nonfinite/out of range " + name)
    return n


@dataclass(frozen=True)
class Candle:
    start: datetime
    open: float
    high: float
    low: float
    close: float
    volume: float = 0.0

    def __post_init__(self):
        if self.start.tzinfo is None or self.start.second or self.start.microsecond:
            raise DataError("Candle start must be timezone-aware, minute aligned")
        values = (self.open, self.high, self.low, self.close, self.volume)
        if not all(math.isfinite(x) for x in values) or min(values[:4]) <= 0 or self.volume < 0:
            raise DataError("Invalid OHLCV")
        if (
            self.low > min(self.open, self.close)
            or self.high < max(self.open, self.close)
            or self.high < self.low
        ):
            raise DataError("Impossible OHLC")


def day_time(now: datetime, hour: int, minute: int) -> datetime:
    return now.astimezone(IST).replace(hour=hour, minute=minute, second=0, microsecond=0)


def exact_minute(now: datetime) -> datetime:
    return now.astimezone(IST).replace(second=0, microsecond=0)


def serialize_bar(c: Candle) -> list[Any]:
    return [c.start.isoformat(), c.open, c.high, c.low, c.close, c.volume]


def parse_candles(raw: list, now: datetime) -> list[Candle]:
    """Drop uncompleted bars; refuse inconsistent duplicates, duplicates do not shadow data."""
    if not isinstance(raw, list):
        raise DataError("Candle payload must be list")
    unique: dict[datetime, Candle] = {}
    for row in raw:
        try:
            if not isinstance(row, (list, tuple)) or len(row) < 5:
                raise DataError("Malformed candle row")
            start = timestamp(row[0])
            if start.second or start.microsecond:
                raise DataError("Unaligned candle")
            if start + timedelta(minutes=1) > now - timedelta(seconds=1):
                continue
            c = Candle(
                start,
                *(read_number(row[i], f"candle_{i}", positive=True) for i in range(1, 5)),
                read_number(row[5], "volume", nonnegative=True) if len(row) > 5 else 0.0,
            )
        except (DataError, TypeError) as exc:
            raise DataError("Invalid OHLC row") from exc
        if c.start in unique and c != unique[c.start]:
            raise DataError("Conflicting duplicate candles")
        unique[c.start] = c
    ordered = sorted(unique.values(), key=lambda c: c.start)
    if not ordered:
        raise DataError("No completed candles")
    return ordered


def contiguous_tail(bars: list[Candle]) -> list[Candle]:
    if not bars:
        return []
    start = len(bars) - 1
    while start and bars[start].start - bars[start - 1].start == timedelta(minutes=1):
        start -= 1
    return bars[start:]


def volatility(bars: list[Candle], n=14, minimum=3.0) -> float:
    window = bars[-(n + 1) :]
    if not window:
        return minimum
    if len(window) == 1:
        return max(minimum, window[0].high - window[0].low)
    tr = [
        max(b.high - b.low, abs(b.high - a.close), abs(b.low - a.close))
        for a, b in zip(window, window[1:])
    ]
    return max(minimum, sum(tr) / len(tr))


def bar_end(bar: Candle, duration: int = 1) -> datetime:
    return bar.start + duration * MINUTE


@dataclass(frozen=True)
class ClosedPrice:
    bars: list[Candle]

    @property
    def through(self) -> datetime | None:
        return bar_end(self.bars[-1]) if self.bars else None

    @property
    def tail_size(self) -> int:
        return len(contiguous_tail(self.bars))

    def covers_entry(self, slot: datetime) -> bool:
        through = self.through
        return through is not None and timedelta(0) <= slot - through <= MAX_ENTRY_CANDLE_LAG

    def audit(self, slot: datetime) -> dict:
        through = self.through
        return {
            "from": self.bars[0].start.isoformat() if self.bars else None,
            "through": through.isoformat() if through else None,
            "expected_through": slot.isoformat(),
            "lag_minutes": (slot - through) // MINUTE if through else None,
            "contiguous_tail": self.tail_size,
            "latest": through == slot,
        }


def merge_closed_price(
    saved: ClosedPrice,
    raw: list,
    received_at: datetime,
    session: tuple[datetime, datetime],
    cfg: Config,
) -> ClosedPrice:
    session_open, session_close = session
    observed = parse_candles(raw, received_at - timedelta(seconds=cfg.feed_grace_seconds - 1))
    observed = [
        bar for bar in observed if session_open <= bar.start and bar_end(bar) <= session_close
    ]
    # Responses can be partial or out of order. Supplement recorded evidence
    # by timestamp while retaining the latest provider correction for a bar.
    by_start = {bar.start: bar for bar in saved.bars}
    by_start.update((bar.start, bar) for bar in observed)
    return ClosedPrice(sorted(by_start.values(), key=lambda bar: bar.start))


def aggregate(bars: list[Candle], duration: int, session_open: datetime) -> list[Candle]:
    groups: dict[datetime, list[Candle]] = {}
    for bar in bars:
        offset = (bar.start - session_open) // MINUTE
        if offset >= 0:
            start = session_open + (offset // duration) * duration * MINUTE
            groups.setdefault(start, []).append(bar)
    return [
        Candle(
            start,
            group[0].open,
            max(bar.high for bar in group),
            min(bar.low for bar in group),
            group[-1].close,
            sum(bar.volume for bar in group),
        )
        for start, group in sorted(groups.items())
        if len(group) == duration
        and all(bar.start == start + i * MINUTE for i, bar in enumerate(group))
    ]


@dataclass(frozen=True)
class Swing:
    price: float
    at: datetime
    known_at: datetime


def swings(
    bars: list[Candle], side: int, duration: int = 1, left: int = 2, right: int = 1
) -> list[Swing]:
    result = []
    for index in range(left, len(bars) - right):
        bar = bars[index]
        group = bars[index - left : index + right + 1]
        if any(b.start != group[0].start + k * duration * MINUTE for k, b in enumerate(group)):
            continue
        values = [side * (b.low if side == 1 else b.high) for b in group]
        # Resolve flat extrema once, at the first occurrence.
        if values.index(min(values)) == left and values[left] < min(values[left + 1 :]):
            result.append(Swing(side * values[left], bar.start, bar_end(group[-1], duration)))
    return result


@dataclass(frozen=True)
class OIRow:
    key: str
    side: str
    strike: float
    oi: int


@dataclass(frozen=True)
class OISnapshot:
    at: datetime
    through: datetime
    expiry: str
    rows: tuple[OIRow, ...]

    @classmethod
    def restore(cls, value: dict) -> OISnapshot:
        return cls(
            timestamp(value["at"]),
            timestamp(value["through"]),
            value["expiry"],
            tuple(OIRow(**row) for row in value["rows"]),
        )


@dataclass(frozen=True)
class OIObservation:
    row: OIRow
    prior: int

    @property
    def increase(self) -> float:
        return (self.row.oi - self.prior) / self.prior


@dataclass(frozen=True)
class OIWindow:
    snapshot: OISnapshot
    baseline: datetime
    changes: tuple[OIObservation, ...]


def make_oi_snapshot(chain: list[dict], expiry: str, at: datetime, through: datetime) -> OISnapshot:
    rows = []
    for row in chain:
        oi = row.get("oi")
        if row["expiry"] != expiry or oi is None:
            continue
        if type(oi) not in (float, int) or not math.isfinite(oi) or oi < 0 or int(oi) != oi:
            continue
        rows.append(OIRow(row["instrument_key"], row["side"], float(row["strike"]), int(oi)))
    return OISnapshot(at, through, expiry, tuple(rows))


def match_oi(saved: list[dict], current: OISnapshot, cfg: Config) -> OIWindow | None:
    options = []
    for row in saved:
        previous = OISnapshot.restore(row)
        if (
            previous.expiry != current.expiry
            or previous.at.date() != current.at.date()
            or previous.through >= current.through
        ):
            continue
        elapsed = (current.at - previous.at).total_seconds()
        expected = DISPATCH_INTERVAL.total_seconds()
        if abs(elapsed - expected) <= cfg.oi_jitter_seconds:
            options.append((abs(elapsed - expected), previous.at, previous))
    if not options:
        return None
    past = min(options, key=lambda item: (item[0], -item[1].timestamp()))[2]
    keys = {(r.key, r.side, r.strike): r.oi for r in past.rows if r.oi > 0}
    changes = []
    for row in current.rows:
        old = keys.get((row.key, row.side, row.strike))
        if old is not None:
            changes.append(OIObservation(row, old))
    return OIWindow(current, past.at, tuple(changes)) if changes else None


def listed_strikes(contracts: list[dict]) -> list[float]:
    # A missing leg is evidence about data availability, never a reason to
    # renumber the exchange's listed strikes or move ATM to another strike.
    return sorted(
        {float(row["strike_price"]) for row in contracts if row["instrument_type"] in ("CE", "PE")}
    )


def paired_oi(window: OIWindow | None) -> dict[float, OIPair]:
    if window is None:
        return {}
    by_strike: dict[float, dict[str, OIObservation]] = {}
    for item in window.changes:
        by_strike.setdefault(item.row.strike, {})[item.row.side] = item
    return {
        strike: OIPair(strike, rows.get("CE"), rows.get("PE")) for strike, rows in by_strike.items()
    }


@dataclass(frozen=True)
class RiskPlan:
    stop: float
    t1: float
    t2: float
    t1_source: str
    t2_source: str
    risk: float
    reward_risk: float
    stop_policy: str
    t1_exit_pct: int = 50
    blended_reward_risk: float | None = None


def stop_buffer(atr_1m: float, atr_3m: float = 0) -> float:
    return max(0.8, 0.18 * atr_1m, 0.12 * atr_3m)


def live_contract(
    row: dict,
    quote: dict | None,
    now: datetime,
    index_time: datetime,
    band: StrikeBand,
    offset: int,
    cfg: Config,
) -> dict:
    checked_quote(quote, now, cfg.quote_max_age_seconds, field="ask")
    assert quote is not None
    seen = timestamp(quote["timestamp"])
    if abs((seen - index_time).total_seconds()) > cfg.quote_max_skew_seconds:
        raise DataError("INDEX_OPTION_QUOTE_SKEW")
    bid = read_number(quote["bid"], "bid", positive=True)
    ask = read_number(quote["ask"], "ask", positive=True)
    spread = 200 * (ask - bid) / (ask + bid)
    lot = read_number(row["lot_size"], "lot_size", positive=True)
    depth = (
        min(read_number(quote[key], key, nonnegative=True) for key in ("bid_qty", "ask_qty")) / lot
    )
    if not lot.is_integer() or not 0 <= spread <= cfg.max_spread_percent:
        raise DataError("INVALID_LIVE_SPREAD_OR_LOT")
    if depth < cfg.min_depth_lots:
        raise DataError("INSUFFICIENT_LIVE_DEPTH")
    pair = band.pairs[offset]
    return {
        "instrument_key": row["instrument_key"],
        "side": row["instrument_type"],
        "strike": pair.strike,
        "atm": band.atm,
        "offset": offset,
        "expiry": row["expiry"],
        "bid": bid,
        "ask": ask,
        "spread_pct": round(spread, 4),
        "depth_lots": depth,
        "lot_size": int(lot),
        "quote_time": seen.isoformat(),
        "paired_oi_at_contract": pair.public(),
    }


class Upstox:
    def __init__(self, token: str):
        if not token or any((c in token for c in "\r\n")):
            raise ProviderError("UPSTOX_ANALYTICS_TOKEN missing or invalid")
        self._token = token

    def get(self, path: str, params: dict | None = None):
        url = "https://api.upstox.com" + path + ("?" + urlencode(params) if params else "")
        req = Request(
            url,
            headers={
                "Authorization": "Bearer " + self._token,
                "Accept": "application/json",
                "User-Agent": "nifty-scanner/" + VERSION,
            },
        )
        for attempt in range(2):
            try:
                with urlopen(req, timeout=7) as r:

                    def reject_constant(value):
                        raise ValueError("Invalid numeric JSON")

                    obj = json.load(
                        r, parse_constant=reject_constant, parse_float=finite_json_float
                    )
                if not isinstance(obj, dict) or obj.get("status") != "success" or "data" not in obj:
                    raise ProviderError("Upstox returned an unsuccessful or invalid response")
                return obj["data"]
            except HTTPError as e:
                if e.code in (429, 500, 502, 503, 504) and attempt < 1:
                    time.sleep(1 + attempt)
                    continue
                raise ProviderError(f"Upstox request failed HTTP {e.code}") from None
            except (URLError, TimeoutError, OSError, ValueError):
                if attempt < 1:
                    time.sleep(1 + attempt)
                    continue
                raise ProviderError("Upstox request failed or returned invalid JSON") from None
        raise ProviderError("Upstox request failed")

    def session(self, now: datetime):
        data = self.get("/v2/market/timings/" + now.astimezone(IST).date().isoformat())
        matches = [x for x in data if x.get("exchange") == "NFO"] if isinstance(data, list) else []
        if not matches:
            return None
        sessions = []
        for row in matches:
            start = datetime.fromtimestamp(
                float(row["start_time"]) / 1000, timezone.utc
            ).astimezone(IST)
            end = datetime.fromtimestamp(float(row["end_time"]) / 1000, timezone.utc).astimezone(
                IST
            )
            if start.date() == now.astimezone(IST).date() and start < end:
                sessions.append((start, end))
        return next(((a, b) for a, b in sessions if a <= now.astimezone(IST) < b), None)

    def candles(self, key=INDEX):
        data = self.get("/v3/historical-candle/intraday/" + quote(key, safe="") + "/minutes/1")
        if not isinstance(data, dict) or not isinstance(data.get("candles"), list):
            raise ProviderError("Invalid candle response")
        return data["candles"]

    def prior_ten(self, today: date):
        previous_day = today - timedelta(days=1)
        from_day = today - timedelta(days=12)
        path = (
            "/v3/historical-candle/"
            + quote(INDEX, safe="")
            + "/minutes/10/"
            + previous_day.isoformat()
            + "/"
            + from_day.isoformat()
        )
        data = self.get(path)
        if not isinstance(data, dict) or not isinstance(data.get("candles"), list):
            raise ProviderError("Invalid prior 10-minute candle response")
        return data["candles"]

    def contracts(self, today: date):
        data = self.get("/v2/option/contract", {"instrument_key": INDEX})
        if not isinstance(data, list):
            raise ProviderError("Invalid option contract response")
        rows = []
        for r in data:
            if not isinstance(r, dict):
                raise ProviderError("Malformed contract record")
            if r.get("underlying_key") != INDEX or r.get("instrument_type") not in (
                "CE",
                "PE",
            ):
                continue
            try:
                exp = date.fromisoformat(str(r["expiry"]))
            except (ValueError, KeyError):
                continue
            if exp >= today:
                try:
                    strike = read_number(r["strike_price"], "listed_strike", positive=True)
                    lot = read_number(r["lot_size"], "listed_lot", positive=True)
                    key = r["instrument_key"]
                    if not lot.is_integer() or not isinstance(key, str) or not key:
                        continue
                except (DataError, KeyError):
                    continue
                rows.append(
                    {
                        "expiry": exp.isoformat(),
                        "instrument_key": key,
                        "instrument_type": r["instrument_type"],
                        "strike_price": strike,
                        "lot_size": int(lot),
                    }
                )
        if not rows:
            raise ProviderError("No unexpired NIFTY option contracts")
        expiry = min((date.fromisoformat(r["expiry"]) for r in rows)).isoformat()
        return (expiry, [r for r in rows if r["expiry"] == expiry])

    def chain(self, expiry: str, contracts: list[dict]):
        data = self.get("/v2/option/chain", {"instrument_key": INDEX, "expiry_date": expiry})
        if not isinstance(data, list) or not data:
            raise ProviderError("Empty option chain")
        valid = {
            r["instrument_key"]: (float(r["strike_price"]), r["instrument_type"])
            for r in contracts
            if r.get("instrument_key") and r.get("strike_price") is not None
        }
        metadata = {r["instrument_key"]: r for r in contracts if r.get("instrument_key")}
        result = []
        seen = set()
        for row in data:
            if not isinstance(row, dict):
                raise ProviderError("Malformed chain record")
            if row.get("underlying_key") != INDEX or row.get("expiry") != expiry:
                raise ProviderError("Chain underlying or expiry mismatch")
            try:
                strike = float(row["strike_price"])
            except (TypeError, ValueError, KeyError):
                raise ProviderError("Invalid strike") from None
            for side, field in (("CE", "call_options"), ("PE", "put_options")):
                option = row.get(field) or {}
                key = option.get("instrument_key")
                if not key:
                    continue
                if valid.get(key) != (strike, side) or key in seen:
                    raise ProviderError("Contract identity mismatch")
                seen.add(key)
                market = option.get("market_data") or {}
                greeks = option.get("option_greeks") or {}
                try:
                    oi = float(market["oi"]) if market.get("oi") is not None else None
                    ltp = float(market.get("ltp") or 0)
                    volume = float(market.get("volume") or 0)
                    delta = float(greeks["delta"]) if greeks.get("delta") is not None else None
                    gamma = float(greeks["gamma"]) if greeks.get("gamma") is not None else None
                    theta = float(greeks["theta"]) if greeks.get("theta") is not None else None
                    vega = float(greeks["vega"]) if greeks.get("vega") is not None else None
                    iv = float(greeks["iv"]) if greeks.get("iv") is not None else None
                    prev_oi = (
                        float(market["prev_oi"]) if market.get("prev_oi") is not None else None
                    )
                    chain_bid = float(market.get("bid_price") or 0)
                    chain_ask = float(market.get("ask_price") or 0)
                    chain_bid_qty = float(market.get("bid_qty") or 0)
                    chain_ask_qty = float(market.get("ask_qty") or 0)
                except (ValueError, TypeError):
                    raise ProviderError("Invalid OI/greek data") from None
                if not all(
                    (
                        math.isfinite(x) and x >= 0
                        for x in (
                            ltp,
                            volume,
                            chain_bid,
                            chain_ask,
                            chain_bid_qty,
                            chain_ask_qty,
                        )
                    )
                ):
                    raise ProviderError("Invalid option chain values")
                if oi is not None and (not math.isfinite(oi) or oi < 0 or not oi.is_integer()):
                    oi = None
                if any(
                    (
                        x is not None and (not math.isfinite(x))
                        for x in (delta, gamma, theta, vega, iv, prev_oi)
                    )
                ):
                    raise ProviderError("Invalid option greek data")
                lot = metadata[key].get("lot_size")
                if (
                    lot is None
                    or not math.isfinite(float(lot))
                    or float(lot) <= 0
                    or (not float(lot).is_integer())
                ):
                    raise ProviderError("Missing or invalid live lot size")
                result.append(
                    {
                        "instrument_key": key,
                        "expiry": expiry,
                        "strike": strike,
                        "side": side,
                        "oi": oi,
                        "ltp": ltp,
                        "volume": volume,
                        "delta": delta,
                        "gamma": gamma,
                        "theta": theta,
                        "vega": vega,
                        "iv": iv,
                        "prev_oi": prev_oi,
                        "lot_size": lot,
                        "chain_bid": chain_bid,
                        "chain_ask": chain_ask,
                        "chain_bid_qty": chain_bid_qty,
                        "chain_ask_qty": chain_ask_qty,
                    }
                )
        # Upstox's chain supplies a spot reference and a much larger distant
        # strike universe than this strategy needs. Keep the listed grid in
        # contracts and retain the local OI profile separately.
        snapshot_spots = [r.get("underlying_spot_price") for r in data]
        observed_spots = [
            float(v)
            for v in snapshot_spots
            if type(v) in (int, float) and math.isfinite(v) and v > 0
        ]
        if observed_spots:
            center = median(observed_spots)
            result = [r for r in result if abs(r["strike"] - center) <= 650]
        if len(result) < 4 or not {"CE", "PE"}.issubset({r["side"] for r in result}):
            raise ProviderError("Incomplete option chain")
        return result

    def quotes(self, keys: list[str]):
        if not keys:
            return {}
        data = self.get(
            "/v2/market-quote/quotes", {"instrument_key": ",".join(dict.fromkeys(keys))}
        )
        if not isinstance(data, dict):
            raise ProviderError("Invalid quote response")
        out = {}
        for q in data.values():
            if not isinstance(q, dict):
                continue
            key = q.get("instrument_token")
            stamp = q.get("timestamp")
            if key not in keys or not stamp:
                continue
            try:
                price = float(q.get("last_price") or 0)
                buys = (q.get("depth") or {}).get("buy") or []
                sells = (q.get("depth") or {}).get("sell") or []
                b = buys[0] if buys else {}
                a = sells[0] if sells else {}
                numeric = {
                    name: float(q[name]) if q.get(name) is not None else None
                    for name in ("oi", "average_price")
                }
                for name, value in numeric.items():
                    if value is not None and (not math.isfinite(value)):
                        numeric[name] = None
                quoted = {
                    "last_price": price,
                    "bid": float(b.get("price") or 0),
                    "bid_qty": float(b.get("quantity") or 0),
                    "ask": float(a.get("price") or 0),
                    "ask_qty": float(a.get("quantity") or 0),
                }
                if any((not math.isfinite(x) or x < 0 for x in quoted.values())):
                    continue
                out[key] = {**quoted, "timestamp": stamp, **numeric}
            except (TypeError, ValueError):
                continue
        return out


def starting_state(now: datetime) -> dict:
    return {
        "schema": 7,
        "engine_version": VERSION,
        "initialized_at": now.isoformat(),
        "initialized_flat": True,
        "session_date": now.date().isoformat(),
        "position": None,
        "history": [],
        "outbox": [],
        "last_exit": None,
        "v124": {
            "session_date": now.date().isoformat(),
            "oi_samples": [],
            "consumed_signals": [],
        },
    }


def validate_state(state: dict):
    if (
        not isinstance(state, dict)
        or state.get("schema") != 7
        or "position" not in state
        or not isinstance(state.get("history"), list)
        or not isinstance(state.get("outbox"), list)
    ):
        raise ScannerError("Invalid or unsupported persisted state")
    ids = set()
    for event in state["outbox"]:
        if (
            not isinstance(event, dict)
            or not isinstance(event.get("id"), str)
            or event["id"] in ids
            or event.get("status")
            not in ("PENDING", "CLAIMED", "SENT", "DELIVERY_UNCERTAIN", "EXPIRED")
        ):
            raise ScannerError("Invalid or duplicate persisted outbox event")
        ids.add(event["id"])
    p = state["position"]
    if p is not None:
        if (
            not isinstance(p, dict)
            or not p.get("id")
            or p.get("status") != "OPEN"
            or p.get("direction") not in ("BULLISH", "BEARISH")
        ):
            raise ScannerError("Invalid persisted reference position")
        side = 1 if p["direction"] == "BULLISH" else -1
        entry, stop, initial, t1, t2 = [
            read_number(
                p.get(k, p.get("stop") if k == "initial_stop" else None),
                k,
                positive=True,
            )
            for k in ("entry_spot", "stop", "initial_stop", "t1", "t2")
        ]
        took_t1 = p.get("t1_hit", False)
        t1_exit_pct = p.get("t1_exit_pct", 50)
        if type(t1_exit_pct) is not int or not 0 < t1_exit_pct < 100:
            raise ScannerError("Invalid persisted T1 allocation")
        if (
            type(took_t1) is not bool
            or side * (entry - initial) <= 0
            or side * (t1 - entry) <= 0
            or side * (t2 - t1) <= 0
            or side * (stop - initial) < 0
            or (not took_t1 and side * (entry - stop) <= 0)
        ):
            raise ScannerError("Invalid persisted position prices")
        if not p.get("instrument_key") or not p.get("expiry"):
            raise ScannerError("Invalid persisted contract identity")
        timestamp(p.get("opened_at"))
        timestamp(p.get("last_candle"))
    if "v124" in state:
        engine = state["v124"]
        if (
            not isinstance(engine, dict)
            or not isinstance(engine.get("oi_samples"), list)
            or not isinstance(engine.get("consumed_signals"), list)
        ):
            raise ScannerError("Invalid persisted strategy state")


def load_state(path: Path) -> dict:
    if not path.exists():
        raise ScannerError(
            "STATE_FILE_MISSING: manually reconcile existing positions before --initialize-flat"
        )
    try:
        with path.open(encoding="utf-8") as f:
            s = json.load(
                f,
                parse_constant=lambda _: (_ for _ in ()).throw(ValueError("Nonfinite state")),
            )
    except (OSError, ValueError) as exc:
        raise ScannerError("State unreadable; fail closed") from exc
    validate_state(s)
    return s


def save_state(path: Path, s: dict):
    validate_state(s)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=".state-", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(s, f, sort_keys=True, separators=(",", ":"), allow_nan=False)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
        d = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(d)
        finally:
            os.close(d)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


@contextmanager
def local_lock(state_path: Path):
    state_path.parent.mkdir(parents=True, exist_ok=True)
    with open(str(state_path) + ".lock", "a+") as f:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def ensure_engine(state: dict, now: datetime) -> dict:
    if state.get("position") and timestamp(state["position"]["opened_at"]).date() > now.date():
        raise ScannerError("FUTURE_DATED_REFERENCE_POSITION")
    if state.get("v124", {}).get("session_date") != now.date().isoformat():
        state["v124"] = starting_state(now)["v124"]
    state["session_date"] = now.date().isoformat()
    state["engine_version"] = VERSION
    return state["v124"]


def new_event(state: dict, kind: str, details: dict, now: datetime) -> str:
    if kind not in ALERT_KINDS:
        raise ScannerError("Non-actionable alert kind")
    details = copy.deepcopy(details)
    email_observation = details.pop("email_observation", None)
    identity = [kind, details["position_id"]]
    if kind == "ADJUST_SL":
        identity.extend((details["observed_at"], details["new_stop"], details["new_t2"]))
    digest = hashlib.sha256(json.dumps(identity, separators=(",", ":")).encode()).hexdigest()[:24]
    for event in state["outbox"]:
        previous = event.get("details", {})
        if event["id"] == digest:
            return digest
        if (
            kind != "ADJUST_SL"
            and event["kind"] == kind
            and previous.get("position_id") == details["position_id"]
        ):
            return event["id"]
    event = {
        "id": digest,
        "kind": kind,
        "details": details,
        "created_at": now.isoformat(),
        "status": "PENDING",
    }
    if email_observation is not None:
        event["email_observation"] = email_observation
    state["outbox"].append(event)
    return digest


def claim_outbox(state: dict, token: str, now: datetime):
    if not token:
        raise ScannerError("Notification claim token absent")
    for event in state["outbox"]:
        if event.get("kind") not in ALERT_KINDS:
            continue
        # Previous claims with no attempted_at cannot have reached SMTP via this
        # implementation: safe to reclaim when a workflow crashed pre-delivery.
        legacy_pending = event.get("status") == "PENDING" and not event.get("attempted_at")
        # Old versions could CLAIM without the v123 durable commit-before-SMTP
        # protocol. Their state CANNOT prove non-delivery; do not resend.
        fresh_reclaim = (
            event.get("status") == "CLAIMED"
            and event.get("claim_policy") == "V123_PHASED"
            and not event.get("attempted_at")
        )
        if (legacy_pending or fresh_reclaim) and event["kind"] == "ENTRY":
            details = event.get("details") or {}
            active_id = (state.get("position") or {}).get("id")
            created = timestamp(event.get("created_at"))
            if details.get("position_id") != active_id or now - created > 3 * MINUTE:
                event.update(status="EXPIRED", expired_at=now.isoformat(), claim=None)
                continue
        if legacy_pending or fresh_reclaim:
            event.update(
                status="CLAIMED",
                claim=token,
                claimed_at=now.isoformat(),
                claim_policy="V123_PHASED",
            )


def append_audit(path: Path, event: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(event, sort_keys=True, allow_nan=False, separators=(",", ":")) + "\n")
        f.flush()
        os.fsync(f.fileno())


def record_inputs(path: Path, record: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = json.dumps(record, allow_nan=False, sort_keys=True, separators=(",", ":")).encode()
    fd, tmp = tempfile.mkstemp(prefix=".capture-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            with gzip.GzipFile(fileobj=stream, mode="wb", compresslevel=7, mtime=0) as z:
                z.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


class RecordingProvider:
    """Time-stamped, exact source-call recording with no token or secrets."""

    def __init__(self, underlying):
        self.provider = underlying
        self.calls = []

    def __getattr__(self, name):
        attr = getattr(self.provider, name)
        if not callable(attr):
            return attr

        def observed(*args, **kwargs):
            signature = {
                "name": name,
                "args": jsonable(args),
                "kwargs": jsonable(kwargs),
            }
            try:
                value = attr(*args, **kwargs)
                self.calls.append({**signature, "result": jsonable(value)})
                return value
            except (ProviderError, DataError) as exc:
                self.calls.append({**signature, "error": type(exc).__name__, "reason": str(exc)})
                raise

        return observed


def jsonable(value: Any):
    if isinstance(value, (datetime, date)):
        return value.isoformat()
    if isinstance(value, (list, tuple)):
        return [jsonable(v) for v in value]
    if isinstance(value, dict):
        return {str(k): jsonable(v) for k, v in value.items()}
    if isinstance(value, (float, int, str, bool)) or value is None:
        return value
    if isinstance(value, Path):
        return str(value)
    raise TypeError("Non-serializable provider payload")


class ReplayProvider:
    """Exact ordered API-recording replay: no network, no future snapshots."""

    def __init__(self, calls: list[dict]):
        self.calls = calls
        self.index = 0

    def __getattr__(self, name):
        def recorded(*args, **kwargs):
            if self.index >= len(self.calls):
                raise ProviderError("CAPTURE_EXHAUSTED:" + name)
            r = self.calls[self.index]
            self.index += 1
            if r["name"] != name or r["args"] != jsonable(args) or r["kwargs"] != jsonable(kwargs):
                raise ProviderError(
                    "CAPTURE_CALL_SEQUENCE_MISMATCH expected " + r["name"] + " got " + name
                )
            if "error" in r:
                cls = DataError if r["error"] == "DataError" else ProviderError
                raise cls(r["reason"])
            if name == "session" and r["result"] is not None:
                return tuple(timestamp(x) for x in r["result"])
            return copy.deepcopy(r["result"])

        return recorded


def checked_quote(q: dict | None, now: datetime, max_age: float, field="last_price") -> float:
    if not isinstance(q, dict):
        raise DataError("Missing live quote")
    price = read_number(q.get(field), field, positive=True)
    age = (now - timestamp(q.get("timestamp"))).total_seconds()
    if not -2 <= age <= max_age:
        raise DataError("STALE_OR_FUTURE_DATED_QUOTE")
    return price


def position_event_payload(p: dict, now: datetime, **more):
    fields = (
        "id",
        "direction",
        "instrument_key",
        "side",
        "strike",
        "expiry",
        "entry_spot",
        "entry_ask",
        "initial_stop",
        "stop",
        "t1",
        "t2",
        "t1_exit_pct",
        "remaining_pct",
        "opened_at",
        "scenario",
        "t1_source",
        "t2_source",
        "stop_policy",
        "runner",
    )
    return {
        "position_id": p["id"],
        "observed_at": now.isoformat(),
        "position": {k: p.get(k) for k in fields},
        "broker_order_submitted": False,
        "broker_fill_confirmed": False,
        **more,
    }


def close_reference(
    position: dict, at: datetime, reason: str, observed: float | None, source: str
) -> dict:
    return dict(
        position,
        status="CLOSED",
        closed_at=at.isoformat(),
        exit_reason=reason,
        observed_exit_spot=observed,
        exit_source=source,
        fill_confirmed=False,
    )


def prior_context(engine: dict, api, now: datetime) -> list[Candle]:
    if "prior_ten" not in engine:
        try:
            raw = api.prior_ten(now.date())
            rows = parse_candles(raw, now)
            days = sorted({b.start.date() for b in rows if b.start.date() < now.date()})
            if not days:
                return []
            most_recent = days[-1]
            bars = [
                b
                for b in rows
                if b.start.date() == most_recent
                and b.start >= day_time(b.start, 9, 15)
                and bar_end(b, 10) <= day_time(b.start, 15, 30)
                and (b.start - day_time(b.start, 9, 15)) % (10 * MINUTE) == timedelta(0)
            ]
            engine["prior_ten"] = [serialize_bar(b) for b in bars]
        except (DataError, ProviderError, ValueError, TypeError, KeyError):
            return []
    return parse_candles(engine["prior_ten"], now) if engine["prior_ten"] else []


MINUTE = timedelta(minutes=1)
DISPATCH_INTERVAL = 3 * MINUTE
MAX_ENTRY_CANDLE_LAG = MINUTE
OI_LEVEL_MATERIAL_CHANGE = 0.02
T1_SPOT_BAND = (45.0, 50.0)
T2_SPOT_BAND = (80.0, 90.0)
STRONG_MOVE = 15.0


@dataclass(frozen=True)
class Config:
    oi_jitter_seconds: int = 35
    feed_grace_seconds: float = 2.0
    quote_max_age_seconds: int = 35
    quote_max_skew_seconds: int = 12
    min_reward_risk: float = 0.0
    max_spread_percent: float = 2.0
    min_depth_lots: float = 1.0
    max_state_history: int = 240
    record_inputs: bool = True
    arm_continuation_runner: bool = True
    initial_stop_points: float = 25.0
    allow_persistent_oi: bool = False

    def __post_init__(self):
        flags = (
            "record_inputs",
            "arm_continuation_runner",
            "allow_persistent_oi",
        )
        integers = (
            "oi_jitter_seconds",
            "quote_max_age_seconds",
            "quote_max_skew_seconds",
            "max_state_history",
        )
        for key, value in asdict(self).items():
            if key in flags:
                if type(value) is not bool:
                    raise DataError(f"{key} must be a boolean")
            elif (
                type(value) not in (int, float)
                or not math.isfinite(value)
                or value < 0
                or (value == 0 and key != "min_reward_risk")
                or (key in integers and type(value) is not int)
            ):
                raise DataError(f"Invalid configuration: {key}")
        if not 20 <= self.initial_stop_points <= 30:
            raise DataError("Initial stop must be between 20 and 30 NIFTY points")
        if not (
            self.oi_jitter_seconds < 60
            and 1 <= self.feed_grace_seconds < 15
            and self.quote_max_skew_seconds <= self.quote_max_age_seconds
        ):
            raise DataError("Inconsistent market data timing")


@dataclass(frozen=True)
class OIPair:
    strike: float
    call: OIObservation | None
    put: OIObservation | None

    @property
    def changes(self) -> tuple[float, float] | None:
        if self.call is not None and self.put is not None:
            return self.call.increase, self.put.increase
        return None

    def rule(self, side: int) -> str | None:
        changes = self.changes
        if changes is None:
            return None
        call, put = changes
        if not (side * call < 0 < side * put):
            return None
        if max(map(abs, changes)) >= OI_LEVEL_MATERIAL_CHANGE:
            return "STANDARD_2_PERCENT"
        return None

    @property
    def quiet(self) -> bool:
        return self.changes is not None and max(map(abs, self.changes)) < OI_LEVEL_MATERIAL_CHANGE

    def public(self) -> dict:
        if self.changes is None:
            state = "MISSING"
        elif self.rule(1):
            state = "BULLISH"
        elif self.rule(-1):
            state = "BEARISH"
        elif self.changes[0] * self.changes[1] > 0:
            state = "MIXED"
        elif self.quiet:
            state = "QUIET"
        else:
            state = "MIXED"
        return {
            "strike": self.strike,
            "state": state,
            "quiet": self.quiet,
            "call_oi": self.call.row.oi if self.call else None,
            "put_oi": self.put.row.oi if self.put else None,
            "call_key": self.call.row.key if self.call else None,
            "put_key": self.put.row.key if self.put else None,
            "call_change_pct": self.call.increase * 100 if self.call is not None else None,
            "put_change_pct": self.put.increase * 100 if self.put is not None else None,
        }


def nearest_strike(grid: list[float], level: float) -> float:
    return min(grid, key=lambda strike: (abs(strike - level), strike))


@dataclass(frozen=True)
class StrikeBand:
    atm: float
    pairs: dict[int, OIPair]

    @classmethod
    def build(cls, grid: list[float], spot: float, pairs: dict[float, OIPair]) -> StrikeBand | None:
        if not grid or not grid[0] <= spot <= grid[-1]:
            return None
        atm = nearest_strike(grid, spot)
        center = grid.index(atm)
        offsets = {}
        for offset in (-2, -1, 0, 1, 2):
            index = center + offset
            if 0 <= index < len(grid):
                strike = grid[index]
                offsets[offset] = pairs.get(strike, OIPair(strike, None, None))
        return cls(atm, offsets)

    def public(self) -> dict:
        return {
            "atm": self.atm,
            "contracts": [
                {
                    "offset": offset,
                    "side": kind,
                    "strike": pair.strike if pair else None,
                    "change_pct": leg.increase * 100 if leg else None,
                    "oi": leg.row.oi if leg else None,
                    "instrument_key": leg.row.key if leg else None,
                }
                for kind, offsets in (("CE", (-2, -1, 0)), ("PE", (0, 1, 2)))
                for offset in offsets
                for pair in [self.pairs.get(offset)]
                for leg in [(pair.call if kind == "CE" else pair.put) if pair else None]
            ],
            "strikes": [
                {"offset": offset, **self.pairs[offset].public()}
                if offset in self.pairs
                else {"offset": offset, "state": "MISSING_LISTING"}
                for offset in (-2, -1, 0, 1, 2)
            ],
        }


# Strategy code. Every price setup is derived from completed candles and has a
# stable origin. Live spot, option OI and the option book are separate inputs.
SCHEDULE_GRACE = timedelta(seconds=90)
POSITIVE = 1
NEGATIVE = -1


def edge(bar: Candle, side: int) -> float:
    return bar.high if side == POSITIVE else bar.low


def defense(bar: Candle, side: int) -> float:
    return bar.low if side == POSITIVE else bar.high


def beyond(value: float, level: float, side: int, margin: float = 0.0) -> bool:
    return side * (value - level) > margin


def held(bars: list[Candle], level: float, side: int, margin: float = 0.0) -> bool:
    return len(bars) >= 2 and all(beyond(bar.close, level, side, margin) for bar in bars[-2:])


def entry_deadline(at: datetime, session_open: datetime) -> datetime:
    slot, remainder = divmod(at - session_open, DISPATCH_INTERVAL)
    return session_open + (slot + bool(remainder) + 1) * DISPATCH_INTERVAL + SCHEDULE_GRACE


@dataclass(frozen=True)
class DefenseZone:
    side: int
    anchor: Swing
    touch: Swing
    tests: int
    tolerance: float

    @property
    def price(self) -> float:
        return self.touch.price

    @property
    def invalidation(self) -> float:
        outer = min(self.side * self.touch.price, self.side * self.anchor.price)
        return self.side * (outer - self.tolerance / 2)


@dataclass(frozen=True)
class Setup:
    kind: str
    side: int
    origin: Swing
    level: float
    confirmed_at: datetime
    invalidation: float
    exhausted_at: float
    tolerance: float
    outer_range: bool = False

    @property
    def id(self) -> str:
        return f"{self.kind}:{self.side}:{self.origin.at.isoformat()}"

    def audit(self) -> dict:
        return jsonable(asdict(self)) | {"id": self.id}


@dataclass(frozen=True)
class DirectionalLeg:
    side: int
    origin: Swing
    extreme: Swing

    @property
    def travel(self) -> float:
        return self.side * (self.extreme.price - self.origin.price)


def directional_leg(threes: list[Candle]) -> DirectionalLeg | None:
    """Track broad legs using the same distance as the first objective."""
    if not threes:
        return None
    first = Swing(threes[0].close, threes[0].start, bar_end(threes[0], 3))
    low = high = first
    leg = None
    reset = T1_SPOT_BAND[0]
    for bar in threes[1:]:
        close = Swing(bar.close, bar.start, bar_end(bar, 3))
        if leg is None:
            if close.price < low.price:
                low = close
            if close.price > high.price:
                high = close
            if high.price - low.price >= reset:
                leg = (
                    DirectionalLeg(POSITIVE, low, high)
                    if high.at > low.at
                    else DirectionalLeg(NEGATIVE, high, low)
                )
        elif beyond(close.price, leg.extreme.price, leg.side):
            leg = replace(leg, extreme=close)
        elif -leg.side * (close.price - leg.extreme.price) >= reset:
            leg = DirectionalLeg(-leg.side, leg.extreme, close)
    return leg


@dataclass(frozen=True)
class Structure:
    opened: datetime
    bars: list[Candle]
    threes: list[Candle]
    tens: list[Candle]
    pivots3: dict[int, list[Swing]]
    zones: dict[int, list[DefenseZone]]
    atr: float
    atr3: float
    move3: float | None
    acceleration: float | None
    trend: int
    range_bounds: tuple[float, float] | None
    leg: DirectionalLeg | None
    setups: list[Setup]

    @property
    def through(self) -> datetime:
        return bar_end(self.bars[-1])

    def regime(self, band: StrikeBand | None) -> str:
        if self.range_bounds:
            if (
                band
                and len(band.pairs) == 5
                and all(pair.quiet for pair in band.pairs.values())
                and abs(self.move3 or 0) < STRONG_MOVE
                and abs(self.acceleration or 0) < STRONG_MOVE
            ):
                return "SIDEWAYS"
            return "MIXED"
        if self.trend:
            return "CONTINUOUS_BULLISH" if self.trend == POSITIVE else "CONTINUOUS_BEARISH"
        return "MIXED"


def swing_zones(
    bars: list[Candle], pivots: list[Swing], side: int, minimum_excursion: float
) -> list[DefenseZone]:
    by_start = {bar.start: i for i, bar in enumerate(bars)}
    zones: list[DefenseZone] = []
    for pivot in pivots:
        index = by_start[pivot.at]
        # Size the zone using volatility known when this touch was confirmed.
        width = min(
            T1_SPOT_BAND[0] / 2,
            max(minimum_excursion / 3, volatility(bars[max(0, index - 13) : index + 1])),
        )
        matched = None
        for previous in reversed(zones):
            if abs(pivot.price - previous.anchor.price) > max(width, previous.tolerance):
                continue
            between = bars[by_start[previous.touch.at] + 1 : index]
            if not between:
                continue
            excursion = max(side * (edge(bar, side) - pivot.price) for bar in between)
            if excursion < max(minimum_excursion / 2, width):
                continue
            if any(
                held(between[max(0, j - 1) : j + 1], previous.invalidation, -side)
                for j in range(1, len(between))
            ):
                continue
            matched = previous
            break
        if matched:
            zones.remove(matched)
            zones.append(DefenseZone(side, matched.anchor, pivot, matched.tests + 1, width))
        else:
            zones.append(DefenseZone(side, pivot, pivot, 1, width))
    active = []
    for zone in zones:
        since = bars[by_start[zone.touch.at] + 1 :]
        if not any(
            held(since[j - 1 : j + 1], zone.invalidation, -side) for j in range(1, len(since))
        ):
            active.append(zone)
    return active


def trend_context(threes: list[Candle], pivots: dict[int, list[Swing]]) -> int:
    if len(threes) < 3:
        return 0
    # Confirm structure with pivots when both pairs exist. The opening impulse
    # can establish direction earlier through successive range and close shifts.
    for side in (POSITIVE, NEGATIVE):
        lows, highs = pivots[POSITIVE][-2:], pivots[NEGATIVE][-2:]
        if len(lows) == len(highs) == 2 and all(
            beyond(pair[-1].price, pair[-2].price, side) for pair in (lows, highs)
        ):
            return side
        first, middle, last = threes[-3:]
        if (
            beyond(last.close, middle.close, side)
            and beyond(middle.close, first.close, side)
            and beyond(last.close, first.close, side, STRONG_MOVE)
            and beyond(edge(last, side), edge(first, side), side)
            and beyond(defense(last, side), defense(first, side), side)
        ):
            return side
    return 0


def established_range(
    bars: list[Candle], tens: list[Candle], atr: float
) -> tuple[float, float] | None:
    if not tens:
        return None
    start = tens[-1].start
    core = [bar for bar in bars if start <= bar.start < bar_end(tens[-1], 10)]
    if len(core) != 10:
        return None
    low, high = min(bar.low for bar in core), max(bar.high for bar in core)
    if abs(core[-1].close - core[0].close) >= max(STRONG_MOVE, atr):
        return None
    if not (
        any(abs(bar.low - low) <= atr for bar in core[:5])
        and any(abs(bar.low - low) <= atr for bar in core[5:])
        and any(abs(bar.high - high) <= atr for bar in core[:5])
        and any(abs(bar.high - high) <= atr for bar in core[5:])
    ):
        return None
    recent = [bar for bar in bars if bar.start >= start]
    if held(recent, high, POSITIVE) or held(recent, low, NEGATIVE):
        return None
    return low, high


def first_close_beyond(
    bars: list[Candle], pivot: Swing, level: float, side: int
) -> datetime | None:
    return next(
        (bar_end(bar) for bar in bars if bar.start > pivot.at and beyond(bar.close, level, side)),
        None,
    )


def local_setups(
    opened: datetime,
    bars: list[Candle],
    threes: list[Candle],
    pivots: dict[int, list[Swing]],
    zones: dict[int, list[DefenseZone]],
    trend: int,
    move: float | None,
    atr: float,
    bounds: tuple[float, float] | None,
) -> list[Setup]:
    setups = []
    by_start = {bar.start: i for i, bar in enumerate(bars)}
    through = bar_end(bars[-1])
    # Track the opposing zones independently of the current trend label. A
    # secondary reversal may form while the three-minute trend is still intact.
    for side, candidates in zones.items():
        for zone in candidates:
            touch = zone.touch
            if through > entry_deadline(touch.known_at, opened) + DISPATCH_INTERVAL:
                continue
            before = bars[: by_start[touch.at]]
            recent = bars[by_start[touch.at] :]
            if not before:
                continue
            local_margin = max(STRONG_MOVE / 3, zone.tolerance / 2)
            if zone.tests >= 2:
                level = touch.price + side * local_margin
                # Use the closer intervening pullback edge when a sharp
                # rejection crosses it in the first completed recovery bar.
                pullback = before[-2:]
                if pullback and side * (edge(pullback[-1], side) - touch.price) >= local_margin:
                    local_edge = max((edge(bar, side) for bar in pullback), key=lambda x: side * x)
                    if side * (local_edge - touch.price) <= T1_SPOT_BAND[0]:
                        level = local_edge
                # Confirm that the touch candle or the first recovery candle
                # rejected the level. The resting zone survives a missed entry.
                crossed = first_close_beyond(recent, touch, level, side)
                if crossed is not None:
                    setups.append(
                        Setup(
                            "REVERSAL",
                            side,
                            touch,
                            level,
                            max(crossed, touch.known_at),
                            zone.invalidation,
                            level + side * T1_SPOT_BAND[0],
                            zone.tolerance,
                        )
                    )
            if trend != side or move is None or side * move <= 0:
                continue
            local_trend = [pivot for pivot in pivots[-side] if pivot.at < touch.at]
            if not local_trend:
                continue
            level = local_trend[-1].price
            from_defense = side * (level - touch.price)
            if not max(STRONG_MOVE / 2, atr / 2) <= from_defense <= T1_SPOT_BAND[1]:
                continue
            crossed = first_close_beyond(recent, touch, level, side)
            if crossed is None:
                continue
            # A resumption needs a genuine pullback. Small local ticks in an
            # extended leg do not establish a new risk and entry reference.
            price_at_cross = next(bar.close for bar in recent if bar_end(bar) == crossed)
            if side * (price_at_cross - level) < local_margin:
                crossed = first_close_beyond(recent, touch, level + side * local_margin, side)
            if crossed is not None:
                setups.append(
                    Setup(
                        "CONTINUATION",
                        side,
                        touch,
                        level,
                        max(crossed, touch.known_at, local_trend[-1].known_at),
                        zone.invalidation,
                        level + side * T1_SPOT_BAND[0],
                        zone.tolerance,
                    )
                )
        # A direction can establish without a pullback through successive
        # completed 3m advances. Use the first confirmed break of that impulse.
        if trend != side or move is None or side * move <= 0 or len(threes) < 3:
            continue
        start = len(threes) - 1
        while (
            start > 0
            and threes[start].start - threes[start - 1].start == DISPATCH_INTERVAL
            and beyond(threes[start].close, threes[start - 1].close, side)
        ):
            start -= 1
        if start == len(threes) - 1:
            continue
        origin_bar = threes[start]
        impulse = threes[start + 1 :]
        basis = defense(origin_bar, side)
        level = edge(origin_bar, side)
        eligible = next(
            (
                bar
                for bar in impulse
                if side * (bar.close - basis) >= STRONG_MOVE and beyond(bar.close, level, side)
            ),
            None,
        )
        if eligible:
            at = bar_end(eligible, 3)
            setups.append(
                Setup(
                    "TREND_BREAK",
                    side,
                    Swing(basis, origin_bar.start, bar_end(origin_bar, 3)),
                    level,
                    at,
                    basis,
                    level + side * T1_SPOT_BAND[0],
                    atr,
                )
            )
    # An outer range break and hold can qualify without waiting for the trend
    # classifier. The earliest close pair anchors the expiry and anti-chase check.
    if len(threes) >= 3:
        last = bars[-1]
        for ten in reversed(aggregate(bars, 10, opened)[-3:]):
            base = [bar for bar in bars if ten.start <= bar.start < bar_end(ten, 10)]
            outer = established_range(base, [ten], atr)
            if outer is None:
                continue
            after = [bar for bar in bars if bar.start >= bar_end(ten, 10)]
            for side, level in ((NEGATIVE, outer[0]), (POSITIVE, outer[1])):
                cross = next(
                    (i for i in range(1, len(after)) if held(after[i - 1 : i + 1], level, side)),
                    None,
                )
                if cross is not None and beyond(last.close, level, side):
                    at = bar_end(after[cross])
                    setups.append(
                        Setup(
                            "RANGE_BREAK",
                            side,
                            Swing(level, ten.start, bar_end(ten, 10)),
                            level,
                            at,
                            level - side * atr,
                            level + side * T1_SPOT_BAND[0],
                            atr,
                            True,
                        )
                    )
            break

    # A completed, failed break above resistance or below support confirms
    # a rejection at the edge of a range. It may precede a break of the
    # distant boundary. The failed break has to test an existing zone.
    for side, candidates in zones.items():
        for trigger_bar in bars[-3:]:
            observed = bar_end(trigger_bar)
            extreme = defense(trigger_bar, side)
            for zone in candidates:
                older = zone.touch if zone.touch.at < trigger_bar.start else zone.anchor
                if older.known_at > trigger_bar.start:
                    continue
                width = max(STRONG_MOVE / 3, zone.tolerance / 2)
                if abs(extreme - older.price) > zone.tolerance:
                    continue
                if side * (trigger_bar.close - older.price) < width:
                    continue
                if side * (trigger_bar.close - trigger_bar.open) < width:
                    continue
                sample = bars[by_start[older.at] + 1 : by_start[trigger_bar.start]]
                if (
                    not sample
                    or max(side * (edge(bar, side) - extreme) for bar in sample) < zone.tolerance
                ):
                    continue
                origin = Swing(extreme, trigger_bar.start, observed)
                level = extreme + side * width
                setups.append(
                    Setup(
                        "EDGE_REJECTION",
                        side,
                        origin,
                        level,
                        observed,
                        extreme - side * width,
                        level + side * T1_SPOT_BAND[0],
                        zone.tolerance,
                        True,
                    )
                )
                break
    if bounds:
        lo, hi = bounds
        setups = [
            setup
            for setup in setups
            if (
                setup.outer_range
                and abs(setup.origin.price - (lo if setup.side == POSITIVE else hi))
                <= setup.tolerance
            )
            or held(bars, hi if setup.side == POSITIVE else lo, setup.side)
        ]
    distinct = {setup.id: setup for setup in setups}
    return sorted(distinct.values(), key=lambda setup: (setup.confirmed_at, setup.id), reverse=True)


def build_book(bars: list[Candle], opens: datetime) -> Structure:
    bars = contiguous_tail(bars)
    threes = aggregate(bars, 3, opens)
    tens = aggregate(bars, 10, opens)
    atr, atr3 = volatility(bars), volatility(threes)
    pivots = {side: swings(threes, side, duration=3, left=1) for side in (POSITIVE, NEGATIVE)}
    zones = {
        side: swing_zones(bars, swings(bars, side, left=1), side, STRONG_MOVE)
        for side in (POSITIVE, NEGATIVE)
    }
    trend = trend_context(threes, pivots)
    move = threes[-1].close - threes[-2].close if len(threes) >= 2 else None
    acceleration = (
        move - (threes[-2].close - threes[-3].close)
        if move is not None and len(threes) >= 3
        else None
    )
    bounds = established_range(bars, tens, atr)
    return Structure(
        opens,
        bars,
        threes,
        tens,
        pivots,
        zones,
        atr,
        atr3,
        move,
        acceleration,
        trend,
        bounds,
        directional_leg(threes),
        local_setups(opens, bars, threes, pivots, zones, trend, move, atr, bounds),
    )


@dataclass(frozen=True)
class StrikeConfirmation:
    entry: OIPair
    defense: OIPair
    entry_unwind: float | None
    defense_build: float | None
    rule: str | None

    @classmethod
    def check(cls, entry: OIPair, defense: OIPair, side: int) -> StrikeConfirmation:
        offer = entry.call if side == POSITIVE else entry.put
        wall = defense.put if side == POSITIVE else defense.call
        unwind = -offer.increase if offer else None
        buildup = wall.increase if wall else None
        rule = None
        # Require both contracts on both sides of each strike for context.
        # Entry unwind and adjacent build are the signed confirmation legs.
        if (
            entry.changes is not None
            and defense.changes is not None
            and unwind is not None
            and buildup is not None
            and min(unwind, buildup) > 0
            and max(unwind, buildup) >= OI_LEVEL_MATERIAL_CHANGE
        ):
            rule = "ENTRY_AND_DEFENSE_2_PERCENT"
        return cls(entry, defense, unwind, buildup, rule)

    @property
    def score(self) -> float:
        return (self.entry_unwind or 0) + (self.defense_build or 0)

    def public(self) -> dict:
        return {
            "entry_pair": self.entry.public(),
            "defense_pair": self.defense.public(),
            "entry_unwind_pct": self.entry_unwind * 100 if self.entry_unwind is not None else None,
            "defense_build_pct": self.defense_build * 100
            if self.defense_build is not None
            else None,
            "rule": self.rule,
        }


@dataclass(frozen=True)
class Choice:
    offset: int
    contract: dict
    signal: StrikeConfirmation


def chain_choices(
    side: int,
    grid: list[float],
    band: StrikeBand,
    pairs: dict[float, OIPair],
    contracts: dict,
    previous: dict[float, OIPair] | None,
) -> tuple[list[Choice], list[dict]]:
    center = grid.index(band.atm)
    choices, checks = [], []
    for offset in (-side, -2 * side):
        i = center + offset - side
        if offset not in band.pairs or not 0 <= i < len(grid):
            checks.append(
                {"offset": offset, "rule": None, "reason": "ENTRY_OR_DEFENSE_LISTING_UNAVAILABLE"}
            )
            continue
        entry, strike = band.pairs[offset], grid[i]
        adjacent = pairs.get(strike, OIPair(strike, None, None))
        result = StrikeConfirmation.check(entry, adjacent, side)
        if (
            not result.rule
            and previous
            and entry.changes is not None
            and adjacent.changes is not None
        ):
            old = StrikeConfirmation.check(
                previous.get(entry.strike, OIPair(entry.strike, None, None)),
                previous.get(strike, OIPair(strike, None, None)),
                side,
            )
            a, b, c, d = (
                result.entry_unwind,
                result.defense_build,
                old.entry_unwind,
                old.defense_build,
            )
            if (
                old.entry.changes is not None
                and old.defense.changes is not None
                and same_pair_contracts(entry, old.entry)
                and same_pair_contracts(adjacent, old.defense)
                and all(x is not None and x > 0 for x in (a, b, c, d))
                and max(1 - (1 - a) * (1 - c), (1 + b) * (1 + d) - 1) >= OI_LEVEL_MATERIAL_CHANGE
            ):
                result = replace(result, rule="TWO_CONSECUTIVE_WINDOWS_2_PERCENT")
        row = contracts.get(("CE" if side == POSITIVE else "PE", entry.strike))
        checks.append({"offset": offset, "strike": entry.strike, **result.public()})
        if row and result.rule:
            selected = entry.call if side == POSITIVE else entry.put
            if selected is not None and row["instrument_key"] == selected.row.key:
                choices.append(Choice(offset, row, result))
    return choices, checks


def same_pair_contracts(current: OIPair, previous: OIPair) -> bool:
    return all(
        newer and older and newer.row.key == older.row.key
        for newer, older in ((current.call, previous.call), (current.put, previous.put))
    )


def nearby_zones(
    book: Structure,
    spot: float,
    quote_at: datetime,
    now: datetime,
    band: StrikeBand,
    grid: list[float],
    pairs: dict[float, OIPair],
    listed: dict,
    quotes: dict,
    cfg: Config,
) -> list[dict]:
    armed = []
    for side, zones in book.zones.items():
        choices, _ = chain_choices(side, grid, band, pairs, listed, None)
        for zone in zones:
            if min(abs(spot - zone.price), abs(spot - zone.anchor.price)) > zone.tolerance:
                continue
            if not beyond(spot, zone.invalidation, side):
                continue
            usable = []
            for choice in choices:
                key = choice.contract["instrument_key"]
                try:
                    quote = live_contract(
                        choice.contract,
                        quotes.get(key),
                        now,
                        quote_at,
                        band,
                        choice.offset,
                        cfg,
                    )
                except (DataError, KeyError, TypeError, ValueError):
                    continue
                usable.append(quote)
            armed.append(
                {
                    "side": "CE" if side == POSITIVE else "PE",
                    "zone": jsonable(asdict(zone)),
                    "status": "WAITING_FOR_COMPLETED_LOCAL_CONFIRMATION",
                    "oi_aligned_strikes": [choice.signal.entry.strike for choice in choices],
                    "usable_quotes": usable,
                }
            )
    return armed


def watch_quote_keys(spot: float, grid: list[float], listed: dict) -> list[str]:
    if not grid or not grid[0] <= spot <= grid[-1]:
        return []
    center = grid.index(nearest_strike(grid, spot))
    # Allow the final index quote to move by one listed ATM strike. Final
    # eligibility is still validated from scratch after that quote arrives.
    return list(
        dict.fromkeys(
            listed[(kind, grid[center + offset])]["instrument_key"]
            for kind, offsets in (("CE", range(-3, 1)), ("PE", range(0, 4)))
            for offset in offsets
            if 0 <= center + offset < len(grid) and (kind, grid[center + offset]) in listed
        )
    )


def obstacle_leg(pair: OIPair, side: int) -> OIObservation | None:
    return pair.call if side == POSITIVE else pair.put


def opposing_oi(pair: OIPair, side: int) -> bool:
    """A growing, dominant opposing leg or material paired opposition."""
    if pair.changes is None:
        return False
    obstacle, other = (pair.call, pair.put) if side == POSITIVE else (pair.put, pair.call)
    assert obstacle is not None and other is not None
    return bool(
        pair.rule(-side)
        or (obstacle.row.oi >= other.row.oi and obstacle.increase >= OI_LEVEL_MATERIAL_CHANGE)
    )


@dataclass(frozen=True)
class PathEvidence:
    levels: list[dict]
    barriers: list[tuple[float, str]]
    unknown: list[float]

    def audit(self, spot: float, side: int) -> dict:
        return {
            "levels": self.levels,
            "barriers": [
                {"level": level, "distance": round(side * (level - spot), 4), "source": label}
                for level, label in self.barriers
            ],
            "unknown_strikes": self.unknown,
        }


def target_path(
    book: Structure,
    grid: list[float],
    pairs: dict[float, OIPair],
    spot: float,
    side: int,
    target: float,
) -> PathEvidence:
    def ahead(level: float) -> bool:
        return beyond(level, spot, side) and side * (target - level) >= 0

    levels, barriers, unknown = [], [], set()
    for strike in grid:
        if not ahead(strike):
            continue
        pair = pairs.get(strike, OIPair(strike, None, None))
        hostile = opposing_oi(pair, side)
        levels.append(pair.public() | {"opposing_oi": hostile})
        if pair.changes is None:
            unknown.add(strike)
        if hostile:
            barriers.append((strike, "OPPOSING_OI"))
    for zone in book.zones[-side]:
        if not ahead(zone.price):
            continue
        strike = nearest_strike(grid, zone.price)
        pair = pairs.get(strike, OIPair(strike, None, None))
        if pair.changes is None and zone.tests >= 2:
            unknown.add(strike)
        hostile = opposing_oi(pair, side)
        leg = obstacle_leg(pair, side)
        weakened = leg is not None and leg.increase <= -OI_LEVEL_MATERIAL_CHANGE
        # A repeatedly defended price zone can be cleared by material unwind
        # of the defending leg even if both legs fall in the same window.
        if hostile or (
            zone.tests >= 2 and pair.changes is not None and not pair.rule(side) and not weakened
        ):
            barriers.append(
                (zone.price, "PRICE_ZONE_WITH_OI_DEFENSE" if hostile else "REPEATED_PRICE_DEFENSE")
            )
    barriers.sort(key=lambda row: side * row[0])
    return PathEvidence(levels, barriers, sorted(unknown))


def targets(
    book: Structure, previous: list[Candle], pairs: dict[float, OIPair], spot: float, side: int
):
    structure = {
        swing.price
        for swing in swings(book.tens, -side, duration=10, left=1)
        + swings(previous, -side, duration=10, left=1)
    }
    oi = {strike for strike, pair in pairs.items() if opposing_oi(pair, side)}

    def choose(band: tuple[float, float]) -> tuple[float, str]:
        lo, hi = band
        center = (lo + hi) / 2
        ranked = [level for level in structure | oi if lo <= side * (level - spot) <= hi]
        if ranked:
            level = min(
                ranked,
                key=lambda p: (abs(side * (p - spot) - center), p not in structure, side * p),
            )
            return level, "10M_STRUCTURE" if level in structure else "OI_LEVEL"
        return round(spot + side * center, 4), "ENTRY_SPOT_DISTANCE"

    return choose(T1_SPOT_BAND), choose(T2_SPOT_BAND)


def plan_entry(
    setup: Setup,
    book: Structure,
    grid: list[float],
    pairs: dict[float, OIPair],
    previous: list[Candle],
    spot: float,
    spot_at: datetime,
    now: datetime,
    last_exit: datetime | None,
    cfg: Config,
) -> tuple[RiskPlan | None, dict]:
    side = setup.side
    gap = side * (spot - setup.level)
    (t1, first_source), (t2, second_source) = targets(book, previous, pairs, spot, side)
    path = target_path(book, grid, pairs, spot, side, t2)
    first_room = side * (t1 - spot)
    failures = []
    if setup.confirmed_at > spot_at:
        failures.append("INDEX_QUOTE_PREDATES_TRIGGER")
    if now > entry_deadline(setup.confirmed_at, book.opened):
        failures.append("TRIGGER_EXPIRED")
    if last_exit and setup.confirmed_at <= last_exit:
        failures.append("TRIGGER_PREDATES_POSITION_EXIT")
    if gap < 0:
        failures.append("PRICE_BACK_BEHIND_TRIGGER")
    if gap > cfg.initial_stop_points:
        failures.append("ENTRY_EXTENDED_FROM_TRIGGER")
    since = [bar for bar in book.bars if bar.start >= setup.confirmed_at]
    if not beyond(setup.exhausted_at, spot, side) or any(
        not beyond(setup.exhausted_at, edge(bar, side), side) for bar in since
    ):
        failures.append("FIRST_OBJECTIVE_ALREADY_TRAVELLED")
    if not beyond(spot, setup.invalidation, side) or any(
        held(since[i - 1 : i + 1], setup.invalidation, -side) for i in range(1, len(since))
    ):
        failures.append("PRICE_DEFENSE_INVALIDATED")
    leg = book.leg
    if leg and leg.side == side and leg.travel >= T2_SPOT_BAND[0]:
        completed_before_origin = [
            bar
            for bar in book.threes
            if leg.origin.at < bar.start and bar_end(bar, 3) <= setup.origin.at
        ]
        prior_prices = [side * bar.close for bar in completed_before_origin]
        required_reset = (
            cfg.initial_stop_points
            if setup.kind in ("REVERSAL", "EDGE_REJECTION")
            else T1_SPOT_BAND[0]
        )
        if (
            prior_prices
            and max(prior_prices) - side * leg.origin.price >= T2_SPOT_BAND[0]
            and max(prior_prices) - side * setup.origin.price < required_reset
        ):
            failures.append("EXTENDED_PARENT_LEG_WITHOUT_RESET")
    if any(side * (level - spot) < first_room for level, _ in path.barriers):
        failures.append("OPPOSING_LEVEL_BEFORE_T1")
    if any(side * (strike - spot) < first_room for strike in path.unknown):
        failures.append("TARGET_PATH_OI_UNAVAILABLE")
    initial_risk = cfg.initial_stop_points
    stop = round(spot - side * initial_risk, 4)
    reward = first_room / initial_risk
    if reward < cfg.min_reward_risk:
        failures.append("REWARD_RISK_BELOW_CONFIGURED_MINIMUM")
    plan = RiskPlan(
        stop, t1, t2, first_source, second_source, initial_risk, reward, "LIVE_SPOT_FIXED_DISTANCE"
    )
    return (None if failures else plan), setup.audit() | {
        "failed_checks": failures,
        "distance_from_trigger": round(gap, 4),
        "distance_to_known_barrier": (
            round(side * (path.barriers[0][0] - spot), 4) if path.barriers else None
        ),
        "target_path": path.audit(spot, side),
        "plan": asdict(plan),
    }


def consider_entry(
    result: dict,
    state: dict,
    engine: dict,
    cfg: Config,
    book: Structure,
    band: StrikeBand,
    grid: list[float],
    pairs: dict[float, OIPair],
    listed: dict,
    previous_pairs: dict[float, OIPair] | None,
    window: OIWindow,
    prior: list[Candle],
    spot: float,
    quote_at: datetime,
    now: datetime,
    initial_atm: float | None,
    fresh_book: dict,
) -> str:
    # Both directional reads run even inside ranges and while a position is
    # open. Only the entry gate can use an eligible, executable option quote.
    choices = {}
    result["strike_checks"] = {}
    for side, kind in ((POSITIVE, "CE"), (NEGATIVE, "PE")):
        choices[side], result["strike_checks"][kind] = chain_choices(
            side,
            grid,
            band,
            pairs,
            listed,
            previous_pairs,
        )
    entered = engine.setdefault("v139_entered", [])
    last_exit = timestamp(state["last_exit"]["at"]) if state.get("last_exit") else None
    eligible = []
    for setup in book.setups:
        plan, assessment = plan_entry(
            setup,
            book,
            grid,
            pairs,
            prior,
            spot,
            quote_at,
            now,
            last_exit,
            cfg,
        )
        failures = assessment["failed_checks"]
        result["evaluations"].append(assessment)
        if setup.id in entered:
            failures.append("TRIGGER_ALREADY_ALERTED")
        if state.get("position"):
            failures.append("ACTIVE_REFERENCE_POSITION")
        if not choices[setup.side]:
            failures.append("ENTRY_AND_DEFENSE_OI_NOT_ALIGNED")
        if failures or plan is None:
            continue
        assessment["quote_checks"] = []
        for choice in choices[setup.side]:
            key = choice.contract["instrument_key"]
            check = {"instrument_key": key, "strike": choice.signal.entry.strike}
            assessment["quote_checks"].append(check)
            try:
                contract = live_contract(
                    choice.contract,
                    fresh_book.get(key),
                    now,
                    quote_at,
                    band,
                    choice.offset,
                    cfg,
                )
            except (DataError, KeyError, ValueError, TypeError) as exc:
                check["reason"] = str(exc)
                continue
            check["reason"] = "QUALIFIED_QUOTE"
            contract["oi_confirmation"] = choice.signal.public()
            rank = (
                -setup.confirmed_at.timestamp(),
                abs(assessment["distance_from_trigger"]),
                -choice.signal.score,
                contract["spread_pct"],
                -contract["depth_lots"],
                abs(choice.offset),
                setup.id,
                key,
            )
            eligible.append((rank, setup, plan, contract))
        if not any(
            check.get("reason") == "QUALIFIED_QUOTE" for check in assessment["quote_checks"]
        ):
            failures.append("DIRECTIONAL_OPTION_QUOTES_UNAVAILABLE")

    if not eligible:
        if result["evaluations"]:
            # Prefer a timed, directionally aligned candidate when reporting
            # why no alert could be sent.
            return min(
                (row for row in result["evaluations"] if row["failed_checks"]),
                key=lambda row: (
                    len(row["failed_checks"]),
                    -timestamp(row["confirmed_at"]).timestamp(),
                ),
            )["failed_checks"][0]
        return "INTACT_RANGE" if book.range_bounds else "WATCHING_LEVELS_WITHOUT_TRIGGER"
    if len({setup.side for _, setup, _, _ in eligible}) > 1:
        return "CONFLICTING_QUALIFIED_DIRECTIONS"
    _, setup, risk, contract = min(eligible, key=lambda row: row[0])
    key = contract["instrument_key"]
    position = {
        "id": hashlib.sha256(f"{setup.id}|{key}".encode()).hexdigest()[:22],
        "status": "OPEN",
        "direction": "BULLISH" if setup.side == POSITIVE else "BEARISH",
        "side": contract["side"],
        "strike": contract["strike"],
        "expiry": contract["expiry"],
        "instrument_key": key,
        "opened_at": now.isoformat(),
        "entry_spot": spot,
        "entry_ask": contract["ask"],
        "initial_stop": risk.stop,
        "defense_strike": contract["oi_confirmation"]["defense_pair"]["strike"],
        "setup_level": setup.level,
        "setup_invalidation": setup.invalidation,
        "policy_version": VERSION,
        "last_candle": book.bars[-1].start.isoformat(),
        "scenario": setup.kind,
        "t1_hit": False,
        "remaining_pct": 100,
        "contract": contract,
        **asdict(risk),
    }
    if cfg.arm_continuation_runner:
        position["runner"] = {"armed_at": now.isoformat(), "checkpoint": risk.t2}
    state["position"] = position
    entered.append(setup.id)
    facts = {
        "index_quote_at": quote_at.isoformat(),
        "option_quote_at": contract["quote_time"],
        "first_break_at": setup.confirmed_at.isoformat(),
        "candle_through": book.through.isoformat(),
        "oi_snapshot_at": window.snapshot.at.isoformat(),
        "initial_atm": initial_atm,
        "final_atm": band.atm,
    }
    event = position_event_payload(
        position,
        now,
        reason="QUALIFIED_PRICE_AND_3M_OI",
        signal=setup.audit(),
        plan=asdict(risk),
        entry_evidence=facts,
        oi={"window": result["oi"], "entry_and_defense": contract["oi_confirmation"]},
    )
    result["alerts_created"].append(new_event(state, "ENTRY", event, now))
    result.update(
        decision="ENTRY",
        reason="QUALIFIED_" + contract["side"],
        position_locked=True,
        selected_position=position,
        entry_evidence=facts,
    )
    return result["reason"]


def manage_position(
    initial: dict,
    price: ClosedPrice,
    book: Structure | None,
    spot: float | None,
    spot_at: datetime | None,
    now: datetime,
    deadline: datetime,
    cfg: Config,
    previous: list[Candle],
    directional_oi: bool,
    grid: list[float] | None = None,
    pairs: dict[float, OIPair] | None = None,
):
    position = copy.deepcopy(initial)
    side = 1 if position["direction"] == "BULLISH" else -1
    opened = timestamp(position["opened_at"])
    cursor = max(timestamp(position["last_candle"]) + MINUTE, exact_minute(opened))
    events, warnings = [], []
    pivots = {p.known_at: p for p in book.pivots3[side]} if book else {}
    blocks = {bar_end(b, 3): i for i, b in enumerate(book.threes)} if book else {}

    def emit(kind, at, **data):
        events.append((kind, position_event_payload(position, at, **data)))

    def close(kind, at, reason, level, source, spot_value):
        position["remaining_pct"] = 0
        emit(
            kind,
            at,
            reason=reason,
            underlying_reference=level,
            source=source,
            email_observation={
                "spot": spot_value,
                "spot_is_close": source.startswith(("COMPLETED_1M", "COMPLETED_3M")),
            },
        )
        return (
            None,
            events,
            close_reference(position, at, reason, level, source),
            warnings,
        )

    for bar in price.bars:
        at = bar_end(bar)
        if bar.start < cursor:
            continue
        if at > min(now, deadline):
            break
        if bar.start != cursor:
            warnings.append("GAP_IN_UNOBSERVED_POSITION_BARS")
            break
        stop, t2 = position["stop"], position["t2"]
        adverse, favorable = defense(bar, side), edge(bar, side)
        observation = {"spot": bar.close, "spot_is_close": True, "stop": stop, "t2": t2}
        modified = position.get("adjusted_at")
        if bar.start < opened:
            if not beyond(adverse, stop, side) or not beyond(position["t1"], favorable, side):
                warnings.append("ENTRY_MINUTE_TOUCH_SEQUENCE_UNKNOWN")
            adverse = favorable = bar.close
        elif modified and bar.start < timestamp(modified) < at:
            old_stop = position.get("stop_before_adjustment", stop)
            if not beyond(adverse, old_stop, side):
                warnings.append("STOP_ADJUSTMENT_MINUTE_LEVEL_UNCERTAIN")
                return close(
                    "EXIT",
                    at,
                    "STRUCTURAL_SL",
                    old_stop,
                    "COMPLETED_1M_OLD_STOP_BREACHED",
                    bar.close,
                )
            if not beyond(adverse, stop, side):
                warnings.append("STOP_ADJUSTMENT_MINUTE_TOUCH_SEQUENCE_UNKNOWN")
            adverse = bar.close
            if t2 != position.get("t2_before_adjustment", t2):
                warnings.append("TARGET_ADJUSTMENT_MINUTE_TOUCH_SEQUENCE_UNKNOWN")
                favorable = bar.close
        hit_t1 = not position.get("t1_hit") and side * (favorable - position["t1"]) >= 0
        hit_t2 = side * (favorable - t2) >= 0
        if not beyond(adverse, stop, side):
            if hit_t1 or hit_t2:
                warnings.append("SAME_MINUTE_STOP_TARGET_SEQUENCE_UNKNOWN_STOP_FIRST")
            return close("EXIT", at, "STRUCTURAL_SL", stop, "COMPLETED_1M_STOP_TOUCH", bar.close)
        if hit_t1:
            position.update(
                t1_hit=True,
                t1_at=at.isoformat(),
                remaining_pct=100 - position.get("t1_exit_pct", 50),
            )
            emit(
                "T1",
                at,
                old_stop=stop,
                new_stop=stop,
                underlying_reference=position["t1"],
                source="COMPLETED_1M_TARGET_TOUCH",
                email_observation=observation,
            )
        if hit_t2 and position.get("t1_hit"):
            return close(
                "T2",
                at,
                "SPOT_TARGET_REACHED",
                t2,
                "COMPLETED_1M_TARGET_TOUCH",
                bar.close,
            )

        # A buffered, confirmed pivot can protect the remainder once both
        # its formation and its confirmation happened after the partial exit.
        pivot = pivots.get(at)
        if position.get("t1_at") and pivot and pivot.at >= timestamp(position["t1_at"]):
            # Use volatility observed at this pivot, rather than a value
            # computed using bars from later in the decision batch.
            atr = volatility([b for b in price.bars if bar_end(b) <= at], minimum=2.5)
            atr3 = volatility([b for b in book.threes if bar_end(b, 3) <= at], minimum=2.5)
            candidate = round(pivot.price - side * stop_buffer(atr, atr3), 4)
            if beyond(candidate, stop, side) and beyond(
                bar.close, candidate, side, max(2.0, 0.30 * atr)
            ):
                position.update(
                    stop=candidate,
                    adjusted_at=at.isoformat(),
                    stop_before_adjustment=stop,
                    t2_before_adjustment=t2,
                    protective_swing=jsonable(asdict(pivot)),
                )
                emit(
                    "ADJUST_SL",
                    at,
                    reason="CONFIRMED_POST_T1_SWING",
                    old_stop=stop,
                    new_stop=candidate,
                    old_t2=t2,
                    new_t2=t2,
                    email_observation={"spot": bar.close, "spot_is_close": True},
                )
        invalidation = position.get("setup_invalidation")
        block = blocks.get(at, 0)
        if (
            position.get("policy_version") in ("138.0.0", VERSION)
            and invalidation is not None
            and block >= 1
        ):
            last = [b for b in price.bars if opened <= b.start and bar_end(b) <= at][-2:]
            if held(last, invalidation, -side) and beyond(
                book.threes[block].close, book.threes[block - 1].close, -side
            ):
                return close(
                    "EXIT",
                    at,
                    "CONFIRMED_ZONE_REVERSAL",
                    bar.close,
                    "COMPLETED_3M_PRICE_INVALIDATION",
                    bar.close,
                )
        position["last_candle"] = bar.start.isoformat()
        cursor = at

    if spot is not None and spot_at is not None and opened <= spot_at <= min(now, deadline):
        modified = position.get("adjusted_at")
        if (not modified or spot_at >= timestamp(modified)) and not beyond(
            spot, position["stop"], side
        ):
            return close(
                "EXIT",
                spot_at,
                "STRUCTURAL_SL",
                position["stop"],
                "FRESH_INDEX_QUOTE",
                spot,
            )
    if now >= deadline:
        return close("EXIT", deadline, "SESSION_REFERENCE_EXIT", spot, "SESSION_CUTOFF", spot)

    # Extend only before the original objective is touched, when a verified
    # post-T1 swing protects the remainder and current OI still confirms.
    if (
        book
        and cfg.arm_continuation_runner
        and position.get("runner")
        and position.get("protective_swing")
        and position.get("t1_hit")
        and directional_oi
        and grid
        and pairs
        and book.move3 is not None
        and side * book.move3 > 0
        and book.trend == side
        and spot is not None
        and spot_at is not None
        and position["last_candle"] == book.bars[-1].start.isoformat()
        and position.get("t2_source") != "RUNNER_STRUCTURE"
    ):
        old = position["t2"]
        new_levels = {
            value
            for b in book.tens + previous
            for value in (edge(b, side), b.close)
            if beyond(value, old, side, max(5.0, 0.40 * book.atr))
            and max(12.0, 0.8 * book.atr3) <= side * (value - spot) <= max(45.0, 2.2 * book.atr3)
        }
        near = max(12.0, book.atr)
        if (
            new_levels
            and 0 < side * (old - spot) <= near
            and beyond(position["stop"], position["entry_spot"], side)
            and timestamp(position["protective_swing"]["known_at"]) <= spot_at <= now
        ):
            new = min(new_levels, key=lambda x: side * x)
            path = target_path(book, grid, pairs, spot, side, new)
            if path.unknown or any(beyond(new, level, side) for level, _ in path.barriers):
                return position, events, None, warnings
            position.update(
                t2=new,
                t2_source="RUNNER_STRUCTURE",
                adjusted_at=now.isoformat(),
                stop_before_adjustment=position["stop"],
                t2_before_adjustment=old,
            )
            emit(
                "ADJUST_SL",
                now,
                reason="RUNNER_TARGET_EXTENDED",
                old_stop=position["stop"],
                new_stop=position["stop"],
                old_t2=old,
                new_t2=new,
                email_observation={"spot": spot},
            )
    return position, events, None, warnings


class ScanClock:
    def __init__(self, read=None, sink=None):
        self.read = read or (lambda: datetime.now(IST))
        self.sink = sink
        self.samples: list[str] = []
        self.last: datetime | None = None

    def __call__(self) -> datetime:
        value = self.read()
        if value.tzinfo is None:
            raise DataError("Scan clock requires a timezone")
        value = value.astimezone(IST)
        if self.last is not None and value < self.last:
            raise DataError("Scan clock moved backward")
        self.last = value
        self.samples.append(value.isoformat())
        if self.sink is not None:
            self.sink.append(self.samples[-1])
        return value


def add_position_events(
    state: dict, result: dict, cfg: Config, position, events, closed, warnings, now
) -> None:
    result["management_warnings"] = warnings
    for kind, detail in events:
        result["alerts_created"].append(new_event(state, kind, detail, now))
    if closed is not None:
        state["history"] = (state["history"] + [closed])[-cfg.max_state_history :]
        state["last_exit"] = {
            "at": closed["closed_at"],
            "direction": closed["direction"],
            "id": closed["id"],
            "reason": closed["exit_reason"],
        }
    state["position"] = position
    result["position_locked"] = position is not None
    result["decision"] = "POSITION_CLOSED" if closed else "POSITION_OPEN"
    result["reason"] = closed["exit_reason"] if closed else "REFERENCE_POSITION_MANAGED"


def capture_price(
    price: ClosedPrice, api, clock: ScanClock, session, cfg: Config, result: dict
) -> ClosedPrice:
    try:
        raw = api.candles()
        return merge_closed_price(price, raw, clock(), session, cfg)
    except (DataError, ProviderError) as exc:
        result["candle_error"] = str(exc)
        return price


def capture_oi(
    api, engine: dict, clock: ScanClock, cfg: Config, result: dict
) -> tuple[list[dict], OIWindow | None]:
    contracts = []
    try:
        expiry, contracts = api.contracts(clock.last.date())
        chain = api.chain(expiry, contracts)
        received = clock()
        slot = exact_minute(received - timedelta(seconds=cfg.feed_grace_seconds))
        sample = make_oi_snapshot(chain, expiry, received, slot)
        ring = engine["oi_samples"]
        window = match_oi(ring, sample, cfg)
        retained = [s for s in ring if received - timestamp(s["at"]) < 15 * MINUTE]
        if not any(s["through"] == slot.isoformat() and s["expiry"] == expiry for s in retained):
            retained.append(jsonable(asdict(sample)))
        engine["oi_samples"] = retained[-8:]
        result["oi"] = {
            "status": "MATCHED" if window else "OI_WINDOW_UNAVAILABLE",
            "at": sample.at.isoformat(),
            "through": slot.isoformat(),
            "expiry": expiry,
            "baseline": window.baseline.isoformat() if window else None,
            "matched_contracts": len(window.changes) if window else 0,
        }
        return contracts, window
    except (DataError, ProviderError, KeyError, ValueError, TypeError) as exc:
        clock()
        result["oi"] = {"status": "OPTION_CHAIN_UNAVAILABLE", "reason": str(exc)}
        return contracts, None


def scan(state: dict, api, cfg: Config, clock_fn=None, clock_sink: list | None = None):
    clock = ScanClock(clock_fn, clock_sink)
    now = clock()
    engine = ensure_engine(state, now)
    active = state.get("position")
    result = {
        "version": VERSION,
        "at": now.isoformat(),
        "session_date": now.date().isoformat(),
        "decision": "NO_TRADE",
        "reason": "UNSET",
        "alerts_created": [],
        "position_locked": bool(active),
        "evaluations": [],
    }

    def finish(reason):
        if result["decision"] in ("POSITION_OPEN", "POSITION_CLOSED"):
            result["entry_check"] = reason
        else:
            result["reason"] = reason
        return result, clock.samples

    hard_exit = day_time(now, *HARD_EXIT)
    if active and timestamp(active["opened_at"]).date() < now.date():
        cutoff = day_time(timestamp(active["opened_at"]), *HARD_EXIT)
        closed = close_reference(
            active,
            cutoff,
            "PRIOR_SESSION_REFERENCE_EXPIRED",
            None,
            "CLOCK_NO_PRIOR_SESSION_FILL",
        )
        event = (
            "EXIT",
            position_event_payload(
                active,
                now,
                reason=closed["exit_reason"],
                effective_at=cutoff.isoformat(),
            ),
        )
        add_position_events(state, result, cfg, None, [event], closed, [], now)
        return result, clock.samples
    if now >= hard_exit and not active:
        return finish("AFTER_SESSION_EXIT_CUTOFF")
    try:
        session = api.session(now)
    except (DataError, ProviderError) as exc:
        session = None
        result["session_failure"] = str(exc)
    now = clock()
    if session is None:
        if active and now >= hard_exit:
            values = manage_position(
                active,
                ClosedPrice([]),
                None,
                None,
                None,
                now,
                hard_exit,
                cfg,
                [],
                False,
            )
            add_position_events(state, result, cfg, *values, now)
            return result, clock.samples
        if active:
            result["decision"] = "POSITION_MONITORING_UNAVAILABLE"
        return finish("NO_VERIFIED_NFO_SESSION")
    opens, closes = session
    deadline = min(hard_exit, closes)

    price = ClosedPrice([])
    try:
        price = merge_closed_price(price, engine.get("closed_candles", []), now, session, cfg)
    except DataError as exc:
        result["candle_cache_error"] = str(exc)
    price = capture_price(price, api, clock, session, cfg, result)
    old_oi = engine["oi_samples"][:]
    contracts, window = (
        capture_oi(api, engine, clock, cfg, result) if clock.last < deadline else ([], None)
    )
    expected = exact_minute(clock.last - timedelta(seconds=cfg.feed_grace_seconds))
    if price.through != expected and clock.last + timedelta(seconds=8) < deadline:
        price = capture_price(price, api, clock, session, cfg, result)
    engine["closed_candles"] = [serialize_bar(b) for b in price.bars]
    book = build_book(price.bars, opens) if price.bars else None
    prior = prior_context(engine, api, clock.last) if book else []
    grid = listed_strikes(contracts)
    pairs = paired_oi(window)
    listed = {
        (row["instrument_type"], float(row["strike_price"])): row
        for row in contracts
        if not window or row["expiry"] == window.snapshot.expiry
    }
    previous = None
    if window and cfg.allow_persistent_oi:
        prior_raw = next(
            (
                x
                for x in reversed(old_oi)
                if timestamp(x["at"]) == window.baseline and x["expiry"] == window.snapshot.expiry
            ),
            None,
        )
        if prior_raw:
            previous = paired_oi(match_oi(old_oi, OISnapshot.restore(prior_raw), cfg))

    def index_quote(quotes, now):
        quote = quotes.get(INDEX)
        return checked_quote(quote, now, cfg.quote_max_age_seconds), timestamp(quote["timestamp"])

    spot = quote_at = None
    try:
        q = api.quotes([INDEX])
        spot, quote_at = index_quote(q, clock())
    except (DataError, ProviderError, KeyError) as exc:
        result["index_quote_error"] = str(exc)
    now = clock()
    initial_atm = (
        StrikeBand.build(grid, spot, pairs).atm
        if spot is not None and grid and grid[0] <= spot <= grid[-1]
        else None
    )
    orders = (
        watch_quote_keys(spot, grid, listed)
        if book
        and spot is not None
        and now < deadline
        and listed
        and window
        and (
            book.setups
            or any(
                min(abs(spot - zone.price), abs(spot - zone.anchor.price)) <= zone.tolerance
                for zones in book.zones.values()
                for zone in zones
            )
        )
        else []
    )
    fresh_book = {}
    if orders:
        try:
            q = api.quotes([INDEX, *orders])
            final_spot, final_at = index_quote(q, clock())
            if final_at < quote_at:
                raise DataError("FINAL_INDEX_QUOTE_MOVED_BACKWARD")
            spot, quote_at, fresh_book = final_spot, final_at, q
        except (DataError, ProviderError, KeyError) as exc:
            result["book_error"] = str(exc)
    now = clock()
    if quote_at is not None and (now - quote_at).total_seconds() > cfg.quote_max_age_seconds:
        spot = quote_at = None
    expected = exact_minute(now - timedelta(seconds=cfg.feed_grace_seconds))
    result["candle_coverage"] = price.audit(expected)
    if window and (now - window.snapshot.at).total_seconds() > cfg.quote_max_age_seconds:
        window, previous, pairs = None, None, {}
        result["oi"]["status"] = "STALE_AT_DECISION"
    if window:
        result["oi"]["candle_through_at_decision"] = (
            price.through.isoformat() if price.through else None
        )
    band = StrikeBand.build(grid, spot, pairs) if spot is not None else None
    result["watch_quote_capture"] = {
        "requested_option_count": len(orders),
        "returned_option_count": sum(k in fresh_book for k in orders),
        "initial_atm": initial_atm,
        "final_atm": band.atm if band else None,
    }

    if active:
        confirms = False
        if (
            window
            and active.get("defense_strike") is not None
            and active["expiry"] == window.snapshot.expiry
        ):
            ds, es = active["defense_strike"], active["strike"]
            strength = StrikeConfirmation.check(
                pairs.get(es, OIPair(es, None, None)),
                pairs.get(ds, OIPair(ds, None, None)),
                POSITIVE if active["side"] == "CE" else NEGATIVE,
            )
            result["active_defense_oi"] = strength.public()
            confirms = bool(strength.rule)
        values = manage_position(
            active, price, book, spot, quote_at, now, deadline, cfg, prior, confirms, grid, pairs
        )
        add_position_events(state, result, cfg, *values, now)
        if values[0] and spot is None and not price.bars:
            result.update(
                decision="POSITION_MONITORING_UNAVAILABLE",
                reason="PRICE_FEED_UNAVAILABLE",
            )

    if book is None:
        return finish("NO_COMPLETED_SESSION_CANDLES")
    result["market_assessment"] = {
        "state": book.regime(band),
        "through": book.through.isoformat(),
        "spot": spot,
        "index_quote_at": quote_at.isoformat() if quote_at else None,
        "move_3m": book.move3,
        "acceleration_3m": book.acceleration,
        "range": book.range_bounds,
        "directional_leg": jsonable(asdict(book.leg)) if book.leg else None,
        "strike_band": band.public() if band else None,
        "support": [jsonable(asdict(zone)) for zone in book.zones[POSITIVE][-12:]],
        "resistance": [jsonable(asdict(zone)) for zone in book.zones[NEGATIVE][-12:]],
        "candidates": [setup.audit() for setup in book.setups],
        "armed_zones": nearby_zones(
            book,
            spot,
            quote_at,
            now,
            band,
            grid,
            pairs,
            listed,
            fresh_book,
            cfg,
        )
        if spot is not None and quote_at is not None and band is not None and window is not None
        else [],
    }
    if now < max(day_time(now, *ENTRY_START), opens + 6 * MINUTE):
        return finish("COLLECTING_OPENING_BASELINE")
    if not price.covers_entry(expected) or price.tail_size < 6:
        return finish("CLOSED_PRICE_UNAVAILABLE_FOR_ENTRY")
    if spot is None:
        return finish("INDEX_QUOTE_UNAVAILABLE_FOR_ENTRY")
    if now >= min(day_time(now, *ENTRY_END), deadline - 10 * MINUTE):
        return finish("OUTSIDE_ENTRY_WINDOW")

    if window is None or band is None:
        return finish("MATCHED_OI_OR_STRIKE_GRID_UNAVAILABLE")
    reason = consider_entry(
        result,
        state,
        engine,
        cfg,
        book,
        band,
        grid,
        pairs,
        listed,
        previous,
        window,
        prior,
        spot,
        quote_at,
        now,
        initial_atm,
        fresh_book,
    )
    if result["decision"] == "ENTRY":
        return result, clock.samples
    return finish(reason)


def email_price(value: Any, pattern: str) -> str:
    try:
        number = read_number(value, "email price", positive=True)
    except (DataError, OverflowError):
        return "Unavailable"
    return format(number, pattern).rstrip("0").rstrip(".")


def mail_content(event: dict) -> tuple[str, str]:
    details = event.get("details") or {}
    position = details.get("position") or {}
    observation = event.get("email_observation") or {}
    kind = event["kind"]
    reason = details.get("reason")

    event_time = None
    for value in (
        details.get("effective_at"),
        details.get("observed_at"),
        event.get("created_at"),
    ):
        try:
            event_time = timestamp(value)
            break
        except DataError:
            continue
    short_time = event_time.strftime("%I:%M %p").lstrip("0") if event_time else "Unavailable"
    full_time = "Unavailable"
    if event_time:
        date_text = event_time.strftime("%d %b %Y")
        clock_text = event_time.strftime("%I:%M:%S %p").lstrip("0")
        full_time = f"{date_text}, {clock_text} IST"

    side = position.get("side")
    strike = email_price(position.get("strike"), ".2f")
    contract = f"{strike} {side}" if side in ("CE", "PE") else strike
    premium = email_price(position.get("entry_ask"), ".2f")
    spot = observation.get("spot")
    if kind == "ENTRY":
        spot = position.get("entry_spot")
    elif not observation and (
        (kind in ("EXIT", "T2") and details.get("source") == "FRESH_INDEX_QUOTE")
        or (kind == "EXIT" and reason == "CONFIRMED_ZONE_REVERSAL")
    ):
        spot = details.get("underlying_reference")
    spot_text = email_price(spot, ",.4f")
    if observation.get("spot_is_close"):
        spot_text += " (1-minute candle close)"

    if kind == "EXIT":
        subject_label, status = {
            "STRUCTURAL_SL": ("SL HIT", "SL Hit"),
            "SESSION_REFERENCE_EXIT": ("Session exit", "Session exit"),
            "PRIOR_SESSION_REFERENCE_EXPIRED": ("Session exit", "Session exit"),
            "CONFIRMED_ZONE_REVERSAL": ("Reversal exit", "Reversal exit"),
            "RUNNER_CONTINUATION_NOT_CONFIRMED": (
                "Runner exit",
                "Runner continuation unconfirmed",
            ),
        }.get(reason, ("Exit", "Exited"))
    elif kind == "ADJUST_SL":
        status = (
            "T2 updated"
            if reason in ("T2_REFINED_AFTER_T1", "RUNNER_TARGET_EXTENDED")
            else "SL adjusted"
        )
        subject_label = status
    else:
        subject_label, status = {
            "ENTRY": ("Entry", "Selected"),
            "T1": ("Target - T1", "T1 reached"),
            "T2": ("Target T2", "T2 reached"),
        }[kind]
    subject = f"{subject_label} | {contract} @ {premium} - Time: {short_time}"

    t1 = email_price(position.get("t1"), ",.4f")
    t2 = email_price(observation.get("t2", position.get("t2")), ",.4f")
    stop = email_price(observation.get("stop", position.get("stop")), ",.4f")
    fields = [
        f"NIFTY Spot: {spot_text}",
        f"Strike: {contract}",
        f"Option price at selection: {premium}",
        f"T1 (underlying): {t1}",
        f"T2 (underlying): {t2}",
        f"SL (underlying): {stop}",
    ]
    touch = observation.get("target_touch_extreme")
    if kind in ("T1", "T2") and touch in ("high", "low", "close"):
        trigger_spot = email_price(observation.get("target_touch_spot"), ",.4f")
        fields.append(f"Target touch: {trigger_spot} (1-minute {touch})")
    if kind == "T1" and details.get("old_stop") is not None and details.get("new_stop") is not None:
        previous = email_price(details["old_stop"], ",.4f")
        updated = email_price(details["new_stop"], ",.4f")
        if details["old_stop"] == details["new_stop"]:
            fields.append(f"SL retained for remaining position: {updated}")
        else:
            fields.append(f"SL adjustment for remaining position: {previous} -> {updated}")
    runner = position.get("runner")
    if runner and kind == "ENTRY":
        fields.append(
            "After T1: the remaining position can continue through the initial T2 checkpoint"
        )
    if kind == "T1":
        fields.append(f"Remaining reference position: {position.get('remaining_pct', 50)}%")
    fields.extend(
        (
            f"Status: {status}",
            f"Timestamp: {full_time}",
        )
    )
    return subject, "\n".join(fields)


def arm_delivery(state: dict, token: str, now: datetime) -> int:
    if not token:
        raise ScannerError("Notification claim token required")
    count = 0
    for e in state["outbox"]:
        if (
            e.get("kind") in ALERT_KINDS
            and e.get("status") == "CLAIMED"
            and e.get("claim") == token
        ):
            # MUST be COMMITTED and PUSHED before the first SMTP socket.
            e.update(
                status="DELIVERY_UNCERTAIN",
                attempted_at=now.isoformat(),
                smtp_stage="ARMED_NO_NETWORK",
            )
            count += 1
    return count


def deliver_armed(state: dict, path: Path, token: str) -> int:
    if not token:
        raise ScannerError("NOTIFICATION_CLAIM_TOKEN required")
    pending = [
        x
        for x in state["outbox"]
        if x.get("status") == "DELIVERY_UNCERTAIN"
        and x.get("smtp_stage") == "ARMED_NO_NETWORK"
        and x.get("claim") == token
        and x.get("kind") in ALERT_KINDS
    ]
    if not pending:
        return 0
    sender = os.environ.get("EMAIL_SENDER", "")
    receiver = os.environ.get("EMAIL_RECEIVER", "")
    password = os.environ.get("EMAIL_PASSWORD", "")
    username = os.environ.get("EMAIL_USERNAME") or sender
    host = os.environ.get("SMTP_HOST", "smtp.gmail.com")
    port = int(os.environ.get("SMTP_PORT", "465"))
    if not (sender and receiver and password and username):
        raise ScannerError("SMTP secrets missing; claims remain safe and undelivered")
    unknown = False
    for e in pending:
        title, body = mail_content(e)
        m = EmailMessage()
        m["From"] = sender
        m["To"] = receiver
        m["Subject"] = title
        m["Message-ID"] = "<" + e["id"] + "@" + sender.rsplit("@", 1)[-1] + ">"
        m.set_content(body)
        # Remote state was already ARMED and committed by the workflow.
        # Update local state to record execution; no automatic retry after crash.
        e.update(smtp_stage="LOCAL_SEND_STARTED")
        save_state(path, state)
        try:
            with smtplib.SMTP_SSL(
                host, port, timeout=20, context=ssl.create_default_context()
            ) as client:
                e["smtp_stage"] = "AUTHENTICATE"
                client.login(username, password)
                e["smtp_stage"] = "SEND"
                client.send_message(m)
            e.update(
                status="SENT",
                sent_at=datetime.now(IST).isoformat(),
                smtp_stage="ACCEPTED_BY_SMTP",
            )
        except (OSError, smtplib.SMTPException) as exc:
            e.update(status="DELIVERY_UNCERTAIN", smtp_error_type=type(exc).__name__)
            unknown = True
        save_state(path, state)
    return 1 if unknown else 0


def paths() -> tuple[Path, Path]:
    return Path(os.environ.get("STATE_FILE", "state/market_state_v120_3.json")), Path(
        os.environ.get("AUDIT_DIR", "audit")
    )


def environment_config() -> Config:
    try:
        raw = json.loads((os.environ.get("NIFTY_SCANNER_CONFIG") or "{}"))
    except json.JSONDecodeError as exc:
        raise ScannerError("Invalid NIFTY_SCANNER_CONFIG JSON") from exc
    if not isinstance(raw, dict):
        raise ScannerError("Configuration must be JSON object")
    for legacy in (
        "oi_entry_floor_bps",
        "oi_entry_ceiling_bps",
        "min_stop_atr",
        "max_stop_atr",
        "max_unretested_leg_atr",
        "cooldown_minutes",
        "allow_atm_reversal",
        "reversal_strike_stop",
        "max_chase_atr",
        "max_initial_risk_points",
    ):
        raw.pop(legacy, None)
    # v133 stored these values as defaults in some deployed configurations.
    # Explicit non-default overrides still apply.
    if raw.get("min_reward_risk") == 1.25:
        raw.pop("min_reward_risk")
    if "t1_min_reward_risk" in raw:
        raw["min_reward_risk"] = raw.pop("t1_min_reward_risk")
    try:
        return Config(**raw)
    except TypeError as exc:
        raise ScannerError("Unknown scanner configuration fields") from exc


def recorded_scan(
    state: dict,
    provider,
    cfg: Config,
    audit_dir: Path,
    token: str,
    replay_clock=None,
    capture=True,
) -> dict:
    actor = RecordingProvider(provider) if capture else provider
    before = json.dumps(state, sort_keys=True, allow_nan=False, separators=(",", ":"))
    before_hash = hashlib.sha256(before.encode()).hexdigest()
    observations = []
    clock = None
    if replay_clock is not None:
        itr = iter(replay_clock)

        def clock():
            try:
                return timestamp(next(itr))
            except StopIteration as exc:
                raise ScannerError("REPLAY_CLOCK_SAMPLES_EXHAUSTED") from exc

    failure = None
    try:
        result, _ = scan(state, actor, cfg, clock_fn=clock, clock_sink=observations)
    except (
        ScannerError,
        DataError,
        ProviderError,
        KeyError,
        ValueError,
        TypeError,
        IndexError,
        OverflowError,
    ) as exc:
        failure = exc
        result = {
            "version": VERSION,
            "decision": "ERROR",
            "reason": type(exc).__name__,
            "detail": str(exc),
            "at": datetime.now(IST).isoformat(),
            "position_locked": bool(state.get("position")),
        }
    now = datetime.now(IST) if not observations else timestamp(observations[0])
    scan_state_hash = hashlib.sha256(
        json.dumps(state, sort_keys=True, allow_nan=False, separators=(",", ":")).encode()
    ).hexdigest()
    # Even on upstream failure, preserve the open position and all queued
    # lifecycle events; never regenerate a missing state from scratch.
    claim_outbox(state, token, now)
    event = {
        "mode": "LIVE",
        "event": "SCAN",
        "at": now.isoformat(),
        "version": VERSION,
        "before_state_sha256": before_hash,
        "result": result,
        "alerts_pending": [
            x["id"]
            for x in state["outbox"]
            if x.get("status") == "CLAIMED" and x.get("claim") == token
        ],
    }
    if capture:
        raw = {
            "version": VERSION,
            "scan_started_at": now.isoformat(),
            "clock_samples": observations,
            "calls": actor.calls,
            "config": asdict(cfg),
            "before_state_sha256": before_hash,
            "before_state": json.loads(before),
            "after_scan_state_sha256": scan_state_hash,
            "result": result,
            "email_observations": True,
            "source_file_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        }
        if cfg.record_inputs and not (
            result.get("reason")
            in (
                "AFTER_SESSION_EXIT_CUTOFF",
                "NO_VERIFIED_NFO_SESSION",
                "BEFORE_FIRST_OI_BASELINE",
            )
            and not result.get("position_locked")
        ):
            session_date = now.date().isoformat()
            run_id = (
                os.environ.get("GITHUB_RUN_ID", "local")
                + "-"
                + os.environ.get("GITHUB_RUN_ATTEMPT", "1")
            )
            captured_at = now.strftime("%H%M%S-%f")
            safe = "".join(x if x.isalnum() or x in "-_" else "_" for x in run_id)
            file = (
                audit_dir
                / ("inputs_" + AUDIT_RELEASE)
                / session_date
                / (captured_at + "-" + safe + ".json.gz")
            )
            record_inputs(file, raw)
            event["input_recording"] = str(file)
    if result.get("reason") != "AFTER_SESSION_EXIT_CUTOFF" or event["alerts_pending"]:
        append_audit(
            audit_dir / (f"market_scan_{AUDIT_RELEASE}_{now.date().isoformat()}.jsonl"),
            event,
        )
    if failure:
        result["audit_recorded"] = True
    return result


def replay_recordings(directory: Path, cfg: Config, output: Path) -> int:
    """Replay recordings produced by this release.

    Mismatched API call sequences fail rather than silently substituting a
    future price, date, quote, or contract not captured at that decision time.
    """
    files = sorted(directory.rglob("*.json.gz"))
    if not files:
        raise ScannerError("NO_CAPTURED_INPUTS_FOUND_FOR_" + AUDIT_RELEASE.upper())
    records = []
    last_at = None
    for file in files:
        try:
            with gzip.open(file, "rt", encoding="utf-8") as f:
                r = json.load(f)
            if r.get("version") != VERSION:
                raise ScannerError("Different recording engine version")
            if not r.get("clock_samples"):
                raise ScannerError("NO_CAPTURED_CLOCK_SAMPLES")
            sample = timestamp(r["clock_samples"][0])
            if last_at is not None and sample < last_at:
                raise ScannerError("CAPTURES_NOT_CHRONOLOGICAL")
            last_at = sample
            # Every invocation replays its EXACT saved pre-scan state. This
            # prevents synthetic paper-flat positions from polluting historical
            # decisions and preserves open-position locks from earlier versions.
            s = r.get("before_state")
            if not isinstance(s, dict):
                raise ScannerError("PRE_SCAN_STATE_NOT_RECORDED")
            validate_state(s)
            state_hash = hashlib.sha256(
                json.dumps(s, sort_keys=True, allow_nan=False, separators=(",", ":")).encode()
            ).hexdigest()
            if state_hash != r.get("before_state_sha256"):
                raise ScannerError("PRE_SCAN_STATE_SHA256_MISMATCH")
            api = ReplayProvider(r["calls"])
            clock = iter(r["clock_samples"])
            recorded_cfg = Config(**r["config"]) if "config" in r else cfg
            evaluated, _ = scan(s, api, recorded_cfg, clock_fn=lambda: timestamp(next(clock)))
            if next(clock, None) is not None:
                raise ScannerError("Captured clock samples were not all consumed")
            if api.index != len(api.calls):
                raise ScannerError("Captured calls not all consumed; replay not equivalent")
            if not r.get("email_observations"):
                # Older v128 captures predate the optional email-only facts.
                for event in s["outbox"]:
                    event.pop("email_observation", None)
            new_hash = hashlib.sha256(
                json.dumps(s, sort_keys=True, allow_nan=False, separators=(",", ":")).encode()
            ).hexdigest()
            matching = jsonable(evaluated) == r.get("result") and new_hash == r.get(
                "after_scan_state_sha256"
            )
            records.append(
                {
                    "file": str(file),
                    "as_of": sample.isoformat(),
                    "decision": evaluated.get("decision"),
                    "reason": evaluated.get("reason"),
                    "expected_decision": r.get("result", {}).get("decision"),
                    "matches_original_decision": matching,
                    "pre_state_sha256_verified": True,
                    "post_state_sha256_verified": new_hash == r.get("after_scan_state_sha256"),
                    "position_locked": bool(s.get("position")),
                }
            )
        except (
            ScannerError,
            DataError,
            ProviderError,
            KeyError,
            ValueError,
            TypeError,
            StopIteration,
        ) as exc:
            records.append({"file": str(file), "status": "REPLAY_INCOMPLETE", "error": str(exc)})
            break
    report = {
        "engine": VERSION,
        "recordings": len(files),
        "processed": len(records),
        "unverified_original_market_history": True,
        "replay_is_not_proof_of_live_fill_or_profitability": True,
        "records": records,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, allow_nan=False), encoding="utf-8")
    print(
        json.dumps(
            {
                "status": "REPLAY_COMPLETE"
                if all("status" not in x for x in records)
                else "REPLAY_INCOMPLETE",
                "report": str(output),
                "processed": len(records),
                "total": len(files),
            }
        )
    )
    return (
        0
        if all(x.get("matches_original_decision") for x in records) and len(records) == len(files)
        else 1
    )


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--version", action="store_true")
    action.add_argument("--initialize-flat", action="store_true")
    action.add_argument("--scan-and-claim", action="store_true")
    action.add_argument("--arm-delivery", action="store_true")
    action.add_argument("--deliver-armed", action="store_true")
    action.add_argument("--reconcile-flat", metavar="POSITION_ID")
    action.add_argument("--requeue-alert", metavar="ALERT_ID")
    action.add_argument("--migrate-state", metavar="SOURCE")
    action.add_argument(
        "--replay-recordings",
        metavar="DIR",
        help=f"Replay recorded {AUDIT_RELEASE} price and OI inputs",
    )
    parser.add_argument("--replay-report", default=f"audit/replay_{AUDIT_RELEASE}.json")
    args = parser.parse_args(argv)
    if args.version:
        print(VERSION)
        return 0
    try:
        cfg = environment_config()
        if args.replay_recordings:
            return replay_recordings(Path(args.replay_recordings), cfg, Path(args.replay_report))
        state_path, audit_dir = paths()
        token = os.environ.get("NOTIFICATION_CLAIM_TOKEN", "")
        with local_lock(state_path):
            if args.initialize_flat:
                if os.environ.get("MANUAL_FLAT_CONFIRMED") != "1":
                    raise ScannerError("MANUAL_FLAT_CONFIRMED=1 required")
                if state_path.exists():
                    raise ScannerError("REFUSING_TO_OVERWRITE_EXISTING_STATE")
                save_state(state_path, starting_state(datetime.now(IST)))
                print(json.dumps({"status": "INITIALIZED_FLAT_REFERENCE_ONLY"}))
                return 0
            if args.migrate_state:
                if state_path.exists():
                    raise ScannerError("Destination exists; no overwrites")
                src = Path(args.migrate_state)
                state = load_state(src)
                ensure_engine(state, datetime.now(IST))
                save_state(state_path, state)
                print(
                    json.dumps(
                        {
                            "status": "MIGRATED_NONDESTRUCTIVE",
                            "position_locked": bool(state.get("position")),
                        }
                    )
                )
                return 0
            state = load_state(state_path)
            if args.reconcile_flat:
                if os.environ.get("MANUAL_FLAT_CONFIRMED") != "1":
                    raise ScannerError("Operator must verify broker/alerts flat")
                p = state.get("position")
                if not p or p["id"] != args.reconcile_flat:
                    raise ScannerError("Position ID does not match active lock")
                closed = dict(
                    p,
                    status="CLOSED",
                    closed_at=datetime.now(IST).isoformat(),
                    exit_reason="OPERATOR_VERIFIED_FLAT_UNKNOWN_FILL",
                    fill_confirmed=False,
                )
                state["history"].append(closed)
                state["position"] = None
                state["last_exit"] = {
                    "at": closed["closed_at"],
                    "direction": closed["direction"],
                    "id": closed["id"],
                }
                save_state(state_path, state)
                append_audit(
                    audit_dir
                    / (f"market_scan_{AUDIT_RELEASE}_{datetime.now(IST).date().isoformat()}.jsonl"),
                    {
                        "event": "MANUAL_RECONCILIATION",
                        "position_id": p["id"],
                        "at": closed["closed_at"],
                    },
                )
                print(json.dumps({"status": "REFERENCE_LOCK_RECONCILED", "position_id": p["id"]}))
                return 0
            if args.requeue_alert:
                if os.environ.get("MANUAL_ALERT_UNDELIVERED_CONFIRMED") != "1":
                    raise ScannerError(
                        "Explicit verified mailbox non-delivery confirmation required"
                    )
                event = next((x for x in state["outbox"] if x["id"] == args.requeue_alert), None)
                if (
                    not event
                    or event.get("kind") not in ALERT_KINDS
                    or event.get("status") not in ("CLAIMED", "DELIVERY_UNCERTAIN")
                ):
                    raise ScannerError("Alert not eligible for verified manual retry")
                event.update(
                    status="PENDING",
                    claim=None,
                    manually_requeued_at=datetime.now(IST).isoformat(),
                )
                event.pop("attempted_at", None)
                save_state(state_path, state)
                print(json.dumps({"status": "MANUALLY_REQUEUED", "event_id": event["id"]}))
                return 0
            if args.arm_delivery:
                count = arm_delivery(state, token, datetime.now(IST))
                save_state(state_path, state)
                print(json.dumps({"status": "DELIVERY_ARMED", "count": count}))
                return 0
            if args.deliver_armed:
                return deliver_armed(state, state_path, token)
            if not token:
                raise ScannerError("NOTIFICATION_CLAIM_TOKEN missing")
            api = Upstox(os.environ.get("UPSTOX_ANALYTICS_TOKEN", ""))
            result = recorded_scan(state, api, cfg, audit_dir, token)
            save_state(state_path, state)
            print(json.dumps(result, sort_keys=True, allow_nan=False))
            return 1 if result["decision"] in ("ERROR", "POSITION_MONITORING_UNAVAILABLE") else 0
    except (ScannerError, OSError, ValueError, TypeError, BlockingIOError) as exc:
        print(
            json.dumps(
                {"status": "ERROR", "reason": type(exc).__name__, "detail": str(exc)},
                allow_nan=False,
            ),
            file=sys.stderr,
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
