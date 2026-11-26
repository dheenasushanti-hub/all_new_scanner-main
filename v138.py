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

VERSION = '138.0.0'
AUDIT_RELEASE = 'v138'
IST = timezone(timedelta(hours=5, minutes=30))
INDEX = 'NSE_INDEX|Nifty 50'
ALERT_KINDS = frozenset({'ENTRY', 'EXIT', 'ADJUST_SL', 'T1', 'T2'})
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
        raise ValueError('nonfinite value')
    return f


def timestamp(value: Any) -> datetime:
    if isinstance(value, bool) or value is None:
        raise DataError('Invalid timestamp')
    try:
        if isinstance(value, (int, float)) or (
            isinstance(value, str) and value.isdigit()
        ):
            n = float(value)
            if not math.isfinite(n):
                raise ValueError('nonfinite timestamp')
            dt = datetime.fromtimestamp(n / 1000 if n > 1e11 else n, timezone.utc)
        else:
            dt = datetime.fromisoformat(str(value).replace('Z', '+00:00'))
        if dt.tzinfo is None:
            raise ValueError('timezone absent')
        return dt.astimezone(IST)
    except (ValueError, OverflowError, TypeError) as exc:
        raise DataError('Invalid timestamp') from exc


def read_number(value: Any, name: str, *, positive=False, nonnegative=False) -> float:
    if isinstance(value, bool):
        raise DataError('Boolean numeric field ' + name)
    try:
        n = float(value)
    except (ValueError, TypeError) as exc:
        raise DataError('Invalid numeric field ' + name) from exc
    if not math.isfinite(n) or (positive and n <= 0) or (nonnegative and n < 0):
        raise DataError('Nonfinite/out of range ' + name)
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
            raise DataError('Candle start must be timezone-aware, minute aligned')
        values = (self.open, self.high, self.low, self.close, self.volume)
        if (
            not all(math.isfinite(x) for x in values)
            or min(values[:4]) <= 0
            or self.volume < 0
        ):
            raise DataError('Invalid OHLCV')
        if (
            self.low > min(self.open, self.close)
            or self.high < max(self.open, self.close)
            or self.high < self.low
        ):
            raise DataError('Impossible OHLC')


def day_time(now: datetime, hour: int, minute: int) -> datetime:
    return now.astimezone(IST).replace(
        hour=hour, minute=minute, second=0, microsecond=0
    )


def exact_minute(now: datetime) -> datetime:
    return now.astimezone(IST).replace(second=0, microsecond=0)


def serialize_bar(c: Candle) -> list[Any]:
    return [c.start.isoformat(), c.open, c.high, c.low, c.close, c.volume]


def parse_candles(raw: list, now: datetime) -> list[Candle]:
    """Drop uncompleted bars; refuse inconsistent duplicates, duplicates do not shadow data."""
    if not isinstance(raw, list):
        raise DataError('Candle payload must be list')
    unique: dict[datetime, Candle] = {}
    for row in raw:
        try:
            if not isinstance(row, (list, tuple)) or len(row) < 5:
                raise DataError('Malformed candle row')
            start = timestamp(row[0])
            if start.second or start.microsecond:
                raise DataError('Unaligned candle')
            if start + timedelta(minutes=1) > now - timedelta(seconds=1):
                continue
            c = Candle(
                start,
                *(
                    read_number(row[i], f'candle_{i}', positive=True)
                    for i in range(1, 5)
                ),
                read_number(row[5], 'volume', nonnegative=True)
                if len(row) > 5
                else 0.0,
            )
        except (DataError, TypeError) as exc:
            raise DataError('Invalid OHLC row') from exc
        if c.start in unique and c != unique[c.start]:
            raise DataError('Conflicting duplicate candles')
        unique[c.start] = c
    ordered = sorted(unique.values(), key=lambda c: c.start)
    if not ordered:
        raise DataError('No completed candles')
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
        return (
            through is not None
            and timedelta(0) <= slot - through <= MAX_ENTRY_CANDLE_LAG
        )

    def audit(self, slot: datetime) -> dict:
        through = self.through
        return {
            'from': self.bars[0].start.isoformat() if self.bars else None,
            'through': through.isoformat() if through else None,
            'expected_through': slot.isoformat(),
            'lag_minutes': (slot - through) // MINUTE if through else None,
            'contiguous_tail': self.tail_size,
            'latest': through == slot,
        }


def merge_closed_price(
    saved: ClosedPrice,
    raw: list,
    received_at: datetime,
    session: tuple[datetime, datetime],
    cfg: Config,
) -> ClosedPrice:
    session_open, session_close = session
    observed = parse_candles(
        raw, received_at - timedelta(seconds=cfg.feed_grace_seconds - 1)
    )
    observed = [
        bar
        for bar in observed
        if session_open <= bar.start and bar_end(bar) <= session_close
    ]
    # Responses can be partial or out of order. Supplement recorded evidence
    # by timestamp while retaining the latest provider correction for a bar.
    by_start = {bar.start: bar for bar in saved.bars}
    by_start.update((bar.start, bar) for bar in observed)
    return ClosedPrice(sorted(by_start.values(), key=lambda bar: bar.start))


def aggregate(
    bars: list[Candle], duration: int, session_open: datetime
) -> list[Candle]:
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
        if any(
            b.start != group[0].start + k * duration * MINUTE
            for k, b in enumerate(group)
        ):
            continue
        values = [side * (b.low if side == 1 else b.high) for b in group]
        # Resolve flat extrema once, at the first occurrence.
        if values.index(min(values)) == left and values[left] < min(values[left + 1 :]):
            result.append(
                Swing(side * values[left], bar.start, bar_end(group[-1], duration))
            )
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
            timestamp(value['at']),
            timestamp(value['through']),
            value['expiry'],
            tuple(OIRow(**row) for row in value['rows']),
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


def make_oi_snapshot(
    chain: list[dict], expiry: str, at: datetime, through: datetime
) -> OISnapshot:
    rows = []
    for row in chain:
        oi = row.get('oi')
        if row['expiry'] != expiry or oi is None:
            continue
        if (
            type(oi) not in (float, int)
            or not math.isfinite(oi)
            or oi < 0
            or int(oi) != oi
        ):
            continue
        rows.append(
            OIRow(row['instrument_key'], row['side'], float(row['strike']), int(oi))
        )
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
        {
            float(row['strike_price'])
            for row in contracts
            if row['instrument_type'] in ('CE', 'PE')
        }
    )


def paired_oi(window: OIWindow | None) -> dict[float, OIPair]:
    if window is None:
        return {}
    by_strike: dict[float, dict[str, OIObservation]] = {}
    for item in window.changes:
        by_strike.setdefault(item.row.strike, {})[item.row.side] = item
    return {
        strike: OIPair(strike, rows.get('CE'), rows.get('PE'))
        for strike, rows in by_strike.items()
    }


@dataclass(frozen=True)
class OILevel:
    strike: float
    oi: int
    change: float | None


def oi_levels(window: OIWindow, spot: float, side: int, atr: float) -> list[OILevel]:
    kind = 'CE' if side == 1 else 'PE'
    changes = {x.row.key: x.increase for x in window.changes}
    max_distance = max(300.0, 24 * atr)
    vicinity = [
        r
        for r in window.snapshot.rows
        if r.side == kind and r.oi > 0 and abs(r.strike - spot) <= max_distance
    ]
    if not vicinity:
        return []
    reference = median(r.oi for r in vicinity)
    levels = [
        OILevel(r.strike, r.oi, changes.get(r.key))
        for r in vicinity
        if r.oi >= reference or changes.get(r.key, 0) > OI_LEVEL_MATERIAL_CHANGE
    ]
    return sorted(levels, key=lambda x: x.strike * side)


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
    checked_quote(quote, now, cfg.quote_max_age_seconds, field='ask')
    assert quote is not None
    seen = timestamp(quote['timestamp'])
    if abs((seen - index_time).total_seconds()) > cfg.quote_max_skew_seconds:
        raise DataError('INDEX_OPTION_QUOTE_SKEW')
    bid = read_number(quote['bid'], 'bid', positive=True)
    ask = read_number(quote['ask'], 'ask', positive=True)
    spread = 200 * (ask - bid) / (ask + bid)
    lot = read_number(row['lot_size'], 'lot_size', positive=True)
    depth = (
        min(
            read_number(quote[key], key, nonnegative=True)
            for key in ('bid_qty', 'ask_qty')
        )
        / lot
    )
    if not lot.is_integer() or not 0 <= spread <= cfg.max_spread_percent:
        raise DataError('INVALID_LIVE_SPREAD_OR_LOT')
    if depth < cfg.min_depth_lots:
        raise DataError('INSUFFICIENT_LIVE_DEPTH')
    pair = band.pairs[offset]
    return {
        'instrument_key': row['instrument_key'],
        'side': row['instrument_type'],
        'strike': pair.strike,
        'atm': band.atm,
        'offset': offset,
        'expiry': row['expiry'],
        'bid': bid,
        'ask': ask,
        'spread_pct': round(spread, 4),
        'depth_lots': depth,
        'lot_size': int(lot),
        'quote_time': seen.isoformat(),
        'paired_oi_at_contract': pair.public(),
    }


class Upstox:
    def __init__(self, token: str):
        if not token or any((c in token for c in '\r\n')):
            raise ProviderError('UPSTOX_ANALYTICS_TOKEN missing or invalid')
        self._token = token

    def get(self, path: str, params: dict | None = None):
        url = (
            'https://api.upstox.com'
            + path
            + ('?' + urlencode(params) if params else '')
        )
        req = Request(
            url,
            headers={
                'Authorization': 'Bearer ' + self._token,
                'Accept': 'application/json',
                'User-Agent': 'nifty-scanner/' + VERSION,
            },
        )
        for attempt in range(2):
            try:
                with urlopen(req, timeout=7) as r:

                    def reject_constant(value):
                        raise ValueError('Invalid numeric JSON')

                    obj = json.load(
                        r, parse_constant=reject_constant, parse_float=finite_json_float
                    )
                if (
                    not isinstance(obj, dict)
                    or obj.get('status') != 'success'
                    or 'data' not in obj
                ):
                    raise ProviderError(
                        'Upstox returned an unsuccessful or invalid response'
                    )
                return obj['data']
            except HTTPError as e:
                if e.code in (429, 500, 502, 503, 504) and attempt < 1:
                    time.sleep(1 + attempt)
                    continue
                raise ProviderError(f'Upstox request failed HTTP {e.code}') from None
            except (URLError, TimeoutError, OSError, ValueError):
                if attempt < 1:
                    time.sleep(1 + attempt)
                    continue
                raise ProviderError(
                    'Upstox request failed or returned invalid JSON'
                ) from None
        raise ProviderError('Upstox request failed')

    def session(self, now: datetime):
        data = self.get('/v2/market/timings/' + now.astimezone(IST).date().isoformat())
        matches = (
            [x for x in data if x.get('exchange') == 'NFO']
            if isinstance(data, list)
            else []
        )
        if not matches:
            return None
        sessions = []
        for row in matches:
            start = datetime.fromtimestamp(
                float(row['start_time']) / 1000, timezone.utc
            ).astimezone(IST)
            end = datetime.fromtimestamp(
                float(row['end_time']) / 1000, timezone.utc
            ).astimezone(IST)
            if start.date() == now.astimezone(IST).date() and start < end:
                sessions.append((start, end))
        return next(((a, b) for a, b in sessions if a <= now.astimezone(IST) < b), None)

    def candles(self, key=INDEX):
        data = self.get(
            '/v3/historical-candle/intraday/' + quote(key, safe='') + '/minutes/1'
        )
        if not isinstance(data, dict) or not isinstance(data.get('candles'), list):
            raise ProviderError('Invalid candle response')
        return data['candles']

    def prior_ten(self, today: date):
        previous_day = today - timedelta(days=1)
        from_day = today - timedelta(days=12)
        path = (
            '/v3/historical-candle/'
            + quote(INDEX, safe='')
            + '/minutes/10/'
            + previous_day.isoformat()
            + '/'
            + from_day.isoformat()
        )
        data = self.get(path)
        if not isinstance(data, dict) or not isinstance(data.get('candles'), list):
            raise ProviderError('Invalid prior 10-minute candle response')
        return data['candles']

    def contracts(self, today: date):
        data = self.get('/v2/option/contract', {'instrument_key': INDEX})
        if not isinstance(data, list):
            raise ProviderError('Invalid option contract response')
        rows = []
        for r in data:
            if not isinstance(r, dict):
                raise ProviderError('Malformed contract record')
            if r.get('underlying_key') != INDEX or r.get('instrument_type') not in (
                'CE',
                'PE',
            ):
                continue
            try:
                exp = date.fromisoformat(str(r['expiry']))
            except (ValueError, KeyError):
                continue
            if exp >= today:
                try:
                    strike = read_number(
                        r['strike_price'], 'listed_strike', positive=True
                    )
                    lot = read_number(r['lot_size'], 'listed_lot', positive=True)
                    key = r['instrument_key']
                    if not lot.is_integer() or not isinstance(key, str) or not key:
                        continue
                except (DataError, KeyError):
                    continue
                rows.append(
                    {
                        'expiry': exp.isoformat(),
                        'instrument_key': key,
                        'instrument_type': r['instrument_type'],
                        'strike_price': strike,
                        'lot_size': int(lot),
                    }
                )
        if not rows:
            raise ProviderError('No unexpired NIFTY option contracts')
        expiry = min((date.fromisoformat(r['expiry']) for r in rows)).isoformat()
        return (expiry, [r for r in rows if r['expiry'] == expiry])

    def chain(self, expiry: str, contracts: list[dict]):
        data = self.get(
            '/v2/option/chain', {'instrument_key': INDEX, 'expiry_date': expiry}
        )
        if not isinstance(data, list) or not data:
            raise ProviderError('Empty option chain')
        valid = {
            r['instrument_key']: (float(r['strike_price']), r['instrument_type'])
            for r in contracts
            if r.get('instrument_key') and r.get('strike_price') is not None
        }
        metadata = {
            r['instrument_key']: r for r in contracts if r.get('instrument_key')
        }
        result = []
        seen = set()
        for row in data:
            if not isinstance(row, dict):
                raise ProviderError('Malformed chain record')
            if row.get('underlying_key') != INDEX or row.get('expiry') != expiry:
                raise ProviderError('Chain underlying or expiry mismatch')
            try:
                strike = float(row['strike_price'])
            except (TypeError, ValueError, KeyError):
                raise ProviderError('Invalid strike') from None
            for side, field in (('CE', 'call_options'), ('PE', 'put_options')):
                option = row.get(field) or {}
                key = option.get('instrument_key')
                if not key:
                    continue
                if valid.get(key) != (strike, side) or key in seen:
                    raise ProviderError('Contract identity mismatch')
                seen.add(key)
                market = option.get('market_data') or {}
                greeks = option.get('option_greeks') or {}
                try:
                    oi = float(market['oi']) if market.get('oi') is not None else None
                    ltp = float(market.get('ltp') or 0)
                    volume = float(market.get('volume') or 0)
                    delta = (
                        float(greeks['delta'])
                        if greeks.get('delta') is not None
                        else None
                    )
                    gamma = (
                        float(greeks['gamma'])
                        if greeks.get('gamma') is not None
                        else None
                    )
                    theta = (
                        float(greeks['theta'])
                        if greeks.get('theta') is not None
                        else None
                    )
                    vega = (
                        float(greeks['vega'])
                        if greeks.get('vega') is not None
                        else None
                    )
                    iv = float(greeks['iv']) if greeks.get('iv') is not None else None
                    prev_oi = (
                        float(market['prev_oi'])
                        if market.get('prev_oi') is not None
                        else None
                    )
                    chain_bid = float(market.get('bid_price') or 0)
                    chain_ask = float(market.get('ask_price') or 0)
                    chain_bid_qty = float(market.get('bid_qty') or 0)
                    chain_ask_qty = float(market.get('ask_qty') or 0)
                except (ValueError, TypeError):
                    raise ProviderError('Invalid OI/greek data') from None
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
                    raise ProviderError('Invalid option chain values')
                if oi is not None and (
                    not math.isfinite(oi) or oi < 0 or not oi.is_integer()
                ):
                    oi = None
                if any(
                    (
                        x is not None and (not math.isfinite(x))
                        for x in (delta, gamma, theta, vega, iv, prev_oi)
                    )
                ):
                    raise ProviderError('Invalid option greek data')
                lot = metadata[key].get('lot_size')
                if (
                    lot is None
                    or not math.isfinite(float(lot))
                    or float(lot) <= 0
                    or (not float(lot).is_integer())
                ):
                    raise ProviderError('Missing or invalid live lot size')
                result.append(
                    {
                        'instrument_key': key,
                        'expiry': expiry,
                        'strike': strike,
                        'side': side,
                        'oi': oi,
                        'ltp': ltp,
                        'volume': volume,
                        'delta': delta,
                        'gamma': gamma,
                        'theta': theta,
                        'vega': vega,
                        'iv': iv,
                        'prev_oi': prev_oi,
                        'lot_size': lot,
                        'chain_bid': chain_bid,
                        'chain_ask': chain_ask,
                        'chain_bid_qty': chain_bid_qty,
                        'chain_ask_qty': chain_ask_qty,
                    }
                )
        # Upstox's chain supplies a spot reference and a much larger distant
        # strike universe than this strategy needs. Keep the listed grid in
        # contracts and retain the local OI profile separately.
        snapshot_spots = [r.get('underlying_spot_price') for r in data]
        observed_spots = [
            float(v)
            for v in snapshot_spots
            if type(v) in (int, float) and math.isfinite(v) and v > 0
        ]
        if observed_spots:
            center = median(observed_spots)
            result = [r for r in result if abs(r['strike'] - center) <= 650]
        if len(result) < 4 or not {'CE', 'PE'}.issubset({r['side'] for r in result}):
            raise ProviderError('Incomplete option chain')
        return result

    def quotes(self, keys: list[str]):
        if not keys:
            return {}
        data = self.get(
            '/v2/market-quote/quotes', {'instrument_key': ','.join(dict.fromkeys(keys))}
        )
        if not isinstance(data, dict):
            raise ProviderError('Invalid quote response')
        out = {}
        for q in data.values():
            if not isinstance(q, dict):
                continue
            key = q.get('instrument_token')
            stamp = q.get('timestamp')
            if key not in keys or not stamp:
                continue
            try:
                price = float(q.get('last_price') or 0)
                buys = (q.get('depth') or {}).get('buy') or []
                sells = (q.get('depth') or {}).get('sell') or []
                b = buys[0] if buys else {}
                a = sells[0] if sells else {}
                numeric = {
                    name: float(q[name]) if q.get(name) is not None else None
                    for name in ('oi', 'average_price')
                }
                for name, value in numeric.items():
                    if value is not None and (not math.isfinite(value)):
                        numeric[name] = None
                quoted = {
                    'last_price': price,
                    'bid': float(b.get('price') or 0),
                    'bid_qty': float(b.get('quantity') or 0),
                    'ask': float(a.get('price') or 0),
                    'ask_qty': float(a.get('quantity') or 0),
                }
                if any((not math.isfinite(x) or x < 0 for x in quoted.values())):
                    continue
                out[key] = {**quoted, 'timestamp': stamp, **numeric}
            except (TypeError, ValueError):
                continue
        return out


def starting_state(now: datetime) -> dict:
    return {
        'schema': 7,
        'engine_version': VERSION,
        'initialized_at': now.isoformat(),
        'initialized_flat': True,
        'session_date': now.date().isoformat(),
        'position': None,
        'history': [],
        'outbox': [],
        'last_exit': None,
        'v124': {
            'session_date': now.date().isoformat(),
            'oi_samples': [],
            'consumed_signals': [],
        },
    }


def validate_state(state: dict):
    if (
        not isinstance(state, dict)
        or state.get('schema') != 7
        or 'position' not in state
        or not isinstance(state.get('history'), list)
        or not isinstance(state.get('outbox'), list)
    ):
        raise ScannerError('Invalid or unsupported persisted state')
    ids = set()
    for event in state['outbox']:
        if (
            not isinstance(event, dict)
            or not isinstance(event.get('id'), str)
            or event['id'] in ids
            or event.get('status')
            not in ('PENDING', 'CLAIMED', 'SENT', 'DELIVERY_UNCERTAIN', 'EXPIRED')
        ):
            raise ScannerError('Invalid or duplicate persisted outbox event')
        ids.add(event['id'])
    p = state['position']
    if p is not None:
        if (
            not isinstance(p, dict)
            or not p.get('id')
            or p.get('status') != 'OPEN'
            or p.get('direction') not in ('BULLISH', 'BEARISH')
        ):
            raise ScannerError('Invalid persisted reference position')
        side = 1 if p['direction'] == 'BULLISH' else -1
        entry, stop, initial, t1, t2 = [
            read_number(
                p.get(k, p.get('stop') if k == 'initial_stop' else None),
                k,
                positive=True,
            )
            for k in ('entry_spot', 'stop', 'initial_stop', 't1', 't2')
        ]
        took_t1 = p.get('t1_hit', False)
        t1_exit_pct = p.get('t1_exit_pct', 50)
        if type(t1_exit_pct) is not int or not 0 < t1_exit_pct < 100:
            raise ScannerError('Invalid persisted T1 allocation')
        if (
            type(took_t1) is not bool
            or side * (entry - initial) <= 0
            or side * (t1 - entry) <= 0
            or side * (t2 - t1) <= 0
            or side * (stop - initial) < 0
            or (not took_t1 and side * (entry - stop) <= 0)
        ):
            raise ScannerError('Invalid persisted position prices')
        if not p.get('instrument_key') or not p.get('expiry'):
            raise ScannerError('Invalid persisted contract identity')
        timestamp(p.get('opened_at'))
        timestamp(p.get('last_candle'))
    if 'v124' in state:
        engine = state['v124']
        if (
            not isinstance(engine, dict)
            or not isinstance(engine.get('oi_samples'), list)
            or not isinstance(engine.get('consumed_signals'), list)
        ):
            raise ScannerError('Invalid persisted strategy state')


def load_state(path: Path) -> dict:
    if not path.exists():
        raise ScannerError(
            'STATE_FILE_MISSING: manually reconcile existing positions before --initialize-flat'
        )
    try:
        with path.open(encoding='utf-8') as f:
            s = json.load(
                f,
                parse_constant=lambda _: (_ for _ in ()).throw(
                    ValueError('Nonfinite state')
                ),
            )
    except (OSError, ValueError) as exc:
        raise ScannerError('State unreadable; fail closed') from exc
    validate_state(s)
    return s


def save_state(path: Path, s: dict):
    validate_state(s)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix='.state-', dir=path.parent)
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as f:
            json.dump(s, f, sort_keys=True, separators=(',', ':'), allow_nan=False)
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
    with open(str(state_path) + '.lock', 'a+') as f:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def ensure_engine(state: dict, now: datetime) -> dict:
    if (
        state.get('position')
        and timestamp(state['position']['opened_at']).date() > now.date()
    ):
        raise ScannerError('FUTURE_DATED_REFERENCE_POSITION')
    if state.get('v124', {}).get('session_date') != now.date().isoformat():
        state['v124'] = starting_state(now)['v124']
    state['session_date'] = now.date().isoformat()
    state['engine_version'] = VERSION
    return state['v124']


def new_event(state: dict, kind: str, details: dict, now: datetime) -> str:
    if kind not in ALERT_KINDS:
        raise ScannerError('Non-actionable alert kind')
    details = copy.deepcopy(details)
    email_observation = details.pop('email_observation', None)
    identity = [kind, details['position_id']]
    if kind == 'ADJUST_SL':
        identity.extend(
            (details['observed_at'], details['new_stop'], details['new_t2'])
        )
    digest = hashlib.sha256(
        json.dumps(identity, separators=(',', ':')).encode()
    ).hexdigest()[:24]
    for event in state['outbox']:
        previous = event.get('details', {})
        if event['id'] == digest:
            return digest
        if (
            kind != 'ADJUST_SL'
            and event['kind'] == kind
            and previous.get('position_id') == details['position_id']
        ):
            return event['id']
    event = {
        'id': digest,
        'kind': kind,
        'details': details,
        'created_at': now.isoformat(),
        'status': 'PENDING',
    }
    if email_observation is not None:
        event['email_observation'] = email_observation
    state['outbox'].append(event)
    return digest


def claim_outbox(state: dict, token: str, now: datetime):
    if not token:
        raise ScannerError('Notification claim token absent')
    for event in state['outbox']:
        if event.get('kind') not in ALERT_KINDS:
            continue
        # Previous claims with no attempted_at cannot have reached SMTP via this
        # implementation: safe to reclaim when a workflow crashed pre-delivery.
        legacy_pending = event.get('status') == 'PENDING' and not event.get(
            'attempted_at'
        )
        # Old versions could CLAIM without the v123 durable commit-before-SMTP
        # protocol. Their state CANNOT prove non-delivery; do not resend.
        fresh_reclaim = (
            event.get('status') == 'CLAIMED'
            and event.get('claim_policy') == 'V123_PHASED'
            and not event.get('attempted_at')
        )
        if (legacy_pending or fresh_reclaim) and event['kind'] == 'ENTRY':
            details = event.get('details') or {}
            active_id = (state.get('position') or {}).get('id')
            created = timestamp(event.get('created_at'))
            if details.get('position_id') != active_id or now - created > 3 * MINUTE:
                event.update(status='EXPIRED', expired_at=now.isoformat(), claim=None)
                continue
        if legacy_pending or fresh_reclaim:
            event.update(
                status='CLAIMED',
                claim=token,
                claimed_at=now.isoformat(),
                claim_policy='V123_PHASED',
            )


def append_audit(path: Path, event: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a', encoding='utf-8') as f:
        f.write(
            json.dumps(event, sort_keys=True, allow_nan=False, separators=(',', ':'))
            + '\n'
        )
        f.flush()
        os.fsync(f.fileno())


def record_inputs(path: Path, record: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = json.dumps(
        record, allow_nan=False, sort_keys=True, separators=(',', ':')
    ).encode()
    fd, tmp = tempfile.mkstemp(prefix='.capture-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as stream:
            with gzip.GzipFile(
                fileobj=stream, mode='wb', compresslevel=7, mtime=0
            ) as z:
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
                'name': name,
                'args': jsonable(args),
                'kwargs': jsonable(kwargs),
            }
            try:
                value = attr(*args, **kwargs)
                self.calls.append({**signature, 'result': jsonable(value)})
                return value
            except (ProviderError, DataError) as exc:
                self.calls.append(
                    {**signature, 'error': type(exc).__name__, 'reason': str(exc)}
                )
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
    raise TypeError('Non-serializable provider payload')


class ReplayProvider:
    """Exact ordered API-recording replay: no network, no future snapshots."""

    def __init__(self, calls: list[dict]):
        self.calls = calls
        self.index = 0

    def __getattr__(self, name):
        def recorded(*args, **kwargs):
            if self.index >= len(self.calls):
                raise ProviderError('CAPTURE_EXHAUSTED:' + name)
            r = self.calls[self.index]
            self.index += 1
            if (
                r['name'] != name
                or r['args'] != jsonable(args)
                or r['kwargs'] != jsonable(kwargs)
            ):
                raise ProviderError(
                    'CAPTURE_CALL_SEQUENCE_MISMATCH expected '
                    + r['name']
                    + ' got '
                    + name
                )
            if 'error' in r:
                cls = DataError if r['error'] == 'DataError' else ProviderError
                raise cls(r['reason'])
            if name == 'session' and r['result'] is not None:
                return tuple(timestamp(x) for x in r['result'])
            return copy.deepcopy(r['result'])

        return recorded


def checked_quote(
    q: dict | None, now: datetime, max_age: float, field='last_price'
) -> float:
    if not isinstance(q, dict):
        raise DataError('Missing live quote')
    price = read_number(q.get(field), field, positive=True)
    age = (now - timestamp(q.get('timestamp'))).total_seconds()
    if not -2 <= age <= max_age:
        raise DataError('STALE_OR_FUTURE_DATED_QUOTE')
    return price


def position_event_payload(p: dict, now: datetime, **more):
    fields = (
        'id',
        'direction',
        'instrument_key',
        'side',
        'strike',
        'expiry',
        'entry_spot',
        'entry_ask',
        'initial_stop',
        'stop',
        't1',
        't2',
        't1_exit_pct',
        'remaining_pct',
        'opened_at',
        'scenario',
        't1_source',
        't2_source',
        'stop_policy',
        'runner',
    )
    return {
        'position_id': p['id'],
        'observed_at': now.isoformat(),
        'position': {k: p.get(k) for k in fields},
        'broker_order_submitted': False,
        'broker_fill_confirmed': False,
        **more,
    }


def close_reference(
    position: dict, at: datetime, reason: str, observed: float | None, source: str
) -> dict:
    return dict(
        position,
        status='CLOSED',
        closed_at=at.isoformat(),
        exit_reason=reason,
        observed_exit_spot=observed,
        exit_source=source,
        fill_confirmed=False,
    )


def prior_context(engine: dict, api, now: datetime) -> list[Candle]:
    if 'prior_ten' not in engine:
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
            engine['prior_ten'] = [serialize_bar(b) for b in bars]
        except (DataError, ProviderError, ValueError, TypeError, KeyError):
            return []
    return parse_candles(engine['prior_ten'], now) if engine['prior_ten'] else []


MINUTE = timedelta(minutes=1)
DISPATCH_INTERVAL = 3 * MINUTE
MAX_ENTRY_CANDLE_LAG = MINUTE
OI_LEVEL_MATERIAL_CHANGE = 0.02
EARLY_RETEST_OI_CHANGE = 0.019
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
            'record_inputs',
            'arm_continuation_runner',
            'allow_persistent_oi',
        )
        integers = (
            'oi_jitter_seconds',
            'quote_max_age_seconds',
            'quote_max_skew_seconds',
            'max_state_history',
        )
        for key, value in asdict(self).items():
            if key in flags:
                if type(value) is not bool:
                    raise DataError(f'{key} must be a boolean')
            elif (
                type(value) not in (int, float)
                or not math.isfinite(value)
                or value < 0
                or (value == 0 and key != 'min_reward_risk')
                or (key in integers and type(value) is not int)
            ):
                raise DataError(f'Invalid configuration: {key}')
        if not 20 <= self.initial_stop_points <= 30:
            raise DataError('Initial stop must be between 20 and 30 NIFTY points')
        if not (
            self.oi_jitter_seconds < 60
            and 1 <= self.feed_grace_seconds < 15
            and self.quote_max_skew_seconds <= self.quote_max_age_seconds
        ):
            raise DataError('Inconsistent market data timing')


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

    def rule(self, side: int, defended: bool = False) -> str | None:
        changes = self.changes
        if changes is None:
            return None
        call, put = changes
        if not (side * call < 0 < side * put):
            return None
        strong, weak = sorted(map(abs, changes), reverse=True)
        if strong >= OI_LEVEL_MATERIAL_CHANGE:
            return 'STANDARD_2_PERCENT'
        if defended and strong >= EARLY_RETEST_OI_CHANGE and weak >= 0.005:
            return 'DEFENDED_RETEST_1_9_PERCENT'
        return None

    @property
    def quiet(self) -> bool:
        return (
            self.changes is not None
            and max(map(abs, self.changes)) < EARLY_RETEST_OI_CHANGE
        )

    def public(self) -> dict:
        if self.changes is None:
            state = 'MISSING'
        elif self.rule(1):
            state = 'BULLISH'
        elif self.rule(-1):
            state = 'BEARISH'
        elif self.changes[0] * self.changes[1] > 0:
            state = 'MIXED'
        elif self.quiet:
            state = 'QUIET'
        else:
            state = 'MIXED'
        return {
            'strike': self.strike,
            'state': state,
            'quiet': self.quiet,
            'call_change_pct': self.call.increase * 100
            if self.call is not None
            else None,
            'put_change_pct': self.put.increase * 100 if self.put is not None else None,
        }


def nearest_strike(grid: list[float], level: float) -> float:
    return min(grid, key=lambda strike: (abs(strike - level), strike))


@dataclass(frozen=True)
class StrikeBand:
    atm: float
    pairs: dict[int, OIPair]

    @classmethod
    def build(
        cls, grid: list[float], spot: float, pairs: dict[float, OIPair]
    ) -> StrikeBand | None:
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
            'atm': self.atm,
            'strikes': [
                {'offset': offset, **self.pairs[offset].public()}
                if offset in self.pairs
                else {'offset': offset, 'state': 'MISSING_LISTING'}
                for offset in (-2, -1, 0, 1, 2)
            ],
        }


# The price book is replayed from closed candles. Regimes, defended zones
# and entry attempts have separate identities and clocks.
WATCH_LENGTH = timedelta(minutes=18)
SCHEDULE_GRACE = timedelta(seconds=90)


def edge(bar: Candle, side: int) -> float:
    return bar.high if side == 1 else bar.low


def defense(bar: Candle, side: int) -> float:
    return bar.low if side == 1 else bar.high


def beyond(value: float, level: float, side: int, margin: float = 0.0) -> bool:
    return side * (value - level) > margin


def held(bars: list[Candle], level: float, side: int, margin: float = 0.0) -> bool:
    return len(bars) >= 2 and all(
        beyond(b.close, level, side, margin) for b in bars[-2:]
    )


def latest_pivot(bars: list[Candle], side: int, duration: int) -> Swing | None:
    if len(bars) < 3:
        return None
    pivots = swings(bars[-3:], side, duration=duration, left=1)
    return pivots[-1] if pivots else None


def entry_deadline(at: datetime, session_open: datetime) -> datetime:
    slot, remainder = divmod(at - session_open, DISPATCH_INTERVAL)
    return (
        session_open
        + (slot + int(bool(remainder)) + 1) * DISPATCH_INTERVAL
        + SCHEDULE_GRACE
    )


@dataclass
class MarketLeg:
    side: int
    origin: Swing
    protected: Swing
    extreme: Swing
    spent: bool = False
    pullback: Swing | None = None
    pullback_block: bool = False

    @property
    def id(self) -> str:
        return f'{self.side}:{self.origin.at.isoformat()}'


@dataclass(frozen=True)
class PriceRange:
    low: float
    high: float
    established_at: datetime
    margin: float

    def boundary(self, side: int) -> float:
        return self.high if side == 1 else self.low


@dataclass
class RangeBreak:
    zone: PriceRange
    side: int
    first_break: datetime
    retest_completed: bool = False


@dataclass
class Watch:
    side: int
    kind: str
    level: Swing
    registered_at: datetime
    until: datetime
    parent: str | None
    reaction: float | None = None
    stopped_at: datetime | None = None
    spent_at: datetime | None = None

    @property
    def id(self) -> str:
        return f'{self.kind}:{self.side}:{self.level.at.isoformat()}'


@dataclass(frozen=True)
class EntryTrigger:
    watch_id: str
    side: int
    kind: str
    level: float
    defense: Swing
    first_break: datetime
    confirmed_at: datetime
    expires_at: datetime
    max_extension: float
    first_objective: float
    parent: str | None
    retest: bool
    mature_leg: bool = False
    live_condition: bool = False
    range_edge: float | None = None
    setup_origin: datetime | None = None

    @property
    def id(self) -> str:
        return f'{self.watch_id}:{self.kind}:{(self.setup_origin or self.first_break).isoformat()}'


def consolidation(bars: list[Candle], atr: float, atr3: float) -> PriceRange | None:
    for size in (18, 9):
        if len(bars) < size:
            continue
        group = bars[-size:]
        low, high = min(b.low for b in group), max(b.high for b in group)
        span = high - low
        if not max(8.0, 0.8 * atr) <= span <= min(4.2 * atr, 2.2 * atr3):
            continue
        mid = (high + low) / 2
        closes = [b.close for b in group]
        travel = sum(abs(y - x) for x, y in zip(closes, closes[1:]))
        if abs(closes[-1] - closes[0]) > min(0.34 * span, 0.30 * travel):
            continue
        sides = [c > mid for c in closes if abs(c - mid) >= 0.07 * span]
        if sum(x != y for x, y in zip(sides, sides[1:])) >= 3:
            return PriceRange(low, high, bar_end(group[-1]), max(1.0, 0.25 * atr))
    return None


@dataclass(frozen=True)
class Retest:
    watch: Watch
    second: Swing
    reaction: float
    trend_aligned: bool

    @property
    def trigger(self) -> float:
        return self.second.price + 0.60 * (self.reaction - self.second.price)

    @property
    def protective(self) -> Swing:
        return min(
            (self.watch.level, self.second), key=lambda x: self.watch.side * x.price
        )


class PriceBook:
    def __init__(self, session_open: datetime):
        self.opens = session_open
        self.bars: list[Candle] = []
        self.threes: list[Candle] = []
        self.tens: list[Candle] = []
        self.atr = self.atr3 = 2.5
        self.leg: MarketLeg | None = None
        self.region: PriceRange | None = None
        self.breakout: RangeBreak | None = None
        self.watches: dict[str, Watch] = {}
        self.triggers: dict[str, EntryTrigger] = {}
        self.retests: dict[str, Retest] = {}
        self.range_break_ids: set[tuple[datetime, int]] = set()
        self.last_quoted_retests: dict[str, datetime] = {}
        self.pending_flip: tuple[int, float, datetime] | None = None
        self.pivots3: dict[int, list[Swing]] = {-1: [], 1: []}
        self.pivots10: dict[int, list[Swing]] = {-1: [], 1: []}

    @property
    def through(self):
        return bar_end(self.bars[-1])

    @property
    def move3(self):
        return (
            self.threes[-1].close - self.threes[-2].close
            if len(self.threes) >= 2
            else None
        )

    @property
    def trend(self):
        return self.leg.side if self.leg else 0

    def register(self, side: int, kind: str, pivot: Swing, now: datetime) -> Watch:
        watch = Watch(
            side,
            kind,
            pivot,
            now,
            now + WATCH_LENGTH,
            self.leg.id if self.leg else None,
        )
        return self.watches.setdefault(watch.id, watch)

    def trigger(
        self,
        watch: Watch,
        kind: str,
        threshold: float,
        pivot: Swing,
        first: datetime,
        confirmed: datetime,
        *,
        retest: bool = False,
        mature: bool = False,
        live: bool = False,
        range_edge: float | None = None,
        setup_origin: datetime | None = None,
    ) -> EntryTrigger:
        max_extension = min(
            32.0 if first - self.opens <= 18 * MINUTE else 26.0,
            max(17.0, 1.15 * self.atr),
        )
        return EntryTrigger(
            watch.id,
            watch.side,
            kind,
            threshold,
            pivot,
            first,
            confirmed,
            entry_deadline(first, self.opens),
            max_extension,
            threshold + watch.side * 47.5,
            watch.parent,
            retest,
            mature,
            live,
            range_edge,
            setup_origin,
        )

    def add_trigger(self, *args, **kwargs):
        outcome = self.trigger(*args, **kwargs)
        self.triggers.setdefault(outcome.id, outcome)

    def create_leg(self, side: int, pivot: Swing, bar: Candle) -> MarketLeg:
        self.leg = MarketLeg(
            side, pivot, pivot, Swing(edge(bar, side), bar.start, bar_end(bar))
        )
        self.pending_flip = None
        return self.leg

    def maintain_watches(self, bar: Candle, now: datetime):
        margin = max(2.0, 0.20 * self.atr)
        for watch in self.watches.values():
            if watch.stopped_at or watch.spent_at or now > watch.until:
                continue
            side = watch.side
            # A wick may refine a defense. Two closes outside it end the watch.
            if held(self.bars, watch.level.price, -side, margin):
                watch.stopped_at = now
                continue
            favorable = edge(bar, side)
            if watch.reaction is None or beyond(favorable, watch.reaction, side):
                watch.reaction = favorable
            if any(
                t.watch_id == watch.id
                and bar.start >= t.confirmed_at
                and beyond(favorable, t.first_objective, side)
                for t in self.triggers.values()
            ):
                watch.spent_at = now

    def process_regime(self, bar: Candle, now: datetime):
        move = self.move3
        if move is None or bar_end(self.threes[-1], 3) != now:
            return
        before, latest = self.threes[-2:]
        if self.leg is None:
            side = 1 if move > 0 else -1
            if abs(move) < max(15.0, 0.55 * self.atr3) or not beyond(
                latest.close, edge(before, side), side, 0.10 * self.atr
            ):
                return
            pivot = Swing(defense(before, side), before.start, bar_end(before, 3))
            self.create_leg(side, pivot, bar)
            watch = self.register(side, 'IMBALANCE', pivot, now)
            self.add_trigger(watch, 'TREND_BREAK', edge(before, side), pivot, now, now)
            return
        leg = self.leg
        side = leg.side
        if (
            self.pending_flip
            and self.pending_flip[0] == -side
            and beyond(move, 0.0, -side, max(6.0, 0.20 * self.atr3))
        ):
            other, boundary, first = self.pending_flip
            if held(self.bars, boundary, other):
                pivots = self.pivots3[other]
                pivot = (
                    pivots[-1]
                    if pivots and now - pivots[-1].at <= WATCH_LENGTH
                    else Swing(defense(before, other), before.start, bar_end(before, 3))
                )
                self.create_leg(other, pivot, bar)
                watch = self.register(other, 'STRUCTURE_CHANGE', pivot, now)
                self.add_trigger(watch, 'TREND_BREAK', boundary, pivot, first, now)

    def monitor_leg(self, bar: Candle, now: datetime):
        leg = self.leg
        if leg is None:
            return
        side = leg.side
        atr = self.atr
        if held(self.bars, leg.protected.price, -side, 0.10 * atr):
            if self.pending_flip is None:
                self.pending_flip = (-side, leg.protected.price, bar_end(self.bars[-2]))
        elif held(self.bars, leg.protected.price, side):
            self.pending_flip = None

        favorable = edge(bar, side)
        if beyond(favorable, leg.origin.price, side, 50.0):
            leg.spent = True
        if leg.pullback:
            if beyond(leg.pullback.price, defense(bar, side), side):
                leg.pullback = Swing(defense(bar, side), bar.start, now)
            if beyond(bar.close, leg.extreme.price, side, 0.05):
                pivot = leg.pullback
                watch = self.register(side, 'PULLBACK', pivot, now)
                meaningful = any(
                    p.at >= pivot.at - 2 * MINUTE
                    and p.at > leg.origin.at
                    and abs(p.price - pivot.price) <= max(3.0, 0.35 * atr)
                    for p in self.pivots3[side][-3:]
                )
                if (
                    not leg.spent
                    or meaningful
                    or leg.pullback_block
                    or now - self.opens <= 18 * MINUTE
                ):
                    self.add_trigger(
                        watch,
                        'CONTINUATION',
                        leg.extreme.price,
                        pivot,
                        now,
                        now,
                        retest=True,
                        mature=leg.spent and now - self.opens > 18 * MINUTE,
                    )
                leg.extreme = Swing(favorable, bar.start, now)
                leg.pullback = None
                leg.pullback_block = False
        else:
            if beyond(favorable, leg.extreme.price, side):
                leg.extreme = Swing(favorable, bar.start, now)
            opening = now - self.opens <= 18 * MINUTE
            compact = (
                self.move3 is not None
                and bar_end(self.threes[-1], 3) == now
                and beyond(self.move3, 0, -side, max(6.0, 0.20 * self.atr3))
            )
            distance = (
                max(10.0, 0.50 * atr, 0.25 * self.atr3)
                if opening
                else max(9.0, 0.60 * atr, 0.35 * self.atr3)
                if compact
                else max(12.0, 0.85 * atr, 0.85 * self.atr3)
            )
            if beyond(leg.extreme.price, bar.close, side, distance):
                leg.pullback = Swing(defense(bar, side), bar.start, now)
                leg.pullback_block = compact

        if len(self.bars) < 3 or self.region:
            return
        prior, probe, response = self.bars[-3:]
        test = defense(probe, side)
        if (
            beyond(prior.close, probe.close, side, max(10.0, 0.85 * atr))
            and beyond(response.close, prior.close, side, 0.10 * atr)
            and beyond(response.close, probe.close, side, max(13.0, 1.1 * atr))
            and abs(defense(response, side) - test) <= max(3.0, 0.35 * atr)
            and beyond(leg.extreme.price, test, side, max(15.0, 0.70 * self.atr3))
        ):
            pivot = Swing(test, probe.start, now)
            watch = self.register(side, 'RECLAIM', pivot, now)
            self.add_trigger(
                watch, 'PULLBACK_RECLAIM', prior.close, pivot, now, now, retest=True
            )

    def monitor_protected_retest(self, bar: Candle, now: datetime):
        leg = self.leg
        if leg is None or len(self.bars) < 4 or not self.threes:
            return
        side = leg.side
        pivot = latest_pivot(self.bars, side, 1)
        if pivot is None or pivot.at <= leg.protected.at:
            return
        protected = leg.protected.price
        prior, probe = self.bars[-3], self.bars[-2]
        level = prior.close
        atr = self.atr
        if (
            abs(pivot.price - protected) <= max(5.0, 0.70 * atr)
            and beyond(probe.close, pivot.price, side, max(10.0, 0.75 * atr))
            and beyond(probe.close, level, side, max(7.0, 0.60 * atr))
            and beyond(bar.close, level, side, 0.10 * atr)
            and any(b.start <= pivot.at < bar_end(b, 3) for b in self.threes[-2:])
        ):
            watch = self.register(side, 'PROTECTED_LEVEL_RETEST', pivot, now)
            self.add_trigger(
                watch,
                'STRUCTURAL_RETEST',
                level,
                pivot,
                bar_end(probe),
                now,
                retest=True,
                mature=leg.spent,
            )

    def monitor_retests(self, bar: Candle, now: datetime):
        if not self.trend:
            return
        recent = self.bars[-22:]
        tolerance = max(5.0, min(15.0, 0.70 * self.atr))
        for watch in list(self.watches.values()):
            side = watch.side
            second = Swing(defense(bar, side), bar.start, now)
            if (
                watch.kind != 'LEVEL'
                or watch.stopped_at
                or watch.spent_at
                or now > watch.until
                or second.at - watch.level.at < 3 * MINUTE
                or abs(watch.level.price - second.price) > tolerance
            ):
                continue
            middle = [b for b in recent if watch.level.at < b.start < second.at]
            outer = min(watch.level.price * side, second.price * side)
            if not middle or any(side * defense(b, side) < outer for b in middle):
                continue
            reaction = max((edge(b, side) for b in middle), key=lambda x: x * side)
            near = max(watch.level.price * side, second.price * side)
            if reaction * side - near < max(12.0, 0.9 * self.atr) or max(
                b.close * side for b in middle
            ) - near < max(7.0, 0.55 * self.atr):
                continue
            prev = self.retests.get(watch.id)
            separated = prev is not None and any(
                prev.second.at < b.start < second.at
                and beyond(b.close, prev.second.price, side, max(10.0, 0.70 * self.atr))
                for b in middle
            )
            if prev is None or separated:
                self.retests[watch.id] = Retest(
                    watch, second, reaction, side == self.trend
                )

        for key, retest in list(self.retests.items()):
            if (
                now - retest.second.known_at > 8 * MINUTE
                or retest.watch.stopped_at
                or retest.watch.spent_at
            ):
                del self.retests[key]
                continue
            if beyond(bar.close, retest.trigger, retest.watch.side, 0.10 * self.atr):
                # One first break per two-test structure. A nearby second
                # candle belongs to the existing defense. Updates to other
                # watches never restart this clock.
                trend_aligned = retest.trend_aligned
                formed = any(
                    b.start <= retest.second.at < bar_end(b, 3)
                    for b in self.threes[-2:]
                )
                if not trend_aligned or formed:
                    kind = 'CONTINUATION_RETEST' if trend_aligned else 'REVERSAL'
                    self.add_trigger(
                        retest.watch,
                        kind,
                        retest.trigger,
                        retest.protective,
                        now,
                        now,
                        retest=True,
                        mature=trend_aligned and self.leg.spent,
                        setup_origin=retest.second.known_at,
                    )

    def monitor_range(self, bar: Candle, now: datetime):
        if self.breakout and now - self.breakout.first_break > WATCH_LENGTH:
            self.breakout = None
        if self.region is None and self.breakout is None:
            fresh = [
                e
                for e in self.triggers.values()
                if e.confirmed_at == now and e.kind == 'PULLBACK_RECLAIM'
            ]
            if not fresh:
                self.region = consolidation(self.bars, self.atr, self.atr3)
        region = self.region
        if region:
            for side in (1, -1):
                level = region.boundary(side)
                key = (region.established_at, side)
                if key in self.range_break_ids or not held(
                    self.bars, level, side, region.margin
                ):
                    continue
                self.range_break_ids.add(key)
                prior = [
                    w.level
                    for w in self.watches.values()
                    if w.kind == 'LEVEL'
                    and w.side == side
                    and region.low <= w.level.price <= region.high
                ]
                pivot = (
                    prior[-1]
                    if prior
                    else Swing(
                        region.boundary(-side),
                        region.established_at,
                        region.established_at,
                    )
                )
                first = bar_end(self.bars[-2])
                watch = self.register(side, 'RANGE_EDGE', pivot, now)
                self.add_trigger(
                    watch, 'RANGE_BREAK', level, pivot, first, now, range_edge=level
                )
                self.region = None
                self.breakout = RangeBreak(region, side, first)
                if self.leg is None or self.leg.side != side:
                    self.create_leg(side, pivot, bar)
                break
            return
        broken = self.breakout
        if (
            not broken
            or broken.retest_completed
            or now - broken.first_break < DISPATCH_INTERVAL
        ):
            return
        side = broken.side
        level = broken.zone.boundary(side)
        if held(self.bars, broken.zone.boundary(-side), -side, broken.zone.margin):
            self.region, self.breakout = broken.zone, None
            return
        pivot = latest_pivot(self.bars, side, 1)
        if (
            pivot
            and abs(pivot.price - level) <= max(3.0, 0.65 * self.atr)
            and held(self.bars, level, side)
            and beyond(bar.close, edge(self.bars[-2], side), side)
            and beyond(bar.close, self.bars[-3].close, side)
        ):
            watch = self.register(side, 'EDGE_RETEST', pivot, now)
            self.add_trigger(
                watch,
                'RANGE_RETEST',
                edge(self.bars[-2], side),
                pivot,
                now,
                now,
                retest=True,
                range_edge=level,
            )
            broken.retest_completed = True

    def advance(self, bar: Candle, three: Candle | None, ten: Candle | None):
        self.bars.append(bar)
        now = bar_end(bar)
        if three:
            self.threes.append(three)
        if ten:
            self.tens.append(ten)
        self.atr = volatility(self.bars, minimum=2.5)
        self.atr3 = volatility(self.threes, minimum=2.5)
        self.maintain_watches(bar, now)
        self.monitor_leg(bar, now)
        self.monitor_retests(bar, now)
        self.monitor_protected_retest(bar, now)
        self.process_regime(bar, now)
        self.monitor_range(bar, now)
        for side in (1, -1):
            pivot = latest_pivot(self.bars, side, 1)
            if pivot:
                self.register(side, 'LEVEL', pivot, now)
            if three and (pivot := latest_pivot(self.threes, side, 3)):
                self.pivots3[side].append(pivot)
                if (
                    self.leg
                    and self.leg.side == side
                    and self.pending_flip is None
                    and pivot.at > self.leg.protected.at
                    and beyond(pivot.price, self.leg.protected.price, side)
                ):
                    self.leg.protected = pivot
            if ten and (pivot := latest_pivot(self.tens, side, 10)):
                self.pivots10[side].append(pivot)

    def opportunities(self, spot: float, now: datetime) -> list[EntryTrigger]:
        candidates = list(self.triggers.values())
        for retest in self.retests.values():
            watch = retest.watch
            if (
                not retest.trend_aligned
                and retest.second.known_at == self.through
                and beyond(spot, retest.trigger, watch.side, max(2.0, 0.20 * self.atr))
            ):
                candidate = self.trigger(
                    watch,
                    'REVERSAL',
                    retest.trigger,
                    retest.protective,
                    retest.second.known_at,
                    self.through,
                    retest=True,
                    live=True,
                    setup_origin=retest.second.known_at,
                )
                if candidate.id not in self.triggers:
                    candidates.append(candidate)
        return sorted(
            (x for x in candidates if now <= x.expires_at + DISPATCH_INTERVAL),
            key=lambda x: (x.first_break, x.kind == 'REVERSAL'),
            reverse=True,
        )

    def regime(self, band: StrikeBand | None) -> str:
        if self.region:
            values = [band.pairs.get(i) for i in (-2, -1, 1, 2)] if band else []
            if not values or any(x is None or x.changes is None for x in values):
                return 'RANGE_OI_UNAVAILABLE'
            return 'SIDEWAYS' if all(x.quiet for x in values) else 'MIXED_RANGE'
        return {-1: 'CONTINUOUS_BEARISH', 0: 'UNCLASSIFIED', 1: 'CONTINUOUS_BULLISH'}[
            self.trend
        ]


def build_book(bars: list[Candle], opens: datetime) -> PriceBook:
    bars = contiguous_tail(bars)
    threes = {bar_end(b, 3): b for b in aggregate(bars, 3, opens)}
    tens = {bar_end(b, 10): b for b in aggregate(bars, 10, opens)}
    book = PriceBook(opens)
    for bar in bars:
        through = bar_end(bar)
        book.advance(bar, threes.get(through), tens.get(through))
    return book


@dataclass(frozen=True)
class StrikeConfirmation:
    entry: OIPair
    defense: OIPair
    entry_unwind: float | None
    defense_build: float | None
    rule: str | None

    @classmethod
    def check(
        cls, entry: OIPair, defense: OIPair, side: int, retest: bool
    ) -> StrikeConfirmation:
        offered = entry.call if side == 1 else entry.put
        supporting = defense.put if side == 1 else defense.call
        unwind = -offered.increase if offered else None
        buildup = supporting.increase if supporting else None
        rule = None
        if unwind is not None and buildup is not None and min(unwind, buildup) > 0:
            if max(unwind, buildup) >= OI_LEVEL_MATERIAL_CHANGE:
                rule = 'ENTRY_AND_DEFENSE_2_PERCENT'
            elif (
                retest
                and max(unwind, buildup) >= EARLY_RETEST_OI_CHANGE
                and min(unwind, buildup) >= 0.005
            ):
                rule = 'DEFENDED_RETEST_1_9_PERCENT'
        return cls(entry, defense, unwind, buildup, rule)

    @property
    def score(self) -> float:
        return (self.entry_unwind or 0) + (self.defense_build or 0)

    def public(self) -> dict:
        return {
            'entry_pair': self.entry.public(),
            'defense_pair': self.defense.public(),
            'entry_unwind_pct': self.entry_unwind * 100
            if self.entry_unwind is not None
            else None,
            'defense_build_pct': self.defense_build * 100
            if self.defense_build is not None
            else None,
            'rule': self.rule,
        }


@dataclass(frozen=True)
class Choice:
    offset: int
    contract: dict
    signal: StrikeConfirmation

    def public(self):
        return {
            'offset': self.offset,
            'strike': self.signal.entry.strike,
            **self.signal.public(),
        }


def chain_choices(
    tr: EntryTrigger,
    grid: list[float],
    band: StrikeBand,
    pairs: dict[float, OIPair],
    contracts: dict,
    previous: dict[float, OIPair] | None,
) -> tuple[list[Choice], list[dict]]:
    center, side = grid.index(band.atm), tr.side
    options, checks = [], []
    for offset in (-side, -2 * side):
        adjacent = center + offset - side
        entry = band.pairs.get(offset)
        if entry is None or not 0 <= adjacent < len(grid):
            continue
        ds = grid[adjacent]
        adjacent_pair = pairs.get(ds, OIPair(ds, None, None))
        confirmation = StrikeConfirmation.check(entry, adjacent_pair, side, tr.retest)
        if not confirmation.rule and previous is not None:
            old = StrikeConfirmation.check(
                previous.get(entry.strike, OIPair(entry.strike, None, None)),
                previous.get(ds, OIPair(ds, None, None)),
                side,
                False,
            )
            a, b, c, d = (
                confirmation.entry_unwind,
                confirmation.defense_build,
                old.entry_unwind,
                old.defense_build,
            )
            if (
                all(x is not None and x > 0 for x in (a, b, c, d))
                and max(1 - (1 - a) * (1 - c), (1 + b) * (1 + d) - 1)
                >= OI_LEVEL_MATERIAL_CHANGE
            ):
                confirmation = replace(
                    confirmation, rule='TWO_CONSECUTIVE_WINDOWS_2_PERCENT'
                )
        contract = contracts.get(('CE' if side == 1 else 'PE', entry.strike))
        checks.append(
            {'offset': offset, 'strike': entry.strike, **confirmation.public()}
        )
        if contract and confirmation.rule:
            options.append(Choice(offset, contract, confirmation))
    return options, checks


def targets(
    book: PriceBook, previous: list[Candle], window: OIWindow, spot: float, side: int
) -> tuple:
    grades = {p.price: 'CONFIRMED_10M_SWING' for p in book.pivots10[-side][-8:]}
    for p in swings(previous, -side, duration=10, left=1)[-12:]:
        grades.setdefault(p.price, 'PRIOR_10M_SWING')
    # A barrier for room-to-target must have been revisited by separate
    # completed local swings. Single historical extrema remain objectives.
    tolerance = max(5.0, 0.35 * book.atr3)
    local = [p.price for p in book.pivots3[-side][-18:]]
    structures = tuple(
        level
        for level in grades
        if sum(abs(p - level) <= tolerance for p in local) >= 2
    )
    for level in oi_levels(window, spot, side, book.atr):
        grades.setdefault(level.strike, 'OI_OBJECTIVE')

    def choose(lo, hi):
        middle = (lo + hi) / 2
        within = [p for p in grades if lo <= side * (p - spot) <= hi]
        if within:
            price = min(
                within,
                key=lambda p: (
                    abs(side * (p - spot) - middle),
                    grades[p] == 'OI_OBJECTIVE',
                    p * side,
                ),
            )
            return price, grades[price]
        return round(spot + side * middle, 4), 'ENTRY_SPOT_DISTANCE'

    return choose(*T1_SPOT_BAND), choose(*T2_SPOT_BAND), structures


def evaluate(
    tr: EntryTrigger,
    book: PriceBook,
    spot: float,
    now: datetime,
    clock_at: datetime,
    band: StrikeBand | None,
    grid: list[float],
    pairs: dict[float, OIPair],
    contracts: dict,
    window: OIWindow | None,
    previous_oi: dict[float, OIPair] | None,
    prior: list[Candle],
    state: dict,
    cfg: Config,
) -> tuple[dict, list[Choice], RiskPlan | None]:
    side = tr.side
    watch = book.watches[tr.watch_id]
    gap = side * (spot - tr.level)
    failures = []
    if now > tr.expires_at:
        failures.append('TRIGGER_EXPIRED')
    if watch.spent_at or beyond(spot, tr.first_objective, side):
        failures.append('FIRST_OBJECTIVE_ALREADY_TRAVELLED')
    if watch.stopped_at or not beyond(spot, tr.defense.price, side):
        failures.append('PRICE_DEFENSE_INVALIDATED')
    if now > watch.until:
        failures.append('WATCH_EXPIRED')
    if clock_at < tr.confirmed_at:
        failures.append('INDEX_QUOTE_PREDATES_TRIGGER')
    if gap <= (max(2.0, 0.20 * book.atr) if tr.live_condition else 0.0) or (
        not tr.live_condition and not beyond(book.bars[-1].close, tr.level, side)
    ):
        failures.append('PRICE_BACK_BEHIND_TRIGGER')
    if gap > tr.max_extension:
        failures.append('ENTRY_EXTENDED_FROM_FIRST_BREAK')
    if (
        tr.mature_leg
        and side * (spot - tr.defense.price) > 1.4 * cfg.initial_stop_points
    ):
        failures.append('TOO_FAR_FROM_NEW_DEFENDED_SWING')
    region = book.region
    if region is None and book.breakout:
        broken = book.breakout.zone
        if all(broken.low <= bar.close <= broken.high for bar in book.bars[-2:]):
            region = broken
    if region and not (
        tr.kind == 'REVERSAL'
        and tr.retest
        and beyond(spot, region.boundary(side), side)
    ):
        failures.append('INTACT_RANGE')
    if tr.range_edge is not None and not beyond(spot, tr.range_edge, side):
        failures.append('PRICE_BACK_INSIDE_BROKEN_RANGE')
    if (
        tr.kind in ('TREND_BREAK', 'CONTINUATION', 'CONTINUATION_RETEST')
        and book.trend != side
    ):
        failures.append('TREND_NO_LONGER_ALIGNED')
    if (previous_exit := state.get('last_exit')) and timestamp(
        previous_exit['at']
    ).date() == book.through.date():
        last_at = timestamp(previous_exit['at'])
        if tr.first_break <= last_at:
            failures.append('TRIGGER_PREDATES_POSITION_EXIT')
        elif (
            previous_exit.get('reason') == 'STRUCTURAL_SL'
            and previous_exit.get('direction')
            == ('BULLISH' if side == 1 else 'BEARISH')
            and tr.defense.at < last_at
        ):
            failures.append('FRESH_DEFENSE_REQUIRED_AFTER_STOP')

    plan = None
    options = []
    strikes = []
    if window and band:
        options, strikes = chain_choices(tr, grid, band, pairs, contracts, previous_oi)
        if not options:
            failures.append('ENTRY_AND_DEFENSE_OI_NOT_ALIGNED')
        (t1, t1_source), (t2, t2_source), barriers = targets(
            book, prior, window, spot, side
        )
        reward = side * (t1 - spot) / cfg.initial_stop_points
        buffer = max(17.0, 0.8 * book.atr3)
        room = min(
            (
                side * (level - spot)
                for level in barriers
                if side * (level - spot) >= buffer
            ),
            default=None,
        )
        # Resistance beyond the execution noise can cap the planned reward.
        if room is not None and room < T1_SPOT_BAND[0]:
            failures.append('INSUFFICIENT_ROOM_TO_T1')
        if cfg.min_reward_risk and reward < cfg.min_reward_risk:
            failures.append('T1_REWARD_TO_RISK_BELOW_MINIMUM')
        stop = round(spot - side * cfg.initial_stop_points, 4)
        if min(stop, t1, t2) <= 0 or not beyond(t2, t1, side):
            failures.append('INVALID_RISK_LEVELS')
        if not failures:
            plan = RiskPlan(
                stop,
                t1,
                t2,
                t1_source,
                t2_source,
                cfg.initial_stop_points,
                round(reward, 4),
                'LIVE_INDEX_DISTANCE',
            )
    else:
        room = None
        failures.append('MATCHED_OI_OR_LISTED_ATM_UNAVAILABLE')
    return (
        {
            'trigger_id': tr.id,
            'watch_id': tr.watch_id,
            'kind': tr.kind,
            'first_break_at': tr.first_break.isoformat(),
            'expires_at': tr.expires_at.isoformat(),
            'spot': spot,
            'margin_from_break': round(gap, 4),
            'distance_to_known_barrier': room,
            'first_objective': tr.first_objective,
            'failed_checks': failures,
            'strikes': strikes,
            'eligible_strikes': [o.signal.entry.strike for o in options],
        },
        options,
        plan,
    )


def watch_quote_keys(
    book: PriceBook, spot: float, now: datetime, grid: list[float], contracts: dict
):
    if not grid or not grid[0] <= spot <= grid[-1]:
        return []
    ix = grid.index(nearest_strike(grid, spot))
    directions = {
        w.side
        for w in book.watches.values()
        if not w.stopped_at
        and not w.spent_at
        and w.until >= now
        and abs(w.level.price - spot) <= max(35.0, 2.5 * book.atr3)
    }
    directions.update(
        t.side for t in book.opportunities(spot, now) if t.expires_at >= now
    )
    keys = {}
    for side in sorted(directions):
        for offset in (-side, -2 * side):
            for center in range(max(0, ix - 1), min(len(grid), ix + 2)):
                k = center + offset
                if 0 <= k < len(grid):
                    contract = contracts.get(('CE' if side == 1 else 'PE', grid[k]))
                    if contract:
                        keys[contract['instrument_key']] = None
    return list(keys)


def manage_position(
    initial: dict,
    price: ClosedPrice,
    book: PriceBook | None,
    spot: float | None,
    spot_at: datetime | None,
    now: datetime,
    deadline: datetime,
    cfg: Config,
    previous: list[Candle],
    directional_oi: bool,
):
    position = copy.deepcopy(initial)
    side = 1 if position['direction'] == 'BULLISH' else -1
    opened = timestamp(position['opened_at'])
    cursor = max(timestamp(position['last_candle']) + MINUTE, exact_minute(opened))
    events, warnings = [], []
    pivots = {p.known_at: p for p in book.pivots3[side]} if book else {}
    blocks = {bar_end(b, 3): i for i, b in enumerate(book.threes)} if book else {}

    def emit(kind, at, **data):
        events.append((kind, position_event_payload(position, at, **data)))

    def close(kind, at, reason, level, source, spot_value):
        position['remaining_pct'] = 0
        emit(
            kind,
            at,
            reason=reason,
            underlying_reference=level,
            source=source,
            email_observation={
                'spot': spot_value,
                'spot_is_close': source.startswith(('COMPLETED_1M', 'COMPLETED_3M')),
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
            warnings.append('GAP_IN_UNOBSERVED_POSITION_BARS')
            break
        stop, t2 = position['stop'], position['t2']
        adverse, favorable = defense(bar, side), edge(bar, side)
        observation = {'spot': bar.close, 'spot_is_close': True, 'stop': stop, 't2': t2}
        modified = position.get('adjusted_at')
        if bar.start < opened:
            if not beyond(adverse, stop, side) or not beyond(
                position['t1'], favorable, side
            ):
                warnings.append('ENTRY_MINUTE_TOUCH_SEQUENCE_UNKNOWN')
            adverse = favorable = bar.close
        elif modified and bar.start < timestamp(modified) < at:
            old_stop = position.get('stop_before_adjustment', stop)
            if not beyond(adverse, old_stop, side):
                warnings.append('STOP_ADJUSTMENT_MINUTE_LEVEL_UNCERTAIN')
                return close(
                    'EXIT',
                    at,
                    'STRUCTURAL_SL',
                    old_stop,
                    'COMPLETED_1M_OLD_STOP_BREACHED',
                    bar.close,
                )
            if not beyond(adverse, stop, side):
                warnings.append('STOP_ADJUSTMENT_MINUTE_TOUCH_SEQUENCE_UNKNOWN')
            adverse = bar.close
            if t2 != position.get('t2_before_adjustment', t2):
                warnings.append('TARGET_ADJUSTMENT_MINUTE_TOUCH_SEQUENCE_UNKNOWN')
                favorable = bar.close
        hit_t1 = not position.get('t1_hit') and side * (favorable - position['t1']) >= 0
        hit_t2 = side * (favorable - t2) >= 0
        if not beyond(adverse, stop, side):
            if hit_t1 or hit_t2:
                warnings.append('SAME_MINUTE_STOP_TARGET_SEQUENCE_UNKNOWN_STOP_FIRST')
            return close(
                'EXIT', at, 'STRUCTURAL_SL', stop, 'COMPLETED_1M_STOP_TOUCH', bar.close
            )
        if hit_t1:
            position.update(
                t1_hit=True,
                t1_at=at.isoformat(),
                remaining_pct=100 - position.get('t1_exit_pct', 50),
            )
            emit(
                'T1',
                at,
                old_stop=stop,
                new_stop=stop,
                underlying_reference=position['t1'],
                source='COMPLETED_1M_TARGET_TOUCH',
                email_observation=observation,
            )
        if hit_t2 and position.get('t1_hit'):
            return close(
                'T2',
                at,
                'SPOT_TARGET_REACHED',
                t2,
                'COMPLETED_1M_TARGET_TOUCH',
                bar.close,
            )

        # A buffered, confirmed pivot can protect the remainder once both
        # its formation and its confirmation happened after the partial exit.
        pivot = pivots.get(at)
        if position.get('t1_at') and pivot and pivot.at >= timestamp(position['t1_at']):
            # Use volatility observed at this pivot, rather than a value
            # computed using bars from later in the decision batch.
            atr = volatility([b for b in price.bars if bar_end(b) <= at], minimum=2.5)
            atr3 = volatility(
                [b for b in book.threes if bar_end(b, 3) <= at], minimum=2.5
            )
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
                    'ADJUST_SL',
                    at,
                    reason='CONFIRMED_POST_T1_SWING',
                    old_stop=stop,
                    new_stop=candidate,
                    old_t2=t2,
                    new_t2=t2,
                    email_observation={'spot': bar.close, 'spot_is_close': True},
                )
        invalidation = position.get('setup_invalidation')
        block = blocks.get(at, 0)
        if (
            position.get('policy_version') == VERSION
            and invalidation is not None
            and block >= 1
        ):
            last = [b for b in price.bars if opened <= b.start and bar_end(b) <= at][
                -2:
            ]
            if held(last, invalidation, -side) and beyond(
                book.threes[block].close, book.threes[block - 1].close, -side
            ):
                return close(
                    'EXIT',
                    at,
                    'CONFIRMED_ZONE_REVERSAL',
                    bar.close,
                    'COMPLETED_3M_PRICE_INVALIDATION',
                    bar.close,
                )
        position['last_candle'] = bar.start.isoformat()
        cursor = at

    if (
        spot is not None
        and spot_at is not None
        and opened <= spot_at <= min(now, deadline)
    ):
        modified = position.get('adjusted_at')
        if (not modified or spot_at >= timestamp(modified)) and not beyond(
            spot, position['stop'], side
        ):
            return close(
                'EXIT',
                spot_at,
                'STRUCTURAL_SL',
                position['stop'],
                'FRESH_INDEX_QUOTE',
                spot,
            )
    if now >= deadline:
        return close(
            'EXIT', deadline, 'SESSION_REFERENCE_EXIT', spot, 'SESSION_CUTOFF', spot
        )

    # Extend only before the original objective is touched, when a verified
    # post-T1 swing protects the remainder and current OI still confirms.
    if (
        book
        and cfg.arm_continuation_runner
        and position.get('runner')
        and position.get('protective_swing')
        and position.get('t1_hit')
        and directional_oi
        and spot is not None
        and spot_at is not None
        and position['last_candle'] == book.bars[-1].start.isoformat()
        and position.get('t2_source') != 'RUNNER_STRUCTURE'
    ):
        old = position['t2']
        new_levels = {
            value
            for b in book.tens + previous
            for value in (edge(b, side), b.close)
            if beyond(value, old, side, max(5.0, 0.40 * book.atr))
            and max(12.0, 0.8 * book.atr3)
            <= side * (value - spot)
            <= max(45.0, 2.2 * book.atr3)
        }
        near = max(12.0, book.atr)
        if (
            new_levels
            and 0 < side * (old - spot) <= near
            and beyond(position['stop'], position['entry_spot'], side)
        ):
            new = min(new_levels, key=lambda x: side * x)
            position.update(
                t2=new,
                t2_source='RUNNER_STRUCTURE',
                adjusted_at=now.isoformat(),
                stop_before_adjustment=position['stop'],
                t2_before_adjustment=old,
            )
            emit(
                'ADJUST_SL',
                now,
                reason='RUNNER_TARGET_EXTENDED',
                old_stop=position['stop'],
                new_stop=position['stop'],
                old_t2=old,
                new_t2=new,
                email_observation={'spot': spot},
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
            raise DataError('Scan clock requires a timezone')
        value = value.astimezone(IST)
        if self.last is not None and value < self.last:
            raise DataError('Scan clock moved backward')
        self.last = value
        self.samples.append(value.isoformat())
        if self.sink is not None:
            self.sink.append(self.samples[-1])
        return value


def add_position_events(
    state: dict, result: dict, cfg: Config, position, events, closed, warnings, now
) -> None:
    result['management_warnings'] = warnings
    for kind, detail in events:
        result['alerts_created'].append(new_event(state, kind, detail, now))
    if closed is not None:
        state['history'] = (state['history'] + [closed])[-cfg.max_state_history :]
        state['last_exit'] = {
            'at': closed['closed_at'],
            'direction': closed['direction'],
            'id': closed['id'],
            'reason': closed['exit_reason'],
        }
    state['position'] = position
    result['position_locked'] = position is not None
    result['decision'] = 'POSITION_CLOSED' if closed else 'POSITION_OPEN'
    result['reason'] = closed['exit_reason'] if closed else 'REFERENCE_POSITION_MANAGED'


def capture_price(
    price: ClosedPrice, api, clock: ScanClock, session, cfg: Config, result: dict
) -> ClosedPrice:
    try:
        raw = api.candles()
        return merge_closed_price(price, raw, clock(), session, cfg)
    except (DataError, ProviderError) as exc:
        result['candle_error'] = str(exc)
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
        ring = engine['oi_samples']
        window = match_oi(ring, sample, cfg)
        retained = [s for s in ring if received - timestamp(s['at']) < 15 * MINUTE]
        if not any(
            s['through'] == slot.isoformat() and s['expiry'] == expiry for s in retained
        ):
            retained.append(jsonable(asdict(sample)))
        engine['oi_samples'] = retained[-8:]
        result['oi'] = {
            'status': 'MATCHED' if window else 'OI_WINDOW_UNAVAILABLE',
            'at': sample.at.isoformat(),
            'through': slot.isoformat(),
            'expiry': expiry,
            'baseline': window.baseline.isoformat() if window else None,
            'matched_contracts': len(window.changes) if window else 0,
        }
        return contracts, window
    except (DataError, ProviderError, KeyError, ValueError, TypeError) as exc:
        clock()
        result['oi'] = {'status': 'OPTION_CHAIN_UNAVAILABLE', 'reason': str(exc)}
        return contracts, None


def scan(state: dict, api, cfg: Config, clock_fn=None, clock_sink: list | None = None):
    clock = ScanClock(clock_fn, clock_sink)
    now = clock()
    engine = ensure_engine(state, now)
    active = state.get('position')
    result = {
        'version': VERSION,
        'at': now.isoformat(),
        'session_date': now.date().isoformat(),
        'decision': 'NO_TRADE',
        'reason': 'UNSET',
        'alerts_created': [],
        'position_locked': bool(active),
        'evaluations': [],
    }

    def finish(reason):
        if result['decision'] in ('POSITION_OPEN', 'POSITION_CLOSED'):
            result['entry_check'] = reason
        else:
            result['reason'] = reason
        return result, clock.samples

    hard_exit = day_time(now, *HARD_EXIT)
    if active and timestamp(active['opened_at']).date() < now.date():
        cutoff = day_time(timestamp(active['opened_at']), *HARD_EXIT)
        closed = close_reference(
            active,
            cutoff,
            'PRIOR_SESSION_REFERENCE_EXPIRED',
            None,
            'CLOCK_NO_PRIOR_SESSION_FILL',
        )
        event = (
            'EXIT',
            position_event_payload(
                active,
                now,
                reason=closed['exit_reason'],
                effective_at=cutoff.isoformat(),
            ),
        )
        add_position_events(state, result, cfg, None, [event], closed, [], now)
        return result, clock.samples
    if now >= hard_exit and not active:
        return finish('AFTER_SESSION_EXIT_CUTOFF')
    try:
        session = api.session(now)
    except (DataError, ProviderError) as exc:
        session = None
        result['session_failure'] = str(exc)
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
            result['decision'] = 'POSITION_MONITORING_UNAVAILABLE'
        return finish('NO_VERIFIED_NFO_SESSION')
    opens, closes = session
    deadline = min(hard_exit, closes)

    price = ClosedPrice([])
    try:
        price = merge_closed_price(
            price, engine.get('closed_candles', []), now, session, cfg
        )
    except DataError as exc:
        result['candle_cache_error'] = str(exc)
    price = capture_price(price, api, clock, session, cfg, result)
    old_oi = engine['oi_samples'][:]
    contracts, window = (
        capture_oi(api, engine, clock, cfg, result)
        if clock.last < deadline
        else ([], None)
    )
    expected = exact_minute(clock.last - timedelta(seconds=cfg.feed_grace_seconds))
    if price.through != expected and clock.last + timedelta(seconds=8) < deadline:
        price = capture_price(price, api, clock, session, cfg, result)
    engine['closed_candles'] = [serialize_bar(b) for b in price.bars]
    book = build_book(price.bars, opens) if price.bars else None
    prior = prior_context(engine, api, clock.last) if book else []
    grid = listed_strikes(contracts)
    pairs = paired_oi(window)
    listed = {
        (row['instrument_type'], float(row['strike_price'])): row
        for row in contracts
        if not window or row['expiry'] == window.snapshot.expiry
    }
    previous = None
    if window and cfg.allow_persistent_oi:
        prior_raw = next(
            (
                x
                for x in reversed(old_oi)
                if timestamp(x['at']) == window.baseline
                and x['expiry'] == window.snapshot.expiry
            ),
            None,
        )
        if prior_raw:
            previous = paired_oi(match_oi(old_oi, OISnapshot.restore(prior_raw), cfg))

    def index_quote(quotes, now):
        quote = quotes.get(INDEX)
        return checked_quote(quote, now, cfg.quote_max_age_seconds), timestamp(
            quote['timestamp']
        )

    spot = quote_at = None
    try:
        q = api.quotes([INDEX])
        spot, quote_at = index_quote(q, clock())
    except (DataError, ProviderError, KeyError) as exc:
        result['index_quote_error'] = str(exc)
    now = clock()
    initial_atm = (
        StrikeBand.build(grid, spot, pairs).atm
        if spot is not None and grid and grid[0] <= spot <= grid[-1]
        else None
    )
    orders = (
        watch_quote_keys(book, spot, now, grid, listed)
        if book and spot is not None and now < deadline and listed
        else []
    )
    fresh_book = {}
    if orders:
        try:
            q = api.quotes([INDEX, *orders])
            final_spot, final_at = index_quote(q, clock())
            if final_at < quote_at:
                raise DataError('FINAL_INDEX_QUOTE_MOVED_BACKWARD')
            spot, quote_at, fresh_book = final_spot, final_at, q
        except (DataError, ProviderError, KeyError) as exc:
            result['book_error'] = str(exc)
    now = clock()
    if (
        quote_at is not None
        and (now - quote_at).total_seconds() > cfg.quote_max_age_seconds
    ):
        spot = quote_at = None
    expected = exact_minute(now - timedelta(seconds=cfg.feed_grace_seconds))
    result['candle_coverage'] = price.audit(expected)
    if (
        window
        and (now - window.snapshot.at).total_seconds() > cfg.quote_max_age_seconds
    ):
        window, previous, pairs = None, None, {}
        result['oi']['status'] = 'STALE_AT_DECISION'
    if window:
        result['oi']['candle_through_at_decision'] = (
            price.through.isoformat() if price.through else None
        )
    band = StrikeBand.build(grid, spot, pairs) if spot is not None else None
    result['watch_quote_capture'] = {
        'requested_option_count': len(orders),
        'returned_option_count': sum(k in fresh_book for k in orders),
        'initial_atm': initial_atm,
        'final_atm': band.atm if band else None,
    }

    if active:
        confirms = False
        if (
            window
            and active.get('defense_strike') is not None
            and active['expiry'] == window.snapshot.expiry
        ):
            ds, es = active['defense_strike'], active['strike']
            strength = StrikeConfirmation.check(
                pairs.get(es, OIPair(es, None, None)),
                pairs.get(ds, OIPair(ds, None, None)),
                1 if active['side'] == 'CE' else -1,
                False,
            )
            result['active_defense_oi'] = strength.public()
            confirms = bool(strength.rule)
        values = manage_position(
            active, price, book, spot, quote_at, now, deadline, cfg, prior, confirms
        )
        add_position_events(state, result, cfg, *values, now)
        if values[0] and spot is None and not price.bars:
            result.update(
                decision='POSITION_MONITORING_UNAVAILABLE',
                reason='PRICE_FEED_UNAVAILABLE',
            )

    if book is None:
        return finish('NO_COMPLETED_SESSION_CANDLES')
    result['market_assessment'] = {
        'state': book.regime(band),
        'through': book.through.isoformat(),
        'spot': spot,
        'index_quote_at': quote_at.isoformat() if quote_at else None,
        'move_3m': book.move3,
        'range': jsonable(asdict(book.region)) if book.region else None,
        'leg': jsonable(asdict(book.leg)) if book.leg else None,
        'strike_band': band.public() if band else None,
        'watches': [
            jsonable(asdict(w)) | {'id': w.id}
            for w in book.watches.values()
            if not w.stopped_at and not w.spent_at and w.until >= now
        ],
        'retests': jsonable([asdict(r) for r in book.retests.values()]),
    }
    if now < max(day_time(now, *ENTRY_START), opens + 6 * MINUTE):
        return finish('COLLECTING_OPENING_BASELINE')
    if not price.covers_entry(expected) or price.tail_size < 6:
        return finish('CLOSED_PRICE_UNAVAILABLE_FOR_ENTRY')
    if spot is None:
        return finish('INDEX_QUOTE_UNAVAILABLE_FOR_ENTRY')
    if now >= min(day_time(now, *ENTRY_END), deadline - 10 * MINUTE):
        return finish('OUTSIDE_ENTRY_WINDOW')

    live_breaks = engine.setdefault('v138_live_breaks', {})
    opportunities = []
    for trigger in book.opportunities(spot, now):
        if trigger.live_condition:
            live_breaks.setdefault(trigger.id, exact_minute(quote_at).isoformat())
        if observed := live_breaks.get(trigger.id):
            first = (
                min(timestamp(observed), trigger.first_break)
                if not trigger.live_condition
                else timestamp(observed)
            )
            trigger = replace(
                trigger, first_break=first, expires_at=entry_deadline(first, opens)
            )
        opportunities.append(trigger)
    engine['v138_live_breaks'] = {
        k: v for k, v in live_breaks.items() if now - timestamp(v) < WATCH_LENGTH
    }
    opportunities.sort(
        key=lambda tr: (tr.first_break, tr.kind == 'REVERSAL'), reverse=True
    )
    if not opportunities:
        return finish(
            'INTACT_RANGE' if book.region else 'WATCHING_LEVELS_WITHOUT_TRIGGER'
        )
    result['candidates'] = [
        jsonable(asdict(tr)) | {'id': tr.id} for tr in opportunities
    ]
    last_practical_reason = None
    entered = engine.setdefault('v138_entered', [])
    viable = []
    for tr in opportunities:
        evidence, choices, plan = evaluate(
            tr,
            book,
            spot,
            now,
            quote_at,
            band,
            grid,
            pairs,
            listed,
            window,
            previous,
            prior,
            state,
            cfg,
        )
        failures = evidence['failed_checks']
        if tr.id in entered:
            failures.append('TRIGGER_ALREADY_ALERTED')
        if state.get('position'):
            failures.append('ACTIVE_REFERENCE_POSITION')
        result['evaluations'].append(evidence)
        if last_practical_reason is None:
            last_practical_reason = failures[0] if failures else None
        if plan is None or failures:
            continue
        for choice in choices:
            check = choice.public()
            evidence.setdefault('quote_checks', []).append(check)
            row = choice.contract
            try:
                live = live_contract(
                    row,
                    fresh_book.get(row['instrument_key']),
                    now,
                    quote_at,
                    band,
                    choice.offset,
                    cfg,
                )
            except (DataError, KeyError, ValueError, TypeError) as exc:
                check['quote_reason'] = str(exc)
                last_practical_reason = 'DIRECTIONAL_OPTION_QUOTES_UNAVAILABLE'
                continue
            check['quote_reason'] = 'QUALIFIED_QUOTE'
            live['oi_confirmation'] = choice.signal.public()
            # Latest causal trigger first, then confirmed setup and OI.
            viable.append(
                (
                    (
                        -tr.first_break.timestamp(),
                        tr.live_condition,
                        -choice.signal.score,
                        live['spread_pct'],
                        -live['depth_lots'],
                        abs(choice.offset),
                        live['instrument_key'],
                    ),
                    tr,
                    plan,
                    live,
                )
            )
    if not viable:
        return finish(last_practical_reason or 'NO_QUALIFIED_REFERENCE')
    if len({candidate.side for _, candidate, _, _ in viable}) > 1:
        return finish('CONFLICTING_QUALIFIED_DIRECTIONS')
    _, tr, plan, contract = min(viable, key=lambda row: row[0])
    key = contract['instrument_key']
    position = {
        'id': hashlib.sha256(f'{tr.id}|{key}'.encode()).hexdigest()[:22],
        'status': 'OPEN',
        'direction': 'BULLISH' if tr.side == 1 else 'BEARISH',
        'side': contract['side'],
        'strike': contract['strike'],
        'expiry': contract['expiry'],
        'instrument_key': key,
        'opened_at': now.isoformat(),
        'entry_spot': spot,
        'entry_ask': contract['ask'],
        'initial_stop': plan.stop,
        'defense_strike': contract['oi_confirmation']['defense_pair']['strike'],
        'setup_level': tr.level,
        'setup_invalidation': tr.defense.price,
        'policy_version': VERSION,
        'last_candle': book.bars[-1].start.isoformat(),
        'scenario': tr.kind,
        't1_hit': False,
        'remaining_pct': 100,
        'contract': contract,
        **asdict(plan),
    }
    if (
        cfg.arm_continuation_runner
        and tr.kind
        in ('CONTINUATION', 'TREND_BREAK', 'PULLBACK_RECLAIM', 'RANGE_RETEST')
        and (book.move3 is not None and tr.side * book.move3 >= STRONG_MOVE)
    ):
        position['runner'] = {'armed_at': now.isoformat(), 'checkpoint': plan.t2}
    state['position'] = position
    entered.append(tr.id)
    engine['v138_entered'] = entered[-80:]
    facts = {
        'index_quote_at': quote_at.isoformat(),
        'option_quote_at': contract['quote_time'],
        'first_break_at': tr.first_break.isoformat(),
        'candle_through': book.through.isoformat(),
        'oi_snapshot_at': window.snapshot.at.isoformat(),
        'initial_atm': initial_atm,
        'final_atm': band.atm,
    }
    event = position_event_payload(
        position,
        now,
        reason='QUALIFIED_PRICE_AND_3M_OI',
        signal=jsonable(asdict(tr)) | {'id': tr.id},
        plan=asdict(plan),
        entry_evidence=facts,
        oi={'window': result['oi'], 'entry_and_defense': contract['oi_confirmation']},
    )
    result['alerts_created'].append(new_event(state, 'ENTRY', event, now))
    result.update(
        decision='ENTRY',
        reason='QUALIFIED_' + contract['side'],
        position_locked=True,
        selected_position=position,
        entry_evidence=facts,
    )
    return result, clock.samples


def email_price(value: Any, pattern: str) -> str:
    try:
        number = read_number(value, 'email price', positive=True)
    except (DataError, OverflowError):
        return 'Unavailable'
    return format(number, pattern).rstrip('0').rstrip('.')


def mail_content(event: dict) -> tuple[str, str]:
    details = event.get('details') or {}
    position = details.get('position') or {}
    observation = event.get('email_observation') or {}
    kind = event['kind']
    reason = details.get('reason')

    event_time = None
    for value in (
        details.get('effective_at'),
        details.get('observed_at'),
        event.get('created_at'),
    ):
        try:
            event_time = timestamp(value)
            break
        except DataError:
            continue
    short_time = (
        event_time.strftime('%I:%M %p').lstrip('0') if event_time else 'Unavailable'
    )
    full_time = 'Unavailable'
    if event_time:
        date_text = event_time.strftime('%d %b %Y')
        clock_text = event_time.strftime('%I:%M:%S %p').lstrip('0')
        full_time = f'{date_text}, {clock_text} IST'

    side = position.get('side')
    strike = email_price(position.get('strike'), '.2f')
    contract = f'{strike} {side}' if side in ('CE', 'PE') else strike
    premium = email_price(position.get('entry_ask'), '.2f')
    spot = observation.get('spot')
    if kind == 'ENTRY':
        spot = position.get('entry_spot')
    elif not observation and (
        (kind in ('EXIT', 'T2') and details.get('source') == 'FRESH_INDEX_QUOTE')
        or (kind == 'EXIT' and reason == 'CONFIRMED_ZONE_REVERSAL')
    ):
        spot = details.get('underlying_reference')
    spot_text = email_price(spot, ',.4f')
    if observation.get('spot_is_close'):
        spot_text += ' (1-minute candle close)'

    if kind == 'EXIT':
        subject_label, status = {
            'STRUCTURAL_SL': ('SL HIT', 'SL Hit'),
            'SESSION_REFERENCE_EXIT': ('Session exit', 'Session exit'),
            'PRIOR_SESSION_REFERENCE_EXPIRED': ('Session exit', 'Session exit'),
            'CONFIRMED_ZONE_REVERSAL': ('Reversal exit', 'Reversal exit'),
            'RUNNER_CONTINUATION_NOT_CONFIRMED': (
                'Runner exit',
                'Runner continuation unconfirmed',
            ),
        }.get(reason, ('Exit', 'Exited'))
    elif kind == 'ADJUST_SL':
        status = (
            'T2 updated'
            if reason in ('T2_REFINED_AFTER_T1', 'RUNNER_TARGET_EXTENDED')
            else 'SL adjusted'
        )
        subject_label = status
    else:
        subject_label, status = {
            'ENTRY': ('Entry', 'Selected'),
            'T1': ('Target - T1', 'T1 reached'),
            'T2': ('Target T2', 'T2 reached'),
        }[kind]
    subject = f'{subject_label} | {contract} @ {premium} - Time: {short_time}'

    t1 = email_price(position.get('t1'), ',.4f')
    t2 = email_price(observation.get('t2', position.get('t2')), ',.4f')
    stop = email_price(observation.get('stop', position.get('stop')), ',.4f')
    fields = [
        f'NIFTY Spot: {spot_text}',
        f'Strike: {contract}',
        f'Option price at selection: {premium}',
        f'T1 (underlying): {t1}',
        f'T2 (underlying): {t2}',
        f'SL (underlying): {stop}',
    ]
    touch = observation.get('target_touch_extreme')
    if kind in ('T1', 'T2') and touch in ('high', 'low', 'close'):
        trigger_spot = email_price(observation.get('target_touch_spot'), ',.4f')
        fields.append(f'Target touch: {trigger_spot} (1-minute {touch})')
    if (
        kind == 'T1'
        and details.get('old_stop') is not None
        and details.get('new_stop') is not None
    ):
        previous = email_price(details['old_stop'], ',.4f')
        updated = email_price(details['new_stop'], ',.4f')
        if details['old_stop'] == details['new_stop']:
            fields.append(f'SL retained for remaining position: {updated}')
        else:
            fields.append(
                f'SL adjustment for remaining position: {previous} -> {updated}'
            )
    runner = position.get('runner')
    if runner and kind == 'ENTRY':
        fields.append(
            'After T1: the remaining position can continue through the initial T2 checkpoint'
        )
    if kind == 'T1':
        fields.append(
            f'Remaining reference position: {position.get("remaining_pct", 50)}%'
        )
    fields.extend(
        (
            f'Status: {status}',
            f'Timestamp: {full_time}',
        )
    )
    return subject, '\n'.join(fields)


def arm_delivery(state: dict, token: str, now: datetime) -> int:
    if not token:
        raise ScannerError('Notification claim token required')
    count = 0
    for e in state['outbox']:
        if (
            e.get('kind') in ALERT_KINDS
            and e.get('status') == 'CLAIMED'
            and e.get('claim') == token
        ):
            # MUST be COMMITTED and PUSHED before the first SMTP socket.
            e.update(
                status='DELIVERY_UNCERTAIN',
                attempted_at=now.isoformat(),
                smtp_stage='ARMED_NO_NETWORK',
            )
            count += 1
    return count


def deliver_armed(state: dict, path: Path, token: str) -> int:
    if not token:
        raise ScannerError('NOTIFICATION_CLAIM_TOKEN required')
    pending = [
        x
        for x in state['outbox']
        if x.get('status') == 'DELIVERY_UNCERTAIN'
        and x.get('smtp_stage') == 'ARMED_NO_NETWORK'
        and x.get('claim') == token
        and x.get('kind') in ALERT_KINDS
    ]
    if not pending:
        return 0
    sender = os.environ.get('EMAIL_SENDER', '')
    receiver = os.environ.get('EMAIL_RECEIVER', '')
    password = os.environ.get('EMAIL_PASSWORD', '')
    username = os.environ.get('EMAIL_USERNAME') or sender
    host = os.environ.get('SMTP_HOST', 'smtp.gmail.com')
    port = int(os.environ.get('SMTP_PORT', '465'))
    if not (sender and receiver and password and username):
        raise ScannerError('SMTP secrets missing; claims remain safe and undelivered')
    unknown = False
    for e in pending:
        title, body = mail_content(e)
        m = EmailMessage()
        m['From'] = sender
        m['To'] = receiver
        m['Subject'] = title
        m['Message-ID'] = '<' + e['id'] + '@' + sender.rsplit('@', 1)[-1] + '>'
        m.set_content(body)
        # Remote state was already ARMED and committed by the workflow.
        # Update local state to record execution; no automatic retry after crash.
        e.update(smtp_stage='LOCAL_SEND_STARTED')
        save_state(path, state)
        try:
            with smtplib.SMTP_SSL(
                host, port, timeout=20, context=ssl.create_default_context()
            ) as client:
                e['smtp_stage'] = 'AUTHENTICATE'
                client.login(username, password)
                e['smtp_stage'] = 'SEND'
                client.send_message(m)
            e.update(
                status='SENT',
                sent_at=datetime.now(IST).isoformat(),
                smtp_stage='ACCEPTED_BY_SMTP',
            )
        except (OSError, smtplib.SMTPException) as exc:
            e.update(status='DELIVERY_UNCERTAIN', smtp_error_type=type(exc).__name__)
            unknown = True
        save_state(path, state)
    return 1 if unknown else 0


def shadow_mode() -> bool:
    return os.environ.get('NIFTY_V138_SHADOW') == '1'


def paths() -> tuple[Path, Path]:
    if shadow_mode():
        return Path('state/market_state_v138_shadow.json'), Path('audit/v138_shadow')
    return Path(os.environ.get('STATE_FILE', 'state/market_state_v120_3.json')), Path(
        os.environ.get('AUDIT_DIR', 'audit')
    )


def environment_config() -> Config:
    try:
        raw = json.loads((os.environ.get('NIFTY_SCANNER_CONFIG') or '{}'))
    except json.JSONDecodeError as exc:
        raise ScannerError('Invalid NIFTY_SCANNER_CONFIG JSON') from exc
    if not isinstance(raw, dict):
        raise ScannerError('Configuration must be JSON object')
    for legacy in (
        'oi_entry_floor_bps',
        'oi_entry_ceiling_bps',
        'min_stop_atr',
        'max_stop_atr',
        'max_unretested_leg_atr',
        'cooldown_minutes',
        'allow_atm_reversal',
        'reversal_strike_stop',
        'max_chase_atr',
        'max_initial_risk_points',
    ):
        raw.pop(legacy, None)
    # v133 stored these values as defaults in some deployed configurations.
    # Explicit non-default overrides still apply.
    if raw.get('min_reward_risk') == 1.25:
        raw.pop('min_reward_risk')
    if 't1_min_reward_risk' in raw:
        raw['min_reward_risk'] = raw.pop('t1_min_reward_risk')
    try:
        return Config(**raw)
    except TypeError as exc:
        raise ScannerError('Unknown scanner configuration fields') from exc


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
    before = json.dumps(state, sort_keys=True, allow_nan=False, separators=(',', ':'))
    before_hash = hashlib.sha256(before.encode()).hexdigest()
    observations = []
    clock = None
    if replay_clock is not None:
        itr = iter(replay_clock)

        def clock():
            try:
                return timestamp(next(itr))
            except StopIteration as exc:
                raise ScannerError('REPLAY_CLOCK_SAMPLES_EXHAUSTED') from exc

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
            'version': VERSION,
            'decision': 'ERROR',
            'reason': type(exc).__name__,
            'detail': str(exc),
            'at': datetime.now(IST).isoformat(),
            'position_locked': bool(state.get('position')),
        }
    now = datetime.now(IST) if not observations else timestamp(observations[0])
    scan_state_hash = hashlib.sha256(
        json.dumps(
            state, sort_keys=True, allow_nan=False, separators=(',', ':')
        ).encode()
    ).hexdigest()
    # Even on upstream failure, preserve the open position and all queued
    # lifecycle events; never regenerate a missing state from scratch.
    if not shadow_mode():
        claim_outbox(state, token, now)
    event = {
        'mode': 'SHADOW' if shadow_mode() else 'LIVE',
        'event': 'SCAN',
        'at': now.isoformat(),
        'version': VERSION,
        'before_state_sha256': before_hash,
        'result': result,
        'alerts_pending': [
            x['id']
            for x in state['outbox']
            if x.get('status') == 'CLAIMED' and x.get('claim') == token
        ],
    }
    if capture:
        raw = {
            'version': VERSION,
            'scan_started_at': now.isoformat(),
            'clock_samples': observations,
            'calls': actor.calls,
            'config': asdict(cfg),
            'before_state_sha256': before_hash,
            'before_state': json.loads(before),
            'after_scan_state_sha256': scan_state_hash,
            'result': result,
            'email_observations': True,
            'source_file_sha256': hashlib.sha256(
                Path(__file__).read_bytes()
            ).hexdigest(),
        }
        if cfg.record_inputs and not (
            result.get('reason')
            in (
                'AFTER_SESSION_EXIT_CUTOFF',
                'NO_VERIFIED_NFO_SESSION',
                'BEFORE_FIRST_OI_BASELINE',
            )
            and not result.get('position_locked')
        ):
            session_date = now.date().isoformat()
            run_id = (
                os.environ.get('GITHUB_RUN_ID', 'local')
                + '-'
                + os.environ.get('GITHUB_RUN_ATTEMPT', '1')
            )
            captured_at = now.strftime('%H%M%S-%f')
            safe = ''.join(x if x.isalnum() or x in '-_' else '_' for x in run_id)
            file = (
                audit_dir
                / ('inputs_' + AUDIT_RELEASE)
                / session_date
                / (captured_at + '-' + safe + '.json.gz')
            )
            record_inputs(file, raw)
            event['input_recording'] = str(file)
    if result.get('reason') != 'AFTER_SESSION_EXIT_CUTOFF' or event['alerts_pending']:
        append_audit(
            audit_dir / (f'market_scan_{AUDIT_RELEASE}_{now.date().isoformat()}.jsonl'),
            event,
        )
    if failure:
        result['audit_recorded'] = True
    return result


def replay_recordings(directory: Path, cfg: Config, output: Path) -> int:
    """Replay recordings produced by this release.

    Mismatched API call sequences fail rather than silently substituting a
    future price, date, quote, or contract not captured at that decision time.
    """
    files = sorted(directory.rglob('*.json.gz'))
    if not files:
        raise ScannerError('NO_CAPTURED_INPUTS_FOUND_FOR_' + AUDIT_RELEASE.upper())
    records = []
    last_at = None
    for file in files:
        try:
            with gzip.open(file, 'rt', encoding='utf-8') as f:
                r = json.load(f)
            if r.get('version') != VERSION:
                raise ScannerError('Different recording engine version')
            if not r.get('clock_samples'):
                raise ScannerError('NO_CAPTURED_CLOCK_SAMPLES')
            sample = timestamp(r['clock_samples'][0])
            if last_at is not None and sample < last_at:
                raise ScannerError('CAPTURES_NOT_CHRONOLOGICAL')
            last_at = sample
            # Every invocation replays its EXACT saved pre-scan state. This
            # prevents synthetic paper-flat positions from polluting historical
            # decisions and preserves open-position locks from earlier versions.
            s = r.get('before_state')
            if not isinstance(s, dict):
                raise ScannerError('PRE_SCAN_STATE_NOT_RECORDED')
            validate_state(s)
            state_hash = hashlib.sha256(
                json.dumps(
                    s, sort_keys=True, allow_nan=False, separators=(',', ':')
                ).encode()
            ).hexdigest()
            if state_hash != r.get('before_state_sha256'):
                raise ScannerError('PRE_SCAN_STATE_SHA256_MISMATCH')
            api = ReplayProvider(r['calls'])
            clock = iter(r['clock_samples'])
            recorded_cfg = Config(**r['config']) if 'config' in r else cfg
            evaluated, _ = scan(
                s, api, recorded_cfg, clock_fn=lambda: timestamp(next(clock))
            )
            if next(clock, None) is not None:
                raise ScannerError('Captured clock samples were not all consumed')
            if api.index != len(api.calls):
                raise ScannerError(
                    'Captured calls not all consumed; replay not equivalent'
                )
            if not r.get('email_observations'):
                # Older v128 captures predate the optional email-only facts.
                for event in s['outbox']:
                    event.pop('email_observation', None)
            new_hash = hashlib.sha256(
                json.dumps(
                    s, sort_keys=True, allow_nan=False, separators=(',', ':')
                ).encode()
            ).hexdigest()
            matching = jsonable(evaluated) == r.get('result') and new_hash == r.get(
                'after_scan_state_sha256'
            )
            records.append(
                {
                    'file': str(file),
                    'as_of': sample.isoformat(),
                    'decision': evaluated.get('decision'),
                    'reason': evaluated.get('reason'),
                    'expected_decision': r.get('result', {}).get('decision'),
                    'matches_original_decision': matching,
                    'pre_state_sha256_verified': True,
                    'post_state_sha256_verified': new_hash
                    == r.get('after_scan_state_sha256'),
                    'position_locked': bool(s.get('position')),
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
            records.append(
                {'file': str(file), 'status': 'REPLAY_INCOMPLETE', 'error': str(exc)}
            )
            break
    report = {
        'engine': VERSION,
        'recordings': len(files),
        'processed': len(records),
        'unverified_original_market_history': True,
        'replay_is_not_proof_of_live_fill_or_profitability': True,
        'records': records,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, allow_nan=False), encoding='utf-8')
    print(
        json.dumps(
            {
                'status': 'REPLAY_COMPLETE'
                if all('status' not in x for x in records)
                else 'REPLAY_INCOMPLETE',
                'report': str(output),
                'processed': len(records),
                'total': len(files),
            }
        )
    )
    return (
        0
        if all(x.get('matches_original_decision') for x in records)
        and len(records) == len(files)
        else 1
    )


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--version', action='store_true')
    action.add_argument('--initialize-flat', action='store_true')
    action.add_argument('--scan-and-claim', action='store_true')
    action.add_argument('--arm-delivery', action='store_true')
    action.add_argument('--deliver-armed', action='store_true')
    action.add_argument('--reconcile-flat', metavar='POSITION_ID')
    action.add_argument('--requeue-alert', metavar='ALERT_ID')
    action.add_argument('--migrate-state', metavar='SOURCE')
    action.add_argument(
        '--replay-recordings',
        metavar='DIR',
        help=f'Replay recorded {AUDIT_RELEASE} price and OI inputs',
    )
    parser.add_argument('--replay-report', default=f'audit/replay_{AUDIT_RELEASE}.json')
    args = parser.parse_args(argv)
    if args.version:
        print(VERSION)
        return 0
    try:
        cfg = environment_config()
        if args.replay_recordings:
            return replay_recordings(
                Path(args.replay_recordings), cfg, Path(args.replay_report)
            )
        state_path, audit_dir = paths()
        if shadow_mode() and not args.scan_and_claim:
            raise ScannerError('Shadow mode supports only the scan workflow')
        token = os.environ.get('NOTIFICATION_CLAIM_TOKEN', '')
        with local_lock(state_path):
            if args.initialize_flat:
                if os.environ.get('MANUAL_FLAT_CONFIRMED') != '1':
                    raise ScannerError('MANUAL_FLAT_CONFIRMED=1 required')
                if state_path.exists():
                    raise ScannerError('REFUSING_TO_OVERWRITE_EXISTING_STATE')
                save_state(state_path, starting_state(datetime.now(IST)))
                print(json.dumps({'status': 'INITIALIZED_FLAT_REFERENCE_ONLY'}))
                return 0
            if args.migrate_state:
                if state_path.exists():
                    raise ScannerError('Destination exists; no overwrites')
                src = Path(args.migrate_state)
                state = load_state(src)
                ensure_engine(state, datetime.now(IST))
                save_state(state_path, state)
                print(
                    json.dumps(
                        {
                            'status': 'MIGRATED_NONDESTRUCTIVE',
                            'position_locked': bool(state.get('position')),
                        }
                    )
                )
                return 0
            state = (
                starting_state(datetime.now(IST))
                if shadow_mode() and not state_path.exists()
                else load_state(state_path)
            )
            if args.reconcile_flat:
                if os.environ.get('MANUAL_FLAT_CONFIRMED') != '1':
                    raise ScannerError('Operator must verify broker/alerts flat')
                p = state.get('position')
                if not p or p['id'] != args.reconcile_flat:
                    raise ScannerError('Position ID does not match active lock')
                closed = dict(
                    p,
                    status='CLOSED',
                    closed_at=datetime.now(IST).isoformat(),
                    exit_reason='OPERATOR_VERIFIED_FLAT_UNKNOWN_FILL',
                    fill_confirmed=False,
                )
                state['history'].append(closed)
                state['position'] = None
                state['last_exit'] = {
                    'at': closed['closed_at'],
                    'direction': closed['direction'],
                    'id': closed['id'],
                }
                save_state(state_path, state)
                append_audit(
                    audit_dir
                    / (
                        f'market_scan_{AUDIT_RELEASE}_{datetime.now(IST).date().isoformat()}.jsonl'
                    ),
                    {
                        'event': 'MANUAL_RECONCILIATION',
                        'position_id': p['id'],
                        'at': closed['closed_at'],
                    },
                )
                print(
                    json.dumps(
                        {'status': 'REFERENCE_LOCK_RECONCILED', 'position_id': p['id']}
                    )
                )
                return 0
            if args.requeue_alert:
                if os.environ.get('MANUAL_ALERT_UNDELIVERED_CONFIRMED') != '1':
                    raise ScannerError(
                        'Explicit verified mailbox non-delivery confirmation required'
                    )
                event = next(
                    (x for x in state['outbox'] if x['id'] == args.requeue_alert), None
                )
                if (
                    not event
                    or event.get('kind') not in ALERT_KINDS
                    or event.get('status') not in ('CLAIMED', 'DELIVERY_UNCERTAIN')
                ):
                    raise ScannerError('Alert not eligible for verified manual retry')
                event.update(
                    status='PENDING',
                    claim=None,
                    manually_requeued_at=datetime.now(IST).isoformat(),
                )
                event.pop('attempted_at', None)
                save_state(state_path, state)
                print(
                    json.dumps({'status': 'MANUALLY_REQUEUED', 'event_id': event['id']})
                )
                return 0
            if args.arm_delivery:
                count = arm_delivery(state, token, datetime.now(IST))
                save_state(state_path, state)
                print(json.dumps({'status': 'DELIVERY_ARMED', 'count': count}))
                return 0
            if args.deliver_armed:
                return deliver_armed(state, state_path, token)
            if not token:
                raise ScannerError('NOTIFICATION_CLAIM_TOKEN missing')
            api = Upstox(os.environ.get('UPSTOX_ANALYTICS_TOKEN', ''))
            result = recorded_scan(state, api, cfg, audit_dir, token)
            save_state(state_path, state)
            print(json.dumps(result, sort_keys=True, allow_nan=False))
            return (
                1
                if result['decision'] in ('ERROR', 'POSITION_MONITORING_UNAVAILABLE')
                else 0
            )
    except (ScannerError, OSError, ValueError, TypeError, BlockingIOError) as exc:
        print(
            json.dumps(
                {'status': 'ERROR', 'reason': type(exc).__name__, 'detail': str(exc)},
                allow_nan=False,
            ),
            file=sys.stderr,
        )
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
