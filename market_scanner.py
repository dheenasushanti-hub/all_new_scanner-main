#!/usr/bin/env python3
"""NIFTY options reference-alert scanner, Python 3.11.

Production entry points implement the existing Cloudflare/GitHub Actions and
state/outbox interfaces. Structure, paired OI, contract quotes and position
management are independent decision stages. Historical market data is never
substituted for a live quote. Run regressions with test_market_scanner.py.
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
from dataclasses import dataclass, asdict
from datetime import datetime, date, timedelta, timezone
from email.message import EmailMessage
from pathlib import Path
from statistics import median
from typing import Any
from urllib.parse import urlencode, quote
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError

VERSION = '136.1.0'
AUDIT_RELEASE = 'v136_1'
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


# Decision policy. Infrastructure and the persisted schema remain independent.
MINUTE = timedelta(minutes=1)
DISPATCH_INTERVAL = 3 * MINUTE
MAX_ENTRY_CANDLE_LAG = MINUTE
MAX_TRIGGER_AGE = DISPATCH_INTERVAL + MAX_ENTRY_CANDLE_LAG
CANDLE_REFRESH_REQUEST_BUDGET = timedelta(seconds=16)
OI_LEVEL_MATERIAL_CHANGE = 0.02
EARLY_RETEST_OI_CHANGE = 0.019
T1_SPOT_BAND = (45.0, 50.0)
T2_SPOT_BAND = (80.0, 90.0)
STRONG_MOVE = 15.0
MIN_STOP_POINTS = 2.0
MIN_STOP_ATR_FRACTION = 0.30
CONTAINMENT_MINUTES = 18
STOP_REENTRY_LOOKBACK = 15


@dataclass(frozen=True)
class Config:
    oi_jitter_seconds: int = 35
    feed_grace_seconds: float = 2.0
    quote_max_age_seconds: int = 35
    quote_max_skew_seconds: int = 12
    max_chase_atr: float = 0.75
    min_reward_risk: float = 0.0
    max_spread_percent: float = 2.0
    min_depth_lots: float = 1.0
    max_state_history: int = 240
    record_inputs: bool = True
    arm_continuation_runner: bool = True
    reversal_strike_stop: bool = False

    def __post_init__(self):
        flags = (
            'record_inputs',
            'arm_continuation_runner',
            'reversal_strike_stop',
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

    def score(self, side: int) -> float:
        if self.changes is None:
            return 0.0
        call, put = self.changes
        return side * (put - call)

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


@dataclass(frozen=True)
class Pattern:
    side: int
    first: Swing
    second: Swing
    neckline: float
    confirmed_at: datetime

    @property
    def stop(self) -> float:
        return self.side * min(
            self.side * self.first.price, self.side * self.second.price
        )


@dataclass(frozen=True)
class Signal:
    side: int
    kind: str
    at: datetime
    trigger: float
    oi_level: float
    defended: bool = False
    reversal: Pattern | None = None

    @property
    def identity(self) -> str:
        return f'{self.side}:{self.kind}:{self.at.isoformat()}:{self.trigger:.4f}'


@dataclass(frozen=True)
class RangeEscape:
    bounds: tuple[float, float]
    signal: Signal
    margin: float

    def clear(self, value: float) -> bool:
        return self.signal.side * (value - self.signal.trigger) > self.margin

    def permits(self, signal: Signal, spot: float, close: float) -> bool:
        if signal.side != self.signal.side or signal.at < self.signal.at:
            return False
        if self.clear(spot) and self.clear(close):
            return True
        # After a confirmed outer break, a fresh defended retest may
        # deliberately come back to that same boundary.
        return (
            signal.defended
            and signal.trigger == self.signal.trigger
            and signal.side * (spot - signal.trigger) > 0
            and signal.side * (close - signal.trigger) > 0
        )


@dataclass(frozen=True)
class PriceContext:
    bars: list[Candle]
    threes: list[Candle]
    tens: list[Candle]
    prior_ten: list[Candle]
    atr: float
    atr3: float
    atr10: float
    direction: int
    move: float | None
    acceleration: float | None
    trend: int
    protected: float | None
    broken_side: int
    broken_level: float | None
    broken_at: datetime | None
    bounds: tuple[float, float] | None
    patterns: dict[int, Pattern]
    signals: list[Signal]
    range_escape: RangeEscape | None = None

    @property
    def at(self) -> datetime:
        return bar_end(self.bars[-1])

    def public(self, band: StrikeBand | None) -> dict:
        quiet = band is not None and all(
            k in band.pairs and band.pairs[k].quiet for k in (-2, -1, 1, 2)
        )
        weak = (
            self.move is not None
            and self.acceleration is not None
            and abs(self.move) < STRONG_MOVE
            and abs(self.acceleration) < STRONG_MOVE
        )
        state = 'MIXED'
        if self.bounds is not None:
            if (
                quiet
                and weak
                and self.bounds[1] - self.bounds[0] <= 2 * max(self.atr3, self.atr10)
            ):
                state = 'SIDEWAYS'
        elif self.broken_side and -self.broken_side in self.patterns:
            state = 'BULLISH_REVERSAL' if self.broken_side == -1 else 'BEARISH_REVERSAL'
        elif self.direction and self.direction == self.trend:
            state = 'CONTINUOUS_BULLISH' if self.trend == 1 else 'CONTINUOUS_BEARISH'
        return {
            'state': state,
            'through': self.at.isoformat(),
            'trend': self.trend,
            'protected': self.protected,
            'broken_level': self.broken_level,
            'break_confirmed_at': self.broken_at.isoformat()
            if self.broken_at
            else None,
            'range': self.bounds,
            'range_escape': jsonable(asdict(self.range_escape))
            if self.range_escape
            else None,
            'move_3m': self.move,
            'acceleration_3m': self.acceleration,
            'atr_1m': self.atr,
            'atr_3m': self.atr3,
            'atr_10m': self.atr10,
            'reversal_patterns': [jsonable(asdict(p)) for p in self.patterns.values()],
        }


def three_direction(threes: list[Candle]) -> int:
    if len(threes) < 2 or threes[-1].start - threes[-2].start != DISPATCH_INTERVAL:
        return 0
    first, last = threes[-2:]
    if last.high < first.high and last.low < first.low and last.close < first.close:
        return -1
    if last.high > first.high and last.low > first.low and last.close > first.close:
        return 1
    return 0


def defended_range(bars: list[Candle], atr: float) -> tuple[float, float] | None:
    if len(bars) != 9:
        return None
    lower = min(bar.low for bar in bars)
    upper = max(bar.high for bar in bars)
    width = upper - lower
    if not max(8.0, 1.2 * atr) <= width <= 3.8 * atr:
        return None
    if abs(bars[-1].close - bars[0].close) > 0.55 * width:
        return None
    middle = (lower + upper) / 2
    edge_distance = max(1.0, 0.25 * atr)
    for side, level in ((1, lower), (-1, upper)):
        touches = [
            i
            for i, b in enumerate(bars)
            if abs((b.low if side == 1 else b.high) - level) <= edge_distance
        ]
        if not any(
            j - i >= 2
            and any(side * (bar.close - middle) >= 0 for bar in bars[i + 1 : j])
            for i in touches
            for j in touches
        ):
            return None
    return lower, upper


def broader_containment(bars: list[Candle], atr: float) -> tuple[float, float] | None:
    """Recognize an overlapping auction from completed bars even with single edge tests."""
    if len(bars) != CONTAINMENT_MINUTES:
        return None
    lower = min(bar.low for bar in bars)
    upper = max(bar.high for bar in bars)
    width = upper - lower
    if not max(8.0, 1.2 * atr) <= width <= 4.2 * atr:
        return None
    closes = [bar.close for bar in bars]
    displacement = abs(closes[-1] - closes[0])
    travel = sum(abs(new - old) for old, new in zip(closes, closes[1:]))
    if displacement > 0.30 * width or displacement > 0.24 * travel:
        return None
    # Require repeated traversals of the middle zone. Closes oscillating
    # inside a small band around the midpoint do not count as crossings.
    middle = (lower + upper) / 2
    deadband = 0.08 * width
    sides = [
        1 if close > middle else -1
        for close in closes
        if abs(close - middle) >= deadband
    ]
    if sum(old != new for old, new in zip(sides, sides[1:])) < 3:
        return None
    return lower, upper


def local_patterns(bars: list[Candle], atr: float, side: int) -> list[Pattern]:
    """Two closed tests with an intact zone and an intervening closed reaction."""
    tests = swings(bars, side, left=1)
    tolerance = min(15.0, max(3.0, 0.65 * atr))
    position = {b.start: i for i, b in enumerate(bars)}
    patterns = []
    for j, second in enumerate(tests):
        second_index = position[second.at]
        candidates = []
        for first in reversed(tests[:j]):
            between = bars[position[first.at] + 1 : second_index]
            extremes = [side * (bar.low if side == 1 else bar.high) for bar in between]
            if not between or abs(first.price - second.price) > tolerance:
                continue
            if (
                min(extremes)
                < min(side * first.price, side * second.price) - 0.25 * tolerance
            ):
                continue
            inner = max(side * (bar.high if side == 1 else bar.low) for bar in between)
            if inner - max(side * first.price, side * second.price) < max(
                8.0, 0.50 * atr
            ):
                continue
            if max(side * (bar.close - first.price) for bar in between) < max(
                3.0, 0.28 * atr
            ):
                continue
            stop = min(side * first.price, side * second.price)
            for bar in bars[second_index:]:
                edge = bar.low if side == 1 else bar.high
                if side * edge < stop:
                    break
                if side * bar.close > inner:
                    candidates.append(
                        Pattern(
                            side,
                            first,
                            second,
                            side * inner,
                            max(bar_end(bar), second.known_at),
                        )
                    )
                    break
        if candidates:
            patterns.append(
                min(
                    candidates,
                    key=lambda pattern: (
                        side * pattern.stop,
                        -side * pattern.neckline,
                        pattern.confirmed_at,
                    ),
                )
            )
    return patterns


def accepted_level(bars: list[Candle], side: int, level: float) -> bool:
    return len(bars) >= 2 and all(side * (bar.close - level) > 0 for bar in bars[-2:])


def held_boundary(
    bars: list[Candle], threes: list[Candle], side: int, boundary: float, margin: float
) -> bool:
    if len(bars) < 2 or not threes:
        return False
    level = boundary + side * margin
    return (
        bar_end(threes[-1], 3) >= bars[-1].start
        and side * (threes[-1].close - level) > 0
        and accepted_level(bars, side, level)
    )


def analyze_price(
    bars: list[Candle], prior_ten: list[Candle], session_open: datetime
) -> PriceContext:
    """Walk completed data once in timestamp order. A later bar never relabels an earlier trigger."""
    bars = contiguous_tail(bars)
    threes = aggregate(bars, 3, session_open)
    tens = aggregate(bars, 10, session_open)
    three_count = 0
    direction = trend = broken_side = 0
    protected = broken_level = None
    broken_at = None
    bounds = None
    range_escape = None
    signals: dict[str, Signal] = {}
    patterns: dict[int, Pattern] = {}
    atr = 3.0

    for i, bar in enumerate(bars):
        prefix = bars[: i + 1]
        at = bar_end(bar)
        while three_count < len(threes) and bar_end(threes[three_count], 3) <= at:
            three_count += 1
        completed = threes[:three_count]
        direction = three_direction(completed)
        atr = volatility(prefix, minimum=2.5)
        atr3 = volatility(completed, minimum=2.5)
        prior = prefix[-2] if i else None
        range_break = None
        margin = max(1.0, 0.25 * atr)

        if range_escape is not None:
            escaped = range_escape.signal
            if at - escaped.at > 2 * DISPATCH_INTERVAL:
                range_escape = None
            elif escaped.side * (bar.close - escaped.trigger) <= 0:
                bounds = range_escape.bounds
                range_escape = None
        if bounds is not None:
            for side, level in ((-1, bounds[0]), (1, bounds[1])):
                if held_boundary(prefix, completed, side, level, margin):
                    # The competing range may have been established just
                    # before this close rolled its first test out of view.
                    new_bounds = defended_range(prefix[-9:], atr) or defended_range(
                        prefix[-10:-1], atr
                    )
                    if (
                        new_bounds is not None
                        and new_bounds[1] - new_bounds[0] < bounds[1] - bounds[0]
                        and new_bounds[0] < bounds[1]
                        and new_bounds[1] > bounds[0]
                        and new_bounds[0] <= bar.close <= new_bounds[1]
                    ):
                        # A separately defended, tighter range can straddle
                        # the old boundary. Its own outer edges still govern.
                        bounds = new_bounds
                        break
                    range_break = Signal(side, 'RANGE_BREAK_HOLD', at, level, level)
                    range_escape = RangeEscape(bounds, range_break, margin)
                    bounds = None
                    break
        elif range_escape is None:
            bounds = broader_containment(prefix[-CONTAINMENT_MINUTES:], atr)
            if bounds is None:
                bounds = defended_range(prefix[-9:], atr)

        if (
            trend
            and protected is not None
            and accepted_level(prefix, -trend, protected)
        ):
            broken_side, broken_level, broken_at = trend, protected, at
            trend, protected = 0, None
        if direction and not trend and (not broken_side or direction == -broken_side):
            prior_block = completed[-2]
            edge = prior_block.low if direction == 1 else prior_block.high
            if not accepted_level(prefix, -direction, edge):
                trend, protected = direction, edge
        if trend and protected is not None:
            pivots = swings(completed[-8:], trend, duration=3, left=1)
            for pivot in reversed(pivots):
                if trend * (pivot.price - protected) > 0 and trend * (
                    bar.close - pivot.price
                ) > max(0.7 * atr, 0.3 * atr3):
                    protected = pivot.price
                    break
        if broken_at and at - broken_at > 18 * MINUTE:
            broken_side, broken_level, broken_at = 0, None, None

        if i < 4 or at < bar_end(bars[-1]) - (MAX_TRIGGER_AGE + 2 * MINUTE):
            continue

        def add(signal: Signal):
            signals[signal.identity] = signal

        if range_break:
            add(range_break)
        for side in (1, -1):
            recent_patterns = local_patterns(prefix[-42:], atr, side)
            valid_patterns = [
                p
                for p in recent_patterns
                if at - p.confirmed_at <= 18 * MINUTE
                and all(
                    side * ((b.low if side == 1 else b.high) - p.stop) >= 0
                    for b in prefix
                    if b.start >= p.confirmed_at
                )
            ]
            pattern = max(
                valid_patterns,
                key=lambda p: (p.confirmed_at, p.second.at),
                default=None,
            )
            if pattern is not None:
                patterns[side] = pattern
            else:
                patterns.pop(side, None)

            opposing_pivots = swings(prefix[-32:], -side, left=1)
            near = max(1.0, 0.25 * atr)
            for pivot in opposing_pivots:
                level = pivot.price
                if pivot.known_at > prior.start or side * (bar.close - level) <= 0:
                    continue
                if not any(
                    side * (b.close - level) > 0
                    for b in prefix[-8:-2]
                    if b.start >= pivot.known_at
                ):
                    continue
                edge = bar.low if side == 1 else bar.high
                if abs(edge - level) <= near and side * (prior.close - level) > 0:
                    add(
                        Signal(side, 'DEFENDED_RETEST', at, level, level, True, pattern)
                    )

            if pattern is not None:
                accepted = (
                    broken_side == -side
                    and broken_level is not None
                    and side * (bar.close - broken_level) > 0
                )
                if accepted:
                    protected_break = max(
                        (pattern.neckline, broken_level), key=lambda v: side * v
                    )
                    if at == max(pattern.confirmed_at, broken_at):
                        add(
                            Signal(
                                side,
                                'REVERSAL_BREAK',
                                at,
                                protected_break,
                                protected_break,
                                reversal=pattern,
                            )
                        )
                    # A fresh break of a rebound/rejection pivot can requalify
                    # the same reversal when the first scan lacked aligned OI.
                    for pivot in opposing_pivots:
                        if (
                            pivot.at >= pattern.second.at
                            or pivot.known_at > prior.start
                        ):
                            continue
                        if side * (pivot.price - protected_break) > near and side * (
                            prior.close - pivot.price
                        ) <= 0 < side * (bar.close - pivot.price):
                            add(
                                Signal(
                                    side,
                                    'REVERSAL_BREAK',
                                    at,
                                    pivot.price,
                                    pivot.price,
                                    reversal=pattern,
                                )
                            )

            if direction != side:
                continue
            trigger = (
                max(b.high for b in prefix[-3:-1])
                if side == 1
                else min(b.low for b in prefix[-3:-1])
            )
            if side * (prior.close - trigger) > 0 or side * (bar.close - trigger) <= 0:
                continue
            prior_block = completed[-2]
            anchor = prior_block.low if side == 1 else prior_block.high
            add(
                Signal(
                    side,
                    'OPENING_BREAK' if three_count == 2 else 'CONTINUATION_BREAK',
                    at,
                    trigger,
                    anchor,
                )
            )

    move = acceleration = None
    if len(threes) >= 2 and threes[-1].start - threes[-2].start == DISPATCH_INTERVAL:
        move = threes[-1].close - threes[-2].close
        if (
            len(threes) >= 3
            and threes[-2].start - threes[-3].start == DISPATCH_INTERVAL
        ):
            acceleration = move - (threes[-2].close - threes[-3].close)
    return PriceContext(
        bars,
        threes,
        tens,
        prior_ten,
        atr,
        volatility(threes, minimum=2.5),
        volatility(tens or prior_ten, minimum=2.5),
        direction,
        move,
        acceleration,
        trend,
        protected,
        broken_side,
        broken_level,
        broken_at,
        bounds,
        patterns,
        list(signals.values()),
        range_escape,
    )


def market_targets(
    ctx: PriceContext, window: OIWindow, spot: float, side: int
) -> dict[float, str]:
    levels = {}
    # Intraday levels use only complete ten-minute blocks. The previous
    # session is retained for structural extensions and reversal context.
    for bar in ctx.tens[-12:]:
        value = bar.high if side == 1 else bar.low
        levels[value] = 'COMPLETED_10M'
    for pivot in swings(ctx.prior_ten, -side, duration=10, left=1):
        levels.setdefault(pivot.price, 'PRIOR_10M_SWING')
    for level in oi_levels(window, spot, side, ctx.atr):
        levels.setdefault(level.strike, 'OI_LEVEL')
    return levels


def risk_plan(
    signal: Signal,
    ctx: PriceContext,
    spot: float,
    grid: list[float],
    window: OIWindow,
    cfg: Config,
) -> tuple[RiskPlan | None, str, dict]:
    side = signal.side
    if signal.reversal is not None:
        pattern = signal.reversal
        swing = min((pattern.first, pattern.second), key=lambda p: side * p.price)
        stop, stop_time, stop_source = swing.price, swing.at, 'REVERSAL_SWING'
        if cfg.reversal_strike_stop:
            outer = [strike for strike in grid if 0 < side * (stop - strike) <= ctx.atr]
            if outer:
                stop, stop_source = (
                    nearest_strike(outer, stop),
                    'STRIKE_BEYOND_REVERSAL_SWING',
                )
    elif ctx.threes:
        bar = ctx.threes[-1]
        stop, stop_time, stop_source = (
            bar.close,
            bar_end(bar, 3),
            'LATEST_COMPLETED_3M_CLOSE',
        )
    else:
        return None, 'COMPLETED_3M_STOP_UNAVAILABLE', {}
    risk = side * (spot - stop)
    minimum_risk = max(MIN_STOP_POINTS, MIN_STOP_ATR_FRACTION * ctx.atr)
    evidence = {
        'stop': stop,
        'stop_at': stop_time.isoformat(),
        'stop_source': stop_source,
        'risk_points': round(risk, 4),
        'minimum_stop_clearance': round(minimum_risk, 4),
        'target_anchor': spot,
        'minimum_reward_risk': cfg.min_reward_risk,
    }
    if risk <= 0:
        return None, 'STOP_WRONG_SIDE_OF_LIVE_SPOT', evidence
    if risk + 1e-9 < minimum_risk:
        return None, 'STOP_TOO_CLOSE_TO_LIVE_SPOT', evidence

    levels = market_targets(ctx, window, spot, side)

    def choose(
        bounds: tuple[float, float], ideal: float, fallback: bool = True
    ) -> tuple[float, str] | None:
        low, high = bounds
        included = [
            (value, source)
            for value, source in levels.items()
            if low <= side * (value - spot) <= high
        ]
        if included:
            return min(
                included,
                key=lambda row: (
                    abs(side * (row[0] - spot) - ideal),
                    row[1] != 'COMPLETED_10M',
                    side * row[0],
                ),
            )
        if fallback:
            return round(spot + side * ideal, 4), 'ENTRY_SPOT_DISTANCE'
        return None

    if signal.reversal:
        t1, source1 = choose((35.0, 65.0), 47.5, False) or choose(T1_SPOT_BAND, 47.5)
        t2, source2 = choose(
            (max(65.0, side * (t1 - spot) + 15), 115.0), 85.0, False
        ) or choose(T2_SPOT_BAND, 85.0)
    else:
        t1, source1 = choose(T1_SPOT_BAND, 47.5)
        t2, source2 = choose(T2_SPOT_BAND, 85.0)
    if not (t2 > 0 and side * (t1 - spot) > 0 and side * (t2 - t1) > 0):
        return None, 'INVALID_TARGET_LEVELS', evidence
    reward = side * (t1 - spot) / risk
    evidence.update(t1=t1, t2=t2, reward_risk=round(reward, 4))
    if cfg.min_reward_risk and reward + 1e-10 < cfg.min_reward_risk:
        return None, 'T1_REWARD_TO_RISK_BELOW_MINIMUM', evidence
    policy = 'REVERSAL_SWING' if signal.reversal else 'CONTINUATION_TOUCH'
    return (
        RiskPlan(
            stop, t1, t2, source1, source2, round(risk, 4), round(reward, 4), policy
        ),
        'QUALIFIED',
        evidence,
    )


@dataclass(frozen=True)
class Setup:
    signal: Signal
    plan: RiskPlan
    pair: OIPair
    rule: str
    risk: dict


def evaluate_setups(
    ctx: PriceContext,
    spot: float,
    grid: list[float],
    pairs: dict[float, OIPair],
    window: OIWindow,
    cfg: Config,
    since: datetime,
    slot: datetime,
    consumed: list[str],
) -> tuple[list[dict], list[Setup]]:
    decisions, setups = [], []
    for signal in sorted(
        ctx.signals,
        key=lambda s: (
            s.kind != 'RANGE_BREAK_HOLD',
            not bool(s.reversal),
            not s.defended,
            -s.at.timestamp(),
            abs(spot - s.trigger),
            s.identity,
        ),
    ):
        side = signal.side
        strike = nearest_strike(grid, signal.oi_level)
        pair = pairs.get(strike, OIPair(strike, None, None))
        rule = pair.rule(side, signal.defended)
        detail = {
            'identity': signal.identity,
            'signal': jsonable(asdict(signal)),
            'oi_level': signal.oi_level,
            'mapped_strike': strike,
            'paired_oi_at_level': pair.public(),
            'oi_rule': rule,
        }
        decisions.append(detail)
        extension = side * (spot - signal.trigger)
        cap = min(30.0, max(8.0, cfg.max_chase_atr * ctx.atr))
        detail.update(extension=round(extension, 4), extension_cap=round(cap, 4))
        if signal.identity in consumed or signal.at <= since:
            detail['reason'] = 'TRIGGER_ALREADY_EVALUATED'
        elif signal.at > slot or slot - signal.at > MAX_TRIGGER_AGE:
            detail['reason'] = 'TRIGGER_OUTSIDE_DISPATCH_WINDOW'
        elif ctx.bounds is not None:
            detail['reason'] = 'INTACT_RANGE_AWAITING_OUTER_BREAK_AND_HOLD'
        elif ctx.range_escape is not None and not ctx.range_escape.permits(
            signal, spot, ctx.bars[-1].close
        ):
            detail['reason'] = 'OUTER_RANGE_BREAK_NOT_CONFIRMED_FOR_TRIGGER'
        elif signal.reversal and not any(
            (
                ctx.broken_side == -side
                and ctx.broken_level is not None
                and side * (ctx.bars[-1].close - ctx.broken_level) > 0
                and side * (spot - ctx.broken_level) > 0
                and ctx.trend != -side,
                signal.defended
                and ctx.trend == side
                and any(
                    three_direction(ctx.threes[:i]) == side
                    for i in range(max(2, len(ctx.threes) - 2), len(ctx.threes) + 1)
                ),
            )
        ):
            detail['reason'] = 'OPPOSING_PROTECTED_STRUCTURE_INTACT'
        elif signal.kind == 'RANGE_BREAK_HOLD' and not (
            ctx.range_escape is not None and signal == ctx.range_escape.signal
        ):
            detail['reason'] = 'RANGE_BREAK_NO_LONGER_HELD'
        elif (
            not signal.reversal
            and signal.kind != 'RANGE_BREAK_HOLD'
            and (ctx.direction != side or ctx.trend not in (0, side))
        ):
            detail['reason'] = 'THREE_MINUTE_STRUCTURE_NOT_ALIGNED'
        elif extension <= 0 or side * (ctx.bars[-1].close - signal.trigger) <= 0:
            detail['reason'] = 'PRICE_BACK_BEHIND_TRIGGER'
        elif extension > cap:
            detail['reason'] = 'ENTRY_EXTENDED'
        elif rule is None:
            detail['reason'] = (
                'PAIRED_OI_UNAVAILABLE'
                if pair.changes is None
                else 'PAIRED_OI_NOT_DIRECTIONAL'
            )
        else:
            plan, reason, evidence = risk_plan(signal, ctx, spot, grid, window, cfg)
            detail.update(reason=reason, risk_evidence=evidence)
            if plan is not None:
                setups.append(Setup(signal, plan, pair, rule, evidence))
    return decisions, setups


def directional_contracts(
    band: StrikeBand, setup: Setup, listed: dict
) -> list[tuple[int, OIPair, dict, str]]:
    signal = setup.signal
    side = signal.side
    choices = []
    for offset in (-side, -2 * side):
        pair = band.pairs.get(offset)
        if pair is None:
            continue
        row = listed.get(('CE' if side == 1 else 'PE', pair.strike))
        rule = pair.rule(side, signal.defended)
        if row is not None and rule:
            choices.append((offset, pair, row, rule))
    return choices


def post_exit_entry_check(
    signal: Signal, ctx: PriceContext, spot: float, last_exit: dict, history: list[dict]
) -> dict:
    """Require a new outer break for a same-side entry following a stop."""
    exited = timestamp(last_exit['at'])
    check = {'trigger': signal.identity, 'previous_exit_at': exited.isoformat()}
    if signal.at <= exited:
        return dict(check, reason='REENTRY_REQUIRES_NEW_POST_EXIT_TRIGGER')
    direction = 'BULLISH' if signal.side == 1 else 'BEARISH'
    if exited.date() != ctx.at.date() or last_exit.get('direction') != direction:
        return dict(check, reason='QUALIFIED')
    reason = last_exit.get('reason')
    if reason is None:
        # Existing v136 state stores the reason on the closed position.
        reason = next(
            (
                row.get('exit_reason')
                for row in reversed(history)
                if row.get('id') == last_exit.get('id')
            ),
            None,
        )
    if reason not in ('STRUCTURAL_SL', None):
        return dict(check, reason='QUALIFIED')

    prior = [bar for bar in ctx.bars if bar_end(bar) <= exited][-STOP_REENTRY_LOOKBACK:]
    if len(prior) < 6:
        return dict(check, reason='POST_STOP_STRUCTURE_UNAVAILABLE')
    side = signal.side
    boundary = (
        max(bar.high for bar in prior) if side == 1 else min(bar.low for bar in prior)
    )
    margin = max(1.0, 0.25 * volatility(prior, minimum=2.5))
    post = [bar for bar in ctx.bars if bar.start >= exited]
    threes = [bar for bar in ctx.threes if bar.start >= exited]
    check.update(outer_boundary=boundary, clearance_points=round(margin, 4))
    # A continuation trigger comes from the preceding swing and may sit just
    # inside the boundary. It must still belong to the new break, not the
    # earlier leg. An older range boundary alone cannot authorize re-entry.
    if (
        not held_boundary(post, threes, side, boundary, margin)
        or side * (spot - boundary) <= margin
        or side * (signal.trigger - boundary) < -margin
    ):
        return dict(check, reason='POST_STOP_OUTER_BREAK_AND_HOLD_REQUIRED')
    return dict(check, reason='QUALIFIED')


# Reference position management. Candle observations and live quotes have
# independent timestamps. A newly published adjustment is never retroactive.
def runner_price_support(threes: list[Candle], side: int) -> bool:
    if len(threes) < 2 or threes[-1].start - threes[-2].start != DISPATCH_INTERVAL:
        return False
    older, recent = threes[-2:]
    wiggle = 0.12 * volatility(threes, minimum=2.5)
    if side == 1:
        return (
            recent.high > older.high
            and recent.low >= older.low - wiggle
            and recent.close > older.close
        )
    return (
        recent.low < older.low
        and recent.high <= older.high + wiggle
        and recent.close < older.close
    )


def manage_reference(
    p: dict,
    bars: list[Candle],
    spot: float | None,
    now: datetime,
    deadline: datetime,
    cfg: Config,
    *,
    spot_at: datetime | None = None,
    session_open: datetime | None = None,
) -> tuple[dict | None, list[tuple[str, dict]], dict | None, list[str]]:
    position = copy.deepcopy(p)
    side = 1 if p['direction'] == 'BULLISH' else -1
    opening = timestamp(p['opened_at'])
    session_open = session_open or day_time(opening, 9, 15)
    cursor = timestamp(p['last_candle'])
    entry_minute = exact_minute(opening)
    expected = max(cursor + MINUTE, entry_minute)
    events: list[tuple[str, dict]] = []
    warnings: list[str] = []
    runner = position.get('runner')

    def emit(kind: str, at: datetime, **facts):
        events.append((kind, position_event_payload(position, at, **facts)))

    def finish(
        kind: str,
        at: datetime,
        reason: str,
        level: float | None,
        source: str,
        observation: dict,
    ):
        position['remaining_pct'] = 0
        emit(
            kind,
            at,
            reason=reason,
            underlying_reference=level,
            source=source,
            email_observation=observation,
        )
        return (
            None,
            events,
            close_reference(position, at, reason, level, source),
            warnings,
        )

    for bar in bars:
        if bar.start < expected:
            continue
        if bar.start > expected:
            warnings.append('GAP_IN_UNOBSERVED_POSITION_BARS')
            break
        at = bar_end(bar)
        if at > min(now, deadline):
            break

        stop, t2 = position['stop'], position['t2']
        adjusted = position.get('adjusted_at')
        # A run can update levels inside an open minute. OHLC of that minute
        # can certify a new-level touch only with its post-update close.
        recent_adjustment = bool(adjusted and bar.start < timestamp(adjusted) <= at)
        adverse = bar.low if side == 1 else bar.high
        favorable = bar.high if side == 1 else bar.low
        known_after_entry = bar.start >= opening
        observation = {'spot': bar.close, 'spot_is_close': True, 'stop': stop, 't2': t2}
        extreme = {
            **observation,
            'target_touch_spot': favorable,
            'target_touch_extreme': 'high' if side == 1 else 'low',
        }

        if not known_after_entry:
            if side * (adverse - stop) <= 0 or side * (favorable - position['t1']) >= 0:
                warnings.append('ENTRY_MINUTE_TOUCH_SEQUENCE_UNKNOWN')
            adverse = favorable = bar.close

        if recent_adjustment:
            old_stop = position.get('stop_before_adjustment', stop)
            if side * (adverse - old_stop) <= 0:
                # A tightened stop protects at least as well as its old
                # level, so the breach is certain. Fill timing remains unknown.
                warnings.append('STOP_ADJUSTMENT_MINUTE_LEVEL_UNCERTAIN')
                return finish(
                    'EXIT',
                    at,
                    'STRUCTURAL_SL',
                    stop,
                    'COMPLETED_1M_STOP_OLD_LEVEL_BREACHED',
                    observation,
                )
            if side * (adverse - stop) <= 0 and side * (bar.close - stop) > 0:
                warnings.append('STOP_ADJUSTMENT_MINUTE_TOUCH_SEQUENCE_UNKNOWN')
            adverse = bar.close
            old_t2 = position.get('t2_before_adjustment', t2)
            if position.get('t2_source') == 'RUNNER_STRUCTURE' and old_t2 != t2:
                if side * (favorable - old_t2) >= 0:
                    warnings.append(
                        'PRIOR_TARGET_TOUCH_ORDER_UNKNOWN_IN_ADJUSTMENT_MINUTE'
                    )
                if side * (bar.close - t2) < 0:
                    if side * (favorable - t2) >= 0:
                        warnings.append(
                            'TARGET_ADJUSTMENT_MINUTE_TOUCH_SEQUENCE_UNKNOWN'
                        )
                favorable = bar.close

        if not known_after_entry or recent_adjustment:
            extreme.update(target_touch_spot=favorable, target_touch_extreme='close')

        reached_t1 = (
            not position.get('t1_hit', False)
            and side * (favorable - position['t1']) >= 0
        )
        t2_active = not (
            runner
            and runner.get('reached_at')
            and position['t2_source'] != 'RUNNER_STRUCTURE'
        )
        reached_t2 = t2_active and side * (favorable - t2) >= 0
        if side * (adverse - stop) <= 0:
            if reached_t1 or reached_t2:
                warnings.append('SAME_MINUTE_STOP_TARGET_SEQUENCE_UNKNOWN_STOP_FIRST')
            return finish(
                'EXIT',
                at,
                'STRUCTURAL_SL',
                stop,
                'COMPLETED_1M_STOP_TOUCH',
                observation,
            )

        if reached_t1:
            new_stop = max(
                (stop, position['entry_spot']), key=lambda level: side * level
            )
            position.update(
                t1_hit=True,
                t1_at=at.isoformat(),
                remaining_pct=100 - position.get('t1_exit_pct', 50),
                stop=new_stop,
                adjusted_at=at.isoformat(),
                stop_before_adjustment=stop,
                t2_before_adjustment=t2,
            )
            observation['stop'] = extreme['stop'] = new_stop
            emit(
                'T1',
                at,
                old_stop=stop,
                new_stop=new_stop,
                underlying_reference=position['t1'],
                source='COMPLETED_1M_TARGET_TOUCH',
                email_observation=extreme,
            )

        if position.get('t1_hit') and reached_t2:
            if (
                runner
                and not runner.get('reached_at')
                and runner_price_support(
                    aggregate([b for b in bars if bar_end(b) <= at], 3, session_open),
                    side,
                )
            ):
                runner['reached_at'] = at.isoformat()
                runner['checkpoint_touch'] = favorable
            else:
                return finish(
                    'T2',
                    at,
                    'SPOT_TARGET_REACHED',
                    t2,
                    'COMPLETED_1M_TARGET_TOUCH',
                    extreme,
                )
        if reached_t1 and side * (bar.close - position['stop']) <= 0:
            return finish(
                'EXIT',
                at,
                'STRUCTURAL_SL',
                position['stop'],
                'COMPLETED_1M_CLOSE_AFTER_T1',
                observation,
            )

        position['last_candle'] = bar.start.isoformat()
        expected += MINUTE

    observed_at = spot_at or now
    if spot is not None and opening <= observed_at <= now:
        adjustment = position.get('adjusted_at')
        if (adjustment is None or observed_at >= timestamp(adjustment)) and side * (
            spot - position['stop']
        ) <= 0:
            return finish(
                'EXIT',
                observed_at,
                'STRUCTURAL_SL',
                position['stop'],
                'FRESH_INDEX_QUOTE',
                {'spot': spot},
            )
    if now >= deadline:
        return finish(
            'EXIT',
            deadline,
            'SESSION_REFERENCE_EXIT',
            spot,
            'SESSION_CUTOFF',
            {'spot': spot},
        )
    return position, events, None, warnings


def refine_reference(
    position: dict,
    ctx: PriceContext,
    spot: float,
    band: StrikeBand | None,
    observed_at: datetime,
) -> tuple[str, dict] | None:
    if (
        not position.get('t1_hit')
        or position.get('last_candle') != ctx.bars[-1].start.isoformat()
    ):
        return None
    side = 1 if position['direction'] == 'BULLISH' else -1
    old_stop, old_t2 = position['stop'], position['t2']
    opening = timestamp(position['opened_at'])
    runner = position.get('runner')
    if ctx.threes and runner_price_support(ctx.threes, side):
        bar = ctx.threes[-1]
        # A block containing pre-entry bars cannot set the trailing stop.
        if bar.start >= opening:
            edge = bar.low if side == 1 else bar.high
            next_stop = round(edge - side * stop_buffer(ctx.atr, ctx.atr3), 4)
            if side * (next_stop - old_stop) > 0 and side * (spot - next_stop) >= max(
                1.0, 0.15 * ctx.atr
            ):
                position['stop'] = next_stop

        prior_target_is_ahead = (
            position['t2_source'] != 'RUNNER_STRUCTURE' or side * (old_t2 - spot) > 0
        )
        if (
            runner
            and runner.get('reached_at')
            and prior_target_is_ahead
            and band is not None
            and any(pair.rule(side) for pair in band.pairs.values())
        ):
            # Existing, untouched price structure remains binding. A scan may
            # extend an active objective only while it is still ahead of spot.
            clearance = max(40.0, 1.4 * ctx.atr3)
            completed_close = ctx.threes[-1].close
            levels = {
                value
                for b in ctx.tens + ctx.prior_ten
                for value in ((b.high if side == 1 else b.low), b.close)
                if side * (value - completed_close) >= clearance
                and side * (value - spot) >= max(5.0, 0.3 * ctx.atr)
                and side * (value - old_t2) >= max(1.0, 0.25 * ctx.atr)
            }
            if levels:
                objective = min(levels, key=lambda value: side * (value - spot))
                position.update(t2=objective, t2_source='RUNNER_STRUCTURE')

    if position['stop'] == old_stop and position['t2'] == old_t2:
        return None
    position.update(
        adjusted_at=observed_at.isoformat(),
        stop_before_adjustment=old_stop,
        t2_before_adjustment=old_t2,
    )
    reason = (
        'RUNNER_TARGET_EXTENDED'
        if position['t2'] != old_t2
        else 'CONTINUATION_STOP_TRAILED'
    )
    return 'ADJUST_SL', position_event_payload(
        position,
        observed_at,
        reason=reason,
        old_stop=old_stop,
        new_stop=position['stop'],
        old_t2=old_t2,
        new_t2=position['t2'],
        email_observation={'spot': spot},
    )


def scan(
    state: dict, api, cfg: Config, clock_fn=None, clock_sink: list | None = None
) -> tuple[dict, list[str]]:
    times: list[str] = []

    def clock() -> datetime:
        t = (clock_fn or (lambda: datetime.now(IST)))()
        if t.tzinfo is None:
            raise DataError('Scan clock requires a timezone')
        time_now = t.astimezone(IST)
        if times and time_now < timestamp(times[-1]):
            raise DataError('Scan clock moved backward')
        times.append(time_now.isoformat())
        if clock_sink is not None:
            clock_sink.append(times[-1])
        return time_now

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

    def no_trade(reason: str):
        if result['decision'] in ('POSITION_OPEN', 'POSITION_CLOSED'):
            result['entry_check'] = reason
        else:
            result['reason'] = reason
        return result, times

    def save_position(position, events, closed, warnings, at):
        result['management_warnings'] = warnings
        for kind, detail in events:
            result['alerts_created'].append(new_event(state, kind, detail, at))
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
        result['reason'] = (
            closed['exit_reason'] if closed else 'REFERENCE_POSITION_MANAGED'
        )

    deadline = day_time(now, *HARD_EXIT)
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
                source=closed['exit_source'],
            ),
        )
        save_position(None, [event], closed, [], at=now)
        return result, times
    if not active and now >= deadline:
        return no_trade('AFTER_SESSION_EXIT_CUTOFF')
    try:
        session = api.session(now)
    except (DataError, ProviderError) as exc:
        session = None
        result['session_failure'] = str(exc)
    if not session:
        if active and now >= deadline:
            save_position(
                *manage_reference(active, [], None, now, deadline, cfg), at=now
            )
            return result, times
        if active:
            result['decision'] = 'POSITION_MONITORING_UNAVAILABLE'
        return no_trade('NO_VERIFIED_NFO_SESSION')
    session_open, session_close = session
    deadline = min(deadline, session_close)
    price = ClosedPrice([])
    if engine.get('closed_candles'):
        try:
            price = merge_closed_price(
                price, engine['closed_candles'], now, session, cfg
            )
        except DataError as exc:
            result['candle_cache_error'] = str(exc)

    def price_slot(at: datetime) -> datetime:
        return exact_minute(at - timedelta(seconds=cfg.feed_grace_seconds))

    def refresh_price(error_field: str):
        nonlocal now, price
        try:
            raw = api.candles()
        except (DataError, ProviderError) as exc:
            now = clock()
            result[error_field] = str(exc)
            return
        now = clock()
        try:
            price = merge_closed_price(price, raw, now, session, cfg)
        except DataError as exc:
            result[error_field] = str(exc)

    refresh_price('candle_error')
    result['candle_coverage'] = price.audit(price_slot(now))
    engine['closed_candles'] = [serialize_bar(bar) for bar in price.bars]

    early_baseline = session_open
    if not active and now < early_baseline:
        return no_trade('BEFORE_FIRST_OI_BASELINE')
    window = None
    contracts: list[dict] = []
    # Index candles and OI have independent publication and receipt times.
    # Stamp each snapshot at receipt, even if a candle or a network call crossed a minute.
    slot = price_slot(now)
    if now < deadline and slot >= early_baseline:
        try:
            expiry, contracts = api.contracts(now.date())
            chain = api.chain(expiry, contracts)
            now = clock()
            slot = price_slot(now)
            if now >= deadline:
                result['oi'] = {'status': 'CAPTURE_AFTER_SESSION_EXIT_CUTOFF'}
            else:
                sample = make_oi_snapshot(chain, expiry, now, slot)
                ring = engine['oi_samples']
                window = match_oi(ring, sample, cfg)
                ring = [s for s in ring if now - timestamp(s['at']) < 15 * MINUTE]
                if not any(
                    s['through'] == slot.isoformat() and s['expiry'] == expiry
                    for s in ring
                ):
                    ring.append(jsonable(asdict(sample)))
                engine['oi_samples'] = ring[-8:]
                result['oi'] = {
                    'status': 'MATCHED' if window else 'OI_WINDOW_UNAVAILABLE',
                    'at': now.isoformat(),
                    'through': slot.isoformat(),
                    'candle_through_at_capture': price.through.isoformat()
                    if price.through
                    else None,
                    'expiry': expiry,
                    'baseline': window.baseline.isoformat() if window else None,
                    'matched_contracts': len(window.changes) if window else 0,
                }
        except (DataError, ProviderError, ValueError, KeyError, TypeError) as exc:
            now = clock()
            result['oi'] = {'status': 'OPTION_CHAIN_UNAVAILABLE', 'reason': str(exc)}

    if window is None:
        slot = price_slot(now)
    repolled = False
    slot_ends = slot + MINUTE + timedelta(seconds=cfg.feed_grace_seconds)
    if (
        price.through != slot
        and price_slot(now) == slot
        and now + CANDLE_REFRESH_REQUEST_BUDGET < min(slot_ends, deadline)
    ):
        # The chain request already gave the feed time to publish. Use one
        # opportunistic refresh, then work from the available closed evidence.
        refresh_price('candle_repoll_error')
        repolled = True
        engine['closed_candles'] = [serialize_bar(bar) for bar in price.bars]
    bars = price.bars
    through = price.through
    entry_slot = slot if window is not None else price_slot(now)
    result['candle_coverage'] = price.audit(entry_slot)
    if repolled:
        result['candle_coverage']['recovered_on_repoll'] = through == entry_slot

    spot = None
    quote_time = None
    try:
        quotes = api.quotes([INDEX])
        now = clock()
        quote = quotes.get(INDEX)
        spot = checked_quote(quote, now, cfg.quote_max_age_seconds)
        quote_time = timestamp(quote['timestamp'])
    except (DataError, ProviderError, KeyError) as exc:
        now = clock()
        result['quote_error'] = str(exc)

    prior_ten = prior_context(engine, api, now) if bars else []
    now = clock()
    if (
        window is not None
        and (now - window.snapshot.at).total_seconds() > cfg.quote_max_age_seconds
    ):
        result['oi']['status'] = 'STALE_AT_DECISION'
        window = None
    ctx = analyze_price(bars, prior_ten, session_open) if bars else None
    grid = listed_strikes(contracts)
    pairs = paired_oi(window)
    band = StrikeBand.build(grid, spot, pairs) if spot is not None else None
    if ctx:
        result['market_assessment'] = {
            **ctx.public(band),
            'spot': spot,
            'index_quote_at': quote_time.isoformat() if quote_time else None,
            'strike_band': band.public() if band else None,
        }
        watches = result['market_assessment']['reversal_watches'] = []
        for side in (1, -1):
            pattern = ctx.patterns.get(side)
            recent = ctx.bars[-4:]
            if pattern is not None and ctx.trend == -side:
                levels = [
                    level for level in grid if side * (level - pattern.neckline) > 0
                ]
                first = nearest_strike(levels, pattern.neckline) if levels else None
                watches.append(
                    {
                        'side': side,
                        'pattern': jsonable(asdict(pattern)),
                        'protected': ctx.protected,
                        'first_listed_level': first,
                        'first_listed_level_already_passed': (
                            first is not None
                            and spot is not None
                            and side * (spot - first) >= 0
                        ),
                        'reason': 'OPPOSING_PROTECTED_STRUCTURE_INTACT',
                    }
                )
            elif ctx.trend == -side and len(recent) >= 2:
                edge = (
                    min(b.low for b in recent)
                    if side == 1
                    else max(b.high for b in recent)
                )
                if side * (recent[-1].close - edge) >= max(8.0, 0.75 * ctx.atr) and (
                    side * (recent[-1].close - recent[-2].close) > 0
                ):
                    watches.append(
                        {
                            'side': side,
                            'extreme': edge,
                            'protected': ctx.protected,
                            'reason': 'OBSERVE_BOUNCE_OR_REJECTION',
                        }
                    )

    if active is not None:
        managed, events, closed, warnings = manage_reference(
            active,
            bars,
            spot,
            now,
            deadline,
            cfg,
            spot_at=quote_time,
            session_open=session_open,
        )
        has_fresh_spot = (
            spot is not None
            and quote_time is not None
            and (now - quote_time).total_seconds() <= cfg.quote_max_age_seconds
        )
        if (
            managed
            and ctx
            and has_fresh_spot
            and now < deadline
            and price.covers_entry(price_slot(now))
        ):
            adjustment = refine_reference(managed, ctx, spot, band, now)
            if adjustment:
                t1_event = next(
                    (detail for kind, detail in events if kind == 'T1'), None
                )
                if t1_event:
                    t1_event['adjustment_at'] = now.isoformat()
                    t1_event['new_stop'] = managed['stop']
                    t1_event['position'].update(
                        stop=managed['stop'],
                        t2=managed['t2'],
                        t2_source=managed['t2_source'],
                    )
                    t1_event['email_observation'].update(
                        stop=managed['stop'], t2=managed['t2']
                    )
                else:
                    events.append(adjustment)
        save_position(managed, events, closed, warnings, at=now)
        if managed and spot is None and not bars:
            result.update(
                decision='POSITION_MONITORING_UNAVAILABLE',
                reason='PRICE_FEED_UNAVAILABLE',
            )

    if ctx is None:
        return no_trade('NO_COMPLETED_SESSION_CANDLES')
    if now < max(day_time(now, *ENTRY_START), session_open + 6 * MINUTE):
        return no_trade('COLLECTING_OPENING_BASELINE')
    if not price.covers_entry(entry_slot):
        return no_trade('CLOSED_PRICE_TOO_OLD_FOR_ENTRY')
    if price.tail_size < 6:
        return no_trade('INSUFFICIENT_CONTIGUOUS_PRICE_HISTORY')

    earliest = entry_slot - MAX_TRIGGER_AGE - timedelta(seconds=1)
    previous = engine.get('evaluated_through')
    since = max(earliest, timestamp(previous)) if previous else earliest
    engine['evaluated_through'] = max(through, since).isoformat()
    if (
        window is None
        or (now - window.snapshot.at).total_seconds() > cfg.quote_max_age_seconds
    ):
        return no_trade('OI_WINDOW_UNAVAILABLE_OR_STALE')
    if price_slot(now) != entry_slot:
        return no_trade('PRICE_WINDOW_ROLLED_DURING_SNAPSHOT')
    if (
        quote_time is None
        or quote_time < entry_slot
        or (now - quote_time).total_seconds() > cfg.quote_max_age_seconds
    ):
        return no_trade('INDEX_QUOTE_UNAVAILABLE_FOR_ENTRY')
    if band is None:
        return no_trade('ATM_STRIKE_BAND_UNAVAILABLE')

    result['entry_evidence'] = {
        'index_quote_at': quote_time.isoformat(),
        'index_quote': spot,
        'decision_through': entry_slot.isoformat(),
        'candle_through': through.isoformat(),
        'latest_candle_close': ctx.bars[-1].close,
        'initial_atm': band.atm,
    }
    consumed = engine['consumed_signals']
    decisions, setups = evaluate_setups(
        ctx, spot, grid, pairs, window, cfg, since, entry_slot, consumed
    )
    result['evaluations'] = decisions
    if ctx.bounds is not None:
        return no_trade('INTACT_RANGE_AWAITING_OUTER_BREAK_AND_HOLD')
    if state.get('position') is not None:
        return no_trade('EXISTING_POSITION_REMAINS_VALID')
    last_entry = min(day_time(now, *ENTRY_END), deadline - 10 * MINUTE)
    if now >= last_entry:
        return no_trade('OUTSIDE_ENTRY_WINDOW')
    if not setups:
        return no_trade(
            'NO_QUALIFIED_PRICE_OI_AND_RISK_SETUP'
            if decisions
            else 'NO_FRESH_PRICE_TRIGGER'
        )
    last_exit = state.get('last_exit')
    if last_exit:
        checks = [
            post_exit_entry_check(setup.signal, ctx, spot, last_exit, state['history'])
            for setup in setups
        ]
        result['reentry_checks'] = checks
        setups = [
            setup
            for setup, check in zip(setups, checks)
            if check['reason'] == 'QUALIFIED'
        ]
        if not setups:
            return no_trade(checks[0]['reason'])
    if len({setup.signal.side for setup in setups}) != 1:
        return no_trade('CONFLICTING_QUALIFIED_DIRECTIONS')

    listed = {
        (row['instrument_type'], float(row['strike_price'])): row
        for row in contracts
        if row['expiry'] == window.snapshot.expiry
    }
    center = grid.index(band.atm)
    adjacent = grid[max(0, center - 1) : center + 2]
    request_keys = []
    for value in adjacent:
        candidate_band = StrikeBand.build(grid, value, pairs)
        for setup in setups:
            request_keys.extend(
                row['instrument_key']
                for _, _, row, _ in directional_contracts(candidate_band, setup, listed)
            )
    if not request_keys:
        return no_trade('NO_DIRECTIONAL_OI_AT_ELIGIBLE_OFFSETS')
    try:
        option_quotes = api.quotes([INDEX, *dict.fromkeys(request_keys)])
        now = clock()
        index_quote = option_quotes.get(INDEX)
        final_spot = checked_quote(index_quote, now, cfg.quote_max_age_seconds)
        final_at = timestamp(index_quote['timestamp'])
    except (DataError, ProviderError, KeyError) as exc:
        result['option_quote_error'] = str(exc)
        return no_trade('ENTRY_QUOTE_REQUEST_FAILED')
    if (
        now >= last_entry
        or price_slot(now) != entry_slot
        or final_at < max(entry_slot, quote_time)
        or (now - window.snapshot.at).total_seconds() > cfg.quote_max_age_seconds
    ):
        return no_trade('DECISION_WINDOW_EXPIRED_DURING_QUOTE_FETCH')

    final_band = StrikeBand.build(grid, final_spot, pairs)
    if final_band is None or final_band.atm not in adjacent:
        return no_trade('ATM_CHANGED_BEYOND_REQUESTED_STRIKE_BANDS')
    result['entry_evidence'].update(
        index_quote_at=final_at.isoformat(),
        index_quote=final_spot,
        final_atm=final_band.atm,
    )
    final_checks, final_setups = evaluate_setups(
        ctx, final_spot, grid, pairs, window, cfg, since, entry_slot, consumed
    )
    wanted = {setup.signal.identity for setup in setups}
    result['final_evaluations'] = [
        check for check in final_checks if check['identity'] in wanted
    ]
    final_setups = [setup for setup in final_setups if setup.signal.identity in wanted]
    if not final_setups:
        return no_trade('FINAL_LIVE_PRICE_INVALIDATES_SETUP')
    if last_exit:
        checks = [
            post_exit_entry_check(
                setup.signal, ctx, final_spot, last_exit, state['history']
            )
            for setup in final_setups
        ]
        result['final_reentry_checks'] = checks
        final_setups = [
            setup
            for setup, check in zip(final_setups, checks)
            if check['reason'] == 'QUALIFIED'
        ]
        if not final_setups:
            return no_trade(checks[0]['reason'])

    result['contract_checks'] = []
    for setup in final_setups:
        signal, plan = setup.signal, setup.plan
        ranked = []
        for offset, pair, row, rule in directional_contracts(final_band, setup, listed):
            key = row['instrument_key']
            check = {
                'strike': pair.strike,
                'oi_rule': rule,
                'oi_pair': pair.public(),
                'trigger': signal.identity,
            }
            result['contract_checks'].append(check)
            try:
                contract = live_contract(
                    row, option_quotes.get(key), now, final_at, final_band, offset, cfg
                )
            except (DataError, KeyError, ValueError, TypeError) as exc:
                check['reason'] = str(exc)
                continue
            check['reason'] = 'QUALIFIED_QUOTE'
            contract['oi_rule'] = rule
            ranked.append(
                (
                    -pair.score(signal.side),
                    contract['spread_pct'],
                    -contract['depth_lots'],
                    abs(offset),
                    key,
                    contract,
                )
            )
        if not ranked:
            continue
        *_, key, contract = min(ranked, key=lambda row: row[:-1])
        direction = 'BULLISH' if signal.side == 1 else 'BEARISH'
        position_id = hashlib.sha256(
            f'{now.date()}|{signal.identity}|{key}'.encode()
        ).hexdigest()[:22]
        position = {
            'id': position_id,
            'status': 'OPEN',
            'direction': direction,
            'side': contract['side'],
            'strike': contract['strike'],
            'expiry': contract['expiry'],
            'instrument_key': key,
            'opened_at': now.isoformat(),
            'entry_spot': final_spot,
            'entry_ask': contract['ask'],
            'initial_stop': plan.stop,
            'setup_level': signal.trigger,
            'setup_invalidation': plan.stop,
            'last_candle': bars[-1].start.isoformat(),
            'scenario': signal.kind,
            't1_hit': False,
            'remaining_pct': 100,
            'contract': contract,
            **asdict(plan),
        }
        if (
            cfg.arm_continuation_runner
            and not signal.reversal
            and signal.kind != 'RANGE_BREAK_HOLD'
            and ctx.move is not None
            and signal.side * ctx.move >= STRONG_MOVE
            and setup.rule == 'STANDARD_2_PERCENT'
            and runner_price_support(ctx.threes, signal.side)
        ):
            position['runner'] = {'checkpoint': plan.t2, 'armed_at': now.isoformat()}

        state['position'] = position
        engine['last_entry_through'] = through.isoformat()
        engine['consumed_signals'] = (consumed + [signal.identity])[-160:]
        evidence = result['entry_evidence']
        evidence.update(
            signal_candle_closed_at=signal.at.isoformat(),
            option_quote_at=contract['quote_time'],
        )
        event = position_event_payload(
            position,
            now,
            reason='QUALIFIED_PRICE_AND_3M_OI',
            signal=jsonable(asdict(signal)),
            plan=asdict(plan),
            entry_evidence=evidence,
            risk_evidence=setup.risk,
            oi={
                'window': result['oi'],
                'confirmation_pair': setup.pair.public(),
                'rule': setup.rule,
            },
        )
        result['alerts_created'].append(new_event(state, 'ENTRY', event, now))
        result.update(
            decision='ENTRY',
            reason='QUALIFIED_' + contract['side'],
            position_locked=True,
            selected_position=position,
            final_risk_evidence=setup.risk,
        )
        return result, times
    reason = (
        'DIRECTIONAL_OPTION_QUOTES_UNAVAILABLE'
        if result['contract_checks']
        else 'NO_DIRECTIONAL_OI_AT_FINAL_ATM'
    )
    return no_trade(reason)


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


def paths() -> tuple[Path, Path]:
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
    ):
        raw.pop(legacy, None)
    # v133 stored these values as defaults in some deployed configurations.
    # Explicit non-default overrides still apply.
    if raw.get('max_chase_atr') == 1.25:
        raw.pop('max_chase_atr')
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
    claim_outbox(state, token, now)
    event = {
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
            state = load_state(state_path)
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
