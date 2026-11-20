#!/usr/bin/env python3
"""NIFTY scanner v132.0.0. Reference alerts using completed price and OI windows.

Production runs require Upstox market data and the existing dispatcher. Keep the
existing state path and deploy this Python file and its workflow together. The
durable outbox retains position and delivery identity across workflow reruns.

The supplied OHLC workbooks support historical price validation. They contain
no option OI snapshots or quotes. Exact historical strike decisions need
timestamped option captures. Directional OI confirmation uses signed Call and Put changes at the same strike.

Price analysis uses available closed one-minute candles. A one-minute
publication lag can qualify for entry only with a recent trigger, a matched
three-minute OI observation and a quote from the decision minute. Position
monitoring uses completed candles and fresh index quotes independently.
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

VERSION = '132.0.0'
AUDIT_RELEASE = 'v132'
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
        if isinstance(value, (int, float)) or (isinstance(value, str) and value.isdigit()):
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
        if not all(math.isfinite(x) for x in values) or min(values[:4]) <= 0 or self.volume < 0:
            raise DataError('Invalid OHLCV')
        if self.low > min(self.open, self.close) or self.high < max(self.open, self.close) or self.high < self.low:
            raise DataError('Impossible OHLC')




def day_time(now: datetime, hour: int, minute: int) -> datetime:
    return now.astimezone(IST).replace(hour=hour, minute=minute, second=0, microsecond=0)


def exact_minute(now: datetime) -> datetime:
    return now.astimezone(IST).replace(second=0, microsecond=0)


def serialize_bar(c: Candle) -> list[Any]:
    return [c.start.isoformat(),c.open,c.high,c.low,c.close,c.volume]


def parse_candles(raw: list, now: datetime) -> list[Candle]:
    """Drop uncompleted bars; refuse inconsistent duplicates, duplicates do not shadow data."""
    if not isinstance(raw,list):
        raise DataError('Candle payload must be list')
    unique: dict[datetime,Candle] = {}
    for row in raw:
        try:
            if not isinstance(row,(list,tuple)) or len(row) < 5:
                raise DataError('Malformed candle row')
            start = timestamp(row[0])
            if start.second or start.microsecond:
                raise DataError('Unaligned candle')
            if start + timedelta(minutes=1) > now - timedelta(seconds=1):
                continue
            c = Candle(start,*(read_number(row[i],f'candle_{i}',positive=True) for i in range(1,5)),
                       read_number(row[5], 'volume',nonnegative=True) if len(row)>5 else 0.0)
        except (DataError,TypeError) as exc:
            raise DataError('Invalid OHLC row') from exc
        if c.start in unique and c != unique[c.start]:
            raise DataError('Conflicting duplicate candles')
        unique[c.start] = c
    ordered = sorted(unique.values(), key=lambda c:c.start)
    if not ordered:
        raise DataError('No completed candles')
    return ordered


def contiguous_tail(bars: list[Candle]) -> list[Candle]:
    if not bars:
        return []
    start = len(bars)-1
    while start and bars[start].start-bars[start-1].start == timedelta(minutes=1):
        start -= 1
    return bars[start:]


def volatility(bars: list[Candle], n=14, minimum=3.0) -> float:
    window=bars[-(n+1):]
    if not window:
        return minimum
    if len(window) == 1:
        return max(minimum, window[0].high - window[0].low)
    tr = [max(b.high-b.low, abs(b.high-a.close), abs(b.low-a.close)) for a,b in zip(window,window[1:])]
    return max(minimum, sum(tr)/len(tr))




@dataclass(frozen=True)
class Config:
    oi_jitter_seconds: int = 35
    feed_grace_seconds: float = 2.0
    quote_max_age_seconds: int = 35
    quote_max_skew_seconds: int = 12
    min_stop_atr: float = 0.7
    max_stop_atr: float = 4.5
    max_chase_atr: float = 1.25
    max_unretested_leg_atr: float = 4.0
    min_reward_risk: float = 1.25
    max_spread_percent: float = 2.0
    min_depth_lots: float = 1.0
    cooldown_minutes: int = 4
    max_state_history: int = 240
    record_inputs: bool = True

    def __post_init__(self):
        for key, value in asdict(self).items():
            if key == 'record_inputs':
                if type(value) is not bool:
                    raise DataError('record_inputs must be a boolean')
            elif type(value) not in (int, float) or not math.isfinite(value) or value <= 0:
                raise DataError('Invalid configuration: ' + key)
        for name in ('oi_jitter_seconds',
                     'quote_max_age_seconds', 'quote_max_skew_seconds',
                     'cooldown_minutes', 'max_state_history'):
            if type(getattr(self, name)) is not int:
                raise DataError(name + ' must be an integer')
        if not (self.oi_jitter_seconds < 60 and self.feed_grace_seconds < 15
                and self.min_stop_atr < self.max_stop_atr and self.min_reward_risk >= 1
                and self.quote_max_skew_seconds <= self.quote_max_age_seconds):
            raise DataError('Inconsistent configuration')


MINUTE = timedelta(minutes=1)
OI_MINUTES = 3
MAX_ENTRY_CANDLE_LAG = MINUTE
DISPATCH_INTERVAL = 3 * MINUTE
MAX_TRIGGER_AGE = DISPATCH_INTERVAL + MAX_ENTRY_CANDLE_LAG
LEVEL_STRIKE_TOLERANCE = 20.0
NIFTY_STRIKE_INTERVAL = 50.0
CANDLE_REFRESH_REQUEST_BUDGET = timedelta(seconds=16)
# Separate from strike eligibility. Used when judging changes in the OI map.
OI_LEVEL_MATERIAL_CHANGE = .02
CONTINUATION_SCENARIOS = frozenset({'FAILED_PULLBACK', 'PULLBACK_CONTINUATION', 'TREND_RESUMPTION',
                                    'ACCEPTED_BREAKOUT', 'ACCEPTED_BREAKDOWN', 'OPENING_MOMENTUM'})


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
            'from': self.bars[0].start.isoformat() if self.bars else None,
            'through': through.isoformat() if through else None,
            'expected_through': slot.isoformat(),
            'lag_minutes': (slot - through) // MINUTE if through else None,
            'contiguous_tail': self.tail_size,
            'latest': through == slot,
        }


def merge_closed_price(saved: ClosedPrice, raw: list, received_at: datetime,
                       session: tuple[datetime, datetime], cfg: Config) -> ClosedPrice:
    session_open, session_close = session
    observed = parse_candles(raw, received_at - timedelta(seconds=cfg.feed_grace_seconds - 1))
    observed = [bar for bar in observed if session_open <= bar.start and bar_end(bar) <= session_close]
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
        Candle(start, group[0].open, max(bar.high for bar in group),
               min(bar.low for bar in group), group[-1].close, sum(bar.volume for bar in group))
        for start, group in sorted(groups.items())
        if len(group) == duration and all(bar.start == start + i * MINUTE for i, bar in enumerate(group))
    ]


@dataclass(frozen=True)
class Swing:
    price: float
    at: datetime
    known_at: datetime


def swings(bars: list[Candle], side: int, duration: int = 1,
           left: int = 2, right: int = 1) -> list[Swing]:
    result = []
    for index in range(left, len(bars) - right):
        bar = bars[index]
        group = bars[index-left:index+right+1]
        if any(b.start != group[0].start + k * duration * MINUTE for k, b in enumerate(group)):
            continue
        values = [side * (b.low if side == 1 else b.high) for b in group]
        # Resolve flat extrema once, at the first occurrence.
        if values.index(min(values)) == left and values[left] < min(values[left+1:]):
            result.append(Swing(side * values[left], bar.start, bar_end(group[-1], duration)))
    return result


@dataclass(frozen=True)
class Zone:
    price: float
    source: str
    strength: int
    known_at: datetime


@dataclass(frozen=True)
class ReversalEvidence:
    first_test: datetime
    second_test: datetime
    first_extreme: float
    second_extreme: float
    confirmed_at: datetime
    pattern: str
    intervening_extreme: float | None = None


@dataclass(frozen=True)
class Signal:
    side: int
    scenario: str
    at: datetime
    origin: datetime
    trigger: float
    invalidation: float
    level: float
    reversal: ReversalEvidence | None = None

    @property
    def identity(self) -> str:
        return f'{self.side}:{self.scenario}:{self.origin.isoformat()}'


@dataclass(frozen=True)
class TrendTransition:
    side: int
    level: float
    detected_at: datetime


@dataclass(frozen=True)
class MarketPhase:
    kind: str = 'MIXED'
    reason: str = 'NO_ACCEPTED_STRUCTURE'
    boundary: float | None = None
    transition: TrendTransition | None = None


@dataclass(frozen=True)
class PriceContext:
    at: datetime
    atr: float
    atr3: float
    atr10: float
    trend: int
    protected: float | None
    range_bounds: tuple[float, float] | None
    supports: tuple[Zone, ...]
    resistances: tuple[Zone, ...]
    defends_support: bool
    defends_resistance: bool
    recovery_side: int
    recovery_level: float | None
    recovered_at: datetime | None
    last_established_side: int = 0
    phase: MarketPhase = MarketPhase()


def price_public(value) -> dict:
    return jsonable(asdict(value))


def closes_through(bars: list[Candle], side: int, level: float, buffer: float) -> bool:
    return len(bars) >= 2 and all(side * (bar.close - level) > buffer for bar in bars[-2:])


def observed_zones(bars: list[Candle], ten: list[Candle], prior_ten: list[Candle],
                   side: int, atr: float, session_open: datetime) -> tuple[Zone, ...]:
    zones = [
        Zone(p.price, '1M_SWING', 1, p.known_at) for p in swings(bars[-80:], side)
    ]
    zones.extend(Zone(p.price, '10M_SWING', 3, p.known_at)
                 for p in swings(ten, side, duration=10, left=1))
    first_ten = [b for b in bars if 0 <= (b.start - session_open) // MINUTE < 10]
    if len(first_ten) == 10 and first_ten[0].start == session_open and first_ten[-1].start == session_open + 9*MINUTE:
        extreme = min(b.low for b in first_ten) if side == 1 else max(b.high for b in first_ten)
        zones.append(Zone(extreme, 'OPENING_10M_EXTREME', 3, session_open + 10*MINUTE))
    elif len(first_ten) >= 3:
        # Opening range evolves prior to the first full 10-minute candle.
        early = first_ten[:3]
        extreme = min(b.low for b in early) if side == 1 else max(b.high for b in early)
        zones.append(Zone(extreme, 'OPENING_3M_EXTREME', 1, bar_end(early[-1])))
    if prior_ten:
        zones.extend(Zone(p.price, 'PRIOR_10M_SWING', 3, p.known_at)
                     for p in swings(prior_ten, side, duration=10, left=1))
        extreme = min(b.low for b in prior_ten) if side == 1 else max(b.high for b in prior_ten)
        zones.append(Zone(extreme, 'PRIOR_SESSION_10M_EXTREME', 3, bar_end(prior_ten[-1], 10)))
    tolerance = max(1.5, .36 * atr)
    # Cluster duplicate levels without multiplying several adjacent bars into independent tests.
    grouped: list[list[Zone]] = []
    for zone in sorted(zones, key=lambda z: z.price):
        if grouped and zone.price - grouped[-1][0].price <= tolerance:
            grouped[-1].append(zone)
        else:
            grouped.append([zone])
    result = []
    for group in grouped:
        best = max(group, key=lambda z: (z.strength, z.known_at))
        local_tests = sorted(z.known_at for z in group if z.source == '1M_SWING')
        double = bool(local_tests and (local_tests[-1] - local_tests[0]) >= 3 * MINUTE)
        if double and best.strength < 2:
            best = Zone(best.price, 'REPEATED_1M_REACTION', 2, best.known_at)
        result.append(best)
    return tuple(result)


def directional_steps(bars: list[Candle], side: int) -> tuple[float, ...]:
    if len(bars) < OI_MINUTES:
        return ()
    group = bars[-OI_MINUTES:]
    if any(b.start != group[0].start + i * MINUTE for i, b in enumerate(group)):
        return ()
    origin = group[0].open
    if len(bars) > OI_MINUTES and bars[-OI_MINUTES-1].start + MINUTE == group[0].start:
        origin = bars[-OI_MINUTES-1].close
    closes = [origin, *(b.close for b in group)]
    return tuple(side * (b - a) for a, b in zip(closes, closes[1:]))


def pressure(bars: list[Candle], side: int, atr: float) -> bool:
    steps = directional_steps(bars, side)
    if not steps:
        return False
    net = sum(steps)
    return (net >= .34 * atr and net >= .34 * sum(abs(x) for x in steps)
            and steps[-1] >= -.30 * atr)


def failed_pullback(bars: list[Candle], threes: list[Candle], side: int, atr: float) -> Signal | None:
    """Find the first close through a failed pullback in an established trend.

    Two successive lower closes (or higher closes for CE) can confirm a new
    leg after a brief bounce. The full rolling three-minute return can still
    look flat because its first minute includes the bounce.
    """
    if len(bars) < 9 or len(threes) < 2 or threes[-1].start - threes[-2].start != 3 * MINUTE:
        return None
    latest, pivot = bars[-1], bars[-2]
    if side * (threes[-1].close - threes[-2].close) < .20 * atr:
        return None
    if side * (latest.close - pivot.close) < .30 * atr or side * (pivot.close - bars[-3].close) < 0:
        return None

    def adverse(bar: Candle) -> float:
        return bar.low if side == 1 else -bar.high

    def favorable(bar: Candle) -> float:
        return bar.high if side == 1 else -bar.low

    pivot_depth = adverse(pivot)
    if pivot_depth >= min(adverse(bars[-3]), adverse(latest)):
        return None
    history = bars[-10:-2]
    # Measure the completed impulse first, then the retracement into this pivot.
    turn = max(range(len(history)-4, len(history)), key=lambda i: favorable(history[i]))
    if turn == 0:
        return None
    end = favorable(history[turn])
    start = min(adverse(b) for b in history[:turn])
    impulse = end - start
    retrace = end - pivot_depth
    if impulse < 1.35 * atr or not .45 * atr <= retrace <= .70 * impulse:
        return None
    trigger = favorable(pivot) + max(.6, .10 * atr)
    if not side * pivot.close < trigger <= side * latest.close:
        return None
    return Signal(side, 'FAILED_PULLBACK', bar_end(latest), pivot.start,
                  side * trigger, side * pivot_depth, side * pivot_depth)


def trend_window(threes: list[Candle], atr: float) -> int:
    if len(threes) < 2 or threes[-1].start - threes[-2].start != 3 * MINUTE:
        return 0
    a, b = threes[-2:]
    for side in (1, -1):
        older_edge = side * (a.low if side == 1 else a.high)
        new_edge = side * (b.low if side == 1 else b.high)
        if (side * (a.close - a.open) >= .1 * atr
                and side * (b.close - a.close) >= .22 * atr
                and new_edge >= older_edge - .24 * atr):
            return side
    return 0


def range_bounds(bars: list[Candle], threes: list[Candle], ten: list[Candle],
                 prior_ten: list[Candle], atr: float) -> tuple[float, float] | None:
    if len(ten) < 3 or len(threes) < 5:
        return None
    long, short = ten[-3:], threes[-5:]
    if long[-1].start - long[0].start != 20 * MINUTE or short[-1].start - short[0].start != 12 * MINUTE:
        return None
    long_atr = volatility(ten, n=3, minimum=1)
    short_atr = volatility(threes, n=4, minimum=1)
    long_baseline = volatility(prior_ten[-12:] + ten[:-2], n=12, minimum=1)
    short_baseline = volatility(threes[:-3], n=12, minimum=1)
    if len(prior_ten) + len(ten[:-2]) < 4 or len(threes[:-3]) < 4:
        return None
    if long_atr > 1.05 * long_baseline or short_atr > 1.05 * short_baseline:
        return None
    low, high = min(b.low for b in long), max(b.high for b in long)
    width = high - low
    if width < 1.7 * atr or width > 3.3 * long_atr:
        return None
    if abs(long[-1].close - long[0].open) > .50 * width:
        return None
    if abs(short[-1].close - short[0].open) > .63 * width:
        return None
    if any(not low <= b.close <= high for b in short + bars[-3:]):
        return None
    return low, high


@dataclass(frozen=True)
class PriceTest:
    side: int
    start: datetime
    confirmed: datetime
    extreme: float
    atr: float


@dataclass
class SessionZone:
    side: int
    anchor: float
    width: float
    tests: list[PriceTest]
    invalidated_at: datetime | None = None


@dataclass(frozen=True)
class PendingReversal:
    side: int
    first: PriceTest
    second: PriceTest
    trigger: float
    invalidation: float
    level: float
    intervening_extreme: float


def edge_price(bar: Candle, side: int) -> float:
    return bar.low if side == 1 else bar.high


def away_price(bar: Candle, side: int) -> float:
    return bar.high if side == 1 else bar.low


class SessionReversals:
    """Causal session ledger. A zone survives until two closes accept its break."""

    def __init__(self):
        self.zones: dict[int, list[SessionZone]] = {1: [], -1: []}
        self.pending: list[PendingReversal] = []
        self.last: datetime | None = None

    def advance(self, bars: list[Candle], atr: float) -> list[Signal]:
        current = bars[-1]
        if self.last is not None and current.start != self.last + MINUTE:
            raise DataError('Reversal ledger requires contiguous minute candles')
        self.last = current.start
        if len(bars) < 3:
            return []

        for side in (1, -1):
            for zone in self.zones[side]:
                if zone.invalidated_at is None and closes_through(
                    bars, -side, zone.anchor - side * zone.width,
                    max(.6, .12 * atr),
                ):
                    zone.invalidated_at = bar_end(current)
            self._observe_test(bars, side, atr)

        now = bar_end(current)
        waiting, signals = [], []
        for setup in self.pending:
            side = setup.side
            if side * (edge_price(current, side) - setup.invalidation) < -.18 * atr:
                continue
            if side * (current.close - setup.trigger) <= 0:
                waiting.append(setup)
                continue
            if side * (current.close - bars[-2].close) <= 0:
                waiting.append(setup)
                continue
            signals.append(Signal(
                side, 'DOUBLE_BOTTOM' if side == 1 else 'DOUBLE_TOP',
                now, setup.second.start, setup.trigger, setup.invalidation, setup.level,
                ReversalEvidence(setup.first.start, setup.second.start, setup.first.extreme,
                                 setup.second.extreme, setup.second.confirmed, 'REPEATED_ZONE',
                                 setup.intervening_extreme),
            ))
        self.pending = waiting
        return signals

    def _observe_test(self, bars: list[Candle], side: int, atr: float) -> None:
        pre, tested, confirm = bars[-3:]
        test_edge = edge_price(tested, side)
        if side * (test_edge - edge_price(pre, side)) >= 0:
            return
        if side * (edge_price(confirm, side) - test_edge) < -.28 * atr:
            return
        if side * (confirm.close - test_edge) < .42 * atr:
            return
        test = PriceTest(side, tested.start, bar_end(confirm), test_edge, atr)
        visit_tolerance = min(LEVEL_STRIKE_TOLERANCE, max(2., 1.02 * atr))
        matches = sorted(
            (z for z in self.zones[side] if z.invalidated_at is None
             and abs(z.anchor - test_edge) <= LEVEL_STRIKE_TOLERANCE
             and any(abs(prior.extreme - test_edge) <= visit_tolerance for prior in z.tests)),
            key=lambda z: (abs(z.anchor - test_edge), z.tests[0].start),
        )
        if not matches:
            self.zones[side].append(SessionZone(side, test_edge, max(2., 1.02 * atr), [test]))
            return

        independent = []
        for zone in matches:
            for prior in reversed(zone.tests):
                if (abs(prior.extreme - test_edge) > visit_tolerance
                        or tested.start - prior.start < 2 * MINUTE):
                    continue
                between = [b for b in bars if prior.start < b.start < tested.start]
                if not between:
                    continue
                inside_move = max(side * away_price(b, side) for b in between)
                departure = inside_move - max(side * prior.extreme, side * test_edge)
                closed_reaction = max(side * (b.close - prior.extreme) for b in between)
                if departure >= .53 * atr and closed_reaction >= .30 * atr:
                    independent.append((prior, zone, inside_move))
        if not independent:
            return
        prior, zone, inside_move = max(independent, key=lambda row: (
            row[0].start, -abs(row[1].anchor - test_edge)))
        # The highest rebound (or lowest pullback) belongs to this pair
        # of distinct visits, irrespective of the elapsed number of minutes.
        zone.tests.append(test)
        stop = side * min(side * prior.extreme, side * test_edge)
        trigger = side * inside_move
        self.pending = [x for x in self.pending
                        if not (x.side == side and abs(x.level - zone.anchor) <= zone.width)]
        self.pending.append(PendingReversal(side, prior, test, trigger, stop, zone.anchor,
                                            side * inside_move))

    def watches(self, spot: float, radius: float) -> list[dict]:
        watches = []
        for zones in self.zones.values():
            for zone in zones:
                if zone.invalidated_at is not None or abs(zone.anchor - spot) > radius:
                    continue
                watches.append({'side': zone.side, 'level': zone.anchor,
                                'tests': [price_public(test) for test in zone.tests[-2:]]})
        for setup in self.pending:
            if abs(setup.level - spot) <= radius:
                watches.append({'side': setup.side, 'level': setup.level,
                                'first_test': setup.first.start.isoformat(),
                                'second_test': setup.second.start.isoformat(),
                                'trigger': setup.trigger})
        return watches


def confirmed_reversal(signal: Signal, bars: list[Candle]) -> bool:
    evidence = signal.reversal
    if evidence is None or evidence.pattern != 'REPEATED_ZONE' or evidence.intervening_extreme is None:
        return False
    return signal.side * (bars[-1].close - evidence.intervening_extreme) > 0


def reaction(bars: list[Candle], side: int, price: float, atr: float,
             lookback: int = 8) -> tuple[int, float] | None:
    """An approach to a known level followed by a visible close back away."""
    limit = max(1.5, .43 * atr)
    offset = max(0, len(bars) - lookback)
    for i in range(len(bars)-2, offset-1, -1):
        bar = bars[i]
        edge = bar.low if side == 1 else bar.high
        if not -1.05 * atr <= side * (edge - price) <= limit:
            continue
        after = bars[i+1:]
        base = min(b.low for b in bars[i:]) if side == 1 else max(b.high for b in bars[i:])
        if abs(base - edge) > .20 * atr or max(side * (b.close - price) for b in after) < limit:
            continue
        if side * (bars[-1].close - price) < .12 * atr:
            continue
        return i, base
    return None


def transition_retest(bars: list[Candle], threes: list[Candle], change: TrendTransition,
                      atr: float, atr3: float) -> float | None:
    """Accept a new trend after a completed, defended retest or a new 3m swing."""
    side, level = change.side, change.level
    post = [b for b in bars if b.start >= change.detected_at]
    if len(post) >= 2:
        test, confirm = post[-2:]
        excursion = side * (edge_price(test, side) - level)
        if (-.35 * atr <= excursion <= .42 * atr
                and side * (test.close - level) >= 0
                and side * (confirm.close - level) >= max(.55 * atr, .25 * atr3)
                and side * (confirm.close - test.close) >= .20 * atr):
            return edge_price(test, side)
    completed = [b for b in threes if b.start >= change.detected_at]
    for point in reversed(swings(completed, side, duration=3, left=1)):
        if (side * (point.price - level) > .25 * atr
                and side * (bars[-1].close - point.price) >= .8 * atr):
            return point.price
    return None


def resolve_market_phase(bars: list[Candle], threes: list[Candle], previous: PriceContext | None,
                         atr: float, atr3: float, impulse: int, bounds: tuple | None,
                         signals: list[Signal], support_defended: bool,
                         resistance_defended: bool) -> tuple[int, float | None, int, int,
                                                              float | None, datetime | None, MarketPhase]:
    """Resolve structural state independently of whether a particular entry is executable."""
    last = bars[-1]
    now = bar_end(last)
    buffer = max(.6, .11 * atr)
    trend = previous.trend if previous else 0
    protected = previous.protected if previous else None
    old_side = previous.last_established_side if previous else 0  # audit only
    transition = previous.phase.transition if previous else None
    retest_resolved = False

    if trend and protected is not None and closes_through(bars, -trend, protected, buffer):
        transition = TrendTransition(-trend, protected, now)
        trend, protected = 0, None

    if transition is not None:
        new_stop = transition_retest(bars, threes, transition, atr, atr3)
        if new_stop is not None:
            trend, protected, transition = transition.side, new_stop, None
            retest_resolved = True
        elif closes_through(bars, -transition.side, transition.level, buffer):
            # Failed acceptance stays mixed. The newly accepted side needs
            # its own retest before either trend can be established again.
            transition = TrendTransition(-transition.side, transition.level, now)
    elif not trend and impulse and (previous is None or previous.recovery_side in (0, impulse)):
        edge = edge_price(threes[-2], impulse)
        if not closes_through(bars, -impulse, edge, buffer):
            trend, protected = impulse, edge

    if trend:
        old_side = trend
    if trend and protected is not None:
        for point in reversed(swings(threes[-10:], trend, duration=3, left=1)):
            if (trend * (point.price - protected) > buffer
                    and trend * (last.close - point.price) > max(.9 * atr, .40 * atr3)):
                protected = point.price
                break

    recovery_side = previous.recovery_side if previous else 0
    recovery_level = previous.recovery_level if previous else None
    recovered_at = previous.recovered_at if previous else None
    if recovery_side and ((retest_resolved and trend == recovery_side)
                          or closes_through(bars, -recovery_side, recovery_level, buffer)):
        recovery_side, recovery_level, recovered_at = 0, None, None
    elif recovery_side:
        # A recovery is defended by its last confirmed swing after price has
        # moved away. A shallow counter-move cannot invalidate the old base.
        pivots = swings(threes[-12:], recovery_side, duration=3, left=1)
        for point in reversed(pivots):
            if (point.at >= recovered_at
                    and recovery_side * (point.price - recovery_level) > buffer
                    and recovery_side * (last.close - point.price) >= max(.85 * atr, .4 * atr3)):
                recovery_level = point.price
                if trend == recovery_side:
                    recovery_side, recovery_level, recovered_at = 0, None, None
                break

    for side in (1, -1):
        opposing_defense = support_defended if side == -1 else resistance_defended
        if recovery_side == side or (trend == side and recovery_side != -side):
            continue
        qualified = [signal for signal in signals if signal.reversal is not None and signal.side == side
                     and confirmed_reversal(signal, bars)]
        if recovery_side == -side and opposing_defense:
            # A durable opposite reversal may replace the old recovery. A
            # compact counter-move while its defended swing is close may not.
            qualified = [signal for signal in qualified
                         if abs(last.close - recovery_level) > .55 * atr]
        if qualified:
            best = max(qualified, key=lambda signal: (signal.reversal.pattern == 'REPEATED_ZONE',
                                                       signal.at, -side * signal.invalidation))
            recovery_side, recovery_level, recovered_at = side, best.invalidation, now

    if transition is not None:
        edge = (max(b.high for b in bars) if transition.side == 1 else min(b.low for b in bars))
        accepted = transition.side * (last.close - transition.level) > buffer
        near_edge = abs(last.close - edge) <= .65 * atr
        if accepted and near_edge:
            reason = 'MIXED_NEAR_SESSION_HIGH' if transition.side == 1 else 'MIXED_NEAR_SESSION_LOW'
        else:
            reason = 'MIXED_PENDING_RETEST'
        phase = MarketPhase('MIXED', reason, edge if near_edge and accepted else transition.level, transition)
    elif recovery_side:
        kind = 'BEARISH_TO_BULLISH' if recovery_side == 1 else 'BULLISH_TO_BEARISH'
        phase = MarketPhase(kind, 'CONFIRMED_REVERSAL_STRUCTURE', recovery_level)
    elif bounds is not None and support_defended and resistance_defended:
        phase = MarketPhase('MIXED', 'MIXED_DEFENDED_RANGE')
    elif trend:
        kind = 'CONTINUOUS_BULLISH' if trend == 1 else 'CONTINUOUS_BEARISH'
        phase = MarketPhase(kind, 'DEFENDED_TREND', protected)
    elif bounds is not None:
        phase = MarketPhase('MIXED', 'MIXED_DEFENDED_RANGE')
    else:
        phase = MarketPhase()
    return trend, protected, old_side, recovery_side, recovery_level, recovered_at, phase


def market_signals(bars: list[Candle], prior_ten: list[Candle], session_open: datetime,
                   previous: PriceContext | None,
                   reversals: SessionReversals) -> tuple[PriceContext, list[Signal]]:
    last = bars[-1]
    now = bar_end(last)
    recent = contiguous_tail(bars)
    atr = volatility(recent, minimum=2.5)
    threes, ten = aggregate(bars, 3, session_open), aggregate(bars, 10, session_open)
    atr3 = volatility(threes, minimum=2.5)
    supports = observed_zones(bars, ten, prior_ten, 1, atr, session_open)
    resistances = observed_zones(bars, ten, prior_ten, -1, atr, session_open)
    buffer = max(.6, .11 * atr)
    impulse = trend_window(threes, atr)
    bounds = range_bounds(recent, threes, ten, prior_ten, atr)
    side_zones = {1: supports, -1: resistances}
    results = reversals.advance(recent, atr)

    def nearby_defense(side: int) -> bool:
        # The latest close can probe a level without confirming a break.
        for zone in side_zones[side]:
            if not -.95 * atr <= side * (last.close - zone.price) <= 1.20 * atr:
                continue
            if closes_through(recent, -side, zone.price, buffer):
                continue
            if zone.strength >= 2 or reaction(recent[:-1], side, zone.price, atr, 10):
                return True
            touched = [b for b in recent[-4:] if abs((b.low if side == 1 else b.high) - zone.price) <= .45*atr]
            if zone.known_at <= last.start and touched:
                return True
        return False

    support_defended, resistance_defended = nearby_defense(1), nearby_defense(-1)
    trend, protected, last_established, recovery_side, recovery_level, recovered_at, phase = (
        resolve_market_phase(recent, threes, previous, atr, atr3, impulse, bounds,
                             results, support_defended, resistance_defended)
    )
    if len(recent) < 5:
        context = PriceContext(now, atr, atr3,
                               volatility(ten, minimum=2.5), trend, protected, bounds,
                               supports, resistances, support_defended, resistance_defended,
                               recovery_side, recovery_level, recovered_at, last_established, phase)
        return context, results
    penultimate = recent[-2]

    def add(side: int, scenario: str, origin: datetime, trigger: float, stop: float, level: float):
        if (side * (last.close - trigger) >= 0
                and side * (penultimate.close - trigger) < 0
                and side * (trigger - stop) > 0):
            results.append(Signal(side, scenario, now, origin, trigger, stop, level))

    for side in (1, -1):
        levels, opposing = side_zones[side], side_zones[-side]
        protected_opposite = trend == -side and recovery_side != side
        # A defended zone cannot be traded through on a single close. The double
        # test path still has to break its neckline and pass the live 3m gate.
        if protected_opposite:
            continue
        if trend == side:
            failed = failed_pullback(recent, threes, side, atr)
            if failed is not None:
                results.append(failed)
        if bounds:
            zone = bounds[0] if side == 1 else bounds[1]
            retest = reaction(recent, side, zone, atr, 6)
            if retest and abs(last.close - zone) <= .45 * (bounds[1] - bounds[0]):
                i, base = retest
                test = recent[i]
                trigger = (test.high if side == 1 else test.low) + side * buffer
                add(side, 'RANGE_EDGE', test.start, trigger, base, zone)
        elif impulse == side or trend == side or recovery_side == side:
            for zone in sorted(levels, key=lambda z: abs(last.close-z.price)):
                if zone.known_at >= last.start or not 0 < side * (last.close - zone.price) <= 3.4 * atr:
                    continue
                retest = reaction(recent, side, zone.price, atr)
                if retest:
                    i, base = retest
                    test = recent[i]
                    trigger = (test.high if side == 1 else test.low) + side * buffer
                    in_pullback = i >= 2 and side * (recent[i-2].close - base) > .45 * atr
                    if in_pullback:
                        add(side, 'PULLBACK_CONTINUATION', test.start, trigger, base, zone.price)
            # A clean impulse may resume from a shallow pause with no formal pivot.
            pause = recent[-4:-1]
            floor = min(b.low for b in pause) if side == 1 else max(b.high for b in pause)
            edge = max(b.high for b in pause) if side == 1 else min(b.low for b in pause)
            has_pause = any(side * (b.close-b.open) < .10 * atr for b in pause)
            if has_pause and abs(edge-floor) <= 2.20 * atr:
                add(side, 'TREND_RESUMPTION', pause[0].start, edge + side * buffer, floor, floor)
            if recovery_side == side and recovered_at is not None:
                # A higher low/lower high after a confirmed reversal provides
                # a fresh continuation entry with a new structural stop.
                for pullback in reversed(swings(recent[-14:], side)):
                    if pullback.at < recovered_at or side * (pullback.price - recovery_level) < .28 * atr:
                        continue
                    lead = [b for b in recent if pullback.at - 3*MINUTE <= b.start < pullback.at]
                    if len(lead) >= 2:
                        retest_trigger = max(b.high for b in lead) if side == 1 else min(b.low for b in lead)
                        add(side, 'PULLBACK_CONTINUATION', pullback.at, retest_trigger + side * buffer,
                            pullback.price, pullback.price)
                    break
        # A known level must predate the first break candle.
        for zone in opposing:
            if (zone.known_at > penultimate.start
                    or abs(last.close - zone.price) > 2.3 * atr
                    or not closes_through(recent, side, zone.price, buffer)):
                continue
            prior = recent[-3]
            if side * (prior.close - zone.price) > buffer:
                continue
            legs = recent[-4:-1]
            stop = min(b.low for b in legs) if side == 1 else max(b.high for b in legs)
            # The second completed close establishes acceptance, but the price
            # trigger stays at the first break so the chase check still applies.
            results.append(Signal(side, 'ACCEPTED_BREAKOUT' if side == 1 else 'ACCEPTED_BREAKDOWN',
                                  now, penultimate.start, zone.price + side * buffer, stop, zone.price))
        if len(recent) == len(bars) and recent[0].start == session_open and 6 <= len(recent) <= 9:
            initial = recent[:3]
            trigger = (max(b.high for b in initial) if side == 1 else min(b.low for b in initial)) + side * buffer
            stop = (min(b.low for b in recent[-3:-1]) if side == 1 else max(b.high for b in recent[-3:-1]))
            if pressure(recent, side, atr) and side * (last.close - initial[0].open) >= atr:
                add(side, 'OPENING_MOMENTUM', session_open, trigger, stop, trigger)
                # At 09:21 the opening break may already have been accepted.
                if (len(recent) == 6 and closes_through(recent, side, trigger, 0)
                        and not any(s.scenario == 'OPENING_MOMENTUM' and s.side == side for s in results)):
                    results.append(Signal(side, 'OPENING_MOMENTUM', now, session_open, trigger, stop, trigger))
    context = PriceContext(now, atr, atr3,
                           volatility(ten, minimum=2.5), trend, protected, bounds,
                           supports, resistances, support_defended, resistance_defended,
                           recovery_side, recovery_level, recovered_at, last_established, phase)
    return context, results


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
        return cls(timestamp(value['at']), timestamp(value['through']), value['expiry'],
                   tuple(OIRow(**row) for row in value['rows']))


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
        oi = row.get('oi')
        if row['expiry'] != expiry or oi is None:
            continue
        if type(oi) not in (float, int) or not math.isfinite(oi) or oi < 0 or int(oi) != oi:
            continue
        rows.append(OIRow(row['instrument_key'], row['side'], float(row['strike']), int(oi)))
    return OISnapshot(at, through, expiry, tuple(rows))


def match_oi(saved: list[dict], current: OISnapshot, cfg: Config) -> OIWindow | None:
    options = []
    for row in saved:
        previous = OISnapshot.restore(row)
        if previous.expiry != current.expiry or previous.at.date() != current.at.date():
            continue
        elapsed = (current.at - previous.at).total_seconds()
        expected = DISPATCH_INTERVAL.total_seconds()
        if abs(elapsed - expected) <= cfg.oi_jitter_seconds:
            options.append((abs(elapsed - expected), previous.at, previous))
    if not options:
        return None
    past = min(options, key=lambda item: (item[0], item[1]))[2]
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
    return sorted({float(row['strike_price']) for row in contracts
                   if row['instrument_type'] in ('CE', 'PE')})


@dataclass(frozen=True)
class OIPair:
    strike: float
    call: OIObservation | None
    put: OIObservation | None

    @property
    def state(self) -> str:
        if self.call is None or self.put is None:
            return 'MISSING'
        call, put = self.call.increase, self.put.increase
        if max(abs(call), abs(put)) < OI_LEVEL_MATERIAL_CHANGE:
            return 'QUIET'
        if call < 0 < put:
            return 'BULLISH'
        if put < 0 < call:
            return 'BEARISH'
        return 'MIXED'

    def score(self, side: int) -> float | None:
        if self.call is None or self.put is None:
            return None
        return side * (self.put.increase - self.call.increase)

    def public(self) -> dict:
        return {'strike': self.strike, 'state': self.state,
                'call_change_pct': 100 * self.call.increase if self.call is not None else None,
                'put_change_pct': 100 * self.put.increase if self.put is not None else None}


@dataclass(frozen=True)
class StrikeBand:
    atm: float
    pairs: dict[int, OIPair]

    @classmethod
    def build(cls, grid: list[float], spot: float, pairs: dict[float, OIPair]):
        if not grid or not grid[0] <= spot <= grid[-1]:
            return None
        center = min(range(len(grid)), key=lambda i: (abs(grid[i] - spot), grid[i]))
        observed = {}
        for offset in (-2, -1, 0, 1, 2):
            index = center + offset
            if 0 <= index < len(grid):
                strike = grid[index]
                observed[offset] = pairs.get(strike, OIPair(strike, None, None))
        return cls(grid[center], observed)

    def public(self) -> dict:
        return {'atm': self.atm, 'strikes': [
            {'offset': offset, **self.pairs[offset].public()} if offset in self.pairs
            else {'offset': offset, 'state': 'MISSING_LISTING'}
            for offset in (-2, -1, 0, 1, 2)
        ]}


def paired_oi(window: OIWindow | None) -> dict[float, OIPair]:
    if window is None:
        return {}
    by_strike: dict[float, dict[str, OIObservation]] = {}
    for item in window.changes:
        by_strike.setdefault(item.row.strike, {})[item.row.side] = item
    return {strike: OIPair(strike, rows.get('CE'), rows.get('PE')) for strike, rows in by_strike.items()}


def pairs_at(level: float, grid: list[float], pairs: dict[float, OIPair], *,
             cover_strike_interval: bool = False) -> list[OIPair]:
    strikes = sorted((strike for strike in grid if abs(strike - level) <= LEVEL_STRIKE_TOLERANCE),
                     key=lambda strike: (abs(strike - level), strike))
    if not strikes and cover_strike_interval:
        lower = max((strike for strike in grid if strike < level), default=None)
        upper = min((strike for strike in grid if strike > level), default=None)
        # Cover the center of a listed interval. Skip gaps in the listing.
        if lower is not None and upper is not None and upper - lower <= NIFTY_STRIKE_INTERVAL:
            strikes = [lower if level - lower <= upper - level else upper]
    return [pairs.get(strike, OIPair(strike, None, None)) for strike in strikes]


@dataclass(frozen=True)
class OILevel:
    strike: float
    oi: int
    change: float | None


def oi_levels(window: OIWindow, spot: float, side: int, atr: float) -> list[OILevel]:
    kind = 'CE' if side == 1 else 'PE'
    changes = {x.row.key: x.increase for x in window.changes}
    max_distance = max(300.0, 24 * atr)
    vicinity = [r for r in window.snapshot.rows
                if r.side == kind and r.oi > 0 and abs(r.strike - spot) <= max_distance]
    if not vicinity:
        return []
    reference = median(r.oi for r in vicinity)
    levels = [OILevel(r.strike, r.oi, changes.get(r.key)) for r in vicinity
              if r.oi >= reference or changes.get(r.key, 0) > OI_LEVEL_MATERIAL_CHANGE]
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
    return max(.8, .18 * atr_1m, .12 * atr_3m)


def next_oi_objective(levels: list[OILevel], side: int, beyond: float,
                      atr: float, separation: float = 0) -> float | None:
    for row in levels:
        objective = row.strike - side * max(.5, .10 * atr)
        if side * (objective - beyond) > max(.4 * atr, separation):
            return round(objective, 4)
    return None


@dataclass(frozen=True)
class RiskAssessment:
    plan: RiskPlan | None
    reason: str
    evidence: dict


def stop_for_setup(signal: Signal, ctx: PriceContext, spot: float, cfg: Config,
                   stop_reference: float) -> tuple[float, float]:
    side, atr = signal.side, ctx.atr
    atr3 = ctx.atr3 if signal.scenario in CONTINUATION_SCENARIOS else 0
    # Work in the signed direction, then round outward so rounding never
    # cuts into the structural buffer. Use smaller steps in quieter markets.
    buffered = min(side * signal.invalidation, side * stop_reference) - stop_buffer(atr, atr3)
    signed_stop = min(buffered, side * spot - cfg.min_stop_atr * atr)
    step = 10 if atr >= 10 else 5 if atr >= 5 else 1
    rounded = math.floor(signed_stop / step) * step
    # A cosmetic round-out cannot disqualify a structurally valid stop.
    stop = side * (rounded if side * spot - rounded <= cfg.max_stop_atr * atr else signed_stop)
    return stop, side * (spot - stop)


def defended_walls(levels: list[OILevel], pairs: dict[float, OIPair], bars: list[Candle],
                   spot: float, side: int, atr: float) -> list[float]:
    hostile = 'BEARISH' if side == 1 else 'BULLISH'
    walls = []
    for row in levels:
        if side * (row.strike - spot) <= 0:
            continue
        pair = pairs.get(row.strike)
        # Fresh opposing OI plus a recent price rejection can limit a target.
        # Gross open interest alone only says where to watch the reaction.
        if pair is not None and pair.state == hostile and reaction(bars, -side, row.strike, atr, lookback=6):
            walls.append(row.strike)
    return walls


def risk_plan(signal: Signal, ctx: PriceContext, levels: list[OILevel], spot: float,
              cfg: Config, stop_reference: float, *, pairs: dict[float, OIPair],
              bars: list[Candle]) -> RiskAssessment:
    side, atr = signal.side, ctx.atr
    stop, risk = stop_for_setup(signal, ctx, spot, cfg, stop_reference)
    evidence = {'structural_invalidation': signal.invalidation, 'previous_3m_close': stop_reference,
                'planned_stop': stop, 'risk_points': round(risk, 4),
                'minimum_reward_risk': cfg.min_reward_risk}
    if stop <= 0 or not 0 < risk <= cfg.max_stop_atr * atr:
        return RiskAssessment(None, 'STRUCTURAL_STOP_TOO_WIDE_OR_INVALID', evidence)

    opposing = ctx.resistances if side == 1 else ctx.supports
    checkpoint_levels = {zone.price for zone in opposing
                         if zone.strength >= 3 and side * (zone.price - spot) > 0}
    barriers = defended_walls(levels, pairs, bars, spot, side, atr)
    if signal.scenario == 'RANGE_EDGE' and ctx.range_bounds:
        edge = ctx.range_bounds[1] if side == 1 else ctx.range_bounds[0]
        if side * (edge - spot) > 0:
            barriers.append(edge)
            checkpoint_levels.add(edge)
    checkpoints = sorted(checkpoint_levels, key=lambda level: side * level)
    barrier = min(barriers, key=lambda level: side * level, default=None)
    required = spot + side * cfg.min_reward_risk * risk
    evidence.update(minimum_target=round(required, 4), structural_checkpoints=checkpoints,
                    opposing_barrier=barrier)

    # Prefer the nearest meaningful OI objective that can pay for the stop.
    # Completed 10m levels are checkpoints or fallback objectives, and actual
    # opposing price and OI can cap the route. A range edge is also a cap.
    ranked = [(row.strike, 'OI_OBJECTIVE') for row in levels]
    ranked.extend((level, '10M_STRUCTURE') for level in checkpoints)
    checked = []
    evidence['target_checks'] = checked
    target = None
    found_t1_without_t2 = False
    for level, source in ranked:
        if side * (level - spot) <= 0:
            continue
        if source == 'OI_OBJECTIVE' and any(
            abs(level - checkpoint) <= LEVEL_STRIKE_TOLERANCE for checkpoint in checkpoints
        ):
            source = 'OI_OBJECTIVE_NEAR_10M_STRUCTURE'
        if source == '10M_STRUCTURE':
            level -= side * max(.5, .14 * atr)
        reward_risk = side * (level - spot) / risk
        if barrier is not None and side * (level - barrier) > 0:
            reason = 'BEYOND_DEFENDED_BARRIER'
        elif reward_risk < cfg.min_reward_risk:
            reason = 'BELOW_MINIMUM_REWARD'
        else:
            t2 = next_oi_objective(levels, side, level, atr, separation=max(.8 * atr, .45 * risk))
            reason = 'QUALIFIED' if t2 is not None else 'NO_FURTHER_OI_TARGET'
            if t2 is None:
                found_t1_without_t2 = True
        checked.append({'level': round(level, 4), 'source': source,
                        'reward_risk': round(reward_risk, 4), 'reason': reason})
        if reason == 'QUALIFIED':
            target = (level, source, reward_risk, t2)
            break

    if target is None:
        if found_t1_without_t2:
            reason = 'NO_FURTHER_OI_TARGET'
        else:
            reason = 'DEFENDED_BARRIER_LIMITS_REWARD' if barrier is not None else 'NO_TARGET_MEETS_REWARD_TO_RISK'
        return RiskAssessment(None, reason, evidence)
    t1, source, reward, t2 = target
    policy = 'CONFIRMED_3M_SWING' if signal.scenario in CONTINUATION_SCENARIOS else 'STANDARD_POST_T1'
    plan = RiskPlan(round(stop, 4), round(t1, 4), t2, source, 'NEXT_OI_LEVEL',
                    round(risk, 4), round(reward, 4), policy)
    evidence['intermediate_levels'] = sorted(
        {level for level in checkpoints + [row.strike for row in levels]
         if 0 < side * (level - spot) < side * (t1 - spot)},
        key=lambda level: side * level,
    )
    return RiskAssessment(plan, 'QUALIFIED', evidence)


def live_contract(row: dict, quote: dict | None, now: datetime, index_time: datetime,
                  band: StrikeBand, offset: int, cfg: Config) -> dict:
    checked_quote(quote, now, cfg.quote_max_age_seconds)
    assert quote is not None
    seen = timestamp(quote['timestamp'])
    if abs((seen - index_time).total_seconds()) > cfg.quote_max_skew_seconds:
        raise DataError('INDEX_OPTION_QUOTE_SKEW')
    bid = read_number(quote['bid'], 'bid', positive=True)
    ask = read_number(quote['ask'], 'ask', positive=True)
    spread = 200 * (ask - bid) / (ask + bid)
    lot = read_number(row['lot_size'], 'lot_size', positive=True)
    depth = min(read_number(quote[key], key, nonnegative=True) for key in ('bid_qty', 'ask_qty')) / lot
    if not lot.is_integer() or not 0 <= spread <= cfg.max_spread_percent:
        raise DataError('INVALID_LIVE_SPREAD_OR_LOT')
    if depth < cfg.min_depth_lots:
        raise DataError('INSUFFICIENT_LIVE_DEPTH')
    pair = band.pairs[offset]
    return {'instrument_key': row['instrument_key'], 'side': row['instrument_type'],
            'strike': pair.strike, 'atm': band.atm, 'offset': offset,
            'expiry': row['expiry'], 'bid': bid, 'ask': ask, 'spread_pct': round(spread, 4),
            'depth_lots': depth, 'lot_size': int(lot), 'quote_time': seen.isoformat(),
            'paired_oi_at_contract': pair.public()}


class Upstox:

    def __init__(self, token: str):
        if not token or any((c in token for c in '\r\n')):
            raise ProviderError('UPSTOX_ANALYTICS_TOKEN missing or invalid')
        self._token = token

    def get(self, path: str, params: dict | None=None):
        url = 'https://api.upstox.com' + path + ('?' + urlencode(params) if params else '')
        req = Request(url, headers={'Authorization': 'Bearer ' + self._token, 'Accept': 'application/json',
                                    'User-Agent': 'nifty-scanner/' + VERSION})
        for attempt in range(2):
            try:
                with urlopen(req, timeout=7) as r:

                    def reject_constant(value):
                        raise ValueError('Invalid numeric JSON')
                    obj = json.load(r, parse_constant=reject_constant, parse_float=finite_json_float)
                if not isinstance(obj, dict) or obj.get('status') != 'success' or 'data' not in obj:
                    raise ProviderError('Upstox returned an unsuccessful or invalid response')
                return obj['data']
            except HTTPError as e:
                if e.code in (429, 500, 502, 503, 504) and attempt < 1:
                    time.sleep(1 + attempt)
                    continue
                raise ProviderError(f'Upstox request failed HTTP {e.code}') from None
            except (URLError, TimeoutError, OSError, ValueError) as e:
                if attempt < 1:
                    time.sleep(1 + attempt)
                    continue
                raise ProviderError('Upstox request failed or returned invalid JSON') from None
        raise ProviderError('Upstox request failed')

    def session(self, now: datetime):
        data = self.get('/v2/market/timings/' + now.astimezone(IST).date().isoformat())
        matches = [x for x in data if x.get('exchange') == 'NFO'] if isinstance(data, list) else []
        if not matches:
            return None
        sessions = []
        for row in matches:
            start = datetime.fromtimestamp(float(row['start_time']) / 1000, timezone.utc).astimezone(IST)
            end = datetime.fromtimestamp(float(row['end_time']) / 1000, timezone.utc).astimezone(IST)
            if start.date() == now.astimezone(IST).date() and start < end:
                sessions.append((start, end))
        return next(((a, b) for a, b in sessions if a <= now.astimezone(IST) < b), None)

    def candles(self, key=INDEX):
        data = self.get('/v3/historical-candle/intraday/' + quote(key, safe='') + '/minutes/1')
        if not isinstance(data, dict) or not isinstance(data.get('candles'), list):
            raise ProviderError('Invalid candle response')
        return data['candles']

    def prior_ten(self, today: date):
        previous_day = today - timedelta(days=1)
        from_day = today - timedelta(days=12)
        path = ('/v3/historical-candle/' + quote(INDEX, safe='') + '/minutes/10/'
                + previous_day.isoformat() + '/' + from_day.isoformat())
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
            if r.get('underlying_key') != INDEX or r.get('instrument_type') not in ('CE', 'PE'):
                continue
            try:
                exp = date.fromisoformat(str(r['expiry']))
            except (ValueError, KeyError):
                continue
            if exp >= today:
                try:
                    strike = read_number(r['strike_price'], 'listed_strike', positive=True)
                    lot = read_number(r['lot_size'], 'listed_lot', positive=True)
                    key = r['instrument_key']
                    if not lot.is_integer() or not isinstance(key, str) or not key:
                        continue
                except (DataError, KeyError):
                    continue
                rows.append({'expiry': exp.isoformat(), 'instrument_key': key,
                             'instrument_type': r['instrument_type'],
                             'strike_price': strike, 'lot_size': int(lot)})
        if not rows:
            raise ProviderError('No unexpired NIFTY option contracts')
        expiry = min((date.fromisoformat(r['expiry']) for r in rows)).isoformat()
        return (expiry, [r for r in rows if r['expiry'] == expiry])

    def chain(self, expiry: str, contracts: list[dict]):
        data = self.get('/v2/option/chain', {'instrument_key': INDEX, 'expiry_date': expiry})
        if not isinstance(data, list) or not data:
            raise ProviderError('Empty option chain')
        valid = {r['instrument_key']: (float(r['strike_price']), r['instrument_type']) for r in contracts if r.get('instrument_key') and r.get('strike_price') is not None}
        metadata = {r['instrument_key']: r for r in contracts if r.get('instrument_key')}
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
                    delta = float(greeks['delta']) if greeks.get('delta') is not None else None
                    gamma = float(greeks['gamma']) if greeks.get('gamma') is not None else None
                    theta = float(greeks['theta']) if greeks.get('theta') is not None else None
                    vega = float(greeks['vega']) if greeks.get('vega') is not None else None
                    iv = float(greeks['iv']) if greeks.get('iv') is not None else None
                    prev_oi = float(market['prev_oi']) if market.get('prev_oi') is not None else None
                    chain_bid = float(market.get('bid_price') or 0)
                    chain_ask = float(market.get('ask_price') or 0)
                    chain_bid_qty = float(market.get('bid_qty') or 0)
                    chain_ask_qty = float(market.get('ask_qty') or 0)
                except (ValueError, TypeError):
                    raise ProviderError('Invalid OI/greek data') from None
                if not all((math.isfinite(x) and x >= 0 for x in (ltp, volume, chain_bid, chain_ask, chain_bid_qty, chain_ask_qty))):
                    raise ProviderError('Invalid option chain values')
                if oi is not None and (not math.isfinite(oi) or oi < 0 or not oi.is_integer()):
                    oi = None
                if any((x is not None and (not math.isfinite(x)) for x in (delta, gamma, theta, vega, iv, prev_oi))):
                    raise ProviderError('Invalid option greek data')
                lot = metadata[key].get('lot_size')
                if lot is None or not math.isfinite(float(lot)) or float(lot) <= 0 or (not float(lot).is_integer()):
                    raise ProviderError('Missing or invalid live lot size')
                result.append({'instrument_key': key, 'expiry': expiry, 'strike': strike, 'side': side, 'oi': oi, 'ltp': ltp, 'volume': volume, 'delta': delta, 'gamma': gamma, 'theta': theta, 'vega':vega, 'iv':iv, 'prev_oi':prev_oi, 'lot_size': lot, 'chain_bid':chain_bid, 'chain_ask':chain_ask, 'chain_bid_qty':chain_bid_qty, 'chain_ask_qty':chain_ask_qty})
        # Upstox's chain supplies a spot reference and a much larger distant
        # strike universe than this strategy needs. Keep the listed grid in
        # contracts and retain the local OI profile separately.
        snapshot_spots = [r.get('underlying_spot_price') for r in data]
        observed_spots = [float(v) for v in snapshot_spots
                          if type(v) in (int, float) and math.isfinite(v) and v > 0]
        if observed_spots:
            center = median(observed_spots)
            result = [r for r in result if abs(r['strike'] - center) <= 650]
        if len(result) < 4 or not {'CE', 'PE'}.issubset({r['side'] for r in result}):
            raise ProviderError('Incomplete option chain')
        return result

    def quotes(self, keys: list[str]):
        if not keys:
            return {}
        data = self.get('/v2/market-quote/quotes', {'instrument_key': ','.join(dict.fromkeys(keys))})
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
                numeric = {name: float(q[name]) if q.get(name) is not None else None for name in ('oi', 'average_price')}
                for name, value in numeric.items():
                    if value is not None and (not math.isfinite(value)):
                        numeric[name] = None
                quoted = {'last_price': price, 'bid': float(b.get('price') or 0), 'bid_qty': float(b.get('quantity') or 0), 'ask': float(a.get('price') or 0), 'ask_qty': float(a.get('quantity') or 0)}
                if any((not math.isfinite(x) or x < 0 for x in quoted.values())):
                    continue
                out[key] = {**quoted, 'timestamp': stamp, **numeric}
            except (TypeError, ValueError):
                continue
        return out



def starting_state(now: datetime) -> dict:
    return {'schema': 7, 'engine_version': VERSION, 'initialized_at': now.isoformat(),
            'initialized_flat': True, 'session_date': now.date().isoformat(),
            'position': None, 'history': [], 'outbox': [], 'last_exit': None,
            'v124': {'session_date': now.date().isoformat(), 'oi_samples': [],
                     'consumed_signals': []}}


def validate_state(state: dict):
    if (not isinstance(state, dict) or state.get('schema') != 7 or 'position' not in state
            or not isinstance(state.get('history'), list) or not isinstance(state.get('outbox'), list)):
        raise ScannerError('Invalid or unsupported persisted state')
    ids = set()
    for event in state['outbox']:
        if (not isinstance(event, dict) or not isinstance(event.get('id'), str)
                or event['id'] in ids or event.get('status') not in
                ('PENDING', 'CLAIMED', 'SENT', 'DELIVERY_UNCERTAIN', 'EXPIRED')):
            raise ScannerError('Invalid or duplicate persisted outbox event')
        ids.add(event['id'])
    p = state['position']
    if p is not None:
        if (not isinstance(p, dict) or not p.get('id') or p.get('status') != 'OPEN'
                or p.get('direction') not in ('BULLISH', 'BEARISH')):
            raise ScannerError('Invalid persisted reference position')
        side = 1 if p['direction'] == 'BULLISH' else -1
        entry, stop, initial, t1, t2 = [read_number(p.get(k, p.get('stop') if k == 'initial_stop' else None),
                                                   k, positive=True)
                                        for k in ('entry_spot', 'stop', 'initial_stop', 't1', 't2')]
        took_t1 = p.get('t1_hit', False)
        t1_exit_pct = p.get('t1_exit_pct', 50)
        if type(t1_exit_pct) is not int or not 0 < t1_exit_pct < 100:
            raise ScannerError('Invalid persisted T1 allocation')
        if (type(took_t1) is not bool or side*(entry-initial) <= 0
                or side*(t1-entry) <= 0 or side*(t2-t1) <= 0
                or side*(stop-initial) < 0 or (not took_t1 and side*(entry-stop) <= 0)):
            raise ScannerError('Invalid persisted position prices')
        if not p.get('instrument_key') or not p.get('expiry'):
            raise ScannerError('Invalid persisted contract identity')
        timestamp(p.get('opened_at'))
        timestamp(p.get('last_candle'))
    if 'v124' in state:
        engine = state['v124']
        if (not isinstance(engine, dict) or not isinstance(engine.get('oi_samples'), list)
                or not isinstance(engine.get('consumed_signals'), list)):
            raise ScannerError('Invalid persisted strategy state')


def load_state(path:Path) -> dict:
    if not path.exists():
        raise ScannerError('STATE_FILE_MISSING: manually reconcile existing positions before --initialize-flat')
    try:
        with path.open(encoding='utf-8') as f:
            s=json.load(f,parse_constant=lambda _:(_ for _ in ()).throw(ValueError('Nonfinite state')))
    except (OSError,ValueError) as exc:
        raise ScannerError('State unreadable; fail closed') from exc
    validate_state(s)
    return s


def save_state(path:Path,s:dict):
    validate_state(s)
    path.parent.mkdir(parents=True,exist_ok=True)
    fd,tmp=tempfile.mkstemp(prefix='.state-',dir=path.parent)
    try:
        with os.fdopen(fd,'w',encoding='utf-8') as f:
            json.dump(s,f,sort_keys=True,separators=(',',':'),allow_nan=False)
            f.flush();os.fsync(f.fileno())
        os.replace(tmp,path)
        d=os.open(path.parent,os.O_RDONLY)
        try:os.fsync(d)
        finally:os.close(d)
    finally:
        if os.path.exists(tmp):os.unlink(tmp)


@contextmanager
def local_lock(state_path:Path):
    state_path.parent.mkdir(parents=True,exist_ok=True)
    with open(str(state_path)+'.lock','a+') as f:
        fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
        try:yield
        finally:fcntl.flock(f,fcntl.LOCK_UN)


def ensure_engine(state: dict, now: datetime) -> dict:
    if state.get('position') and timestamp(state['position']['opened_at']).date() > now.date():
        raise ScannerError('FUTURE_DATED_REFERENCE_POSITION')
    if state.get('v124', {}).get('session_date') != now.date().isoformat():
        state['v124'] = starting_state(now)['v124']
    state['session_date'] = now.date().isoformat()
    state['engine_version'] = VERSION
    return state['v124']


def new_event(state:dict,kind:str,details:dict,now:datetime) -> str:
    if kind not in ALERT_KINDS:raise ScannerError('Non-actionable alert kind')
    details=copy.deepcopy(details)
    email_observation = details.pop('email_observation', None)
    digest=hashlib.sha256(json.dumps([kind,details],sort_keys=True,allow_nan=False,
                                      separators=(',',':')).encode()).hexdigest()[:24]
    if not any(e['id']==digest for e in state['outbox']):
        event = {'id': digest, 'kind': kind, 'details': details,
                 'created_at': now.isoformat(), 'status': 'PENDING'}
        if email_observation is not None:
            event['email_observation'] = email_observation
        state['outbox'].append(event)
    return digest


def claim_outbox(state:dict,token:str,now:datetime):
    if not token:raise ScannerError('Notification claim token absent')
    for event in state['outbox']:
        if event.get('kind') not in ALERT_KINDS:continue
        # Previous claims with no attempted_at cannot have reached SMTP via this
        # implementation: safe to reclaim when a workflow crashed pre-delivery.
        legacy_pending=event.get('status')=='PENDING' and not event.get('attempted_at')
        # Old versions could CLAIM without the v123 durable commit-before-SMTP
        # protocol. Their state CANNOT prove non-delivery; do not resend.
        fresh_reclaim=(event.get('status')=='CLAIMED' and
                       event.get('claim_policy')=='V123_PHASED' and
                       not event.get('attempted_at'))
        if (legacy_pending or fresh_reclaim) and event['kind'] == 'ENTRY':
            details = event.get('details') or {}
            active_id = (state.get('position') or {}).get('id')
            created = timestamp(event.get('created_at'))
            if details.get('position_id') != active_id or now - created > 3*MINUTE:
                event.update(status='EXPIRED', expired_at=now.isoformat(), claim=None)
                continue
        if legacy_pending or fresh_reclaim:
            event.update(status='CLAIMED',claim=token,claimed_at=now.isoformat(),
                         claim_policy='V123_PHASED')


def append_audit(path:Path,event:dict):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('a',encoding='utf-8') as f:
        f.write(json.dumps(event,sort_keys=True,allow_nan=False,separators=(',',':'))+'\n')
        f.flush();os.fsync(f.fileno())


def record_inputs(path:Path,record:dict):
    path.parent.mkdir(parents=True,exist_ok=True)
    raw=json.dumps(record,allow_nan=False,sort_keys=True,separators=(',',':')).encode()
    fd,tmp=tempfile.mkstemp(prefix='.capture-',dir=path.parent)
    try:
        with os.fdopen(fd,'wb') as stream:
            with gzip.GzipFile(fileobj=stream,mode='wb',compresslevel=7,mtime=0) as z:z.write(raw)
            stream.flush();os.fsync(stream.fileno())
        os.replace(tmp,path)
    finally:
        if os.path.exists(tmp):os.unlink(tmp)


class RecordingProvider:
    """Time-stamped, exact source-call recording with no token or secrets."""
    def __init__(self,underlying):
        self.provider=underlying
        self.calls=[]
    def __getattr__(self,name):
        attr=getattr(self.provider,name)
        if not callable(attr):return attr
        def observed(*args,**kwargs):
            signature={'name':name,'args':jsonable(args),'kwargs':jsonable(kwargs)}
            try:
                value=attr(*args,**kwargs)
                self.calls.append({**signature,'result':jsonable(value)})
                return value
            except (ProviderError,DataError) as exc:
                self.calls.append({**signature,'error':type(exc).__name__,'reason':str(exc)})
                raise
        return observed


def jsonable(value:Any):
    if isinstance(value,(datetime,date)):return value.isoformat()
    if isinstance(value,(list,tuple)):return [jsonable(v) for v in value]
    if isinstance(value,dict):return {str(k):jsonable(v) for k,v in value.items()}
    if isinstance(value,(float,int,str,bool)) or value is None:return value
    if isinstance(value,Path):return str(value)
    raise TypeError('Non-serializable provider payload')


class ReplayProvider:
    """Exact ordered API-recording replay: no network, no future snapshots."""
    def __init__(self,calls:list[dict]):self.calls=calls;self.index=0
    def __getattr__(self,name):
        def recorded(*args,**kwargs):
            if self.index>=len(self.calls):raise ProviderError('CAPTURE_EXHAUSTED:'+name)
            r=self.calls[self.index];self.index+=1
            if r['name']!=name or r['args']!=jsonable(args) or r['kwargs']!=jsonable(kwargs):
                raise ProviderError('CAPTURE_CALL_SEQUENCE_MISMATCH expected '+r['name']+' got '+name)
            if 'error' in r:
                cls = DataError if r['error'] == 'DataError' else ProviderError
                raise cls(r['reason'])
            if name=='session' and r['result'] is not None:
                return tuple(timestamp(x) for x in r['result'])
            return copy.deepcopy(r['result'])
        return recorded


def checked_quote(q:dict|None,now:datetime,max_age:float,field='last_price')->float:
    if not isinstance(q,dict):raise DataError('Missing live quote')
    price=read_number(q.get(field),field,positive=True)
    age=(now-timestamp(q.get('timestamp'))).total_seconds()
    if not -2<=age<=max_age:raise DataError('STALE_OR_FUTURE_DATED_QUOTE')
    return price


# ----------------------- Chronological position management -----------------

def position_event_payload(p:dict,now:datetime,**more):
    fields=('id','direction','instrument_key','side','strike','expiry','entry_spot','entry_ask','initial_stop',
            'stop','t1','t2','t1_exit_pct','remaining_pct','opened_at','scenario','t1_source','t2_source','stop_policy')
    return {'position_id':p['id'],'observed_at':now.isoformat(),
            'position':{k:p.get(k) for k in fields},'broker_order_submitted':False,
            'broker_fill_confirmed':False,**more}




def close_reference(position: dict, at: datetime, reason: str, observed: float | None,
                    source: str) -> dict:
    return dict(position, status='CLOSED', closed_at=at.isoformat(), exit_reason=reason,
                observed_exit_spot=observed, exit_source=source, fill_confirmed=False)


def manage_reference(p: dict, bars: list[Candle], spot: float | None,
                     now: datetime, deadline: datetime,
                     cfg: Config, *,
                     spot_at: datetime | None = None) -> tuple[dict | None, list[tuple[str, dict]], dict | None, list[str]]:
    position = copy.deepcopy(p)
    side = 1 if position['direction'] == 'BULLISH' else -1
    cursor = timestamp(position['last_candle'])
    opening = timestamp(position['opened_at'])
    alerts: list[tuple[str, dict]] = []
    warnings: list[str] = []

    def emit(kind, at, **fields):
        alerts.append((kind, position_event_payload(position, at, **fields)))

    def finish(kind, at, reason, value, source, email_observation=None):
        if email_observation is None:
            email_observation = {'spot': value}
        emit(kind, at, reason=reason, underlying_reference=value, source=source,
             email_observation=email_observation)
        return None, alerts, close_reference(position, at, reason, value, source), warnings

    def hit_t1(at, source, email_observation):
        old_stop = position['stop']
        entry = position['entry_spot']
        if side * (entry - old_stop) > 0:
            position.update(stop=entry, adjusted_at=at.isoformat(),
                            stop_before_adjustment=old_stop,
                            t2_before_adjustment=position['t2'])
        position.update(t1_hit=True, t1_at=at.isoformat(), remaining_pct=100-position.get('t1_exit_pct', 50))
        emit('T1', at, source=source, underlying_reference=position['t1'],
             old_stop=old_stop, new_stop=position['stop'],
             email_observation={**email_observation, 'stop': position['stop']})

    entry_minute = exact_minute(opening)
    expected = max(cursor, entry_minute) + MINUTE
    for bar in bars:
        if bar.start < expected:
            continue
        if bar.start > expected:
            warnings.append('GAP_IN_UNOBSERVED_POSITION_BARS')
            break
        at = bar_end(bar)
        if at > deadline:
            break
        adverse, favorable = (bar.low, bar.high) if side == 1 else (bar.high, bar.low)
        stop = position['stop']
        t2 = position['t2']
        if position.get('adjusted_at') and bar.start < timestamp(position['adjusted_at']):
            stop = position.get('stop_before_adjustment', stop)
            t2 = position.get('t2_before_adjustment', t2)
        candle_observation = {'spot': bar.close, 'spot_is_close': True, 'stop': stop, 't2': t2}
        if side * (adverse - stop) <= 0:
            return finish('EXIT', at, 'STRUCTURAL_SL', stop, 'COMPLETED_1M_STOP_FIRST',
                          candle_observation)
        reached_t1 = not position['t1_hit'] and side * (favorable - position['t1']) >= 0
        if reached_t1:
            hit_t1(at, 'COMPLETED_1M_HIGH_LOW', candle_observation)
            candle_observation['stop'] = position['stop']
        if position['t1_hit'] and side * (favorable - t2) >= 0:
            return finish('T2', at, 'OI_TARGET_REACHED', t2, 'COMPLETED_1M_HIGH_LOW',
                          candle_observation)
        # The new stop is active at the completed candle's timestamp. Its
        # close can trigger the stop at once, while its earlier wick cannot.
        if reached_t1 and side * (bar.close - position['stop']) <= 0:
            return finish('EXIT', at, 'STRUCTURAL_SL', bar.close, 'COMPLETED_1M_CLOSE_AFTER_T1',
                          candle_observation)
        position['last_candle'] = bar.start.isoformat()
        expected += MINUTE

    if now >= deadline:
        return finish('EXIT', now, 'SESSION_REFERENCE_EXIT', spot,
                      'FRESH_INDEX_QUOTE' if spot is not None else 'CLOCK_NO_FRESH_INDEX_QUOTE')
    stop_changed_at = position.get('adjusted_at')
    if spot is not None and (stop_changed_at is None or (spot_at or now) >= timestamp(stop_changed_at)):
        if side * (spot - position['stop']) <= 0:
            return finish('EXIT', now, 'STRUCTURAL_SL', spot, 'FRESH_INDEX_QUOTE')
        if not position['t1_hit'] and side * (spot - position['t1']) >= 0:
            hit_t1(now, 'FRESH_INDEX_QUOTE', {'spot': spot})
        if position['t1_hit'] and side * (spot - position['t2']) >= 0:
            return finish('T2', now, 'OI_TARGET_REACHED', spot, 'FRESH_INDEX_QUOTE')
    return position, alerts, None, warnings


def refine_reference(position: dict, bars: list[Candle], spot: float,
                     window: OIWindow | None, now: datetime, *,
                     session_open: datetime | None = None) -> list[tuple[str, dict]]:
    if not position['t1_hit']:
        return []
    side = 1 if position['direction'] == 'BULLISH' else -1
    atr = volatility(contiguous_tail(bars), minimum=2.5) if bars else 2.5
    old_stop, old_t2 = position['stop'], position['t2']
    if position.get('adjusted_at') and exact_minute(timestamp(position['adjusted_at'])) == exact_minute(now):
        return []
    entry = position['entry_spot']
    # An adjusted stop is effective only from this observation onward.
    # Require a live quote, safe clearance and chronology after the T1 event.
    if bars and position.get('last_candle') != bars[-1].start.isoformat():
        # Do not apply a new stop to an interval that still has missing bars.
        return []
    opening = timestamp(position['opened_at'])
    policy = position.get('stop_policy')
    continuation = (policy == 'CONFIRMED_3M_SWING'
                    or (policy is None and position.get('scenario') in CONTINUATION_SCENARIOS))
    clearance = .6 * atr
    pivot = None
    if continuation:
        # Keep the existing stop when the trade reaches T1 but the next swing
        # is still forming. A bar that straddles entry cannot set the new stop.
        proposed = old_stop
        threes = aggregate(bars, 3, session_open or day_time(opening, 9, 15))
        atr3 = volatility(threes, minimum=2.5)
        clearance = max(clearance, .30 * atr3)
        pivots = [x for x in swings(threes[-12:], side, duration=3, left=1)
                  if x.at >= exact_minute(opening) + MINUTE and x.known_at <= now]
        if pivots:
            pivot = pivots[-1]
            proposed = pivot.price - side * stop_buffer(atr, atr3)
    else:
        proposed = entry
        pivots = [x for x in swings(bars[-25:], side) if x.at >= exact_minute(opening) + MINUTE]
        if pivots:
            structural = pivots[-1].price - side * stop_buffer(atr)
            if side * (structural - entry) > 0 and side * (spot - structural) >= clearance:
                proposed = structural
    if side * (proposed - old_stop) > .10 * atr and side * (spot - proposed) >= clearance:
        position['stop'] = round(proposed, 4)

    if window:
        levels = oi_levels(window, spot, side, atr)
        objective = next_oi_objective(levels, side,
                                      max((spot, position['t1'] + side*.8*atr), key=lambda v: side*v), atr)
        if objective is not None and abs(objective - old_t2) > .4 * atr:
            # Instead of extending a target because of noise, require that the
            # old wall has weakened in the current matched OI window.
            kind = 'CE' if side == 1 else 'PE'
            old_weak = any(x.row.side == kind and abs(x.row.strike-old_t2) <= max(1, .2*atr)
                           and x.increase < -OI_LEVEL_MATERIAL_CHANGE for x in window.changes)
            if side * (objective - old_t2) < 0 or old_weak:
                position['t2'] = objective
                position['t2_source'] = 'OI_LEVEL_AFTER_T1'

    if position['stop'] == old_stop and position['t2'] == old_t2:
        return []
    position.update(adjusted_at=now.isoformat(), stop_before_adjustment=old_stop,
                    t2_before_adjustment=old_t2)
    if position['stop'] != old_stop:
        reason = 'CONFIRMED_3M_SWING_AFTER_T1' if continuation else 'AFTER_T1_REFINEMENT'
    else:
        reason = 'T2_REFINED_AFTER_T1'
    return [('ADJUST_SL', position_event_payload(
        position, now, reason=reason,
        old_stop=old_stop, new_stop=position['stop'], old_t2=old_t2, new_t2=position['t2'],
        stop_swing=price_public(pivot) if continuation and pivot and position['stop'] != old_stop else None,
        oi_snapshot_at=window.snapshot.at.isoformat() if window else None,
        email_observation={'spot': spot}))]


def prior_context(engine: dict, api, now: datetime) -> list[Candle]:
    if 'prior_ten' not in engine:
        try:
            raw = api.prior_ten(now.date())
            rows = parse_candles(raw, now)
            days = sorted({b.start.date() for b in rows if b.start.date() < now.date()})
            if not days:
                return []
            most_recent = days[-1]
            bars = [b for b in rows if b.start.date() == most_recent
                    and b.start >= day_time(b.start, 9, 15)
                    and bar_end(b, 10) <= day_time(b.start, 15, 30)
                    and (b.start - day_time(b.start, 9, 15)) % (10 * MINUTE) == timedelta(0)]
            engine['prior_ten'] = [serialize_bar(b) for b in bars]
        except (DataError, ProviderError, ValueError, TypeError, KeyError):
            return []
    return parse_candles(engine['prior_ten'], now) if engine['prior_ten'] else []


def price_history(bars: list[Candle], prior_ten: list[Candle],
                  session_open: datetime) -> tuple[PriceContext, list[Signal], list[dict]]:
    # A full causal walk makes the recovered state independent of missed
    # scheduler invocations. Observe the most recent eligible trigger window.
    previous = None
    reversals = SessionReversals()
    live: dict[str, Signal] = {}
    examined = []
    for i in range(1, len(bars)+1):
        if i > 1 and bars[i-1].start - bars[i-2].start != MINUTE:
            previous = None
            reversals = SessionReversals()
        previous, signals = market_signals(bars[:i], prior_ten, session_open, previous, reversals)
        if bar_end(bars[-1]) - previous.at <= MAX_TRIGGER_AGE:
            for signal in signals:
                live.setdefault(signal.identity, signal)
            examined.append({'at': previous.at.isoformat(), 'trend': previous.trend,
                             'protected': previous.protected, 'range': previous.range_bounds,
                             'market_state': price_public(previous.phase),
                             'signals': [price_public(s) for s in signals],
                             'watches': reversals.watches(bars[i-1].close, LEVEL_STRIKE_TOLERANCE)})
    assert previous is not None
    return previous, list(live.values()), jsonable(examined)


def defended_entry_retest(signal: Signal, bars: list[Candle], atr: float) -> bool:
    # Continuation signals with a pullback can use the test that produced their
    # trigger. A new break or resumption needs a test after it was established.
    start = signal.origin if signal.scenario in ('PULLBACK_CONTINUATION', 'FAILED_PULLBACK') else signal.at
    recent = [bar for bar in bars[-6:] if bar.start >= start]
    retest = reaction(recent, signal.side, signal.level, atr)
    if retest is None:
        return False
    test = recent[retest[0]]
    return (signal.side * (test.close - signal.level) >= -max(.6, .11 * atr)
            and signal.side * (recent[-1].close - test.close) >= .20 * atr)


@dataclass(frozen=True)
class BreakRetest:
    test_closed_at: datetime
    edge: float
    close: float
    confirmation: str


def accepted_break_retest(signal: Signal, bars: list[Candle], spot: float, atr: float,
                           allow_live_retest: bool) -> BreakRetest | None:
    if signal.reversal is None and signal.scenario not in ('ACCEPTED_BREAKOUT', 'ACCEPTED_BREAKDOWN'):
        return None
    side, trigger = signal.side, signal.trigger
    post_break = [bar for bar in bars if bar.start >= signal.at]
    if len(post_break) < 2 or any(side * (bar.close - trigger) < 0 for bar in post_break):
        return None
    # A retest needs a completed departure first. Holding the trigger from
    # the first break onward without leaving it is insufficient evidence.
    departure = next((i for i, bar in enumerate(post_break)
                      if side * (bar.close - trigger) >= .60 * atr), None)
    if departure is None:
        return None
    for i in range(len(post_break) - 1, departure, -1):
        test = post_break[i]
        edge = edge_price(test, side)
        if not -.30 * atr <= side * (edge - trigger) <= .42 * atr:
            continue
        after = post_break[i + 1:]
        if after:
            held = all(side * (edge_price(bar, side) - edge) >= -.20 * atr for bar in after)
            if held and side * (after[-1].close - test.close) >= .20 * atr:
                return BreakRetest(bar_end(test), edge, test.close, 'COMPLETED_REBOUND')
        elif allow_live_retest and side * (spot - test.close) >= max(.60, .10 * atr):
            return BreakRetest(bar_end(test), edge, test.close, 'LIVE_REBOUND_AFTER_COMPLETED_TEST')
    return None


@dataclass(frozen=True)
class EntryPriceAssessment:
    reason: str | None = None
    timing: str | None = None
    retest: BreakRetest | None = None


def price_confirmation(signal: Signal, ctx: PriceContext, bars: list[Candle], spot: float,
                       cfg: Config, *, allow_live_retest: bool = False) -> EntryPriceAssessment:
    side = signal.side
    if not bars or signal.at <= bars[0].start:
        return EntryPriceAssessment('CONTIGUOUS_TRIGGER_UNAVAILABLE')
    if signal.reversal is not None:
        if not confirmed_reversal(signal, bars):
            return EntryPriceAssessment('REVERSAL_SWING_NOT_ACCEPTED')
    else:
        # A price-only recovery signal does not authorize other entries
        # against a trend that still has a defended level.
        if ctx.trend == -side:
            return EntryPriceAssessment('OPPOSITE_PROTECTED_TREND')
        if ctx.phase.transition is not None:
            return EntryPriceAssessment(ctx.phase.reason)
    steps = directional_steps(bars, side)
    if not steps:
        return EntryPriceAssessment('THREE_MINUTE_PRICE_UNAVAILABLE')
    retest = None
    if sum(steps) < .10 * ctx.atr3:
        retest = accepted_break_retest(signal, bars, spot, ctx.atr, allow_live_retest)
        if retest is None:
            return EntryPriceAssessment('THREE_MINUTE_PRICE_NOT_ALIGNED')
    if side * (signal.trigger - signal.invalidation) <= 0:
        return EntryPriceAssessment('INVALID_STRUCTURAL_STOP')
    if side * (spot - signal.invalidation) <= 0 or any(
        side * (edge_price(bar, side) - signal.invalidation) < 0
        for bar in bars if bar.start >= signal.at
    ):
        return EntryPriceAssessment('STRUCTURE_INVALIDATED_AFTER_TRIGGER')
    extension = side * (spot - signal.trigger)
    if extension < 0:
        return EntryPriceAssessment('LIVE_PRICE_BACK_BEHIND_TRIGGER')
    if (extension > cfg.max_chase_atr * ctx.atr
            or extension > .90 * side * (signal.trigger - signal.invalidation)
            or abs(spot - bars[-1].close) > 1.7 * ctx.atr):
        return EntryPriceAssessment('ENTRY_EXTENDED')
    if (signal.reversal is None and ctx.trend == side and ctx.protected is not None
            and side * (spot - ctx.protected) > cfg.max_unretested_leg_atr * ctx.atr
            and not defended_entry_retest(signal, bars, ctx.atr)):
        return EntryPriceAssessment('EXTENDED_LEG_NEEDS_DEFENDED_RETEST')
    timing = 'DEFENDED_BREAK_RETEST' if retest is not None else 'THREE_MINUTE_IMPULSE'
    return EntryPriceAssessment(timing=timing, retest=retest)


@dataclass(frozen=True)
class EntrySetup:
    signal: Signal
    plan: RiskPlan
    oi_pair: OIPair
    stop_reference: float


@dataclass(frozen=True)
class MarketReading:
    spot: float
    spot_source: str
    grid: list[float]
    pairs: dict[float, OIPair]
    band: StrikeBand | None

    @classmethod
    def observe(cls, spot: float, source: str, contracts: list[dict], window: OIWindow | None):
        grid = listed_strikes(contracts)
        pairs = paired_oi(window)
        return cls(spot, source, grid, pairs, StrikeBand.build(grid, spot, pairs))

    def public(self, context: PriceContext, bars: list[Candle]) -> dict:
        steps = directional_steps(bars, 1)
        delta = sum(steps) if steps else None
        if delta is None:
            direction = 'UNAVAILABLE'
        elif abs(delta) < .10 * context.atr3:
            direction = 'BALANCED'
        else:
            direction = 'UP' if delta > 0 else 'DOWN'
        range_levels = context.range_bounds
        range_pairs = [found[0] for level in range_levels or ()
                       if (found := pairs_at(level, self.grid, self.pairs))]
        sideways = bool(range_levels and range_levels[0] <= self.spot <= range_levels[1]
                        and len(range_pairs) == 2 and all(pair.state == 'QUIET' for pair in range_pairs)
                        and context.phase.transition is None)
        return {'spot': self.spot, 'spot_source': self.spot_source, 'move_3m': delta,
                'atr_3m': context.atr3, 'direction_3m': direction,
                'market_state': 'SIDEWAYS' if sideways else context.phase.kind,
                'range_oi': [pair.public() for pair in range_pairs],
                'strike_band': self.band.public() if self.band is not None else None}


def signal_priority(signal: Signal) -> int:
    return {'DOUBLE_BOTTOM': 0, 'DOUBLE_TOP': 0, 'OPENING_MOMENTUM': 1,
            'FAILED_PULLBACK': 2, 'PULLBACK_CONTINUATION': 2, 'ACCEPTED_BREAKOUT': 3,
            'ACCEPTED_BREAKDOWN': 3, 'RANGE_EDGE': 4, 'TREND_RESUMPTION': 5}[signal.scenario]


def reversal_can_retire(position: dict, signal: Signal, bars: list[Candle],
                        outbox: list[dict]) -> bool:
    old_side = 1 if position['direction'] == 'BULLISH' else -1
    if (signal.reversal is None or signal.side != -old_side
            or signal.at <= timestamp(position['opened_at'])):
        return False
    level = position.get('setup_invalidation')
    if level is None:
        for event in reversed(outbox):
            details = event.get('details') or {}
            if event.get('kind') == 'ENTRY' and details.get('position_id') == position['id']:
                level = (details.get('signal') or {}).get('invalidation')
                break
    if level is None:
        level = position.get('initial_stop', position['stop'])
    return closes_through(bars, -old_side, level, 0)


def evaluate_setups(signals: list[Signal], context: PriceContext, bars: list[Candle],
                    session_open: datetime, reading: MarketReading, window: OIWindow,
                    slot: datetime, consumed: list[str], cfg: Config, *, quote_at: datetime | None = None
                    ) -> tuple[list[dict], list[EntrySetup], list[Signal]]:
    decisions: list[dict] = []
    setups: list[EntrySetup] = []
    confirmed: list[Signal] = []
    threes = aggregate(bars, 3, session_open)
    recent = contiguous_tail(bars)
    allow_live_retest = quote_at is not None and context.at == slot and quote_at > context.at
    ordered = sorted(signals, key=lambda s: (signal_priority(s), -s.at.timestamp(), s.identity))
    for signal in ordered:
        pairs = pairs_at(signal.level, reading.grid, reading.pairs, cover_strike_interval=True)
        detail = {'signal': price_public(signal), 'identity': signal.identity,
                  'paired_oi_at_level': [pair.public() for pair in pairs]}
        if pairs:
            detail['oi_anchor_distance'] = round(abs(pairs[0].strike - signal.level), 4)
        if context.trend == signal.side and context.protected is not None:
            detail['distance_from_protected_atr'] = round(
                signal.side * (reading.spot - context.protected) / context.atr, 4)
        decisions.append(detail)
        if signal.identity in consumed:
            detail['reason'] = 'SIGNAL_ALREADY_USED'
            continue
        if not timedelta(0) <= slot - signal.at <= MAX_TRIGGER_AGE:
            detail['reason'] = 'PRICE_TRIGGER_EXPIRED'
            continue
        price_check = price_confirmation(signal, context, recent, reading.spot, cfg,
                                         allow_live_retest=allow_live_retest)
        if price_check.reason is not None:
            detail['reason'] = price_check.reason
            continue
        detail['entry_timing'] = price_check.timing
        if price_check.retest is not None:
            detail['retest'] = price_public(price_check.retest)
        if not pairs:
            detail['reason'] = 'NO_STRIKE_NEAR_TRIGGER_LEVEL'
            continue
        # For a price zone use its nearest listed strike; never substitute
        # a distant supportive pair for a quiet or opposing pair on the level.
        pair = pairs[0]
        expected = 'BULLISH' if signal.side == 1 else 'BEARISH'
        if pair.state != expected:
            detail['reason'] = {'MISSING': 'PAIRED_OI_UNAVAILABLE',
                                'QUIET': 'PAIRED_OI_UNDER_2_PERCENT'}.get(
                                    pair.state, 'PAIRED_OI_DIRECTION_MISMATCH')
            continue
        confirmed.append(signal)
        reference = next((bar for bar in reversed(threes)
                          if bar_end(bar, 3) <= signal.at - MINUTE), None)
        if reference is None:
            detail['reason'] = 'PREVIOUS_3M_CLOSE_UNAVAILABLE'
            continue
        levels = oi_levels(window, reading.spot, signal.side, context.atr)
        risk = risk_plan(signal, context, levels, reading.spot, cfg, reference.close,
                         pairs=reading.pairs, bars=recent)
        detail.update(reason=risk.reason, stop_reference_3m=reference.close, risk_evidence=risk.evidence)
        if risk.plan is not None:
            detail['plan'] = asdict(risk.plan)
            setups.append(EntrySetup(signal, risk.plan, pair, reference.close))
    return decisions, setups, confirmed


def scan(state: dict, api, cfg: Config, clock_fn=None,
         clock_sink: list | None = None) -> tuple[dict, list[str]]:
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
    result = {'version': VERSION, 'at': now.isoformat(), 'session_date': now.date().isoformat(),
              'decision': 'NO_TRADE', 'reason': 'UNSET', 'alerts_created': [],
              'position_locked': bool(active), 'evaluations': []}

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
            state['history'] = (state['history'] + [closed])[-cfg.max_state_history:]
            state['last_exit'] = {'at': closed['closed_at'],
                                  'direction': closed['direction'], 'id': closed['id']}
        state['position'] = position
        result['position_locked'] = position is not None
        result['decision'] = 'POSITION_CLOSED' if closed else 'POSITION_OPEN'
        result['reason'] = closed['exit_reason'] if closed else 'REFERENCE_POSITION_MANAGED'

    deadline = day_time(now, *HARD_EXIT)
    if active and timestamp(active['opened_at']).date() < now.date():
        cutoff = day_time(timestamp(active['opened_at']), *HARD_EXIT)
        closed = close_reference(active, cutoff, 'PRIOR_SESSION_REFERENCE_EXPIRED', None,
                                 'CLOCK_NO_PRIOR_SESSION_FILL')
        event = ('EXIT', position_event_payload(active, now, reason=closed['exit_reason'],
                                               effective_at=cutoff.isoformat(), source=closed['exit_source']))
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
            save_position(*manage_reference(active, [], None, now, deadline, cfg), at=now)
            return result, times
        if active:
            result['decision'] = 'POSITION_MONITORING_UNAVAILABLE'
        return no_trade('NO_VERIFIED_NFO_SESSION')
    session_open, session_close = session
    deadline = min(deadline, session_close)
    price = ClosedPrice([])
    if engine.get('closed_candles'):
        try:
            price = merge_closed_price(price, engine['closed_candles'], now, session, cfg)
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
                if not any(s['through'] == slot.isoformat() and s['expiry'] == expiry for s in ring):
                    ring.append(price_public(sample))
                engine['oi_samples'] = ring[-8:]
                result['oi'] = {'status': 'MATCHED' if window else 'OI_WINDOW_UNAVAILABLE',
                                'at': now.isoformat(), 'through': slot.isoformat(),
                                'candle_through_at_capture': price.through.isoformat() if price.through else None,
                                'expiry': expiry,
                                'baseline': window.baseline.isoformat() if window else None,
                                'matched_contracts': len(window.changes) if window else 0}
        except (DataError, ProviderError, ValueError, KeyError, TypeError) as exc:
            now = clock()
            result['oi'] = {'status': 'OPTION_CHAIN_UNAVAILABLE', 'reason': str(exc)}

    if window is None:
        slot = price_slot(now)
    repolled = False
    slot_ends = slot + MINUTE + timedelta(seconds=cfg.feed_grace_seconds)
    if (price.through != slot and price_slot(now) == slot
            and now + CANDLE_REFRESH_REQUEST_BUDGET < min(slot_ends, deadline)):
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

    quotes: dict = {}
    index_spot = None
    quote_time = None
    try:
        quotes = api.quotes([INDEX])
        now = clock()
        quote = quotes.get(INDEX)
        index_spot = checked_quote(quote, now, cfg.quote_max_age_seconds)
        quote_time = timestamp(quote['timestamp'])
    except (DataError, ProviderError, KeyError) as exc:
        now = clock()
        result['quote_error'] = str(exc)

    if active is not None:
        observed = index_spot if quote_time is not None and quote_time >= timestamp(active['opened_at']) else None
        managed, events, closed, warnings = manage_reference(
            active, bars, observed, now, deadline, cfg, spot_at=quote_time)
        # The T1 alert already contains the initial adjustment. Further
        # trailing and target refinement can resume on a subsequent scan.
        if (managed is not None and active.get('t1_hit', False) and observed is not None
                and price.covers_entry(price_slot(now)) and now < deadline):
            events.extend(refine_reference(managed, bars, observed, window, now,
                                            session_open=session_open))
        save_position(managed, events, closed, warnings, at=now)
        if managed is not None and observed is None and not bars:
            result.update(decision='POSITION_MONITORING_UNAVAILABLE', reason='PRICE_FEED_UNAVAILABLE')

    if not bars:
        return no_trade('NO_COMPLETED_SESSION_CANDLES')
    prior_ten = prior_context(engine, api, now)
    now = clock()
    context, signals, recent = price_history(bars, prior_ten, session_open)
    spot = index_spot if index_spot is not None else bars[-1].close
    reading = MarketReading.observe(spot, 'INDEX_QUOTE' if index_spot is not None else 'CANDLE_CLOSE',
                                    contracts, window)
    result['price'] = {'as_of': context.at.isoformat(), 'atr_1m': context.atr, 'atr_3m': context.atr3,
                       'atr_10m': context.atr10, 'trend': context.trend, 'protected': context.protected,
                       'range': context.range_bounds, 'market_state': price_public(context.phase),
                       'observations': recent}
    assessment = reading.public(context, bars)
    watches = list(recent[-1]['watches'])
    tracked_levels = (
        ('PROTECTED_STRUCTURE', context.protected),
        ('REVERSAL_STRUCTURE', context.recovery_level),
        ('POSITION_ENTRY_LEVEL', active.get('setup_level') if active else None),
    )
    if active:
        tracked_levels += tuple(('POSITION_TARGET_CHECKPOINT', level)
                                for level in active.get('target_checkpoints', ()))
    for source, level in tracked_levels:
        if level is not None and all(watch['level'] != level for watch in watches):
            watches.append({'level': level, 'source': source})
    assessment['watched_levels'] = [
        {**watch, 'paired_oi': [pair.public() for pair in pairs_at(watch['level'], reading.grid, reading.pairs)]}
        for watch in watches
    ]
    result['market_assessment'] = assessment

    if now < max(day_time(now, *ENTRY_START), session_open + 6 * MINUTE):
        return no_trade('COLLECTING_OPENING_BASELINE')
    if not price.covers_entry(entry_slot):
        return no_trade('CLOSED_PRICE_TOO_OLD_FOR_ENTRY')
    if price.tail_size < 6:
        return no_trade('INSUFFICIENT_CONTIGUOUS_PRICE_HISTORY')
    if window is None:
        return no_trade('OI_WINDOW_UNAVAILABLE')
    if price_slot(now) != entry_slot:
        return no_trade('PRICE_WINDOW_ROLLED_DURING_SNAPSHOT')
    if quote_time is None or quote_time < entry_slot:
        return no_trade('INDEX_QUOTE_UNAVAILABLE_FOR_ENTRY')
    if reading.band is None:
        return no_trade('ATM_STRIKE_BAND_UNAVAILABLE')

    result['entry_evidence'] = {'index_quote_at': quote_time.isoformat(), 'index_quote': spot,
                                'decision_through': entry_slot.isoformat(), 'candle_through': through.isoformat(),
                                'candle_lag_minutes': (entry_slot - through) // MINUTE}
    consumed = engine['consumed_signals']
    decisions, setups, confirmed = evaluate_setups(
        signals, context, bars, session_open, reading, window, entry_slot, consumed, cfg, quote_at=quote_time)
    result['evaluations'] = decisions
    if assessment['market_state'] == 'SIDEWAYS':
        return no_trade('SIDEWAYS_NO_DIRECTIONAL_ENTRY')

    position = state.get('position')
    if position is not None:
        reversal = next((signal for signal in confirmed
                         if reversal_can_retire(position, signal, bars, state['outbox'])), None)
        if reversal is None:
            return no_trade('EXISTING_POSITION_REMAINS_VALID')
        rotated = close_reference(position, now, 'CONFIRMED_ZONE_REVERSAL', spot, 'FRESH_PRICE_AND_PAIRED_OI')
        exit_details = position_event_payload(
            position, now, reason=rotated['exit_reason'], underlying_reference=spot,
            source=rotated['exit_source'], signal=price_public(reversal))
        save_position(None, [('EXIT', exit_details)], rotated, result.get('management_warnings', []), at=now)
        result['rotated_from'] = position['id']
        setups = [setup for setup in setups if setup.signal.identity == reversal.identity]

    last_entry = min(day_time(now, *ENTRY_END), deadline - 10 * MINUTE)
    if now >= last_entry:
        return no_trade('OUTSIDE_ENTRY_WINDOW')
    if engine.get('last_entry_through') == through.isoformat():
        return no_trade('SIGNAL_WINDOW_ALREADY_USED')
    if not setups:
        return no_trade('NO_QUALIFIED_PRICE_OI_AND_RISK_SETUP' if signals else 'NO_FRESH_PRICE_TRIGGER')
    if len({setup.signal.side for setup in setups}) != 1:
        return no_trade('CONFLICTING_QUALIFIED_DIRECTIONS')

    # Evaluate the market before deciding if a same-side re-entry is allowed.
    setup = setups[0]
    signal, plan = setup.signal, setup.plan
    direction = 'BULLISH' if signal.side == 1 else 'BEARISH'
    last_exit = state.get('last_exit')
    if (last_exit and last_exit['direction'] == direction
            and now - timestamp(last_exit['at']) < cfg.cooldown_minutes * MINUTE):
        return no_trade('SAME_DIRECTION_POST_EXIT_COOLDOWN')

    option_side = 'CE' if signal.side == 1 else 'PE'
    listed = {(row['instrument_type'], float(row['strike_price'])): row for row in contracts}
    choices = []
    for offset in (-signal.side, -2 * signal.side):
        pair = reading.band.pairs.get(offset)
        if pair is None:
            continue
        row = listed.get((option_side, pair.strike))
        if row is not None:
            choices.append((offset, pair, row))
    if not choices:
        return no_trade('DIRECTIONAL_OFFSETS_NOT_LISTED')
    try:
        option_quotes = api.quotes([INDEX, *(row['instrument_key'] for _, _, row in choices)])
        now = clock()
        final_index = option_quotes.get(INDEX)
        final_spot = checked_quote(final_index, now, cfg.quote_max_age_seconds)
        final_quote_time = timestamp(final_index['timestamp'])
    except (DataError, ProviderError, KeyError) as exc:
        result['option_quote_error'] = str(exc)
        return no_trade('ENTRY_QUOTE_REQUEST_FAILED')
    if now >= last_entry or price_slot(now) != entry_slot or final_quote_time < entry_slot:
        return no_trade('DECISION_WINDOW_EXPIRED_DURING_QUOTE_FETCH')

    final_reading = MarketReading.observe(final_spot, 'INDEX_QUOTE', contracts, window)
    if final_reading.band is None or final_reading.band.atm != reading.band.atm:
        return no_trade('ATM_CHANGED_BEFORE_EXECUTION')
    spot, quote_time = final_spot, final_quote_time
    final_checks, executable, _ = evaluate_setups(
        [item.signal for item in setups], context, bars, session_open, final_reading,
        window, entry_slot, consumed, cfg, quote_at=quote_time)
    if not executable:
        result['final_risk_checks'] = final_checks
        return no_trade(final_checks[0]['reason'])
    setup = executable[0]
    signal, plan = setup.signal, setup.plan
    final_check = next(check for check in final_checks
                       if check['identity'] == signal.identity and check['reason'] == 'QUALIFIED')
    final_evidence = final_check['risk_evidence']
    result['final_risk_evidence'] = final_evidence
    result['entry_evidence'].update(index_quote_at=quote_time.isoformat(), index_quote=spot,
                                    entry_timing=final_check['entry_timing'])
    if 'retest' in final_check:
        result['entry_evidence']['retest'] = final_check['retest']

    ranked = []
    result['contract_checks'] = []
    for offset, pair, row in choices:
        key = row['instrument_key']
        try:
            contract = live_contract(row, option_quotes.get(key), now, quote_time, reading.band, offset, cfg)
        except (DataError, KeyError, ValueError, TypeError) as exc:
            result['contract_checks'].append({'strike': pair.strike, 'reason': str(exc)})
            continue
        score = pair.score(signal.side)
        result['contract_checks'].append({'strike': pair.strike, 'reason': 'QUALIFIED_QUOTE',
                                          'oi_state': pair.state, 'directional_oi_score': score})
        ranked.append((pair.state != direction, score is None, -(score or 0),
                       contract['spread_pct'], -contract['depth_lots'], abs(offset), key, contract))
    if not ranked:
        if not any(row['instrument_key'] in option_quotes for _, _, row in choices):
            return no_trade('DIRECTIONAL_OPTION_QUOTES_UNAVAILABLE')
        return no_trade('NO_LIQUID_CONTRACT_IN_DIRECTIONAL_OFFSETS')

    *_, key, contract = min(ranked, key=lambda item: item[:-1])
    position_id = hashlib.sha256(f'{now.date()}|{signal.identity}|{key}'.encode()).hexdigest()[:22]
    position = {'id': position_id, 'status': 'OPEN', 'direction': direction,
                'side': contract['side'], 'strike': contract['strike'], 'expiry': contract['expiry'],
                'instrument_key': key, 'opened_at': now.isoformat(), 'entry_spot': spot,
                'entry_ask': contract['ask'], 'initial_stop': plan.stop,
                'setup_level': signal.level, 'setup_invalidation': signal.invalidation,
                'target_checkpoints': final_evidence['intermediate_levels'],
                'last_candle': bars[-1].start.isoformat(), 'scenario': signal.scenario,
                't1_hit': False, 'remaining_pct': 100, 'contract': contract, **asdict(plan)}
    state['position'] = position
    engine['last_entry_through'] = through.isoformat()
    engine['consumed_signals'] = (consumed + [item.signal.identity for item in setups])[-160:]
    event_id = new_event(state, 'ENTRY', position_event_payload(
        position, now, reason='QUALIFIED_PRICE_AND_3M_OI', signal=price_public(signal),
        plan=asdict(plan), entry_evidence=result['entry_evidence'], risk_evidence=final_evidence,
        oi={'window': result['oi'], 'confirmation_pair': setup.oi_pair.public(),
            'stop_reference_3m': setup.stop_reference, 'contract': contract}), now)
    result['alerts_created'].append(event_id)
    result.update(decision='ENTRY', reason='QUALIFIED_' + contract['side'],
                  position_locked=True, selected_position=position)
    return result, times


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
    for value in (details.get('effective_at'), details.get('observed_at'), event.get('created_at')):
        try:
            event_time = timestamp(value)
            break
        except DataError:
            continue
    short_time = event_time.strftime('%I:%M %p').lstrip('0') if event_time else 'Unavailable'
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
        status = 'T2 updated' if reason == 'T2_REFINED_AFTER_T1' else 'SL adjusted'
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
    if kind == 'T1' and details.get('old_stop') is not None and details.get('new_stop') is not None:
        previous = email_price(details['old_stop'], ',.4f')
        updated = email_price(details['new_stop'], ',.4f')
        if details['old_stop'] == details['new_stop']:
            fields.append(f'SL retained for remaining position: {updated}')
        else:
            fields.append(f'SL adjustment for remaining position: {previous} -> {updated}')
    fields.extend((
        f'Status: {status}',
        f'Timestamp: {full_time}',
    ))
    return subject, '\n'.join(fields)


def arm_delivery(state:dict,token:str,now:datetime) -> int:
    if not token:raise ScannerError('Notification claim token required')
    count=0
    for e in state['outbox']:
        if e.get('kind') in ALERT_KINDS and e.get('status')=='CLAIMED' and e.get('claim')==token:
            # MUST be COMMITTED and PUSHED before the first SMTP socket.
            e.update(status='DELIVERY_UNCERTAIN',attempted_at=now.isoformat(),
                     smtp_stage='ARMED_NO_NETWORK')
            count+=1
    return count


def deliver_armed(state:dict,path:Path,token:str) -> int:
    if not token:raise ScannerError('NOTIFICATION_CLAIM_TOKEN required')
    pending=[x for x in state['outbox'] if x.get('status')=='DELIVERY_UNCERTAIN'
             and x.get('smtp_stage')=='ARMED_NO_NETWORK' and x.get('claim')==token
             and x.get('kind') in ALERT_KINDS]
    if not pending:return 0
    sender=os.environ.get('EMAIL_SENDER','')
    receiver=os.environ.get('EMAIL_RECEIVER','')
    password=os.environ.get('EMAIL_PASSWORD','')
    username=os.environ.get('EMAIL_USERNAME') or sender
    host=os.environ.get('SMTP_HOST','smtp.gmail.com')
    port=int(os.environ.get('SMTP_PORT','465'))
    if not (sender and receiver and password and username):
        raise ScannerError('SMTP secrets missing; claims remain safe and undelivered')
    unknown=False
    for e in pending:
        title,body=mail_content(e)
        m=EmailMessage()
        m['From']=sender;m['To']=receiver;m['Subject']=title
        m['Message-ID']='<'+e['id']+'@'+sender.rsplit('@',1)[-1]+'>'
        m.set_content(body)
        # Remote state was already ARMED and committed by the workflow.
        # Update local state to record execution; no automatic retry after crash.
        e.update(smtp_stage='LOCAL_SEND_STARTED')
        save_state(path,state)
        try:
            with smtplib.SMTP_SSL(host,port,timeout=20,context=ssl.create_default_context()) as client:
                e['smtp_stage']='AUTHENTICATE'
                client.login(username,password)
                e['smtp_stage']='SEND'
                client.send_message(m)
            e.update(status='SENT',sent_at=datetime.now(IST).isoformat(),smtp_stage='ACCEPTED_BY_SMTP')
        except (OSError,smtplib.SMTPException) as exc:
            e.update(status='DELIVERY_UNCERTAIN',smtp_error_type=type(exc).__name__)
            unknown=True
        save_state(path,state)
    return 1 if unknown else 0


def paths() -> tuple[Path,Path]:
    return Path(os.environ.get('STATE_FILE','state/market_state_v120_3.json')),Path(os.environ.get('AUDIT_DIR','audit'))


def environment_config() -> Config:
    try:raw=json.loads((os.environ.get('NIFTY_SCANNER_CONFIG') or '{}'))
    except json.JSONDecodeError as exc:raise ScannerError('Invalid NIFTY_SCANNER_CONFIG JSON') from exc
    if not isinstance(raw,dict):raise ScannerError('Configuration must be JSON object')
    for legacy in ('oi_entry_floor_bps', 'oi_entry_ceiling_bps'):
        raw.pop(legacy, None)
    try:return Config(**raw)
    except TypeError as exc:raise ScannerError('Unknown scanner configuration fields') from exc


def recorded_scan(state:dict,provider, cfg:Config, audit_dir:Path,token:str, replay_clock=None,
                  capture=True) -> dict:
    actor=RecordingProvider(provider) if capture else provider
    before=json.dumps(state,sort_keys=True,allow_nan=False,separators=(',',':'))
    before_hash=hashlib.sha256(before.encode()).hexdigest()
    observations=[]
    clock=None
    if replay_clock is not None:
        itr=iter(replay_clock)
        def clock():
            try:return timestamp(next(itr))
            except StopIteration as exc:raise ScannerError('REPLAY_CLOCK_SAMPLES_EXHAUSTED') from exc
    failure=None
    try:
        result,_=scan(state,actor,cfg,clock_fn=clock,clock_sink=observations)
    except (ScannerError,DataError,ProviderError,KeyError,ValueError,TypeError,IndexError,OverflowError) as exc:
        failure=exc
        result={'version':VERSION,'decision':'ERROR','reason':type(exc).__name__,
                'detail':str(exc),'at':datetime.now(IST).isoformat(),
                'position_locked':bool(state.get('position'))}
    now=datetime.now(IST) if not observations else timestamp(observations[0])
    scan_state_hash=hashlib.sha256(json.dumps(state,sort_keys=True,allow_nan=False,
                               separators=(',',':')).encode()).hexdigest()
    # Even on upstream failure, preserve the open position and all queued
    # lifecycle events; never regenerate a missing state from scratch.
    claim_outbox(state,token,now)
    event={'event':'SCAN','at':now.isoformat(),'version':VERSION,
           'before_state_sha256':before_hash,'result':result,
           'alerts_pending':[x['id'] for x in state['outbox'] if x.get('status')=='CLAIMED' and x.get('claim')==token]}
    if capture:
        raw={'version':VERSION,'scan_started_at':now.isoformat(),'clock_samples':observations,
             'calls':actor.calls,'config':asdict(cfg),'before_state_sha256':before_hash,
             'before_state':json.loads(before), 'after_scan_state_sha256':scan_state_hash,
             'result':result,'email_observations':True,
             'source_file_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
        if cfg.record_inputs and not (
            result.get('reason') in ('AFTER_SESSION_EXIT_CUTOFF', 'NO_VERIFIED_NFO_SESSION',
                                     'BEFORE_FIRST_OI_BASELINE')
            and not result.get('position_locked')
        ):
            session_date=now.date().isoformat()
            run_id=os.environ.get('GITHUB_RUN_ID','local')+'-'+os.environ.get('GITHUB_RUN_ATTEMPT','1')
            captured_at=now.strftime('%H%M%S-%f')
            safe=''.join(x if x.isalnum() or x in '-_' else '_' for x in run_id)
            file=audit_dir/('inputs_'+AUDIT_RELEASE)/session_date/(captured_at+'-'+safe+'.json.gz')
            record_inputs(file,raw)
            event['input_recording']=str(file)
    if result.get('reason') != 'AFTER_SESSION_EXIT_CUTOFF' or event['alerts_pending']:
        append_audit(audit_dir/(f'market_scan_{AUDIT_RELEASE}_{now.date().isoformat()}.jsonl'), event)
    if failure:
        result['audit_recorded']=True
    return result


def replay_recordings(directory:Path, cfg:Config, output:Path) -> int:
    """Replay recordings produced by this release.

    Mismatched API call sequences fail rather than silently substituting a
    future price, date, quote, or contract not captured at that decision time.
    """
    files=sorted(directory.rglob('*.json.gz'))
    if not files:raise ScannerError('NO_CAPTURED_INPUTS_FOUND_FOR_'+AUDIT_RELEASE.upper())
    records=[]
    last_at=None
    for file in files:
        try:
            with gzip.open(file,'rt',encoding='utf-8') as f:r=json.load(f)
            if r.get('version')!=VERSION:raise ScannerError('Different recording engine version')
            if not r.get('clock_samples'):raise ScannerError('NO_CAPTURED_CLOCK_SAMPLES')
            sample=timestamp(r['clock_samples'][0])
            if last_at is not None and sample<last_at:
                raise ScannerError('CAPTURES_NOT_CHRONOLOGICAL')
            last_at=sample
            # Every invocation replays its EXACT saved pre-scan state. This
            # prevents synthetic paper-flat positions from polluting historical
            # decisions and preserves open-position locks from earlier versions.
            s=r.get('before_state')
            if not isinstance(s,dict):raise ScannerError('PRE_SCAN_STATE_NOT_RECORDED')
            validate_state(s)
            state_hash=hashlib.sha256(json.dumps(s,sort_keys=True,allow_nan=False,
                                          separators=(',',':')).encode()).hexdigest()
            if state_hash!=r.get('before_state_sha256'):
                raise ScannerError('PRE_SCAN_STATE_SHA256_MISMATCH')
            api=ReplayProvider(r['calls'])
            clock=iter(r['clock_samples'])
            recorded_cfg = Config(**r['config']) if 'config' in r else cfg
            evaluated,_=scan(s,api,recorded_cfg,clock_fn=lambda:timestamp(next(clock)))
            if next(clock, None) is not None:
                raise ScannerError('Captured clock samples were not all consumed')
            if api.index!=len(api.calls):
                raise ScannerError('Captured calls not all consumed; replay not equivalent')
            if not r.get('email_observations'):
                # Older v128 captures predate the optional email-only facts.
                for event in s['outbox']:
                    event.pop('email_observation', None)
            new_hash=hashlib.sha256(json.dumps(s,sort_keys=True,allow_nan=False,
                                            separators=(',',':')).encode()).hexdigest()
            matching=(jsonable(evaluated)==r.get('result') and new_hash==r.get('after_scan_state_sha256'))
            records.append({'file':str(file),'as_of':sample.isoformat(),
                            'decision':evaluated.get('decision'),'reason':evaluated.get('reason'),
                            'expected_decision':r.get('result',{}).get('decision'),
                            'matches_original_decision':matching,
                            'pre_state_sha256_verified':True,
                            'post_state_sha256_verified':new_hash==r.get('after_scan_state_sha256'),
                            'position_locked':bool(s.get('position'))})
        except (ScannerError,DataError,ProviderError,KeyError,ValueError,TypeError,StopIteration) as exc:
            records.append({'file':str(file),'status':'REPLAY_INCOMPLETE','error':str(exc)})
            break
    report={'engine':VERSION,'recordings':len(files),'processed':len(records),
            'unverified_original_market_history':True,
            'replay_is_not_proof_of_live_fill_or_profitability':True,'records':records}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(report,indent=2,allow_nan=False),encoding='utf-8')
    print(json.dumps({'status':'REPLAY_COMPLETE' if all('status' not in x for x in records) else 'REPLAY_INCOMPLETE',
                      'report':str(output),'processed':len(records),'total':len(files)}))
    return 0 if all(x.get('matches_original_decision') for x in records) and len(records)==len(files) else 1


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    action=parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--version',action='store_true')
    action.add_argument('--initialize-flat',action='store_true')
    action.add_argument('--scan-and-claim',action='store_true')
    action.add_argument('--arm-delivery',action='store_true')
    action.add_argument('--deliver-armed',action='store_true')
    action.add_argument('--reconcile-flat',metavar='POSITION_ID')
    action.add_argument('--requeue-alert',metavar='ALERT_ID')
    action.add_argument('--migrate-state',metavar='SOURCE')
    action.add_argument('--replay-recordings',metavar='DIR', help=f'Replay recorded {AUDIT_RELEASE} price and OI inputs')
    parser.add_argument('--replay-report',default=f'audit/replay_{AUDIT_RELEASE}.json')
    args=parser.parse_args(argv)
    if args.version:print(VERSION);return 0
    try:
        cfg=environment_config()
        if args.replay_recordings:
            return replay_recordings(Path(args.replay_recordings),cfg,Path(args.replay_report))
        state_path,audit_dir=paths()
        token=os.environ.get('NOTIFICATION_CLAIM_TOKEN','')
        with local_lock(state_path):
            if args.initialize_flat:
                if os.environ.get('MANUAL_FLAT_CONFIRMED')!='1':raise ScannerError('MANUAL_FLAT_CONFIRMED=1 required')
                if state_path.exists():raise ScannerError('REFUSING_TO_OVERWRITE_EXISTING_STATE')
                save_state(state_path,starting_state(datetime.now(IST)))
                print(json.dumps({'status':'INITIALIZED_FLAT_REFERENCE_ONLY'}));return 0
            if args.migrate_state:
                if state_path.exists():raise ScannerError('Destination exists; no overwrites')
                src=Path(args.migrate_state)
                state=load_state(src)
                ensure_engine(state,datetime.now(IST))
                save_state(state_path,state)
                print(json.dumps({'status':'MIGRATED_NONDESTRUCTIVE','position_locked':bool(state.get('position'))}));return 0
            state=load_state(state_path)
            if args.reconcile_flat:
                if os.environ.get('MANUAL_FLAT_CONFIRMED')!='1':raise ScannerError('Operator must verify broker/alerts flat')
                p=state.get('position')
                if not p or p['id']!=args.reconcile_flat:raise ScannerError('Position ID does not match active lock')
                closed=dict(p,status='CLOSED',closed_at=datetime.now(IST).isoformat(),
                            exit_reason='OPERATOR_VERIFIED_FLAT_UNKNOWN_FILL',fill_confirmed=False)
                state['history'].append(closed);state['position']=None
                state['last_exit']={'at':closed['closed_at'],'direction':closed['direction'],'id':closed['id']}
                save_state(state_path,state)
                append_audit(audit_dir/(f'market_scan_{AUDIT_RELEASE}_{datetime.now(IST).date().isoformat()}.jsonl'),
                             {'event':'MANUAL_RECONCILIATION','position_id':p['id'],'at':closed['closed_at']})
                print(json.dumps({'status':'REFERENCE_LOCK_RECONCILED','position_id':p['id']}));return 0
            if args.requeue_alert:
                if os.environ.get('MANUAL_ALERT_UNDELIVERED_CONFIRMED')!='1':
                    raise ScannerError('Explicit verified mailbox non-delivery confirmation required')
                event=next((x for x in state['outbox'] if x['id']==args.requeue_alert),None)
                if not event or event.get('kind') not in ALERT_KINDS or event.get('status') not in ('CLAIMED','DELIVERY_UNCERTAIN'):
                    raise ScannerError('Alert not eligible for verified manual retry')
                event.update(status='PENDING',claim=None,manually_requeued_at=datetime.now(IST).isoformat())
                event.pop('attempted_at',None)
                save_state(state_path,state)
                print(json.dumps({'status':'MANUALLY_REQUEUED','event_id':event['id']}));return 0
            if args.arm_delivery:
                count=arm_delivery(state,token,datetime.now(IST))
                save_state(state_path,state)
                print(json.dumps({'status':'DELIVERY_ARMED','count':count}));return 0
            if args.deliver_armed:
                return deliver_armed(state,state_path,token)
            if not token:raise ScannerError('NOTIFICATION_CLAIM_TOKEN missing')
            api=Upstox(os.environ.get('UPSTOX_ANALYTICS_TOKEN',''))
            result=recorded_scan(state,api,cfg,audit_dir,token)
            save_state(state_path,state)
            print(json.dumps(result,sort_keys=True,allow_nan=False))
            return 1 if result['decision'] in ('ERROR','POSITION_MONITORING_UNAVAILABLE') else 0
    except (ScannerError,OSError,ValueError,TypeError,BlockingIOError) as exc:
        print(json.dumps({'status':'ERROR','reason':type(exc).__name__,'detail':str(exc)},allow_nan=False),file=sys.stderr)
        return 1

if __name__=='__main__':
    raise SystemExit(main())
