#!/usr/bin/env python3
"""NIFTY scanner v126.0.0. Reference alerts using completed price and OI windows.

Production runs require Upstox market data and the existing dispatcher. Keep the
existing state path and deploy this Python file and its workflow together. The
durable outbox retains position and delivery identity across workflow reruns.

The supplied OHLC workbooks support historical price validation. They contain
no option OI snapshots or quotes. Exact historical strike decisions need
timestamped option captures. The 1.80%–2.00% entry band is a strategy rule.
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

VERSION = '126.0.0'
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
            c = Candle(start,*(read_number(row[i],f'candle_{i}',positive=True) for i in range(1,5)),
                       read_number(row[5], 'volume',nonnegative=True) if len(row)>5 else 0.0)
        except (DataError,TypeError) as exc:
            raise DataError('Invalid OHLC row') from exc
        if c.start + timedelta(minutes=1) > now - timedelta(seconds=1):
            continue
        if c.start in unique and c != unique[c.start]:
            raise DataError('Conflicting duplicate candles')
        unique[c.start] = c
    ordered = sorted(unique.values(), key=lambda c:c.start)
    if not ordered:
        raise DataError('No completed candles')
    return ordered


def contiguous_tail(bars: list[Candle]) -> list[Candle]:
    start = len(bars)-1
    while start and bars[start].start-bars[start-1].start == timedelta(minutes=1):
        start -= 1
    return bars[start:] if bars else []


def volatility(bars: list[Candle], n=14, minimum=3.0) -> float:
    window=bars[-(n+1):]
    if len(window)<3:
        return minimum
    tr = [max(b.high-b.low, abs(b.high-a.close), abs(b.low-a.close)) for a,b in zip(window,window[1:])]
    return max(minimum, sum(tr)/len(tr))




@dataclass(frozen=True)
class Config:
    oi_entry_floor_bps: int = 180
    oi_entry_ceiling_bps: int = 200
    oi_jitter_seconds: int = 35
    feed_grace_seconds: float = 2.0
    quote_max_age_seconds: int = 35
    quote_max_skew_seconds: int = 12
    min_stop_atr: float = 0.7
    max_stop_atr: float = 4.5
    max_chase_atr: float = 1.25
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
        for name in ('oi_entry_floor_bps', 'oi_entry_ceiling_bps', 'oi_jitter_seconds',
                     'quote_max_age_seconds', 'quote_max_skew_seconds',
                     'cooldown_minutes', 'max_state_history'):
            if type(getattr(self, name)) is not int:
                raise DataError(name + ' must be an integer')
        if not (self.oi_jitter_seconds < 60 and self.feed_grace_seconds < 15
                and self.min_stop_atr < self.max_stop_atr and self.min_reward_risk >= 1
                and self.quote_max_skew_seconds <= self.quote_max_age_seconds):
            raise DataError('Inconsistent configuration')
        if not 180 <= self.oi_entry_floor_bps <= self.oi_entry_ceiling_bps <= 200:
            raise DataError('OI entry bounds must be ordered within 180–200 basis points')


MINUTE = timedelta(minutes=1)
OI_MINUTES = 3
# Separate from strike eligibility. Used when judging changes in the OI map.
OI_LEVEL_MATERIAL_CHANGE = .02
CONTINUATION_SCENARIOS = frozenset({'FAILED_PULLBACK', 'PULLBACK_CONTINUATION', 'TREND_RESUMPTION',
                                    'ACCEPTED_BREAKOUT', 'ACCEPTED_BREAKDOWN', 'OPENING_MOMENTUM'})


def bar_end(bar: Candle, duration: int = 1) -> datetime:
    return bar.start + duration * MINUTE


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


def reversal_pressure(bars: list[Candle], side: int, atr: float) -> bool:
    steps = directional_steps(bars, side)
    if not steps:
        return False
    return (sum(step > 0 for step in steps) >= 2 and steps[-1] > 0
            and sum(steps) >= max(.50 * atr, .65 * sum(abs(step) for step in steps)))


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


@dataclass
class PriceSweep:
    testing: Candle
    side: int
    level: float
    recovery: float | None = None
    last_retest: float | None = None


def edge_price(bar: Candle, side: int) -> float:
    return bar.low if side == 1 else bar.high


def away_price(bar: Candle, side: int) -> float:
    return bar.high if side == 1 else bar.low


class SessionReversals:
    """Causal session ledger. A zone survives until two closes accept its break."""

    def __init__(self):
        self.zones: dict[int, list[SessionZone]] = {1: [], -1: []}
        self.sweeps: dict[int, PriceSweep] = {}
        self.pending: list[PendingReversal] = []
        self.last: datetime | None = None

    def advance(self, bars: list[Candle], atr: float) -> list[Signal]:
        current = bars[-1]
        if self.last is not None and current.start != self.last + MINUTE:
            raise DataError('Reversal ledger requires contiguous minute candles')
        self.last = current.start
        if len(bars) < 4:
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
            if (now - setup.second.confirmed > 7 * MINUTE
                    or side * (edge_price(current, side) - setup.invalidation) < -.18 * atr):
                continue
            if side * (current.close - setup.trigger) < 0:
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
        for side in (1, -1):
            recovery = self._advance_sweep(bars, side, atr)
            if recovery is not None:
                signals.append(recovery)
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
        matches = sorted(
            (z for z in self.zones[side] if z.invalidated_at is None
             and abs(z.anchor - test_edge) <= min(z.width, max(2., 1.02 * atr))),
            key=lambda z: (abs(z.anchor - test_edge), z.tests[0].start),
        )
        if not matches:
            self.zones[side].append(SessionZone(side, test_edge, max(2., 1.02 * atr), [test]))
            return

        independent = []
        for zone in matches:
            for prior in reversed(zone.tests):
                if tested.start - prior.start < 2 * MINUTE:
                    continue
                between = [b for b in bars if prior.start < b.start < tested.start]
                if not between:
                    continue
                inside_move = max(side * away_price(b, side) for b in between)
                departure = inside_move - max(side * prior.extreme, side * test_edge)
                closed_reaction = max(side * (b.close - prior.extreme) for b in between)
                if departure >= .53 * atr and closed_reaction >= .30 * atr:
                    score = departure - .15 * abs(prior.extreme - test_edge)
                    independent.append((score, prior, zone, inside_move))
        if not independent:
            return
        _, prior, zone, inside_move = max(independent, key=lambda row: (row[0], row[1].start))
        separation = tested.start - prior.start
        # Keep the established zone fixed. A later test cannot drag it from
        # one swing to the next. The recent test owns risk once a new leg starts.
        zone.tests.append(test)
        if separation <= 8 * MINUTE:
            neck = inside_move
            stop = side * min(side * prior.extreme, side * test_edge)
        else:
            neck = max(side * away_price(pre, side), side * away_price(tested, side))
            stop = test_edge
        trigger = side * (neck + max(.6, .11 * atr))
        self.pending = [x for x in self.pending
                        if not (x.side == side and abs(x.level - zone.anchor) <= zone.width)]
        self.pending.append(PendingReversal(side, prior, test, trigger, stop, zone.anchor,
                                            side * inside_move))

    def _advance_sweep(self, bars: list[Candle], side: int, atr: float) -> Signal | None:
        current = bars[-1]
        now = bar_end(current)
        high_score = side * away_price(current, side)
        test_score = side * edge_price(current, side)
        old = self.sweeps.get(side)
        if old is not None:
            origin = side * edge_price(old.testing, side)
            if current.start - old.testing.start > 10 * MINUTE or test_score <= origin:
                self.sweeps.pop(side)
                old = None
            elif old.recovery is None:
                if side * (current.close - old.level) >= .85 * atr:
                    old.recovery = high_score
            else:
                retest_close = side * (current.close - current.open)
                retrace = old.recovery - test_score
                if (retrace >= .40 * atr and test_score - origin >= .40 * atr
                        and side * (current.close - old.level) >= .50 * atr
                        and retest_close >= .22 * atr
                        and (old.last_retest is None or side * old.last_retest - test_score >= .15 * atr)
                        and side * (current.close - bars[-2].close) > 0):
                    old.last_retest = edge_price(current, side)
                    return Signal(
                        side, 'SWEEP_RETEST', now, current.start, current.close,
                        edge_price(current, side), old.level,
                        ReversalEvidence(old.testing.start, current.start,
                                         edge_price(old.testing, side), edge_price(current, side),
                                         now, 'RECLAIM_AND_DEFENDED_RETEST'),
                    )
                old.recovery = max(old.recovery, high_score)
        if old is None:
            reference = side * min(side * edge_price(b, side) for b in bars[-4:-1])
            if (side * (reference - edge_price(current, side)) >= .30 * atr
                    and side * (current.close - reference) >= .24 * atr):
                self.sweeps[side] = PriceSweep(current, side, reference)
        return None


def confirmed_reversal(signal: Signal, bars: list[Candle], atr: float) -> bool:
    if signal.scenario != 'SWEEP_RETEST':
        return reversal_pressure(bars, signal.side, atr)
    steps = directional_steps(bars, signal.side)
    return bool(steps and steps[-1] > 0 and sum(x > 0 for x in steps) >= 2
                and sum(steps) >= max(.42 * atr, .48 * sum(abs(x) for x in steps)))


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
    trend = previous.trend if previous else 0
    protected = previous.protected if previous else None
    # Preserve a session thesis across a transition only when the opening and
    # subsequent minute history are present. A recovered feed may begin in
    # the middle of an opposing pullback.
    complete_session = recent[0].start == session_open
    last_established = (previous.last_established_side or trend) if previous and complete_session else 0
    if trend and protected is not None and closes_through(recent, -trend, protected, buffer):
        trend, protected = 0, None
    may_establish = (last_established in (0, impulse)
                     or bool(previous and previous.recovery_side == impulse))
    if not trend and impulse and may_establish:
        edge = threes[-2].low if impulse == 1 else threes[-2].high
        if not closes_through(recent, -impulse, edge, buffer):
            trend, protected = impulse, edge
            if complete_session:
                last_established = trend
    if trend and protected is not None:
        for point in reversed(swings(threes[-10:], trend, duration=3, left=1)):
            if (trend * (point.price - protected) > buffer
                    and trend * (last.close - point.price) > max(.9 * atr, .40 * atr3)):
                protected = point.price
                break
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
    recovery_side = previous.recovery_side if previous else 0
    recovery_level = previous.recovery_level if previous else None
    recovered_at = previous.recovered_at if previous else None
    if recovery_side and (now - recovered_at > 14 * MINUTE or trend == recovery_side
                          or closes_through(recent, -recovery_side, recovery_level, buffer)):
        recovery_side, recovery_level, recovered_at = 0, None, None
    if len(recent) < 5:
        context = PriceContext(now, atr, atr3,
                               volatility(ten, minimum=2.5), trend, protected, bounds,
                               supports, resistances, support_defended, resistance_defended,
                               recovery_side, recovery_level, recovered_at, last_established)
        return context, results
    penultimate = recent[-2]

    def add(side: int, scenario: str, origin: datetime, trigger: float, stop: float, level: float):
        if (side * (last.close - trigger) >= 0
                and side * (penultimate.close - trigger) < 0
                and side * (trigger - stop) > 0):
            results.append(Signal(side, scenario, now, origin, trigger, stop, level))

    for side in (1, -1):
        levels, opposing = side_zones[side], side_zones[-side]
        for reversal in (row for row in results.copy() if row.reversal and row.side == side):
            opposing_level = support_defended if side == -1 else resistance_defended
            if (trend != side and recovery_side != side and not (recovery_side == -side and opposing_level)
                    and confirmed_reversal(reversal, recent, atr)):
                recovery_side, recovery_level, recovered_at = side, reversal.invalidation, now
        protected_opposite = (trend or last_established) == -side and recovery_side != side
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
                           recovery_side, recovery_level, recovered_at, last_established)
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

    def exceeds(self, threshold_bps: int) -> bool:
        # Compare raw OI counts so displayed rounding cannot change eligibility.
        return self.prior > 0 and (self.row.oi - self.prior) * 10_000 > self.prior * threshold_bps


@dataclass(frozen=True)
class OIEntryThreshold:
    bps: int
    reason: str


def entry_oi_threshold(signal: Signal, context: PriceContext, bars: list[Candle],
                       spot: float, cfg: Config) -> OIEntryThreshold:
    """Reduce the hurdle only for fresh signals with clean price follow-through."""
    floor, ceiling = cfg.oi_entry_floor_bps, cfg.oi_entry_ceiling_bps
    if floor == ceiling:
        return OIEntryThreshold(ceiling, 'FIXED_CONFIGURED_THRESHOLD')
    extension = signal.side * (spot - signal.trigger)
    opposing_defense = context.defends_resistance if signal.side == 1 else context.defends_support
    age = context.at - signal.at
    if opposing_defense or not timedelta(0) <= age <= MINUTE or not 0 <= extension <= .55 * context.atr:
        return OIEntryThreshold(ceiling, 'STANDARD_PRICE_THRESHOLD')
    steps = directional_steps(bars, signal.side)
    if not steps or steps[-1] <= 0 or sum(step > 0 for step in steps) < 2:
        return OIEntryThreshold(ceiling, 'STANDARD_PRICE_THRESHOLD')
    net = sum(steps)
    efficiency = net / sum(abs(step) for step in steps)
    if net >= .75 * context.atr and efficiency >= .65:
        return OIEntryThreshold(floor, 'STRONG_EARLY_PRICE_CONFIRMATION')
    if net >= .50 * context.atr and efficiency >= .50:
        return OIEntryThreshold((floor + ceiling) // 2, 'EARLY_PRICE_CONFIRMATION')
    return OIEntryThreshold(ceiling, 'STANDARD_PRICE_THRESHOLD')


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
        if previous.expiry != current.expiry or previous.through != current.through - 3 * MINUTE:
            continue
        elapsed = (current.at - previous.at).total_seconds()
        if abs(elapsed - 180) <= cfg.oi_jitter_seconds:
            options.append((abs(elapsed - 180), previous.at, previous))
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


@dataclass(frozen=True)
class OptionCandidate:
    row: OIRow
    atm: float
    offset: int
    change: float
    prior_oi: int
    threshold_bps: int


def listed_strikes(contracts: list[dict]) -> list[float]:
    # Missing OI cannot silently move ATM or the offsets.
    by_side = [{float(row['strike_price']) for row in contracts if row['instrument_type'] == kind}
               for kind in ('CE', 'PE')]
    return sorted(by_side[0] & by_side[1])


def rank_options(window: OIWindow, grid: list[float], side: int,
                 spot: float, threshold_bps: int) -> tuple[list[OptionCandidate], list[dict]]:
    kind = 'CE' if side == 1 else 'PE'
    if len(grid) < 3 or not grid[0] <= spot <= grid[-1]:
        return [], []
    idx = min(range(len(grid)), key=lambda i: (abs(grid[i] - spot), grid[i]))
    selected_indices = (idx-side, idx-2*side)
    if not all(0 <= i < len(grid) for i in selected_indices):
        return [], []
    changes = {(x.row.side, x.row.strike): x for x in window.changes}
    ranked, audit = [], []
    for i in selected_indices:
        strike = grid[i]
        item = changes.get((kind, strike))
        audit.append({'side': kind, 'strike': strike, 'offset': i-idx, 'atm': grid[idx],
                      'status': 'MATCHED' if item else 'OI_COMPARISON_MISSING',
                      'increase_pct': 100 * item.increase if item else None,
                      'prior_oi': item.prior if item else None,
                      'current_oi': item.row.oi if item else None,
                      'meets_threshold': item.exceeds(threshold_bps) if item else None})
        if item and item.exceeds(threshold_bps):
            ranked.append(OptionCandidate(item.row, grid[idx], i-idx, item.increase,
                                          item.prior, threshold_bps))
    if any(x['status'] != 'MATCHED' for x in audit):
        return [], audit
    return sorted(ranked, key=lambda x: (-x.change, abs(x.offset), x.row.key)), audit


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


def level_confirmation(signal: Signal, ctx: PriceContext, window: OIWindow,
                       spot: float) -> tuple[bool, dict]:
    side = signal.side
    same = oi_levels(window, spot, -side, ctx.atr)
    ahead = oi_levels(window, spot, side, ctx.atr)
    locality = max(25.0, 1.7 * ctx.atr)
    supportive = [x for x in same if abs(x.strike - signal.level) <= locality]
    cleared = [x for x in ahead if abs(x.strike - signal.level) <= locality
               and side * (spot - x.strike) > .10 * ctx.atr]
    # A move through a former wall or defense can itself verify the price
    # reaction. Falling OI there strengthens the break. An intact wall remains
    # a target constraint even when the selected option is building OI.
    material = OI_LEVEL_MATERIAL_CHANGE
    weakening = [x for x in cleared if x.change is not None and x.change < -material]
    held_level = [x for x in supportive if x.change is not None and x.change >= -material]
    changed_support = [x for x in held_level if x.change is not None and x.change > material]
    near_wall = [x for x in ahead if 0 <= side * (x.strike - spot) <= .85 * ctx.atr
                 and x.change is not None and x.change > material]
    defense = ctx.defends_resistance if side == 1 else ctx.defends_support
    detail = {'held_levels': [asdict(x) for x in held_level],
              'strengthening_levels': [asdict(x) for x in changed_support],
              'cleared_levels': [asdict(x) for x in cleared],
              'weakening_barriers': [asdict(x) for x in weakening],
              'intact_nearby_walls': [asdict(x) for x in near_wall]}
    if signal.scenario == 'FAILED_PULLBACK':
        # A live OI wall matters here only when price has defended that wall.
        # An unrelated old support or resistance cannot corroborate it.
        price_walls = ctx.resistances if side == 1 else ctx.supports
        nearby_confirmed = any(abs(wall.strike - zone.price) <= max(2., .35 * ctx.atr)
                               for wall in near_wall for zone in price_walls if zone.strength >= 2)
        return not (defense and nearby_confirmed), detail
    if defense and near_wall:
        return False, detail
    if signal.scenario in ('PULLBACK_CONTINUATION', 'TREND_RESUMPTION',
                           'ACCEPTED_BREAKOUT', 'ACCEPTED_BREAKDOWN'):
        # Require local OI evidence at the defended or broken level. The strike
        # ranking gate independently applies the selected entry threshold.
        evidence = changed_support or weakening or [
            x for x in held_level if x.change > 0
        ] or [x for x in cleared if x.change is not None and x.change < 0]
        return bool(evidence), detail
    return True, detail


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


def is_zone_rotation(signal: Signal) -> bool:
    evidence = signal.reversal
    return bool(evidence and evidence.pattern == 'REPEATED_ZONE'
                and evidence.second_test - evidence.first_test >= 9 * MINUTE)


def stop_buffer(atr_1m: float, atr_3m: float = 0) -> float:
    return max(.8, .18 * atr_1m, .12 * atr_3m)


def next_oi_objective(levels: list[OILevel], side: int, beyond: float,
                      atr: float, separation: float = 0) -> float | None:
    for row in levels:
        objective = row.strike - side * max(.5, .10 * atr)
        if side * (objective - beyond) > max(.4 * atr, separation):
            return round(objective, 4)
    return None


def risk_plan(signal: Signal, ctx: PriceContext, levels: list[OILevel],
              spot: float, cfg: Config) -> tuple[RiskPlan | None, str]:
    side, atr = signal.side, ctx.atr
    continuation = signal.scenario in CONTINUATION_SCENARIOS
    stop = signal.invalidation - side * stop_buffer(atr, ctx.atr3 if continuation else 0)
    risk = side * (spot - stop)
    if risk < cfg.min_stop_atr * atr:
        stop = spot - side * cfg.min_stop_atr * atr
        risk = cfg.min_stop_atr * atr
    if risk > cfg.max_stop_atr * atr:
        return None, 'STRUCTURAL_STOP_TOO_WIDE'
    opposing = ctx.resistances if side == 1 else ctx.supports
    projected = []
    for zone in opposing:
        if zone.strength >= 3 and side * (zone.price - spot) > .15 * atr:
            matches = [x for x in levels if abs(x.strike - zone.price) <= max(4.0, .60*atr)
                       and side * (x.strike - spot) > .15*atr]
            effective = min([zone.price, *(x.strike for x in matches)], key=lambda x: side*x)
            projected.append((effective, zone.source + ('+OI' if matches else '')))
    if ctx.range_bounds:
        edge = ctx.range_bounds[1] if side == 1 else ctx.range_bounds[0]
        if side * (edge - spot) > .15 * atr:
            projected.append((edge, '10M_RANGE_EDGE'))
    if not projected:
        return None, 'NO_10M_TARGET'
    level, source = min(projected, key=lambda row: side*row[0])
    if signal.scenario == 'SWEEP_RETEST':
        # A broken 10m level can become a barrier on the retest. Require
        # corroboration at that price from a growing OI concentration.
        structure = [z for z in (*ctx.supports, *ctx.resistances) if z.strength >= 3]
        capped = [row for row in levels if row.change is not None
                  and row.change > OI_LEVEL_MATERIAL_CHANGE
                  and .15 * atr < side * (row.strike - spot) < side * (level - spot)
                  and any(abs(row.strike - z.price) <= .65 * atr for z in structure)]
        if capped:
            level = min(capped, key=lambda row: side * row.strike).strike
            source = '10M_STRUCTURE_AND_OI_RETEST'
    # A strengthening OI barrier confirmed at a price reaction can cap T1.
    for wall in levels:
        if not .15 * atr < side * (wall.strike - spot) < side * (level - spot):
            continue
        if wall.change is not None and wall.change > OI_LEVEL_MATERIAL_CHANGE and any(
            abs(wall.strike - z.price) <= .5 * atr for z in opposing if z.strength >= 2
        ):
            level, source = wall.strike, 'DEFENDED_OI_LEVEL_BEFORE_10M_TARGET'
            break
    # A 10m swing marks the center of a reaction area. A continuation
    # target sits at its near edge, allowing for the normal 3m excursion.
    approach = max(.5, .14 * atr)
    if signal.scenario == 'FAILED_PULLBACK' and '10M' in source:
        approach = max(approach, .35 * ctx.atr3)
    t1 = level - side * approach
    reward = side * (t1 - spot) / risk
    if reward < cfg.min_reward_risk and is_zone_rotation(signal):
        # A distant repeated zone can justify staged exits. The first support
        # or resistance remains T1. T2 needs independent confluence with the
        # intervening swing, and the weighted plan must still meet min R.
        peak = signal.reversal.intervening_extreme
        if peak is not None and reward >= .60:
            choices = [row for row in levels if abs(row.strike - peak) <= max(2., .55 * atr)
                       and side * (row.strike - t1) > max(.8 * atr, .45 * risk)]
            if choices:
                wall = min(choices, key=lambda row: abs(row.strike - peak))
                t2 = wall.strike - side * max(.5, .10 * atr)
                blended = .40 * reward + .60 * side * (t2 - spot) / risk
                if blended >= cfg.min_reward_risk:
                    return RiskPlan(round(stop, 4), round(t1, 4), round(t2, 4), source,
                                    'OI_AND_REPEATED_ZONE_EXCURSION', round(risk, 4), round(reward, 4),
                                    'CONFIRMED_3M_SWING', 40, round(blended, 4)), 'QUALIFIED'
    if reward < cfg.min_reward_risk:
        return None, 'INSUFFICIENT_REWARD_TO_10M_TARGET'
    t2 = next_oi_objective(levels, side, t1, atr, separation=max(.8 * atr, .45 * risk))
    if t2 is None:
        return None, 'NO_FURTHER_OI_TARGET'
    policy = 'CONFIRMED_3M_SWING' if continuation else 'STANDARD_POST_T1'
    return RiskPlan(round(stop, 4), round(t1, 4), t2, source, 'NEXT_OI_LEVEL',
                    round(risk, 4), round(reward, 4), policy), 'QUALIFIED'


def live_contract(candidate: OptionCandidate, quote: dict | None, now: datetime,
                  index_time: datetime, row: dict, cfg: Config) -> dict:
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
    return {'instrument_key': candidate.row.key, 'side': candidate.row.side,
            'strike': candidate.row.strike, 'atm': candidate.atm, 'offset': candidate.offset,
            'expiry': row['expiry'], 'bid': bid, 'ask': ask, 'spread_pct': round(spread, 4),
            'depth_lots': depth, 'lot_size': int(lot), 'quote_time': seen.isoformat(),
            'oi_change_pct': round(100 * candidate.change, 6),
            'oi_entry_threshold_pct': candidate.threshold_bps / 100,
            'oi_previous': candidate.prior_oi, 'oi_current': candidate.row.oi}


class Upstox:

    def __init__(self, token: str):
        if not token or any((c in token for c in '\r\n')):
            raise ProviderError('UPSTOX_ANALYTICS_TOKEN missing or invalid')
        self._token = token

    def get(self, path: str, params: dict | None=None):
        url = 'https://api.upstox.com' + path + ('?' + urlencode(params) if params else '')
        req = Request(url, headers={'Authorization': 'Bearer ' + self._token, 'Accept': 'application/json', 'User-Agent': 'nifty-scanner/124.0'})
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
    digest=hashlib.sha256(json.dumps([kind,details],sort_keys=True,allow_nan=False,
                                      separators=(',',':')).encode()).hexdigest()[:24]
    if not any(e['id']==digest for e in state['outbox']):
        state['outbox'].append({'id':digest,'kind':kind,'details':details,
                                'created_at':now.isoformat(),'status':'PENDING'})
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
                     cfg: Config) -> tuple[dict | None, list[tuple[str, dict]], dict | None, list[str]]:
    position = copy.deepcopy(p)
    side = 1 if position['direction'] == 'BULLISH' else -1
    cursor = timestamp(position['last_candle'])
    opening = timestamp(position['opened_at'])
    alerts: list[tuple[str, dict]] = []
    warnings: list[str] = []

    def emit(kind, at, **fields):
        alerts.append((kind, position_event_payload(position, at, **fields)))

    def finish(kind, at, reason, value, source):
        emit(kind, at, reason=reason, underlying_reference=value, source=source)
        return None, alerts, close_reference(position, at, reason, value, source), warnings

    def hit_t1(at, source):
        position.update(t1_hit=True, t1_at=at.isoformat(), remaining_pct=100-position.get('t1_exit_pct', 50))
        emit('T1', at, source=source, underlying_reference=position['t1'])

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
        if side * (adverse - stop) <= 0:
            return finish('EXIT', at, 'STRUCTURAL_SL', stop, 'COMPLETED_1M_STOP_FIRST')
        if not position['t1_hit'] and side * (favorable - position['t1']) >= 0:
            hit_t1(at, 'COMPLETED_1M_HIGH_LOW')
        if position['t1_hit'] and side * (favorable - t2) >= 0:
            return finish('T2', at, 'OI_TARGET_REACHED', t2, 'COMPLETED_1M_HIGH_LOW')
        position['last_candle'] = bar.start.isoformat()
        expected += MINUTE

    if now >= deadline:
        return finish('EXIT', now, 'SESSION_REFERENCE_EXIT', spot,
                      'FRESH_INDEX_QUOTE' if spot is not None else 'CLOCK_NO_FRESH_INDEX_QUOTE')
    if spot is not None:
        if side * (spot - position['stop']) <= 0:
            return finish('EXIT', now, 'STRUCTURAL_SL', spot, 'FRESH_INDEX_QUOTE')
        if not position['t1_hit'] and side * (spot - position['t1']) >= 0:
            hit_t1(now, 'FRESH_INDEX_QUOTE')
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
        oi_snapshot_at=window.snapshot.at.isoformat() if window else None))]


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
    # scheduler invocations. Only the last three closed minutes can alert.
    previous = None
    reversals = SessionReversals()
    live: dict[str, Signal] = {}
    examined = []
    for i in range(1, len(bars)+1):
        if i > 1 and bars[i-1].start - bars[i-2].start != MINUTE:
            previous = None
            reversals = SessionReversals()
        previous, signals = market_signals(bars[:i], prior_ten, session_open, previous, reversals)
        if i >= len(bars)-2:
            for signal in signals:
                live.setdefault(signal.identity, signal)
            examined.append({'at': previous.at.isoformat(), 'trend': previous.trend,
                             'protected': previous.protected, 'range': previous.range_bounds,
                             'signals': [price_public(s) for s in signals]})
    assert previous is not None
    return previous, list(live.values()), jsonable(examined)


def safe_price_direction(signal: Signal, ctx: PriceContext, bars: list[Candle],
                         spot: float, cfg: Config) -> str | None:
    side, atr = signal.side, ctx.atr
    reversal = signal.reversal is not None or signal.scenario in ('DOUBLE_BOTTOM', 'DOUBLE_TOP')
    failed = signal.scenario == 'FAILED_PULLBACK'
    established = ctx.trend or ctx.last_established_side
    if established == -side and not reversal and ctx.recovery_side != side:
        return 'OPPOSITE_PROTECTED_TREND'
    if reversal and established == -side and not confirmed_reversal(signal, bars, atr):
        return 'COUNTERTREND_REVERSAL_NOT_CONFIRMED'
    if failed and ctx.trend != side:
        return 'PULLBACK_TREND_LOST'
    defended = ctx.defends_resistance if side == 1 else ctx.defends_support
    accepted = signal.scenario in ('ACCEPTED_BREAKOUT', 'ACCEPTED_BREAKDOWN')
    if defended and (accepted or reversal or failed or ctx.recovery_side == side):
        opposing = ctx.resistances if side == 1 else ctx.supports
        for level in opposing:
            clearance = .45 * atr if signal.reversal is not None and level.strength == 2 else .75 * atr
            near = -.15*atr <= side * (level.price - spot) <= clearance
            if near and level.strength >= 2 and not closes_through(bars, side, level.price, max(.6, .11*atr)):
                return 'NEARBY_CONFIRMED_OPPOSING_LEVEL'
    if defended and not accepted and not reversal and not failed and ctx.recovery_side != side:
        return 'OPPOSING_PRICE_LEVEL_DEFENDED'
    if (ctx.recovery_side == -side and ctx.recovery_level is not None
            and abs(spot - ctx.recovery_level) <= (.55 if is_zone_rotation(signal) else 2.2) * atr
            and not (failed and side * (spot - ctx.recovery_level) >= .35 * atr)
            and not closes_through(bars, side, ctx.recovery_level, max(.6, .11*atr))):
        return 'OPPOSING_REVERSAL_LEVEL_STILL_DEFENDED'
    if failed:
        # Discovery already verified the preceding aligned 3m progression.
        # Keep that evidence only while the renewed 1m leg still holds.
        recent = [b for b in bars if signal.at - MINUTE <= b.start]
        if not recent or side * (recent[-1].close - signal.trigger) < -.10 * atr:
            return 'PULLBACK_TRIGGER_LOST'
    elif not pressure(bars, side, atr):
        return 'THREE_MINUTE_PRICE_NOT_ALIGNED'
    if side * (signal.trigger - signal.invalidation) <= 0:
        return 'INVALID_STRUCTURAL_STOP'
    if side * (spot - signal.invalidation) <= 0:
        return 'STRUCTURE_INVALIDATED'
    since_trigger = [b for b in bars if b.start >= signal.at]
    if any(side * ((b.low if side == 1 else b.high) - signal.invalidation) <= 0 for b in since_trigger):
        return 'STRUCTURE_INVALIDATED_AFTER_TRIGGER'
    extension = side * (spot - signal.trigger)
    if extension < 0:
        return 'LIVE_PRICE_BACK_BEHIND_TRIGGER'
    initial_distance = side * (signal.trigger - signal.invalidation)
    if failed:
        initial_distance += stop_buffer(atr, ctx.atr3)
    if extension > cfg.max_chase_atr * atr or extension > .90 * initial_distance:
        return 'ENTRY_EXTENDED'
    if abs(spot - bars[-1].close) > 1.7 * atr:
        return 'LIVE_SPOT_TOO_FAR_FROM_RECENT_CLOSE'
    return None


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
    rotation_from = None
    result = {'version': VERSION, 'at': now.isoformat(), 'session_date': now.date().isoformat(),
              'decision': 'NO_TRADE', 'reason': 'UNSET', 'alerts_created': [],
              'position_locked': bool(active), 'evaluations': []}

    def no_trade(reason: str):
        if rotation_from is not None:
            result['rotation_check'] = reason
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
    bars = []
    try:
        raw = api.candles()
        now = clock()
        bars = [b for b in parse_candles(raw, now - timedelta(seconds=cfg.feed_grace_seconds - 1))
                if session_open <= b.start and bar_end(b) <= session_close]
    except (DataError, ProviderError) as exc:
        now = clock()
        result['candle_error'] = str(exc)

    expected = exact_minute(now - timedelta(seconds=cfg.feed_grace_seconds))
    through = bar_end(bars[-1]) if bars else None
    latest = through == expected
    if bars:
        result['candle_coverage'] = {'from': bars[0].start.isoformat(), 'through': through.isoformat(),
                                     'contiguous_tail': len(contiguous_tail(bars)), 'latest': latest}
    if not active and (not latest or len(contiguous_tail(bars)) < 3):
        return no_trade('LATEST_COMPLETED_CANDLES_UNAVAILABLE')

    early_baseline = max(day_time(now, 9, 18), session_open + 3 * MINUTE)
    if not active and now < early_baseline:
        return no_trade('BEFORE_FIRST_OI_BASELINE')
    spot_for_management = None
    managed = None
    management_events = []
    management_warnings = []
    closed_before_capture = False
    if active:
        try:
            quotes = api.quotes([INDEX])
            now = clock()
            spot_for_management = checked_quote(quotes.get(INDEX), now, cfg.quote_max_age_seconds)
        except (DataError, ProviderError, KeyError) as exc:
            now = clock()
            result['quote_error'] = str(exc)
        managed, management_events, closed, management_warnings = manage_reference(
            active, bars, spot_for_management, now, deadline, cfg
        )
        if closed is not None:
            save_position(managed, management_events, closed, management_warnings, at=now)
            closed_before_capture = True

    window = None
    chain: list[dict] = []
    contracts: list[dict] = []
    # Capture OI even while a strike is locked or before entry can be allowed.
    # The baseline belongs to one exact price-window end.
    if latest and through is not None and now < deadline:
        try:
            expiry, contracts = api.contracts(now.date())
            chain = api.chain(expiry, contracts)
            now = clock()
            if exact_minute(now - timedelta(seconds=cfg.feed_grace_seconds)) != through:
                result['oi'] = {'status': 'CAPTURE_CROSSED_PRICE_WINDOW'}
            else:
                sample = make_oi_snapshot(chain, expiry, now, through)
                ring = engine['oi_samples']
                window = match_oi(ring, sample, cfg)
                ring = [s for s in ring if now - timestamp(s['at']) < 15 * MINUTE]
                if not any(s['through'] == through.isoformat() and s['expiry'] == expiry for s in ring):
                    ring.append(price_public(sample))
                engine['oi_samples'] = ring[-8:]
                result['oi'] = {'status': 'MATCHED' if window else 'OI_WINDOW_UNAVAILABLE',
                                'at': now.isoformat(), 'through': through.isoformat(),
                                'expiry': expiry,
                                'baseline': window.baseline.isoformat() if window else None,
                                'matched_contracts': len(window.changes) if window else 0}
        except (DataError, ProviderError, ValueError, KeyError, TypeError) as exc:
            now = clock()
            result['oi'] = {'status': 'OPTION_CHAIN_UNAVAILABLE', 'reason': str(exc)}

    if closed_before_capture:
        # A closing alert still leaves an OI baseline for the next scheduled run.
        return result, times

    if active:
        if window and spot_for_management is not None and bars and managed['t1_hit']:
            try:
                fresh = api.quotes([INDEX])
                now = clock()
                fresh_spot = checked_quote(fresh.get(INDEX), now, cfg.quote_max_age_seconds)
                managed, extra, closed, warnings = manage_reference(managed, bars, fresh_spot, now, deadline, cfg)
                management_events.extend(extra)
                management_warnings.extend(warnings)
                if managed is not None and exact_minute(now - timedelta(seconds=cfg.feed_grace_seconds)) == through:
                    management_events.extend(refine_reference(managed, bars, fresh_spot, window, now,
                                                              session_open=session_open))
            except (DataError, ProviderError, KeyError) as exc:
                now = clock()
                result['refinement_error'] = str(exc)
        elif (spot_for_management is not None and bars and managed['t1_hit']
              and exact_minute(now - timedelta(seconds=cfg.feed_grace_seconds)) == through
              and now < deadline):
            management_events.extend(refine_reference(managed, bars, spot_for_management, None, now,
                                                      session_open=session_open))
        if managed is not None and now >= deadline:
            managed, extra, closed, warnings = manage_reference(managed, [], None, now, deadline, cfg)
            management_events.extend(extra)
            management_warnings.extend(warnings)
        save_position(managed, management_events, closed, management_warnings, at=now)
        if managed is not None and spot_for_management is None and not bars:
            result.update(decision='POSITION_MONITORING_UNAVAILABLE', reason='PRICE_FEED_UNAVAILABLE')
        if managed is None or not managed['t1_hit'] or not window or not latest or spot_for_management is None:
            return result, times
        # A reversal can replace only the remainder of a trade that already
        # realized T1. Leave that position intact unless the new contract,
        # price, OI and risk all qualify in the same observation.
        rotation_from = managed

    if now < max(day_time(now, *ENTRY_START), session_open+6*MINUTE):
        return no_trade('COLLECTING_OPENING_BASELINE')
    last_entry = min(day_time(now, *ENTRY_END), deadline - 10*MINUTE)
    if now >= last_entry:
        return no_trade('OUTSIDE_ENTRY_WINDOW')
    if len(contiguous_tail(bars)) < 6:
        return no_trade('INSUFFICIENT_CONTIGUOUS_PRICE_HISTORY')
    last_exit = state.get('last_exit')
    if last_exit and now - timestamp(last_exit['at']) < cfg.cooldown_minutes * MINUTE:
        return no_trade('POST_EXIT_COOLDOWN')

    prior_ten = prior_context(engine, api, now)
    now = clock()
    context, signals, recent = price_history(bars, prior_ten, session_open)
    result['price'] = {'atr_1m': context.atr, 'atr_3m': context.atr3, 'atr_10m': context.atr10,
                       'trend': context.trend, 'protected': context.protected, 'range': context.range_bounds,
                       'last_established_side': context.last_established_side,
                       'recovery_side': context.recovery_side, 'recovery_level': context.recovery_level,
                       'defended_support': context.defends_support,
                       'defended_resistance': context.defends_resistance,
                       'observations': recent}
    if rotation_from is not None:
        existing = 1 if rotation_from['direction'] == 'BULLISH' else -1
        signals = [signal for signal in signals if signal.side == -existing and is_zone_rotation(signal)]
    if not signals:
        return no_trade('NO_FRESH_PRICE_TRIGGER')
    if window is None:
        return no_trade('OI_WINDOW_UNAVAILABLE')
    if exact_minute(now - timedelta(seconds=cfg.feed_grace_seconds)) != through:
        return no_trade('PRICE_WINDOW_ROLLED_DURING_SNAPSHOT')

    preliminary = bars[-1].close
    grid = listed_strikes(contracts)
    span = 1.7 * context.atr
    plausible_spots = {preliminary - span, preliminary, preliminary + span}
    plausible_spots.update(strike for strike in grid if abs(strike - preliminary) <= span)
    # Prefetch at the floor. Final ranking uses each setup's live threshold.
    desired_keys = {candidate.row.key for side in {signal.side for signal in signals}
                    for price in plausible_spots
                    for candidate in rank_options(window, grid, side, price, cfg.oi_entry_floor_bps)[0]}
    desired = [INDEX, *sorted(desired_keys)]
    try:
        quotes = api.quotes(desired)
    except (DataError, ProviderError) as exc:
        result['quote_error'] = str(exc)
        return no_trade('ENTRY_QUOTE_REQUEST_FAILED')
    now = clock()
    if now >= last_entry or exact_minute(now - timedelta(seconds=cfg.feed_grace_seconds)) != through:
        return no_trade('DECISION_WINDOW_EXPIRED_DURING_QUOTE_FETCH')
    quote = quotes.get(INDEX)
    try:
        spot = checked_quote(quote, now, cfg.quote_max_age_seconds)
        quote_time = timestamp(quote['timestamp'])
    except (DataError, KeyError):
        return no_trade('INDEX_QUOTE_UNAVAILABLE')
    if quote_time < through - timedelta(seconds=2):
        return no_trade('INDEX_QUOTE_PREDATES_PRICE_WINDOW')

    front = {r['instrument_key']: r for r in chain}
    consumed = engine['consumed_signals']
    last_fill = engine.get('last_entry_through')
    if last_fill == through.isoformat():
        return no_trade('SIGNAL_WINDOW_ALREADY_USED')
    priority = {'DOUBLE_BOTTOM': 0, 'DOUBLE_TOP': 0, 'SWEEP_RETEST': 0, 'OPENING_MOMENTUM': 1,
                'FAILED_PULLBACK': 2, 'ACCEPTED_BREAKOUT': 3, 'ACCEPTED_BREAKDOWN': 3,
                'PULLBACK_CONTINUATION': 4, 'RANGE_EDGE': 5, 'TREND_RESUMPTION': 6}
    eligible = []
    for signal in sorted(signals, key=lambda x: (priority[x.scenario], x.at, x.identity)):
        details = {'signal': price_public(signal), 'identity': signal.identity}
        result['evaluations'].append(details)
        if signal.identity in consumed:
            details['reason'] = 'SIGNAL_ALREADY_USED'
            continue
        reason = safe_price_direction(signal, context, bars, spot, cfg)
        if reason:
            details['reason'] = reason
            continue
        supported, level_detail = level_confirmation(signal, context, window, spot)
        details['oi_structure'] = level_detail
        if not supported:
            details['reason'] = 'OI_LEVELS_DO_NOT_CONFIRM_PRICE'
            continue
        threshold = entry_oi_threshold(signal, context, bars, spot, cfg)
        details['oi_entry_threshold'] = {'pct': threshold.bps / 100, 'reason': threshold.reason}
        candidates, compared = rank_options(window, grid, signal.side, spot, threshold.bps)
        details['oi_candidates'] = compared
        details['candidate_ranking'] = [asdict(c) for c in candidates]
        if not candidates:
            if not compared:
                details['reason'] = 'ATM_OFFSETS_UNAVAILABLE'
            elif any(x['status'] != 'MATCHED' for x in compared):
                details['reason'] = 'CANDIDATE_OI_COMPARISON_INCOMPLETE'
            else:
                details['reason'] = 'NO_OPTION_OI_CHANGE_ABOVE_ENTRY_THRESHOLD'
            continue
        plan, reason = risk_plan(signal, context, oi_levels(window, spot, signal.side, context.atr), spot, cfg)
        details['reason'] = reason
        if plan:
            details['plan'] = asdict(plan)
            eligible.append((signal, plan, candidates, details))
    if not eligible:
        return no_trade('PRICE_OI_OR_RISK_REQUIREMENTS_NOT_MET')
    if len({signal.side for signal, *_ in eligible}) > 1:
        return no_trade('CONFLICTING_QUALIFIED_DIRECTIONS')

    for signal, plan, candidates, details in eligible:
        details['contract_rejections'] = []
        for candidate in candidates:
            key = candidate.row.key
            if key not in desired:
                details['contract_rejections'].append({'key': key, 'reason': 'ATM_MOVED_OUTSIDE_QUOTED_GRID'})
                break
            try:
                contract = live_contract(candidate, quotes.get(key), now, quote_time, front[key], cfg)
            except (DataError, KeyError, ValueError, TypeError) as exc:
                details['contract_rejections'].append({'key': key, 'reason': str(exc)})
                continue
            position_id = hashlib.sha256(
                f'{now.date()}|{signal.identity}|{key}'.encode()
            ).hexdigest()[:22]
            direction = 'BULLISH' if signal.side == 1 else 'BEARISH'
            position = {'id': position_id, 'status': 'OPEN', 'direction': direction,
                        'side': contract['side'], 'strike': contract['strike'], 'expiry': contract['expiry'],
                        'instrument_key': key, 'opened_at': now.isoformat(), 'entry_spot': spot,
                        'entry_ask': contract['ask'], 'initial_stop': plan.stop,
                        'last_candle': bars[-1].start.isoformat(), 'scenario': signal.scenario,
                        't1_hit': False, 'remaining_pct': 100, 'contract': contract, **asdict(plan)}
            if rotation_from is not None:
                rotated = close_reference(rotation_from, now, 'CONFIRMED_ZONE_REVERSAL', spot,
                                          'FRESH_PRICE_OI_AND_NEW_CONTRACT')
                close_event = ('EXIT', position_event_payload(
                    rotation_from, now, reason=rotated['exit_reason'], underlying_reference=spot,
                    source=rotated['exit_source'], replacement_position_id=position_id,
                    signal=price_public(signal)))
                save_position(None, [close_event], rotated, management_warnings, at=now)
                result['rotated_from'] = rotation_from['id']
            state['position'] = position
            engine['last_entry_through'] = through.isoformat()
            engine['consumed_signals'] = (consumed + [s.identity for s, *_ in eligible])[-160:]
            event_id = new_event(state, 'ENTRY', position_event_payload(
                position, now, reason='QUALIFIED_PRICE_AND_3M_OI', signal=price_public(signal),
                plan=asdict(plan), oi={'window': result['oi'], 'contract': contract,
                                      'entry_threshold': details['oi_entry_threshold'],
                                      'price_levels': details['oi_structure']}), now)
            result['alerts_created'].append(event_id)
            result.update(decision='ENTRY', reason='QUALIFIED_' + contract['side'],
                          position_locked=True, selected_position=position)
            return result, times
    return no_trade('NO_LIQUID_CONTRACT_IN_OI_RANKING')


def mail_content(event:dict) -> tuple[str,str]:
    d=event['details'];p=d.get('position') or {}
    side=p.get('side','')
    strike=p.get('strike','')
    kind=event['kind']
    remaining = 0 if kind in ('EXIT', 'T2') else p.get('remaining_pct')
    extra= d.get('reason','')
    subject=f'NIFTY scanner | {kind} {strike} {side} | {extra}'
    lines=[f'ALERT: {kind}','',f'Event ID: {event["id"]}',
           f'Position ID: {d.get("position_id")}',f'Observed at: {d.get("observed_at")}',
           f'Strike: {strike} {side}',f'Expiry: {p.get("expiry")}',
           f'Entry underlying reference: {p.get("entry_spot")}',
           f'Underlying initial stop: {p.get("initial_stop")}',
           f'Current underlying stop: {p.get("stop")}',
           f'T1 (underlying): {p.get("t1")}',f'T2 (underlying): {p.get("t2")}',
           f'Position allocated to T1: {p.get("t1_exit_pct") or 50}%',
           f'Position remaining: {remaining}%',
           f'Observed underlying reference: {d.get("underlying_reference")}',
           f'Event reason: {extra}',f'Old/new stop: {d.get("old_stop")} -> {d.get("new_stop")}',
           f'Old/new T2: {d.get("old_t2")} -> {d.get("new_t2")}',
           f'Source: {d.get("source")}',
           f'Effective session cutoff: {d.get("effective_at")}', 
           f'Signal: {json.dumps(d.get("signal",{}),sort_keys=True)}',
           f'Execution/risk plan: {json.dumps(d.get("plan",{}),sort_keys=True)}',
           f'OI context: {json.dumps(d.get("oi",{}),sort_keys=True)}',
                      '',
           'REFERENCE ALERT ONLY. No broker order was placed or confirmed.',
           'Stops and targets are underlying index reference levels, not option premium stop orders.',
           'Candle OHLC cannot prove intrabar order or the price at which a user could have filled.',
           'Uncertain delivery needs explicit mailbox verification before a manual retry.']
    return subject,'\n'.join(lines)


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
             'result':result,'source_file_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
        if cfg.record_inputs and not (
            result.get('reason') in ('AFTER_SESSION_EXIT_CUTOFF', 'NO_VERIFIED_NFO_SESSION',
                                     'BEFORE_FIRST_OI_BASELINE')
            and not result.get('position_locked')
        ):
            session_date=now.date().isoformat()
            run_id=os.environ.get('GITHUB_RUN_ID','local')+'-'+os.environ.get('GITHUB_RUN_ATTEMPT','1')
            captured_at=now.strftime('%H%M%S-%f')
            safe=''.join(x if x.isalnum() or x in '-_' else '_' for x in run_id)
            file=audit_dir/'inputs_v126'/session_date/(captured_at+'-'+safe+'.json.gz')
            record_inputs(file,raw)
            event['input_recording']=str(file)
    if result.get('reason') != 'AFTER_SESSION_EXIT_CUTOFF' or event['alerts_pending']:
        append_audit(audit_dir/('market_scan_v126_'+now.date().isoformat()+'.jsonl'), event)
    if failure:
        result['audit_recorded']=True
    return result


def replay_recordings(directory:Path, cfg:Config, output:Path) -> int:
    """Replay v126 recordings in the inputs_v126 directory.

    Mismatched API call sequences fail rather than silently substituting a
    future price, date, quote, or contract not captured at that decision time.
    """
    files=sorted(directory.rglob('*.json.gz'))
    if not files:raise ScannerError('NO_V126_CAPTURED_INPUTS_FOUND')
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
    action.add_argument('--replay-recordings',metavar='DIR', help='Replay recorded v126 price and OI inputs')
    parser.add_argument('--replay-report',default='audit/replay_v126.json')
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
                append_audit(audit_dir/('market_scan_v126_'+datetime.now(IST).date().isoformat()+'.jsonl'),
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
