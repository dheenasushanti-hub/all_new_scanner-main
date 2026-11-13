#!/usr/bin/env python3
"""NIFTY OI-first analytical scanner v120.1.0 — single-file production candidate.

Completed price bars -> protected structure -> conditional forward scenarios ->
independent setup watches -> fixed risk plan -> one quoted option contract ->
chronological position management -> durable state and notification claims.

Python 3.11+ standard library only. Configuration is environment-backed. No README, auxiliary Python module,
installation package, regression code, or separate YAML is required at runtime.
This executable does not submit broker orders or claim calibrated win odds.
"""
from __future__ import annotations


# scanner/__init__.py
__version__ = '120.1.0'


# scanner/core.py
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta, timezone
from math import isfinite, log1p, ceil, floor
from statistics import median
from typing import Any
IST = timezone(timedelta(hours=5, minutes=30))

class DataError(ValueError):
    pass

def finite_json_float(value):
    """Reject numeric overflow as well as literal NaN/Infinity at ingress."""
    number = float(value)
    if not isfinite(number):
        raise ValueError('Non-finite numeric JSON')
    return number

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
            raise DataError('Candle timestamps must be timezone-aware minute starts')
        vals = (self.open, self.high, self.low, self.close, self.volume)
        if not all((isfinite(v) for v in vals)) or min(self.open, self.high, self.low, self.close) <= 0:
            raise DataError('Invalid candle prices')
        if self.high < max(self.open, self.close, self.low) or self.low > min(self.open, self.close, self.high) or self.volume < 0:
            raise DataError('Invalid candle OHLC or volume')

@dataclass(frozen=True)
class Config:
    max_risk: float = 30.0
    min_rr: float = 1.25
    max_quote_age: float = 45.0
    max_spread_pct: float = 2.0
    max_entry_extension_atr: float = 0.75
    min_bars: int = 6
    min_wall_fraction: float = 0.65
    strike_step: float = 50.0
    stop_buffer: float = 1.0
    no_progress_minutes: int = 12
    premium_hard_loss_pct: float = 25.0
    premium_runner_drawdown_pct: float = 18.0
    watch_minutes: int = 8
    min_stop_atr: float = 0.6
    max_entry_risk_fraction: float = 0.5
    runner_progress_atr: float = 0.3
    forecast_horizon_minutes: int = 15
    intraday_hard_exit_hour: int = 15
    intraday_hard_exit_minute: int = 15
    entry_cutoff_lead_minutes: int = 10
    # v119.1 configuration, documented engineering choices; not fitted probabilities.
    oi_nearby_points: float = 400.0
    oi_zone_half_width: float = 20.0  # 10–20pt causal OI price zones
    oi_material_change_fraction: float = 0.005
    oi_horizon_max_seconds: int = 3600
    min_option_volume: float = 1.0
    target_clearance_atr: float = 0.12
    min_intraday_projection_atr: float = 1.25
    max_option_iv: float = 200.0
    max_premium_cost_ratio: float = 0.65
    opening_oi_baseline_cutoff_minutes: int = 20
    depth_full_score_lots: float = 12.0
    premium_proxy_max_spread_pct: float = 15.0
    iv_shock_points: float = 1.0
    candle_publication_grace_seconds: float = 50.0
    candle_retry_interval_seconds: float = 2.0
    # v119.1 entry/target orchestration. These are deterministic engineering
    # constraints, not fitted probabilities or claims of future performance.
    reversal_acceptance_window_minutes: int = 12
    acceptance_hold_bars: int = 2
    acceptance_buffer_atr: float = 0.12
    max_target_projection_atr: float = 4.0
    one_itm_execution_tolerance: float = 0.06
    # v120.1: session-wide, independent price-action level tests. All values
    # are deterministic engineering thresholds; no statistically fitted edge.
    level_zone_atr: float = 0.28
    level_reset_atr: float = 0.65
    level_reaction_atr: float = 0.32
    level_independent_tests: int = 2
    level_stale_minutes: int = 390
    regime_window_minutes: int = 30
    sideways_efficiency_limit: float = 0.24
    entry_adverse_body_atr: float = 0.48
    entry_adverse_close_fraction: float = 0.36
    entry_near_level_atr: float = 1.20
    early_reversal_watch_minutes: int = 6
    # v119 entry quality: deterministic engineering thresholds, not fitted win odds.
    quote_adverse_atr: float = 0.42
    quote_adverse_min_points: float = 2.5
    quote_adverse_risk_fraction: float = 0.20
    quote_chase_atr: float = 0.85
    quote_chase_risk_fraction: float = 0.75
    recent_oi_touch_bars: int = 9
    oi_obstruction_min_relative: float = 0.65
    oi_obstruction_very_strong_relative: float = 0.90
    oi_touch_tolerance_atr: float = 0.35
    barrier_reward_safety_atr: float = 0.22
    last_minute_budget_atr_sqrt: float = 1.50
    last_minute_dispatch_buffer: float = 3.0
    minimum_entry_to_exit_minutes: float = 8.0
    reversal_short_window_bars: int = 3
    # v120.1: closed-price early discovery, impulse exhaustion and episode integrity.
    # Fixed engineering thresholds, not back-tested profitability estimates.
    early_recovery_body_atr: float = 0.18
    early_recovery_change_atr: float = 0.18
    early_recovery_retrace_atr: float = 0.55
    early_breakout_buffer_atr: float = 0.08
    early_max_pretrigger_leg_atr: float = 2.15
    early_watch_max_minutes: int = 5
    impulse_window_bars: int = 10
    impulse_extension_max_atr: float = 2.70
    impulse_recent_run_max_atr: float = 2.30
    impulse_reset_pullback_atr: float = 0.70
    impulse_reset_min_opposing_bars: int = 2
    impulse_min_age_bars: int = 3
    opportunity_journal_max_rows: int = 160

    def __post_init__(self):
        if not (10.0 <= self.oi_zone_half_width <= 20.0):
            raise DataError('OI_ZONE_HALF_WIDTH_MUST_BE_10_TO_20_POINTS')
        for value in (self.quote_adverse_atr,self.quote_adverse_min_points,
                      self.quote_adverse_risk_fraction,self.quote_chase_atr,
                      self.quote_chase_risk_fraction,self.oi_obstruction_min_relative,
                      self.oi_obstruction_very_strong_relative,self.oi_touch_tolerance_atr,
                      self.barrier_reward_safety_atr,self.last_minute_budget_atr_sqrt,
                      self.last_minute_dispatch_buffer,self.minimum_entry_to_exit_minutes):
            if not isfinite(value) or value <= 0:
                raise DataError('Invalid v119 entry quality configuration')
        for field in (self.early_recovery_body_atr,self.early_recovery_change_atr,
                      self.early_recovery_retrace_atr,self.early_breakout_buffer_atr,
                      self.early_max_pretrigger_leg_atr,self.impulse_extension_max_atr,
                      self.impulse_recent_run_max_atr,self.impulse_reset_pullback_atr):
            if not isfinite(field) or field <= 0 or field > 6:
                raise DataError('Invalid v119.1 opportunity parameter')
        if (not 2 <= self.early_watch_max_minutes <= 8 or
            not 6 <= self.impulse_window_bars <= 24 or
            not 1 <= self.impulse_reset_min_opposing_bars <= 3 or
            not 2 <= self.impulse_min_age_bars <= 7 or
            not 30 <= self.opportunity_journal_max_rows <= 600):
            raise DataError('Invalid v119.1 opportunity bounds')
        if (self.quote_adverse_atr > 1 or self.quote_chase_atr > 2 or
            self.quote_adverse_risk_fraction > 1 or self.quote_chase_risk_fraction > 2 or
            not 0.25 <= self.oi_obstruction_min_relative <= 1 or
            not self.oi_obstruction_min_relative <= self.oi_obstruction_very_strong_relative <= 1 or
            not 1 <= self.recent_oi_touch_bars <= 40 or
            not 2 <= self.reversal_short_window_bars <= 8 or
            self.minimum_entry_to_exit_minutes > 20 or self.last_minute_dispatch_buffer > 6):
            raise DataError('Invalid v119 entry quality parameter bounds')
        for field in (self.max_risk, self.min_rr, self.max_quote_age, self.max_spread_pct, self.max_entry_extension_atr, self.min_wall_fraction, self.strike_step, self.stop_buffer, self.premium_hard_loss_pct, self.premium_runner_drawdown_pct, self.min_stop_atr, self.runner_progress_atr, self.oi_nearby_points, self.oi_material_change_fraction, self.oi_horizon_max_seconds, self.min_option_volume, self.target_clearance_atr, self.min_intraday_projection_atr, self.max_option_iv, self.max_premium_cost_ratio, self.depth_full_score_lots, self.premium_proxy_max_spread_pct, self.iv_shock_points, self.candle_publication_grace_seconds, self.candle_retry_interval_seconds, self.acceptance_buffer_atr, self.max_target_projection_atr, self.one_itm_execution_tolerance, self.level_zone_atr, self.level_reset_atr, self.level_reaction_atr, self.sideways_efficiency_limit, self.entry_adverse_body_atr, self.entry_adverse_close_fraction, self.entry_near_level_atr):
            if not isfinite(field) or field <= 0:
                raise DataError('Invalid strategy configuration')
        if any((not isinstance(v, int) or isinstance(v, bool) for v in (self.min_bars, self.no_progress_minutes, self.watch_minutes, self.opening_oi_baseline_cutoff_minutes, self.reversal_acceptance_window_minutes, self.acceptance_hold_bars))) or self.min_wall_fraction > 1 or self.max_premium_cost_ratio >= 1 or self.oi_material_change_fraction >= 1 or self.min_bars < 6 or (self.no_progress_minutes < 1) or (self.watch_minutes < 1) or (self.opening_oi_baseline_cutoff_minutes < 1 or self.opening_oi_baseline_cutoff_minutes > 60) or (not 0 < self.max_entry_risk_fraction <= 1) or (max(self.premium_hard_loss_pct, self.premium_runner_drawdown_pct) >= 100):
            raise DataError('Invalid strategy configuration')
        if self.max_risk > 30 or self.min_rr < 1.25:
            raise DataError('Approved risk limits cannot be weakened')
        if not isinstance(self.forecast_horizon_minutes, int) or isinstance(self.forecast_horizon_minutes, bool) or (not 3 <= self.forecast_horizon_minutes <= 60):
            raise DataError('Invalid forecast horizon')
        if any((not isinstance(v, int) or isinstance(v, bool) for v in (self.intraday_hard_exit_hour, self.intraday_hard_exit_minute, self.entry_cutoff_lead_minutes))):
            raise DataError('Invalid intraday cutoff configuration')
        if not 0 <= self.intraday_hard_exit_hour <= 23 or not 0 <= self.intraday_hard_exit_minute <= 59 or not 3 <= self.entry_cutoff_lead_minutes <= 30:
            raise DataError('Invalid intraday cutoff configuration')
        if (self.intraday_hard_exit_hour, self.intraday_hard_exit_minute) != (15, 15):
            raise DataError('MANDATORY_1515_IST_HARD_EXIT_CANNOT_BE_OVERRIDDEN')
        if self.entry_cutoff_lead_minutes < 10:
            raise DataError('ENTRY_CUTOFF_MUST_BE_NO_LATER_THAN_1505_IST')
        if self.candle_publication_grace_seconds > 60 or self.candle_retry_interval_seconds > 10 or self.candle_retry_interval_seconds > self.candle_publication_grace_seconds:
            raise DataError('Invalid candle publication grace/retry configuration')
        if not 3 <= self.reversal_acceptance_window_minutes <= 30 or not 1 <= self.acceptance_hold_bars <= 3:
            raise DataError('Invalid acceptance-entry configuration')
        if self.acceptance_buffer_atr > 0.5 or not 1.25 <= self.max_target_projection_atr <= 6.0 or self.one_itm_execution_tolerance > 0.15:
            raise DataError('Invalid continuation target/contract configuration')
        if not (0.08 <= self.level_zone_atr <= 0.60 and
                0.35 <= self.level_reset_atr <= 1.5 and
                0.15 <= self.level_reaction_atr <= 0.80 and
                0.10 <= self.sideways_efficiency_limit <= 0.45 and
                0.30 <= self.entry_adverse_body_atr <= 1.2 and
                0.15 <= self.entry_adverse_close_fraction <= 0.45 and
                0.5 <= self.entry_near_level_atr <= 2.0):
            raise DataError('Invalid price-level/regime constraints')
        for number,lo,hi in ((self.level_independent_tests,2,4),
                             (self.level_stale_minutes,30,420),
                             (self.regime_window_minutes,15,90),
                             (self.early_reversal_watch_minutes,2,10)):
            if not isinstance(number,int) or isinstance(number,bool) or not lo <= number <= hi:
                raise DataError('Invalid price-action lookback/confirmation configuration')

def scan_candle_watermark(started: datetime) -> datetime:
    """Latest whole 1m candle that was complete when this scan began.

    This value is immutable for the scan.  Crossing a minute boundary while
    later API calls are running must not move the analytical candle universe.
    """
    if started.tzinfo is None:
        raise DataError('NAIVE_CANDLE_TIME')
    return started.astimezone(IST).replace(second=0, microsecond=0) - timedelta(minutes=1)

def candle_publication_deadline(required_start: datetime, grace_seconds: float) -> datetime:
    if required_start.tzinfo is None or not isfinite(float(grace_seconds)) or float(grace_seconds) <= 0:
        raise DataError('INVALID_CANDLE_PUBLICATION_POLICY')
    return required_start.astimezone(IST) + timedelta(minutes=1, seconds=float(grace_seconds))

def normalize_candles(raw: list[list[Any]], now: datetime, latest_allowed_start: datetime | None = None) -> list[Candle]:
    if now.tzinfo is None:
        raise DataError('naive evaluation time')
    now_ist = now.astimezone(IST)
    today = now_ist.date()
    if latest_allowed_start is not None and latest_allowed_start.tzinfo is None:
        raise DataError('NAIVE_CANDLE_TIME')
    cap = latest_allowed_start.astimezone(IST) if latest_allowed_start is not None else None
    by_time: dict[datetime, Candle] = {}
    for row in raw:
        if len(row) < 5:
            raise DataError('Malformed candle')
        t = datetime.fromisoformat(str(row[0]).replace('Z', '+00:00'))
        if t.tzinfo is None:
            raise DataError('Candle timestamp has no timezone')
        t = t.astimezone(IST)
        if t.date() != today or t + timedelta(minutes=1) > now_ist:
            continue
        if cap is not None and t > cap:
            continue
        c = Candle(t, *(float(v) for v in row[1:5]), float(row[5] or 0) if len(row) > 5 else 0.0)
        if t in by_time and by_time[t] != c:
            raise DataError('Conflicting duplicate candles')
        by_time[t] = c
    return [by_time[t] for t in sorted(by_time)]

def validate_latest_start(latest_start: datetime, now: datetime | None = None, required_start: datetime | None = None) -> None:
    if latest_start.tzinfo is None:
        raise DataError('NAIVE_CANDLE_TIME')
    if required_start is None:
        if now is None or now.tzinfo is None:
            raise DataError('NAIVE_CANDLE_TIME')
        required_start = scan_candle_watermark(now)
    elif required_start.tzinfo is None:
        raise DataError('NAIVE_CANDLE_TIME')
    if latest_start.astimezone(IST) != required_start.astimezone(IST):
        raise DataError('LATEST_COMPLETED_CANDLE_MISSING')

def validate_candles(bars: list[Candle], now: datetime | None = None, minimum: int=9, required_start: datetime | None = None) -> None:
    if len(bars) < minimum:
        raise DataError('INSUFFICIENT_CANDLES')
    validate_latest_start(bars[-1].start, now, required_start)
    for a, b in zip(bars, bars[1:]):
        if b.start - a.start != timedelta(minutes=1):
            raise DataError('CANDLE_GAP')

def contiguous_tail(bars: list[Candle]) -> tuple[list[Candle], int]:
    """Discard pre-gap history; management separately checks its full open interval."""
    cut = 0
    for i in range(1, len(bars)):
        if bars[i].start - bars[i - 1].start != timedelta(minutes=1):
            cut = i
    return (bars[cut:], cut)

def aggregate(bars: list[Candle], n: int) -> list[Candle]:
    groups: dict[datetime, list[Candle]] = {}
    for b in bars:
        start = b.start.replace(hour=9, minute=15, second=0, microsecond=0)
        elapsed = int((b.start - start).total_seconds() // 60)
        if elapsed < 0:
            continue
        slot = start + timedelta(minutes=elapsed // n * n)
        groups.setdefault(slot, []).append(b)
    result = []
    for t, g in sorted(groups.items()):
        if len(g) == n and all((c.start == t + timedelta(minutes=i) for i, c in enumerate(g))):
            result.append(Candle(t, g[0].open, max((x.high for x in g)), min((x.low for x in g)), g[-1].close, sum((x.volume for x in g))))
    return result

def atr(bars: list[Candle], n: int=14) -> float:
    ranges = []
    for i, c in enumerate(bars):
        prev = bars[i - 1].close if i else c.open
        ranges.append(max(c.high - c.low, abs(c.high - prev), abs(c.low - prev)))
    return sum(ranges[-n:]) / len(ranges[-n:]) if ranges else 0.0

def pivots(bars: list[Candle]) -> tuple[list[tuple[datetime, float]], list[tuple[datetime, float]]]:
    """Confirmed with one complete right-hand bar, so never see the future."""
    lows = []
    highs = []
    for i in range(2, len(bars) - 1):
        x = bars[i]
        if x.low < min(bars[i - 2].low, bars[i - 1].low) and x.low <= bars[i + 1].low:
            lows.append((x.start, x.low))
        if x.high > max(bars[i - 2].high, bars[i - 1].high) and x.high >= bars[i + 1].high:
            highs.append((x.start, x.high))
    return (lows, highs)


# ---------------------------------------------------------------------------
# v119.1 PRICE-ACTION LEVELS, PHASES AND CAUSAL ENTRY CONFLICT GATES
# ---------------------------------------------------------------------------

def _interaction_band(a: float, config: Config) -> float:
    """Volatility-relative zone, capped to avoid treating 50-point strikes as one."""
    return max(2.0, min(8.0, config.level_zone_atr * max(float(a), 1.0)))


def _price_level_anchors(bars: list[Candle], config: Config, prior_day=None) -> list[dict]:
    """Deterministic known-as-of anchors. Future pivots are never considered."""
    if not bars:
        return []
    low=min(b.low for b in bars); high=max(b.high for b in bars)
    step=config.strike_step
    floor_i=int(floor((low-step)/step)); ceil_i=int(ceil((high+step)/step))
    anchors: dict[float,set[str]]={}
    def add(price, source):
        if price is None:return
        try:
            val=float(price)
            if not isfinite(val) or val<=0 or val<low-2*step or val>high+2*step:return
            anchors.setdefault(round(val,4),set()).add(source)
        except (TypeError,ValueError):return
    # 50-point option strike grid must be recognized even when OI is absent.
    for i in range(floor_i,ceil_i+1):
        add(i*step,'ROUND_STRIKE_GRID')
    for key,level in (('OPENING_HIGH',max(b.high for b in bars[:min(6,len(bars))])),
                      ('OPENING_LOW',min(b.low for b in bars[:min(6,len(bars))]))):add(level,key)
    for i,bar in enumerate(bars):
        if i>0 and i<len(bars)-1:
            if bar.high>=max(bars[i-1].high,bars[i+1].high):
                add(bar.high,'CONFIRMED_1M_SWING_HIGH')
            if bar.low<=min(bars[i-1].low,bars[i+1].low):
                add(bar.low,'CONFIRMED_1M_SWING_LOW')
    threes=aggregate(bars,3)
    lows,highs=pivots(threes)
    for _,x in lows:add(x,'CONFIRMED_3M_PIVOT_LOW')
    for _,x in highs:add(x,'CONFIRMED_3M_PIVOT_HIGH')
    fifteens=aggregate(bars,15)
    lows,highs=pivots(fifteens)
    for _,x in lows:add(x,'CONFIRMED_15M_PIVOT_LOW')
    for _,x in highs:add(x,'CONFIRMED_15M_PIVOT_HIGH')
    for k in ('high','low','close'):
        if isinstance(prior_day,dict):add(prior_day.get(k),'PREVIOUS_SESSION_'+k.upper())
    # Avoid unbounded micro-pivots or quadratic work in multi-hour sessions.
    priority=lambda row:(0 if 'ROUND_STRIKE_GRID' in row[1] else 1,
                         0 if any('3M_' in x or '15M_' in x for x in row[1]) else 1,
                         -len(row[1]),row[0])
    rows=sorted(anchors.items(),key=priority)
    # Keep all round strikes, plus the most relevant measured swing levels.
    if len(rows)>180:
        rounds=[x for x in rows if 'ROUND_STRIKE_GRID' in x[1]]
        other=[x for x in rows if 'ROUND_STRIKE_GRID' not in x[1]]
        rows=rounds+other[:max(0,180-len(rounds))]
    return [{'price':p,'sources':sorted(sources)} for p,sources in sorted(rows)]


def build_price_action_ledger(bars: list[Candle], config: Config, prior_day=None) -> dict:
    """Replay independent price rejection/defense events over completed session.

    A new event requires price to move away from a zone for two complete bars
    before another test is counted. Consecutive wicks are *one* test, not two.
    The resulting ledger is deterministic from complete bars; no future prices,
    cached regime seeding, OI assumptions or broker executions are involved.
    """
    if not bars:return {'as_of':None,'levels':[],'resistances':[],'supports':[]}
    if any(b.start-a.start!=timedelta(minutes=1) for a,b in zip(bars,bars[1:])):
        raise DataError('PRICE_LEVEL_REPLAY_REQUIRES_CONTIGUOUS_BARS')
    rolling=[max(1.,atr(bars[max(0,i-13):i+1])) for i in range(len(bars))]
    threes=aggregate(bars,3)
    end=(bars[-1].start+timedelta(minutes=1))
    records=[]
    for anchor in _price_level_anchors(bars,config,prior_day):
        level=anchor['price'];r_armed=True;s_armed=True
        r_pending=None;s_pending=None;r_away=0;s_away=0
        r_events=[];s_events=[];touches_above=0;touches_below=0
        for i,c in enumerate(bars):
            a=rolling[i];band=_interaction_band(a,config)
            reset=max(1.5*band,config.level_reset_atr*a)
            react=max(band*0.75,config.level_reaction_atr*a)
            # Price must leave the tested zone before an independent retest.
            if c.high<level-band and c.close<level-reset:
                r_away+=1
            else:r_away=0
            if c.low>level+band and c.close>level+reset:
                s_away+=1
            else:s_away=0
            if r_away>=2:
                r_armed=True;r_pending=None
            if s_away>=2:
                s_armed=True;s_pending=None
            prev_close=bars[i-1].close if i else c.open
            if r_armed and c.high>=level-band and min(c.open,prev_close)<=level+band:
                r_pending={'index':i,'high':c.high,'tested_at':c.start.isoformat()}
                r_armed=False;touches_above+=1
            if s_armed and c.low<=level+band and max(c.open,prev_close)>=level-band:
                s_pending={'index':i,'low':c.low,'tested_at':c.start.isoformat()}
                s_armed=False;touches_below+=1
            if r_pending is not None:
                r_pending['high']=max(r_pending['high'],c.high)
                if c.close<=level-react and r_pending['high']>=level-band:
                    r_events.append({'tested_at':r_pending['tested_at'],
                        'confirmed_at':(c.start+timedelta(minutes=1)).isoformat(),
                        'extreme':round(r_pending['high'],4),
                        'reaction_close':round(c.close,4),
                        'false_breakout_wick':bool(r_pending['high']>level+band)})
                    r_pending=None
                elif i-r_pending['index']>6:r_pending=None
            if s_pending is not None:
                s_pending['low']=min(s_pending['low'],c.low)
                if c.close>=level+react and s_pending['low']<=level+band:
                    s_events.append({'tested_at':s_pending['tested_at'],
                        'confirmed_at':(c.start+timedelta(minutes=1)).isoformat(),
                        'extreme':round(s_pending['low'],4),
                        'reaction_close':round(c.close,4),
                        'false_breakdown_wick':bool(s_pending['low']<level-band)})
                    s_pending=None
                elif i-s_pending['index']>6:s_pending=None
        last_a=max(1.,rolling[-1]);zone=_interaction_band(last_a,config)
        acceptance_up=[];acceptance_down=[]
        for x,y in zip(threes,threes[1:]):
            if x.close>level+zone and y.close>level+zone:
                acceptance_up.append((y.start+timedelta(minutes=3)).isoformat())
            if x.close<level-zone and y.close<level-zone:
                acceptance_down.append((y.start+timedelta(minutes=3)).isoformat())
        last_up=acceptance_up[-1] if acceptance_up else None
        last_down=acceptance_down[-1] if acceptance_down else None
        last_r=r_events[-1]['confirmed_at'] if r_events else None
        last_s=s_events[-1]['confirmed_at'] if s_events else None
        r_fresh=bool(last_r and (end-datetime.fromisoformat(last_r)).total_seconds()<=60*config.level_stale_minutes)
        s_fresh=bool(last_s and (end-datetime.fromisoformat(last_s)).total_seconds()<=60*config.level_stale_minutes)
        # An accepted breakout invalidates earlier rejections. A later failed
        # return below can reinstate them only through fresh price rejection.
        r_valid=bool(r_fresh and (not last_up or last_r>last_up))
        s_valid=bool(s_fresh and (not last_down or last_s>last_down))
        status_r=('CONFIRMED' if r_valid and len(r_events)>=config.level_independent_tests
                  else 'OBSERVED' if r_valid and r_events else 'UNCONFIRMED')
        status_s=('CONFIRMED' if s_valid and len(s_events)>=config.level_independent_tests
                  else 'OBSERVED' if s_valid and s_events else 'UNCONFIRMED')
        records.append({'price':level,'sources':anchor['sources'],
            'zone_half_width':round(zone,4),'resistance_status':status_r,
            'support_status':status_s,'resistance_rejections':len(r_events),
            'support_defenses':len(s_events),'resistance_touches':touches_above,
            'support_touches':touches_below,
            'false_breakouts_rejected':sum(bool(x.get('false_breakout_wick')) for x in r_events),
            'false_breakdowns_reclaimed':sum(bool(x.get('false_breakdown_wick')) for x in s_events),
            'last_resistance_at':last_r,
            'last_support_at':last_s,'accepted_above_at':last_up,
            'accepted_below_at':last_down,'accepted_above_now':bool(last_up and
                bars[-1].close>level+zone and (not last_r or last_up>last_r)),
            'accepted_below_now':bool(last_down and
                bars[-1].close<level-zone and (not last_s or last_down>last_s)),
            'resistance_events':r_events[-5:],'support_events':s_events[-5:]})
    spot=bars[-1].close
    resistances=[x for x in records if x['resistance_status']!='UNCONFIRMED' and x['price']>=spot-x['zone_half_width']]
    supports=[x for x in records if x['support_status']!='UNCONFIRMED' and x['price']<=spot+x['zone_half_width']]
    resistances.sort(key=lambda x:(x['price']-spot,-x['resistance_rejections']))
    supports.sort(key=lambda x:(spot-x['price'],-x['support_defenses']))
    return {'as_of':end.isoformat(),'levels':records,
            'resistances':resistances,'supports':supports,
            'replay_bars':len(bars),'method':'COMPLETE_1M_REPLAY_INDEPENDENT_RETESTS_AND_TWO_3M_ACCEPTANCES'}


def classify_market_phase(bars: list[Candle], structure: dict, ledger: dict,
                          config: Config) -> dict:
    """Trading regime is distinct from the protected directional thesis.

    A trend may become balanced or range-bound without a confirmed reversal.
    Conversely, a one-minute rejection cannot silently reverse the thesis.
    """
    recent=bars[-config.regime_window_minutes:]
    a=max(1.,atr(bars));span=max(x.high for x in recent)-min(x.low for x in recent)
    work=sum(abs(x.close-x.open) for x in recent)
    efficiency=abs(recent[-1].close-recent[0].open)/max(work,1.)
    spot=bars[-1].close
    recent_rejections=[x for x in ledger.get('resistances',[])
                       if x['resistance_status']=='CONFIRMED']
    recent_defenses=[x for x in ledger.get('supports',[])
                     if x['support_status']=='CONFIRMED']
    paired=[]
    for sup in recent_defenses:
        for res in recent_rejections:
            width=res['price']-sup['price']
            if max(a,config.strike_step*.7)<=width<=max(8*a,3*config.strike_step):
                if sup['price']-sup['zone_half_width']<=spot<=res['price']+res['zone_half_width']:
                    paired.append((width,sup,res))
    # Prefer well-established outer boundaries over tiny incidental internal
    # swings. Round strikes and multi-test levels carry more evidence; a wide
    # confirmed channel is not replaced by the narrowest micro pivot pair.
    def pair_quality(item):
        width,support,resistance=item
        events=min(int(support['support_defenses']),int(resistance['resistance_rejections']))
        major=int('ROUND_STRIKE_GRID' in support['sources'])+int('ROUND_STRIKE_GRID' in resistance['sources'])
        higher_tf=int(any('3M' in s or '15M' in s for s in support['sources']))+int(any('3M' in s or '15M' in s for s in resistance['sources']))
        return (major*3+min(4,events)*2+higher_tf, min(width/max(1.,a),5.),width)
    active_pair=max(paired,key=pair_quality) if paired else None
    trend=structure.get('direction','RANGE')
    r3=structure.get('recent_3m');r15=structure.get('context_15m')
    latest=bars[-1]
    adverse=latest_candle_adverse(latest,trend,spot,a,config)
    if structure.get('pending_break'):
        phase='REVERSAL_PENDING'
    elif active_pair and efficiency<=config.sideways_efficiency_limit*1.6:
        phase='RANGE'
    elif (trend in ('BULLISH','BEARISH') and r3 in ('BULLISH','BEARISH')
          and r3!=trend and (r15!=trend or adverse)):
        # Tactical reversal warning is earlier than thesis reversal: one
        # completed 3m opposite plus 1m rejection is sufficient to suspend
        # trend entries, but NOT to assert a new protected trend.
        phase='REVERSAL_WARNING'
    elif trend in ('BULLISH','BEARISH') and adverse:
        phase='MOMENTUM_CONFLICT'
    elif trend in ('BULLISH','BEARISH') and efficiency<=config.sideways_efficiency_limit and len(recent)>=15:
        phase='BALANCED_UNCONFIRMED'
    elif trend in ('BULLISH','BEARISH'):
        phase=trend+'_TREND'
    else:
        phase='RANGE' if active_pair else 'BALANCED_UNCONFIRMED'
    return {'phase':phase,'protected_thesis':trend,'recent_3m':r3,'context_15m':r15,
        'recent_efficiency':round(efficiency,5),'recent_span':round(span,5),
        'atr_1m':round(a,5),'confirmed_range':bool(active_pair),
        'range_support':active_pair[1]['price'] if active_pair else None,
        'range_resistance':active_pair[2]['price'] if active_pair else None,
        'latest_candle_adverse':adverse,
        'method':'SEPARATE_PROTECTED_THESIS_FROM_TRADING_REGIME'}


def latest_candle_adverse(bar: Candle, direction: str, live_spot: float,
                          a: float, config: Config) -> bool:
    """A substantial opposite closing candle cannot be rescued by an old watch."""
    sign=1 if direction=='BULLISH' else -1 if direction=='BEARISH' else 0
    if not sign:return False
    adverse_body=-sign*(bar.close-bar.open)
    spread=max(bar.high-bar.low,1e-8)
    closing_side=(bar.close-bar.low)/spread if sign==1 else (bar.high-bar.close)/spread
    # Recovery of the opposite candle requires a fresh confirming signal;
    # a live quote slightly beyond the old trigger does not reset this veto.
    spot_recovered=sign*(live_spot-bar.open)>max(0.5,0.12*a)
    return (adverse_body>=config.entry_adverse_body_atr*a and
            closing_side<=config.entry_adverse_close_fraction and
            not spot_recovered)


def _level_reaction_setup(bars: list[Candle], structure: dict, context: dict,
                          config: Config) -> list[dict]:
    """Construct range or early reversal opportunities from *completed* prices.

    In a protected countertrend, the newest 3m must also align with the
    proposed tactical move. A single opposite candle is only a watch, never
    automatic evidence of a tradable structural reversal.
    """
    if len(bars)<max(6,config.min_bars):return []
    c=bars[-1];p=bars[-2];spot=c.close
    phase=context.get('market_phase') or {};ledger=context.get('price_action_ledger') or {}
    a=max(1.,atr(bars));out=[]
    if phase.get('phase') not in ('RANGE','REVERSAL_WARNING','REVERSAL_PENDING'):
        return []
    for direction in ('BULLISH','BEARISH'):
        sign=1 if direction=='BULLISH' else -1
        opposing=(ledger.get('supports',[]) if sign==1 else ledger.get('resistances',[]))
        signal_kind=('RANGE_SUPPORT_RECLAIM' if sign==1 else 'RANGE_RESISTANCE_REJECTION')
        if phase.get('phase')!='RANGE':
            if direction==structure.get('direction'):continue
            signal_kind=('EARLY_SUPPORT_REVERSAL' if sign==1 else 'EARLY_RESISTANCE_REVERSAL')
        # Confirmed price reaction at a level that was independently retested.
        candidates=[]
        for z in opposing:
            status=z['support_status' if sign==1 else 'resistance_status']
            if status!='CONFIRMED':continue
            lvl=float(z['price']);band=float(z['zone_half_width'])
            if abs(lvl-c.close)>max(config.entry_near_level_atr*a,1.7*band):continue
            if sign==1 and min(x.low for x in bars[-2:])>lvl+band:continue
            if sign==-1 and max(x.high for x in bars[-2:])<lvl-band:continue
            candidates.append(z)
        if not candidates:continue
        if structure.get('recent_3m')!=direction:continue
        if sign*(c.close-c.open)<0.30*a:continue
        if sign*(c.close-p.close)<0.25*a:continue
        zone=min(candidates,key=lambda x:abs(float(x['price'])-spot))
        stop=(min(x.low for x in bars[-3:])-config.stop_buffer if sign==1
              else max(x.high for x in bars[-3:])+config.stop_buffer)
        if sign*(spot-stop)<=0:continue
        confirmed=(c.start+timedelta(minutes=1)).isoformat()
        kind='SUPPORT' if sign==1 else 'RESISTANCE'
        out.append({'direction':direction,'kind':signal_kind,'trigger':spot,
            'confirmed_at':confirmed,'invalidation':stop,
            'trade_invalidation':stop,'atr_1m':a,
            'stop_role':'LOCAL_COMPLETED_PRICE_REACTION',
            'protected_thesis_boundary':structure.get('support' if sign==1 else 'resistance'),
            'thesis_invalidation':{'level':structure.get('support' if sign==1 else 'resistance'),
                                  'requires':'CONFIRMED_PROTECTED_STRUCTURE_BREAK'},
            'three_confirmed_at':(datetime.fromisoformat(structure['last_3m'])+timedelta(minutes=3)).isoformat(),
            'dependencies':[{'kind':'PRICE_ACTION_ZONE','direction':direction,
                             'role':kind,'level':float(zone['price']),
                             'min_events':config.level_independent_tests}],
            'evidence':['INDEPENDENT_LEVEL_TESTS','COMPLETED_1M_REJECTION_OR_RECLAIM',
                        'COMPLETED_3M_DIRECTION','TACTICAL_DIRECTION_SEPARATE_FROM_PROTECTED_THESIS']})
    return out

def classify_flow(old_oi: float, new_oi: float, old_price: float, new_price: float, side: str) -> str:
    """Price/OI pattern only; it does not identify initiators or participant positions."""
    if side not in {'CE', 'PE'} or not all((isfinite(x) for x in (old_oi, new_oi, old_price, new_price))) or min(old_oi, new_oi, old_price, new_price) <= 0:
        return 'UNAVAILABLE'
    dp = (new_price - old_price) / old_price
    doi = (new_oi - old_oi) / old_oi
    if abs(dp) < 0.005 or abs(doi) < 0.005:
        return 'UNCHANGED_OR_NOISY'
    return {(True, True): 'LONG_BUILDUP_HYPOTHESIS', (True, False): 'SHORT_COVERING_HYPOTHESIS', (False, True): 'SHORT_BUILDUP_HYPOTHESIS', (False, False): 'LONG_UNWINDING_HYPOTHESIS'}[dp > 0, doi > 0]

# v118 STRATEGY RESEARCH IMPLEMENTATION.
# All regime inference, setups, watches, risk and contract ranking below were
# designed independently of the previous release's trading functions.
# Provider, wire format and persistence facilities are retained for compatibility.

def oi_context(chain: list[dict[str, Any]], spot: float, config: Config) -> dict[str, Any]:
    """Identify near-spot CE resistance and PE support candidates.

    OI magnitude alone never sets trade direction. Contract identity and expiry
    are retained so any setup that depends on an OI wall can be revalidated on
    later scans against the same contract rather than a merely similar strike.
    """
    output = {'put_support': None, 'call_resistance': None, 'walls': [],
              'meaning': 'Candidate CE resistance / PE support, subject to price test and comparability'}
    for side, label in (('PE','put_support'), ('CE','call_resistance')):
        subset = [r for r in chain if r.get('side') == side
                  and abs(float(r['strike'])-spot) <= config.oi_nearby_points
                  and float(r.get('oi') or 0) > 0]
        if not subset:
            continue
        peak = max(float(r['oi']) for r in subset)
        typical = median(float(r['oi']) for r in subset)
        if peak < max(1, typical) * 1.20 and len(subset) >= 4:
            continue
        candidates=[]
        for r in subset:
            strike=float(r['strike']); oi=float(r['oi']); strength=oi/peak
            if strength < config.min_wall_fraction:
                continue
            candidates.append({'instrument_key': r.get('instrument_key'),
                               'expiry': r.get('expiry'),
                               'strike': strike,'side':side,'oi':oi,
                               'relative_to_side_max':round(strength,5),
                               'interpretation':'POTENTIAL_SUPPORT' if side=='PE' else 'POTENTIAL_RESISTANCE',
                               'location':'BELOW' if strike < spot else 'ABOVE' if strike > spot else 'AT_SPOT'})
        candidates.sort(key=lambda x:(abs(x['strike']-spot),-x['oi']))
        output['walls'].extend(candidates[:6])
        preferred=[c for c in candidates if (c['strike']<=spot if side=='PE' else c['strike']>=spot)]
        if preferred:
            output[label]=dict(preferred[0])
    output['walls'].sort(key=lambda x:(x['side'], x['strike']))
    return output



def _structure_at(bars: list[Candle]) -> dict[str, Any]:
    """Causal one-pass 3m structure; a boundary can only move upon defended pivots.

    A single 3m close through the defended boundary creates a *pending* break;
    acceptance requires later independent completed candles beyond the level.
    No OI or 15m observation may flip the protected regime by itself.
    """
    if len(bars) < 6:
        raise DataError('OPENING_CANDLE_WARMUP')
    if any(y.start-x.start != timedelta(minutes=1) for x,y in zip(bars,bars[1:])):
        raise DataError('CANDLE_GAP')
    threes = aggregate(bars,3)
    fifteens = aggregate(bars,15)
    if len(threes) < 2:
        raise DataError('COMPLETED_3M_UNAVAILABLE')
    first = threes[:2]
    direction = 'RANGE'
    beginning = first[0].start
    established_at = None
    reversal = None
    pending = None
    support = min(x.low for x in first)
    resistance = max(x.high for x in first)
    boundary_source = 'OPENING_TWO_3M_EXTREMES'
    price_atr = max(atr(bars[:6]), 1.0)
    displacement = first[-1].close-first[0].open
    open_threshold = max(2.0,0.8*price_atr)
    if abs(displacement) >= open_threshold and (first[1].close-first[0].close)*displacement >= 0:
        direction = 'BULLISH' if displacement > 0 else 'BEARISH'
        established_at = (first[-1].start+timedelta(minutes=3)).isoformat()
    prior = first[:]
    pending_accepts = 0
    last_reason = 'OPENING_STRUCTURE' if direction != 'RANGE' else 'OPENING_RANGE'
    # Fold each completed 3m without looking at the remainder of the session.
    for i in range(2,len(threes)):
        c = threes[i]
        end = c.start+timedelta(minutes=3)
        history = threes[:i+1]
        window_atr = max(atr(history[-6:]),1.0)
        buffer = max(1.0,0.12*window_atr)
        # A three-bar confirmed swing uses only the immediately completed right bar.
        confirmed_low = history[-2].low if len(history)>=3 and history[-2].low < history[-3].low and history[-2].low <= history[-1].low else None
        confirmed_high = history[-2].high if len(history)>=3 and history[-2].high > history[-3].high and history[-2].high >= history[-1].high else None
        if direction == 'RANGE':
            # Range must first break on a closed 3m bar, then demonstrate acceptance.
            side = 'BULLISH' if c.close > resistance+buffer else 'BEARISH' if c.close < support-buffer else None
            if side:
                if pending and pending['direction'] == side:
                    pending_accepts += 1
                else:
                    pending = {'direction':side,'level':resistance if side=='BULLISH' else support,
                               'first_at':end.isoformat(),'type':'RANGE_BREAK'}
                    pending_accepts = 0
                if pending_accepts>=1:
                    direction=side
                    established_at=end.isoformat()
                    last_reason='RANGE_BREAK_ACCEPTED'
                    pending=None
                    pending_accepts=0
                    boundary_source='CONFIRMED_RANGE_BOUNDARY'
            else:
                if pending and ((pending['direction']=='BULLISH' and c.close<=resistance) or
                                (pending['direction']=='BEARISH' and c.close>=support)):
                    pending=None
                    pending_accepts=0
                    last_reason='FALSE_RANGE_BREAK'
                if pending is None:
                    support=min(support,c.low)
                    resistance=max(resistance,c.high)
            continue
        sign = 1 if direction=='BULLISH' else -1
        level = support if sign==1 else resistance
        crossed = sign*(c.close-level)<-buffer
        reclaimed = sign*(c.close-level)>buffer
        if crossed:
            next_direction = 'BEARISH' if sign==1 else 'BULLISH'
            if pending is None or pending['direction']!=next_direction:
                pending={'direction':next_direction,'level':level,'first_at':end.isoformat(),
                         'type':'PROTECTED_BOUNDARY_BREAK'}
                pending_accepts=0
                last_reason='PROTECTED_BREAK_PENDING'
            else:
                pending_accepts+=1
            if pending_accepts>=1:
                # Independent subsequent completed 3m acceptance: not a single wick.
                old = direction
                direction=next_direction
                reversal={'direction':direction,'old_direction':old,'level':level,
                          'confirmed_at':end.isoformat(),'evidence':'TWO_SEPARATE_CLOSED_3M_BEYOND_DEFENDED_LEVEL'}
                established_at=end.isoformat()
                last_reason='SUPPORT_BREAK_CONFIRMED' if old=='BULLISH' else 'RESISTANCE_BREAK_CONFIRMED'
                boundary_source='ACCEPTED_REVERSAL_PIVOT'
                pending=None
                pending_accepts=0
                if direction=='BULLISH':
                    support=min(x.low for x in history[-2:])
                    resistance=max(x.high for x in history[-4:])
                else:
                    resistance=max(x.high for x in history[-2:])
                    support=min(x.low for x in history[-4:])
            continue
        if pending and reclaimed:
            last_reason='FALSE_PROTECTED_BREAK_RECLAIMED'
            pending=None
            pending_accepts=0
        # Only a significant, fully defended new swing can ratchet protected levels.
        if pending is None and established_at and end > datetime.fromisoformat(established_at):
            if direction=='BULLISH' and confirmed_low is not None and confirmed_low > support:
                impulse_high=max(x.high for x in history[-4:-1])
                significance=impulse_high-confirmed_low
                if significance >= max(5,0.9*window_atr) and c.close>history[-2].high+buffer:
                    support=confirmed_low
                    boundary_source='DEFENDED_CONFIRMED_3M_HIGHER_LOW'
                    last_reason='SUPPORT_ADVANCED_AFTER_IMPULSE'
            elif direction=='BEARISH' and confirmed_high is not None and confirmed_high < resistance:
                impulse_low=min(x.low for x in history[-4:-1])
                significance=confirmed_high-impulse_low
                if significance >= max(5,0.9*window_atr) and c.close<history[-2].low-buffer:
                    resistance=confirmed_high
                    boundary_source='DEFENDED_CONFIRMED_3M_LOWER_HIGH'
                    last_reason='RESISTANCE_ADVANCED_AFTER_IMPULSE'
    last3=threes[-1]
    recent3='BULLISH' if last3.close>last3.open and last3.close>threes[-2].close else 'BEARISH' if last3.close<last3.open and last3.close<threes[-2].close else 'MIXED'
    if direction=='BULLISH':
        phase = 'BULL_SUPPORT_TEST' if pending else 'BULL_TREND' if recent3=='BULLISH' else 'BULL_PULLBACK'
    elif direction=='BEARISH':
        phase = 'BEAR_RESISTANCE_TEST' if pending else 'BEAR_TREND' if recent3=='BEARISH' else 'BEAR_BOUNCE'
    else:
        phase='RANGE'
    low_piv,high_piv=pivots(threes)
    long_low,long_high=pivots(fifteens)
    context='DEVELOPING'
    if len(fifteens)>=2:
        context='BULLISH' if fifteens[-1].close>fifteens[-2].close else 'BEARISH' if fifteens[-1].close<fifteens[-2].close else 'SIDEWAYS'
    return {'engine_revision':1191,'direction':direction,'state':phase,'support':support,
            'resistance':resistance,'boundary_source':boundary_source,'pending_break':pending,
            'break_confirmed':reversal is not None and last_reason in ('SUPPORT_BREAK_CONFIRMED','RESISTANCE_BREAK_CONFIRMED'),
            'last_reversal':reversal,'reason':last_reason,'established_at':established_at,
            'established_confirmed_at':established_at,'recent_3m':recent3,
            'atr_1m':max(atr(bars),1.0),'atr_3m':max(atr(threes),1.0),
            'last_3m':last3.start.isoformat(),'last_3m_close':last3.close,
            'context_15m':context,'confirmed_pivot_low':low_piv[-1][1] if low_piv else None,
            'confirmed_pivot_high':high_piv[-1][1] if high_piv else None,
            'confirmed_15m_pivot_low':long_low[-1][1] if long_low else None,
            'confirmed_15m_pivot_high':long_high[-1][1] if long_high else None,
            'processed_1m':bars[-1].start.isoformat(),'history_start':bars[0].start.isoformat(),
            'buffer':max(1.0,0.12*max(atr(threes[-6:]),1.0)),
            'price_efficiency':abs(bars[-1].close-bars[0].open)/max(1,sum(abs(b.close-b.open) for b in bars))}


def update_structure(bars, old=None):
    """Cold start and hot scan give identical as-of regime from complete session bars.

    `old` is never used as a strategy seed: obsolete states cannot contaminate
    new calculations. The source candle range must be continuous.
    """
    return _structure_at(bars)


def _round_directional_target(value: float, direction: str, step: float) -> float:
    """Round a forward projection outward to the live strike grid."""
    if not all(isfinite(float(x)) and float(x) > 0 for x in (value, step)):
        raise DataError('INVALID_TARGET_ROUNDING_INPUT')
    scaled=float(value)/float(step)
    return float(ceil(scaled-1e-12)*step if direction=='BULLISH' else floor(scaled+1e-12)*step)


def forecast_market(bars, structure, spot, oi, futures=None, config=None):
    """Explain the evolving thesis as conditional scenarios, never guarantees.

    v119.1 deliberately distinguishes a *forecast hurdle* from a target-limiting
    barrier. Potential OI concentrations and historical pivots are surfaced,
    but they do not automatically cap a directional continuation objective
    unless later price/OI evidence upgrades them to a hard barrier.
    """
    config=config or Config()
    d=structure['direction']; pending=structure.get('pending_break')
    boundary=structure.get('support') if d=='BULLISH' else structure.get('resistance') if d=='BEARISH' else None
    if not structure.get('boundary_trusted',True):
        primary='SESSION_STRUCTURE_INCOMPLETE'
    elif pending:
        primary='DEFENDED_BOUNDARY_UNDER_TEST_WAIT_ACCEPTANCE'
    elif d=='BULLISH':
        primary='BULLISH_CONTINUATION' if structure.get('recent_3m')==d else 'BULLISH_PULLBACK_RECOVERY_CONDITIONAL'
    elif d=='BEARISH':
        primary='BEARISH_CONTINUATION' if structure.get('recent_3m')==d else 'BEARISH_BOUNCE_REJECTION_CONDITIONAL'
    else:
        primary='RANGE_RECLAIM_OR_REJECTION'
    evidence=[]; cautions=[]; scenarios=[]
    mixed_oi=oi.get('price_oi_interpretation') or {}
    evidence.extend(mixed_oi.get('evidence') or [])
    cautions.extend(mixed_oi.get('cautions') or [])

    def targets_for(direction):
        sign=1 if direction=='BULLISH' else -1
        rows=[]
        for level in oi.get('levels') or []:
            try:
                px=float(level['price'])
                if sign*(px-spot)<=0.25: continue
                source=str(level.get('source') or level.get('kind') or 'LEVEL')
                rows.append((abs(px-spot), px, source, bool(level.get('hard_barrier') or level.get('price_rejection_confirmed'))))
            except (KeyError,TypeError,ValueError):
                continue
        rows.sort(key=lambda x:(x[0],x[1]))
        result=[]
        for _,px,source,hard in rows[:2]:
            result.append({'level':round(px,5),'source':source,'role':'HARD_BARRIER' if hard else 'SOFT_INTERMEDIATE_HURDLE'})
        a=max(float(structure.get('atr_1m') or atr(bars) or 1),1.0)
        recent=float(oi.get('recent_impulse_height') or 0)
        thesis_leg=0.0
        try:
            if boundary is not None:
                thesis_leg=abs(float(bars[-1].close)-float(boundary))
        except (TypeError,ValueError):
            thesis_leg=0.0
        projection=max(config.min_intraday_projection_atr*a,
                       min(max(recent,thesis_leg),config.max_target_projection_atr*a) if max(recent,thesis_leg)>0 else 0)
        projected=_round_directional_target(spot+sign*projection,direction,config.strike_step)
        if sign*(projected-spot)>0.25 and all(abs(projected-x['level'])>1e-6 for x in result):
            result.append({'level':round(projected,5),'source':'CAUSAL_CONTINUATION_PROJECTION','role':'CONTINUATION_OBJECTIVE'})
        return result[:3]

    common_entry=['COMPLETED_1M_ACCEPTANCE_OR_FRESH_PRICE_TRIGGER','LATEST_COMPLETED_3M_CONFIRMATION','ENTRY_NOT_STALE_OR_CHASED']
    if d in ('BULLISH','BEARISH'):
        evidence.append('DEFENDED_PRICE_STRUCTURE_'+d)
        if structure.get('recent_3m')==d:evidence.append('LAST_COMPLETED_3M_ALIGNED')
        else:cautions.append('WAIT_FOR_PRICE_RESUMPTION')
        if structure.get('context_15m')==d:evidence.append('COMPLETED_15M_ALIGNED')
        elif structure.get('context_15m')!='DEVELOPING':cautions.append('15M_MIXED_OR_OPPOSED')
        wall=oi.get('put_support' if d=='BULLISH' else 'call_resistance') or {}
        if oi.get('fresh_snapshot') and float(wall.get('oi_change') or 0)>0:evidence.append('NEAR_DEFENDED_OI_WALL_STRENGTHENS')
        pattern=(futures or {}).get('price_oi_pattern')
        supportive={'LONG_BUILDUP_HYPOTHESIS','SHORT_COVERING_HYPOTHESIS'} if d=='BULLISH' else {'SHORT_BUILDUP_HYPOTHESIS','LONG_UNWINDING_HYPOTHESIS'}
        if pattern in supportive:evidence.append('FUTURES_PRICE_OI_HYPOTHESIS_COMPATIBLE')
        elif pattern and pattern not in ('UNAVAILABLE','UNCHANGED_OR_NOISY'):cautions.append('FUTURES_FLOW_MIXED')
        recent_reversal=structure.get('last_reversal') or {}
        if recent_reversal.get('direction')==d:
            try:
                if datetime.fromisoformat((bars[-1].start+timedelta(minutes=1)).isoformat())-datetime.fromisoformat(recent_reversal['confirmed_at']) <= timedelta(minutes=config.reversal_acceptance_window_minutes):
                    evidence.append('RECENT_CONFIRMED_REVERSAL_ACCEPTANCE_WINDOW')
            except (ValueError,TypeError,KeyError):
                pass
        alt='BEARISH' if d=='BULLISH' else 'BULLISH'
        scenarios=[
            {'name':'CONTINUATION_OR_PULLBACK_RESUMPTION','direction':d,
             'entry_conditions':common_entry+['PROTECTED_LEVEL_HOLDS','FORMER_RESISTANCE_SUPPORT_OR_ACCEPTANCE_LEVEL_HOLDS','PRICE_RECOVERS_OR_CONTINUES_IN_THESIS_DIRECTION'],
             'invalidation':{'type':'PROTECTED_STRUCTURE','level':boundary,
                             'requires':'TWO_SEPARATE_COMPLETED_3M_CLOSES_BEYOND_DEFENDED_LEVEL'},
             'potential_targets':targets_for(d),
             'supporting_evidence':list(evidence),'status':'WATCH' if not pending else 'BLOCKED_PENDING_BREAK'},
            {'name':'GENUINE_REVERSAL','direction':alt,
             'entry_conditions':['MEANINGFUL_BREAK_OF_PROTECTED_STRUCTURE','TWO_SEPARATE_COMPLETED_3M_ACCEPTANCES_BEYOND_PROTECTED_LEVEL','FRESH_COMPLETED_1M_ACCEPTANCE_OR_TRIGGER_AFTER_REVERSAL','NO_STALE_WATCH_REUSE'],
             'invalidation':{'type':'FAILED_REVERSAL','level':boundary,'requires':'PRICE_RECLAIMS_OR_REJECTS_BROKEN_BOUNDARY'},
             'potential_targets':targets_for(alt),
             'supporting_evidence':['OPPOSITE_ENTRY_REQUIRES_CONFIRMED_STRUCTURE_CHANGE'],
             'status':'WAIT_CONFIRMATION' if d!=alt else 'WATCH'}]
    else:
        for wall,side,name in (('put_support','BULLISH','RANGE_SUPPORT_RECLAIM'),('call_resistance','BEARISH','RANGE_RESISTANCE_REJECTION')):
            level=oi.get(wall) or {}
            if level:
                scenarios.append({'name':name,'direction':side,
                    'entry_conditions':['PRICE_TEST_OF_RANGE_OR_OI_LEVEL','COMPLETED_1M_RECLAIM_OR_REJECTION','LATEST_COMPLETED_3M_CONFIRMATION'],
                    'invalidation':{'type':'FAILED_RANGE_REACTION','level':level.get('strike'),'requires':'PRICE_ACCEPTS_THROUGH_TESTED_LEVEL'},
                    'potential_targets':targets_for(side),
                    'supporting_evidence':['RANGE_SIDES_EVALUATED_INDEPENDENTLY',level.get('interpretation','POTENTIAL_OI_LEVEL')],
                    'status':'WATCH'})
    if not structure.get('boundary_trusted',True):cautions.append('SESSION_OPENING_HISTORY_MISSING')
    if pending:cautions.append('NO_COUNTERTREND_ENTRY_WHILE_BREAK_IS_UNCONFIRMED')
    return {'as_of':(bars[-1].start+timedelta(minutes=1)).isoformat(),
            'primary_scenario':primary,'directional_thesis':d,'protected_boundary':boundary,
            'invalidation_requires':'TWO_SEPARATE_CLOSED_3M_ACCEPTANCES_BEYOND_DEFENDED_PRICE_LEVEL',
            'entry_readiness':'ASSESS_ACCEPTANCE_OR_TRIGGER' if structure.get('boundary_trusted',True) and not pending and structure.get('recent_3m')==d and d!='RANGE' else 'WAIT',
            'supporting_evidence':evidence,'cautions':cautions,'scenarios':scenarios,
            'spot':spot,'conditional_analysis_not_prediction_guarantee':True}


def enrich_oi_context(context, comparison, bars, spot, fresh=True, config=None, price_ledger=None):
    """Attach matched OI change, price tests and premium observations to OI walls."""
    config=config or Config()
    output=dict(context, fresh_snapshot=bool(fresh), comparability=comparison.get('status'),
                opening_baseline_status=comparison.get('opening_baseline_status'))
    matched=comparison.get('nearby_changes') or []
    baseline=comparison.get('session_baseline_oi_changes') or []
    index={(x.get('side'),float(x['strike'])):x for x in matched}
    baseline_index={(x.get('side'),float(x['strike'])):x for x in baseline}
    output['atr_1m']=max(atr(bars),1.0)
    expanded=[]
    for row in context.get('walls',[]):
        wall=dict(row); side=wall['side']; strike=wall['strike']
        near=index.get((side,strike)); longer=baseline_index.get((side,strike))
        change=near.get('oi_change') if near else None
        wall.update(oi_change=change,
                    oi_change_pct=100*change/near['previous_oi'] if near and near.get('previous_oi') else None,
                    session_oi_change=longer.get('oi_change') if longer else None,
                    pattern=near.get('classification') if near else 'UNAVAILABLE')
        if near:
            wall['premium_observation']={k:near.get(k) for k in (
                'premium_change_pct','greek_adjusted_residual_pct','premium_change_source',
                'premium_source_quality','flow_price_source')}
        # OI is supporting evidence. Independent completed PRICE tests are
        # sufficient for a price barrier even with declining or unavailable OI.
        levels=(price_ledger or {}).get('levels') or []
        match=next((x for x in levels if abs(float(x['price'])-float(strike))<=0.001),None)
        role='support_status' if side=='PE' else 'resistance_status'
        events='support_defenses' if side=='PE' else 'resistance_rejections'
        tests=int(match.get(events) or 0) if match else 0
        confirmed=bool(match and match.get(role)=='CONFIRMED')
        wall['price_test_count']=tests
        wall['price_rejection_confirmed']=confirmed
        growing_oi=(bool(fresh and near and near.get('previous_oi') and change is not None)
                    and float(change)/float(near['previous_oi'])>=config.oi_material_change_fraction)
        wall['hard_barrier']=bool(confirmed)
        wall['barrier_status']='PRICE_CONFIRMED' if confirmed else ('OI_BUILDUP_UNCONFIRMED_PRICE' if growing_oi else 'POTENTIAL')
        expanded.append(wall)
    output['walls']=expanded
    for label,side in (('put_support','PE'),('call_resistance','CE')):
        item=output.get(label)
        output[label]=next((x for x in expanded if item and x['strike']==item['strike'] and x['side']==side),None)
    output['oi_horizons']=comparison.get('horizons',[])
    output['opening_baseline_fetched_at']=comparison.get('opening_baseline_fetched_at')
    return output



def price_oi_evidence(context, comparison, structure, spot):
    """Interpret matched price/OI patterns as hypotheses, never participant intent."""
    price_thesis=structure.get('direction')
    report={'bias':'NEUTRAL','evidence':[],'cautions':[],'horizon_count':len(comparison.get('horizons') or []),
            'source_quality':comparison.get('status','BASELINE_ONLY'),
            'opening_baseline_status':comparison.get('opening_baseline_status'),
            'participant_intent_inferred':False,'premium_oi_observations':[]}
    votes={'BULLISH':0.0,'BEARISH':0.0}
    for w in context.get('walls',[]):
        oi=float(w.get('oi') or 0); relative=float(w.get('relative_to_side_max') or 0); change=w.get('oi_change')
        if change is None or not oi:continue
        interval_change=float(change)/max(1.,oi)
        if abs(interval_change)<0.005:continue
        strike=float(w['strike']); price_near=abs(spot-strike)<=max(20.,context.get('atr_1m',1.)*1.5)
        if not price_near:continue
        premium=w.get('premium_observation') or {}
        if premium:
            report['premium_oi_observations'].append({'side':w['side'],'strike':strike,**premium,
                'interpretation':'OBSERVATION_ONLY_NOT_DIRECTIONAL_VETO'})
        if w['side']=='PE' and spot>=strike:
            if interval_change>0 and w.get('price_test_count',0)>0:
                report['evidence'].append('PE_OI_INCREASE_AT_HELD_SUPPORT');votes['BULLISH']+=min(relative,1.)
            elif interval_change<0 and spot-strike<context.get('atr_1m',1.)*0.6:report['cautions'].append('NEARBY_PE_SUPPORT_OI_DECREASES')
        elif w['side']=='CE' and spot<=strike:
            if interval_change>0 and w.get('price_test_count',0)>0:
                report['evidence'].append('CE_OI_INCREASE_AT_REJECTED_RESISTANCE');votes['BEARISH']+=min(relative,1.)
            elif interval_change<0 and strike-spot<context.get('atr_1m',1.)*0.6:report['cautions'].append('OVERHEAD_CE_OI_DECREASES')
    if votes['BULLISH']>votes['BEARISH']+0.5:report['bias']='BULLISH_SUPPORT_HYPOTHESIS'
    elif votes['BEARISH']>votes['BULLISH']+0.5:report['bias']='BEARISH_RESISTANCE_HYPOTHESIS'
    if price_thesis=='BULLISH' and report['bias']=='BEARISH_RESISTANCE_HYPOTHESIS':report['cautions'].append('OI_RESISTANCE_VS_BULLISH_STRUCTURE_PRICE_CONFIRMATION_REQUIRED')
    if price_thesis=='BEARISH' and report['bias']=='BULLISH_SUPPORT_HYPOTHESIS':report['cautions'].append('OI_SUPPORT_VS_BEARISH_STRUCTURE_PRICE_CONFIRMATION_REQUIRED')
    report['votes']=votes
    return report

ACCEPTANCE_SETUP_KINDS = {
    'POST_REVERSAL_ACCEPTANCE_CONTINUATION',
    'TREND_ACCEPTANCE_CONTINUATION',
}

# Pure momentum/breakout entries may become stale after rapid extension.
# Acceptance/reclaim/recovery setups are structure-led: their eligibility is
# governed by the still-valid tactical stop, dependencies and live RR rather
# than by a universal ATR chase cap.
CHASE_SENSITIVE_SETUP_KINDS = {
    'OPENING_MOMENTUM',
    'TREND_BREAKOUT',
    'ACCEPTED_RANGE_BREAKOUT',
    'ACCEPTED_RANGE_BREAKDOWN',
}


def _accepted_price_level(structure, side, close, a):
    """Return the nearest already-crossed price level whose acceptance matters.

    The broad protected thesis boundary remains a dependency, but a continuation
    trade should normally be invalidated by the local accepted/retested price
    structure rather than by a much more distant session thesis boundary.
    """
    sign=1 if side=='BULLISH' else -1
    tolerance=max(0.5,min(2.5,0.18*max(a,1.0)))
    rows=[]
    rev=structure.get('last_reversal') or {}
    if rev.get('direction')==side and rev.get('level') is not None:
        rows.append(('CONFIRMED_REVERSAL_BREAK_LEVEL',float(rev['level'])))
    if side=='BULLISH':
        for source,key in (('FORMER_STRUCTURE_RESISTANCE','resistance'),('CONFIRMED_3M_PIVOT_HIGH','confirmed_pivot_high'),('CONFIRMED_15M_PIVOT_HIGH','confirmed_15m_pivot_high')):
            value=structure.get(key)
            if value is not None and float(value)<=close+tolerance:
                rows.append((source,float(value)))
        if not rows:return None,None
        source,level=max(rows,key=lambda x:x[1])
    else:
        for source,key in (('FORMER_STRUCTURE_SUPPORT','support'),('CONFIRMED_3M_PIVOT_LOW','confirmed_pivot_low'),('CONFIRMED_15M_PIVOT_LOW','confirmed_15m_pivot_low')):
            value=structure.get(key)
            if value is not None and float(value)>=close-tolerance:
                rows.append((source,float(value)))
        if not rows:return None,None
        source,level=min(rows,key=lambda x:x[1])
    # Do not call a level accepted if it is actually on the wrong side.
    if sign*(close-level)<-tolerance:
        return None,None
    return level,source


def _candidate_at(bars, structure, config, context):
    """Generate causal entry setups from completed 1m and closed 3m only.

    v119.1 retains an explicit post-reversal/trend acceptance path. A confirmed
    directional structure does not have to prove itself again by printing a
    fresh micro-breakout above the immediately preceding 1m high. Instead, an
    accepted former resistance/support level plus an aligned completed 3m bar
    may qualify, subject to the same live extension, dependency and risk gates.
    """
    if len(bars)<config.min_bars or len(aggregate(bars,3))<2:return []
    c,p=bars[-1],bars[-2]; d=structure['direction']; a=max(atr(bars),1.0)
    t=(c.start+timedelta(minutes=1)).isoformat(); threes=aggregate(bars,3)
    last_completed=(threes[-1].start+timedelta(minutes=3))
    if c.start+timedelta(minutes=1)-last_completed>timedelta(minutes=5):return []
    results=[]
    for side in ('BULLISH','BEARISH'):
        sign=1 if side=='BULLISH' else -1; trend=d==side and not structure.get('pending_break')
        if d in ('BULLISH','BEARISH') and not trend:continue
        three=threes[-1]
        if side=='BULLISH':
            three_aligned=three.close>three.open and three.close>=threes[-2].close
            body=c.close-c.open; momentum=(c.close>p.high and c.close>=p.close)
            recovery=(c.low<=p.low+0.15*a and c.close>p.high and p.close<=p.open)
            price_stop=min(x.low for x in bars[-3:])-config.stop_buffer
            level=context.get('put_support') or {}; wall=level.get('strike')
            wall_reclaim=wall is not None and min(x.low for x in bars[-4:])<=wall+0.3*a and c.close>wall+0.1*a and c.close>p.high
            boundary=structure.get('support'); reaction_level=p.low; oi_side='PE'
        else:
            three_aligned=three.close<three.open and three.close<=threes[-2].close
            body=c.open-c.close; momentum=(c.close<p.low and c.close<=p.close)
            recovery=(c.high>=p.high-0.15*a and c.close<p.low and p.close>=p.open)
            price_stop=max(x.high for x in bars[-3:])+config.stop_buffer
            level=context.get('call_resistance') or {}; wall=level.get('strike')
            wall_reclaim=wall is not None and max(x.high for x in bars[-4:])>=wall-0.3*a and c.close<wall-0.1*a and c.close<p.low
            boundary=structure.get('resistance'); reaction_level=p.high; oi_side='CE'

        # Early recovery has a separate price trigger: a closed 1m rebound
        # after a genuine short counter-direction pullback, with the completed
        # 3m already aligned. A new high/low beyond the preceding wick is NOT
        # required. The quality/target gates will still reject stale or
        # counter-structural entries. This does not flip a protected thesis.
        pullback_seen=any(sign*(x.close-x.open)<=-0.18*a for x in bars[-5:-1])
        recovered_body=sign*(c.close-c.open)>=0.22*a
        recovered_close=sign*(c.close-p.close)>=0.20*a
        reclaimed_middle=sign*(c.close-(p.open+p.close)/2)>=0.10*a
        not_yet_broken_previous_extreme=(c.close<=p.high if sign==1 else c.close>=p.low)
        early_pullback=(trend and three_aligned and len(bars)>=9 and pullback_seen
                        and recovered_body and recovered_close and reclaimed_middle
                        and not_yet_broken_previous_extreme)

        kinds=[]
        acceptance_level=None; acceptance_source=None; acceptance_kind=None
        if trend and three_aligned:
            acceptance_level,acceptance_source=_accepted_price_level(structure,side,c.close,a)
            if acceptance_level is not None:
                buffer=max(0.5,min(2.0,config.acceptance_buffer_atr*a))
                recent=bars[-3:]
                accepted=sum(1 for x in recent if sign*(x.close-acceptance_level)>=-0.25*buffer)
                latest_holds=sign*(c.close-acceptance_level)>=buffer
                three_holds=sign*(three.close-acceptance_level)>=buffer
                non_opposing=sign*(c.close-c.open)>=-0.15*a
                prior_near_or_below=sign*(threes[-2].close-acceptance_level)<=max(buffer,0.20*a)
                if accepted>=config.acceptance_hold_bars and latest_holds and three_holds and non_opposing and prior_near_or_below:
                    recent_reversal=structure.get('last_reversal') or {}
                    reversal_fresh=False
                    if recent_reversal.get('direction')==side and recent_reversal.get('confirmed_at'):
                        try:
                            reversal_fresh=datetime.fromisoformat(t)-datetime.fromisoformat(recent_reversal['confirmed_at'])<=timedelta(minutes=config.reversal_acceptance_window_minutes)
                        except (ValueError,TypeError):
                            reversal_fresh=False
                    acceptance_kind='POST_REVERSAL_ACCEPTANCE_CONTINUATION' if reversal_fresh else 'TREND_ACCEPTANCE_CONTINUATION'
                    kinds.append(acceptance_kind)

        # Existing momentum/recovery paths remain available, but their body
        # threshold is intentionally not imposed on the acceptance path above.
        if body>=max(0.4,0.1*a) and three_aligned:
            if trend and boundary is not None and sign*(c.close-boundary)<=0:
                pass
            elif trend:
                if momentum:
                    prev_range=bars[-6:-1]; prior_extreme=max(x.high for x in prev_range) if sign==1 else min(x.low for x in prev_range)
                    kinds.append('TREND_BREAKOUT' if sign*(c.close-prior_extreme)>0 else 'OPENING_MOMENTUM' if len(bars)<=12 else 'TREND_CONTINUATION')
                if recovery or wall_reclaim:kinds.append('TREND_SUPPORT_RECLAIM' if sign==1 else 'TREND_RESISTANCE_REJECTION')
                if early_pullback:
                    kinds.append('TREND_PULLBACK_RECOVERY')
                protected=structure.get('support' if sign==1 else 'resistance')
                if protected is not None and any((x.low < protected if sign==1 else x.high > protected) for x in bars[-4:-1]) and sign*(c.close-protected)>0 and momentum:kinds.insert(0,'FALSE_BREAK_RECLAIM' if sign==1 else 'FALSE_BREAK_REJECTION')
                if structure.get('reason')=='RANGE_BREAK_ACCEPTED' and momentum:kinds.insert(0,'ACCEPTED_RANGE_BREAKOUT' if sign==1 else 'ACCEPTED_RANGE_BREAKDOWN')
                recent_reversal=structure.get('last_reversal') or {}
                if recent_reversal.get('direction')==side and recent_reversal.get('confirmed_at'):
                    try:
                        if datetime.fromisoformat(t)-datetime.fromisoformat(recent_reversal['confirmed_at'])<=timedelta(minutes=config.reversal_acceptance_window_minutes) and momentum:
                            kinds.insert(0,'CONFIRMED_REVERSAL')
                    except (ValueError,TypeError):
                        pass
            else:
                if wall_reclaim or recovery:kinds=['RANGE_SUPPORT_RECLAIM' if sign==1 else 'RANGE_RESISTANCE_REJECTION']

        for kind in dict.fromkeys(kinds):
            # Tactical stop is local and setup-specific. The much broader
            # protected thesis boundary is persisted separately as a dependency.
            invalid=price_stop
            if kind in ACCEPTANCE_SETUP_KINDS and acceptance_level is not None:
                local_window=bars[-3:]
                invalid=(min(x.low for x in local_window)-config.stop_buffer if sign==1
                         else max(x.high for x in local_window)+config.stop_buffer)
            if side=='BULLISH' and invalid>=c.close or side=='BEARISH' and invalid<=c.close:continue
            dependencies=[]
            if trend and boundary is not None:
                dependencies.append({'kind':'PROTECTED_STRUCTURE','direction':side,'level':float(boundary),
                                     'role':'SUPPORT' if sign==1 else 'RESISTANCE','source':structure.get('boundary_source')})
            if kind in ACCEPTANCE_SETUP_KINDS and acceptance_level is not None:
                dependencies.append({'kind':'PRICE_ACCEPTANCE_LEVEL','direction':side,'level':float(acceptance_level),
                                     'role':'FORMER_RESISTANCE_ACCEPTED_AS_SUPPORT' if sign==1 else 'FORMER_SUPPORT_ACCEPTED_AS_RESISTANCE',
                                     'source':acceptance_source})
            if wall_reclaim and wall is not None:
                dependencies.append({'kind':'OI_WALL','direction':side,'side':oi_side,'strike':float(wall),
                                     'instrument_key':level.get('instrument_key'),'expiry':level.get('expiry'),
                                     'relative_strength_at_creation':level.get('relative_to_side_max'),
                                     'barrier_status_at_creation':level.get('barrier_status','POTENTIAL')})
            elif (recovery or kind=='TREND_PULLBACK_RECOVERY') and kind not in ACCEPTANCE_SETUP_KINDS:
                dependencies.append({'kind':'PRICE_REACTION_LEVEL','direction':side,'level':float(reaction_level),
                                     'role':'PULLBACK_LOW_RECLAIM' if sign==1 else 'BOUNCE_HIGH_REJECTION'})
            evidence=['COMPLETE_1M_TRIGGER_OR_ACCEPTANCE','COMPLETED_3M_DIRECTION','PROTECTED_REGIME_OR_RANGE_LEVEL']
            if kind in ACCEPTANCE_SETUP_KINDS:
                evidence.extend(['FORMER_LEVEL_ACCEPTED_ON_COMPLETED_PRICE','TACTICAL_TRADE_INVALIDATION_SEPARATE_FROM_THESIS_INVALIDATION'])
            if wall_reclaim:evidence.append('CURRENT_OI_WALL_PRICE_REACTION')
            if kind=='TREND_PULLBACK_RECOVERY':
                evidence.append('EARLY_PULLBACK_RECLAIM_CLOSED_1M_AND_ALIGNED_COMPLETED_3M')
            results.append({'direction':side,'kind':kind,'trigger':c.close,'confirmed_at':t,'invalidation':invalid,
                            'trade_invalidation':invalid,'atr_1m':a,'stop_role':'LOCAL_COMPLETED_1M_PRICE_STRUCTURE',
                            'protected_thesis_boundary':boundary,
                            'thesis_invalidation':{'level':boundary,'requires':'CONFIRMED_PROTECTED_STRUCTURE_BREAK'} if boundary is not None else None,
                            'acceptance_level':acceptance_level if kind in ACCEPTANCE_SETUP_KINDS else None,
                            'acceptance_source':acceptance_source if kind in ACCEPTANCE_SETUP_KINDS else None,
                            'confirmation_locked':kind in ACCEPTANCE_SETUP_KINDS,
                            'three_confirmed_at':last_completed.isoformat(),'dependencies':dependencies,'evidence':evidence})
    return results


def _early_trend_price_setups(bars: list[Candle], structure: dict,
                              context: dict, config: Config) -> list[dict]:
    """A causal earlier entry candidate is not a retrospective profitable trade.

    One closed 1m reaction after a genuine pullback (or a new short breakout),
    plus the *last completed* 3m direction and the defended structural thesis.
    Supports both long and short and does not use the current unfinished minute,
    future OI, future prices or the eventual trade outcome.
    """
    if len(bars)<max(config.min_bars,9) or len(aggregate(bars,3))<2:
        return []
    if structure.get('pending_break'):
        return []
    d=structure.get('direction')
    if d not in ('BULLISH','BEARISH') or structure.get('recent_3m')!=d:
        return []
    side=1 if d=='BULLISH' else -1
    a=max(1.,atr(bars)); c,p=bars[-1],bars[-2]
    threes=aggregate(bars,3)
    last_3m=threes[-1]
    aligned=(side*(last_3m.close-last_3m.open)>0 and
             side*(last_3m.close-threes[-2].close)>=0)
    if not aligned:
        return []
    boundary=structure.get('support' if side==1 else 'resistance')
    if boundary is None or side*(c.close-float(boundary))<=0:
        return []
    # Pullback is a completed counter-direction move, not just a wick.
    recent=bars[-6:-1]
    adverse=[x for x in recent if side*(x.close-x.open)<-0.12*a]
    prior_extreme=(max(x.high for x in recent) if side==1 else min(x.low for x in recent))
    pullback_distance=max(0.,side*(prior_extreme-p.close))
    rebound=(side*(c.close-c.open)>=config.early_recovery_body_atr*a and
             side*(c.close-p.close)>=config.early_recovery_change_atr*a and
             side*(c.close-(p.open+p.close)/2)>0)
    recovery=(bool(adverse) and rebound and
              pullback_distance>=config.early_recovery_retrace_atr*a and
              side*(c.close-prior_extreme)<=0)
    # Breakout based on *previous closed candles*. Do not wait for an
    # additional full 3m after the already-confirmed aligned bar.
    last_three=bars[-4:-1]
    old_extreme=max(x.high for x in last_three) if side==1 else min(x.low for x in last_three)
    breakout=(side*(c.close-old_extreme)>=config.early_breakout_buffer_atr*a and
              side*(c.close-c.open)>=config.early_recovery_body_atr*a)
    if not recovery and not breakout:
        return []
    if breakout and not recovery:
        recent_leg=(side*(c.close-(min(x.low for x in bars[-6:]) if side==1
                                   else max(x.high for x in bars[-6:]))))
        if recent_leg>config.early_max_pretrigger_leg_atr*a:
            return []
    kind='EARLY_TREND_PULLBACK_RECOVERY' if recovery else 'EARLY_TREND_BREAKOUT'
    stop=(min(x.low for x in bars[-3:])-config.stop_buffer if side==1 else
          max(x.high for x in bars[-3:])+config.stop_buffer)
    risk=side*(c.close-stop)
    if not 0<risk<=config.max_risk:
        return []
    # The early signal is allowed to confirm with the completed 3m; a previous
    # one-minute counter-candle does not flip the defended thesis.
    accepted_level=None
    for level in (context.get('price_action_ledger') or {}).get('levels',[]):
        price=float(level.get('price') or 0)
        accepted=level.get('accepted_above_now' if side==1 else 'accepted_below_now')
        if accepted and side*(c.close-price)>0 and abs(c.close-price)<=max(2*a,12.):
            accepted_level=price
            break
    confirm=(c.start+timedelta(minutes=1)).isoformat()
    dependencies=[{'kind':'PROTECTED_STRUCTURE','direction':d,'level':float(boundary),
                   'role':'SUPPORT' if side==1 else 'RESISTANCE',
                   'source':structure.get('boundary_source')}]
    if recovery:
        # Reference the previous 1m *close* rather than a high that has not
        # been reclaimed. The protective stop still comes from real lows/highs.
        dependencies.append({'kind':'PRICE_REACTION_LEVEL','direction':d,
                             'level':p.close,'role':'EARLY_PULLBACK_RECLAIM'})
    if accepted_level is not None:
        dependencies.append({'kind':'PRICE_ACCEPTANCE_LEVEL','direction':d,
                             'level':accepted_level,'source':'TWO_CLOSED_3M_ACCEPTANCE'})
    return [{'direction':d,'kind':kind,'trigger':c.close,'confirmed_at':confirm,
             'invalidation':stop,'trade_invalidation':stop,'atr_1m':a,
             'stop_role':'LOCAL_COMPLETED_EARLY_1M_PRICE_REACTION',
             'three_confirmed_at':(last_3m.start+timedelta(minutes=3)).isoformat(),
             'confirmation_locked':False,'accepted_level':accepted_level,
             'protected_thesis_boundary':float(boundary),
             'thesis_invalidation':{'level':float(boundary),
                                   'requires':'CONFIRMED_PROTECTED_STRUCTURE_BREAK'},
             'dependencies':dependencies,
             'evidence':['CAUSAL_COMPLETE_1M_EARLY_SIGNAL','ALIGNED_COMPLETED_3M',
                         'PRESERVED_PROTECTED_THESIS','LOCAL_UNCLIPPED_RISK_STOP'],
             'setup_discovery_method':'V1191_EARLY_CLOSED_PRICE'}]


def directional_impulse_gate(setup: dict, bars: list[Candle], live_spot: float,
                             config: Config) -> tuple[bool,str,dict]:
    """Bound an *episode*, not only the newest setup's trigger displacement.

    A new micro-breakdown at the end of a multi-ATR impulse is not a new
    opportunity. Only a material closed-candle counter-direction pullback
    with at least two adverse bars can reset its reference swing. This rule
    is symmetric for bullish and bearish moves and never backdates data.
    """
    if len(bars)<config.impulse_window_bars or setup.get('direction') not in ('BULLISH','BEARISH'):
        return True,'INSUFFICIENT_EPISODE_HISTORY_OR_NO_DIRECTION',{}
    direction=setup['direction'];sign=1 if direction=='BULLISH' else -1
    a=max(1.,atr(bars));window=bars[-config.impulse_window_bars:]
    # Use only closed candle bodies for the reset, not transient quote spikes.
    reset_at=None
    consecutive=0;reset_range=0.
    for i in range(1,len(window)):
        delta=sign*(window[i].close-window[i-1].close)
        if delta<0:
            consecutive+=1;reset_range+=-delta
        else:
            if consecutive>=config.impulse_reset_min_opposing_bars and reset_range>=config.impulse_reset_pullback_atr*a:
                reset_at=i-1
            consecutive=0;reset_range=0.
    if consecutive>=config.impulse_reset_min_opposing_bars and reset_range>=config.impulse_reset_pullback_atr*a:
        reset_at=len(window)-1
    leg=window[reset_at:] if reset_at is not None and reset_at<len(window)-2 else window
    # A valid reset should start on the pullback extremum, or shortly after.
    if reset_at is not None and reset_at<len(window)-2:
        leg=window[reset_at:]
    first=leg[0];last=leg[-1]
    from_origin=sign*(live_spot-first.open)
    move=max(0.,from_origin)
    six=bars[-6:]
    short_move=max(0.,sign*(live_spot-six[0].open))
    episode_age=(last.start-first.start).total_seconds()/60
    is_recovery=setup.get('kind') in ('EARLY_TREND_PULLBACK_RECOVERY','TREND_PULLBACK_RECOVERY',
                                     'TREND_SUPPORT_RECLAIM','TREND_RESISTANCE_REJECTION',
                                     'RANGE_SUPPORT_RECLAIM','RANGE_RESISTANCE_REJECTION')
    # Recovery is not an unconditional bypass: its own confirmed pullback
    # must be measurable from closed candle prices.
    valid_recovery=bool(is_recovery and reset_at is not None and
                        reset_at<len(window)-1 and len(leg)>=2)
    diagnostics={'episode_origin':first.start.isoformat(),
                 'origin_price':first.open,'episode_age_minutes':episode_age,
                 'move_from_origin_points':round(move,4),
                 'move_from_origin_atr':round(move/a,4),
                 'last_six_move_atr':round(short_move/a,4),
                 'material_reset_at':window[reset_at].start.isoformat() if reset_at is not None else None,
                 'confirmed_pullback_recovery':valid_recovery}
    if (not valid_recovery and len(leg)>=config.impulse_min_age_bars and
        move>config.impulse_extension_max_atr*a):
        return False,'DIRECTIONAL_IMPULSE_ALREADY_EXTENDED',diagnostics
    if not valid_recovery and short_move>config.impulse_recent_run_max_atr*a:
        return False,'FAST_IMPULSE_EXHAUSTION_NO_PULLBACK',diagnostics
    return True,'DIRECTIONAL_EPISODE_WITHIN_ENTRY_WINDOW',diagnostics


def observe_opportunities(state: dict, setups: list[dict], now: datetime,
                          latest_closed_bar: Candle, config: Config) -> None:
    """Persist observed opportunities at scan time, with no retroactive fills.

    A setup found via historical bar reconstruction is first *observed* now,
    not at its earlier bar's close. Preserve rejection and selection history.
    """
    records=state.setdefault('opportunity_journal',[])
    if not isinstance(records,list):
        raise StateError('INVALID_OPPORTUNITY_JOURNAL')
    keyset={r.get('key') for r in records if isinstance(r,dict)}
    for s in setups:
        try:
            confirmed=datetime.fromisoformat(s['confirmed_at'])
            if confirmed>now or confirmed>latest_closed_bar.start+timedelta(minutes=1):
                raise DataError('OPPORTUNITY_FUTURE_CONFIRMATION')
            signature='|'.join([str(s['direction']),str(s['kind']),s['confirmed_at'],
                                str(round(float(s['trigger']),4))])
            key=hashlib.sha256(signature.encode()).hexdigest()[:20]
            if key in keyset:continue
            records.append({'key':key,'direction':s['direction'],'kind':s['kind'],
                            'confirmed_at':s['confirmed_at'],'first_observed_at':now.isoformat(),
                            'confirmed_bar_price':float(s['trigger']),
                            'status':'OBSERVED_NOT_EXECUTED'})
            keyset.add(key)
        except DataError:
            raise
        except (KeyError,TypeError,ValueError):
            raise DataError('MALFORMED_OPPORTUNITY_RECORD') from None
    state['opportunity_journal']=records[-config.opportunity_journal_max_rows:]


def mark_opportunity(state: dict, candidate: dict, status: str, reason: str,
                     at: datetime) -> None:
    for item in reversed(state.get('opportunity_journal') or []):
        if (item.get('direction')==candidate.get('direction') and
            item.get('kind')==candidate.get('kind') and
            item.get('confirmed_at')==candidate.get('confirmed_at') and
            item.get('confirmed_bar_price')==candidate.get('trigger')):
            item['last_evaluated_at']=at.isoformat()
            item['status']=status
            item['last_reason']=reason
            break


def make_setups(bars, structure, spot, config, context):
    result=[]
    for back in range(min(3,len(bars)-config.min_bars+1)):
        prefix=bars[:len(bars)-back] if back else bars
        asof=_structure_at(prefix)
        # Current chain was captured after earlier candles; do not backdate it.
        # Reconstructed historical signals may only use completed price bars.
        historical_context = context if not back else {}
        for setup in _candidate_at(prefix,asof,config,historical_context):
            # A later completed candle cannot validate an earlier setup if its stop was touched.
            follow=bars[len(prefix):]
            sign=1 if setup['direction']=='BULLISH' else -1
            if any(c.low<=setup['invalidation'] if sign==1 else c.high>=setup['invalidation'] for c in follow):continue
            result.append(setup)
    return result


def make_setup(bars, structure, spot, config, context=None):
    choices=make_setups(bars,structure,spot,config,context or {})
    return choices[0] if choices else None


def gate_candidate(setup, structure, context=None):
    d=setup.get('direction'); thesis=structure.get('direction')
    if d not in ('BULLISH','BEARISH'):return False,'INVALID_DIRECTION'
    context=context or {}
    phase=(context.get('market_phase') or {}).get('phase')
    kind=str(setup.get('kind') or '')
    # A twice-rejected/defended price-action zone blocks directional entry
    # from within that zone until independently accepted beyond it.
    # Do this *before* the range and countertrend fast paths as well.
    live_spot=context.get('spot_live')
    if live_spot is not None:
        sign=1 if d=='BULLISH' else -1
        status='resistance_status' if sign==1 else 'support_status'
        for level_row in (context.get('price_action_ledger') or {}).get('levels',[]):
            if level_row.get(status)!='CONFIRMED':continue
            zone=float(level_row.get('zone_half_width') or 0)
            ahead=sign*(float(level_row['price'])-float(live_spot))
            if -zone <= ahead <= zone:
                return False,'ENTRY_INSIDE_UNACCEPTED_CONFIRMED_PRICE_ZONE'
    if phase=='RANGE':
        if kind.startswith('RANGE_'):
            # A range label is not permission to buy against a defended bearish
            # thesis or sell against a defended bullish thesis. v118/v119.0
            # bypassed this check, including the 14:25 countertrend CE case.
            if thesis in ('BULLISH','BEARISH') and d!=thesis:
                return False,'PROTECTED_THESIS_OPPOSES_COUNTERTREND_RANGE_ENTRY'
            if not (context.get('market_phase') or {}).get('confirmed_range'):
                return False,'RANGE_BOUNDARIES_NOT_INDEPENDENTLY_CONFIRMED'
            if structure.get('recent_3m')!=d:
                return False,'RANGE_REACTION_REQUIRES_COMPLETED_3M_ALIGNMENT'
            return True,'RANGE_REACTION_WITH_PROTECTED_STRUCTURE'
        if kind.startswith('EARLY_TREND_') and thesis==d and not structure.get('pending_break'):
            # An aligned early reaction can be considered in consolidation,
            # but *only* with a completed accepted boundary, never from inside
            # an unaccepted two-test resistance/support zone.
            if not setup.get('accepted_level') or structure.get('recent_3m')!=d:
                return False,'RANGE_REQUIRES_ACCEPTED_EARLY_TREND_BREAK'
            return True,'EARLY_TREND_FROM_ACCEPTED_RANGE_BOUNDARY'
        return False,'RANGE_REQUIRES_REACTION_SETUP'
    if kind.startswith('RANGE_'):
        return False,'RANGE_NO_LONGER_CONFIRMED'
    if kind.startswith('EARLY_') and not kind.startswith('EARLY_TREND_'):
        expected='BULLISH' if 'SUPPORT' in kind else 'BEARISH'
        if phase not in ('REVERSAL_WARNING','REVERSAL_PENDING') or d!=expected or d==thesis:
            return False,'EARLY_REVERSAL_REQUIRES_CONFIRMED_LEVEL_AND_PHASE'
        if structure.get('recent_3m')!=d:
            return False,'EARLY_REVERSAL_REQUIRES_OPPOSING_COMPLETED_3M'
        return True,'EARLY_TACTICAL_REVERSAL_NOT_PROTECTED_TREND_FLIP'
    if structure.get('pending_break'):
        return False,'PROTECTED_BOUNDARY_BREAK_UNCONFIRMED'
    if phase in ('REVERSAL_WARNING','BALANCED_UNCONFIRMED'):
        return False,'TREND_ENTRY_BLOCKED_BY_MARKET_TRANSITION'
    if thesis=='RANGE':
        return False,'UNCONFIRMED_RANGE_DIRECTION'
    if thesis!=d:return False,'PROTECTED_THESIS_OPPOSES_ENTRY'
    level=structure.get('support' if d=='BULLISH' else 'resistance')
    if level is not None and setup.get('trigger') is not None and (1 if d=='BULLISH' else -1)*(float(setup['trigger'])-float(level))<=0:
        return False,'PROTECTED_LEVEL_NOT_RECLAIMED'
    return True,'ALIGNED_WITH_DEFENDED_STRUCTURE'


def validate_setup_dependencies(setup, structure, context, spot, config):
    """Revalidate evidence a saved watch explicitly depended on."""
    diagnostics=[]; a=max(float(context.get('atr_1m') or setup.get('atr_1m') or 1),1.0)
    for dep in setup.get('dependencies') or []:
        kind=dep.get('kind'); direction=setup.get('direction'); sign=1 if direction=='BULLISH' else -1
        if kind=='PROTECTED_STRUCTURE':
            if structure.get('direction')!=direction or structure.get('pending_break'):
                return False,'WATCH_PROTECTED_STRUCTURE_DEPENDENCY_FAILED',diagnostics+[dep]
            level=float(dep['level'])
            if sign*(spot-level)<=0:
                return False,'WATCH_PROTECTED_LEVEL_NOT_HELD',diagnostics+[dep]
            diagnostics.append({'kind':kind,'status':'VALID','level':level})
        elif kind=='PRICE_REACTION_LEVEL':
            level=float(dep['level'])
            if sign*(spot-level)<-max(0.5,0.15*a):
                return False,'WATCH_PRICE_LEVEL_DEPENDENCY_FAILED',diagnostics+[dep]
            diagnostics.append({'kind':kind,'status':'VALID','level':level})
        elif kind=='PRICE_ACCEPTANCE_LEVEL':
            level=float(dep['level']); band=max(0.5,min(2.0,config.acceptance_buffer_atr*a))
            if sign*(spot-level)<-band:
                return False,'WATCH_ACCEPTANCE_LEVEL_FAILED',diagnostics+[dep]
            diagnostics.append({'kind':kind,'status':'VALID','level':level,'source':dep.get('source')})
        elif kind=='PRICE_ACTION_ZONE':
            ledger=context.get('price_action_ledger') or {}
            level=float(dep['level']); role=dep.get('role')
            if role not in ('SUPPORT','RESISTANCE'):
                return False,'WATCH_INVALID_LEVEL_ROLE',diagnostics+[dep]
            match=next((z for z in ledger.get('levels',[])
                        if abs(float(z['price'])-level)<0.01),None)
            status='support_status' if role=='SUPPORT' else 'resistance_status'
            count='support_defenses' if role=='SUPPORT' else 'resistance_rejections'
            if not match or match.get(status)!='CONFIRMED' or int(match.get(count) or 0)<int(dep.get('min_events') or 2):
                return False,'WATCH_CONFIRMED_LEVEL_DISAPPEARED',diagnostics+[dep]
            if role=='SUPPORT' and spot<level-float(match['zone_half_width']):
                return False,'WATCH_SUPPORT_BREAK_ACCEPTED',diagnostics+[dep]
            if role=='RESISTANCE' and spot>level+float(match['zone_half_width']):
                return False,'WATCH_RESISTANCE_BREAK_ACCEPTED',diagnostics+[dep]
            diagnostics.append({'kind':kind,'status':'VALID','price':level,'role':role,
                                'independent_tests':match.get(count)})
        elif kind=='OI_WALL':
            if not context.get('fresh_snapshot'):
                return False,'WATCH_OI_DEPENDENCY_UNAVAILABLE',diagnostics+[dep]
            strike=float(dep['strike']); side=dep.get('side'); key=dep.get('instrument_key'); expiry=dep.get('expiry')
            matches=[w for w in context.get('walls',[]) if w.get('side')==side and abs(float(w.get('strike'))-strike)<1e-8]
            if key: matches=[w for w in matches if w.get('instrument_key')==key]
            if expiry: matches=[w for w in matches if w.get('expiry')==expiry]
            if not matches:
                return False,'WATCH_OI_DEPENDENCY_DISAPPEARED',diagnostics+[dep]
            wall=matches[0]; strength=float(wall.get('relative_to_side_max') or 0)
            if strength+1e-12<config.min_wall_fraction:
                return False,'WATCH_OI_DEPENDENCY_WEAKENED',diagnostics+[{'dependency':dep,'current':wall}]
            band=max(2.0,0.2*a)
            if side=='PE' and direction=='BULLISH' and spot<strike-band:
                return False,'WATCH_OI_SUPPORT_ACCEPTED_BELOW',diagnostics+[{'dependency':dep,'current':wall}]
            if side=='CE' and direction=='BEARISH' and spot>strike+band:
                return False,'WATCH_OI_RESISTANCE_ACCEPTED_ABOVE',diagnostics+[{'dependency':dep,'current':wall}]
            diagnostics.append({'kind':kind,'status':'VALID','strike':strike,'instrument_key':wall.get('instrument_key'),'relative_strength':strength})
    return True,'DEPENDENCIES_VALID',diagnostics


def refresh_setup_watches(bars, structure, spot, now, prior, config, context, fresh_candidates=None):
    """Revalidate each setup independently; one rejection never suppresses others.

    Acceptance setups carry the completed 3m confirmation that created them.
    During their short watch window they do not require a second, redundant 3m
    confirmation merely because the dispatcher runs later; they still require
    the protected thesis, accepted price level, live trigger and tactical stop
    to remain valid. Other setup types keep the stricter latest-3m alignment.
    """
    fresh=list(fresh_candidates) if fresh_candidates is not None else make_setups(bars,structure,spot,config,context)
    bykey={}
    for row in fresh+list(prior or []):
        if not isinstance(row,dict) or not all(k in row for k in ('confirmed_at','direction','invalidation','trigger','kind')):continue
        key=(row['confirmed_at'],row['direction'],row['kind'],round(float(row['trigger']),3))
        bykey.setdefault(key,dict(row))
    eligible=[]; retained=[]; diagnostics=[]
    current_atr=max(atr(bars),1.0)
    for s in sorted(bykey.values(),key=lambda r:r['confirmed_at'],reverse=True):
        try:
            at=datetime.fromisoformat(s['confirmed_at']); age=(now-at).total_seconds(); sign=1 if s['direction']=='BULLISH' else -1
            follow=[c for c in bars if c.start>=at]; allowed,gate=gate_candidate(s,structure,context); reason=None; dependency_details=[]
            effective_watch=(min(config.watch_minutes,config.early_watch_max_minutes) if str(s.get('kind','')).startswith('EARLY_TREND_') else min(config.watch_minutes,config.early_reversal_watch_minutes) if str(s.get('kind','')).startswith('EARLY_') else config.watch_minutes)
            if age<0 or age>60*effective_watch:reason='WATCH_EXPIRED'
            elif bars[0].start>at:reason='WATCH_HISTORY_UNAVAILABLE'
            elif any(c.low<=s['invalidation'] if sign==1 else c.high>=s['invalidation'] for c in follow):reason='WATCH_STOP_TOUCHED'
            elif sign*(spot-s['invalidation'])<=0:reason='WATCH_STOP_BREACHED_LIVE'
            elif not allowed:reason=gate
            else:
                dep_ok,dep_reason,dependency_details=validate_setup_dependencies(s,structure,context,spot,config)
                if not dep_ok:reason=dep_reason
            if reason:
                diagnostics.append({'setup':s,'reason':reason,'age_seconds':age,'dependency_details':dependency_details});continue
            retained.append(s)
            extension=sign*(spot-float(s['trigger'])); r=sign*(spot-float(s['invalidation']))
            three_end=datetime.fromisoformat(structure['last_3m'])+timedelta(minutes=3)
            prior_confirmed=datetime.fromisoformat(s.get('three_confirmed_at',s['confirmed_at']))
            acceptance_kind=s.get('kind') in ACCEPTANCE_SETUP_KINDS and bool(s.get('confirmation_locked'))
            if acceptance_kind:
                level=s.get('acceptance_level')
                acceptance_live=True
                if level is not None:
                    band=max(0.5,min(2.0,config.acceptance_buffer_atr*current_atr))
                    acceptance_live=sign*(bars[-1].close-float(level))>=-band and sign*(spot-float(level))>=-band
                if not acceptance_live:reason='WAIT_FOR_ACCEPTANCE_LEVEL_RECLAIM'
                elif three_end<prior_confirmed:reason='SETUP_3M_CONFIRMATION_MISSING'
            elif structure.get('recent_3m')!=s['direction']:
                reason='WAIT_FOR_NEW_COMPLETED_3M_ALIGNMENT'
            elif three_end<prior_confirmed:
                reason='SETUP_3M_CONFIRMATION_MISSING'
            if reason is None:
                if latest_candle_adverse(bars[-1],s['direction'],spot,current_atr,config):
                    reason='LATEST_COMPLETED_CANDLE_OPPOSES_SAVED_SETUP'
                elif extension < -max(0.5,0.15*current_atr):
                    reason='TRIGGER_NOT_RECLAIMED'
                elif s.get('kind') in CHASE_SENSITIVE_SETUP_KINDS and extension>config.max_entry_extension_atr*current_atr:
                    reason='STALE_ENTRY_CHASE_LIMIT'
                elif r<=0 or extension>config.max_entry_risk_fraction*r:
                    reason='ENTRY_RISK_EXTENSION_LIMIT'
                else:
                    eligible.append(s);reason='PRICE_STRUCTURE_DEPENDENCIES_AND_3M_READY'
            diagnostics.append({'setup':s,'reason':reason,'age_seconds':age,'dependency_details':dependency_details})
        except (KeyError,ValueError,TypeError):diagnostics.append({'setup':s,'reason':'INVALID_SAVED_WATCH'})
    return eligible,retained[:30],diagnostics


def build_level_book(bars, structure, oi, spot, prior_day=None, futures=None, price_ledger=None):
    """Causal multi-source level inventory; source and significance always audited.

    Opening 6m, previous session OHLC, confirmed 3m/15m pivots, defended thesis,
    relevant option OI concentrations and *validated* futures price VWAP.
    These are candidates; OI is not promoted to a confirmed price rejection.
    """
    threes=aggregate(bars,3); fifteens=aggregate(bars,15)
    data=[]
    def add(price, source, kind='PRICE', weight=1.0, **extra):
        if price is None:return
        try:
            x=float(price)
            if x>0 and isfinite(x):data.append({'price':x,'source':source,'kind':kind,'significance':weight,**extra})
        except (TypeError,ValueError):return
    for z in (price_ledger or {}).get('levels',[]):
        for role,status,count in (('RESISTANCE','resistance_status','resistance_rejections'),
                                  ('SUPPORT','support_status','support_defenses')):
            if z.get(status) in ('OBSERVED','CONFIRMED'):
                strong=z[status]=='CONFIRMED'
                add(z['price'],'PRICE_ACTION_'+role,kind='PRICE',
                    weight=3.3 if strong else 1.45,
                    price_rejection_confirmed=strong,
                    hard_barrier=strong,
                    event_count=int(z.get(count) or 0),
                    zone_half_width=z.get('zone_half_width'),
                    latest_test_at=z.get('last_resistance_at' if role=='RESISTANCE' else 'last_support_at'),
                    interaction_status=z.get(status),
                    sources=z.get('sources'))
    if len(bars)>=6:
        add(max(x.high for x in bars[:6]),'OPENING_SIX_MINUTE_HIGH',weight=2.2)
        add(min(x.low for x in bars[:6]),'OPENING_SIX_MINUTE_LOW',weight=2.2)
    if prior_day:
        for field in ('high','low','close'):
            add(prior_day.get(field),'PREVIOUS_SESSION_'+field.upper(),weight=1.7 if field!='close' else 1.25)
    add(structure.get('support'),'PROTECTED_SUPPORT',weight=2.7)
    add(structure.get('resistance'),'PROTECTED_RESISTANCE',weight=2.7)
    for label in ('confirmed_pivot_low','confirmed_pivot_high','confirmed_15m_pivot_low','confirmed_15m_pivot_high'):
        add(structure.get(label),label.upper(),weight=1.85 if '15m' in label else 1.5)
    lows, highs=pivots(threes)
    for _,price in lows[-5:]:add(price,'CONFIRMED_3M_PIVOT_SUPPORT',weight=1.4)
    for _,price in highs[-5:]:add(price,'CONFIRMED_3M_PIVOT_RESISTANCE',weight=1.4)
    # Completed 15m context is optional at the open; 09:21 eligibility intact.
    if len(fifteens)>=2:
        add(max(x.high for x in fifteens[-2:]),'COMPLETED_15M_CONTEXT_HIGH',weight=1.25)
        add(min(x.low for x in fifteens[-2:]),'COMPLETED_15M_CONTEXT_LOW',weight=1.25)
    for wall in oi.get('walls',[]):
        add(wall.get('strike'),'OI_'+str(wall.get('side')),kind='OI',
            weight=1.0+float(wall.get('relative_to_side_max') or 0),
            oi=float(wall.get('oi') or 0), price_rejection_confirmed=bool(wall.get('price_rejection_confirmed')),
            hard_barrier=bool(wall.get('hard_barrier')),
            oi_change=wall.get('oi_change'),barrier_status=wall.get('barrier_status','POTENTIAL'))
    f=futures or {}
    if f.get('status') not in ('UNAVAILABLE','STALE'):
        add(f.get('candle_vwap_estimate'),'FUTURES_COMPLETED_CANDLE_VWAP_ESTIMATE',weight=1.15)
    data.sort(key=lambda x:(x['price'],-x['significance']))
    # Deduplicate identical source/price (not different independent evidence).
    unique=[];seen=set()
    for x in data:
        key=(x['source'],round(x['price'],2))
        if key not in seen:unique.append(x);seen.add(key)
    opening=(max(x.high for x in bars[:6])-min(x.low for x in bars[:6])) if len(bars)>=6 else 0.0
    impulse=(max(x.high for x in bars[-9:])-min(x.low for x in bars[-9:])) if bars else 0.0
    return {'levels':unique,'opening_range_height':opening,
            'recent_impulse_height':impulse,'atr_1m':max(atr(bars),1.0),
            'level_source_count':len(unique)}


def contextual_futures_alignment(futures, structure, spot):
    """Futures confirms/conflicts price thesis, but cannot by itself reverse it."""
    d=structure.get('direction');f=futures or {};pattern=f.get('price_oi_pattern')
    if not f or f.get('status') in ('UNAVAILABLE','STALE'):
        return {'status':'UNAVAILABLE','trade_veto':False}
    supportive={'BULLISH':{'LONG_BUILDUP_HYPOTHESIS','SHORT_COVERING_HYPOTHESIS'},
                'BEARISH':{'SHORT_BUILDUP_HYPOTHESIS','LONG_UNWINDING_HYPOTHESIS'}}
    alignment='NEUTRAL'
    if pattern in supportive.get(d,set()):alignment='SUPPORTIVE_HYPOTHESIS'
    elif pattern not in (None,'UNAVAILABLE','UNCHANGED_OR_NOISY') and d in supportive:
        alignment='CONFLICTING_HYPOTHESIS'
    vwap=f.get('candle_vwap_estimate')
    location='UNKNOWN'
    if vwap is not None and f.get('price'):
        location='ABOVE' if float(f['price'])>float(vwap) else 'BELOW'
    return {'status':'OBSERVED','alignment':alignment,'vwap_location':location,
            'pattern':pattern,'price_basis_points':float(f['price'])-spot if f.get('price') else None,
            'trade_veto':False,'certainty':'HYPOTHESIS_NOT_PARTICIPANT_INTENT'}

def risk_plan(setup,spot,context,config):
    """Build the actual underlying trade plan without clipping structural risk.

    v119.1 separates three concepts that v117.1 could conflate:
      * tactical trade invalidation (the stop used for this entry),
      * broad protected-thesis invalidation (a setup dependency), and
      * soft intermediate hurdles versus genuinely hard target barriers.

    Potential OI concentrations and historical pivots remain visible in the
    plan but do not automatically force a continuation target to stop there.
    A hard barrier may cap the target; a soft hurdle is audited and monitored.
    """
    d=setup.get('direction')
    if d not in ('BULLISH','BEARISH') or not isfinite(float(spot)) or spot<=0:
        return None,'INVALID_ENTRY'
    sign=1 if d=='BULLISH' else -1
    a=max(1.,float(setup.get('atr_1m') or context.get('atr_1m') or 1))
    raw=float(setup.get('trade_invalidation',setup['invalidation']))
    initial=sign*(spot-raw)
    if not isfinite(initial) or initial<=0:return None,'STOP_ON_WRONG_SIDE'
    # Volatility floor may expand the local stop outward; it may never compress
    # a genuine tactical invalidation just to manufacture eligibility.
    stop=spot-sign*max(initial,config.min_stop_atr*a)
    risk=sign*(spot-stop)
    if risk>config.max_risk+1e-8:return None,'STOP_TOO_WIDE'
    if risk<1:return None,'STOP_TOO_TIGHT_FOR_NOISE'
    minimum=risk*config.min_rr
    levels=list(context.get('levels') or [])
    # Compatibility for isolated callers that supply former context fields.
    if not levels:
        for name in ('price_resistance','minor_resistance','price_support','minor_support'):
            if context.get(name) is not None:
                levels.append({'price':float(context[name]),'source':name,'kind':'PRICE','significance':2})
        for w in context.get('walls',[]):
            levels.append({'price':float(w['strike']),'source':'OI_'+w['side'],'kind':'OI',
                           'significance':1.0+float(w.get('relative_to_side_max') or 0),
                           'price_rejection_confirmed':w.get('price_rejection_confirmed',False),
                           'hard_barrier':w.get('hard_barrier',False)})
        for side,name in (('CE','call_resistance'),('PE','put_support')):
            w=context.get(name) or {}
            if w.get('strike') is not None:
                levels.append({'price':float(w['strike']),'source':'OI_'+side,'kind':'OI',
                               'significance':1+float(w.get('relative_to_side_max') or 0),
                               'price_rejection_confirmed':w.get('price_rejection_confirmed',False),
                               'hard_barrier':w.get('hard_barrier',False)})

    setup_kind=str(setup.get('kind') or '')
    range_setup=setup_kind.startswith('RANGE_')
    obstructions=[]
    for level in levels:
        try:
            px=float(level['price']);gap=sign*(px-spot)
            if not isfinite(px) or gap<=0.25:continue
            source=str(level.get('source',''));kind=str(level.get('kind','PRICE'))
            # An earlier support ABOVE price is not automatically resistance,
            # and an earlier resistance BELOW price is not automatically support.
            if (source=='PRICE_ACTION_SUPPORT' and d=='BULLISH') or (source=='PRICE_ACTION_RESISTANCE' and d=='BEARISH'):
                continue
            if kind=='OI' and (('CE' not in source and d=='BULLISH') or ('PE' not in source and d=='BEARISH')):
                continue
            quality=float(level.get('significance') or 1)
            if kind=='OI' and quality<1.5 and not level.get('hard_barrier'):continue
            if kind=='PRICE' and quality<1.4:continue
            hard=False
            hard_reason=None
            if range_setup:
                hard=True;hard_reason='RANGE_OPPOSING_LEVEL'
            elif kind=='OI' and (bool(level.get('hard_barrier')) or bool(level.get('price_rejection_confirmed'))):
                hard=True;hard_reason='CONFIRMED_OI_OR_PRICE_REJECTION'
            elif bool(level.get('hard_barrier')):
                hard=True;hard_reason='EXPLICIT_HARD_BARRIER'
            obstructions.append({**level,'distance':gap,'target_role':'HARD_BARRIER' if hard else 'SOFT_HURDLE','hard_reason':hard_reason})
        except (ValueError,TypeError,KeyError):continue
    obstructions.sort(key=lambda x:(x['distance'],-float(x.get('significance') or 0)))
    hard=[x for x in obstructions if x['target_role']=='HARD_BARRIER']
    soft=[x for x in obstructions if x['target_role']=='SOFT_HURDLE']
    # A measured reaction zone consumes some of the available target room.
    # Never calculate RR up to the *centre* of a resistance/support zone.
    price_barrier=next((x for x in hard if x.get('source')=='PRICE_ACTION_'+
                        ('RESISTANCE' if d=='BULLISH' else 'SUPPORT')),None)
    if price_barrier:
        clearance=max(config.target_clearance_atr*a,
                      float(price_barrier.get('zone_half_width') or 0))
        achievable=price_barrier['distance']-clearance
        if achievable+1e-8<minimum:
            return None,'CONFIRMED_PRICE_LEVEL_INSUFFICIENT_REWARD_ROOM'

    if range_setup and obstructions:
        first=obstructions[0]
        if first['distance']+1e-8<minimum:
            return None,'TARGET_ROOM_INSUFFICIENT_NEAREST_'+str(first.get('kind','LEVEL'))
        t1=float(first['price']);target_source=str(first.get('source'));target_quality='OBSERVED_RANGE_OBSTRUCTION'
    else:
        recent=float(context.get('recent_impulse_height') or 0)
        opening=float(context.get('opening_range_height') or 0)
        thesis_leg=0.0
        try:
            protected=setup.get('protected_thesis_boundary')
            if protected is not None:
                thesis_leg=abs(float(setup.get('trigger',spot))-float(protected))
        except (TypeError,ValueError):
            thesis_leg=0.0
        measured=max(recent,thesis_leg)
        bounded_measured=min(measured,config.max_target_projection_atr*a) if measured>0 else 0.0
        projection=max(minimum,config.min_intraday_projection_atr*a,bounded_measured)
        raw_target=spot+sign*projection
        projected=_round_directional_target(raw_target,d,config.strike_step)
        # Rounding outward must still produce at least the required RR.
        if sign*(projected-spot)+1e-8<minimum:
            projected=_round_directional_target(spot+sign*minimum,d,config.strike_step)
        blocking=next((x for x in hard if x['distance']<sign*(projected-spot)-1e-8),None)
        if blocking:
            if blocking['distance']+1e-8<minimum:
                return None,'TARGET_ROOM_INSUFFICIENT_HARD_BARRIER'
            if str(blocking.get('source','')).startswith('PRICE_ACTION_'):
                margin=max(config.target_clearance_atr*a,
                           float(blocking.get('zone_half_width') or 0))
                t1=float(blocking['price'])-sign*margin
            else:
                t1=float(blocking['price'])
            target_source=str(blocking.get('source'));target_quality='HARD_OBSERVED_BARRIER'
        else:
            t1=float(projected);target_source='CAUSAL_CONTINUATION_PROJECTION';target_quality='PROJECTED_WITH_SOFT_HURDLES'

    rr=sign*(t1-spot)/risk
    if rr+1e-8<config.min_rr:return None,'UNDERLYING_RR_BELOW_MINIMUM'
    # T2 is the next meaningful forward objective. A hard barrier beyond T1 is
    # preferred; otherwise move one live strike step farther in the direction.
    beyond_hard=[x for x in hard if sign*(float(x['price'])-t1)>0.25]
    if beyond_hard:
        t2=float(beyond_hard[0]['price'])
    else:
        t2=_round_directional_target(t1+sign*max(config.strike_step,a,risk),d,config.strike_step)
        if sign*(t2-t1)<=0:
            t2=t1+sign*config.strike_step
    distance_to_t2=sign*(t2-spot)
    intermediate=[dict(x) for x in obstructions if x['distance']<=distance_to_t2+0.01]
    soft_before_t1=[dict(x) for x in soft if x['distance']<sign*(t1-spot)-1e-8]
    hard_before_t1=[dict(x) for x in hard if x['distance']<=sign*(t1-spot)+1e-8]
    plan={'entry_underlying':spot,'stop_underlying':round(stop,5),'risk_points':round(risk,5),
          't1_underlying':round(t1,5),'t2_underlying':round(t2,5),'underlying_rr':round(rr,5),
          'target_source':target_source,'target_quality':target_quality,'fixed_targets':True,
          'intermediate_barriers':intermediate,'soft_intermediate_hurdles':soft_before_t1,
          'hard_target_barriers':hard_before_t1,
          'nearest_opposing_level':obstructions[0] if obstructions else None,
          'structural_invalidation_requested':raw,
          'trade_invalidation_requested':raw,
          'trade_invalidation_role':setup.get('stop_role','LOCAL_PRICE_STRUCTURE'),
          'protected_thesis_boundary':setup.get('protected_thesis_boundary'),
          'thesis_invalidation':setup.get('thesis_invalidation'),
          'volatility_floor_used':risk>initial+1e-8,
          'projected_target_not_historical_resistance':target_source=='CAUSAL_CONTINUATION_PROJECTION',
          'soft_hurdles_do_not_equal_confirmed_rejection':True,
          'risk_limit_points':config.max_risk}
    return plan,'OK'



def select_contract(chain,quotes,direction,scenario,spot,now,expiry,config,plan=None):
    """Rank only eligible current-expiry contracts using quote quality and actual plan risk.

    Range/reversal uses CE ATM-1/-2 or PE ATM+1/+2. Trend uses ATM or one ITM.
    Confirmed acceptance continuation prefers one-ITM when its live execution
    quality is within a bounded tolerance of the best eligible contract.
    When a proposed underlying plan is supplied (the production path), premium
    stress and responsiveness are computed from that plan's actual stop and T1,
    never from a universal 30-point hypothetical move.
    """
    side='CE' if direction=='BULLISH' else 'PE'
    relevant=[r for r in chain if r.get('side')==side and r.get('expiry')==expiry]
    strikes=sorted({float(r['strike']) for r in relevant})
    if not strikes:return None,[{'reason':'NO_MATCHING_CONTRACTS'}]
    atm=min(strikes,key=lambda x:(abs(x-spot),x))
    if scenario in ('RANGE','REVERSAL'):
        offsets=(-1,-2) if side=='CE' else (1,2)
    elif scenario=='TREND_ACCEPTANCE':
        offsets=(-1,0) if side=='CE' else (1,0)
    else:
        offsets=(0,-1) if side=='CE' else (0,1)
    allowed={round(atm+n*config.strike_step,5):n for n in offsets}
    candidate_rows=[r for r in relevant if float(r['strike']) in allowed]
    max_vol=max([float(r.get('volume') or 0) for r in candidate_rows]+[1.0])
    ranked=[];diag=[]
    minutes_remaining=(datetime.fromisoformat(expiry+'T15:30:00+05:30')-now).total_seconds()/60
    if minutes_remaining<=0:return None,[{'reason':'CONTRACT_AFTER_EXPIRY_CUTOFF'}]
    plan_risk=plan_reward=None
    if plan is not None:
        try:
            plan_risk=float(plan['risk_points']); plan_reward=abs(float(plan['t1_underlying'])-float(plan['entry_underlying']))
            if not all(isfinite(x) and x>0 for x in (plan_risk,plan_reward)):
                raise ValueError
        except (KeyError,TypeError,ValueError):
            return None,[{'reason':'INVALID_PROPOSED_TRADE_PLAN'}]
    for r in candidate_rows:
        strike=float(r['strike']);key=r.get('instrument_key');q=quotes.get(key)
        def reject(reason,**extra):diag.append({'instrument_key':key,'strike':strike,'reason':reason,**extra})
        if not q:reject('QUOTE_MISSING');continue
        try:
            stamped=parse_feed_timestamp(q['timestamp']);age=(now-stamped).total_seconds()
            bid=float(q['bid']);ask=float(q['ask']);bq=float(q['bid_qty']);aq=float(q['ask_qty'])
            vol=float(r.get('volume') or 0);lot=float(r['lot_size']);delta=float(r['delta']);gamma=float(r['gamma']);theta=float(r['theta'])
            raw_vega=r.get('vega');raw_iv=r.get('iv');iv=float(raw_iv) if raw_iv is not None else None;vega=float(raw_vega) if raw_vega is not None else None
            numerics=[bid,ask,bq,aq,vol,lot,delta,gamma,theta]+([iv] if iv is not None else [])+([vega] if vega is not None else [])
            if not all(isfinite(x) for x in numerics):reject('NONFINITE_CONTRACT_OR_QUOTE');continue
            if gamma<0:reject('INVALID_NEGATIVE_GAMMA');continue
            if not -2<=age<=config.max_quote_age:reject('QUOTE_STALE_OR_CLOCK_SKEW');continue
            if lot<=0 or int(lot)!=lot or isinstance(r['lot_size'],bool):reject('INVALID_LIVE_LOT_SIZE');continue
            if not (min(bid,ask)>0 and ask>=bid and vol>=config.min_option_volume):reject('INVALID_BID_ASK_OR_VOLUME');continue
            depth_lots=min(bq,aq)/lot
            if depth_lots<1:reject('INSUFFICIENT_LIVE_LOT_BID_ASK_DEPTH',depth_lots=round(depth_lots,4));continue
            if (side=='CE' and delta<=0) or (side=='PE' and delta>=0) or not 0.30<=abs(delta)<=0.85:reject('DELTA_SIGN_OR_RANGE_INVALID');continue
            if iv is not None and not 0<iv<=config.max_option_iv:reject('IMPOSSIBLE_OR_EXTREME_IV');continue
            spread=200*(ask-bid)/(ask+bid)
            if spread>config.max_spread_pct:reject('SPREAD_TOO_WIDE');continue
            hold_minutes=min(15.0,max(1.0,minutes_remaining))
            theta_cost=max(0,-theta)*hold_minutes/1440
            iv_stress=abs(vega or 0)*config.iv_shock_points
            total_friction=(ask-bid)+theta_cost+0.25*iv_stress
            plan_stress=None; favourable_response=None; stress_score=0.5
            if plan_risk is not None:
                favourable_response=max(0.0,abs(delta)*plan_reward+.5*gamma*plan_reward**2-theta_cost)
                if favourable_response<=total_friction:
                    reject('FRICTION_EXCEEDS_PLAN_T1_SENSITIVITY',plan_reward_points=plan_reward);continue
                plan_stress=max(0.0,abs(delta)*plan_risk-.5*gamma*plan_risk**2)+theta_cost+iv_stress+(ask-bid)
                if plan_stress/max(ask,0.01)>config.max_premium_cost_ratio:
                    reject('ACTUAL_PLAN_OPTION_STRESS_EXCEEDS_PREMIUM_LIMIT',plan_risk_points=plan_risk,
                           estimated_premium_loss=round(plan_stress,4));continue
                stress_score=max(0,1-min(1,total_friction/max(favourable_response,0.01)))
            delta_score=max(0,1-abs(abs(delta)-(0.60 if scenario in ('RANGE','REVERSAL') else 0.56))/0.40)
            spread_score=max(0,1-spread/config.max_spread_pct)
            depth_score=min(1.0,log1p(depth_lots)/log1p(config.depth_full_score_lots))
            depth_imbalance=min(bq,aq)/max(bq,aq) if max(bq,aq)>0 else 0
            volume_score=min(1,(vol/max_vol)**0.25)
            decay_score=max(0,1-min(1,theta_cost/max(ask,0.01)*25))
            gamma_score=max(0,1-min(1,abs(gamma)*100))
            iv_score=0.65 if iv is None else max(0,1-abs(iv-16)/max(30,iv))
            vega_score=0.65 if vega is None else max(0,1-min(1,abs(vega)*config.iv_shock_points/max(ask,.01)))
            preferred_itm=(-1 if side=='CE' else 1)
            if scenario=='TREND_ACCEPTANCE':
                moneyness_score=1.0 if allowed[strike]==preferred_itm else 0.95
            else:
                moneyness_score=1.0 if allowed[strike] in (-1,1) else 0.96
            score=(.24*delta_score+.22*spread_score+.11*depth_score+.06*volume_score+.07*decay_score+
                   .05*gamma_score+.06*iv_score+.05*vega_score+.05*moneyness_score+.06*stress_score+.03*depth_imbalance)
            candidate={'instrument_key':key,'strike':strike,'expiry':expiry,'side':side,'lot_size':int(lot),
                       'bid':bid,'ask':ask,'bid_qty':bq,'ask_qty':aq,'depth_lots':round(depth_lots,4),
                       'volume':vol,'delta':delta,'gamma':gamma,'theta':theta,'iv':iv,'vega':vega,'spread_pct':spread,
                       'quote_age_seconds':round(age,3),'quote_timestamp':stamped.isoformat(),'atm':atm,
                       'offset_steps':allowed[strike],'offset':allowed[strike],'selection_regime':scenario,
                       'execution_score':round(score,6),'selection_score':round(score,6),'score_is_probability':False,
                       'actual_plan_risk_points':plan_risk,'actual_plan_t1_reward_points':plan_reward,
                       'actual_plan_option_premium_loss_estimate':round(plan_stress,4) if plan_stress is not None else None,
                       'actual_plan_t1_premium_response_estimate':round(favourable_response,4) if favourable_response is not None else None,
                       'risk_assessment':'ACTUAL_PROPOSED_PLAN' if plan_risk is not None else 'UNAVAILABLE_NO_PLAN_COMPONENT_RANKING_ONLY',
                       'option_friction_estimate':round(total_friction,4),'expiry_minutes_remaining_at_quote':round(minutes_remaining,2),
                       'selection_components':{'delta':round(delta_score,4),'spread':round(spread_score,4),'depth':round(depth_score,4),
                            'depth_imbalance':round(depth_imbalance,4),'volume':round(volume_score,4),'theta':round(decay_score,4),
                            'gamma':round(gamma_score,4),'iv':round(iv_score,4),'vega':round(vega_score,4),
                            'moneyness':round(moneyness_score,4),'stress':round(stress_score,4)}}
            ranked.append((score,candidate))
        except (KeyError,ValueError,TypeError,OverflowError):reject('MALFORMED_CANDIDATE')
    if not ranked:return None,diag or [{'reason':'NO_LIQUID_CANDIDATE'}]
    ranked.sort(key=lambda x:(-x[0],x[1]['spread_pct'],-x[1]['depth_lots'],-x[1]['volume'],x[1]['strike']))
    best_score,best=ranked[0]
    chosen=best
    if scenario=='TREND_ACCEPTANCE':
        preferred_offset=-1 if side=='CE' else 1
        preferred=next(((score,row) for score,row in ranked if row.get('offset_steps')==preferred_offset),None)
        if preferred and preferred[0]+config.one_itm_execution_tolerance>=best_score:
            chosen=preferred[1]
            chosen['selection_rationale']='PREFERRED_ONE_ITM_FOR_CONFIRMED_DIRECTIONAL_ACCEPTANCE_WITHIN_EXECUTION_TOLERANCE'
        else:
            chosen['selection_rationale']='BEST_EXECUTION_SELECTED_BECAUSE_ONE_ITM_WAS_MATERIALLY_INFERIOR_OR_UNAVAILABLE'
    else:
        chosen['selection_rationale']='HIGHEST_ELIGIBLE_EXECUTION_QUALITY_WITH_CURRENT_METADATA_QUOTE_DEPTH_AND_ACTUAL_PLAN_RISK' if plan is not None else 'COMPONENT_RANKING_ONLY_NO_ENTRY_PLAN'
    for score,row in ranked:
        if row['instrument_key']==chosen['instrument_key']:
            continue
        diag.append({'reason':'LOWER_OR_NONPREFERRED_COMPOSITE_EXECUTION_QUALITY','strike':row['strike'],'instrument_key':row['instrument_key'],
                     'execution_score':row['execution_score'],'selected_score':chosen['execution_score'],'spread_pct':row['spread_pct'],
                     'depth_lots':row['depth_lots'],'delta':row['delta'],'iv':row['iv'],'theta':row['theta'],
                     'actual_plan_option_premium_loss_estimate':row.get('actual_plan_option_premium_loss_estimate')})
    return chosen,diag



def contract_sensitivity(contract,plan,horizon_minutes=15):
    delta=contract.get('delta')
    if delta is None:return {'status':'UNAVAILABLE','reason':'MISSING_DELTA'}
    delta=abs(float(delta)); gamma=float(contract.get('gamma') or 0);theta=float(contract.get('theta') or 0)
    bid,ask=float(contract['bid']),float(contract['ask'])
    risk=float(plan['risk_points']);reward=abs(float(plan['t1_underlying'])-float(plan['entry_underlying']))
    decay=theta*horizon_minutes/1440
    vega=contract.get('vega')
    iv=contract.get('iv')
    iv_uncertainty=abs(float(vega)) if vega is not None else None
    return {'status':'LOCAL_SENSITIVITY_ESTIMATE','horizon_minutes':horizon_minutes,
            'observed_iv':iv,'iv_shock_plus_minus_1_point_premium_sensitivity':iv_uncertainty,
            'estimated_bid_at_underlying_t1':max(0,bid+delta*reward+.5*gamma*reward**2+decay),
            'estimated_bid_at_underlying_stop':max(0,bid-delta*risk+.5*gamma*risk**2+decay),
            'estimated_t1_change_from_entry_ask':bid+delta*reward+.5*gamma*reward**2+decay-ask,
            'estimated_stop_change_from_entry_ask':bid-delta*risk+.5*gamma*risk**2+decay-ask,
            'assumptions':['FIXED_LOCAL_GREEKS','NO_IV_DIRECTION_ASSUMED','DAILY_THETA_DIVIDED_BY_1440','VEGA_CONVENTION_REQUIRES_PROVIDER_CONFIRMATION','OBSERVED_BID_ASK_ONLY'],
            'probability_or_guaranteed_return':False}


# scanner/provider.py
import json
import gzip
import os
import time
from datetime import datetime, date, timezone
from math import isfinite
from urllib.parse import quote, urlencode
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError
from pathlib import Path
INDEX = 'NSE_INDEX|Nifty 50'

class ProviderError(RuntimeError):
    pass

class Upstox:

    def __init__(self, token: str):
        if not token or any((c in token for c in '\r\n')):
            raise ProviderError('UPSTOX_ANALYTICS_TOKEN missing or invalid')
        self._token = token

    def get(self, path: str, params: dict | None=None):
        url = 'https://api.upstox.com' + path + ('?' + urlencode(params) if params else '')
        req = Request(url, headers={'Authorization': 'Bearer ' + self._token, 'Accept': 'application/json', 'User-Agent': 'nifty-scanner/120.1'})
        for attempt in range(3):
            try:
                with urlopen(req, timeout=12) as r:

                    def reject_constant(value):
                        raise ValueError('Invalid numeric JSON')
                    obj = json.load(r, parse_constant=reject_constant, parse_float=finite_json_float)
                if not isinstance(obj, dict) or obj.get('status') != 'success' or 'data' not in obj:
                    raise ProviderError('Upstox returned an unsuccessful or invalid response')
                return obj['data']
            except HTTPError as e:
                if e.code in (429, 500, 502, 503, 504) and attempt < 2:
                    time.sleep(1 + attempt)
                    continue
                raise ProviderError(f'Upstox request failed HTTP {e.code}') from None
            except (URLError, TimeoutError, OSError, ValueError) as e:
                if attempt < 2:
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

    def previous_session(self, today: date):
        """Prior completed day OHLC from official V3 historical daily candles.

        Optional enrichment, never fabricate previous-session levels if missing.
        Provider may include holidays; choose last strictly earlier session.
        """
        prior=today-timedelta(days=1)
        from_day=today-timedelta(days=15)
        data=self.get('/v3/historical-candle/'+quote(INDEX,safe='')+'/days/1/'+prior.isoformat()+'/'+from_day.isoformat())
        raw=data.get('candles') if isinstance(data,dict) else None
        if not isinstance(raw,list):raise ProviderError('Prior day data malformed')
        good=[]
        for row in raw:
            try:
                t=parse_feed_timestamp(row[0]);d=t.date()
                prices=[float(x) for x in row[1:5]]
                if d<today and all(isfinite(x) and x>0 for x in prices) and prices[1]>=max(prices[0],prices[3]) and prices[2]<=min(prices[0],prices[3]):
                    good.append((d,{'date':d.isoformat(),'open':prices[0], 'high':prices[1],
                                    'low':prices[2],'close':prices[3],'source':'UPSTOX_OFFICIAL_DAILY_COMPLETED'}))
            except (TypeError,ValueError,KeyError,IndexError):continue
        if not good:raise ProviderError('Previous completed session OHLC unavailable')
        return max(good,key=lambda x:x[0])[1]

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
                rows.append(r)
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
                    oi = float(market.get('oi') or 0)
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
                if not all((isfinite(x) and x >= 0 for x in (oi, ltp, volume, chain_bid, chain_ask, chain_bid_qty, chain_ask_qty))):
                    raise ProviderError('Invalid option chain values')
                if any((x is not None and (not isfinite(x)) for x in (delta, gamma, theta, vega, iv, prev_oi))):
                    raise ProviderError('Invalid option greek data')
                lot = metadata[key].get('lot_size')
                if lot is None or not isfinite(float(lot)) or float(lot) <= 0 or (not float(lot).is_integer()):
                    raise ProviderError('Missing or invalid live lot size')
                result.append({'instrument_key': key, 'expiry': expiry, 'strike': strike, 'side': side, 'oi': oi, 'ltp': ltp, 'volume': volume, 'delta': delta, 'gamma': gamma, 'theta': theta, 'vega':vega, 'iv':iv, 'prev_oi':prev_oi, 'lot_size': lot, 'chain_bid':chain_bid, 'chain_ask':chain_ask, 'chain_bid_qty':chain_bid_qty, 'chain_ask_qty':chain_ask_qty})
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
                    if value is not None and (not isfinite(value)):
                        numeric[name] = None
                quoted = {'last_price': price, 'bid': float(b.get('price') or 0), 'bid_qty': float(b.get('quantity') or 0), 'ask': float(a.get('price') or 0), 'ask_qty': float(a.get('quantity') or 0)}
                if any((not isfinite(x) or x < 0 for x in quoted.values())):
                    continue
                out[key] = {**quoted, 'timestamp': stamp, **numeric}
            except (TypeError, ValueError):
                continue
        return out

    def nearest_nifty_future(self, now: datetime, cache: Path) -> dict:
        """Resolve from the provider's daily instrument master, never stale-cache fallback."""
        day = now.astimezone(IST).date().isoformat()
        try:
            if cache.exists():
                saved = json.loads(cache.read_text(encoding='utf-8'))
                if saved.get('day') == day and saved.get('instruments'):
                    instruments = saved['instruments']
                else:
                    instruments = []
            else:
                instruments = []
            if not instruments:
                req = Request('https://assets.upstox.com/market-quote/instruments/exchange/NSE.json.gz', headers={'User-Agent': 'nifty-scanner/120.1'})
                with urlopen(req, timeout=20) as response:
                    raw = response.read(40000001)
                if len(raw) > 40000000:
                    raise ProviderError('Instrument master too large')
                master = json.loads(gzip.decompress(raw))
                instruments = [x for x in master if x.get('segment') == 'NSE_FO' and x.get('instrument_type') == 'FUT' and (x.get('underlying_key') == INDEX) and (x.get('underlying_symbol') == 'NIFTY')]
                if not instruments:
                    raise ProviderError('No NIFTY futures in instrument master')
                cache.parent.mkdir(parents=True, exist_ok=True)
                tmp = cache.with_suffix('.tmp')
                tmp.write_text(json.dumps({'day': day, 'instruments': instruments}), encoding='utf-8')
                os.replace(tmp, cache)
            found = []
            for item in instruments:
                exp = datetime.fromtimestamp(float(item['expiry']) / 1000, timezone.utc).astimezone(IST).date()
                if exp >= now.astimezone(IST).date():
                    found.append((exp, item))
            if not found:
                raise ProviderError('No unexpired NIFTY future')
            exp, item = min(found, key=lambda t: t[0])
            return {'instrument_key': item['instrument_key'], 'expiry': exp.isoformat(), 'trading_symbol': item.get('trading_symbol')}
        except (OSError, ValueError, TypeError, KeyError, URLError, json.JSONDecodeError) as e:
            raise ProviderError('NIFTY futures master unavailable') from None

def parse_feed_timestamp(value):
    """Accept documented Upstox exchange timestamps (ISO or epoch milliseconds)."""
    if isinstance(value,bool) or value is None:
        raise ValueError('Missing provider timestamp')
    if isinstance(value,(int,float)) or (isinstance(value,str) and value.strip().isdigit()):
        number=float(value)
        if not isfinite(number):raise ValueError('Non-finite quote timestamp')
        seconds=number/1000 if abs(number)>1e11 else number
        return datetime.fromtimestamp(seconds,timezone.utc).astimezone(IST)
    t=datetime.fromisoformat(str(value).replace('Z','+00:00'))
    if t.tzinfo is None:raise ValueError('Unzoned quote timestamp')
    return t.astimezone(IST)

def checked_spot(quote_data: dict, now: datetime, max_age: float) -> float:
    try:
        timestamp = parse_feed_timestamp(quote_data['timestamp'])
        if timestamp.tzinfo is None:
            raise ValueError()
        age = (now - timestamp).total_seconds()
        spot = float(quote_data['last_price'])
        if age < -2 or age > max_age or (not isfinite(spot)) or (spot <= 0):
            raise ValueError()
        return spot
    except (TypeError, ValueError, KeyError):
        raise DataError('SPOT_QUOTE_STALE_OR_INVALID') from None


# scanner/state.py
import fcntl
import hashlib
import json
import os
import tempfile
import copy
from contextlib import contextmanager
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any

class StateError(RuntimeError):
    pass

def validate_position(position):
    """Reject ambiguous state instead of silently discarding an open lock."""
    from math import isfinite
    from datetime import date
    p = position
    try:
        if p.get('status') != 'OPEN' or p['direction'] not in ('BULLISH', 'BEARISH'):
            raise ValueError()
        side = 'CE' if p['direction'] == 'BULLISH' else 'PE'
        if p.get('side', side) != side or not isinstance(p['instrument_key'], str) or (not p['instrument_key'].strip()) or any((c in p['instrument_key'] for c in '\r\n')):
            raise ValueError()
        for key in ('entry_spot', 'entry_ask', 'stop', 't1', 't2', 'best_spot'):
            if isinstance(p[key], bool) or not isinstance(p[key], (int, float)) or (not isfinite(p[key])) or (p[key] <= 0):
                raise ValueError()
        sign = 1 if p['direction'] == 'BULLISH' else -1
        if sign * (p['t1'] - p['entry_spot']) <= 0 or sign * (p['t2'] - p['t1']) <= 0:
            raise ValueError()
        if sign * (p['t2'] - p['stop']) <= 0 or not 0 < float(p.get('remaining_pct', 100)) <= 100:
            raise ValueError()
        opened = datetime.fromisoformat(p['opened_at'])
        checkpoint = datetime.fromisoformat(p['last_candle'])
        if opened.tzinfo is None or checkpoint.tzinfo is None or checkpoint.second or checkpoint.microsecond:
            raise ValueError()
        if not p.get('id') or date.fromisoformat(p['expiry']) < opened.date():
            raise ValueError()
        if (p.get('plan') or {}).get('t1_underlying', p['t1']) != p['t1'] or (p.get('plan') or {}).get('t2_underlying', p['t2']) != p['t2']:
            raise ValueError()
    except (ValueError, TypeError, KeyError, AttributeError):
        raise StateError('Invalid open position; lock requires reconciliation') from None

def migrate_state(source, destination, now):
    """Create v119 schema-7 state once while preserving operational continuity.

    v118 schema-6 and v117 schema-5 operational state is compatible at the data layer, so
    open-position locks, outbox, history and same-session OI history/baseline
    are preserved. Old setup watches and thesis are deliberately cleared
    because v119 changes entry semantics. Earlier schemas keep the conservative
    migration behavior and do not import stale strategy observations.
    """
    if destination.exists():
        raise StateError('Destination state already exists; refusing to overwrite')
    try:
        raw=source.read_bytes()
        def bad_number(value):
            raise ValueError('Non-finite legacy state')
        legacy=json.loads(raw,parse_constant=bad_number,parse_float=finite_json_float)
        if not isinstance(legacy,dict):raise ValueError()
    except (ValueError,OSError):
        raise StateError('Migration source is unreadable') from None

    schema=legacy.get('schema')
    if schema in (1,2,3,4,5,6,7):
        state=load(source,allow_legacy=True)
        preserve_intraday_oi=(schema in (5,6,7))
        state.update(schema=7,engine_version='120.1.0',thesis=None,setup_watches=[],
                     opportunity_journal=[],futures_snapshot=None,price_action_ledger={},market_phase={})
        if not preserve_intraday_oi:
            state.update(oi_snapshot=None,oi_history=[],session_oi_baseline=None)
        state['strategy_migration']={
            'from_schema':schema,
            'entry_engine_reset':True,
            'entry_quality_revision':1192,
            'operational_position_preserved':state.get('position') is not None,
            'intraday_oi_preserved':preserve_intraday_oi,
            'at':now.isoformat(),
        }
    elif legacy.get('schema_version') in (107,109):
        if legacy.get('position_reconciliation_required'):
            raise StateError('Legacy state requires reconciliation; it cannot be migrated as flat')
        state={'schema':7,'engine_version':'120.1.0','initialized_at':now.isoformat(),'session_date':legacy.get('session_date'),
               'thesis':None,'position':None,'history':[],'outbox':[],'last_exit':None,'oi_snapshot':None,'oi_history':[],
               'session_oi_baseline':None,'setup_watches':[],'thesis_history':[],'opportunity_journal':[]}
        original=legacy.get('active_position')
        if original is not None:
            if not isinstance(original,dict) or original.get('status')!='OPEN':
                raise StateError('Ambiguous legacy active position; reconcile before migrating')
            def required(name):
                value=original.get(name)
                if value is None:raise StateError('Legacy active position lacks '+name)
                return value
            p={'id':required('position_id'),'status':'OPEN','direction':required('direction'),'instrument_key':required('instrument_key'),
               'expiry':required('expiry'),'side':required('side'),'strike':required('strike'),'session_date':required('session_date'),
               'opened_at':required('opened_at'),'last_candle':required('last_monitored_candle'),'entry_spot':required('entry_spot'),
               'entry_ask':required('entry_premium_ask'),'stop':required('stop_underlying'),'t1':required('t1_underlying'),
               't2':required('t2_underlying'),'best_spot':required('favourable_spot_extreme'),'t1_hit':bool(original.get('t1_hit')),
               'remaining_pct':required('remaining_pct'),'contract':original.get('selected_contract') or {},
               'plan':{'t1_underlying':required('t1_underlying'),'t2_underlying':required('t2_underlying')},
               'last_progress_at':original.get('last_checked_at') or required('opened_at'),'migrated_legacy_position':True}
            if p['t1_hit']:
                at=original.get('post_t1_started_at') or original.get('t1_hit_at')
                if not at:raise StateError('Legacy T1 runner has no T1 time; reconcile before migrating')
                p.update(t1_at=at,runner_started_at=at,runner_last_progress_at=original.get('post_t1_last_progress_at') or at,
                         runner_progress_anchor=original.get('post_t1_anchor_spot') or p['t1'],runner_peak_spot=original.get('post_t1_peak_spot') or p['t1'],
                         runner_peak_bid=original.get('post_t1_peak_premium_bid'))
            validate_position(p);state['position']=p
        prior_exit=legacy.get('last_position_exit') or {}
        if prior_exit.get('closed_at'):
            closed_at=datetime.fromisoformat(prior_exit['closed_at']);origin=closed_at.replace(hour=9,minute=15,second=0,microsecond=0)
            elapsed=int((closed_at-origin).total_seconds()//180);last_completed=origin+timedelta(minutes=3*(elapsed-1))
            state['last_exit']={'at':prior_exit['closed_at'],'direction':prior_exit.get('direction'),'three':last_completed.isoformat()}
        state['legacy_position_history']=legacy.get('position_history') or []
        state['legacy_notification_history']=legacy.get('notification_history') or []
        for item in legacy.get('pending_notifications') or []:
            details={'legacy_notification':item,'source_version':legacy.get('scanner_version'),'historical':True}
            event=queue(state,'LEGACY_NOTIFICATION_REVIEW_REQUIRED',details,now)
            entry=next((e for e in state['outbox'] if e['id']==event))
            entry.update(status='DELIVERY_UNCERTAIN',delayed_delivery=True)
    else:
        raise StateError('Unsupported migration schema; no state was created')

    digest=hashlib.sha256(raw).hexdigest()
    archive=destination.parent/'archives_v119_2'/(source.name+'.'+digest[:16]+'.json')
    if not archive.exists():
        archive.parent.mkdir(parents=True,exist_ok=True)
        fd,tmp=tempfile.mkstemp(dir=archive.parent,prefix='.migration-')
        try:
            with os.fdopen(fd,'wb') as stream:
                stream.write(raw);stream.flush();os.fsync(stream.fileno())
            os.replace(tmp,archive)
        finally:
            if os.path.exists(tmp):os.unlink(tmp)
    state['entry_quality_revision']=1192
    state['migration']={'source_file':source.name,'source_sha256':digest,'archive':str(archive),'at':now.isoformat()}
    save(destination,state);load(destination)
    return state


@contextmanager
def lock(path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(str(path) + '.lock', 'a+') as f:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise StateError('Another local scan is running') from None
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)

def save(path: Path, state: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix='.' + path.name + '.', dir=path.parent)
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as f:
            json.dump(state, f, sort_keys=True, separators=(',', ':'), allow_nan=False)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
        directory = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)

def load(path: Path, allow_legacy=False):
    if not path.exists():
        raise StateError('STATE_NOT_INITIALIZED: reconcile prior scanner and initialize the new state')
    try:
        def invalid_number(value):
            raise ValueError('Non-finite number in state')
        with path.open(encoding='utf-8') as f:
            state=json.load(f,parse_constant=invalid_number,parse_float=finite_json_float)
    except (OSError,ValueError) as exc:
        raise StateError('State is unreadable; reconcile before continuing') from exc
    allowed=(1,2,3,4,5,6,7) if allow_legacy else (7,)
    if not isinstance(state,dict) or state.get('schema') not in allowed or not isinstance(state.get('outbox'),list) or 'position' not in state or not isinstance(state.get('history'),list):
        raise StateError('Unsupported or invalid state; reconcile before continuing')
    if state['position'] is not None:
        p=state['position']
        if not isinstance(p,dict) or p.get('status')!='OPEN' or p.get('direction') not in ('BULLISH','BEARISH') or not all(k in p for k in ('id','instrument_key','expiry','entry_spot','entry_ask','stop','t1','t2','opened_at','last_candle')):
            raise StateError('Invalid open position; lock requires reconciliation')
    seen=set()
    for event in state['outbox']:
        if not isinstance(event,dict) or not all(k in event for k in ('id','kind','details','created_at','status')) or event['id'] in seen or event['status'] not in ('PENDING','CLAIMED','SENT','DELIVERY_UNCERTAIN','EXPIRED'):
            raise StateError('Invalid notification outbox')
        seen.add(event['id'])
    if state['position'] is not None:validate_position(state['position'])
    for key in ('price_action_ledger','market_phase'):
        if key in state and not isinstance(state[key],dict):
            raise StateError('Invalid v119.1 market-state collection: '+key)
    for field in ('setup_watches','thesis_history','opportunity_journal'):
        if field in state and not isinstance(state[field],list):
            raise StateError('Invalid state collection: '+field)
    state.setdefault('oi_history',[]);state.setdefault('session_oi_baseline',None);state.setdefault('setup_watches',[]);state.setdefault('thesis_history',[]);state.setdefault('opportunity_journal',[])
    if not allow_legacy:
        if state.get('entry_quality_revision') not in (1191, 1192):
            raise StateError('SCHEMA7_PREVIOUS_STATE_REQUIRES_OPERATOR_MIGRATION: do not copy an older state in place')
        state['schema']=7;state['engine_version']='120.1.0'
    return state


def initialize(path: Path, now: datetime):
    if path.exists():raise StateError('State already exists; refusing to overwrite')
    save(path,{'schema':7,'engine_version':'120.1.0','initialized_at':now.isoformat(),'initialized_flat':True,'entry_quality_revision':1192,'session_date':None,
               'thesis':None,'position':None,'history':[],'outbox':[],'last_exit':None,'oi_snapshot':None,'oi_history':[],
               'session_oi_baseline':None,'setup_watches':[],'thesis_history':[],'opportunity_journal':[]})


def queue(state: dict, kind: str, details: dict, when: datetime):
    raw = json.dumps([kind, details], sort_keys=True, separators=(',', ':'), allow_nan=False)
    event_id = hashlib.sha256(raw.encode()).hexdigest()[:24]
    if kind != 'ENTRY':
        return event_id  # non-entry is always captured in audit, never emailed
    if not any((x['id'] == event_id for x in state['outbox'])):
        state['outbox'].append({'id': event_id, 'kind': kind, 'created_at': when.isoformat(), 'details': copy.deepcopy(details), 'status': 'PENDING', 'claim': None})
    return event_id

def claim(state: dict, token: str, now=None):
    if not token or len(token) > 160:
        raise StateError('Notification claim token required')
    for event in state['outbox']:
        if event['status'] == 'PENDING' and event.get('kind') == 'ENTRY':
            if now and (now - datetime.fromisoformat(event['created_at'])).total_seconds() > 8 * 60:
                event['delayed_delivery'] = True
            event.update(status='CLAIMED', claim=token)
    sent = [e for e in state['outbox'] if e['status'] == 'SENT']
    if len(sent) > 1000:
        keep = {e['id'] for e in sent[-1000:]}
        state['outbox'] = [e for e in state['outbox'] if e['status'] != 'SENT' or e['id'] in keep]

def append_audit(path: Path, event: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(event, sort_keys=True, separators=(',', ':'), allow_nan=False) + '\n'
    with path.open('a', encoding='utf-8') as f:
        f.write(line)
        f.flush()
        os.fsync(f.fileno())

def capture_inputs(directory: Path, identifier: str, data: dict) -> dict:
    """Write reproducible market inputs without credentials or inferred candle prices."""
    import gzip
    directory.mkdir(parents=True, exist_ok=True)
    raw = json.dumps(data, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()
    content = gzip.compress(raw, mtime=0)
    path = directory / (identifier + '.json.gz')
    if path.exists():
        identifier = identifier + '-' + hashlib.sha256(content).hexdigest()[:12]
        path = directory / (identifier + '.json.gz')
    fd, tmp = tempfile.mkstemp(dir=directory, prefix='.inputs-')
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)
    return {'path': str(path), 'sha256': hashlib.sha256(content).hexdigest(), 'format': 'RECORDED_INPUTS_V1'}

def wire(value):
    from datetime import date
    if isinstance(value, datetime):
        return {'__datetime__': value.isoformat()}
    if isinstance(value, date):
        return {'__date__': value.isoformat()}
    if isinstance(value, Path):
        return {'__path__': str(value)}
    if isinstance(value, tuple):
        return {'__tuple__': [wire(x) for x in value]}
    if isinstance(value, list):
        return [wire(x) for x in value]
    if isinstance(value, dict):
        return {k: wire(v) for k, v in value.items()}
    return value

def unwire(value):
    from datetime import date
    if isinstance(value, list):
        return [unwire(x) for x in value]
    if isinstance(value, dict):
        if set(value) == {'__datetime__'}:
            return datetime.fromisoformat(value['__datetime__'])
        if set(value) == {'__date__'}:
            return date.fromisoformat(value['__date__'])
        if set(value) == {'__path__'}:
            return Path(value['__path__'])
        if set(value) == {'__tuple__'}:
            return tuple((unwire(x) for x in value['__tuple__']))
        return {k: unwire(v) for k, v in value.items()}
    return value

class RecordingAPI:
    """Record public market-data method results only, never headers or tokens."""
    methods = {'session', 'candles', 'contracts', 'chain', 'quotes', 'nearest_nifty_future', 'previous_session'}

    def __init__(self, api, events):
        self.api = api
        self.events = events

    def __getattr__(self, name):
        target = getattr(self.api, name, None)
        if name == 'previous_session' and target is None:
            def target(*args, **kwargs):
                raise ProviderError('Previous day enrichment not implemented by adapter')
        elif target is None:
            raise AttributeError(name)
        if name not in self.methods or not callable(target):
            return target

        def call(*args, **kwargs):
            row = {'method': name, 'args': wire(args), 'kwargs': wire(kwargs)}
            self.events.append(row)
            try:
                result = target(*args, **kwargs)
                row['result'] = wire(result)
                return result
            except Exception as exc:
                row['error_type'] = type(exc).__name__
                row['error_message'] = str(exc) if type(exc).__name__ in ('ProviderError', 'DataError') else 'Market adapter failed'
                raise
        return call


# scanner/forecasting.py
from datetime import datetime, timedelta
import hashlib

def forecast_report(records):
    """Report directional outcomes, not simulated option fills or trade P&L."""
    settled = [r for r in records if r.get('status') == 'ASSESSED']
    correct = sum((r['directional_correct_at_horizon'] for r in settled))
    by_scenario = {}
    for row in settled:
        name = row['primary_scenario']
        result = by_scenario.setdefault(name, {'assessed': 0, 'directionally_correct': 0})
        result['assessed'] += 1
        result['directionally_correct'] += int(row['directional_correct_at_horizon'])
    return {'scope': 'FORWARD_UNDERLYING_DIRECTION_ONLY_NOT_OPTION_TRADE_PERFORMANCE', 'recorded': len(records), 'assessed': len(settled), 'directionally_correct': correct, 'directional_accuracy': correct / len(settled) if settled else None, 'pending': sum((r.get('status') == 'PENDING' for r in records)), 'unscorable': sum((r.get('status') == 'UNSCORABLE' for r in records)), 'by_scenario': by_scenario, 'probability_calibration_established': False}

def record_and_assess(state, bars, now, forecast, horizon_minutes=15):
    """Freeze today's outlook before observing its later, completed candles.

    The minute containing the creation quote is excluded from excursions
    because its extremes could precede the observation. Every subsequent
    required minute must be present. Missing values are never interpolated.
    """
    records = state.setdefault('forecast_records', [])
    by_time = {c.start: c for c in bars}
    for record in records:
        if record.get('status') != 'PENDING':
            continue
        made = datetime.fromisoformat(record['created_at'])
        due = made + timedelta(minutes=record['horizon_minutes'])
        end = due.replace(second=0, microsecond=0)
        if due > end:
            end += timedelta(minutes=1)
        if now < end:
            continue
        first = made.replace(second=0, microsecond=0)
        if made > first:
            first += timedelta(minutes=1)
        times = []
        cursor = first
        while cursor < end:
            times.append(cursor)
            cursor += timedelta(minutes=1)
        if not times or any((t not in by_time for t in times)):
            record.update(status='UNSCORABLE', reason='INCOMPLETE_FORWARD_MINUTE_PATH', assessed_at=now.isoformat())
            continue
        path = [by_time[t] for t in times]
        sign = 1 if record['direction'] == 'BULLISH' else -1
        baseline = record['spot_at_creation']
        move = sign * (path[-1].close - baseline)
        favorable = max((sign * ((c.high if sign == 1 else c.low) - baseline) for c in path))
        adverse = max((-sign * ((c.low if sign == 1 else c.high) - baseline) for c in path))
        record.update(status='ASSESSED', assessed_at=now.isoformat(), endpoint_at=end.isoformat(), endpoint_spot=path[-1].close, signed_change_underlying=move, favorable_excursion_points=max(0.0, favorable), adverse_excursion_points=max(0.0, adverse), directional_correct_at_horizon=move > 0)
    direction = forecast.get('directional_thesis')
    ready = forecast.get('entry_readiness', 'ASSESS_TRIGGER') == 'ASSESS_TRIGGER'
    if direction in ('BULLISH', 'BEARISH') and ready and (not forecast.get('primary_scenario', '').startswith('STRUCTURAL_BREAK_')):
        slot = forecast['as_of']
        identifier = hashlib.sha256((now.date().isoformat() + '|' + slot + '|' + direction).encode()).hexdigest()[:24]
        if not any((r['id'] == identifier for r in records)):
            records.append({'id': identifier, 'created_at': now.isoformat(), 'forecast_bar_end': slot, 'horizon_minutes': horizon_minutes, 'direction': direction, 'spot_at_creation': forecast['spot'], 'primary_scenario': forecast['primary_scenario'], 'protected_boundary': forecast.get('protected_boundary'), 'status': 'PENDING'})
    pending = [r for r in records if r['status'] == 'PENDING']
    settled = [r for r in records if r['status'] != 'PENDING'][-500:]
    state['forecast_records'] = settled + pending
    return forecast_report(state['forecast_records'])


# scanner/entry_quality_v119.py (embedded in standalone release)

def _opposing_level_role(level: dict, direction: str) -> str | None:
    """Return a structural/OI role only when it actually opposes a trade.

    An old support above the current spot is NOT silently a resistance; it
    becomes one only after documented breakdown acceptance/retest.
    """
    source=str(level.get('source') or '')
    kind=str(level.get('kind') or '')
    bullish=direction=='BULLISH'
    if direction not in ('BULLISH','BEARISH'):
        return None
    if source.startswith('PRICE_ACTION_'):
        role=source.removeprefix('PRICE_ACTION_')
        return role if (role=='RESISTANCE' if bullish else role=='SUPPORT') else None
    if kind=='OI':
        if (bullish and source=='OI_CE') or (not bullish and source=='OI_PE'):
            return 'OI_WALL'
        return None
    exact={
        'OPENING_SIX_MINUTE_HIGH':'RESISTANCE',
        'OPENING_SIX_MINUTE_LOW':'SUPPORT',
        'PREVIOUS_SESSION_HIGH':'RESISTANCE',
        'PREVIOUS_SESSION_LOW':'SUPPORT',
        'PROTECTED_RESISTANCE':'RESISTANCE',
        'PROTECTED_SUPPORT':'SUPPORT',
        'CONFIRMED_3M_PIVOT_RESISTANCE':'RESISTANCE',
        'CONFIRMED_3M_PIVOT_SUPPORT':'SUPPORT',
        'CONFIRMED_PIVOT_HIGH':'RESISTANCE',
        'CONFIRMED_PIVOT_LOW':'SUPPORT',
        'CONFIRMED_15M_PIVOT_HIGH':'RESISTANCE',
        'CONFIRMED_15M_PIVOT_LOW':'SUPPORT',
        'COMPLETED_15M_CONTEXT_HIGH':'RESISTANCE',
        'COMPLETED_15M_CONTEXT_LOW':'SUPPORT',
    }
    role=exact.get(source)
    if role==( 'RESISTANCE' if bullish else 'SUPPORT'):
        return role
    return None


def _completed_acceptance(bars: list[Candle], level: float, direction: str,
                          zone: float, atr_1m: float, config: Config) -> bool:
    """Two *closed* consecutive 3-minute candles establish acceptance.

    Current live quotes, incompletely formed bars and future bars are excluded.
    This intentionally matches v118.3 price-level replay acceptance rules.
    """
    sign=1 if direction=='BULLISH' else -1
    threes=aggregate(bars,3)
    if len(threes)<2:
        return False
    band=max(zone,0.5,config.acceptance_buffer_atr*atr_1m)
    return all(sign*(c.close-level)>band for c in threes[-2:])


def _level_recently_interacted(bars: list[Candle], level: float,
                               a: float, config: Config) -> bool:
    band=max(1.0,config.oi_touch_tolerance_atr*a)
    return any(c.low-band<=level<=c.high+band for c in bars[-config.recent_oi_touch_bars:])


def quote_entry_gate(setup: dict, bars: list[Candle], live_spot: float,
                     config: Config) -> tuple[bool,str,dict]:
    """Prevent stale confirmation watches from trading a now-reversing quote."""
    d=setup.get('direction')
    if d not in ('BULLISH','BEARISH') or len(bars)<config.min_bars or not isfinite(live_spot):
        return False,'ENTRY_QUALITY_INPUT_INVALID',{}
    sign=1 if d=='BULLISH' else -1
    a=max(1.0,atr(bars))
    last=bars[-1]
    stop=float(setup.get('trade_invalidation',setup['invalidation']))
    risk=sign*(live_spot-stop)
    if risk<=0 or not isfinite(risk):
        return False,'ENTRY_QUALITY_STOP_ON_WRONG_SIDE',{}
    adverse= -sign*(live_spot-last.close)
    adverse_limit=max(config.quote_adverse_min_points,
                      config.quote_adverse_atr*a,
                      config.quote_adverse_risk_fraction*risk)
    extension=sign*(live_spot-float(setup['trigger']))
    extension_limit=min(config.quote_chase_atr*a,
                        config.quote_chase_risk_fraction*risk)
    diagnostics={'last_completed_close':last.close,'live_spot':live_spot,
                 'quote_adverse_points':round(adverse,5),
                 'adverse_limit_points':round(adverse_limit,5),
                 'extension_points':round(extension,5),
                 'extension_limit_points':round(extension_limit,5),
                 'setup_confirmed_at':setup.get('confirmed_at'),
                 'setup_kind':setup.get('kind')}
    if adverse>adverse_limit:
        return False,'LIVE_QUOTE_REVERSED_FROM_COMPLETED_TRIGGER',diagnostics
    # For a normal trend watch, extension is not evidence of a better entry.
    # Local acceptance/reclaim watches still get a risk-scaled extension window.
    if extension>extension_limit:
        return False,'LIVE_QUOTE_CHASING_PAST_SETUP',diagnostics
    # Opposite closed-minute movement signals a conflict with the saved watch.
    window=bars[-config.reversal_short_window_bars:]
    shift=-sign*(window[-1].close-window[0].open)
    diagnostics['recent_adverse_shift_points']=round(shift,5)
    if shift>=0.85*a and sign*(last.close-last.open)<0 and not str(setup.get('kind','')).startswith('EARLY_'):
        return False,'RECENT_COMPLETED_MINUTE_MOMENTUM_REVERSED',diagnostics
    return True,'LIVE_QUOTE_ENTRY_QUALITY_VALID',diagnostics


def target_and_time_gate(setup: dict, plan: dict, bars: list[Candle],
                         live_spot: float, context: dict, now: datetime,
                         config: Config) -> tuple[dict | None,str,dict]:
    """Place achievable T1 before unaccepted opposition, then test time budget.

    This gate is AFTER underlying risk calculation but BEFORE contract ranking.
    The gate can only decrease T1, and never expands a stop, increases a
    target or treats a potential OI level as certain participant intent.
    """
    direction=setup.get('direction')
    if direction not in ('BULLISH','BEARISH') or now.tzinfo is None:
        return None,'INVALID_TARGET_TIME_GATE',{}
    sign=1 if direction=='BULLISH' else -1
    a=max(1.,atr(bars))
    risk=float(plan['risk_points'])
    minimum_reward=risk*config.min_rr
    proposed=float(plan['t1_underlying'])
    proposed_distance=sign*(proposed-live_spot)
    level_diagnostics=[]
    candidate_barriers=[]
    for row in context.get('levels') or []:
        try:
            role=_opposing_level_role(row,direction)
            if not role:continue
            level=float(row['price']);distance=sign*(level-live_spot)
            zone=max(0.0,float(row.get('zone_half_width') or 0.0))
            if not isfinite(level) or not isfinite(zone):continue
            if distance< -max(zone,a*config.barrier_reward_safety_atr):
                continue  # Opposing wall has already been crossed.
            accepted=_completed_acceptance(bars,level,direction,zone,a,config)
            # A quote on the new side of the level is not, by itself, acceptance.
            if distance<=0 and not accepted and abs(distance)>max(zone,0.25*a):
                continue  # Farther-behind wall cannot block current reward path.
            relative=max(0.0,min(1.0,float(row.get('significance') or 1)-1)) if role=='OI_WALL' else 0.0
            interacted=_level_recently_interacted(bars,level,a,config)
            confirmed=bool(row.get('hard_barrier') or row.get('price_rejection_confirmed'))
            structural=bool(role!='OI_WALL' and (confirmed or (interacted and
                (str(row.get('source') or '').startswith(('PROTECTED_','PREVIOUS_SESSION_','OPENING_','CONFIRMED_','COMPLETED_'))))))
            oi_material=bool(role=='OI_WALL' and relative>=config.oi_obstruction_min_relative and
                             (interacted or relative>=config.oi_obstruction_very_strong_relative))
            material=confirmed or structural or oi_material
            margin=max(zone,config.barrier_reward_safety_atr*a)
            clearance=distance-margin
            record={'source':row.get('source'),'price':level,'role':role,
                'distance_points':round(distance,5),'zone_half_width':round(zone,5),
                'usable_clearance_points':round(clearance,5),
                'accepted_by_two_closed_3m':accepted,
                'confirmed_price':confirmed,'recent_price_interaction':interacted,
                'material':material,'oi_relative':round(relative,4),
                'classification':('ACCEPTED' if accepted else 'CONFIRMED_PRICE' if confirmed
                                  else 'MATERIAL_PRICE_LEVEL' if structural else 'OI_PRICE_CONFLUENCE' if oi_material
                                  else 'SOFT_OBSERVATION')}
            level_diagnostics.append(record)
            if material and not accepted and distance>=-margin:
                candidate_barriers.append((clearance,record))
        except (KeyError,ValueError,TypeError,OverflowError):
            continue
    candidate_barriers.sort(key=lambda x:x[0])
    diagnostics={'opposing_levels':sorted(level_diagnostics,key=lambda x:x['distance_points'])[:25],
                 'minimum_reward_points':round(minimum_reward,5),
                 'planned_t1_before_gate':proposed,
                 'risk_points':risk,
                 'atr_1m':round(a,5),
                 'barrier_policy':'PRICE_CONFIRMED_OR_CONTEXTUAL_SIGNIFICANT_UNACCEPTED_REACTION'}
    # Determine target room only from the nearest *material* unaccepted level
    # in the proposed route, not from a distant irrelevant OI concentration.
    if candidate_barriers:
        headroom,level_record=candidate_barriers[0]
        diagnostics['nearest_material_obstruction']=level_record
        if headroom+1e-8<minimum_reward:
            return None,'OPPOSING_LEVEL_INSUFFICIENT_ACHIEVABLE_REWARD',diagnostics
        if headroom+1e-8<proposed_distance:
            capped=live_spot+sign*headroom
            if sign*(capped-live_spot)+1e-8<minimum_reward:
                return None,'MATERIAL_LEVEL_T1_BELOW_MINIMUM_RR',diagnostics
            plan=dict(plan)
            plan['t1_underlying']=round(capped,5)
            plan['underlying_rr']=round(headroom/risk,5)
            plan['target_source']='V1191_PRE_UNACCEPTED_LEVEL_BUFFER'
            plan['target_quality']='CONSERVATIVE_OPPOSING_LEVEL_CAP'
            plan['projected_target_not_historical_resistance']=False
            plan['t1_capped_from']=round(proposed,5)
            plan['target_cap_obstruction']=level_record
            diagnostics['adjusted_t1']=plan['t1_underlying']
    now_ist=now.astimezone(IST)
    minutes_left=max(0.0,(intraday_hard_exit_at(now_ist,config)-now_ist).total_seconds()/60)
    usable=max(0.0,minutes_left-config.last_minute_dispatch_buffer)
    target_distance=sign*(float(plan['t1_underlying'])-live_spot)
    baseline_budget=config.last_minute_budget_atr_sqrt*a*(usable**0.5)
    # Momentum forecast is explicitly capped to avoid extrapolating an
    # unusually large recent 3m candle indefinitely into the close.
    recent=aggregate(bars,3)[-3:]
    completed_velocity=max(0.0,sign*(recent[-1].close-recent[0].open)/max(3.0,len(recent)*3.0)) if recent else 0.0
    momentum_budget=min(2*baseline_budget,completed_velocity*usable)
    budget=max(baseline_budget,momentum_budget)
    diagnostics.update(minutes_until_hard_exit=round(minutes_left,4),
                       usable_minutes_after_dispatch=round(usable,4),
                       time_budget_points=round(budget,4),
                       t1_distance_points=round(target_distance,4),
                       completed_momentum_velocity=round(completed_velocity,4),
                       time_model='ATR_SQRT_WINDOW_OR_CAPPED_CAUSAL_3M_VELOCITY_NO_PROBABILITY')
    if minutes_left<config.minimum_entry_to_exit_minutes:
        return None,'INSUFFICIENT_INTRADAY_HOLDING_WINDOW',diagnostics
    if target_distance>budget+1e-8:
        return None,'T1_UNLIKELY_WITHIN_REMAINING_SESSION_BUDGET',diagnostics
    plan=dict(plan)
    plan['entry_quality']={'evaluated_at':now.isoformat(),
                           'nearest_material_obstruction':diagnostics.get('nearest_material_obstruction'),
                           'minutes_until_exit':diagnostics['minutes_until_hard_exit'],
                           'time_budget_points':diagnostics['time_budget_points'],
                           'price_levels_audited':len(level_diagnostics)}
    return plan,'V1191_ENTRY_CLEARANCE_TARGET_TIME_VALID',diagnostics


# scanner/position.py
from datetime import datetime, timedelta
from math import isfinite

# v119.1 independent, completed-candle chronological position management.
from datetime import datetime, timedelta
from math import isfinite

def intraday_hard_exit_at(reference: datetime, config: Config) -> datetime:
    """Absolute IST end-of-day exit required by the strategy contract.

    This is intentionally independent of the exchange-reported NFO session end.
    The scanner may still use the exchange session for data validity, but every
    reference option position must be flat at the first scan at/after 15:15 IST.
    """
    if reference.tzinfo is None:
        raise DataError('NAIVE_INTRADAY_EXIT_REFERENCE')
    local=reference.astimezone(IST)
    return local.replace(hour=config.intraday_hard_exit_hour,
                         minute=config.intraday_hard_exit_minute,
                         second=0,microsecond=0)


def entry_cutoff_at(reference: datetime, config: Config) -> datetime:
    return intraday_hard_exit_at(reference,config)-timedelta(minutes=config.entry_cutoff_lead_minutes)


def manage(position, bars, spot, quote, now, market_close, config, structure=None, oi=None):
    """Manage the *alert reference*, not a broker-confirmed position or fill.

    No assumption about the ordering of extremes inside a minute: when a stop
    and target are both touched, prefer the adverse stop. Missing intervals
    raise DataError; the orchestration retains the original contract lock.
    """
    p=copy.deepcopy(position)
    plan_check=p.get('plan') or {}
    if any(plan_check.get(field) is not None and float(plan_check[field]) != float(p[target]) for field,target in [('t1_underlying','t1'),('t2_underlying','t2')]):
        raise DataError('FIXED_TARGETS_CHANGED')
    validate_position(p)
    events=[]; oi=oi or {}
    direction=p['direction']; sign=1 if direction=='BULLISH' else -1
    opened=datetime.fromisoformat(p['opened_at'])
    checkpoint=datetime.fromisoformat(p['last_candle'])
    if opened>now or checkpoint>now.replace(second=0,microsecond=0):
        raise DataError('POSITION_CLOCK_NOT_MONOTONIC')
    ordered=sorted(bars,key=lambda b:b.start)
    hard_exit=intraday_hard_exit_at(now,config)
    unseen=[c for c in ordered if c.start>checkpoint]
    # If a scan is delayed beyond 15:15, only events that were knowable by the
    # mandated exit time are allowed to affect the position. Later candles must
    # never retroactively change a position that should already be flat.
    new=[c for c in unseen if now<hard_exit or c.start+timedelta(minutes=1)<=hard_exit]
    if new and new[0].start!=checkpoint+timedelta(minutes=1):
        raise DataError('POSITION_MONITORING_CANDLE_GAP')
    if any(b.start-a.start!=timedelta(minutes=1) for a,b in zip(new,new[1:])):
        raise DataError('POSITION_MONITORING_CANDLE_GAP')
    if any(c.start+timedelta(minutes=1)>now for c in new):
        raise DataError('UNCOMPLETED_POSITION_CANDLE')
    # The entry checkpoint is initialized to the minute containing the alert.
    # Review that completed candle once, separately from the later candles.
    # Its OHLC cannot establish whether a touch preceded or followed entry.
    entry_start = opened.replace(second=0, microsecond=0)
    if not p.get('entry_minute_reviewed') and now >= entry_start + timedelta(minutes=1):
        entry_bars = [c for c in ordered if c.start == entry_start]
        if not entry_bars:
            events.append({'kind':'MONITORING_DEGRADED', 'position_id':p['id'],
                           'at':now.isoformat(), 'reason':'ENTRY_MINUTE_HISTORY_UNAVAILABLE',
                           'fill_confirmed':False})
        else:
            entry_bar = entry_bars[0]
            adverse = entry_bar.low if sign == 1 else entry_bar.high
            favourable = entry_bar.high if sign == 1 else entry_bar.low
            # A migrated position may already have a ratcheted stop. Prefer
            # the original plan rather than projecting a later stop backward.
            initial_stop = (p.get('plan') or {}).get('stop_underlying')
            initial_stop = float(initial_stop) if initial_stop is not None else float(p['stop'])
            touched = []
            if sign*(adverse-initial_stop) <= 0:
                touched.append('STOP')
            if sign*(favourable-p['t1']) >= 0:
                touched.append('T1')
            if touched:
                events.append({'kind':'MONITORING_DEGRADED', 'position_id':p['id'],
                               'at':(entry_start+timedelta(minutes=1)).isoformat(),
                               'reason':'ENTRY_MINUTE_TOUCH_ORDER_UNKNOWN',
                               'possible_touches':touched, 'stop_reference':initial_stop,
                               'stop_reference_source':'INITIAL_PLAN' if (p.get('plan') or {}).get('stop_underlying') is not None else 'CURRENT_STOP_LEGACY',
                               'fill_confirmed':False})
        p['entry_minute_reviewed'] = True
    quote_bid=None
    if quote:
        try:
            stamped=parse_feed_timestamp(quote['timestamp'])
            age=(now-stamped).total_seconds()
            bid=float(quote['bid'])
            if stamped.tzinfo and -2<=age<=config.max_quote_age and isfinite(bid) and bid>0:
                quote_bid=bid
                p['last_bid']=bid
                p['last_bid_at']=stamped.isoformat()
        except (KeyError,ValueError,TypeError):pass
    volatility=max(atr(ordered),1)
    progress_increment=max(2,config.runner_progress_atr*volatility)

    def update_stop(new_stop,why,at):
        if not isfinite(new_stop):return
        if sign*(new_stop-p['stop'])<=0:return
        if sign*(p['best_spot']-new_stop)<=0:return
        former=p['stop']
        p['stop']=round(new_stop,5)
        events.append({'kind':'STOP_RATCHET','position_id':p['id'],'at':at.isoformat(),
                       'old_stop':former,'new_stop':p['stop'],'source':why,
                       'broker_order_amended':False})

    def finish(reason,at,reference,origin):
        p.update(status='CLOSED',closed_at=at.isoformat(),exit_reason=reason,
                 exit_reference_spot=reference,exit_source=origin,remaining_pct=0,
                 fill_confirmed=False)
        return None, events+[{'kind':'EXIT','position':copy.deepcopy(p),
                               'reason':reason,'detected_at':now.isoformat(),
                               'event_time':at.isoformat(),'reference_spot':reference,
                               'source':origin,'reference_bid_at_detection':quote_bid,
                               'fill_confirmed':False}],p

    def target1(at,origin):
        if p.get('t1_hit'):return
        p.update(t1_hit=True,t1_at=at.isoformat(),runner_started_at=at.isoformat(),
                 runner_last_progress_at=at.isoformat(),runner_progress_anchor=p['t1'],
                 runner_peak_spot=p['t1'],runner_peak_bid=None,
                 runner_grace_used=False,management_state='RUNNER',remaining_pct=50)
        # A protected stop moves to break even. The ratio is a modelled slice,
        # never evidence that a broker executed a partial exit.
        p['stop']=max(float(p['stop']),float(p['entry_spot'])) if sign==1 else min(float(p['stop']),float(p['entry_spot']))
        events.append({'kind':'TARGET_1','position_id':p['id'],'at':at.isoformat(),
                       'reference_spot':p['t1'],'new_stop':p['stop'],
                       'remaining_pct':50,'source':origin,'broker_fill_confirmed':False})

    def progress(price,at):
        if sign*(price-p['best_spot'])>0:p['best_spot']=price
        anchor=float(p.get('progress_anchor',p['entry_spot']))
        if sign*(price-anchor)>=progress_increment:
            p.update(progress_anchor=price,last_progress_at=at.isoformat())
        if p.get('t1_hit'):
            if sign*(price-float(p.get('runner_peak_spot',p['t1'])))>0:
                p['runner_peak_spot']=price
            anchor=float(p.get('runner_progress_anchor',p['t1']))
            if sign*(price-anchor)>=progress_increment:
                p.update(runner_progress_anchor=price,runner_last_progress_at=at.isoformat())

    # Walk all unseen *completed* candles chronologically.
    for i,c in enumerate(new):
        if c.start<=opened.replace(second=0,microsecond=0):
            p['last_candle']=c.start.isoformat(); continue
        event_at=c.start+timedelta(minutes=1)
        adverse=c.low if sign==1 else c.high
        favourable=c.high if sign==1 else c.low
        if sign*(adverse-p['stop'])<=0:
            return finish('STOP_TOUCHED',event_at,p['stop'],'COMPLETED_1M_STOP_FIRST_IF_AMBIGUOUS')
        if not p.get('t1_hit') and sign*(favourable-p['t1'])>=0:
            target1(event_at,'COMPLETED_1M_EXTREME')
            # OHLC does not reveal whether the new breakeven stop was crossed
            # before or after T1. Use the conservative outcome, not a fill claim.
            if sign*(adverse-p['stop'])<=0:
                return finish('POST_T1_STOP_POSSIBLE_SAME_CANDLE',event_at,p['stop'],'AMBIGUOUS_1M_ADVERSE_ASSUMPTION')
        if p.get('t1_hit') and sign*(favourable-p['t2'])>=0:
            return finish('TARGET_2_TOUCHED',event_at,p['t2'],'COMPLETED_1M_EXTREME')
        progress(favourable,event_at)
        p['last_candle']=c.start.isoformat()
    if now>=hard_exit:
        exit_bar=next((c for c in reversed(ordered) if c.start+timedelta(minutes=1)==hard_exit),None)
        reference=float(exit_bar.close) if exit_bar is not None else float(spot)
        source='COMPLETED_1M_1515_CLOSE_REFERENCE' if exit_bar is not None else 'FRESH_LIVE_INDEX_QUOTE_AFTER_1515'
        return finish('INTRADAY_HARD_EXIT_1515',hard_exit,reference,source)
    # Live spot protects a position even if the option bid is missing.
    if sign*(spot-p['stop'])<=0:
        return finish('STOP_TOUCHED',now,spot,'FRESH_LIVE_INDEX_QUOTE')
    if not p.get('t1_hit') and sign*(spot-p['t1'])>=0:target1(now,'FRESH_LIVE_INDEX_QUOTE')
    if p.get('t1_hit') and sign*(spot-p['t2'])>=0:
        return finish('TARGET_2_TOUCHED',now,spot,'FRESH_LIVE_INDEX_QUOTE')
    progress(spot,now)
    # A genuine accepted structural reversal invalidates the previous trade.
    if structure and structure.get('boundary_trusted',True) and not structure.get('pending_break') and structure.get('direction') in ('BULLISH','BEARISH') and structure['direction']!=direction:
        rev=structure.get('last_reversal') or {}
        if rev.get('direction')==structure['direction'] and rev.get('confirmed_at'):
            if datetime.fromisoformat(rev['confirmed_at'])>=opened:
                return finish('OPPOSITE_STRUCTURE_CONFIRMED',now,spot,'TWO_CLOSED_3M_ACCEPTANCES')
    # Structural trailing uses fully confirmed three-minute pivots, and before
    # T1 additionally requires a fresh, matched positive OI change.
    completed_threes=aggregate(ordered,3)
    low,high=pivots(completed_threes)
    candidate_pivots=low if sign==1 else high
    eligible=[(t,v) for t,v in candidate_pivots if t>=opened]
    if eligible:
        _,pivot=eligible[-1]
        candidate=pivot-sign*max(config.stop_buffer,0.1*volatility)
        if p.get('t1_hit'):
            update_stop(candidate,'CONFIRMED_3M_RUNNER_STRUCTURE',now)
        else:
            wall=oi.get('put_support' if sign==1 else 'call_resistance') or {}
            supportive=(oi.get('fresh_snapshot') and wall.get('oi_change') is not None and
                        float(wall['oi_change'])>0 and wall.get('strike') is not None and
                        abs(float(wall['strike'])-pivot)<=config.strike_step)
            if supportive and sign*(spot-p['entry_spot'])>=progress_increment:
                update_stop(candidate,'CONFIRMED_3M_PIVOT_AND_MATCHED_OI',now)
    premium_drawdown=None; premium_cap=None
    if quote_bid is not None:
        if quote_bid<=float(p['entry_ask'])*(1-config.premium_hard_loss_pct/100):
            return finish('PREMIUM_LOSS_GUARD',now,spot,'FRESH_LIVE_OPTION_BID')
        if p.get('t1_hit'):
            # On the T1 detection scan no historical bid is invented; only
            # subsequent observed bids count for runner drawdown. Premium decay
            # is supporting evidence; it cannot override intact price structure.
            start=datetime.fromisoformat(p['runner_started_at'])
            if now>start:
                peak=max(float(p.get('runner_peak_bid') or 0),quote_bid)
                p['runner_peak_bid']=peak
                days_left=(market_close-now).total_seconds()/60
                same_day=p.get('expiry')==now.date().isoformat()
                premium_cap=config.premium_runner_drawdown_pct if not same_day else max(8.0,min(config.premium_runner_drawdown_pct,8+days_left/120*10))
                premium_drawdown=100*(peak-quote_bid)/peak
                p['runner_bid_drawdown_pct']=premium_drawdown
                p['runner_drawdown_limit_pct']=premium_cap

    def structure_weakening():
        if not structure:
            return False,{'available':False}
        same_thesis=(structure.get('direction')==direction and not structure.get('pending_break'))
        recent_opposed=(structure.get('recent_3m') in ('BULLISH','BEARISH') and structure.get('recent_3m')!=direction)
        context_opposed=(structure.get('context_15m') in ('BULLISH','BEARISH') and structure.get('context_15m')!=direction)
        local=structure.get('support' if sign==1 else 'resistance')
        local_failed=(local is not None and sign*(spot-float(local))<-max(config.stop_buffer,0.15*volatility))
        peak=float(p.get('runner_peak_spot') or p.get('best_spot') or p['entry_spot'])
        underlying_drawdown=max(0.0,sign*(peak-spot))
        meaningful_drawdown=underlying_drawdown>=max(0.75*volatility,progress_increment)
        stop_room=max(0.0,sign*(spot-float(p['stop'])))
        close_to_stop=stop_room<=max(0.75*volatility,2*config.stop_buffer)
        weakened=(not same_thesis and recent_opposed and meaningful_drawdown) or \
                 (recent_opposed and meaningful_drawdown and (context_opposed or local_failed or close_to_stop)) or \
                 (local_failed and meaningful_drawdown)
        return weakened,{'available':True,'same_thesis':same_thesis,'recent_3m_opposed':recent_opposed,
                         'context_15m_opposed':context_opposed,'local_structure_failed':local_failed,
                         'underlying_drawdown_points':round(underlying_drawdown,5),
                         'meaningful_underlying_drawdown':meaningful_drawdown,
                         'stop_room_points':round(stop_room,5),'close_to_stop':close_to_stop}

    weakened,weak_diag=structure_weakening()
    p['runner_structure_diagnostics']=weak_diag
    if p.get('t1_hit'):
        t1time=datetime.fromisoformat(p.get('runner_started_at') or p['t1_at'])
        last=datetime.fromisoformat(p.get('runner_last_progress_at') or p['t1_at'])
        idle=max(0.0,(now-last).total_seconds()/60)
        elapsed=max(0.0,(now-t1time).total_seconds()/60)
        theta=(p.get('contract') or {}).get('theta')
        decay=abs(float(theta))*elapsed/(1440*float(p['entry_ask'])) if theta is not None and isfinite(float(theta)) else None
        p.update(runner_idle_minutes=idle,estimated_runner_theta_fraction=decay,
                 runner_no_progress_3m_bars=int(idle//3),runner_structure_weakening=weakened)
        stalled=idle>=config.no_progress_minutes
        theta_caution=decay is not None and idle>=6 and decay>=0.005
        premium_material=(premium_drawdown is not None and premium_cap is not None and premium_drawdown>=premium_cap)
        premium_confirming=(premium_drawdown is not None and premium_cap is not None and premium_drawdown>=0.5*premium_cap)
        prolonged=idle>=max(config.no_progress_minutes+6,18)
        theta_material=decay is not None and decay>=0.01
        # Structure is primary. Time/theta and premium deterioration may confirm
        # a weakening runner, but never close an otherwise intact trend alone.
        if premium_material and weakened:
            return finish('RUNNER_PREMIUM_DRAWDOWN_WITH_STRUCTURE_WEAKENING',now,spot,'FRESH_LIVE_OPTION_BID_AND_PRICE_STRUCTURE')
        if weakened and stalled and (premium_confirming or prolonged or theta_material):
            return finish('RUNNER_STRUCTURE_WEAKENING_NO_PROGRESS',now,spot,'POST_T1_STRUCTURE_AND_PROGRESS')
        p['runner_theta_caution']=bool(theta_caution)
        p['runner_no_progress_caution']=bool(stalled)
    elif (now-opened).total_seconds()/60>=config.no_progress_minutes and sign*(p['best_spot']-p['entry_spot'])<.3*volatility:
        # Pre-T1 no-progress is not a standalone exit either. The tactical stop
        # and confirmed structure remain authoritative.
        if weakened:
            return finish('ENTRY_STRUCTURE_WEAKENING_NO_PROGRESS',now,spot,'PRE_T1_STRUCTURE_AND_PROGRESS')
        p['entry_no_progress_caution']=True
    if p.get('expiry')==now.date().isoformat() and (market_close-now).total_seconds()<=25*60 and p.get('t1_hit'):
        # No automatic expiry-window profit cutting while the protected
        # underlying move remains valid. The 15:15 hard exit still applies.
        p['expiry_runner_time_caution'] = True
    p['management_state']='RUNNER' if p.get('t1_hit') else 'INITIAL'
    p['last_checked_at']=now.isoformat()
    return p,events,None


def clock():
    return datetime.now(IST)

def release_fingerprint():
    """Bind replay evidence to these exact executable source bytes."""
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

def fresh_candles(api: Upstox, config: Config, raw=None, clock_fn=None, required_start=None, publication_deadline=None):
    """Fetch one immutable per-scan candle watermark with bounded provider grace.

    `required_start` is fixed by the caller at scan start.  A later wall-clock
    minute must never advance it.  If the provider has not published the candle
    that was already due at scan start, retries continue only until the deadline
    associated with that candle's completion boundary.
    """
    clock_source = clock_fn or clock
    first_now = clock_source()
    if first_now.tzinfo is None:
        raise DataError('NAIVE_CANDLE_TIME')
    required = required_start or scan_candle_watermark(first_now)
    if required.tzinfo is None:
        raise DataError('NAIVE_CANDLE_TIME')
    deadline = publication_deadline or candle_publication_deadline(required, config.candle_publication_grace_seconds)
    if deadline.tzinfo is None:
        raise DataError('NAIVE_CANDLE_TIME')
    max_attempts = max(1, int(config.candle_publication_grace_seconds / config.candle_retry_interval_seconds) + 2)
    attempt = 0
    now = first_now
    while attempt < max_attempts:
        if raw is None:
            raw = api.candles()
        bars, discarded = contiguous_tail(normalize_candles(raw, now, required))
        try:
            if not bars:
                raise DataError('LATEST_COMPLETED_CANDLE_MISSING')
            validate_candles(bars, now, config.min_bars, required_start=required)
            return (bars, discarded, now, attempt)
        except DataError as exc:
            if str(exc) != 'LATEST_COMPLETED_CANDLE_MISSING':
                raise
            current = clock_source()
            if current.tzinfo is None:
                raise DataError('NAIVE_CANDLE_TIME')
            if current >= deadline or attempt + 1 >= max_attempts:
                raise
            remaining = max(0.0, (deadline - current).total_seconds())
            sleep_for = min(float(config.candle_retry_interval_seconds), remaining)
            if sleep_for > 0 and not getattr(api, 'replay_mode', False):
                time.sleep(sleep_for)
            raw = None
            attempt += 1
            now = clock_source()
    raise DataError('LATEST_COMPLETED_CANDLE_MISSING')

def _chain_premium_proxy(row, max_spread_pct=15.0):
    """Prefer a valid two-sided chain midpoint; LTP is lower-confidence fallback."""
    try:
        last=float(row.get('ltp') or 0); bid=float(row.get('chain_bid') or 0); ask=float(row.get('chain_ask') or 0)
    except (TypeError,ValueError,OverflowError):return None,'UNAVAILABLE',0.0
    if not all(isfinite(x) for x in (last,bid,ask)):return None,'UNAVAILABLE',0.0
    if bid>0 and ask>=bid and ask>0:
        mid=(bid+ask)/2; spread=100*(ask-bid)/mid if mid>0 else float('inf')
        if mid>0 and spread<=max_spread_pct:return mid,'CHAIN_MID',1.0
    if last>0:return last,'LTP_FALLBACK_NO_EVENT_TIMESTAMP',0.60
    return None,'UNAVAILABLE',0.0


def _greek_adjusted_premium_change(current, previous, previous_spot, current_spot, elapsed_seconds, max_spread_pct=15.0):
    cur,cur_source,cur_quality=_chain_premium_proxy(current,max_spread_pct)
    old,old_source,old_quality=_chain_premium_proxy(previous,max_spread_pct)
    if cur is None or old is None or old<=0 or cur_source!=old_source:
        return None,None,'SOURCE_MISMATCH' if cur_source!=old_source else 'UNAVAILABLE',0.0
    raw_pct=100*(cur-old)/old
    names=('delta','gamma','theta','vega','iv')
    try:
        now_vals=[float(current[n]) for n in names]; old_vals=[float(previous[n]) for n in names]
        if previous_spot is None or float(previous_spot)<=0 or not all(isfinite(x) for x in now_vals+old_vals):raise ValueError
        delta_now,gamma_now,theta_now,vega_now,iv_now=now_vals
        delta_old,gamma_old,theta_old,vega_old,iv_old=old_vals
        move=float(current_spot)-float(previous_spot); elapsed_days=max(0.,elapsed_seconds)/86400
        expected=((delta_now+delta_old)/2)*move + .5*((gamma_now+gamma_old)/2)*move*move
        expected += ((theta_now+theta_old)/2)*elapsed_days + ((vega_now+vega_old)/2)*(iv_now-iv_old)
        residual_pct=100*((cur-old)-expected)/old
        if not isfinite(residual_pct):raise ValueError
        return raw_pct,residual_pct,'GREEK_ADJUSTED_'+cur_source,min(cur_quality,old_quality)
    except (KeyError,TypeError,ValueError,OverflowError):
        quality=min(cur_quality,old_quality)*(0.45 if cur_source=='CHAIN_MID' else 0.25)
        return raw_pct,raw_pct,'RAW_PREMIUM_FALLBACK_LOW_CONFIDENCE',quality


def oi_comparison(previous: dict | None, chain: list[dict], expiry: str, now: datetime,
                  spot: float | None=None, history: list[dict] | None=None,
                  session_baseline: dict | None=None, max_horizon_seconds: int=3600,
                  premium_proxy_max_spread_pct: float=15.0):
    """Identity-matched OI deltas plus an explicitly labelled opening baseline."""
    result={'status':'BASELINE_ONLY','flows':[], 'nearby_changes':[], 'horizons':[],
            'quality':'RECEIPT_TIME_NOT_EXCHANGE_SNAPSHOT_TIME','opening_baseline_status':'UNAVAILABLE'}

    def compare_snapshot(label,snap,allow_any_age=False):
        if not isinstance(snap,dict) or snap.get('expiry')!=expiry or snap.get('session_date')!=now.astimezone(IST).date().isoformat():return None
        try:
            stamp=datetime.fromisoformat(snap['fetched_at']); age=(now-stamp).total_seconds()
            if age<=0:return None
            if not allow_any_age and not 30<=age<=max_horizon_seconds:return None
            old={r['instrument_key']:r for r in snap['rows'] if isinstance(r,dict) and r.get('instrument_key')}
            changes=[]; flows=[]; matched=0; previous_spot=snap.get('spot')
            for r in chain:
                p=old.get(r.get('instrument_key'))
                if not p or any(p.get(k)!=r.get(k) for k in ('expiry','side','strike')):continue
                matched+=1; old_oi=float(p['oi']); new_oi=float(r['oi'])
                old_price,old_source,_=_chain_premium_proxy(p,premium_proxy_max_spread_pct)
                new_price,new_source,_=_chain_premium_proxy(r,premium_proxy_max_spread_pct)
                if old_price is None or new_price is None or old_source!=new_source:
                    old_price=float(p['ltp']);new_price=float(r['ltp']);flow_price_source='LTP_FALLBACK'
                else:flow_price_source=new_source
                flow=classify_flow(old_oi,new_oi,old_price,new_price,r['side'])
                raw,residual,premium_source,premium_quality=_greek_adjusted_premium_change(
                    r,p,previous_spot,spot if spot is not None else previous_spot,age,premium_proxy_max_spread_pct)
                if spot is None or abs(float(r['strike'])-spot)<=400:
                    changes.append({'instrument_key':r['instrument_key'],'strike':r['strike'],'side':r['side'],
                                    'previous_oi':old_oi,'current_oi':new_oi,'oi_change':new_oi-old_oi,
                                    'option_price_change':new_price-old_price,'classification':flow,'interval_seconds':age,
                                    'flow_price_source':flow_price_source,'premium_change_pct':raw,
                                    'greek_adjusted_residual_pct':residual,'premium_change_source':premium_source,
                                    'premium_source_quality':premium_quality})
                if flow not in ('UNAVAILABLE','UNCHANGED_OR_NOISY'):flows.append({'side':r['side'],'strike':r['strike'],'classification':flow})
            if not matched:return None
            return {'label':label,'interval_seconds':age,'fetched_at':stamp.isoformat(),'nearby_changes':changes,'flows':flows,'matched':matched,
                    'aggregate_ce_oi_change':sum(x['oi_change'] for x in changes if x['side']=='CE'),
                    'aggregate_pe_oi_change':sum(x['oi_change'] for x in changes if x['side']=='PE')}
        except (TypeError,KeyError,ValueError,OverflowError,ZeroDivisionError):return None

    sources=[]
    if previous:sources.append(('LAST_SUCCESSFUL',previous))
    for old in history or []:
        if isinstance(old,dict) and old.get('fetched_at')!=(previous or {}).get('fetched_at'):sources.append(('SESSION_HISTORY',old))
    usable=[x for x in (compare_snapshot(label,snap) for label,snap in sources) if x]
    if usable:
        usable.sort(key=lambda x:x['interval_seconds']);recent=usable[0]
        result.update(status='COMPARABLE_RECEIPT_TIMES_ONLY',flows=recent['flows'],nearby_changes=recent['nearby_changes'],
                      interval_seconds=recent['interval_seconds'],matched_contracts=recent['matched'],
                      horizons=[{k:v for k,v in h.items() if k not in ('nearby_changes','flows')} for h in usable])
    elif previous:result['status']='BASELINE_GAP'

    baseline=compare_snapshot('SESSION_BASELINE',session_baseline,allow_any_age=True) if session_baseline else None
    if baseline:
        role=session_baseline.get('baseline_role')
        if role=='OPENING_SESSION_BASELINE' and session_baseline.get('opening_baseline_available') is True:
            result['opening_baseline_status']='AVAILABLE'
            result['opening_baseline_fetched_at']=baseline['fetched_at']
            result['session_baseline_oi_changes']=baseline['nearby_changes']
        else:
            result['opening_baseline_status']='UNAVAILABLE_FIRST_CAPTURE_WAS_LATE'
            result['first_observed_session_oi_changes']=baseline['nearby_changes']
            result['session_baseline_oi_changes']=[]
    else:
        result['session_baseline_oi_changes']=[]
    return result


def snapshot_compact(chain, expiry, timestamp, spot):
    """Bound storage while retaining exact identity and premium/Greek observations."""
    fields=('instrument_key','expiry','side','strike','oi','ltp','volume','chain_bid','chain_ask','chain_bid_qty','chain_ask_qty','delta','gamma','theta','vega','iv')
    rows=[{k:r.get(k) for k in fields} for r in chain if abs(float(r['strike'])-spot)<=650]
    return {'session_date':timestamp.astimezone(IST).date().isoformat(),'expiry':expiry,
            'fetched_at':timestamp.isoformat(),'spot':float(spot),'rows':rows}


def advance_oi_history(state, chain, expiry, timestamp, spot, baseline_cutoff_minutes=20):
    """Append receipts and preserve the first session capture with honest labelling."""
    new=snapshot_compact(chain,expiry,timestamp,spot); session_date=new['session_date']
    baseline=state.get('session_oi_baseline')
    if not isinstance(baseline,dict) or baseline.get('expiry')!=expiry or baseline.get('session_date')!=session_date:
        session_open=timestamp.astimezone(IST).replace(hour=9,minute=15,second=0,microsecond=0)
        age=(timestamp.astimezone(IST)-session_open).total_seconds()/60
        is_opening=0<=age<=baseline_cutoff_minutes
        baseline=dict(new,baseline_role='OPENING_SESSION_BASELINE' if is_opening else 'FIRST_OBSERVED_SESSION_SNAPSHOT_NOT_OPENING',
                      opening_baseline_available=is_opening)
        state['session_oi_baseline']=baseline
    older=state.get('oi_history') or []
    older=[x for x in older if isinstance(x,dict) and x.get('expiry')==expiry and x.get('session_date')==session_date]
    if not older or (timestamp-datetime.fromisoformat(older[-1]['fetched_at'])).total_seconds()>=30:older.append(new)
    state['oi_history']=older if len(older) <= 21 else [older[0], *older[-20:]]
    state['oi_snapshot']=new
    return new



# v119.1 reference-only recovery. NEVER represent a modeled signal as a broker fill.
# A broker position opened manually outside this scanner remains the operator's
# responsibility. A broker-submitted/confirmed or unclassified position stays locked.
def is_unexecuted_reference(position: Any) -> bool:
    return (isinstance(position, dict)
            and position.get('status') == 'OPEN'
            and position.get('reference_position') is True
            and position.get('broker_order_submitted') is False
            and position.get('broker_fill_confirmed') is False)


def expire_unexecuted_reference(state: dict, observed_at: datetime, config: Config,
                                cause: str) -> dict | None:
    """Retire only an explicitly unexecuted *scanner reference*, never a broker fill.

    The time of physical exchange execution and the 15:15 price are NOT known.
    Save both the logical policy cutoff and actual detection time. Preserve
    immutable original position, stop, targets, history, and outbox identity.
    """
    p = state.get('position')
    if not is_unexecuted_reference(p) or observed_at.tzinfo is None:
        return None
    try:
        day_text = p.get('session_date') or state.get('session_date')
        from datetime import date as _date
        position_day = _date.fromisoformat(str(day_text))
        opened_at = datetime.fromisoformat(p['opened_at']).astimezone(IST)
    except (ValueError, KeyError, TypeError, AttributeError):
        return None
    cutoff = datetime.combine(position_day,
                              datetime.min.time(), IST).replace(
                                  hour=config.intraday_hard_exit_hour,
                                  minute=config.intraday_hard_exit_minute)
    seen = observed_at.astimezone(IST)
    if opened_at > cutoff or seen < cutoff:
        return None
    closed = copy.deepcopy(p)
    closed.update(status='CLOSED', closed_at=seen.isoformat(),
                  exit_reason='UNOBSERVED_1515_REFERENCE_CUTOFF',
                  exit_source='SCANNER_POLICY_CUTOFF_WITHOUT_MARKET_PRICE',
                  exit_due_at=cutoff.isoformat(),
                  exit_reference_spot=None,
                  reference_exit_price_verified=False,
                  broker_exit_verified=False,
                  fill_confirmed=False,
                  remaining_pct=0,
                  recovery_cause=str(cause)[:240])
    state.setdefault('history', []).append(closed)
    state['history'] = state['history'][-200:]
    state['position'] = None
    state['last_exit'] = {'at': cutoff.isoformat(), 'direction': p['direction'],
                          'three': (state.get('thesis') or {}).get('last_3m')}
    details = {'position': closed, 'position_id': p['id'], 'cause': str(cause)[:240],
               'reason': 'REFERENCE_ONLY_EXPIRED_NO_BROKER_EXIT_INFERRED',
               'policy_exit_due_at': cutoff.isoformat(),
               'detected_at': seen.isoformat(),
               'manual_broker_position_must_be_checked': True,
               'not_an_executed_order': True}
    queue(state, 'REFERENCE_POSITION_EXPIRED_UNVERIFIED', details, seen)
    item = {'position_id': p['id'], 'cutoff_at': cutoff.isoformat(),
            'detected_at': seen.isoformat(), 'cause': str(cause)[:240],
            'reference_only': True, 'exit_price_verified': False,
            'broker_exit_verified': False}
    state.setdefault('reference_recovery_log', []).append(item)
    state['reference_recovery_log'] = state['reference_recovery_log'][-100:]
    return item


def record_candle_delay(state: dict, day: str, at: datetime) -> int:
    health = state.get('feed_health') or {}
    misses = int(health.get('consecutive_candle_delays', 0)) if health.get('session_date') == day else 0
    misses = min(misses + 1, 1000)
    state['feed_health'] = {'session_date': day,
                            'consecutive_candle_delays': misses,
                            'last_delay_at': at.isoformat()}
    if misses == 3:
        queue(state, 'DATA_FEED_DEGRADED',
              {'session_date': day, 'reason': 'LATEST_COMPLETED_CANDLE_MISSING',
               'consecutive_scans': 3,
               'action': 'REVIEW_UPSTOX_DATA_PUBLICATION_NO_TRADE_EXECUTED'}, at)
    return misses


def reset_candle_delay(state: dict, day: str) -> None:
    state['feed_health'] = {'session_date': day, 'consecutive_candle_delays': 0}



def publish_price_action_state(state: dict, result: dict, bars: list[Candle],
                               structure: dict, config: Config, spot: float,
                               prior_day=None) -> tuple[dict, dict, list[dict]]:
    """Same causal market structure evidence for flat and position-open scans.

    Keeps the exact analytical level history, current trading regime and
    bounded session audit in sync without backdating receipts or relying on OI.
    """
    price_ledger=build_price_action_ledger(bars,config,prior_day)
    phase=classify_market_phase(bars,structure,price_ledger,config)
    active=[z for z in price_ledger['levels'] if
            z['resistance_status']!='UNCONFIRMED' or z['support_status']!='UNCONFIRMED']
    active.sort(key=lambda z:(abs(float(z['price'])-spot),
                    -int(z['resistance_rejections'])-int(z['support_defenses'])))
    state['price_action_ledger']={'as_of':price_ledger['as_of'],
        'levels':active[:70]}
    state['market_phase']={'as_of':price_ledger['as_of'],**phase}
    result['market_phase']=phase
    result['price_action_summary']={'as_of':price_ledger['as_of'],
        'confirmed_resistances':[{k:z[k] for k in ('price','zone_half_width','resistance_rejections','last_resistance_at')}
             for z in price_ledger['resistances'] if z['resistance_status']=='CONFIRMED'][:12],
        'confirmed_supports':[{k:z[k] for k in ('price','zone_half_width','support_defenses','last_support_at')}
             for z in price_ledger['supports'] if z['support_status']=='CONFIRMED'][:12]}
    return price_ledger,phase,active


def add_phase_to_forecast(result: dict, market_phase: dict) -> None:
    """Do not market a broad directional thesis as an immediately tradable move."""
    forecast=result.get('forecast')
    if not isinstance(forecast,dict):return
    forecast['trading_regime']=market_phase.get('phase')
    forecast['independent_price_action_levels']=result.get('price_action_summary')
    if market_phase.get('phase') not in ('BULLISH_TREND','BEARISH_TREND'):
        forecast.setdefault('cautions',[]).append(
            'PROTECTED_THESIS_NOT_TRADE_SIGNAL_WHILE_PHASE_'+str(market_phase.get('phase')))
        forecast['entry_readiness']='INDEPENDENT_VALIDATED_REACTION_REQUIRED'

# ============================================================================
# v120.1 OI-FIRST CAUSAL MARKET ENGINE -- embedded in this single production file
# ============================================================================
# The PE/CE options open-interest concentration defines *candidate* price
# barriers. Completed price reactions determine which ones are defended,
# rejected or accepted through. OI does not reveal participant identity.
# No module imports, ad hoc overrides or test code are needed to use this engine.

@dataclass(frozen=True)
class OIZone1201:
    strike: float
    side: str
    oi: float
    strength: float
    low: float
    high: float
    delta_oi: float | None
    touches: int
    rejection: bool
    defense: bool
    accepted_below: bool
    accepted_above: bool
    instrument_key: str

    def as_dict(self) -> dict:
        return {
            'strike': self.strike, 'side': self.side, 'oi': self.oi,
            'relative_oi': round(self.strength, 6), 'low': self.low,
            'high': self.high, 'zone_half_width': (self.high - self.low) / 2,
            'oi_change': self.delta_oi, 'touches': self.touches,
            'rejection': self.rejection, 'defense': self.defense,
            'accepted_below': self.accepted_below,
            'accepted_above': self.accepted_above,
            'instrument_key': self.instrument_key,
            'interpretation': 'CALL_OI_RESISTANCE' if self.side == 'CE'
                              else 'PUT_OI_SUPPORT',
        }


def v1201_three_direction(bars: list[Candle], direction: str, a: float) -> bool:
    threes = aggregate(bars, 3)
    if not threes:
        return False
    latest = threes[-1]
    if latest.start + timedelta(minutes=3) < bars[-1].start:
        return False  # stale completed 3m context
    sign = 1 if direction == 'BULLISH' else -1
    return (sign * (latest.close - latest.open) >= 0.12 * a
            or (len(threes) >= 2 and
                sign * (latest.close - threes[-2].close) >= 0.30 * a))


def v1201_price_alignment(bars: list[Candle], direction: str, a: float) -> bool:
    if len(bars) < 6:
        return False
    sign = 1 if direction == 'BULLISH' else -1
    recent = bars[-3:]
    aligned = sum(1 for c in recent if sign * (c.close - c.open) > 0.05 * a)
    return bool(aligned >= 2 and
                sign * (recent[-1].close - recent[0].open) >= 0.28 * a and
                v1201_three_direction(bars, direction, a))


def v1201_accepted(bars: list[Candle], edge: float, direction: str,
                   a: float) -> bool:
    # At least two fully closed 1m bars and a fully closed 3m on the new side.
    if len(bars) < 6 or not v1201_three_direction(bars, direction, a):
        return False
    sign = 1 if direction == 'BULLISH' else -1
    margin = max(0.5, 0.08 * a)
    if not all(sign * (c.close - edge) > margin for c in bars[-2:]):
        return False
    threes = aggregate(bars, 3)
    return bool(threes and sign * (threes[-1].close - edge) > margin)


def v1201_zone_book(chain: list[dict], bars: list[Candle], spot: float,
                    oi_context_live: dict, config: Config) -> list[OIZone1201]:
    """Current-chain OI support/resistance; no future or earlier OI backdating."""
    if len(bars) < 6 or not isfinite(spot) or spot <= 0:
        return []
    half = config.oi_zone_half_width
    a = max(1., atr(bars))
    near = []
    for r in chain:
        try:
            if (r.get('side') in ('CE', 'PE') and
                abs(float(r['strike']) - spot) <= config.oi_nearby_points and
                float(r['oi']) > 0 and r.get('expiry') and r.get('instrument_key')):
                near.append(r)
        except (TypeError, ValueError, KeyError, OverflowError):
            continue
    peak = {side: max((float(r['oi']) for r in near if r['side'] == side),
                      default=0.0) for side in ('CE', 'PE')}
    changes = {(r['side'], float(r['strike'])): r.get('oi_change')
               for r in (oi_context_live or {}).get('walls', [])
               if r.get('side') in ('CE', 'PE') and r.get('strike') is not None}
    zones = []
    for r in near:
        side = r['side']
        strike = float(r['strike'])
        strength = float(r['oi']) / peak[side] if peak[side] else 0.
        # Preserve nearby secondary CE/PE OI walls even if not the side peak.
        threshold = min(0.50, config.min_wall_fraction) if abs(strike - spot) <= half else config.min_wall_fraction
        if strength < threshold:
            continue
        low, high = strike - half, strike + half
        accepted_below = v1201_accepted(bars, low, 'BEARISH', a)
        accepted_above = v1201_accepted(bars, high, 'BULLISH', a)
        recent = bars[-18:]
        touches = sum(c.low <= high and c.high >= low for c in recent)
        visited_ce = any(c.high >= low and c.low <= high + 2 * a for c in recent)
        visited_pe = any(c.low <= high and c.high >= low - 2 * a for c in recent)
        rejection = bool(side == 'CE' and visited_ce and not accepted_above
                         and v1201_price_alignment(bars, 'BEARISH', a)
                         and max(c.high for c in recent[-9:]) - bars[-1].close >= .60 * a)
        defense = bool(side == 'PE' and visited_pe and not accepted_below
                       and v1201_price_alignment(bars, 'BULLISH', a)
                       and bars[-1].close - min(c.low for c in recent[-9:]) >= .60 * a)
        zones.append(OIZone1201(
            strike=strike, side=side, oi=float(r['oi']), strength=strength,
            low=low, high=high, delta_oi=changes.get((side, strike)),
            touches=touches, rejection=rejection, defense=defense,
            accepted_below=accepted_below, accepted_above=accepted_above,
            instrument_key=r['instrument_key']))
    return sorted(zones, key=lambda z: (z.strike, z.side))


def v1201_support_upper_lip_probe(zone: OIZone1201, spot: float,
                                  zones: list[OIZone1201],
                                  protected_thesis: str) -> bool:
    """One precise tactical exception; never a wholesale bypass of PE support.

    At 10:57 actual spot 25209, the 25200 PE support's upper lip was
    unconfirmed; an independently observed *same-strike* 25200 CE rejection
    provided the counter-pressure. At 12:18 spot 25086 inside 25100 PE
    support, or in a defended bearish structure, this exception is forbidden.
    """
    return bool(protected_thesis == 'BULLISH' and zone.side == 'PE'
                and not zone.defense and not zone.accepted_below
                and zone.strike + 5.0 <= spot <= zone.high
                and any(z.side == 'CE' and z.rejection and
                        abs(z.strike - zone.strike) <= 0.01 for z in zones))


def v1201_obstruction(direction: str, spot: float,
                     zones: list[OIZone1201], protected: str):
    """Distance to near edge of the closest unaccepted OI obstruction."""
    opposing = 'CE' if direction == 'BULLISH' else 'PE'
    seen = []
    for z in zones:
        if z.side != opposing:
            continue
        if direction == 'BULLISH':
            if z.accepted_above and spot > z.high:
                continue
            if spot <= z.high:
                seen.append((max(0., z.low - spot), z))
        else:
            if v1201_support_upper_lip_probe(z, spot, zones, protected):
                continue
            if z.accepted_below and spot < z.low:
                continue
            if spot >= z.low:
                seen.append((max(0., spot - z.high), z))
    if not seen:
        return None, float('inf')
    distance, z = min(seen, key=lambda pair: (pair[0], -pair[1].strength))
    return z, distance


def v1201_gate(direction: str, spot: float, bars: list[Candle],
              zones: list[OIZone1201], stop: float,
              protected: str, config: Config) -> tuple[bool, str, dict]:
    """Hard pre-trade OI opposition, quote and unreset-impulse checks."""
    if direction not in ('BULLISH', 'BEARISH') or len(bars) < config.min_bars:
        return False, 'OI_ZONE_INPUTS_INSUFFICIENT', {}
    sign = 1 if direction == 'BULLISH' else -1
    risk = sign * (spot - stop)
    a = max(1., atr(bars))
    details = {'atr': round(a, 5), 'risk': round(risk, 5),
               'last_1m_close': bars[-1].close, 'spot': spot,
               'protected_thesis': protected, 'zone_width': config.oi_zone_half_width}
    if risk <= 1 or risk > config.max_risk:
        return False, 'OI_ZONE_INVALID_STOP_RISK', details
    adverse = -sign * (spot - bars[-1].close)
    adverse_limit = max(config.quote_adverse_min_points,
                        config.quote_adverse_atr * a,
                        config.quote_adverse_risk_fraction * risk)
    if adverse > adverse_limit:
        return False, 'OI_ZONE_QUOTE_REVERSED_FROM_TRIGGER', details
    early_rejection = bool(direction == 'BEARISH' and
                           any(z.side == 'CE' and z.rejection for z in zones))
    chase_limit = max(config.quote_chase_atr * a,
                      1.25 * a if early_rejection else 0.)
    if sign * (spot - bars[-1].close) > chase_limit:
        return False, 'OI_ZONE_LIVE_QUOTE_CHASING', details
    for z in zones:
        if direction == 'BEARISH' and z.side == 'PE':
            if z.low <= spot <= z.high and not z.accepted_below:
                if v1201_support_upper_lip_probe(z, spot, zones, protected):
                    details.setdefault('early_tactical_probe', []).append(z.as_dict())
                    continue
                return False, 'INSIDE_UNACCEPTED_PUT_OI_SUPPORT_ZONE', {
                    **details, 'blocking': z.as_dict()}
            if z.low - .5 * a < spot < z.low and not z.accepted_below:
                return False, 'PUT_OI_SUPPORT_BREAK_NOT_CONFIRMED', {
                    **details, 'blocking': z.as_dict()}
        elif direction == 'BULLISH' and z.side == 'CE':
            if z.low <= spot <= z.high and not z.accepted_above:
                return False, 'INSIDE_UNACCEPTED_CALL_OI_RESISTANCE_ZONE', {
                    **details, 'blocking': z.as_dict()}
            if z.high < spot < z.high + .5 * a and not z.accepted_above:
                return False, 'CALL_OI_BREAK_NOT_CONFIRMED', {
                    **details, 'blocking': z.as_dict()}
    opposing, available = v1201_obstruction(direction, spot, zones, protected)
    if opposing:
        details['nearest_opposing_oi'] = opposing.as_dict()
        details['reward_room_to_zone_edge'] = round(available, 5)
        if available < risk * config.min_rr + max(.5, .1 * a):
            return False, 'OI_ZONE_REWARD_ROOM_INSUFFICIENT', details
    # Exhausted impulse from the completed bars is not a fresh entry.
    tail = bars[-9:]
    progress = sign * (tail[-1].close - tail[0].open)
    reset_bars = sum(sign * (b.close - b.open) <= -.12 * a for b in tail[-6:])
    if progress > 4 * a and not reset_bars:
        details['unreset_leg_atr'] = round(progress / a, 5)
        return False, 'UNRESET_EXTENDED_MOMENTUM_ENTRY', details
    # Two opposite 1m bars after the trigger invalidate earlier candidates.
    if (len(bars) >= 3 and sum(sign * (c.close - c.open) <= -.15 * a
                               for c in bars[-3:]) >= 2):
        return False, 'RECENT_COMPLETED_PRICE_REVERSED', details
    return True, 'OI_ZONE_PRICE_AND_RISK_CONFIRMED', details


def v1201_candidate_stop(direction: str, kind: str,
                        prefix: list[Candle], zone: OIZone1201,
                        config: Config) -> float:
    if direction == 'BULLISH':
        technical = min(c.low for c in prefix[-4:]) - config.stop_buffer
        if kind == 'OI_ZONE_RESISTANCE_ACCEPTANCE':
            technical = min(technical, zone.high - config.stop_buffer)
        return technical
    technical = max(c.high for c in prefix[-4:]) + config.stop_buffer
    if kind == 'OI_ZONE_SUPPORT_ACCEPTANCE':
        technical = max(technical, zone.low + config.stop_buffer)
    return technical


def v1201_setup_candidates(chain: list[dict], bars: list[Candle],
                           spot: float, oi_live: dict, structure: dict,
                           config: Config) -> tuple[list[dict], list[OIZone1201], list[dict]]:
    """Four causal scenario types plus 1m recovery between 3m dispatches.

    Never send conditional-entry setups. All published candidates undergo
    *current* quote, current OI and live contract gates. The last 3 prefixes
    are only closed PRICE reconstructions: current OI is not backdated.
    """
    zones = v1201_zone_book(chain, bars, spot, oi_live, config)
    details: list[dict] = []
    candidates: list[dict] = []
    if len(bars) < config.min_bars:
        return [], zones, [{'reason': 'OPENING_1M_WARMUP_INCOMPLETE'}]
    protected = str(structure.get('direction') or 'RANGE')
    complete_at = bars[-1].start + timedelta(minutes=1)
    used = set()
    for direction in ('BEARISH', 'BULLISH'):
        sign = 1 if direction == 'BULLISH' else -1
        for back in range(min(3, len(bars) - config.min_bars + 1)):
            prefix = bars[:-back] if back else bars
            a = max(1., atr(prefix))
            if not v1201_price_alignment(prefix, direction, a):
                if not back:
                    details.append({'direction': direction,
                                    'reason': '1M_AND_CLOSED_3M_MISMATCH'})
                continue
            if back and not v1201_three_direction(bars, direction, max(1., atr(bars))):
                continue
            for z in zones:
                if direction == 'BEARISH':
                    if z.side == 'CE' and z.rejection:
                        kind = 'OI_ZONE_RESISTANCE_REJECTION'
                    elif z.side == 'PE' and z.accepted_below and spot < z.low:
                        kind = 'OI_ZONE_SUPPORT_ACCEPTANCE'
                    elif (z.side == 'CE' and protected == 'BEARISH'
                          and not z.accepted_above and spot < z.low
                          and max(c.high for c in prefix[-5:]) >= z.low - .5 * a
                          and prefix[-1].close < prefix[-2].close):
                        # Continuation only after a *recent* CE resistance
                        # retest; a downtrend by itself does not create a trade.
                        kind = 'OI_ZONE_BEARISH_RETEST_CONTINUATION'
                    else:
                        continue
                else:
                    if z.side == 'PE' and z.defense:
                        kind = 'OI_ZONE_SUPPORT_DEFENSE'
                    elif z.side == 'CE' and z.accepted_above and spot > z.high:
                        kind = 'OI_ZONE_RESISTANCE_ACCEPTANCE'
                    elif (z.side == 'PE' and protected == 'BULLISH'
                          and not z.accepted_below and spot > z.high
                          and min(c.low for c in prefix[-5:]) <= z.high + .5 * a
                          and prefix[-1].close > prefix[-2].close):
                        # Continuation after a defended/retested Put-OI level,
                        # not after an unreset extended bullish impulse.
                        kind = 'OI_ZONE_BULLISH_RETEST_CONTINUATION'
                    else:
                        continue
                if kind in ('OI_ZONE_SUPPORT_DEFENSE', 'OI_ZONE_RESISTANCE_REJECTION'):
                    # Entry must arise from an actual recent test, not hours-old OI.
                    interaction_window = prefix[-4:]
                    if not any(c.low <= z.high and c.high >= z.low for c in interaction_window):
                        continue
                stop = v1201_candidate_stop(direction, kind, prefix, z, config)
                if any(sign * (c.low - stop) <= 0 if sign > 0 else
                       sign * (c.high - stop) <= 0 for c in bars[len(prefix):]):
                    continue
                allowed, reason, diag = v1201_gate(
                    direction, spot, bars, zones, stop, protected, config)
                details.append({'kind': kind, 'direction': direction,
                                'level': z.strike, 'reason': reason,
                                'evaluation': diag,
                                'price_trigger_completed_at':
                                (prefix[-1].start + timedelta(minutes=1)).isoformat(),
                                'oi_assessed_at_current_scan': True})
                if not allowed:
                    continue
                key = (kind, z.side, z.strike, direction)
                if key in used:
                    continue
                used.add(key)
                candidates.append({
                    'kind': kind, 'direction': direction,
                    'trigger': float(prefix[-1].close),
                    'confirmed_at': complete_at.isoformat(),  # causal current scan
                    'source_price_trigger_at':
                    (prefix[-1].start + timedelta(minutes=1)).isoformat(),
                    'invalidation': round(stop, 5),
                    'trade_invalidation': round(stop, 5),
                    'atr_1m': a,
                    'three_confirmed_at':
                    (aggregate(prefix, 3)[-1].start + timedelta(minutes=3)).isoformat(),
                    'stop_role': 'COMPLETED_1M_SWING_PLUS_OI_ZONE',
                    'protected_thesis_boundary': structure.get(
                        'support' if direction == 'BULLISH' else 'resistance'),
                    'thesis_invalidation': {
                        'level': structure.get('support' if direction == 'BULLISH'
                                               else 'resistance'),
                        'requires': 'PROTECTED_BREAK_ON_COMPLETED_3M'},
                    'dependencies': [{
                        'kind': 'LIVE_OI_ZONE_AND_COMPLETED_PRICE',
                        'strike': z.strike, 'side': z.side,
                        'bounds': [z.low, z.high],
                        'instrument_key': z.instrument_key}],
                    'oi_anchor': z.as_dict(),
                    'evidence': ['OI_CONCENTRATION_ZONE', 'CONFIRMED_1M_AND_3M',
                                 'CURRENT_FRESH_OPTION_CHAIN',
                                 'STRUCTURAL_STOP_WITHOUT_RISK_COMPRESSION'],
                })
    ranking = {'OI_ZONE_RESISTANCE_REJECTION': 0, 'OI_ZONE_SUPPORT_DEFENSE': 0,
               'OI_ZONE_SUPPORT_ACCEPTANCE': 1, 'OI_ZONE_RESISTANCE_ACCEPTANCE': 1,
               'OI_ZONE_BEARISH_RETEST_CONTINUATION': 2,
               'OI_ZONE_BULLISH_RETEST_CONTINUATION': 2}
    candidates.sort(key=lambda item: (
        ranking.get(item['kind'], 2),
        -float(item['oi_anchor']['relative_oi']),
        abs(float(item['oi_anchor']['strike']) - spot)))
    return candidates, zones, details


def v1201_risk_inventory(context: dict, zones: list[OIZone1201],
                        spot: float, protected: str) -> dict:
    """Use OI price zones as the primary barriers, and confirmed price levels.

    The early same-strike tactical probe is explicitly excluded from a hard
    *target* barrier until completed price actually defends that Put level.
    """
    result = dict(context)
    barriers = []
    for z in zones:
        if v1201_support_upper_lip_probe(z, spot, zones, protected):
            continue
        barriers.append({
            'price': z.strike, 'kind': 'OI', 'source': 'OI_' + z.side,
            'significance': 1 + z.strength, 'oi': z.oi,
            'zone_half_width': (z.high - z.low) / 2,
            'price_rejection_confirmed': z.rejection if z.side == 'CE' else z.defense,
            'hard_barrier': True, 'accepted_above': z.accepted_above,
            'accepted_below': z.accepted_below,
        })
    # Independent completed-price tests are additional evidence, but nearby
    # untested historical pivots cannot override current OI support/resistance.
    for z in (context.get('price_action_ledger') or {}).get('levels', []):
        for role, status in [('RESISTANCE', 'resistance_status'),
                             ('SUPPORT', 'support_status')]:
            if z.get(status) == 'CONFIRMED':
                barriers.append({
                    'price': float(z['price']),
                    'source': 'PRICE_ACTION_' + role, 'kind': 'PRICE',
                    'significance': 2.8,
                    'zone_half_width': float(z.get('zone_half_width') or 0),
                    'hard_barrier': True,
                    'price_rejection_confirmed': True,
                })
    result['levels'] = barriers
    return result


def v1201_risk_plan(setup: dict, spot: float, context: dict,
                   zones: list[OIZone1201], config: Config,
                   now: datetime, bars: list[Candle], protected: str):
    """Fixed structural stop and T1 before first unaccepted opposing OI zone.

    Stop is never clipped to manufacture risk eligibility. Projection is
    explicitly heuristic; it is not a calibrated target-hit probability.
    """
    d = setup['direction']
    sign = 1 if d == 'BULLISH' else -1
    stop = float(setup['trade_invalidation'])
    a = max(1., atr(bars))
    if sign * (spot - stop) <= 1:
        return None, 'INVALID_TACTICAL_STOP', {}
    risk = max(sign * (spot - stop), config.min_stop_atr * a)
    stop = spot - sign * risk
    if risk > config.max_risk:
        return None, 'TACTICAL_STOP_EXCEEDS_APPROVED_MAX_RISK', {'risk': risk}
    if now >= entry_cutoff_at(now, config):
        return None, 'TOO_CLOSE_TO_1515_CUTOFF', {}
    time_left = (intraday_hard_exit_at(now, config) - now).total_seconds() / 60
    if time_left < config.minimum_entry_to_exit_minutes:
        return None, 'INSUFFICIENT_HOLDING_WINDOW', {'minutes_left': time_left}
    recent = float(context.get('recent_impulse_height') or 0.0)
    projection = max(risk * config.min_rr, config.min_intraday_projection_atr * a,
                     min(max(0., recent), config.max_target_projection_atr * a))
    projection = min(projection, config.max_target_projection_atr * a)
    if projection < risk * config.min_rr:
        return None, 'INTRADAY_TARGET_EXCEEDS_VOLATILITY_CAP', {}
    # Compare to first opposing OI *edge*, not to the strike centre.
    nearest, room = v1201_obstruction(d, spot, zones, protected)
    target_source = 'BOUNDED_COMPLETED_PRICE_PROJECTION'
    if nearest:
        safe_room = max(0.0, room - max(0.5, config.target_clearance_atr * a))
        if safe_room < risk * config.min_rr:
            return None, 'T1_BLOCKED_BY_OPPOSING_OI_ZONE', {'barrier': nearest.as_dict(),
                                                             'safe_room': round(safe_room, 5)}
        if safe_room < projection:
            projection = safe_room
            target_source = 'OBSERVED_OI_SUPPORT_RESISTANCE_EDGE'
    # Additional independently price-confirmed zones have precedence over
    # untested pivot estimates (already stored in the price ledger).
    other = []
    for row in (context.get('price_action_ledger') or {}).get('levels', []):
        role = ('resistance_status' if sign > 0 else 'support_status')
        if row.get(role) != 'CONFIRMED':
            continue
        # An old support from a previous regime is not a fresh hard barrier.
        last_test = row.get('last_resistance_at' if sign > 0 else 'last_support_at')
        if not last_test:
            continue
        try:
            if (now - datetime.fromisoformat(last_test)).total_seconds() > 15 * 60:
                continue
        except ValueError:
            continue
        px = float(row['price'])
        width = float(row.get('zone_half_width') or 0.)
        room_to_edge = sign * (px - spot) - width - max(.5, config.target_clearance_atr * a)
        if room_to_edge > 0:
            other.append((room_to_edge, px))
    if other:
        first_room, first_level = min(other)
        if first_room < risk * config.min_rr:
            return None, 'T1_BLOCKED_BY_CONFIRMED_PRICE_REACTION', {
                'price_barrier': first_level, 'clearance': first_room}
        if first_room < projection:
            projection = first_room
            target_source = 'CONFIRMED_PRICE_ACTION_BARRIER_EDGE'
    if projection / risk < config.min_rr - 1e-8:
        return None, 'UNDERLYING_RR_INSUFFICIENT', {}
    # Conservative time budget, not a probabilistic return model.
    usable = max(0., time_left - config.last_minute_dispatch_buffer)
    time_budget = (config.last_minute_budget_atr_sqrt * a * usable ** 0.5)
    if projection > time_budget:
        return None, 'TARGET_EXCEEDS_REMAINING_SESSION_TIME_BUDGET', {
            'distance': projection, 'time_budget': time_budget}
    target1 = round(spot + sign * projection, 5)
    target2 = round(target1 + sign * max(config.strike_step, a, risk), 5)
    # T2 cannot pass unaccepted OI opposition just because T1 was reached.
    # The runner's future extension is only an objective, never an assumed fill.
    if nearest:
        target_edge = nearest.low if sign > 0 else nearest.high
        target_buffer = max(0.5, config.target_clearance_atr * a)
        conservative_t2 = round(target_edge - sign * target_buffer, 5)
        if sign * (conservative_t2 - target1) > 0.25:
            if sign * (target2 - conservative_t2) > 0:
                target2 = conservative_t2
    plan = {
        'entry_underlying': spot, 'stop_underlying': round(stop, 5),
        'risk_points': round(risk, 5), 't1_underlying': target1,
        't2_underlying': target2,
        'underlying_rr': round(projection / risk, 5),
        'structural_invalidation_requested': setup['trade_invalidation'],
        'target_quality': 'PRICE_OBSERVED_LEVEL' if target_source != 'BOUNDED_COMPLETED_PRICE_PROJECTION' else 'CAUSAL_PROJECTION',
        'target_source': target_source,
        'fixed_targets': True, 'nearest_opposing_oi': nearest.as_dict() if nearest else None,
        'thesis_invalidation': setup.get('thesis_invalidation'),
        'projected_target_not_historical_resistance': target_source == 'BOUNDED_COMPLETED_PRICE_PROJECTION',
        'entry_quality': {'minutes_until_exit': round(time_left, 3),
                          'time_budget_points': round(time_budget, 3),
                          'oi_zone_primary': True,
                          'evaluated_at': now.isoformat()},
    }
    return plan, 'OI_FIRST_RISK_PLAN_VALID', {'risk': risk, 'projection': projection}


def scan(state: dict[str, Any], api: Upstox, config: Config, audit_dir: Path, time_source=None) -> dict:
    samples = []

    def tick():
        t = (time_source or clock)()
        samples.append(t.isoformat())
        return t
    started = tick()
    day = started.date().isoformat()
    required_candle_start = scan_candle_watermark(started)
    publication_deadline = candle_publication_deadline(required_candle_start, config.candle_publication_grace_seconds)
    result = {'timestamp': started.isoformat(), 'version': __version__, 'session_date': day, 'decision': 'NO_TRADE', 'reason': 'UNSET',
              'scan_candle_watermark': required_candle_start.isoformat(),
              'candle_publication_grace_deadline': publication_deadline.isoformat()}
    evidence = {'version': __version__, 'started_at': started.isoformat(), 'state_before': copy.deepcopy(state),
                'scan_candle_watermark': required_candle_start.isoformat(),
                'candle_publication_grace_deadline': publication_deadline.isoformat()}
    evidence.update(clock_samples=samples, api_events=[], config=asdict(config))
    evidence['release_sha256'] = release_fingerprint()
    api = RecordingAPI(api, evidence['api_events'])

    def remember_structure(value, at):
        state['thesis'] = value
        history = state.setdefault('thesis_history', [])
        fields = ('direction', 'state', 'support', 'resistance', 'pending_break', 'last_reversal')
        if not history or any((history[-1].get(k) != value.get(k) for k in fields)):
            history.append(dict(value, at=at.isoformat()))
            state['thesis_history'] = history[-200:]
    try:
        # Strategy-only migration: NO destructive state migration. The existing
        # schema-7 position, history, OI baselines and email outbox remain.
        if state.get('oi_strategy_revision') != 1201:
            state['setup_watches'] = []
            state['opportunity_journal'] = []
            state['oi_strategy_revision'] = 1201
            state['oi_strategy_activated_at'] = started.isoformat()
            # Protected thesis is recomputed from today's completed candles.
            state['thesis'] = None
        cutoff_today = intraday_hard_exit_at(started, config)
        result['intraday_hard_exit_at'] = cutoff_today.isoformat()
        result['entry_cutoff_at'] = entry_cutoff_at(started,config).isoformat()
        if state.get('session_date') and state['session_date'] != day and state.get('position'):
            recovered = expire_unexecuted_reference(state, started, config, 'PRIOR_SESSION_MISSED_END_OF_DAY_PROCESSING')
            if recovered is None:
                result.update(decision='POSITION_MONITORING_UNAVAILABLE',
                              reason='PRIOR_SESSION_POSITION_REQUIRES_RECONCILIATION',
                              position_id=state['position'].get('id'))
                return result
            result['prior_session_reference_recovery'] = recovered
        if state.get('session_date') != day:
            state.update(session_date=day, thesis=None, oi_snapshot=None, oi_history=[], session_oi_baseline=None, previous_session=None, futures_snapshot=None, last_exit=None, last_processed_candle=None, setup_watches=[], opportunity_journal=[], price_action_ledger={}, market_phase={}, feed_health={'session_date':day,'consecutive_candle_delays':0})
        if started >= cutoff_today and not state.get('position'):
            result['reason'] = 'AFTER_1515_NO_NEW_ENTRIES'
            return result
        session = api.session(started)
        if session is None:
            if state.get('position'):
                recovered = expire_unexecuted_reference(state, tick(), config, 'SESSION_UNAVAILABLE_AT_OR_AFTER_CUTOFF')
                if recovered:
                    result.update(decision='REFERENCE_POSITION_EXPIRED',
                                  reason='UNOBSERVED_1515_REFERENCE_CUTOFF',
                                  reference_recovery=recovered)
                else:
                    result.update(decision='POSITION_MONITORING_UNAVAILABLE', reason='MARKET_CLOSED_POSITION_LOCK_RETAINED')
                    queue(state, 'MONITORING_UNAVAILABLE', {'position_id': state['position'].get('id'), 'session_date': day, 'cause': 'MARKET_CLOSED'}, tick())
            else:
                result['reason'] = 'MARKET_CLOSED_OR_TIMINGS_UNAVAILABLE'
            return result
        session_start, session_end = session
        evidence['session'] = [session_start.isoformat(), session_end.isoformat()]
        result['intraday_hard_exit_at'] = intraday_hard_exit_at(started,config).isoformat()
        result['entry_cutoff_at'] = entry_cutoff_at(started,config).isoformat()
        if not state.get('position') and started < session_start + timedelta(minutes=config.min_bars):
            result['reason'] = 'OPENING_CANDLE_WARMUP'
            return result
        raw = api.candles()
        open_position = state.get('position')
        keys = [INDEX] + ([open_position['instrument_key']] if open_position else [])
        previous_future = state.get('futures_snapshot') or {}
        if open_position and previous_future.get('instrument_key'):
            keys.append(previous_future['instrument_key'])
        quotes = api.quotes(keys)
        bars, discarded, now, retries = fresh_candles(api, config, raw, clock_fn=tick, required_start=required_candle_start, publication_deadline=publication_deadline)
        result['candle_refresh_retries'] = retries
        result['candle_refresh_attempts'] = retries + 1
        reset_candle_delay(state, day)
        result['latest_candle_received'] = bars[-1].start.isoformat()
        evidence.update(candles=[[c.start.isoformat(), c.open, c.high, c.low, c.close, c.volume] for c in bars], quotes=quotes, evaluated_at=now.isoformat())
        spot = checked_spot(quotes.get(INDEX, {}), now, config.max_quote_age)
        complete_history = bars[0].start == session_start.replace(second=0, microsecond=0)
        if not complete_history:
            result['structure_data_quality'] = 'SESSION_OPENING_HISTORY_MISSING'
            if not open_position:
                result['reason'] = 'SESSION_STRUCTURE_HISTORY_INCOMPLETE'
                return result
        result.update(spot=spot, spot_quote_timestamp=quotes[INDEX]['timestamp'], last_complete_1m=bars[-1].start.isoformat(), discarded_pre_gap_candles=discarded)
        last_processed = state.get('last_processed_candle')
        if discarded and (not last_processed or datetime.fromisoformat(last_processed) < bars[0].start):
            state['thesis'] = None
            result['structure_reset_reason'] = 'UNSEEN_CANDLE_GAP'
        thesis = update_structure(bars, state.get('thesis'))
        thesis['boundary_trusted'] = complete_history
        remember_structure(thesis, now)
        state['last_processed_candle'] = bars[-1].start.isoformat()
        result['structure'] = thesis
        result['forecast'] = forecast_market(bars, thesis, spot, {}, config=config)
        if open_position:
            active_oi = {}
            active_chain = []
            try:
                active_exp, active_contracts = api.contracts(now.date())
                if active_exp != open_position['expiry']:
                    raise ProviderError('ACTIVE_EXPIRY_OI_UNAVAILABLE')
                active_chain = api.chain(active_exp, active_contracts)
                oi_at = tick()
                comparison = oi_comparison(state.get('oi_snapshot'), active_chain, active_exp, oi_at, spot, state.get('oi_history'), state.get('session_oi_baseline'), config.oi_horizon_max_seconds, config.premium_proxy_max_spread_pct)
                active_oi = enrich_oi_context(oi_context(active_chain, spot, config), comparison, bars, spot, config=config)
                advance_oi_history(state,active_chain,active_exp,oi_at,spot,config.opening_oi_baseline_cutoff_minutes)
                evidence.update(chain=active_chain, chain_received_at=oi_at.isoformat(), contracts=active_contracts)
                result.update(oi_levels=active_oi, oi_flow_context=comparison)
            except (ProviderError, DataError, ValueError, TypeError, KeyError):
                result['oi_monitoring'] = 'UNAVAILABLE_SPOT_PROTECTION_CONTINUES'
            quotes = api.quotes(keys)
            bars, _, now, management_retries = fresh_candles(api, config, clock_fn=tick, required_start=required_candle_start, publication_deadline=publication_deadline)
            result['position_monitoring_candle_refresh_retries'] = management_retries
            result['position_monitoring_candle_refresh_attempts'] = management_retries + 1
            spot = checked_spot(quotes.get(INDEX, {}), now, config.max_quote_age)
            thesis = update_structure(bars, thesis)
            thesis['boundary_trusted'] = bars[0].start == session_start.replace(second=0, microsecond=0)
            remember_structure(thesis, now)
            prior_day_for_levels=state.get('previous_session')
            if not isinstance(prior_day_for_levels,dict) or prior_day_for_levels.get('validated_for_session')!=day:
                prior_day_for_levels=None
            position_ledger,position_phase,_=publish_price_action_state(
                state,result,bars,thesis,config,spot,prior_day_for_levels)
            if active_chain:
                active_oi = enrich_oi_context(oi_context(active_chain, spot, config), comparison, bars, spot, fresh=(now - oi_at).total_seconds() <= config.max_quote_age, config=config,price_ledger=position_ledger)
                result['oi_levels'] = active_oi
            state['last_processed_candle'] = bars[-1].start.isoformat()
            evidence.update(candles=[[c.start.isoformat(), c.open, c.high, c.low, c.close, c.volume] for c in bars], quotes=quotes, evaluated_at=now.isoformat())
            result.update(spot=spot, structure=thesis, last_complete_1m=bars[-1].start.isoformat())
            result['forecast'] = forecast_market(bars, thesis, spot, active_oi, config=config)
            add_phase_to_forecast(result,position_phase)
            future_quote = quotes.get(previous_future.get('instrument_key'))
            if future_quote:
                try:
                    future_price = checked_spot(future_quote, now, config.max_quote_age)
                    result['futures'] = {'instrument_key': previous_future['instrument_key'], 'price': future_price, 'provider_average_price': future_quote.get('average_price'), 'quote_timestamp': future_quote['timestamp'], 'role': 'CONTEXT_ONLY'}
                except DataError:
                    result['futures'] = {'status': 'STALE', 'role': 'CONTEXT_ONLY'}
            option_quote = quotes.get(open_position['instrument_key'])
            valid_option_quote = False
            try:
                qt = parse_feed_timestamp(option_quote['timestamp'])
                age = (now - qt).total_seconds()
                valid_option_quote = qt.tzinfo is not None and -2 <= age <= config.max_quote_age and (float(option_quote['bid']) > 0)
            except (TypeError, KeyError, ValueError):
                pass
            if not valid_option_quote:
                result['premium_monitoring'] = 'OPTION_QUOTE_UNAVAILABLE_OR_STALE'
                queue(state, 'MONITORING_DEGRADED', {'position_id': open_position['id'], 'session_date': day, 'cause': 'OPTION_QUOTE_UNAVAILABLE_OR_STALE'}, now)
            managed, events, closed = manage(open_position, bars, spot, option_quote, now, session_end, config, thesis, active_oi)
            state['position'] = managed
            for event in events:
                event.update(contract={k: open_position.get(k) for k in ('side', 'strike', 'expiry', 'direction')}, structure=thesis, oi_levels=active_oi)
                context_position = managed or closed or open_position
                event['position_context'] = {k: context_position.get(k) for k in ('side', 'strike', 'expiry', 'direction', 'entry_spot', 'entry_ask', 'stop', 't1', 't2', 'remaining_pct', 'management_state')}
                if event.get('remaining_pct') is not None:
                    event['position_context']['remaining_pct'] = event['remaining_pct']
                if event.get('new_stop') is not None:
                    event['position_context']['stop'] = event['new_stop']
                queue(state, event['kind'], event, now)
            reversal_exit = None
            if closed:
                state['history'].append(closed)
                state['history'] = state['history'][-200:]
                state['last_exit'] = {'at': closed['closed_at'], 'direction': closed['direction'], 'three': thesis.get('last_3m')}
                result.update(decision='POSITION_CLOSED', reason=closed['exit_reason'], position=closed)
                result['position_exit'] = closed
                if closed['exit_reason'] == 'OPPOSITE_STRUCTURE_CONFIRMED':
                    reversal_exit = closed
            else:
                result.update(decision='POSITION_OPEN', reason='POSITION_LOCKED', position=managed)
            if reversal_exit is None:
                return result
        try:
            future = api.nearest_nifty_future(now, Path('.cache/nifty_futures_v119_2.json'))
            fq = api.quotes([future['instrument_key']]).get(future['instrument_key'], {})
            ft = tick()
            fp = checked_spot(fq, ft, config.max_quote_age)
            current = {**future, 'price': fp, 'oi': fq.get('oi'), 'at': ft.isoformat()}
            prior = state.get('futures_snapshot')
            pattern = 'UNAVAILABLE'
            if prior and prior.get('instrument_key') == current['instrument_key']:
                try:
                    gap = (ft - datetime.fromisoformat(prior['at'])).total_seconds()
                    if 30 <= gap <= 900:
                        pattern = classify_flow(float(prior['oi']), float(current['oi']), float(prior['price']), fp, 'CE')
                except (ValueError, TypeError, KeyError):
                    pass
            state['futures_snapshot'] = current
            result['futures'] = {**future, 'price': fp, 'average_price': fq.get('average_price'), 'price_oi_pattern': pattern, 'role': 'CONTEXT_ONLY'}
            try:
                future_now = tick()
                future_bars = normalize_candles(api.candles(future['instrument_key']), future_now, required_candle_start)
                validate_candles(future_bars, future_now, 1, required_start=required_candle_start)
                volume = sum((c.volume for c in future_bars))
                if volume > 0:
                    result['futures']['candle_vwap_estimate'] = sum(((c.high + c.low + c.close) / 3 * c.volume for c in future_bars)) / volume
                    result['futures']['vwap_method'] = 'COMPLETED_CANDLE_TYPICAL_PRICE_ESTIMATE'
                else:
                    result['futures']['vwap_status'] = 'NO_POSITIVE_VOLUME'
            except (ProviderError, DataError, TypeError):
                result['futures']['vwap_status'] = 'UNAVAILABLE'
            if prior and prior.get('instrument_key') == current['instrument_key'] and (30 <= (ft - datetime.fromisoformat(prior['at'])).total_seconds() <= 900):
                delta = fp - float(prior['price'])
                old_oi = prior.get('oi')
                new_oi = current.get('oi')
                if old_oi and new_oi and (abs(delta) >= max(1.0, 0.1 * float(thesis.get('atr_1m') or 1))) and (abs(float(new_oi) - float(old_oi)) / float(old_oi) >= 0.0005):
                    result['futures']['price_oi_pattern'] = {(True, True): 'LONG_BUILDUP_HYPOTHESIS', (True, False): 'SHORT_COVERING_HYPOTHESIS', (False, True): 'SHORT_BUILDUP_HYPOTHESIS', (False, False): 'LONG_UNWINDING_HYPOTHESIS'}[delta > 0, float(new_oi) > float(old_oi)]
        except (ProviderError, ValueError, TypeError, KeyError):
            result['futures'] = {'status': 'UNAVAILABLE', 'role': 'CONTEXT_ONLY'}
        except DataError:
            result['futures'] = {'status': 'STALE', 'role': 'CONTEXT_ONLY'}
        # Yesterday's completed daily OHLC is immutable for this session; use
        # a verified session-scoped cache to avoid repeat API calls and delays.
        prior_cached=state.get('previous_session') or {}
        previous_day=None
        if prior_cached.get('validated_for_session')==day and prior_cached.get('date') and prior_cached['date']<day:
            previous_day=prior_cached
        else:
            try:
                previous_day=api.previous_session(now.date())
                if previous_day.get('date') and previous_day['date']<day:
                    previous_day=dict(previous_day,validated_for_session=day)
                    state['previous_session']=previous_day
                else:
                    previous_day=None
            except (ProviderError, DataError, ValueError, TypeError, AttributeError):
                result['previous_session_levels']={'status':'UNAVAILABLE','reason':'NONFATAL_ENRICHMENT'}
        if previous_day:
            result['previous_session_levels']=previous_day
        expiry, contracts = api.contracts(tick().date())
        chain = api.chain(expiry, contracts)
        chain_at = tick()
        result['chain_received_at'] = chain_at.isoformat()
        result['chain_timestamp_quality'] = 'FETCH_TIME_ONLY'
        context = oi_context(chain, spot, config)
        result['oi_levels'] = context
        result['oi_flow_context'] = oi_comparison(state.get('oi_snapshot'), chain, expiry, chain_at, spot, state.get('oi_history'), state.get('session_oi_baseline'), config.oi_horizon_max_seconds, config.premium_proxy_max_spread_pct)
        advance_oi_history(state,chain,expiry,chain_at,spot,config.opening_oi_baseline_cutoff_minutes)
        evidence.update(chain=chain, chain_received_at=chain_at.isoformat(), contracts=contracts, futures=result.get('futures'))
        strikes = sorted({r['strike'] for r in chain})
        if len(strikes) < 3:
            raise DataError('INSUFFICIENT_STRIKE_GRID')
        actual_steps = sorted(set((round(b - a, 6) for a, b in zip(strikes, strikes[1:]) if b > a)))
        if not actual_steps or abs(actual_steps[0] - config.strike_step) > 1e-06:
            raise DataError('STRIKE_GRID_CHANGED')
        atm = min(strikes, key=lambda x: (abs(x - spot), x))
        targets = {atm + i * config.strike_step for i in range(-3, 4)}
        keys = [INDEX] + [r['instrument_key'] for r in chain if r['strike'] in targets]
        full = api.quotes(keys)
        now = tick()
        try:
            validate_candles(bars, now, config.min_bars, required_start=required_candle_start)
        except DataError as exc:
            if str(exc) != 'LATEST_COMPLETED_CANDLE_MISSING':
                raise
            bars, discarded, now, retries = fresh_candles(api, config, clock_fn=tick, required_start=required_candle_start, publication_deadline=publication_deadline)
            if discarded and datetime.fromisoformat(state['last_processed_candle']) < bars[0].start:
                thesis = None
            thesis = update_structure(bars, thesis)
            thesis['boundary_trusted'] = bars[0].start == session_start.replace(second=0, microsecond=0)
            remember_structure(thesis, now)
            state['last_processed_candle'] = bars[-1].start.isoformat()
            result.update(structure=thesis, last_complete_1m=bars[-1].start.isoformat(), latest_candle_received=bars[-1].start.isoformat(), post_chain_candle_refresh=True, post_chain_candle_refresh_retries=retries)
        if (now - chain_at).total_seconds() > config.max_quote_age:
            raise DataError('CHAIN_TOO_OLD')
        if bars[0].start != session_start.replace(second=0, microsecond=0):
            result['reason'] = 'SESSION_STRUCTURE_HISTORY_INCOMPLETE'
            return result
        if (now - started).total_seconds() > 120:
            raise DataError('SCAN_BUDGET_EXCEEDED')
        spot = checked_spot(full.get(INDEX, {}), now, config.max_quote_age)
        price_ledger,market_phase,active_levels=publish_price_action_state(
            state,result,bars,thesis,config,spot,previous_day)
        context = enrich_oi_context(oi_context(chain, spot, config), result['oi_flow_context'], bars, spot, config=config, price_ledger=price_ledger)
        # Entry decisions need active zones, not the complete all-day anchor
        # inventory; the full ledger was already replayed causally above.
        context['price_action_ledger']={
            'as_of':price_ledger['as_of'],
            'levels':active_levels[:70],
            'resistances':price_ledger['resistances'][:35],
            'supports':price_ledger['supports'][:35],
            'replay_bars':price_ledger['replay_bars'],
            'method':price_ledger['method']}
        context['market_phase']=market_phase
        context['spot_live']=spot
        supports = [float(x) for x in (thesis.get('confirmed_pivot_low'), thesis.get('confirmed_15m_pivot_low')) if x is not None and float(x) < spot]
        resistances = [float(x) for x in (thesis.get('confirmed_pivot_high'), thesis.get('confirmed_15m_pivot_high')) if x is not None and float(x) > spot]
        context.update(price_support=thesis.get('confirmed_15m_pivot_low'), price_resistance=thesis.get('confirmed_15m_pivot_high'), minor_support=max(supports) if supports else None, minor_resistance=min(resistances) if resistances else None)
        context.update(build_level_book(bars, thesis, context, spot, previous_day, result.get('futures'),price_ledger))
        result['futures_alignment']=contextual_futures_alignment(result.get('futures'),thesis,spot)
        context['price_oi_interpretation']=price_oi_evidence(context,result['oi_flow_context'],thesis,spot)
        result['price_oi_interpretation']=context['price_oi_interpretation']
        result['level_inventory']=context['levels']
        result.update(spot=spot, spot_quote_timestamp=full[INDEX]['timestamp'], oi_levels=context)
        result['forecast'] = forecast_market(bars, thesis, spot, context, result.get('futures'), config)
        add_phase_to_forecast(result,market_phase)
        evidence.update(candles=[[c.start.isoformat(), c.open, c.high, c.low, c.close, c.volume] for c in bars], quotes=full, evaluated_at=now.isoformat())
        # v120.1: OI concentration defines zones; completed price proves
        # rejection, defense or acceptance. Legacy watch paths do not run.
        state['setup_watches'] = []
        state['last_setup_candle'] = bars[-1].start.isoformat()
        setups, zones, zone_checks = v1201_setup_candidates(
            chain, bars, spot, context, thesis, config)
        result['oi_zone_analysis'] = {
            'method': 'OI_CONCENTRATION_PLUS_CLOSED_1M_3M_PRICE',
            'zones': [z.as_dict() for z in zones],
            'candidate_diagnostics': zone_checks,
            'as_of': now.isoformat(), 'oi_receipt': chain_at.isoformat(),
            'not_backdated': True, 'hard_rejections_require_price_confirmation': True,
        }
        result['entry_price_diagnostics'] = {
            'latest_1m': {'start': bars[-1].start.isoformat(),
                          'open': bars[-1].open, 'high': bars[-1].high,
                          'low': bars[-1].low, 'close': bars[-1].close},
            'closed_3m': thesis.get('last_3m'),
            'protected_thesis': thesis.get('direction'),
            'market_phase': market_phase.get('phase'),
            'fresh_candidates': len(setups), 'legacy_watch_count': 0,
        }
        if now >= entry_cutoff_at(now, config):
            result['reason'] = 'ENTRY_TOO_CLOSE_TO_1515_HARD_EXIT'
            return result
        if not setups:
            result['reason'] = 'NO_QUALIFIED_OI_PRICE_REACTION'
            return result
        evaluated = []
        qualified = []
        last = state.get('last_exit') or {}
        # Current level inventory, not last session's stale price-only trend.
        risk_context = v1201_risk_inventory(
            context, zones, spot, str(thesis.get('direction') or 'RANGE'))
        for setup in setups:
            row = {'setup': setup}
            direction = setup['direction']
            # Old 1m candidate only survives if live completed 3m still aligns.
            if not v1201_three_direction(bars, direction, max(1., atr(bars))):
                row['reason'] = 'CURRENT_CLOSED_3M_REVERSED'
                evaluated.append(row)
                continue
            # A previously stopped-out reference cannot be reopened merely
            # because the same 3m episode still appears in the option chain.
            if last.get('at'):
                ex = datetime.fromisoformat(last['at'])
                if (datetime.fromisoformat(setup['confirmed_at']) <= ex or
                    (last.get('direction') == direction and
                     (now - ex).total_seconds() < 180)):
                    row['reason'] = 'WAIT_FOR_NEW_POST_EXIT_STRUCTURE'
                    evaluated.append(row)
                    continue
            plan, reason, plan_diag = v1201_risk_plan(
                setup, spot, risk_context, zones, config, now, bars,
                str(thesis.get('direction') or 'RANGE'))
            row['risk_diagnostics'] = plan_diag
            if plan is None:
                row['reason'] = reason
                evaluated.append(row)
                continue
            scenario = ('REVERSAL' if setup['kind'] in (
                'OI_ZONE_RESISTANCE_REJECTION', 'OI_ZONE_SUPPORT_DEFENSE')
                else 'TREND_ACCEPTANCE')
            contract, rejected = select_contract(
                chain, full, direction, scenario, spot, now, expiry,
                config, plan=plan)
            row['rejected_contracts'] = rejected
            if not contract:
                row['reason'] = 'NO_CURRENT_LIQUID_OPTION_QUOTE'
                evaluated.append(row)
                continue
            contract['plan_sensitivity'] = contract_sensitivity(contract, plan)
            key = '|'.join([day, expiry, direction, contract['instrument_key'],
                            setup['kind'], setup['confirmed_at'],
                            str(setup['oi_anchor']['strike'])])
            ident = hashlib.sha256(key.encode()).hexdigest()[:24]
            # Suppress historical duplicate and same-observation duplicate.
            if (any(p.get('id') == ident for p in state['history']) or
                any((e.get('kind') == 'ENTRY' and
                     (e.get('details') or {}).get('position', {}).get('id') == ident)
                    for e in state.get('outbox', []))):
                row['reason'] = 'DUPLICATE_OI_OPPORTUNITY_SUPPRESSED'
                evaluated.append(row)
                continue
            row.update(reason='QUALIFIED', risk_plan=plan,
                       selected_contract=contract, position_id=ident)
            evaluated.append(row)
            qualified.append((setup, plan, contract, ident))
        result['candidate_evaluations'] = evaluated
        if not qualified:
            result['reason'] = (evaluated[0]['reason'] if evaluated
                                else 'OI_ZONE_NO_QUALIFIED_CANDIDATE')
            return result
        qualified.sort(key=lambda item: (
            -float(item[2]['execution_score']),
            -float(item[1]['underlying_rr']),
            abs(spot-float(item[0]['oi_anchor']['strike'])),
            item[0]['kind'], item[3]))
        setup, plan, contract, ident = qualified[0]
        result['qualified_opportunity_rankings'] = [
            {'kind': item[0]['kind'], 'direction': item[0]['direction'],
             'strike': item[2]['strike'],
             'execution_score': item[2]['execution_score'],
             'score_is_probability': False}
            for item in qualified]
        result['opportunity_discovery'] = {
            'first_observed_at': now.isoformat(),
            'source_price_trigger_at': setup['source_price_trigger_at'],
            'confirmed_at': setup['confirmed_at'], 'not_backdated': True,
            'kind': setup['kind'], 'direction': setup['direction'],
        }
        result['entry_quality'] = plan.get('entry_quality')
        result.update(
            setup=setup, risk_plan=plan, selected_contract=contract,
            strike_selection={
                'selected_strike': contract['strike'],
                'selected_side': contract['side'],
                'selected_instrument_key': contract['instrument_key'],
                'rationale': contract.get('selection_rationale'),
                'oi_zone_anchor': setup['oi_anchor'],
            })
        position = {
            'id': ident, 'status': 'OPEN', 'session_date': day,
            'opened_at': now.isoformat(), 'direction': setup['direction'],
            'kind': setup['kind'], 'instrument_key': contract['instrument_key'],
            'expiry': expiry, 'strike': contract['strike'],
            'side': contract['side'], 'entry_spot': spot,
            'entry_ask': contract['ask'], 'stop': plan['stop_underlying'],
            't1': plan['t1_underlying'], 't2': plan['t2_underlying'],
            't1_hit': False, 'remaining_pct': 100,
            'last_candle': now.replace(second=0, microsecond=0).isoformat(),
            'last_progress_at': now.isoformat(), 'best_spot': spot,
            'entry_minute_ohlc_ignored': True, 'reference_position': True,
            'broker_order_submitted': False, 'broker_fill_confirmed': False,
            'plan': plan, 'contract': contract,
        }
        state['position'] = position
        queue(state, 'ENTRY', {
            'position': position, 'setup': setup,
            'structure': thesis, 'oi_levels': context,
            'oi_zone_analysis': result['oi_zone_analysis'],
            'forecast': result['forecast'],
        }, now)
        result.update(decision='QUALIFIED', reason='QUALIFIED_'+contract['side'],
                      position=position)
        return result
    except (DataError, ProviderError, ValueError, KeyError, TypeError) as exc:
        # A missing just-closed minute is not a trustworthy trade input.
        # Treat occasional publication lag as a safe NO_TRADE rather than
        # reporting every three-minute retry as a broken GitHub job.
        missing_candle = isinstance(exc, DataError) and str(exc) == 'LATEST_COMPLETED_CANDLE_MISSING'
        event_time = tick()
        if state.get('position'):
            recovered = expire_unexecuted_reference(state, event_time, config,
                                                      'CUTOFF_DATA_UNAVAILABLE_' + type(exc).__name__)
            if recovered:
                result.update(decision='REFERENCE_POSITION_EXPIRED',
                              reason='UNOBSERVED_1515_REFERENCE_CUTOFF',
                              reference_recovery=recovered,
                              data_error_at_exit=str(exc)[:240])
                return result
            # Before the exit cutoff, or if broker exposure may exist, never
            # clear a contract lock when its management inputs are missing.
            result.update(decision='POSITION_MONITORING_UNAVAILABLE',
                          reason='POSITION_LOCK_RETAINED', message=str(exc)[:240])
            queue(state, 'MONITORING_UNAVAILABLE',
                  {'position_id': state['position'].get('id'), 'session_date': day,
                   'cause': str(exc)[:240]}, event_time)
        elif missing_candle:
            misses = record_candle_delay(state, day, event_time)
            result.update(decision='NO_TRADE', reason='CANDLE_PUBLICATION_PENDING',
                          severity='WARNING' if misses < 3 else 'DEGRADED',
                          consecutive_delays=misses,
                          message='LATEST_COMPLETED_CANDLE_MISSING_NO_STALE_FALLBACK')
        else:
            result.update(decision='NO_TRADE', reason='DATA_OR_INTEGRATION_ERROR',
                          message=str(exc)[:240])
        return result
    except Exception as exc:
        result.update(decision='NO_TRADE', reason='UNEXPECTED_INTERNAL_ERROR', error_type=type(exc).__name__, message='Unexpected scan failure; no new entry is approved')
        if state.get('position'):
            result.update(decision='POSITION_MONITORING_UNAVAILABLE', reason='POSITION_LOCK_RETAINED')
            queue(state, 'MONITORING_UNAVAILABLE', {'position_id': state['position'].get('id'), 'session_date': day, 'cause': type(exc).__name__}, tick())
        return result
    finally:
        result['finished_at'] = tick().isoformat()
        if result.get('forecast') and result.get('spot') and ('bars' in locals()):
            try:
                result['forecast_statistics'] = record_and_assess(state, bars, datetime.fromisoformat(result['finished_at']), result['forecast'], config.forecast_horizon_minutes)
            except Exception as exc:
                result['forecast_assessment_error'] = type(exc).__name__
        evidence['expected_result'] = copy.deepcopy(result)
        evidence['expected_state_after'] = copy.deepcopy(state)
        identifier = started.strftime('%H%M%S%f')
        # Audit/input write failures are operational errors, but never discard
        # a qualified reference position or its durable outbox lock. main()
        # still commits state and exits nonzero so the workflow reports failure.
        try:
            result['input_capture'] = capture_inputs(audit_dir / 'inputs_v119_2' / day, identifier, evidence)
        except (OSError,ValueError,TypeError) as exc:
            result['persistence_error']='INPUT_CAPTURE_FAILED_'+type(exc).__name__
        try:
            append_audit(audit_dir / ('market_scan_v119_2_' + day + '.jsonl'), result)
        except (OSError,ValueError,TypeError) as exc:
            result['persistence_error']='AUDIT_WRITE_FAILED_'+type(exc).__name__

# market_scanner.py
import argparse
import json
import os
import smtplib
import ssl
import sys
from datetime import datetime
from email.message import EmailMessage
from pathlib import Path

def paths():
    return (Path(os.environ.get('STATE_FILE', 'state/market_state_v119_2.json')), Path(os.environ.get('AUDIT_DIR', 'audit')))

def alert_text(event):
    d = event['details']
    p = d.get('position') or d.get('position_context') or {}
    contract = d.get('contract') or p
    lines = ['NIFTY ' + event['kind'].replace('_', ' '), 'Original observation: ' + event['created_at']]
    if contract.get('side'):
        lines.append(f"Contract: {contract.get('strike')} {contract['side']} | Expiry {contract.get('expiry')}")
    for field, label in [('entry_spot', 'NIFTY entry reference'), ('entry_ask', 'Option ask reference'), ('stop', 'NIFTY stop'), ('t1', 'NIFTY target 1'), ('t2', 'NIFTY target 2'), ('remaining_pct', 'Remaining position %')]:
        if p.get(field) is not None:
            lines.append(f'{label}: {p[field]}')
    if d.get('new_stop') is not None:
        lines.append('Updated NIFTY stop: ' + str(d['new_stop']))
    reason = d.get('reason') or d.get('cause')
    if reason:
        lines.append('Reason: ' + str(reason).replace('_', ' '))
    if event['kind'] == 'REFERENCE_POSITION_EXPIRED_UNVERIFIED':
        lines.append('URGENT: This retires an ANALYTICAL reference only; no historical price or broker exit was verified.')
        lines.append('Check all actual Upstox positions. The scanner does not submit or close broker orders.')
        lines.append('Policy cutoff (not an observed fill): ' + str(d.get('policy_exit_due_at')))
    if event['kind'] == 'DATA_FEED_DEGRADED':
        lines.append('Three successive scans lacked the newest completed 1m candle. No stale bars were used for new trades.')
    possible = d.get('possible_touches') or []
    if possible:
        lines.append('Entry-minute possible touches (ordering unknown): ' + ', '.join(str(x) for x in possible))
        lines.append('No broker execution is inferred from whole-minute OHLC.')
    structure = d.get('structure') or {}
    oi = d.get('oi_levels') or {}
    if structure:
        lines.append(f"Market structure: {structure.get('state')} | Support {structure.get('support')} | Resistance {structure.get('resistance')} | 15m context {structure.get('context_15m')}")
    for key, label in [('put_support', 'Put OI support'), ('call_resistance', 'Call OI resistance')]:
        wall = oi.get(key)
        if wall:
            lines.append(f"{label}: {wall['strike']} | OI change {wall.get('oi_change')} | Pattern {wall.get('pattern', 'unavailable')}")
    if p.get('plan'):
        lines.append('Underlying reward/risk: ' + str(p['plan'].get('underlying_rr')))
    if p.get('management_state'):
        lines.append('Management: ' + p['management_state'])
    forecast = d.get('forecast') or {}
    if forecast:
        lines.append('Primary scenario: ' + forecast['primary_scenario'])
        lines.append('Scenario invalidation boundary: ' + str(forecast.get('protected_boundary')))
        lines.append('Evidence: ' + ', '.join(forecast.get('supporting_evidence') or []))
        if forecast.get('cautions'):
            lines.append('Cautions: ' + ', '.join(forecast['cautions']))
    sensitivity = (p.get('contract') or {}).get('plan_sensitivity') or {}
    if sensitivity.get('status') == 'LOCAL_SENSITIVITY_ESTIMATE':
        lines.append('Modelled option bid at underlying T1: ' + str(round(sensitivity['estimated_bid_at_underlying_t1'], 2)) + ' (unchanged-IV/Greeks approximation)')
    if d.get('reference_spot') is not None:
        lines.append('NIFTY at detection/interval reference: ' + str(d['reference_spot']))
    if d.get('detected_at'):
        lines.append('Detected at: ' + d['detected_at'])
    if d.get('event_time') or d.get('at'):
        lines.append('Event time / candle interval end: ' + str(d.get('event_time') or d['at']))
    if d.get('source'):
        lines.append('Observation source: ' + d['source'])
    if d.get('reference_bid_at_detection') is not None:
        lines.append('Option bid at detection: ' + str(d['reference_bid_at_detection']))
    lines.append('This is an analytical alert, not a submitted order or confirmed fill. Stops require management at the broker.')
    if event.get('manually_requeued_at') or event.get('delayed_delivery'):
        lines.append('Historical/delayed observation; this message is not a fresh entry instruction.')
    return '\n'.join(lines)

def deliver(s: dict, path: Path, token: str):
    sender = os.environ.get('EMAIL_SENDER', '')
    receiver = os.environ.get('EMAIL_RECEIVER', '')
    username = os.environ.get('EMAIL_USERNAME') or sender
    password = os.environ.get('EMAIL_PASSWORD', '')
    host = os.environ.get('SMTP_HOST', 'smtp.gmail.com')
    port = int(os.environ.get('SMTP_PORT', '465'))
    if not token:
        raise StateError('Notification claim token missing')
    if not any((e.get('kind') == 'ENTRY' and e.get('status') == 'CLAIMED' and e.get('claim') == token for e in s['outbox'])):
        return 0
    if not all((sender, receiver, username, password, token)):
        raise StateError('Email credentials or claim token missing')
    uncertain = False
    for event in s['outbox']:
        if event.get('kind') != 'ENTRY' or event.get('status') != 'CLAIMED' or event.get('claim') != token:
            continue
        label = 'HISTORICAL ' if event.get('delayed_delivery') else 'RETRIED ' if event.get('manually_requeued_at') else ''
        msg = EmailMessage()
        msg['Subject'] = 'NIFTY scanner: ' + label + event['kind']
        msg['From'] = sender
        msg['To'] = receiver
        msg['Message-ID'] = '<' + event['id'] + '@nifty-scanner.local>'
        msg.set_content(alert_text(event))
        try:
            event['delivery_stage'] = 'CONNECT'
            with smtplib.SMTP_SSL(host, port, timeout=20, context=ssl.create_default_context()) as smtp:
                event['delivery_stage'] = 'AUTHENTICATE'
                smtp.login(username, password)
                event['delivery_stage'] = 'SEND'
                smtp.send_message(msg)
            event['status'] = 'SENT'
            event['sent_at'] = datetime.now(IST).isoformat()
        except (OSError, smtplib.SMTPException) as exc:
            event['status'] = 'DELIVERY_UNCERTAIN'
            event['attempted_at'] = datetime.now(IST).isoformat()
            uncertain = True
            event['error_type'] = type(exc).__name__
        save(path, s)
    return 1 if uncertain else 0

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--version', action='store_true')
    mode.add_argument('--initialize-flat', action='store_true', help='Initialize only after manually reconciling prior scanner and broker positions')
    mode.add_argument('--scan-and-claim', action='store_true')
    mode.add_argument('--deliver-claimed', action='store_true')
    mode.add_argument('--reconcile-flat', metavar='POSITION_ID', help='After manual verification, close the matching alert lock without inventing a fill')
    mode.add_argument('--requeue-alert', metavar='ALERT_ID', help='After verifying non-delivery, explicitly requeue an uncertain alert')
    mode.add_argument('--migrate-state', metavar='SOURCE', help='Migrate a recognized existing state once; preserves its source and active lock')
    mode.add_argument('--forecast-report', action='store_true', help='Summarize recorded forward-underlying outcomes, without calling the API')
    args = parser.parse_args()
    if args.version:
        print(__version__)
        return 0
    state_path, audit_dir = paths()
    try:
        with lock(state_path):
            if args.migrate_state:
                migrated = migrate_state(Path(args.migrate_state), state_path, datetime.now(IST))
                print(json.dumps({'status': 'MIGRATED', 'schema': migrated['schema'], 'position_locked': bool(migrated.get('position'))}))
                return 0
            if args.initialize_flat:
                initialize(state_path, datetime.now(IST))
                print('Initialized flat state after operator reconciliation.')
                return 0
            state = load(state_path)
            if args.forecast_report:
                print(json.dumps(forecast_report(state.get('forecast_records') or []), sort_keys=True))
                return 0
            if args.reconcile_flat:
                position = state.get('position')
                if not isinstance(position, dict) or position.get('id') != args.reconcile_flat:
                    raise StateError('Position ID does not match the current open lock')
                now = datetime.now(IST).isoformat()
                closed = dict(position, status='CLOSED', closed_at=now, exit_reason='MANUAL_RECONCILIATION_NO_FILL')
                state['history'].append(closed)
                state['position'] = None
                state['last_exit'] = {'at': now, 'direction': closed.get('direction'), 'three': (state.get('thesis') or {}).get('last_3m')}
                save(state_path, state)
                append_audit(audit_dir / ('market_scan_v119_2_' + datetime.now(IST).date().isoformat() + '.jsonl'), {'operation': 'MANUAL_RECONCILIATION', 'position_id': args.reconcile_flat, 'at': now, 'fill': 'UNKNOWN'})
                print(json.dumps({'status': 'RECONCILED_FLAT', 'position_id': args.reconcile_flat, 'at': now}))
                return 0
            if args.requeue_alert:
                event = next((x for x in state['outbox'] if x.get('id') == args.requeue_alert), None)
                if not event or event.get('kind') != 'ENTRY' or event.get('status') not in {'CLAIMED', 'DELIVERY_UNCERTAIN'}:
                    raise StateError('Alert ID is not an uncertain or previously claimed alert')
                event.update(status='PENDING', claim=None, manually_requeued_at=datetime.now(IST).isoformat())
                save(state_path, state)
                append_audit(audit_dir / ('market_scan_v119_2_' + datetime.now(IST).date().isoformat() + '.jsonl'), {'operation': 'MANUAL_ALERT_REQUEUE', 'alert_id': args.requeue_alert, 'at': datetime.now(IST).isoformat()})
                print(json.dumps({'status': 'REQUEUED', 'alert_id': args.requeue_alert}))
                return 0
            token = os.environ.get('NOTIFICATION_CLAIM_TOKEN', '')
            if args.deliver_claimed:
                return deliver(state, state_path, token)
            if not token:
                raise StateError('NOTIFICATION_CLAIM_TOKEN is required')
            values = json.loads(os.environ.get('NIFTY_SCANNER_CONFIG', '{}'))
            if not isinstance(values, dict):
                raise StateError('NIFTY_SCANNER_CONFIG must be a JSON object')
            try:
                config = Config(**values)
            except TypeError:
                raise StateError('Unknown or invalid strategy configuration field') from None
            try:
                api = Upstox(os.environ.get('UPSTOX_ANALYTICS_TOKEN', ''))
            except ProviderError as exc:
                now = datetime.now(IST)
                recovered = expire_unexecuted_reference(state, now, config, 'UPSTOX_AUTHENTICATION_UNAVAILABLE')
                if state.get('position'):
                    queue(state, 'MONITORING_UNAVAILABLE', {'position_id': state['position'].get('id'), 'session_date': now.date().isoformat(), 'cause': 'TOKEN_UNAVAILABLE'}, now)
                if recovered or state.get('position'):
                    claim(state, token, datetime.now(IST))
                    save(state_path, state)
                print(json.dumps({'decision': 'ERROR', 'message': str(exc),
                                  'reference_recovery': recovered}, allow_nan=False), file=sys.stderr)
                return 1
            result = scan(state, api, config, audit_dir)
            claim(state, token, datetime.now(IST))
            save(state_path, state)
            print(json.dumps(result, sort_keys=True, allow_nan=False))
            return 1 if result['decision'] == 'POSITION_MONITORING_UNAVAILABLE' or bool(result.get('persistence_error')) or result['reason'] in {'DATA_OR_INTEGRATION_ERROR', 'UNEXPECTED_INTERNAL_ERROR', 'PRIOR_SESSION_POSITION_REQUIRES_RECONCILIATION'} else 0
    except (StateError, OSError, ValueError) as exc:
        print(json.dumps({'decision': 'ERROR', 'message': str(exc)}, allow_nan=False), file=sys.stderr)
        return 1
if __name__ == '__main__':
    sys.exit(main())
