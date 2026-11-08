"""
Kelly-allocated graduated multi-prover, and timing instrumentation of the
chunk scheduler — runtime mirror of ``QBX/Formal/MultiProver/KellyAllocation.lean``
and ``KellyScheduler.lean``.

Graduated design
----------------
The four incomplete channels (link, anchor, harmonic, oscillator) are
*refuters*: a disagreement is a valid refutation (``verdict_ne_proved_of_disagree``),
an agreement decides nothing.  The fold channel (Garside normal form) is the
complete decider.  For each claim ``b1 = b2``:

1. every refuter gets a tick budget: ``floor`` plus its share of the spare
   ticks, proportional to its Kelly weight (``tick_share`` = Lean ``tickShare``);
2. refuters run in order (cheap first) if their budget covers their cost; the
   first disagreement answers ``REFUTED``;
3. if no refuter refuted, the fold channel decides (``graduatedRun``).

The answer is always the machine's verdict, whatever the statistics, budgets
and update rule (``graduated_channels_eq_verdict``,
``graduatedLoop_channels_eq_verdict``).  Kelly only changes *how much work* is
spent, never the answer.

Statistics: each refuter keeps ``attempts`` / ``decisions`` (refutations).  Its
rate is the Laplace estimate ``(d + 1) / (a + 2)`` (``TierStats.rate``) and its
weight the clipped Kelly fraction ``max(0, (p b − (1 − p)) / b)``
(``Sovereign.Organism.kellyQ``) with payoff ``b = cost(fold) / cost(channel)``:
a refutation saves a fold run, a failed attempt wastes the channel's cost.  A
refuter with weight 0 is *dead* (``kellyWeight_eq_zero_of_failures``): it gets
the floor, which is normally below its cost, so it is skipped.  Only refuters
that actually ran are charged; every ``explore_every``-th claim the skipped
refuters are also run *after* the answer is fixed, to refresh their statistics
(an update rule that keeps the tiers, so the Lean theorems apply).

Costs are in ticks of a deterministic model fitted to single-core timings of
this implementation (``default_cost``); pass ``cost=`` to use your own.
"""

from __future__ import annotations

import math
import time
from dataclasses import dataclass, field, replace
from fractions import Fraction
from typing import Callable, Dict, List, Optional, Sequence, Tuple

from qbx_ir.algebra.garside import left_normal_form
from qbx_ir.algebra.multiprover import (
    SWEEP_POINTS,
    balanced_reduce,
    chunk_reading,
    harmonic_reading_from_burau,
    link_reading,
    oscillator_reading,
    same_reading,
    split_word,
)
from qbx_ir.core.braid import Braid

REFUTERS: Tuple[str, ...] = ("link", "oscillator", "anchor", "harmonic")


# --------------------------------------------------------------------------
# Kelly allocation (mirror of KellyAllocation.lean, exact rationals)
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class TierStats:
    """``TierStats``: attempts and decisions of one tier."""

    attempts: int = 0
    decisions: int = 0

    @property
    def rate(self) -> Fraction:
        """Laplace estimate ``(decisions + 1) / (attempts + 2)`` (``TierStats.rate``)."""
        return Fraction(self.decisions + 1, self.attempts + 2)

    def record(self, decided: bool) -> "TierStats":
        """``TierStats.record``."""
        return TierStats(self.attempts + 1, self.decisions + (1 if decided else 0))


def kelly_q(p: Fraction, b: Fraction) -> Fraction:
    """Clipped Kelly fraction ``max 0 ((p b − (1 − p)) / b)`` (``kellyQ``)."""
    return max(Fraction(0), (p * b - (1 - p)) / b)


def kelly_weight(stats: TierStats, payoff: Fraction) -> Fraction:
    """``kellyWeight``."""
    return kelly_q(stats.rate, Fraction(payoff))


def _eff_weight(ws: Sequence[Fraction], w: Fraction) -> Fraction:
    return Fraction(1) if sum(ws) == 0 else w


def _eff_total(ws: Sequence[Fraction]) -> Fraction:
    return Fraction(len(ws)) if sum(ws) == 0 else sum(ws)


def spare_ticks(total: int, floor: int, ws: Sequence[Fraction]) -> int:
    """``spareTicks`` (truncated subtraction, as in ℕ)."""
    return max(0, total - floor * len(ws))


def tick_share(total: int, floor: int, ws: Sequence[Fraction], w: Fraction) -> int:
    """``tickShare``: the floor plus the proportional part of the spare, rounded down."""
    if not ws:
        return floor
    return floor + math.floor(spare_ticks(total, floor, ws) * _eff_weight(ws, w) / _eff_total(ws))


def alloc_ticks(total: int, floor: int, ws: Sequence[Fraction]) -> List[int]:
    """``allocTicks``."""
    return [tick_share(total, floor, ws, w) for w in ws]


# --------------------------------------------------------------------------
# Cost model
# --------------------------------------------------------------------------


def default_cost(channel: str, b1: Braid, b2: Braid) -> int:
    """Ticks (≈ µs on one core) for a channel on the pair, from a model fitted to
    single-core timings of this implementation (strand counts 3–5, words of
    50–800 letters).  ``L`` is the word length, ``m = n − 1`` the Burau size.

    * link: linear;  oscillator: linear (four levels, small matrices);
    * anchor: chunked Burau products with a balanced merge, ≈ ``2.5 L^1.5 m³``;
    * harmonic: anchor plus the vectorised evaluation of the combined matrix at
      the ``SWEEP_POINTS`` sample points, ≈ ``5 m² L`` more;
    * fold: Garside normal form, ≈ ``0.45 L² n^1.5``.

    Measured on this implementation (one core): at ``n = 3``, ``L = 800`` the
    fold channel took 1.4 s, the chunked Burau reading 0.44 s, the oscillator
    0.12 s and the link reading 1 ms.  These are rough fits, used only to set
    budgets; they never affect answers.
    """
    n = b1.strand_count
    m = max(n - 1, 1)
    total = 0
    for b in (b1, b2):
        L = max(len(b.word), 1)
        if channel == "link":
            total += 2 * L
        elif channel == "oscillator":
            total += 50 * L * n
        elif channel == "anchor":
            total += int(2.5 * L ** 1.5 * m ** 3)
        elif channel == "harmonic":
            total += int(2.5 * L ** 1.5 * m ** 3) + 5 * m * m * L
        elif channel == "fold":
            total += int(0.45 * L * L * n ** 1.5)
        else:
            raise ValueError(channel)
    return max(total, 1)


# --------------------------------------------------------------------------
# The graduated prover
# --------------------------------------------------------------------------


@dataclass
class KellyResult:
    verdict: str  # "PROVED" / "REFUTED"
    decided_by: str  # the refuter that refuted, or "fold"
    budgets: Dict[str, int]
    costs: Dict[str, int]
    ran: Tuple[str, ...]
    skipped: Tuple[str, ...]
    seconds: Dict[str, float]


class _PairReadings:
    """Lazily computed channel readings of a pair, shared between channels
    (anchor and harmonic share the chunked Burau matrix)."""

    def __init__(self, b1: Braid, b2: Braid, chunk_size: int):
        self.b = (b1, b2)
        self.chunk_size = chunk_size
        self._sched = None

    def sched(self):
        if self._sched is None:
            self._sched = tuple(
                balanced_reduce([chunk_reading(b.strand_count, c)
                                 for c in split_word(b.word, self.chunk_size)])
                for b in self.b
            )
        return self._sched

    def disagree(self, channel: str) -> bool:
        b1, b2 = self.b
        if channel == "link":
            return not same_reading("link", link_reading(b1), link_reading(b2))
        if channel == "oscillator":
            return not same_reading("oscillator", oscillator_reading(b1), oscillator_reading(b2))
        if channel == "anchor":
            s1, s2 = self.sched()
            return s1.burau != s2.burau
        if channel == "harmonic":
            s1, s2 = self.sched()
            n = b1.strand_count
            return harmonic_reading_from_burau(s1.burau, n) != harmonic_reading_from_burau(s2.burau, n)
        raise ValueError(channel)


@dataclass
class KellyMultiProver:
    """The graduated multi-prover with Kelly tick allocation.

    ``budget_factor``: the refuters share ``budget_factor × cost(fold)`` ticks per
    claim; ``floor``: ticks every refuter gets regardless of its weight (as a
    fraction of the same unit, default 0: dead refuters are skipped).
    """

    refuters: Tuple[str, ...] = REFUTERS
    budget_factor: Fraction = Fraction(1)
    floor_factor: Fraction = Fraction(0)
    explore_every: int = 16
    chunk_size: int = 64
    cost: Callable[[str, Braid, Braid], int] = default_cost
    stats: Dict[str, TierStats] = field(default_factory=dict)
    tasks: int = 0
    fold_runs: int = 0

    def __post_init__(self):
        for c in self.refuters:
            self.stats.setdefault(c, TierStats())

    def payoff(self, channel: str, b1: Braid, b2: Braid) -> Fraction:
        return Fraction(self.cost("fold", b1, b2), self.cost(channel, b1, b2))

    def allocate(self, b1: Braid, b2: Braid) -> Tuple[Dict[str, int], Dict[str, int]]:
        """Budgets (``tickShare``) and costs of every refuter for this claim."""
        costs = {c: self.cost(c, b1, b2) for c in self.refuters}
        fold_cost = self.cost("fold", b1, b2)
        total = int(self.budget_factor * fold_cost)
        floor = int(self.floor_factor * fold_cost)
        ws = [kelly_weight(self.stats[c], self.payoff(c, b1, b2)) for c in self.refuters]
        shares = alloc_ticks(total, floor, ws)
        return dict(zip(self.refuters, shares)), costs

    def decide(self, b1: Braid, b2: Braid) -> KellyResult:
        if b1.strand_count != b2.strand_count:
            raise ValueError("braids on different strand counts")
        self.tasks += 1
        budgets, costs = self.allocate(b1, b2)
        readings = _PairReadings(b1, b2, self.chunk_size)
        ran: List[str] = []
        seconds: Dict[str, float] = {}
        decided_by = None
        for c in self.refuters:
            if budgets[c] < costs[c]:
                continue
            t0 = time.perf_counter()
            refuted = readings.disagree(c)
            seconds[c] = time.perf_counter() - t0
            ran.append(c)
            self.stats[c] = self.stats[c].record(refuted)
            if refuted:
                decided_by = c
                break
        if decided_by is None:
            t0 = time.perf_counter()
            proved = left_normal_form(b1) == left_normal_form(b2)
            seconds["fold"] = time.perf_counter() - t0
            self.fold_runs += 1
            verdict, decided_by = ("PROVED" if proved else "REFUTED"), "fold"
        else:
            verdict = "REFUTED"
        skipped = tuple(c for c in self.refuters if budgets[c] < costs[c])
        if self.explore_every and self.tasks % self.explore_every == 0:
            # Exploration: refresh the statistics of skipped refuters.  The answer
            # is already fixed, so this is only a statistics update.
            for c in skipped:
                self.stats[c] = self.stats[c].record(readings.disagree(c))
        return KellyResult(verdict, decided_by, budgets, costs, tuple(ran), skipped, seconds)


# --------------------------------------------------------------------------
# Instrumentation: chunked phase vs reconstruction phase
# --------------------------------------------------------------------------


@dataclass
class SchedulerTiming:
    """Wall-clock split of one scheduled verdict (seconds, one core).

    * ``chunk_map``: summaries (perm, writhe, exact Burau) of every chunk — the
      embarrassingly parallel part (``schedule_correct``); ``chunk_max`` is the
      slowest single chunk;
    * ``merge``: the balanced reduction of the summaries (⌈log₂ k⌉ rounds);
    * ``reconstruct``: the non-homomorphic channels on the combined braid —
      Garside normal form (``fold``), linking spectrum (``link``), Jones values
      (``oscillator``) on the whole word, and the resonance pattern from the
      combined Burau matrix (``harmonic``).
    """

    chunks: int
    chunk_map: float
    chunk_max: float
    merge: float
    reconstruct: Dict[str, float]

    @property
    def reconstruct_total(self) -> float:
        return sum(self.reconstruct.values())

    def reconstruct_fraction(self, workers: int = 1) -> float:
        """Share of the reconstruction in the total, if the chunk map runs on
        ``workers`` cores (ideal split, bounded below by the slowest chunk)."""
        par = max(self.chunk_map / max(workers, 1), self.chunk_max) + self.merge
        tot = par + self.reconstruct_total
        return self.reconstruct_total / tot if tot > 0 else 0.0


def timed_scheduled_reading(braid: Braid, chunk_size: int = 64) -> SchedulerTiming:
    """Run the scheduler on one braid and time each phase."""
    n = braid.strand_count
    parts = []
    t_max = 0.0
    t0 = time.perf_counter()
    for c in split_word(braid.word, chunk_size):
        s = time.perf_counter()
        parts.append(chunk_reading(n, c))
        t_max = max(t_max, time.perf_counter() - s)
    t_map = time.perf_counter() - t0
    t0 = time.perf_counter()
    combined = balanced_reduce(parts)
    t_merge = time.perf_counter() - t0
    rec: Dict[str, float] = {}
    t0 = time.perf_counter()
    left_normal_form(braid)
    rec["fold"] = time.perf_counter() - t0
    t0 = time.perf_counter()
    link_reading(braid)
    rec["link"] = time.perf_counter() - t0
    t0 = time.perf_counter()
    oscillator_reading(braid)
    rec["oscillator"] = time.perf_counter() - t0
    t0 = time.perf_counter()
    harmonic_reading_from_burau(combined.burau, n)
    rec["harmonic"] = time.perf_counter() - t0
    return SchedulerTiming(len(parts), t_map, t_max, t_merge, rec)


__all__ = [
    "REFUTERS",
    "TierStats",
    "kelly_q",
    "kelly_weight",
    "spare_ticks",
    "tick_share",
    "alloc_ticks",
    "default_cost",
    "KellyResult",
    "KellyMultiProver",
    "SchedulerTiming",
    "timed_scheduled_reading",
]
