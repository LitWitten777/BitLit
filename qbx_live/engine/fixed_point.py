"""Fixed-point engine: lattice states, merging, synchronous and asynchronous iteration.

The guarantees come from the seal lane (``QBX/Formal/Seal/``):

* **S3** ``MergeTree.eval_eq_of_mem_iff`` — merging join-semilattice states gives a result that
  depends only on the *set* of states merged.  So :func:`merge_deliveries` may receive worker
  states in any order, bracketing, or with duplicates (re-sent messages) and still returns the
  same state.  The function checks nothing at run time; it relies on ``join`` being a lattice
  join (associative, commutative, idempotent), which :func:`check_join` tests on samples.
* **S4** ``iterate_card_bot_eq_lfp`` / ``chaotic_eventually_lfp`` — for a monotone update on a
  finite lattice, synchronous iteration from bottom stops at the least fixed point within
  ``card`` rounds, and asynchronous iteration along a fair schedule reaches the same point.
  :func:`run_sync` and :func:`run_async` report the rounds / single-component updates used, so
  the two can be compared (family E of the plan).
"""

from __future__ import annotations

import itertools
import random
from dataclasses import dataclass, field
from typing import Callable, Iterable, List, Sequence, Tuple

from qbx_engine import seal

State = Tuple  # a product-lattice state: one component per node


def check_join(join: Callable, samples: Sequence) -> bool:
    """Test the lattice-join laws (associative, commutative, idempotent) on ``samples``."""
    for a, b in itertools.product(samples, repeat=2):
        if join(a, b) != join(b, a) or join(a, a) != a:
            return False
    for a, b, c in itertools.product(samples, repeat=3):
        if join(join(a, b), c) != join(a, join(b, c)):
            return False
    return True


def merge_deliveries(deliveries: Iterable, join: Callable):
    """Merge worker states in whatever order they arrive (S3: the order does not matter)."""
    return seal.merge(deliveries, join)


@dataclass
class SyncRun:
    point: State
    rounds: int
    residuals: List[int] = field(default_factory=list)  # components changed per round


def run_sync(F: Callable[[State], State], bottom: State, max_rounds: int) -> SyncRun:
    """Kleene iteration ``x ← F(x)`` from ``bottom`` until ``F(x) = x``.

    ``residuals[r]`` is the number of components that changed in round ``r`` (the convergence
    heat strip of the plan); the final round has residual 0."""
    x = tuple(bottom)
    residuals: List[int] = []
    for r in range(max_rounds + 1):
        y = tuple(F(x))
        changed = sum(1 for a, b in zip(x, y) if a != b)
        residuals.append(changed)
        if changed == 0:
            point, rounds = seal.kleene(F, tuple(bottom), max_rounds)
            assert point == x and rounds == r  # same object as the seal-lane function
            return SyncRun(x, r, residuals)
        x = y
    raise RuntimeError("no fixed point within max_rounds")


@dataclass
class AsyncRun:
    point: State
    updates: int        # single-component recomputations performed
    steps: int          # schedule positions consumed


def run_async(F: Callable[[State], State], bottom: State, schedule: Iterable[int],
              max_steps: int) -> AsyncRun:
    """Chaotic iteration: at each step only the scheduled component is recomputed.

    Stops as soon as the state is a fixed point of ``F`` (checked after every change), or
    raises if ``max_steps`` steps are not enough.  With a fair schedule (every component
    visited infinitely often) S4 guarantees the result is the least fixed point."""
    x = tuple(bottom)
    updates = 0
    it = iter(schedule)
    if tuple(F(x)) == x:
        return AsyncRun(x, 0, 0)
    for step in range(1, max_steps + 1):
        i = next(it)
        fx = tuple(F(x))
        if fx[i] != x[i]:
            x = x[:i] + (fx[i],) + x[i + 1:]
            updates += 1
            if tuple(F(x)) == x:
                return AsyncRun(x, updates, step)
    raise RuntimeError("no fixed point within max_steps")


def round_robin(n: int) -> Iterable[int]:
    """The fair schedule ``0, 1, …, n−1, 0, 1, …``."""
    return itertools.cycle(range(n))


def random_fair(n: int, seed: int = 0) -> Iterable[int]:
    """A fair random schedule: random permutations of ``range(n)``, one after another."""
    rng = random.Random(seed)
    while True:
        perm = list(range(n))
        rng.shuffle(perm)
        yield from perm


def reachability_update(edges: Sequence[Tuple[int, int]], sources: Sequence[int], n: int
                        ) -> Callable[[State], State]:
    """A standard monotone update on the Boolean lattice ``{False, True}ⁿ``: node ``v`` is
    reached if it is a source or has a reached predecessor.  Its least fixed point is the set of
    nodes reachable from ``sources`` (a family-E style workload)."""
    preds: List[List[int]] = [[] for _ in range(n)]
    for u, v in edges:
        preds[v].append(u)
    src = set(sources)

    def F(x: State) -> State:
        return tuple((v in src) or any(x[u] for u in preds[v]) for v in range(n))

    return F
