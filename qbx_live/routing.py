"""
Three-fold-way routing for the five-channel machine.

``QBX/Formal/MultiProver/ThreeFoldWay.lean`` proves the three-fold-way type of
the matrices each channel computes (:data:`CHANNEL_TYPES`).  This module uses
two consequences of those theorems to plan an evaluation; neither changes a
verdict.

1. **Real points are exact.**  A family of real type can be computed in real
   (here: integer) arithmetic.  The fold channel's permutation matrices, the
   writhe character at ``t = ±1`` and the Burau matrices at ``t = −1``
   (``fold_isReal``, ``charRep_isReal``, ``harmonic_pi_isReal``) are integer
   data, cheap to compute and compared exactly.  They run first as refuters.
   At non-real ``t`` the Burau channel is of complex type
   (``anchor_isComplex``, ``harmonic_isComplex``) and needs ℤ[t, t⁻¹] or
   floating point, so it runs later.

2. **The sweep folds in half.**  Complex conjugation exchanges the harmonic
   readings at ``θ`` and ``−θ`` (``burauAt_neg``), so the resonance set is
   symmetric (``neg_mem_resonanceSet``, ``two_pi_sub_mem_resonanceSet``).  On
   the grid ``θ_k = 2πk/N`` sample ``N − k`` equals sample ``k``, and
   :func:`harmonic_reading_folded` computes only ``k ≤ N/2``.

**Soundness of the plan.**  Every refuter is a function of the braid element
(``Channel.agree_of_eval_eq``), so a refutation is always correct; if no
refuter fires, the claim is decided by the complete fold channel (Garside
normal form, ``verdict_eq_proved_iff``).  Hence :func:`route` returns the same
``PROVED`` / ``REFUTED`` verdict as :func:`qbx_ir.algebra.multiprover.verdict`
(checked in ``tests/qbx_live/test_routing.py``).  The *order* of the refuters is
a cost heuristic, not a theorem.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Dict, List, Optional, Tuple

import numpy as np

from qbx_ir.algebra import multiprover as mp
from qbx_ir.algebra.garside import left_normal_form
from qbx_ir.algebra.invariants import permutation, writhe
from qbx_ir.algebra.polynomial_invariants import burau_matrix
from qbx_ir.core.braid import Braid

#: Proved three-fold-way type of each channel's matrices (Lean name in brackets).
CHANNEL_TYPES: Dict[str, Tuple[str, str]] = {
    "fold": ("real", "fold_isReal"),
    "link": ("complex at non-real t, real at t = ±1", "writheChar_isComplex, charRep_isReal"),
    "anchor": ("complex at non-real t", "anchor_isComplex"),
    "harmonic": ("complex for sin θ ≠ 0, real at θ = π", "harmonic_isComplex, harmonic_pi_isReal"),
    "oscillator": ("quaternionic, not real (fundamental strand, classical limit)",
                   "su2_isQuaternionic, su2_not_real"),
}


# ----------------------------------------------------------------------------- exact real points

def burau_at_minus_one(braid: Braid) -> Tuple[Tuple[int, ...], ...]:
    """The reduced Burau matrix at the real point ``t = −1``, exactly (integer entries)."""
    out = []
    for row in burau_matrix(braid):
        r = []
        for e in row:
            v = sum((Fraction(c) * (1 if k % 2 == 0 else -1) for k, c in e.coeffs.items()),
                    Fraction(0))
            if v.denominator != 1:
                raise ValueError("non-integral Burau value at t = -1")
            r.append(int(v))
        out.append(tuple(r))
    return tuple(out)


# ----------------------------------------------------------------------------- folded sweep

def harmonic_reading_folded(braid: Braid, points: int = mp.SWEEP_POINTS) -> Tuple[bool, ...]:
    """The harmonic resonance pattern on ``θ_k = 2πk/points``, computing only
    ``k ≤ points/2`` and filling ``k > points/2`` by ``pattern[k] = pattern[points − k]``
    (``two_pi_sub_mem_resonanceSet``)."""
    n = braid.strand_count
    if n < 2:
        return tuple(False for _ in range(points))
    half = points // 2 + 1
    mat = burau_matrix(braid)
    thetas = 2 * math.pi * np.arange(half) / points
    m = len(mat)
    stack = np.zeros((half, m, m), dtype=complex)
    for r, row in enumerate(mat):
        for c, entry in enumerate(row):
            if not entry.coeffs:
                continue
            exps = np.array(list(entry.coeffs.keys()), dtype=float)
            coeffs = np.array([float(v) for v in entry.coeffs.values()])
            stack[:, r, c] = np.exp(1j * np.outer(thetas, exps)) @ coeffs
    if n == 3:
        first = [bool(x) for x in np.abs(np.trace(stack, axis1=1, axis2=2)) <= 2 + 1e-9]
    else:
        ev = np.linalg.eigvals(stack)
        first = [bool(x) for x in np.any(np.abs(np.abs(ev) - 1) < 1e-7, axis=1)]
    return tuple(first[k] if k < half else first[points - k] for k in range(points))


# ----------------------------------------------------------------------------- routing

@dataclass(frozen=True)
class Step:
    name: str          # refuter name
    channel: str       # channel it belongs to
    kind: str          # "real-exact", "complex-exact", "complex-sampled", "decider"
    lean: str          # theorem making it sound / of this type


#: The refuters, cheapest exact real-type checks first.
PLAN: Tuple[Step, ...] = (
    Step("permutation", "fold", "real-exact", "fold_isReal"),
    Step("writhe", "link", "real-exact", "charRep_isReal"),
    Step("burau_at_-1", "harmonic", "real-exact", "harmonic_pi_isReal"),
    Step("burau_exact", "anchor", "complex-exact", "anchor_isComplex"),
    Step("link_spectrum", "link", "complex-exact", "Channel.agree_of_eval_eq"),
    Step("harmonic_folded", "harmonic", "complex-sampled", "two_pi_sub_mem_resonanceSet"),
)

_READ: Dict[str, Callable[[Braid], object]] = {
    "permutation": permutation,
    "writhe": writhe,
    "burau_at_-1": burau_at_minus_one,
    "burau_exact": mp.anchor_reading,
    "link_spectrum": mp.link_reading,
    "harmonic_folded": harmonic_reading_folded,
}


@dataclass(frozen=True)
class RoutedVerdict:
    verdict: str                      # "PROVED" / "REFUTED"
    refuted_by: Optional[Step]        # the first refuter that fired, if any
    steps_run: Tuple[str, ...]        # refuters evaluated, in order
    decided_by_fold: bool             # the normal forms were compared

    def to_dict(self) -> dict:
        return {
            "verdict": self.verdict,
            "refuted_by": None if self.refuted_by is None else {
                "check": self.refuted_by.name, "channel": self.refuted_by.channel,
                "kind": self.refuted_by.kind, "lean": self.refuted_by.lean},
            "steps_run": list(self.steps_run),
            "decided_by_fold": self.decided_by_fold,
        }


def route(b1: Braid, b2: Braid, plan: Tuple[Step, ...] = PLAN) -> RoutedVerdict:
    """Decide ``b1 = b2``: run the refuters in ``plan`` order, stop at the first
    disagreement; otherwise compare Garside normal forms."""
    if b1.strand_count != b2.strand_count:
        raise ValueError("braids on different strand counts")
    run: List[str] = []
    for step in plan:
        run.append(step.name)
        read = _READ[step.name]
        if read(b1) != read(b2):
            return RoutedVerdict("REFUTED", step, tuple(run), False)
    proved = left_normal_form(b1) == left_normal_form(b2)
    return RoutedVerdict("PROVED" if proved else "REFUTED", None, tuple(run), True)
