"""
The five-channel resonance machine — runtime mirror of ``QBX/Formal/MultiProver``.

A braid is read by five channels; a claimed identity ``b1 = b2`` is decided by
the (complete) fold channel and the other four channels report whether they
*resonate* (agree) or not.  The Lean files named below prove the statements
the tests in ``tests/qbx_ir/test_multiprover.py`` check numerically.

============  ==============================================  =========================
channel       reading                                         Lean
============  ==============================================  =========================
fold          Garside left normal form + permutation          ``BraidPolytope.lean``
link          component count + sorted linking numbers        ``LinkCoupling.lean``
anchor        reduced Burau matrix over ℤ[t, t⁻¹]             ``TorusAnchor.lean``
harmonic      resonance pattern on a grid of θ ∈ [0, 2π)      ``HarmonicSweep.lean``
oscillator    Jones invariant at q = e^{iπ/r}, r = 3..6       ``OscillatorChannel.lean``
============  ==============================================  =========================

* :func:`verdict` — ``"PROVED"`` iff the normal forms agree
  (``verdict_eq_proved_iff``); otherwise ``"REFUTED"`` with the list of
  channels that disagree (never empty: the fold channel always does,
  ``resonance_iff``).
* :func:`defect` / :func:`heal` — the defect ``b2⁻¹ b1`` repairs the claim
  (``heal``, ``defect_eq_one_iff``).
* :func:`harmonic_resonant` — for 3-braids the exact criterion
  ``|tr ρ̄(β)(e^{iθ})| ≤ 2`` (``resonance_iff_trace``); every 3-braid
  resonates when ``cos θ > -1/2`` (``resonance_universal``).

The harmonic and oscillator readings are floating-point samples of exact
objects; equal braids always give equal samples, but agreement of samples is
evidence, not proof.  Only the fold channel decides.
"""

from __future__ import annotations

import cmath
import math
from dataclasses import dataclass
from typing import Dict, List, Tuple

import numpy as np

from qbx_ir.algebra.garside import left_normal_form
from qbx_ir.algebra.invariants import component_count, linking_matrix, permutation
from qbx_ir.algebra.polynomial_invariants import burau_matrix
from qbx_ir.core.braid import Braid

CHANNELS = ("fold", "link", "anchor", "harmonic", "oscillator")

#: Sweep grid for the harmonic channel (avoids the exceptional points of the
#: Squier form, θ = ±2π/3, by using an odd number of samples).
SWEEP_POINTS = 181

#: Roots of unity q = e^{iπ/r} probed by the oscillator channel.
OSCILLATOR_LEVELS = (3, 4, 5, 6)

_TOL = 1e-9


# --------------------------------------------------------------------------
# Channel readings
# --------------------------------------------------------------------------


def fold_reading(braid: Braid):
    """Garside normal form (a path of permutohedron vertices) and permutation."""
    return (left_normal_form(braid), permutation(braid))


def link_reading(braid: Braid) -> Tuple[int, Tuple[int, ...]]:
    """Number of closure components and the multiset of pairwise linking numbers."""
    return (component_count(braid), tuple(sorted(linking_matrix(braid).values())))


def anchor_reading(braid: Braid) -> Tuple[Tuple[Tuple[Tuple[int, int], ...], ...], ...]:
    """The reduced Burau matrix over ℤ[t, t⁻¹], as exact integer coefficient tables."""
    return tuple(
        tuple(tuple(sorted(entry.to_int_dict().items())) for entry in row)
        for row in burau_matrix(braid)
    )


def _evaluate_matrix(mat, theta: float) -> np.ndarray:
    """An exact Burau matrix over ℤ[t, t⁻¹] evaluated at t = e^{iθ}."""
    t = cmath.exp(1j * theta)
    return np.array([[entry.evaluate(t) for entry in row] for row in mat], dtype=complex)


def burau_at(braid: Braid, theta: float) -> np.ndarray:
    """ρ̄(β)(e^{iθ}) as a complex matrix."""
    return _evaluate_matrix(burau_matrix(braid), theta)


def _resonant_matrix(m: np.ndarray, strand_count: int) -> bool:
    if strand_count < 2:
        return False
    if strand_count == 3:
        return abs(np.trace(m)) <= 2 + 1e-9
    return bool(np.any(np.abs(np.abs(np.linalg.eigvals(m)) - 1) < 1e-7))


def harmonic_resonant(braid: Braid, theta: float) -> bool:
    """Does ρ̄(β)(e^{iθ}) have an eigenvalue on the unit circle?

    For 3-braids this is the exact criterion ``|tr| ≤ 2`` of
    ``resonance_iff_trace``; for other strand counts the eigenvalues are
    computed numerically.
    """
    if braid.strand_count < 2:
        return False
    return _resonant_matrix(burau_at(braid, theta), braid.strand_count)


def harmonic_reading_from_burau(mat, strand_count: int,
                                points: int = SWEEP_POINTS) -> Tuple[bool, ...]:
    """The resonance pattern computed from an exact Burau matrix (e.g. the combined
    matrix of the chunk scheduler).

    Every entry ``Σ c_e t^e`` is evaluated at all sample points at once
    (``exp(i e θ_k)`` as one array product), and the resonance test runs on the
    stack of evaluated matrices; the matrix is never re-multiplied along the word.
    """
    if strand_count < 2:
        return tuple(False for _ in range(points))
    thetas = 2 * math.pi * np.arange(points) / points
    m = len(mat)
    stack = np.zeros((points, m, m), dtype=complex)
    for r, row in enumerate(mat):
        for c, entry in enumerate(row):
            if not entry.coeffs:
                continue
            exps = np.array(list(entry.coeffs.keys()), dtype=float)
            coeffs = np.array([float(v) for v in entry.coeffs.values()])
            stack[:, r, c] = np.exp(1j * np.outer(thetas, exps)) @ coeffs
    if strand_count == 3:
        return tuple(bool(x) for x in np.abs(np.trace(stack, axis1=1, axis2=2)) <= 2 + 1e-9)
    ev = np.linalg.eigvals(stack)
    return tuple(bool(x) for x in np.any(np.abs(np.abs(ev) - 1) < 1e-7, axis=1))


def harmonic_reading(braid: Braid, points: int = SWEEP_POINTS) -> Tuple[bool, ...]:
    """The resonance pattern on the grid θ_k = 2πk / points.

    The exact Burau matrix is computed once and evaluated at every sample point
    (the same numbers as calling :func:`harmonic_resonant` per point, which
    recomputes the matrix each time: 181 matrix products along the word instead
    of one).
    """
    if braid.strand_count < 2:
        return tuple(False for _ in range(points))
    return harmonic_reading_from_burau(burau_matrix(braid), braid.strand_count, points)


def oscillator_reading(braid: Braid) -> Tuple[complex, ...]:
    """The Jones invariant of the closure at q = e^{iπ/r} for each probed level r."""
    from qbx_ir.quantum.representation import jones_from_quantum_trace

    out = []
    for r in OSCILLATOR_LEVELS:
        v = jones_from_quantum_trace(braid, cmath.exp(1j * math.pi / r))
        out.append(complex(round(v.real, 8), round(v.imag, 8)))
    return tuple(out)


_READERS = {
    "fold": fold_reading,
    "link": link_reading,
    "anchor": anchor_reading,
    "harmonic": harmonic_reading,
    "oscillator": oscillator_reading,
}


def reading(braid: Braid) -> Dict[str, object]:
    """All five channel readings of a braid."""
    return {c: _READERS[c](braid) for c in CHANNELS}


def quantum_dim(r: int, k: int) -> float:
    """[k] at q = e^{iπ/r}: sin(kπ/r) / sin(π/r) (``quantumDim``)."""
    return math.sin(k * math.pi / r) / math.sin(math.pi / r)


# --------------------------------------------------------------------------
# Verdict and healing
# --------------------------------------------------------------------------


def same_reading(channel: str, x, y) -> bool:
    """Do two readings of ``channel`` agree?

    The oscillator readings are floating-point values accumulated along the
    word, so two words of the same braid can differ in the last bits.  They
    are compared with a relative tolerance instead of exactly (exact
    comparison of rounded values is unsound at rounding boundaries: two
    values ``x.xxxxxxxx4999…`` and ``x.xxxxxxxx5000…`` round differently).
    All other readings are exact (or computed from exact data) and are
    compared with ``==``.
    """
    if channel == "oscillator":
        return len(x) == len(y) and all(
            abs(a - b) <= 1e-7 * (1 + abs(a)) for a, b in zip(x, y)
        )
    return x == y


@dataclass(frozen=True)
class Certificate:
    verdict: str  # "PROVED" or "REFUTED"
    agree: Tuple[str, ...]
    disagree: Tuple[str, ...]

    @property
    def partial_resonance(self) -> bool:
        """Some channels agree while others refute: the interesting case."""
        return bool(self.agree) and bool(self.disagree)


def verdict(b1: Braid, b2: Braid) -> Certificate:
    """Decide ``b1 = b2`` and report which channels resonate."""
    if b1.strand_count != b2.strand_count:
        raise ValueError("braids on different strand counts")
    r1, r2 = reading(b1), reading(b2)
    agree = tuple(c for c in CHANNELS if same_reading(c, r1[c], r2[c]))
    disagree = tuple(c for c in CHANNELS if not same_reading(c, r1[c], r2[c]))
    proved = left_normal_form(b1) == left_normal_form(b2)
    return Certificate("PROVED" if proved else "REFUTED", agree, disagree)


def defect(b1: Braid, b2: Braid) -> Braid:
    """The defect ``b2⁻¹ · b1`` of the claim ``b1 = b2``."""
    return b2.inverse() * b1


def heal(b1: Braid, b2: Braid) -> Braid:
    """``b2 · defect`` — always equal to ``b1`` in the braid group."""
    return b2 * defect(b1, b2)


# --------------------------------------------------------------------------
# Certified chunk scheduler (``QBX/Formal/MultiProver/Scheduler.lean``)
# --------------------------------------------------------------------------
#
# The homomorphic readings (permutation, writhe, exact Burau matrix) are
# computed chunk by chunk and combined by a balanced reduction tree.  Lean
# proves that *any* chunking and *any* reduction schedule give the reading of
# the whole word (``schedule_correct``; the balanced tree needs ⌈log₂ k⌉
# rounds for k chunks, ``balanced_schedule_depth``).  The non-homomorphic
# readings (Garside normal form, linking spectrum, resonance set, Jones
# values) are functions of the braid element and are computed once from the
# combined braid (``channels_agree_of_summary``).


@dataclass(frozen=True)
class ChunkReading:
    """Summary of one chunk: permutation, writhe and exact Burau matrix (``Summary``)."""

    strand_count: int
    perm: Tuple[int, ...]  # same convention as ``invariants.permutation``
    writhe: int
    burau: Tuple[Tuple[object, ...], ...]  # rows of ``Laurent`` entries


def chunk_reading(strand_count: int, word) -> ChunkReading:
    """The summary of a chunk (``summary``)."""
    from qbx_ir.algebra.invariants import writhe as _writhe

    b = Braid(strand_count=strand_count, word=tuple(word),
              strands=Braid.identity(strand_count).strands)
    return ChunkReading(
        strand_count,
        tuple(permutation(b)),
        _writhe(b),
        tuple(tuple(row) for row in burau_matrix(b)),
    )


def merge_readings(a: ChunkReading, b: ChunkReading) -> ChunkReading:
    """Combine the summaries of two consecutive chunks (the monoid product of ``Summary``)."""
    from qbx_ir.algebra.laurent import matmul

    if a.strand_count != b.strand_count:
        raise ValueError("chunks on different strand counts")
    perm = tuple(a.perm[p - 1] for p in b.perm)
    mat = matmul([list(r) for r in a.burau], [list(r) for r in b.burau])
    return ChunkReading(a.strand_count, perm, a.writhe + b.writhe,
                        tuple(tuple(r) for r in mat))


def balanced_reduce(parts: List[ChunkReading]) -> ChunkReading:
    """The balanced schedule (``balanced``): split in half, recurse, merge."""
    if not parts:
        raise ValueError("no chunks")
    if len(parts) == 1:
        return parts[0]
    mid = len(parts) // 2
    return merge_readings(balanced_reduce(parts[:mid]), balanced_reduce(parts[mid:]))


def split_word(word, chunk_size: int) -> List[tuple]:
    """Cut a word into consecutive chunks of at most ``chunk_size`` letters (at least one chunk)."""
    word = tuple(word)
    if chunk_size < 1:
        raise ValueError("chunk_size must be ≥ 1")
    return [word[i:i + chunk_size] for i in range(0, len(word), chunk_size)] or [()]


def scheduled_reading(braid: Braid, chunk_size: int = 64) -> ChunkReading:
    """Permutation, writhe and Burau matrix of ``braid`` by chunked map–reduce
    (``schedule_correct``: equal to the direct readings)."""
    parts = [chunk_reading(braid.strand_count, c) for c in split_word(braid.word, chunk_size)]
    return balanced_reduce(parts)


def scheduled_anchor_reading(braid: Braid, chunk_size: int = 64):
    """The anchor channel computed by the chunk scheduler (same format as ``anchor_reading``)."""
    s = scheduled_reading(braid, chunk_size)
    return tuple(
        tuple(tuple(sorted(entry.to_int_dict().items())) for entry in row) for row in s.burau
    )
