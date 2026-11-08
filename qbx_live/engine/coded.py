"""Polynomial-coded products of representation-matrix blocks over ``n`` workers.

Task: given ``k`` blocks ``A₀, …, A_{k−1}`` (for example reduced Burau matrices of ``k``
sub-words) and a matrix ``B``, compute every ``A_e · B``.  Encoding: worker ``j`` receives
``P(x_j) = Σ_e A_e x_jᵉ`` and returns ``P(x_j) · B = Σ_e (A_e B) x_jᵉ``, a matrix polynomial
with ``k`` coefficients.  The master decodes from the **first ``k`` answers to arrive** by
Lagrange interpolation; the remaining ``n − k`` workers may be slow or dead.

Seal lane S5 (``QBX/Formal/Seal/CodedDecoding.lean``): ``coded_decode_of_workers`` — any
``k`` answers at distinct points recover the coefficients exactly; ``coded_insufficient`` —
``k − 1`` answers never determine them.  The exact path below uses
:func:`qbx_engine.seal.coded_decode` and is therefore exact; the floating-point path does the
same arithmetic in ``float`` and :func:`float_error` measures how far it drifts from the exact
answer (Vandermonde systems are ill-conditioned, so the drift grows with ``k`` and with the
spread of the points).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import List, Optional, Sequence, Tuple

from qbx_engine import seal

Matrix = List[List[Fraction]]


def mat_mul(A: Sequence[Sequence], B: Sequence[Sequence]) -> List[List]:
    return [[sum(A[i][t] * B[t][j] for t in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def default_points(n: int) -> List[Fraction]:
    """Distinct evaluation points ``0, 1, −1, 2, −2, …`` (small magnitudes keep floats sane)."""
    pts, m = [Fraction(0)], 1
    while len(pts) < n:
        pts.append(Fraction(m))
        if len(pts) < n:
            pts.append(Fraction(-m))
        m += 1
    return pts


@dataclass
class CodedRun:
    products: List[Matrix]        # decoded A_e · B, exact
    used_workers: List[int]       # the k workers whose answers were used (arrival order)
    finish_time: float            # arrival time of the k-th answer (the run's latency)
    uncoded_time: Optional[float]  # latency without coding: wait for the k block workers


def worker_answer(blocks: Sequence[Matrix], B: Matrix, x: Fraction) -> Matrix:
    """What worker ``j`` computes: ``P(x) · B``."""
    return mat_mul(seal.coded_encode(blocks, x), B)


def coded_product(blocks: Sequence[Matrix], B: Matrix, n: int,
                  delays: Sequence[Optional[float]],
                  points: Optional[Sequence[Fraction]] = None) -> CodedRun:
    """Run the coded product with ``n`` workers; ``delays[j]`` is worker ``j``'s answer time,
    ``None`` for a worker that never answers.  Raises ``ValueError`` if fewer than ``k``
    workers answer (S5: ``k − 1`` answers are never enough)."""
    k = len(blocks)
    if not k <= n == len(delays):
        raise ValueError("need k ≤ n and one delay per worker")
    xs = list(points) if points is not None else default_points(n)
    alive = sorted((d, j) for j, d in enumerate(delays) if d is not None)
    if len(alive) < k:
        raise ValueError(f"only {len(alive)} of the k = {k} needed answers arrived")
    first = alive[:k]
    responses = [(xs[j], worker_answer(blocks, B, xs[j])) for _, j in first]
    products = seal.coded_decode(responses, k)
    # Uncoded baseline: block e goes to worker e and must arrive.
    block_delays = list(delays[:k])
    uncoded = None if any(d is None for d in block_delays) else max(block_delays)
    return CodedRun(products, [j for _, j in first], first[-1][0], uncoded)


def float_decode(responses: Sequence[Tuple[float, Sequence[Sequence[float]]]], k: int
                 ) -> List[List[List[float]]]:
    """Lagrange decoding in floating point (same algorithm as the exact decoder)."""
    pts = list(responses)[:k]
    xs = [float(x) for x, _ in pts]
    rows, cols = len(pts[0][1]), len(pts[0][1][0])
    out = [[[0.0] * cols for _ in range(rows)] for _ in range(k)]
    for j, (xj, (_, Mj)) in enumerate(zip(xs, pts)):
        poly, denom = [1.0], 1.0
        for m, xm in enumerate(xs):
            if m == j:
                continue
            poly = [0.0] + poly
            for e in range(len(poly) - 1):
                poly[e] -= xm * poly[e + 1]
            denom *= xj - xm
        for e in range(k):
            c = poly[e] / denom
            for r in range(rows):
                for s in range(cols):
                    out[e][r][s] += c * float(Mj[r][s])
    return out


def float_error(blocks: Sequence[Matrix], B: Matrix, workers: Sequence[int],
                points: Optional[Sequence[Fraction]] = None) -> float:
    """Largest entrywise error of the floating-point decoder against the exact products, when
    the answers of ``workers`` (``k`` of them) are used."""
    k = len(blocks)
    xs = list(points) if points is not None else default_points(max(workers) + 1)
    fl = [(float(xs[j]), [[float(v) for v in row] for row in worker_answer(blocks, B, xs[j])])
          for j in workers]
    approx = float_decode(fl, k)
    exact = [mat_mul(A, B) for A in blocks]
    return max(abs(approx[e][r][s] - float(exact[e][r][s]))
               for e in range(k) for r in range(len(exact[e])) for s in range(len(exact[e][0])))


def burau_blocks(words: Sequence[Sequence[Tuple[int, bool]]], n_strands: int,
                 t: Fraction = Fraction(2)) -> List[Matrix]:
    """Reduced Burau matrices of sub-words at ``t`` — the representation-matrix blocks of
    family B/C."""
    return [seal.burau(w, n_strands, t) for w in words]
