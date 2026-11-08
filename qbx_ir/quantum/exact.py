"""
Exact (integer / rational) quantum representation matrices.

The numerical representation of :mod:`qbx_ir.quantum.representation` works in
floating point, so :class:`qbx_ir.core.equality.EqualityKind.REPRESENTATION`
can only compare up to a tolerance.  For the ``U_q(sl_2)`` R-matrix
(:class:`qbx_ir.quantum.r_matrix.SL2RMatrix`) at a *rational* parameter
``q = p / r`` every entry of ``ρ(B)`` is rational, and this module computes it
exactly, using integers only:

* each letter is multiplied by the scaled R-matrix ``p r · Ř`` (or
  ``p r · Ř⁻¹``), whose entries are integers (:func:`scaled_generators`);
* the denominator is ``(p r)^{length}``;
* the fraction is reduced: everything is divided by ``gcd(denominator,
  entries)`` with the sign that makes the denominator positive.

The result (:class:`ExactMatrix`) is the unique reduced representation of the
rational matrix, so two braids have equal ``ρ`` iff their exact matrices are
equal as values (Lean: ``QBX/Formal/BraidRepCert.lean``, ``repCert_eq_iff``).

Convention: the matrix of a word is the product in word order,
``ρ(g_1 ⋯ g_k) = ρ(g_1) ⋯ ρ(g_k)`` (as
:func:`qbx_ir.quantum.representation.representation_alt`, and as the Lean
``Word.repOp``).  Basis states ``s = (s_1, …, s_n)`` are indexed by
``Σ s_m 2^{n-m}`` (first tensor factor most significant), as ``numpy.kron``.
Matrices are flattened row-major.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence, Tuple

from qbx_ir.core.braid import Braid

Table = Tuple[Tuple[int, ...], ...]


@dataclass(frozen=True)
class ExactMatrix:
    """A reduced rational matrix ``numerators / denominator`` (``denominator > 0``,
    ``gcd(denominator, numerators) = 1``), flattened row-major."""

    dimension: int
    numerators: Tuple[int, ...]
    denominator: int

    def entry(self, row: int, col: int) -> Fraction:
        return Fraction(self.numerators[row * self.dimension + col], self.denominator)

    def to_fractions(self):
        d = self.dimension
        return [[self.entry(i, j) for j in range(d)] for i in range(d)]


def parameter_problem(q_num: int, q_den: int) -> bool:
    """True unless ``q_num / q_den`` is a non-zero rational in lowest terms with
    ``q_den > 0``."""
    return not (isinstance(q_num, int) and isinstance(q_den, int)
                and q_den > 0 and q_num != 0 and math.gcd(q_num, q_den) == 1)


def scaled_generators(q_num: int, q_den: int) -> Tuple[Table, Table]:
    """``p r · Ř`` and ``p r · Ř⁻¹`` for ``q = p / r`` as 4×4 integer tables,
    ``table[a*2+b][c*2+e] = ⟨a b| · |c e⟩`` (Lean: ``sl2Scaled``, ``sl2ScaledInv``)."""
    p, r = q_num, q_den
    pp, rr, pr = p * p, r * r, p * r
    pos = ((pp, 0, 0, 0),
           (0, 0, pr, 0),
           (0, pr, pp - rr, 0),
           (0, 0, 0, pp))
    neg = ((rr, 0, 0, 0),
           (0, -(pp - rr), pr, 0),
           (0, pr, 0, 0),
           (0, 0, 0, rr))
    return pos, neg


def reduce_fraction(numerators: Sequence[int], denominator: int) -> Tuple[Tuple[int, ...], int]:
    """Divide by ``± gcd(denominator, numerators)`` so that the denominator is positive
    (Lean: ``reduceCert``); ``denominator`` must be non-zero."""
    g = math.gcd(denominator, *numerators)
    if denominator < 0:
        g = -g
    return tuple(x // g for x in numerators), denominator // g


def scaled_product(strand_count: int, word: Sequence[int], q_num: int,
                   q_den: int) -> Tuple[int, ...]:
    """The integer matrix ``Π (p r · ρ(g))`` in word order, flattened row-major
    (Lean: ``Word.scaledMat``)."""
    n = strand_count
    dim = 2 ** n
    pos, neg = scaled_generators(q_num, q_den)
    u = [1 if x == y else 0 for x in range(dim) for y in range(dim)]
    for g in word:
        i = abs(g)
        table = pos if g > 0 else neg
        w1 = 2 ** (n - i)
        w2 = 2 ** (n - i - 1)
        new = [0] * (dim * dim)
        for t in range(dim):
            c = (t // w1) % 2
            e = (t // w2) % 2
            base = t - c * w1 - e * w2
            col = c * 2 + e
            terms = [(base + a * w1 + b * w2, table[a * 2 + b][col])
                     for a in (0, 1) for b in (0, 1) if table[a * 2 + b][col] != 0]
            for x in range(dim):
                row = x * dim
                new[row + t] = sum(u[row + s] * coef for s, coef in terms)
        u = new
    return tuple(u)


def exact_sl2_matrix(strand_count: int, word: Sequence[int], q_num: int = 2,
                     q_den: int = 1) -> ExactMatrix:
    """The exact ``U_q(sl_2)`` matrix of the braid ``(strand_count, word)`` at
    ``q = q_num / q_den`` (Lean: ``Word.repCert``)."""
    if parameter_problem(q_num, q_den):
        raise ValueError("q must be a non-zero rational q_num / q_den in lowest terms, q_den > 0")
    nums = scaled_product(strand_count, word, q_num, q_den)
    den = (q_num * q_den) ** len(word)
    nums, den = reduce_fraction(nums, den)
    return ExactMatrix(2 ** strand_count, nums, den)


class ExactSL2Representation:
    """``representation_fn`` for :func:`qbx_ir.core.equality.check_equality` with
    ``EqualityKind.REPRESENTATION``: returns the :class:`ExactMatrix` of a braid, so the
    comparison is exact (no tolerance)."""

    def __init__(self, q: Fraction | int = 2):
        q = Fraction(q)
        if q == 0:
            raise ValueError("q must be non-zero")
        self.q = q

    def __call__(self, braid: Braid) -> ExactMatrix:
        return exact_sl2_matrix(braid.strand_count, braid.short_form(),
                                self.q.numerator, self.q.denominator)

    def __repr__(self) -> str:
        return f"ExactSL2Representation(q={self.q})"


__all__ = [
    "ExactMatrix",
    "ExactSL2Representation",
    "exact_sl2_matrix",
    "parameter_problem",
    "reduce_fraction",
    "scaled_generators",
    "scaled_product",
]
