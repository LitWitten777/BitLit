"""``SU(2)_k`` anyons: fusion rules, F-symbols (quantum 6j) and R-symbols.

Labels are spins ``j ∈ {0, 1/2, …, k/2}``; internally a label is the integer
``2j`` (``0 … k``), and ``label_name(2j)`` gives ``"0"``, ``"1/2"``, ``"1"``, ….

* Fusion (truncated Clebsch–Gordan):
  ``j1 ⊗ j2 = |j1 − j2|, |j1 − j2| + 1, …, min(j1 + j2, k − j1 − j2)``.
* Quantum integers at ``q = e^{iπ/(k+2)}``: ``[n] = sin(nπ/(k+2)) / sin(π/(k+2))``
  (real and positive for ``0 < n < k + 2``).
* F-symbols: ``[F^{abc}_d]_{ef} = (−1)^{a+b+c+d} √([2e+1][2f+1]) {a b e; c d f}_q``
  with the Racah–Wigner quantum 6j symbol; real orthogonal matrices.
* R-symbols: ``R^{ab}_c = (−1)^{c−a−b} q^{c(c+1) − a(a+1) − b(b+1)}``.
* Topological spin ``θ_j = q^{2 j (j+1)} = e^{2πi j(j+1)/(k+2)}``.

Conventions for F and R are those of ``qbx_ir.anyon.AnyonModel`` and
``QBX/Formal/AnyonCoherence.lean``: ``F(a, b, c, d, e, f) = [F^{abc}_d]_{ef}``
(``e`` the intermediate of ``a ⊗ b``, ``f`` of ``b ⊗ c``),
``R(a, b, c) = R^{ab}_c``; ``pentagon_residual`` and ``hexagon_residual``
(``coherence.py``) check exactly the equations of
``tests/qbx_ir/test_anyon_coherence.py``.

Origin: Phase D work stream D6 (``foundation/phase_d/D6_codes_anyons/``),
integrated here on 2026-10-04.  ``su2k_model(k)`` packages the data as a
``qbx_ir.anyon.AnyonModel``.
"""
from __future__ import annotations

import cmath
import itertools
import math
from fractions import Fraction
from functools import lru_cache

__all__ = ["SU2k", "label_name", "su2k_model"]


def label_name(two_j: int) -> str:
    return str(Fraction(two_j, 2))


class SU2k:
    """The ``SU(2)_k`` data at ``q = e^{iπ/(k+2)}`` (or its conjugate if
    ``conjugate=True``)."""

    def __init__(self, k: int, conjugate: bool = False):
        if k < 1:
            raise ValueError("k >= 1")
        self.k = k
        self.conjugate = conjugate
        self.labels = tuple(range(k + 1))          # 2j
        self.vacuum = 0

    # ---- quantum numbers ---------------------------------------------------

    def qint(self, n: int) -> float:
        r = self.k + 2
        return math.sin(n * math.pi / r) / math.sin(math.pi / r)

    @lru_cache(maxsize=None)
    def qfact(self, n: int) -> float:
        out = 1.0
        for i in range(2, n + 1):
            out *= self.qint(i)
        return out

    def qdim(self, a: int) -> float:
        return self.qint(a + 1)

    def total_dimension(self) -> float:
        return math.sqrt(sum(self.qdim(a) ** 2 for a in self.labels))

    # ---- fusion -----------------------------------------------------------

    def admissible(self, a: int, b: int, c: int) -> bool:
        """``c ∈ a ⊗ b`` (all labels doubled)."""
        return (abs(a - b) <= c <= a + b and (a + b + c) % 2 == 0
                and a + b + c <= 2 * self.k)

    def fuse(self, a: int, b: int) -> list[int]:
        return [c for c in self.labels if self.admissible(a, b, c)]

    # ---- 6j symbols ---------------------------------------------------------

    def _delta(self, a: int, b: int, c: int) -> float:
        f = self.qfact
        return math.sqrt(f((a + b - c) // 2) * f((a - b + c) // 2)
                         * f((-a + b + c) // 2) / f((a + b + c) // 2 + 1))

    def sixj(self, j1: int, j2: int, j12: int, j3: int, j: int, j23: int) -> float:
        """Racah–Wigner quantum 6j symbol ``{j1 j2 j12; j3 j j23}_q``
        (labels doubled); 0 unless all four triangles are admissible."""
        if not (self.admissible(j1, j2, j12) and self.admissible(j12, j3, j)
                and self.admissible(j2, j3, j23) and self.admissible(j1, j23, j)):
            return 0.0
        f = self.qfact
        a1 = (j1 + j2 + j12) // 2
        a2 = (j12 + j3 + j) // 2
        a3 = (j2 + j3 + j23) // 2
        a4 = (j1 + j23 + j) // 2
        b1 = (j1 + j2 + j3 + j) // 2
        b2 = (j1 + j3 + j12 + j23) // 2
        b3 = (j2 + j + j12 + j23) // 2
        total = 0.0
        for z in range(max(a1, a2, a3, a4), min(b1, b2, b3) + 1):
            total += (-1) ** z * f(z + 1) / (
                f(z - a1) * f(z - a2) * f(z - a3) * f(z - a4)
                * f(b1 - z) * f(b2 - z) * f(b3 - z))
        return (self._delta(j1, j2, j12) * self._delta(j12, j3, j)
                * self._delta(j2, j3, j23) * self._delta(j1, j23, j) * total)

    # ---- F and R --------------------------------------------------------------

    def F(self, a: int, b: int, c: int, d: int, e: int, f: int) -> float:
        """``[F^{abc}_d]_{ef}``, zero on non-admissible vertices."""
        if not (self.admissible(a, b, e) and self.admissible(e, c, d)
                and self.admissible(b, c, f) and self.admissible(a, f, d)):
            return 0.0
        sign = (-1) ** ((a + b + c + d) // 2)
        return sign * math.sqrt(self.qint(e + 1) * self.qint(f + 1)) * \
            self.sixj(a, b, e, c, d, f)

    def F_matrix(self, a: int, b: int, c: int, d: int) -> list[list[float]]:
        left = [e for e in self.labels
                if self.admissible(a, b, e) and self.admissible(e, c, d)]
        right = [f for f in self.labels
                 if self.admissible(b, c, f) and self.admissible(a, f, d)]
        return [[self.F(a, b, c, d, e, f) for f in right] for e in left]

    def _qpow(self, x) -> complex:
        s = -1 if self.conjugate else 1
        return cmath.exp(s * 1j * math.pi * float(x) / (self.k + 2))

    @staticmethod
    def _casimir(a: int) -> Fraction:
        return Fraction(a, 2) * (Fraction(a, 2) + 1)

    def R(self, a: int, b: int, c: int) -> complex:
        """``R^{ab}_c``, zero if ``c ∉ a ⊗ b``."""
        if not self.admissible(a, b, c):
            return 0.0
        sign = -1 if ((c - a - b) // 2) % 2 else 1
        return sign * self._qpow(self._casimir(c) - self._casimir(a) - self._casimir(b))

    def theta(self, a: int) -> complex:
        """Topological spin ``θ_a = q^{2 j(j+1)}`` (``a`` = 2j)."""
        return self._qpow(2 * self._casimir(a))

    # ---- array form and coherence ------------------------------------------------

    def data(self):
        """The model as ``coherence.AnyonData`` (labels ``0 … k`` = 2j)."""
        import numpy as np
        from .coherence import AnyonData
        L = len(self.labels)
        N = np.zeros((L,) * 3, dtype=int)
        R = np.zeros((L,) * 3, dtype=complex)
        for a, b, c in itertools.product(self.labels, repeat=3):
            if self.admissible(a, b, c):
                N[a, b, c] = 1
                R[a, b, c] = self.R(a, b, c)
        F = np.zeros((L,) * 6, dtype=complex)
        for idx in itertools.product(self.labels, repeat=6):
            F[idx] = self.F(*idx)
        d = np.array([self.qdim(a) for a in self.labels])
        return AnyonData(tuple(label_name(a) for a in self.labels), N, F, R, d)

    def pentagon_residual(self) -> float:
        from .coherence import pentagon_residual
        return pentagon_residual(self.data())

    def hexagon_residual(self, reverse: bool = False) -> float:
        from .coherence import hexagon_residual
        return hexagon_residual(self.data(), reverse)

    def unitarity_residual(self) -> float:
        from .coherence import unitarity_residual
        return unitarity_residual(self.data())


def su2k_model(k: int, conjugate: bool = False):
    """``SU(2)_k`` as a ``qbx_ir.anyon.AnyonModel`` (labels ``"0"``, ``"1/2"``, …)."""
    import numpy as np
    from .model import AnyonModel
    s = SU2k(k, conjugate=conjugate)
    names = tuple(label_name(a) for a in s.labels)
    index = {name: a for a, name in zip(s.labels, names)}
    fusion = {(names[a], names[b]): frozenset(names[c] for c in s.fuse(a, b))
              for a in s.labels[1:] for b in s.labels[1:]}
    r_symbols = {(names[a], names[b], names[c]): s.R(a, b, c)
                 for a in s.labels[1:] for b in s.labels[1:] for c in s.fuse(a, b)}

    def f_function(a, b, c, d):
        return np.asarray(s.F_matrix(index[a], index[b], index[c], index[d]),
                          dtype=np.complex128)

    return AnyonModel(
        name=f"SU(2)_{k}",
        labels=names,
        vacuum=names[0],
        fusion=fusion,
        quantum_dims={names[a]: s.qdim(a) for a in s.labels},
        r_symbols=r_symbols,
        f_function=f_function,
    )
