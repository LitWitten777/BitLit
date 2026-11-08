"""
R-matrix implementations (braided form Ř = P∘R).

An R-matrix here is a linear operator Ř: V ⊗ V → V ⊗ V satisfying the
braided Yang–Baxter equation

    (Ř ⊗ I)(I ⊗ Ř)(Ř ⊗ I) = (I ⊗ Ř)(Ř ⊗ I)(I ⊗ Ř)

so that σ_i ↦ I^{⊗(i-1)} ⊗ Ř ⊗ I^{⊗(n-i-1)} is a representation of B_n.

Provided:

- SL2RMatrix:          the U_q(sl_2) spin-1/2 Ř (V = ℂ²), Hecke relation
                       (Ř − q)(Ř + q⁻¹) = 0; its closure trace gives the
                       Jones polynomial.
- TwistedSwapRMatrix:  Ř(e_a ⊗ e_b) = c_{ab} e_b ⊗ e_a for any non-zero
                       table c; always a solution (the Lean library proves
                       this for every table).  The pre-0.2 "SL2RMatrix"
                       (√q, 1, 1, 1/√q) is the special case
                       ``TwistedSwapRMatrix.legacy_sl2(q)``.
- PermutationRMatrix:  the flip Ř(x ⊗ y) = y ⊗ x (all c_{ab} = 1).

The Lean library ``QBX/Formal/YangBaxter.lean`` proves the Yang–Baxter
equation for the SL2 and twisted-swap families symbolically.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Sequence

import numpy as np


class RMatrix(ABC):
    """Abstract base for braided R-matrices."""

    @property
    @abstractmethod
    def dim(self) -> int:
        """Dimension of V (so Ř is dim² × dim²)."""

    @abstractmethod
    def matrix(self) -> np.ndarray:
        """Ř as a (dim², dim²) numpy array."""

    def inverse_matrix(self) -> np.ndarray:
        """Ř⁻¹ (subclasses may override with a closed form)."""
        return np.linalg.inv(self.matrix())

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}(dim={self.dim})"


class SL2RMatrix(RMatrix):
    """
    The braided spin-1/2 R-matrix of U_q(sl_2).

    Basis (V⊗V): |00>, |01>, |10>, |11>

        Ř = [[q, 0, 0,        0],
             [0, 0, 1,        0],
             [0, 1, q − q⁻¹,  0],
             [0, 0, 0,        q]]

    Ř satisfies YBE for every q ≠ 0 and the Hecke relation
    (Ř − q)(Ř + q⁻¹) = 0, so Ř⁻¹ = Ř − (q − q⁻¹)·I.
    """

    def __init__(self, q: complex = 2.0):
        if q == 0:
            raise ValueError("q must be non-zero")
        self.q = complex(q)

    @property
    def dim(self) -> int:
        return 2

    def matrix(self) -> np.ndarray:
        q = self.q
        R = np.zeros((4, 4), dtype=np.complex128)
        R[0, 0] = q
        R[1, 2] = 1.0
        R[2, 1] = 1.0
        R[2, 2] = q - 1.0 / q
        R[3, 3] = q
        return R

    def inverse_matrix(self) -> np.ndarray:
        q = self.q
        return self.matrix() - (q - 1.0 / q) * np.eye(4, dtype=np.complex128)

    def __repr__(self) -> str:
        return f"SL2RMatrix(q={self.q})"


class TwistedSwapRMatrix(RMatrix):
    """
    Ř(e_a ⊗ e_b) = c[a][b] · e_b ⊗ e_a  (a "diagonal-twisted flip").

    Every such Ř with non-zero entries satisfies the Yang–Baxter equation:
    both sides send e_a⊗e_b⊗e_c to c_ab c_ac c_bc · e_c⊗e_b⊗e_a.
    """

    def __init__(self, table: Sequence[Sequence[complex]]):
        c = np.asarray(table, dtype=np.complex128)
        if c.ndim != 2 or c.shape[0] != c.shape[1]:
            raise ValueError("table must be square")
        if np.any(c == 0):
            raise ValueError("table entries must be non-zero (invertibility)")
        self.table = c

    @classmethod
    def legacy_sl2(cls, q: complex = 2.0) -> "TwistedSwapRMatrix":
        """The matrix shipped as 'SL2RMatrix' in QBX-IR 0.1."""
        s = np.sqrt(complex(q))
        return cls([[s, 1.0], [1.0, 1.0 / s]])

    @property
    def dim(self) -> int:
        return self.table.shape[0]

    def matrix(self) -> np.ndarray:
        d = self.dim
        R = np.zeros((d * d, d * d), dtype=np.complex128)
        for a in range(d):
            for b in range(d):
                R[b * d + a, a * d + b] = self.table[a, b]
        return R


class PermutationRMatrix(TwistedSwapRMatrix):
    """The flip Ř(x ⊗ y) = y ⊗ x: represents B_n through S_n."""

    def __init__(self, dim: int = 2):
        super().__init__(np.ones((dim, dim)))

    def inverse_matrix(self) -> np.ndarray:
        return self.matrix()


def hecke_residual(R: SL2RMatrix) -> float:
    """max |(Ř − q)(Ř + q⁻¹)|."""
    M = R.matrix()
    eye = np.eye(4)
    return float(np.abs((M - R.q * eye) @ (M + eye / R.q)).max())


__all__ = [
    "RMatrix",
    "SL2RMatrix",
    "TwistedSwapRMatrix",
    "PermutationRMatrix",
    "hecke_residual",
]
