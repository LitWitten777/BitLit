"""
Numerical verification (mode V2, QBX.md §24) of braid equalities via the
quantum representation.  The symbolic/formal counterpart (mode V3) lives in
the Lean library ``QBX/Formal``.
"""

from __future__ import annotations

from typing import Tuple

import numpy as np

from qbx_ir.core.braid import Braid
from qbx_ir.quantum.r_matrix import RMatrix
from qbx_ir.quantum.representation import representation


def verify_yang_baxter(R: RMatrix, tol: float = 1e-9) -> Tuple[bool, float]:
    """
    Verify the Yang–Baxter equation for Ř on V^⊗3, i.e.
    ρ(σ_1 σ_2 σ_1) = ρ(σ_2 σ_1 σ_2).  Returns (holds, max_residual).
    """
    B1 = Braid.from_short_form(3, [1, 2, 1])
    B2 = Braid.from_short_form(3, [2, 1, 2])
    residual = float(np.abs(representation(B1, R) - representation(B2, R)).max())
    return (residual < tol, residual)


def verify_braid_relations(R: RMatrix, n: int = 4, tol: float = 1e-9) -> Tuple[bool, float]:
    """
    Check every defining relation of B_n (braid, far-commutation and
    σ_i σ_i⁻¹ = 1) in the representation.  Returns (holds, max_residual).
    """
    worst = 0.0
    pairs = []
    for i in range(1, n):
        pairs.append(([i, -i], []))
        if i + 1 < n:
            pairs.append(([i, i + 1, i], [i + 1, i, i + 1]))
        for j in range(i + 2, n):
            pairs.append(([i, j], [j, i]))
    for lhs, rhs in pairs:
        ok, res = verify_braid_equality(
            Braid.from_short_form(n, lhs), Braid.from_short_form(n, rhs), R, tol
        )
        worst = max(worst, res)
    return (worst < tol, worst)


def verify_braid_equality(
    b1: Braid,
    b2: Braid,
    R: RMatrix,
    tol: float = 1e-9,
) -> Tuple[bool, float]:
    """Verify ρ(B1) = ρ(B2) for a given Ř."""
    if b1.strand_count != b2.strand_count:
        return (False, float("inf"))
    u1 = representation(b1, R)
    u2 = representation(b2, R)
    residual = float(np.abs(u1 - u2).max())
    return (residual < tol, residual)


def verify_unitarity(R: RMatrix, tol: float = 1e-9) -> Tuple[bool, float]:
    """Check Ř†Ř = I.  (The SL2 Ř is unitary only for |q| = 1, q = ±1 ...)."""
    R_mat = R.matrix()
    prod = R_mat.conj().T @ R_mat
    residual = float(np.abs(prod - np.eye(R_mat.shape[0])).max())
    return (residual < tol, residual)
