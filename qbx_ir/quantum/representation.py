"""
The quantum representation ρ: B_n → GL(V^⊗n).

Each generator σ_i is mapped to the operator

    ρ(σ_i) = I^{⊗(i-1)} ⊗ Ř ⊗ I^{⊗(n-i-1)}

and a braid word (read bottom → top) to the product of these operators,
the first generator acting first: ρ(g_1 g_2 ⋯ g_k) = ρ(g_k) ⋯ ρ(g_1).
The Lean library proves (``QBX.Formal.braidRep``) that for any invertible
Ř satisfying the Yang–Baxter equation this assignment respects all braid
relations, for every n.
"""

from __future__ import annotations

import numpy as np

from qbx_ir.core.braid import Braid
from qbx_ir.quantum.r_matrix import RMatrix


def embed_r(R: np.ndarray, dim: int, i: int, n: int) -> np.ndarray:
    """
    Embed the (dim² × dim²) matrix R at positions (i, i+1) of an n-fold
    tensor product. Both i and n are 1-indexed for consistency with the
    braid convention.
    """
    if not (1 <= i < n):
        raise ValueError(f"Invalid position i={i} for n={n}")
    left = np.eye(dim ** (i - 1), dtype=R.dtype)
    right = np.eye(dim ** (n - i - 1), dtype=R.dtype)
    return np.kron(np.kron(left, R), right)


def representation(braid: Braid, R: RMatrix) -> np.ndarray:
    """
    Compute the quantum operator ρ(B) for a braid B and R-matrix R.

    Returns a (dim^n, dim^n) numpy array.
    """
    n = braid.strand_count
    d = R.dim
    R_mat = R.matrix()
    R_inv = R.inverse_matrix()
    U = np.eye(d ** n, dtype=np.complex128)
    for g in braid.word:
        op = embed_r(R_mat if g.sign == 1 else R_inv, d, g.index, n)
        U = op @ U
    return U


def representation_alt(braid: Braid, R: RMatrix) -> np.ndarray:
    """
    Alternative convention: ρ'(g_1 ⋯ g_k) = ρ(g_1) ⋯ ρ(g_k)
    (matrix product in word order).
    """
    n = braid.strand_count
    d = R.dim
    R_mat = R.matrix()
    R_inv = R.inverse_matrix()
    U = np.eye(d ** n, dtype=np.complex128)
    for g in braid.word:
        op = embed_r(R_mat if g.sign == 1 else R_inv, d, g.index, n)
        U = U @ op
    return U


def quantum_trace(braid: Braid, q: complex) -> complex:
    """
    Enhanced (Markov) trace Tr(μ^{⊗n} ρ(B)) for the SL2 Ř at parameter q,
    with μ = diag(q⁻¹, q).
    """
    from qbx_ir.quantum.r_matrix import SL2RMatrix

    U = representation(braid, SL2RMatrix(q))
    mu = np.diag([1.0 / complex(q), complex(q)])
    M = np.array([[1.0]], dtype=np.complex128)
    for _ in range(braid.strand_count):
        M = np.kron(M, mu)
    return complex(np.trace(M @ U))


def jones_from_quantum_trace(braid: Braid, q: complex) -> complex:
    """
    Jones polynomial of the closure evaluated through the quantum (L5) layer:

        V(t)|_{t^{1/2} = −q⁻¹} = q^{−2w} · Tr(μ^{⊗n} ρ(B)) / (q + q⁻¹)

    This ties the quantum view (L5) to the invariant view (L6); the tests
    check it against the Kauffman-bracket state sum.
    """
    from qbx_ir.algebra.invariants import writhe

    q = complex(q)
    return q ** (-2 * writhe(braid)) * quantum_trace(braid, q) / (q + 1.0 / q)
