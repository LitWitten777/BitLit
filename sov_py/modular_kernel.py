"""
Modular Kernel & Non-Invertibility of Sedenion Zero Divisors (HYP-125, OP-052).

Formalizes and computationally verifies:
1. Left and right multiplication integer matrices M(V) for sedenion cross-octet zero divisors.
2. Universal Smith Normal Form (SNF) invariant factors: (1^8, 2^4, 0^4).
3. Modulo 2 reduction: rank = 8, nullity = 8 over F_2.
4. Modulo 2^16 action: exact kernel size |ker(M mod 2^16)| = 2^68, comprising a rank-4 free submodule
   and a rank-4 2-torsion submodule.
5. Determinant det(M) = 0, unconditionally proving non-invertibility over Z, Q, R, and Z_{2^16}.
6. Unconditional information-theoretic barrier against backward meet-in-the-middle path inversion:
   each step S_{t+1} = V * S_t mod 2^16 loses exactly 68 bits of preimage entropy.
"""

from __future__ import annotations

import math
from typing import Any

import numpy as np
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form

from .cd_algebra import build_cd_multiplication_table
from .graph import get_cached_annihilation_graph

# Precomputed Cayley-Dickson 16x16 sign table
_SIGN_16, _ = build_cd_multiplication_table(16)


def sedenion_left_mult_matrix(vi: int, vj: int, vs1: int, vs2: int) -> np.ndarray:
    """
    Constructs the 16x16 integer representation matrix M of left multiplication L_V
    for the cross-octet zero divisor V = vs1 * e_{vi} + vs2 * e_{8+vj}.

    L_V(e_k) = vs1 * (e_{vi} * e_k) + vs2 * (e_{8+vj} * e_k)
             = vs1 * sign(vi, k) * e_{vi ^ k} + vs2 * sign(8+vj, k) * e_{(8+vj) ^ k}
    """
    M = np.zeros((16, 16), dtype=int)
    for k in range(16):
        m1 = vi ^ k
        M[m1, k] += vs1 * _SIGN_16[vi, k]
        m2 = (8 + vj) ^ k
        M[m2, k] += vs2 * _SIGN_16[8 + vj, k]
    return M


def sedenion_right_mult_matrix(vi: int, vj: int, vs1: int, vs2: int) -> np.ndarray:
    """
    Constructs the 16x16 integer representation matrix of right multiplication R_V: X |-> X * V.
    """
    M = np.zeros((16, 16), dtype=int)
    for k in range(16):
        m1 = k ^ vi
        M[m1, k] += vs1 * _SIGN_16[k, vi]
        m2 = k ^ (8 + vj)
        M[m2, k] += vs2 * _SIGN_16[k, 8 + vj]
    return M


def compute_snf_invariants(M: np.ndarray) -> list[int]:
    """Computes the diagonal entries of the Smith Normal Form of integer matrix M."""
    M_sp = sp.Matrix(M)
    snf = smith_normal_form(M_sp)
    return [int(snf[i, i]) for i in range(16)]


def f2_rank_and_nullity(M: np.ndarray) -> tuple[int, int]:
    """Computes rank and nullity of M mod 2 over the finite field F_2."""
    M_f2 = sp.Matrix(M % 2)
    rank = int(M_f2.rank())
    nullity = 16 - rank
    return rank, nullity


def modular_kernel_log2_size(M: np.ndarray, modulus_bits: int = 16) -> int:
    """
    Computes log2 |ker(M mod 2^modulus_bits)| from the Smith Normal Form.
    If SNF diagonal is d_1, ..., d_16:
    For d_i != 0: ker factor is Z_{gcd(d_i, 2^b)}, size is gcd(d_i, 2^b).
    For d_i == 0: ker factor is Z_{2^b}, size is 2^b.
    """
    diag = compute_snf_invariants(M)
    modulus = 2 ** modulus_bits
    total_log2 = 0
    for d in diag:
        if d == 0:
            total_log2 += modulus_bits
        else:
            g = math.gcd(abs(d), modulus)
            total_log2 += int(math.log2(g))
    return total_log2


def verify_non_invertibility(M: np.ndarray, modulus_bits: int = 16) -> bool:
    """
    Verifies that M is non-invertible over Z_{2^modulus_bits} (i.e. det(M) = 0 mod 2).
    A matrix over Z_{2^b} is invertible iff det(M) is invertible in Z_{2^b} (i.e. det(M) is odd).
    """
    det = int(round(np.linalg.det(M)))
    return (det % 2) == 0


def verify_all_ramanujan_vertices() -> dict[str, Any]:
    """
    Verifies the modular kernel invariants for all 24 vertices of the Ramanujan expander graph Gamma.
    """
    graph = get_cached_annihilation_graph()
    results = []
    for u in sorted(graph.nx_graph.nodes):
        v = graph.nx_graph.nodes[u]["vector"]
        M = sedenion_left_mult_matrix(v.i, v.j, v.s1, v.s2)
        diag = compute_snf_invariants(M)
        rank_f2, nullity_f2 = f2_rank_and_nullity(M)
        log2_ker = modular_kernel_log2_size(M, 16)
        det = int(round(np.linalg.det(M)))
        non_inv = verify_non_invertibility(M, 16)
        results.append({
            "vertex": u,
            "vector": (v.i, v.j, v.s1, v.s2),
            "snf": diag,
            "rank_f2": rank_f2,
            "nullity_f2": nullity_f2,
            "log2_ker": log2_ker,
            "det": det,
            "non_invertible": non_inv,
        })
    return {
        "num_vertices": len(results),
        "all_snf_match": all(r["snf"] == [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 0, 0, 0, 0] for r in results),
        "all_nullity_8": all(r["nullity_f2"] == 8 for r in results),
        "all_log2_ker_68": all(r["log2_ker"] == 68 for r in results),
        "all_det_zero": all(r["det"] == 0 for r in results),
        "all_non_invertible": all(r["non_invertible"] for r in results),
        "details": results,
    }


def verify_all_168_zero_divisors() -> dict[str, Any]:
    """
    Verifies the modular kernel invariants across all 168 cross-octet zero divisors.
    """
    zd_count = 0
    snf_expected = [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 0, 0, 0, 0]
    all_snf_ok = True
    all_nullity_ok = True
    all_det_ok = True

    for vi in range(1, 8):
        for vj in range(1, 8):
            if vi == vj:
                continue
            for vs1 in (1, -1):
                for vs2 in (1, -1):
                    zd_count += 1
                    M = sedenion_left_mult_matrix(vi, vj, vs1, vs2)
                    diag = compute_snf_invariants(M)
                    if diag != snf_expected:
                        all_snf_ok = False
                    rank_f2, nullity_f2 = f2_rank_and_nullity(M)
                    if nullity_f2 != 8:
                        all_nullity_ok = False
                    det = int(round(np.linalg.det(M)))
                    if det != 0:
                        all_det_ok = False

    return {
        "zd_count": zd_count,
        "all_snf_ok": all_snf_ok,
        "all_nullity_ok": all_nullity_ok,
        "all_det_ok": all_det_ok,
    }
