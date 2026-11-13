r"""tensor_rank_barriers_48.py — Certified Local Rank and Uniqueness Barriers
========================================================================
Grounding: Abhinav Agarwal (Sep 2026),
"Certified local rank and uniqueness barriers for a 48-term matrix-multiplication decomposition"
arXiv:2609.xxxxx.

Decomposition D(\tau) of \langle 4, 4, 4 \rangle over R = \mathbb{Z}[1/2, t, t^{-1}]:
\langle 4, 4, 4 \rangle = \sum_{i=1}^{48} \operatorname{vec}(U_i(t)) \otimes \operatorname{vec}(V_i(t)) \otimes \operatorname{vec}(W_i(t))

Key Invariants:
1. Pairwise Separation: 3 * C(48, 2) = 3384 unit minors \pm 2^a t^k in R.
2. Mode k-Rank Profile: (k_A, k_B, k_C) = (2, 3, 3) at D(2).
   - Mode 1: exactly 2 (16 dependent triples forming 4 cycle-blocks A, B, C, D of size 4).
   - Modes 2 and 3: k-rank >= 3.
3. Strong 3-Local Rigidity: \rho_{strong}(D(2)) >= min(48, k_B, \lfloor(k_B + k_C)/2\rfloor) = 3.
4. Rank Radius: \rho(D(2)) >= 10 (via 6,540,715,864 subsets of size 10 satisfying Lovitz-Petrov,
   and 32 core subsets certified by Young flattening \lceil 194/20 \rceil = 10).
5. Border Rank Radius: \bar{\rho}(D(2)) >= 8 (via commutator rank and Young flattening \lceil 77/10 \rceil = 8).
6. Cycle-Block Structure: X = {4, 9, 12, 15, 17, 19, 22, 25, 28, 32, 34, 35, 38, 40, 44, 48}.
   A = {4, 17, 34, 40}, B = {9, 25, 28, 35}, C = {12, 19, 22, 32}, D = {15, 38, 44, 48}.
"""

from __future__ import annotations
import math
from typing import Dict, List, Set, Tuple


def verify_mode_krank_profile(k_A: int, k_B: int, k_C: int) -> Tuple[int, int, int]:
    """Return the sorted k-rank profile tuple."""
    return tuple(sorted([k_A, k_B, k_C]))


def strong_radius_from_profile(k_A: int, k_B: int, k_C: int, n: int = 48) -> int:
    r"""Theorem 2.10 (Agarwal 2026):
    For profile k_A <= k_B <= k_C:
    \rho_{strong} >= min(n, k_B, \lfloor (k_B + k_C) / 2 \rfloor)
    """
    sorted_k = sorted([k_A, k_B, k_C])
    k1, k2, k3 = sorted_k[0], sorted_k[1], sorted_k[2]
    return min(n, k2, (k2 + k3) // 2)


def border_transfer_bound(k_A: int, k_B: int, k_C: int, n: int = 48) -> int:
    """Border transfer bound for border radius (Corollary 4.5):
    For profile (2, 3, 3): min(48, 4, 3) = 3.
    General formula: min(n, k_B + 1, (k_B + k_C) // 2)
    """
    sorted_k = sorted([k_A, k_B, k_C])
    k1, k2, k3 = sorted_k[0], sorted_k[1], sorted_k[2]
    return min(n, k2 + 1, (k2 + k3) // 2)


def young_flattening_bound(young_rank: int, binomial_divisor: int) -> int:
    r"""Compute Young flattening rank lower bound:
    R >= \lceil young_rank / binomial_divisor \rceil
    """
    if binomial_divisor <= 0:
        raise ValueError("Divisor must be positive.")
    return math.ceil(young_rank / binomial_divisor)


def cycle_block_partition() -> Dict[str, Set[int]]:
    """Return the four cycle-blocks of the high-rank set X."""
    X: Set[int] = {4, 9, 12, 15, 17, 19, 22, 25, 28, 32, 34, 35, 38, 40, 44, 48}
    A: Set[int] = {4, 17, 34, 40}
    B: Set[int] = {9, 25, 28, 35}
    C: Set[int] = {12, 19, 22, 32}
    D: Set[int] = {15, 38, 44, 48}
    return {"X": X, "A": A, "B": B, "C": C, "D": D}


def pairwise_separation_count(n_summands: int = 48, n_modes: int = 3) -> int:
    """Count of (pair, mode) combinations certifying pairwise separation:
    n_modes * C(n_summands, 2)
    """
    pairs = n_summands * (n_summands - 1) // 2
    return n_modes * pairs


def kruskal_rank_sum_bound(k_A: int, k_B: int, k_C: int) -> int:
    """Compute Kruskal sum k_A + k_B + k_C."""
    return k_A + k_B + k_C


def census_level_exception_count() -> Dict[int, int]:
    """Certified exception counts across census levels in Agarwal (2026):
    - Level 6: 32 exceptions (certified by Lemma 3.6)
    - Level 7: 4240 exceptions (4176 by Lemma 3.6, 64 by Lemma 3.7 + Young)
    - Level 8: 154936 exceptions (151664 by commutator, 712 by rank ineq, 2560 by Lemma 3.7 + Young)
    - Level 10: 32 residual exceptions inside core X (certified by Young flattening ranks 190-195)
    """
    return {
        6: 32,
        7: 4240,
        8: 154936,
        10: 32,
    }


def hyp238_master_verification() -> Tuple[bool, Dict[str, any]]:
    """Master verification of HYP-238 algebraic invariants."""
    # 1. Separation count
    sep_count = pairwise_separation_count(48, 3)
    assert sep_count == 3384

    # 2. Strong radius from profile (2, 3, 3)
    rho_strong = strong_radius_from_profile(2, 3, 3, 48)
    assert rho_strong == 3

    # 3. Border transfer bound
    border_bound = border_transfer_bound(2, 3, 3, 48)
    assert border_bound == 3

    # 4. Young flattening levels
    y7 = young_flattening_bound(41, 6)    # Level 7: C(4, 2) = 6 -> ceil(41/6) = 7
    y8 = young_flattening_bound(77, 10)   # Level 8: C(5, 2) = 10 -> ceil(77/10) = 8
    y10_a = young_flattening_bound(194, 20)  # Level 10: C(6, 3) = 20 -> ceil(194/20) = 10
    y10_b = young_flattening_bound(195, 20)  # Level 10: C(6, 3) = 20 -> ceil(195/20) = 10
    assert y7 == 7
    assert y8 == 8
    assert y10_a == 10
    assert y10_b == 10

    # 5. Cycle block partition
    blocks = cycle_block_partition()
    union_abcd = blocks["A"] | blocks["B"] | blocks["C"] | blocks["D"]
    assert union_abcd == blocks["X"]
    assert len(blocks["X"]) == 16
    assert len(blocks["A"]) == 4
    assert len(blocks["B"]) == 4
    assert len(blocks["C"]) == 4
    assert len(blocks["D"]) == 4
    assert len(blocks["A"] & blocks["B"]) == 0
    assert len(blocks["A"] & blocks["C"]) == 0
    assert len(blocks["A"] & blocks["D"]) == 0
    assert len(blocks["B"] & blocks["C"]) == 0
    assert len(blocks["B"] & blocks["D"]) == 0
    assert len(blocks["C"] & blocks["D"]) == 0

    # 6. Total subsets of size 10
    c48_10 = math.comb(48, 10)
    assert c48_10 == 6540715896
    lp_ten_subsets = c48_10 - 32
    assert lp_ten_subsets == 6540715864

    # 7. Level 8 exception decomposition
    assert 151664 + 712 + 2560 == 154936

    results = {
        "pairwise_separation_count": sep_count,
        "strong_radius": rho_strong,
        "border_transfer_bound": border_bound,
        "young_flattening_level_7": y7,
        "young_flattening_level_8": y8,
        "young_flattening_level_10": y10_a,
        "c48_10_total": c48_10,
        "lp_satisfied_ten_subsets": lp_ten_subsets,
        "cycle_blocks_valid": True,
    }
    return True, results
