"""
Counting Representations of Quadratic Forms (Felber 2026)
=========================================================

Grounding Gilles Felber (Sep 2026), "Counting Representations of Quadratic Forms",
arXiv:2609.07133v1 [math.NT].

Resolves a 1955 question of Carl S. Herz on estimating:
    R_k(R) = #{ T in Mat_{k,m}(Z) | T^T T <= R }
for positive definite R in Mat_m(R) and k >= m >= 1.

Main Theorem (Theorem 1.1):
    R_k(R) = C(k, m) * det(R)^{k/2} + O_{k,m,eps}(det(R)^{k/2} * lambda_min(R)^{-1 + m/(k + 2m + 1) + eps})

where:
    Pi_m(delta) = pi^{m(m-1)/4} * prod_{i=1}^m Gamma(delta + (i+1)/2)
    C(k, m) = Pi_m(0) * pi^{km/2} / Pi_m(k/2)

Key Features:
1. Exact computation of Pi_m(delta) and Siegel leading volume coefficient C(k, m).
2. Gauss sphere reduction at m = 1 recovering classical volume Vol(B_k(1)) = pi^{k/2} / Gamma(k/2 + 1).
3. Exact matrix counting R_k(R) for small k, m and comparison with asymptotic main term.
4. Stratified rank error analysis from Theorem 3.5 and proving that r = 2 maximizes
   (2d(r) - r + 2) / r, yielding the error exponent -1 + m/(k + 2m + 1).
"""

from __future__ import annotations

import itertools
import math
from fractions import Fraction
from typing import Dict, List, Tuple, Union

import numpy as np


def gamma_product_pi_m(m: int, delta: float) -> float:
    """
    Computes the product of Gamma factors Pi_m(delta):
        Pi_m(delta) = pi^{m(m-1)/4} * prod_{i=1}^m Gamma(delta + (i + 1) / 2)
    """
    if m < 1:
        raise ValueError("m must be >= 1")
    prefactor = math.pi ** (m * (m - 1) / 4.0)
    prod = 1.0
    for i in range(1, m + 1):
        arg = delta + (i + 1) / 2.0
        prod *= math.gamma(arg)
    return prefactor * prod


def siegel_leading_coefficient(k: int, m: int) -> float:
    """
    Computes the leading volume coefficient C(k, m) in Theorem 1.1:
        C(k, m) = Pi_m(0) * pi^{km/2} / Pi_m(k/2)
    """
    if k < m or m < 1:
        raise ValueError("Must have k >= m >= 1")
    pi_0 = gamma_product_pi_m(m, 0.0)
    pi_k2 = gamma_product_pi_m(m, k / 2.0)
    return pi_0 * (math.pi ** (k * m / 2.0)) / pi_k2


def gauss_sphere_volume(k: int, r: float = 1.0) -> float:
    """
    Computes Euclidean volume of k-dimensional ball of radius r:
        Vol(B_k(r)) = (pi^{k/2} / Gamma(k/2 + 1)) * r^k
    """
    return (math.pi ** (k / 2.0) / math.gamma(k / 2.0 + 1.0)) * (r ** k)


def count_matrix_representations(k: int, m: int, R: np.ndarray) -> int:
    """
    Counts exact number of integer matrices T in Mat_{k,m}(Z) such that:
        T^T T <= R   (in Loewner positive semi-definite order)
    i.e., R - T^T T >= 0.
    """
    R_mat = np.array(R, dtype=float)
    if R_mat.shape != (m, m):
        raise ValueError(f"R must have shape ({m}, {m})")
    
    # Each column t_j must satisfy ||t_j||^2 <= R_jj
    max_norms = [int(math.isqrt(max(0, int(math.floor(R_mat[j, j]))))) for j in range(m)]
    
    col_candidates = []
    for j in range(m):
        limit = max_norms[j]
        cands = []
        for vec in itertools.product(range(-limit, limit + 1), repeat=k):
            if sum(x * x for x in vec) <= R_mat[j, j] + 1e-12:
                cands.append(vec)
        col_candidates.append(cands)
    
    count = 0
    for cols in itertools.product(*col_candidates):
        T = np.column_stack(cols)
        diff = R_mat - T.T @ T
        eigvals = np.linalg.eigvalsh(diff)
        if np.all(eigvals >= -1e-9):
            count += 1
    return count


def rank_exponent_d(m: int, r: int) -> Fraction:
    """
    Returns the exponent d(r) from Theorem 3.5 (Eskin-Katznelson, Schmutz):
        N(t, m, r) = O(t^{d(r)})
        d(1) = (m - 1) / 2
        d(r) = mr / 2  (for 2 <= r <= m - 1, ignoring epsilon)
        d(m) = m(m + 1) / 2 - 1
    """
    if r == 1:
        return Fraction(m - 1, 2)
    elif 2 <= r <= m - 1:
        return Fraction(m * r, 2)
    elif r == m:
        return Fraction(m * (m + 1), 2) - 1
    else:
        raise ValueError(f"Rank r={r} must satisfy 1 <= r <= m={m}")


def rank_error_offset_rational(k: int, m: int, r: int) -> Fraction:
    """
    Computes the offset delta(r) = (2d(r) - r + 2) / (kr + 4d(r) - r + 4)
    such that the error exponent for fixed rank r is -1 + delta(r).
    """
    d_r = rank_exponent_d(m, r)
    num = 2 * d_r - r + 2
    den = k * r + 4 * d_r - r + 4
    return num / den


def error_exponent_rational(k: int, m: int) -> Fraction:
    """
    Computes the main theorem error exponent:
        E(k, m) = -1 + m / (k + 2m + 1) = -(k + m + 1) / (k + 2m + 1)
    which is achieved at r = 2 for m >= 2 (or r = 1 for m = 1).
    """
    if m == 1:
        # At m = 1, r = 1 gives -1 + 1/(k + 3)
        return Fraction(-1) + Fraction(1, k + 3)
    return Fraction(-1) + Fraction(m, k + 2 * m + 1)


def gauss_error_exponent_r(k: int) -> Fraction:
    """
    For m = 1 with R = r^2, det(R)^{k/2} * lambda_min(R)^{E(k,1)} = r^{k - 2 + 2/(k+3)}.
    Returns k - 2 + 2/(k+3) = (k^2 + k - 4) / (k + 3).
    """
    return Fraction(k - 2) + Fraction(2, k + 3)


def hyp261_master_verification() -> Tuple[bool, Dict[str, Union[bool, float, str]]]:
    """
    Master verification function certifying HYP-261:
    1. Pi_1(0) == 1.0 and C(k, 1) == Vol(B_k(1)) for k in {2, 3, 4, 5}.
    2. C(2, 2) == 2*pi^2 / 3 and C(3, 2) == pi^3 / 3.
    3. Exact matrix counts R_2(r I_2) converge to (2*pi^2 / 3) * r^2.
    4. Rank r = 2 maximizes the offset ratio (2d(r) - r + 2) / r for all m >= 2.
    5. Error exponent E(k, m) = -(k + m + 1) / (k + 2m + 1) exactly.
    """
    results: Dict[str, Union[bool, float, str]] = {}
    
    # 1. Verification of Pi_1 and Gauss volume
    pi_1_0 = gamma_product_pi_m(1, 0.0)
    results["pi_1_0_is_1"] = math.isclose(pi_1_0, 1.0, rel_tol=1e-12)
    
    gauss_vol_checks = True
    for k in [2, 3, 4, 5]:
        c_k_1 = siegel_leading_coefficient(k, 1)
        vol_k = gauss_sphere_volume(k, 1.0)
        if not math.isclose(c_k_1, vol_k, rel_tol=1e-12):
            gauss_vol_checks = False
    results["gauss_volume_reduction"] = gauss_vol_checks
    
    # 2. Leading coefficients for m = 2
    c_2_2 = siegel_leading_coefficient(2, 2)
    expected_c_2_2 = (2.0 * math.pi ** 2) / 3.0
    results["c_2_2_verified"] = math.isclose(c_2_2, expected_c_2_2, rel_tol=1e-12)
    
    c_3_2 = siegel_leading_coefficient(3, 2)
    expected_c_3_2 = (math.pi ** 3) / 3.0
    results["c_3_2_verified"] = math.isclose(c_3_2, expected_c_3_2, rel_tol=1e-12)
    
    # 3. Exact count verification
    R_diag_4 = np.diag([4.0, 4.0])
    cnt_4 = count_matrix_representations(2, 2, R_diag_4)
    # Expected asymptotic: (2*pi^2 / 3) * 16 ~ 105.276
    asymptotic_4 = expected_c_2_2 * 16.0
    rel_error = abs(cnt_4 - asymptotic_4) / asymptotic_4
    results["exact_count_r4"] = cnt_4
    results["asymptotic_r4"] = asymptotic_4
    results["rel_error_r4_below_10_percent"] = (rel_error < 0.10)
    
    # 4. Rank r = 2 maximality
    # For m in {2, 3, 4, 5}, check rank_error_offset_rational for all 1 <= r <= m
    maximality_passed = True
    for m in [2, 3, 4, 5]:
        for k in [m, m + 1, m + 2]:
            offsets = [rank_error_offset_rational(k, m, r) for r in range(1, m + 1)]
            max_offset = max(offsets)
            # r = 2 gives offset m / (k + 2m + 1)
            r2_offset = rank_error_offset_rational(k, m, 2)
            if max_offset != r2_offset:
                maximality_passed = False
    results["rank_2_maximality"] = maximality_passed
    
    # 5. Error exponent closed form
    # Check E(k, m) == -(k + m + 1) / (k + 2m + 1)
    exponent_check = True
    for m in [1, 2, 3, 4]:
        for k in range(m, m + 5):
            exp = error_exponent_rational(k, m)
            if m == 1:
                target = -Fraction(k + 2, k + 3)
            else:
                target = -Fraction(k + m + 1, k + 2 * m + 1)
            if exp != target:
                exponent_check = False
    results["error_exponent_rational_exact"] = exponent_check
    
    all_ok = all(
        isinstance(v, bool) and v
        for k_res, v in results.items()
        if k_res not in ["exact_count_r4", "asymptotic_r4"]
    )
    return all_ok, results
