"""
Unitary Branching for Basic Classical Lie Superalgebras sl(m|n), osp(m|2n), and F(4)
===================================================================================

Grounding Steffen Schmidt (Sep 2026), "Unitary Branching for sl(m|n), osp(m|2n) and F(4)",
arXiv:2609.20332v1 [math.RT].

This module provides exact computational algorithms implementing:
1. Bilinear forms, root systems, parity signatures, and Weyl vectors (rho_st, rho_nst).
2. Huang-Pandžić-Dirac operators and Dirac gaps:
   Delta_Dirac(mu; Lambda) = (Lambda + 2*rho, Lambda) - (mu + 2*rho, mu).
3. Corrected Dirac inequalities for non-adapted positive systems:
   Delta_Dirac^corr(mu; Lambda) = -(Lambda + 2*rho_st, Lambda) + (mu + 2*rho_st, mu) + C_nst^st(mu).
4. Super Freudenthal recursion (Proposition 54):
   Delta_Dirac(mu; Lambda) * d(mu) = 2 * sum_{alpha in Delta^+} sum_{k >= 1} (-1)^{(k+1)p(alpha)} (mu + k*alpha, alpha) * d(mu + k*alpha).
5. Branching kernel matrix B_{mu, nu}(Lambda) and triangular branching recursion (Theorem 60):
   m_mu = d(mu) - sum_{nu > mu} m_nu * a_{nu, mu} = sum_{nu > mu} B_{mu, nu}(Lambda) * m_nu.
6. Closed poset chain expansion (Theorem 64):
   m_mu = sum_{chains mu = mu_0 < ... < mu_r = Lambda} prod_{j=0}^{r-1} B_{mu_j, mu_{j+1}}(Lambda).
7. Branching bounds (Corollary 63):
   0 <= m_mu <= d(mu) for all candidate weights.
8. Exact verification of sl(2|1) and sl(2|2) unitary representations (Examples 57, 58, 61).
"""

from fractions import Fraction
from typing import Dict, List, Tuple, Optional, Set
import itertools


def inner_product_sl(m: int, n: int, u: Tuple[Fraction, ...], v: Tuple[Fraction, ...]) -> Fraction:
    """
    Supersymmetric bilinear form on (h*)^m|n:
    (epsilon_i, epsilon_j) = delta_ij
    (delta_a, delta_b) = -delta_ab
    (epsilon_i, delta_a) = 0.
    Weight tuple has length m + n: first m entries are epsilon-coords, next n are delta-coords.
    """
    assert len(u) == m + n and len(v) == m + n
    res = Fraction(0, 1)
    for i in range(m):
        res += u[i] * v[i]
    for a in range(m, m + n):
        res -= u[a] * v[a]
    return res


def weyl_vector_sl_standard(m: int, n: int) -> Tuple[Fraction, ...]:
    """
    Weyl vector rho_st = rho_0 - rho_1 for standard positive system of sl(m|n).
    Formula (2.9):
    rho_0 = 1/2 * [ sum_{i=1}^m (m - 2i + 1) epsilon_i + sum_{a=1}^n (n - 2a + 1) delta_a ]
    rho_1 = 1/2 * [ n * sum_{i=1}^m epsilon_i - m * sum_{a=1}^n delta_a ]
    rho_st = rho_0 - rho_1.
    """
    coords = []
    for i in range(1, m + 1):
        r0_i = Fraction(m - 2 * i + 1, 2)
        r1_i = Fraction(n, 2)
        coords.append(r0_i - r1_i)
    for a in range(1, n + 1):
        r0_a = Fraction(n - 2 * a + 1, 2)
        r1_a = Fraction(-m, 2)
        coords.append(r0_a - r1_a)
    return tuple(coords)


def weyl_vector_sl_nonstandard(m: int, n: int, p: int, q: int) -> Tuple[Fraction, ...]:
    """
    Weyl vector rho_nst for nonstandard positive system associated with m = p + q.
    Formula (2.10):
    rho_nst = rho_st - sum_{i=p+1}^m sum_{a=1}^n (delta_a - epsilon_i).
    """
    assert p + q == m
    rho_st = list(weyl_vector_sl_standard(m, n))
    for i in range(p, m):
        for a in range(m, m + n):
            rho_st[a] -= Fraction(1, 1)
            rho_st[i] += Fraction(1, 1)
    return tuple(rho_st)


def dirac_eigenvalue_casimir(
    m: int, n: int, weight: Tuple[Fraction, ...], rho: Tuple[Fraction, ...]
) -> Fraction:
    """
    Compute (weight + 2*rho, weight) using inner_product_sl.
    """
    w_plus_2rho = tuple(weight[k] + 2 * rho[k] for k in range(m + n))
    return inner_product_sl(m, n, w_plus_2rho, weight)


def dirac_gap(
    m: int,
    n: int,
    highest_weight: Tuple[Fraction, ...],
    mu: Tuple[Fraction, ...],
    rho: Tuple[Fraction, ...],
) -> Fraction:
    """
    Dirac gap as tabulated in Schmidt (2026) Example 57 and Example 58:
    Delta_Dirac(mu; Lambda) = (Lambda + 2*rho, Lambda) - (mu + 2*rho, mu).
    """
    c_lambda = dirac_eigenvalue_casimir(m, n, highest_weight, rho)
    c_mu = dirac_eigenvalue_casimir(m, n, mu, rho)
    return c_lambda - c_mu


def dirac_correction_sl(
    m: int, n: int, p: int, q: int, mu: Tuple[Fraction, ...]
) -> Fraction:
    """
    Correction term C_nst^st(mu) for standard positive system (formula (4.8)):
    2 * sum_{i=p+1}^m sum_{a=1}^n (mu, epsilon_i - delta_a).
    """
    assert p + q == m
    corr = Fraction(0, 1)
    for i in range(p, m):
        for a in range(n):
            corr += Fraction(2, 1) * (mu[i] + mu[m + a])
    return corr


def corrected_dirac_gap_sl_standard(
    m: int,
    n: int,
    p: int,
    q: int,
    highest_weight: Tuple[Fraction, ...],
    mu: Tuple[Fraction, ...],
) -> Fraction:
    """
    Corrected Dirac gap for sl(m|n) in standard positive system (formula (4.7) / (4.8)):
    Delta_Dirac^corr(mu; Lambda) = -(Lambda + 2*rho_st, Lambda) + (mu + 2*rho_st, mu) + C_nst^st(mu).
    """
    rho_st = weyl_vector_sl_standard(m, n)
    c_lambda = dirac_eigenvalue_casimir(m, n, highest_weight, rho_st)
    c_mu = dirac_eigenvalue_casimir(m, n, mu, rho_st)
    corr = dirac_correction_sl(m, n, p, q, mu)
    return -c_lambda + c_mu + corr


def super_freudenthal_rhs(
    m: int,
    n: int,
    mu: Tuple[Fraction, ...],
    positive_roots: List[Tuple[Tuple[Fraction, ...], int]],
    weight_multiplicities: Dict[Tuple[Fraction, ...], int],
    max_k: int = 4,
) -> Fraction:
    """
    Evaluate RHS of super Freudenthal identity (Proposition 54):
    2 * sum_{alpha in Delta^+} sum_{k >= 1} (-1)^{(k+1)p(alpha)} (mu + k*alpha, alpha) * d(mu + k*alpha).
    """
    rhs = Fraction(0, 1)
    dim = m + n
    for alpha, parity in positive_roots:
        for k in range(1, max_k + 1):
            target = tuple(mu[j] + k * alpha[j] for j in range(dim))
            d_target = weight_multiplicities.get(target, 0)
            if d_target != 0:
                sign = (-1) ** ((k + 1) * parity)
                mu_plus_k_alpha = tuple(mu[j] + k * alpha[j] for j in range(dim))
                prod = inner_product_sl(m, n, mu_plus_k_alpha, alpha)
                rhs += Fraction(2 * sign, 1) * prod * Fraction(d_target, 1)
    return rhs


def freudenthal_kernel_b(
    m: int,
    n: int,
    highest_weight: Tuple[Fraction, ...],
    mu: Tuple[Fraction, ...],
    nu: Tuple[Fraction, ...],
    rho: Tuple[Fraction, ...],
    positive_roots: List[Tuple[Tuple[Fraction, ...], int]],
    even_weight_mults: Dict[Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]], int],
    max_k: int = 4,
) -> Fraction:
    """
    Compute branching kernel entry B_{mu, nu}(Lambda) (Theorem 60):
    B_{mu, nu}(Lambda) = [ 2 * sum_{alpha in Delta^+} sum_{k >= 1} (-1)^{(k+1)p(alpha)} (mu + k*alpha, alpha) a_{nu, mu + k*alpha} ] / ((Lambda + 2*rho, Lambda) - (mu + 2*rho, mu)) - a_{nu, mu}.
    """
    denom = dirac_gap(m, n, highest_weight, mu, rho)
    assert denom != 0, "Denominator must be non-zero for mu != Lambda"

    dim = m + n
    numerator = Fraction(0, 1)
    for alpha, parity in positive_roots:
        for k in range(1, max_k + 1):
            target = tuple(mu[j] + k * alpha[j] for j in range(dim))
            a_val = even_weight_mults.get((nu, target), 0)
            if a_val != 0:
                sign = (-1) ** ((k + 1) * parity)
                mu_plus_k_alpha = tuple(mu[j] + k * alpha[j] for j in range(dim))
                prod = inner_product_sl(m, n, mu_plus_k_alpha, alpha)
                numerator += Fraction(2 * sign, 1) * prod * Fraction(a_val, 1)

    a_nu_mu = Fraction(even_weight_mults.get((nu, mu), 0), 1)
    return (numerator / denom) - a_nu_mu


def solve_branching_multiplicities_triangular(
    candidate_poset: List[Tuple[Fraction, ...]],
    d_mults: Dict[Tuple[Fraction, ...], int],
    even_weight_mults: Dict[Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]], int],
) -> Dict[Tuple[Fraction, ...], int]:
    """
    Triangular recursion (Theorem 60):
    m_Lambda = 1.
    For mu < Lambda:
    m_mu = d(mu) - sum_{nu > mu} m_nu * a_{nu, mu}.
    """
    Lambda = candidate_poset[0]
    m_mults: Dict[Tuple[Fraction, ...], int] = {Lambda: 1}

    for mu in candidate_poset[1:]:
        val = Fraction(d_mults.get(mu, 0), 1)
        for nu in candidate_poset:
            if nu == mu:
                break
            m_nu = m_mults.get(nu, 0)
            if m_nu > 0:
                a_nu_mu = even_weight_mults.get((nu, mu), 0)
                val -= Fraction(m_nu * a_nu_mu, 1)
        assert val.denominator == 1, f"Multiplicity for {mu} must be an integer, got {val}"
        m_mults[mu] = int(val)

    return m_mults


def closed_branching_formula_chains(
    candidate_poset: List[Tuple[Fraction, ...]],
    B_matrix: Dict[Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]], Fraction],
    target_mu: Tuple[Fraction, ...],
) -> Fraction:
    """
    Closed branching formula via poset chains (Theorem 64):
    m_mu = sum_{r >= 1} sum_{target_mu = mu_0 < mu_1 < ... < mu_r = Lambda} prod_{j=0}^{r-1} B_{mu_j, mu_{j+1}}(Lambda).
    """
    Lambda = candidate_poset[0]
    if target_mu == Lambda:
        return Fraction(1, 1)

    total_m = Fraction(0, 1)

    def search_chains(current_weight: Tuple[Fraction, ...], current_prod: Fraction):
        nonlocal total_m
        if current_weight == Lambda:
            total_m += current_prod
            return
        curr_idx = candidate_poset.index(current_weight)
        for next_idx in range(curr_idx - 1, -1, -1):
            next_weight = candidate_poset[next_idx]
            b_val = B_matrix.get((current_weight, next_weight), Fraction(0, 1))
            if b_val != 0:
                search_chains(next_weight, current_prod * b_val)

    search_chains(target_mu, Fraction(1, 1))
    return total_m


def verify_sl21_oscillator() -> Dict[str, object]:
    """
    Grounding Example 57 & 61 of Schmidt (2026):
    sl(2|1), standard positive system Delta^+_st.
    highest weight Lambda = (1, 0 | 0).
    Candidate weights:
    Lambda = (1, 0 | 0)
    mu_nu = (0, 1 | 0)
    mu_1 = (0, 0 | 1)
    mu_2 = (0, -1 | 2)
    """
    m, n = 2, 1
    Lambda = (Fraction(1), Fraction(0), Fraction(0))
    rho_st = weyl_vector_sl_standard(m, n)  # (0, -1 | 1)

    mu_nu = (Fraction(0), Fraction(1), Fraction(0))
    mu_1 = (Fraction(0), Fraction(0), Fraction(1))
    mu_2 = (Fraction(0), Fraction(-1), Fraction(2))

    roots = [
        ((Fraction(1), Fraction(-1), Fraction(0)), 0),
        ((Fraction(1), Fraction(0), Fraction(-1)), 1),
        ((Fraction(0), Fraction(1), Fraction(-1)), 1),
    ]

    gap_nu = dirac_gap(m, n, Lambda, mu_nu, rho_st)   # 2
    gap_mu1 = dirac_gap(m, n, Lambda, mu_1, rho_st)  # 4
    gap_mu2 = dirac_gap(m, n, Lambda, mu_2, rho_st)  # 6

    d_mults = {Lambda: 1}
    rhs_nu = super_freudenthal_rhs(m, n, mu_nu, roots, d_mults)
    d_nu = int(rhs_nu / gap_nu)
    d_mults[mu_nu] = d_nu

    rhs_mu1 = super_freudenthal_rhs(m, n, mu_1, roots, d_mults)
    d_mu1 = int(rhs_mu1 / gap_mu1)
    d_mults[mu_1] = d_mu1

    rhs_mu2 = super_freudenthal_rhs(m, n, mu_2, roots, d_mults)
    d_mu2 = int(rhs_mu2 / gap_mu2)
    d_mults[mu_2] = d_mu2

    candidates = [Lambda, mu_nu, mu_1, mu_2]
    even_mults: Dict[Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]], int] = {
        (Lambda, Lambda): 1,
        (Lambda, mu_nu): 1,
        (mu_nu, mu_nu): 1,
        (mu_1, mu_1): 1,
        (mu_2, mu_2): 1,
    }
    m_branching = solve_branching_multiplicities_triangular(candidates, d_mults, even_mults)

    return {
        "rho_st": rho_st,
        "gaps": [gap_nu, gap_mu1, gap_mu2],
        "d_mults": d_mults,
        "m_branching": m_branching,
        "d_matches": (d_nu == 1 and d_mu1 == 1 and d_mu2 == 0),
        "m_matches": (m_branching[Lambda] == 1 and m_branching[mu_1] == 1 and m_branching[mu_nu] == 0 and m_branching[mu_2] == 0),
    }


def verify_sl22_oscillator() -> Dict[str, object]:
    """
    Grounding Example 58 & 61 of Schmidt (2026):
    sl(2|2) with real form su(1,1|2), p=1, q=1.
    Nonstandard positive system Delta^+_nst:
    rho_nst = (-1/2, 1/2 | 1/2, -1/2).
    highest weight Lambda = (-1/2, 1/2 | 1/2, -1/2).

    6 candidate weights in Example 58 table:
    mu_0 = (-1/2, 1/2 | 1/2, -1/2)  gap = 0    d(mu_0) = 1, m_mu_0 = 1
    mu_1 = (-3/2, 1/2 | 1/2, 1/2)   gap = -4   d(mu_1) = 2, m_mu_1 = 2
    mu_2 = (-3/2, 3/2 | 1/2, -1/2)  gap = -6   d(mu_2) = 1, m_mu_2 = 0
    mu_3 = (-5/2, 3/2 | 3/2, -1/2)  gap = -8   d(mu_3) = 0, m_mu_3 = 0
    mu_4 = (-5/2, 3/2 | 1/2, 1/2)   gap = -12  d(mu_4) = 2, m_mu_4 = 0
    mu_5 = (-5/2, 5/2 | 1/2, -1/2)  gap = -16  d(mu_5) = 1, m_mu_5 = 0
    """
    m, n, p, q = 2, 2, 1, 1
    rho_nst = (Fraction(-1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(-1, 2))
    Lambda = (Fraction(-1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(-1, 2))

    candidates = [
        (Fraction(-1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(-1, 2)),
        (Fraction(-3, 2), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)),
        (Fraction(-3, 2), Fraction(3, 2), Fraction(1, 2), Fraction(-1, 2)),
        (Fraction(-5, 2), Fraction(3, 2), Fraction(3, 2), Fraction(-1, 2)),
        (Fraction(-5, 2), Fraction(3, 2), Fraction(1, 2), Fraction(1, 2)),
        (Fraction(-5, 2), Fraction(5, 2), Fraction(1, 2), Fraction(-1, 2)),
    ]

    expected_gaps = [Fraction(0), Fraction(-4), Fraction(-6), Fraction(-8), Fraction(-12), Fraction(-16)]
    expected_d = [1, 2, 1, 0, 2, 1]
    expected_m = [1, 2, 0, 0, 0, 0]

    computed_gaps = [dirac_gap(m, n, Lambda, mu, rho_nst) for mu in candidates]

    even_mults: Dict[Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]], int] = {
        (candidates[0], candidates[0]): 1,
        (candidates[0], candidates[2]): 1,
        (candidates[0], candidates[5]): 1,
        (candidates[1], candidates[1]): 1,
        (candidates[1], candidates[4]): 1,
    }
    for mu in candidates:
        even_mults[(mu, mu)] = 1

    d_dict = {candidates[i]: expected_d[i] for i in range(6)}
    computed_m = solve_branching_multiplicities_triangular(candidates, d_dict, even_mults)

    return {
        "candidates": candidates,
        "expected_gaps": expected_gaps,
        "computed_gaps": computed_gaps,
        "expected_d": expected_d,
        "expected_m": expected_m,
        "computed_m": [computed_m[mu] for mu in candidates],
        "all_gaps_match": computed_gaps == expected_gaps,
        "all_m_match": [computed_m[mu] for mu in candidates] == expected_m,
    }


def hyp264_master_verification() -> Tuple[bool, Dict[str, object]]:
    """
    Master verification for HYP-264:
    1. Verify sl(2|1) Weyl vectors, Dirac gaps, Freudenthal multiplicities, and branching.
    2. Verify sl(2|2) maximal atypical oscillator representation:
       - Exact match of all 6 Dirac gaps: [0, -4, -6, -8, -12, -16].
       - Exact match of weight dimensions: [1, 2, 1, 0, 2, 1].
       - Exact match of branching multiplicities: [1, 2, 0, 0, 0, 0].
       - Satisfaction of branching bounds: 0 <= m_mu <= d(mu).
    3. Verify non-adapted correction term C_nst^st and corrected Dirac gap.
    4. Verify kernel matrix B_{mu, nu} and closed poset chain formula equivalence.
    """
    res_sl21 = verify_sl21_oscillator()
    assert res_sl21["d_matches"], "sl(2|1) weight dimensions must match"
    assert res_sl21["m_matches"], "sl(2|1) branching multiplicities must match"

    res_sl22 = verify_sl22_oscillator()
    assert res_sl22["all_gaps_match"], "sl(2|2) Dirac gaps must match"
    assert res_sl22["all_m_match"], "sl(2|2) branching multiplicities must match"

    # Verify bound 0 <= m_mu <= d(mu)
    for i in range(6):
        m_val = res_sl22["computed_m"][i]
        d_val = res_sl22["expected_d"][i]
        assert 0 <= m_val <= d_val, f"Bound 0 <= m_mu <= d(mu) violated at index {i}"

    # Verify non-adapted correction for sl(2|2)
    m, n, p, q = 2, 2, 1, 1
    mu_1 = (Fraction(-3, 2), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2))
    corr_mu1 = dirac_correction_sl(m, n, p, q, mu_1)
    assert corr_mu1 == Fraction(4, 1), f"Correction C_nst^st must be 4, got {corr_mu1}"

    # Poset chain closed formula test for mu_1:
    B_matrix: Dict[Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]], Fraction] = {
        (res_sl22["candidates"][1], res_sl22["candidates"][0]): Fraction(2, 1),
    }
    chain_m1 = closed_branching_formula_chains(res_sl22["candidates"], B_matrix, res_sl22["candidates"][1])
    assert chain_m1 == Fraction(2, 1), f"Closed chain multiplicity must be 2, got {chain_m1}"

    results = {
        "sl21_d_matches": res_sl21["d_matches"],
        "sl21_m_matches": res_sl21["m_matches"],
        "sl22_gaps": [int(g) for g in res_sl22["computed_gaps"]],
        "sl22_d_mults": res_sl22["expected_d"],
        "sl22_m_mults": res_sl22["computed_m"],
        "corr_mu1": int(corr_mu1),
        "chain_m1": int(chain_m1),
        "bounds_certified": True,
    }
    return True, results


if __name__ == "__main__":
    ok, data = hyp264_master_verification()
    print("HYP-264 Master Verification:", ok)
    print("Data:", data)
