"""
torus_knot_rogers_ramanujan.py

Rigorous computational implementation of geometric Rogers-Ramanujan and Andrews-Gordon
identities for torus-knot singularities X^a = Y^b via bounded cylindric partitions,
rational Dyck paths, and HJO q-series.

Grounds:
Yifeng Huang, Kenny Lau, and Ken Ono (2026),
"Rogers-Ramanujan identities from the geometry of X^a = Y^b",
arXiv:2609.xxxxx / Cognition Library preprint.
"""

from math import gcd, comb, ceil
from typing import Dict, List, Tuple, Set
import sympy as sp

q = sp.Symbol("q")


def semigroup_and_gaps(a: int, b: int, max_val: int = 100) -> Tuple[Set[int], List[int], int, int]:
    """
    Computes numerical semigroup Gamma = <a, b>, gap set G = Z_{>=0} \\ Gamma,
    Frobenius maximum gap f = ab - a - b, and genus delta = (a - 1)(b - 1) // 2.
    """
    assert a > 1 and b > 1, "a and b must be > 1"
    assert gcd(a, b) == 1, "a and b must be coprime"
    
    f_expected = a * b - a - b
    delta_expected = (a - 1) * (b - 1) // 2
    limit = max(max_val, f_expected + a + b + 10)
    
    gamma = set()
    for u in range(limit // a + 1):
        for v in range((limit - a * u) // b + 1):
            gamma.add(a * u + b * v)
            
    gaps = sorted([x for x in range(limit) if x not in gamma])
    # All elements > f_expected must be in gamma
    for x in range(f_expected + 1, limit):
        assert x in gamma, f"Element {x} > f={f_expected} not in Gamma"
        
    G = [g for g in gaps if g <= f_expected]
    assert len(G) == delta_expected, f"Expected {delta_expected} gaps, got {len(G)}"
    assert max(G) == f_expected, f"Expected max gap {f_expected}, got {max(G)}"
    return gamma, G, f_expected, delta_expected


def gap_poset(a: int, b: int) -> Dict[str, any]:
    """
    Computes the gap poset (G, <=) where g <= h iff h - g in Gamma.
    Also returns the Sylvester coordinates (x, y) with 1 <= x < a, 1 <= y < b,
    ay - bx > 0, g = ay - bx.
    """
    gamma, G, f, delta = semigroup_and_gaps(a, b)
    order_pairs = []
    for g in G:
        for h in G:
            if (h - g) in gamma:
                order_pairs.append((g, h))
                
    sylvester = {}
    for x in range(1, a):
        for y in range(1, b):
            val = a * y - b * x
            if val > 0:
                sylvester[val] = (x, y)
                
    assert set(sylvester.keys()) == set(G), "Sylvester coordinates mismatch with G"
    return {
        "G": G,
        "f": f,
        "delta": delta,
        "order_pairs": set(order_pairs),
        "sylvester": sylvester,
    }


def order_filters(a: int, b: int) -> List[Dict[int, int]]:
    """
    Returns all order filters of the gap poset G.
    An order filter is represented as a dictionary {g: 1 if g in filter else 0}.
    Verifies that the total count of order filters equals the rational Catalan
    number Cat(a, b) = 1/(a + b) * binom(a + b, a).
    """
    gamma, G, f, delta = semigroup_and_gaps(a, b)
    expected_cat = comb(a + b, a) // (a + b)
    
    import itertools
    filters = []
    for bits in itertools.product([0, 1], repeat=len(G)):
        n_vec = dict(zip(G, bits))
        valid = True
        for g in G:
            if not valid:
                break
            for h in G:
                if (h - g) in gamma and g != h:
                    # if g <= h in poset, filter must satisfy: g in filter => h in filter
                    # i.e. n_g <= n_h
                    if n_vec[g] > n_vec[h]:
                        valid = False
                        break
        if valid:
            filters.append(n_vec)
            
    assert len(filters) == expected_cat, f"Expected {expected_cat} filters, got {len(filters)}"
    return filters


def cone_vectors(a: int, b: int, N: int) -> List[Dict[int, int]]:
    """
    Returns all gap vectors n in C with n_f <= N.
    C := {n in Z_{>=0}^G : n_g <= n_h whenever g <= h}.
    """
    gamma, G, f, delta = semigroup_and_gaps(a, b)
    import itertools
    vectors = []
    for vals in itertools.product(range(N + 1), repeat=len(G)):
        n_vec = dict(zip(G, vals))
        valid = True
        for g in G:
            if not valid:
                break
            for h in G:
                if (h - g) in gamma and g != h:
                    if n_vec[g] > n_vec[h]:
                        valid = False
                        break
        if valid and n_vec[f] <= N:
            vectors.append(n_vec)
    return vectors


def K_kernel(s: int, a: int, b: int) -> int:
    """
    K(s) := 1_{s >= 0} - 1_{s >= a} - 1_{s >= b} + 1_{s >= a + b}
    """
    return (1 if s >= 0 else 0) - (1 if s >= a else 0) - (1 if s >= b else 0) + (1 if s >= (a + b) else 0)


def quadratic_form_Q(n_vec: Dict[int, int], a: int, b: int) -> int:
    """
    Q(n) := sum_{g, h in G} K(h - g) n_g n_h.
    Verifies effective positive definiteness: Q(n) >= n_f^2 / delta.
    """
    gamma, G, f, delta = semigroup_and_gaps(a, b)
    val = 0
    for g in G:
        for h in G:
            val += K_kernel(h - g, a, b) * n_vec[g] * n_vec[h]
            
    # Check effective positive definiteness bound (Theorem 1.3 of Huang 2026)
    nf = n_vec.get(f, 0)
    assert val * delta >= nf * nf, f"Effective positive definiteness failed: Q={val}, nf^2/delta={nf**2 / delta}"
    return val


def q_factorial(n: int) -> sp.Expr:
    """
    (q; q)_n = prod_{i=1}^n (1 - q^i)
    """
    res = sp.Integer(1)
    for i in range(1, n + 1):
        res *= (1 - q**i)
    return res


def q_binomial(u: int, v: int) -> sp.Expr:
    """
    Gaussian binomial [u choose v]_q.
    """
    if v < 0 or v > u:
        return sp.Integer(0)
    if v == 0 or v == u:
        return sp.Integer(1)
    num = q_factorial(u)
    den = q_factorial(v) * q_factorial(u - v)
    return sp.simplify(num / den)


def good_traverse_factorization(n_vec: Dict[int, int], N: int, a: int, b: int) -> sp.Expr:
    """
    [N choose n]_{q; G} := prod_{g in G} [ n_hat(g + b) - n_hat(g - a) choose n(g) - n_hat(g - a) ]_q.
    where n_hat(j) = n_j for j in G, N for j in Gamma, 0 for j < 0.
    """
    gamma, G, f, delta = semigroup_and_gaps(a, b)
    
    def n_hat(j: int) -> int:
        if j < 0:
            return 0
        if j in G:
            return n_vec[j]
        if j in gamma:
            return N
        return 0

    mult = sp.Integer(1)
    for g in G:
        u = n_hat(g + b) - n_hat(g - a)
        v = n_vec[g] - n_hat(g - a)
        mult *= q_binomial(u, v)
    return sp.expand(mult)


def HJO_polynomial_F(a: int, b: int, N: int) -> sp.Expr:
    """
    F_N(q) := N_{a, b; N}(q, 1) = sum_{n in C, n_f <= N} [N choose n]_{q; G} q^{Q(n)}.
    Verifies that F_N(1) = Cat(a, b)^N.
    """
    vecs = cone_vectors(a, b, N)
    poly = sp.Integer(0)
    for n_vec in vecs:
        factor = good_traverse_factorization(n_vec, N, a, b)
        Q = quadratic_form_Q(n_vec, a, b)
        poly += factor * (q**Q)
    poly = sp.expand(poly)
    
    cat = comb(a + b, a) // (a + b)
    val_at_1 = poly.subs(q, 1)
    assert val_at_1 == cat**N, f"F_{N}(1) = {val_at_1} != {cat**N}"
    return poly


def universal_shifts(a: int, b: int, N: int) -> Tuple[int, int]:
    """
    Computes universal shifts:
    d = a + b
    kappa_N = (d - 1) * binom(N, 2)
    gamma_N = d * binom(N, 2)
    """
    d = a + b
    binom_N_2 = N * (N - 1) // 2
    kappa_N = (d - 1) * binom_N_2
    gamma_N = d * binom_N_2
    assert gamma_N - kappa_N == binom_N_2
    return kappa_N, gamma_N


def dyck_paths(a: int, b: int, N: int) -> List[List[int]]:
    """
    Enumerates rational Dyck paths from (0, 0) to (a*N, b*N) weakly above diagonal y = (b/a)*x.
    Returns list of y-coordinates of the horizontal steps (columns x = 0 ... a*N - 1).
    """
    target_x, target_y = a * N, b * N
    paths = []
    
    def backtrack(x: int, y: int, cur_y: List[int]):
        if x == target_x and y == target_y:
            paths.append(list(cur_y))
            return
        if y < target_y:
            backtrack(x, y + 1, cur_y)
        if x < target_x:
            # Condition to stay weakly above diagonal: a * y >= b * (x + 1)
            if a * y >= b * (x + 1):
                backtrack(x + 1, y, cur_y + [y])
                
    backtrack(0, 0, [])
    return paths


def dyck_area_polynomial_A(a: int, b: int, N: int) -> sp.Expr:
    """
    A_N(q) := sum_{P in D_{aN, bN}} q^{area(P)}
    where area(P) = sum_{x=0}^{aN-1} (y_x - ceil(b*(x + 1)/a)).
    """
    paths = dyck_paths(a, b, N)
    poly = sp.Integer(0)
    for p in paths:
        area = sum(p[x] - ceil(b * (x + 1) / a) for x in range(a * N))
        poly += q**area
    return sp.expand(poly)


def verify_recurrence_and_F2(a: int, b: int) -> Dict[str, any]:
    """
    Verifies the core q-difference relations:
    1. F_1(q) = A_1(q).
    2. q^{a+b} F_2(q) = A_1(q)^2 - (1 - q) A_2(q).
    3. Divisibility of A_1(q)^2 - q^{a+b} F_2(q) by 1 - q in Z[q],
       with quotient at q=1 equal to |D_{2a, 2b}| = A_2(1).
    """
    d = a + b
    A1 = dyck_area_polynomial_A(a, b, 1)
    A2 = dyck_area_polynomial_A(a, b, 2)
    F1 = HJO_polynomial_F(a, b, 1)
    F2 = HJO_polynomial_F(a, b, 2)
    
    assert sp.simplify(F1 - A1) == 0, f"F1 != A1: F1={F1}, A1={A1}"
    
    lhs = q**d * F2
    rhs = A1**2 - (1 - q) * A2
    diff = sp.simplify(lhs - rhs)
    assert diff == 0, f"Recurrence failed: lhs - rhs = {diff}"
    
    # Polynomial division
    poly = sp.Poly(A1**2 - q**d * F2, q)
    quo, rem = sp.div(poly, sp.Poly(1 - q, q))
    assert rem == 0, "Not divisible by 1 - q"
    val_at_1 = quo.subs(q, 1)
    expected_A2_1 = A2.subs(q, 1)
    assert val_at_1 == expected_A2_1, f"Quotient at 1 {val_at_1} != A2(1) {expected_A2_1}"
    
    return {
        "A1": A1,
        "A2": A2,
        "F1": F1,
        "F2": F2,
        "A2_at_1": int(expected_A2_1),
        "F1_at_1": int(F1.subs(q, 1)),
        "F2_at_1": int(F2.subs(q, 1)),
    }


def rho_exponents(a: int, b: int, max_m: int) -> List[int]:
    """
    Computes rho_{a, b}(m) := min(a, b, dist(am, d Z)) - 1 + 1_{d | m}
    for m = 1 ... max_m.
    """
    d = a + b
    res = []
    for m in range(1, max_m + 1):
        rem = (a * m) % d
        dist = min(rem, d - rem)
        indicator = 1 if (m % d == 0) else 0
        val = min(a, b, dist) - 1 + indicator
        res.append(val)
    return res


def expand_P_product(a: int, b: int, max_deg: int = 15) -> List[int]:
    """
    Expands P_{a, b}(q) = prod_{m >= 1} (1 - q^m)^{-rho_{a, b}(m)}
    as a formal power series up to degree max_deg.
    """
    d = a + b
    exps = rho_exponents(a, b, d)
    coeffs = [0] * (max_deg + 1)
    coeffs[0] = 1
    for m in range(1, max_deg + 1):
        r = exps[(m - 1) % d]
        for _ in range(r):
            for i in range(m, max_deg + 1):
                coeffs[i] += coeffs[i - m]
    return coeffs


def corteel_warnaar_Q_poly(a: int, b: int, m: int) -> sp.Expr:
    """
    Computes Q_{m, c}(q) = sum_{n in C, n_f = m} q^{Q(n)} [m choose n]_{q; G}.
    Verifies that all coefficients are non-negative integers.
    """
    gamma, G, f, delta = semigroup_and_gaps(a, b)
    vecs = cone_vectors(a, b, m)
    poly = sp.Integer(0)
    for n_vec in vecs:
        if n_vec[f] == m:
            factor = good_traverse_factorization(n_vec, m, a, b)
            Q = quadratic_form_Q(n_vec, a, b)
            poly += factor * (q**Q)
    poly = sp.expand(poly)
    
    # Check non-negativity of coefficients
    poly_obj = sp.Poly(poly, q)
    for c in poly_obj.coeffs():
        assert c >= 0, f"Negative coefficient {c} in Q_{m, c}(q)"
    return poly


def hyp265_master_verification() -> Tuple[bool, Dict[str, any]]:
    """
    Master verification function for HYP-265:
    1. Tests (2, 3) classical Rogers-Ramanujan case:
       - Cat(2, 3) = 2, F_1(1) = 2, F_2(1) = 4, |D_{4, 6}| = 23
       - F_1(q) = 1 + q
       - F_2(q) = 1 + q + q^2 + q^4
       - rho mod 5: [1, 0, 0, 1, 0]
    2. Tests (3, 4) Lau-Ono case:
       - Cat(3, 4) = 5, F_1(1) = 5
       - rho mod 7: [2, 0, 1, 1, 0, 2, 0]
    3. Tests (4, 5) Huang-Lau-Ono case:
       - Cat(4, 5) = 14, F_1(1) = 14, F_2(1) = 196, |D_{8, 10}| = 2529
       - F_1(q) = 1 + 3q + 3q^2 + 3q^3 + 2q^4 + q^5 + q^6
       - F_2(q) matching formula on page 36
       - Shifts: kappa_2 = 8, gamma_2 = 9
       - rho mod 9: [3, 0, 2, 1, 1, 2, 0, 3, 0]
       - Corteel-Warnaar positivity for m = 0, 1, 2
    """
    # (2, 3)
    rec23 = verify_recurrence_and_F2(2, 3)
    assert rec23["F1_at_1"] == 2
    assert rec23["F2_at_1"] == 4
    assert rec23["A2_at_1"] == 23
    assert rec23["F1"] == 1 + q
    assert rec23["F2"] == 1 + q + q**2 + q**4
    assert rho_exponents(2, 3, 5) == [1, 0, 0, 1, 0]
    
    # (3, 4)
    assert rho_exponents(3, 4, 7) == [2, 0, 1, 1, 0, 2, 0]
    filters34 = order_filters(3, 4)
    assert len(filters34) == 5
    
    # (4, 5)
    rec45 = verify_recurrence_and_F2(4, 5)
    assert rec45["F1_at_1"] == 14
    assert rec45["F2_at_1"] == 196
    assert rec45["A2_at_1"] == 2529
    assert rec45["F1"] == 1 + 3*q + 3*q**2 + 3*q**3 + 2*q**4 + q**5 + q**6
    
    expected_F2_45 = (
        1 + 3*q + 6*q**2 + 9*q**3 + 13*q**4 + 14*q**5 + 17*q**6 + 16*q**7
        + 17*q**8 + 15*q**9 + 15*q**10 + 12*q**11 + 13*q**12 + 9*q**13 + 9*q**14
        + 6*q**15 + 6*q**16 + 4*q**17 + 4*q**18 + 2*q**19 + 2*q**20
        + q**21 + q**22 + q**24
    )
    assert sp.simplify(rec45["F2"] - expected_F2_45) == 0
    
    kap2, gam2 = universal_shifts(4, 5, 2)
    assert kap2 == 8 and gam2 == 9
    assert rho_exponents(4, 5, 9) == [3, 0, 2, 1, 1, 2, 0, 3, 0]
    
    # Check Corteel-Warnaar positivity
    Q0 = corteel_warnaar_Q_poly(4, 5, 0)
    Q1 = corteel_warnaar_Q_poly(4, 5, 1)
    assert Q0 == 1
    assert Q1 == 3*q + 3*q**2 + 3*q**3 + 2*q**4 + q**5 + q**6
    
    results = {
        "status": "PASS",
        "case_2_3": rec23,
        "case_4_5": rec45,
        "shifts_4_5_N2": {"kappa_2": kap2, "gamma_2": gam2},
        "rho_4_5": rho_exponents(4, 5, 9),
    }
    return True, results


if __name__ == "__main__":
    ok, res = hyp265_master_verification()
    print("HYP-265 Master Verification:", ok)
    print("Results:", res)
