r"""Torus Knots as Loop-Edges in Three-Sphere Triangulations & Complexity Duality.

Grounding: Lezhi Lin and Jonathan Spreer (Sep 13, 2026), "Torus knots as loop-edges
in three-sphere triangulations", arXiv:2609.14200v1 [math.GT]. (HYP-255)

Mathematical Core:
1. Minimally Layered Solid Torus LST(a, b):
   - For coprime a <= b, built from base 0-tetrahedron Mobius band (slopes 1, 1, 2)
     via subtraction-form Euclidean algorithm (anthyphairesis).
   - Size |LST(a, b)| = \ell(a, b) equals the number of subtraction steps down to (1, 1).
2. Canonical Three-Sphere Triangulation:
   - For coprime P, Q >= 2, there exists a unique basis {(p, r), (q, s)} with
     p, q, r, s > 0 such that (p, r) + (q, s) = (P, Q) and |ps - qr| = 1.
   - Triangulation T = LST(p, q) \cup LST(r, s) is a 1-vertex triangulation of S^3.
   - The central interface edge represents the torus knot T(P, Q) = T(p + q, r + s).
   - Total tetrahedra: |T| = \ell(p, q) + \ell(r, s).
3. Complexity Duality:
   - Linear family T(2, 2k + 1):
       (p, q, r, s) = (1, 1, k, k + 1) => |T| = \ell(1, 1) + \ell(k, k + 1) = 0 + k = k.
       Crossing number c(K) = 2k + 1. Size is linear in crossing number.
   - Logarithmic family T(F_n, F_{n+1}) for even n >= 4:
       By Cassini's identity F_{n-1} F_{n+1} - F_n^2 = 1, unique split is:
         (p, q, r, s) = (F_{n-1}, F_{n-2}, F_n, F_{n-1}).
       Size |T| = \ell(F_{n-1}, F_{n-2}) + \ell(F_n, F_{n-1}) = (n - 3) + (n - 2) = 2n - 5.
       Crossing number c(K) = F_{n+1}(F_n - 1) grows exponentially ~ \phi^{2n+1}.
       Triangulation complexity is strictly O(log c(K)), proving an exponential speed-up.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, List, Tuple
import math


def euclidean_subtractions(a: int, b: int) -> int:
    r"""Compute the number of subtraction steps in the Euclidean algorithm (anthyphairesis)

    reducing the coprime pair (a, b) down to the base case (1, 1).
    \ell(1, 1) = 0.
    \ell(1, 2) = 1.
    \ell(k, k+1) = k.
    """
    if a < 1 or b < 1:
        raise ValueError("Inputs a, b must be positive integers")
    if math.gcd(a, b) != 1:
        raise ValueError("Inputs a, b must be coprime")

    if a > b:
        a, b = b, a

    steps = 0
    while (a, b) != (1, 1):
        if a > b:
            a, b = b, a
        b -= a
        steps += 1
    return steps


def canonical_heegaard_split(P: int, Q: int) -> Tuple[int, int, int, int]:
    r"""Find the canonical decomposition (p, q, r, s) of Proposition 4.3:

    p, q, r, s > 0,
    p + q = P,
    r + s = Q,
    |ps - qr| = 1.
    Normalized such that p is chosen via p*Q \equiv 1 (mod P).
    """
    if P < 2 or Q < 2:
        raise ValueError("P and Q must be at least 2")
    if math.gcd(P, Q) != 1:
        raise ValueError("P and Q must be coprime")

    # p * Q \equiv 1 (mod P)
    p = pow(Q, -1, P)
    q = P - p
    r = (p * Q - 1) // P
    s = Q - r

    if not (p > 0 and q > 0 and r > 0 and s > 0):
        # Fall back to alternative residue
        p = pow(-Q, -1, P)
        q = P - p
        r = (p * Q + 1) // P
        s = Q - r

    assert abs(p * s - q * r) == 1, f"Determinant condition failed: |{p}*{s} - {q}*{r}| != 1"
    assert p + q == P, "Sum p + q != P"
    assert r + s == Q, "Sum r + s != Q"

    return p, q, r, s


def torus_knot_triangulation_size(P: int, Q: int) -> int:
    r"""Compute the number of tetrahedra in the canonical one-vertex triangulation

    of S^3 realizing T(P, Q) as a loop-edge:
    |T| = \ell(p, q) + \ell(r, s).
    """
    p, q, r, s = canonical_heegaard_split(P, Q)
    return euclidean_subtractions(p, q) + euclidean_subtractions(r, s)


def torus_knot_crossing_number(P: int, Q: int) -> int:
    r"""Compute the minimal crossing number of the torus knot T(P, Q):

    c(T(P, Q)) = min{P(Q - 1), Q(P - 1)}.
    """
    return min(P * (Q - 1), Q * (P - 1))


def fibonacci_number(n: int) -> int:
    r"""Return the n-th Fibonacci number with F_1 = 1, F_2 = 1, F_3 = 2, ..."""
    if n <= 0:
        return 0
    a, b = 0, 1
    for _ in range(n - 1):
        a, b = b, a + b
    return b


def fibonacci_family_record(even_n: int) -> Dict[str, int]:
    r"""Compute the exact data for the Fibonacci family T(F_n, F_{n+1}) for even n >= 4:

    - P = F_n, Q = F_{n+1}
    - (p, q, r, s) = (F_{n-1}, F_{n-2}, F_n, F_{n-1})
    - |T| = 2n - 5
    - c(K) = F_{n+1}(F_n - 1)
    """
    if even_n < 4 or even_n % 2 != 0:
        raise ValueError("even_n must be an even integer >= 4")

    Fn_minus_2 = fibonacci_number(even_n - 2)
    Fn_minus_1 = fibonacci_number(even_n - 1)
    Fn = fibonacci_number(even_n)
    Fn_plus_1 = fibonacci_number(even_n + 1)

    p, q = Fn_minus_1, Fn_minus_2
    r, s = Fn, Fn_minus_1

    l1 = euclidean_subtractions(p, q)
    l2 = euclidean_subtractions(r, s)
    total_tet = l1 + l2

    c = Fn_plus_1 * (Fn - 1)

    return {
        "n": even_n,
        "P": Fn,
        "Q": Fn_plus_1,
        "p": p,
        "q": q,
        "r": r,
        "s": s,
        "l1": l1,
        "l2": l2,
        "total_tetrahedra": total_tet,
        "predicted_tetrahedra": 2 * even_n - 5,
        "crossing_number": c,
        "det": abs(p * s - q * r),
    }


def hyp255_master_verification() -> Tuple[bool, Dict]:
    r"""Master verification for HYP-255: Torus Knots as Loop-Edges in S^3 Triangulations."""
    results = {}

    # 1. Linear family check: T(2, 2k+1) has |T| = k and c = 2k+1
    linear_ok = True
    for k in range(1, 10):
        P, Q = 2, 2 * k + 1
        tet = torus_knot_triangulation_size(P, Q)
        c = torus_knot_crossing_number(P, Q)
        if tet != k or c != 2 * k + 1:
            linear_ok = False
            break
    results["linear_family"] = linear_ok

    # 2. Fibonacci family Table 2 exact reproduction:
    # n = 4:  T(3, 5)     -> tet = 3,  c = 10
    # n = 6:  T(8, 13)    -> tet = 7,  c = 91
    # n = 8:  T(21, 34)   -> tet = 11, c = 680
    # n = 10: T(55, 89)   -> tet = 15, c = 4806
    # n = 12: T(144, 233) -> tet = 19, c = 33319
    table_2_targets = [
        (4, 3, 5, 3, 10),
        (6, 8, 13, 7, 91),
        (8, 21, 34, 11, 680),
        (10, 55, 89, 15, 4806),
        (12, 144, 233, 19, 33319),
    ]
    fib_ok = True
    for n, P_exp, Q_exp, tet_exp, c_exp in table_2_targets:
        rec = fibonacci_family_record(n)
        if (
            rec["P"] != P_exp
            or rec["Q"] != Q_exp
            or rec["total_tetrahedra"] != tet_exp
            or rec["total_tetrahedra"] != rec["predicted_tetrahedra"]
            or rec["crossing_number"] != c_exp
            or rec["det"] != 1
        ):
            fib_ok = False
            break
    results["fibonacci_table_2"] = fib_ok

    # 3. Logarithmic scaling verification:
    # Check that across n=4..12, Delta tet = 4 while c grows by factor > 6.8
    growth_ok = True
    c_prev = 10
    for n in [6, 8, 10, 12]:
        rec = fibonacci_family_record(n)
        c_curr = rec["crossing_number"]
        ratio = c_curr / c_prev
        if ratio < 6.8:
            growth_ok = False
            break
        c_prev = c_curr
    results["logarithmic_scaling"] = growth_ok

    all_pass = all(results.values())
    return all_pass, results
