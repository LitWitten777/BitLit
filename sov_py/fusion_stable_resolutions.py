"""Fusion-Stable Endosplit p-Permutation Resolutions and Splendid Rickard Equivalences.

Grounding:
    Xin Huang (2026),
    "Fusion-stable endosplit p-permutation resolutions",
    arXiv preprint in /data/mind/cognition/library/.

Key Mathematical Results:
1. Superclass Function Basis:
   - C(P) is the abelian group of integer-valued functions on Sub(P) constant on P-conjugacy classes.
   - For R <= P, omega_{P/R}(Q) = 1 if Q <=_P R, and 0 otherwise.
   - {omega_{P/R} | R in S} is a Z-basis of C(P), with upper triangular matrix and 1s on diagonal.
2. Borel-Smith Subgroup C_b(P):
   - (i) If p is odd and S <| T <= P with T/S = C_p, then f(S) - f(T) is even.
   - (ii) If S <| T <= P with T/S = C_p x C_p, then f(S) - f(T) = sum_{S < U < T} (f(U) - f(T)).
   - (iii) If p = 2 and S <| T <| N <= N_P(S) with T/S = C_2, then f(S) - f(T) is even when N/S = C_4,
     and divisible by 4 when N/S = Q_8.
3. Bouc-Yalcin Exact Sequence of p-Biset Functors:
   0 -> C_b -> C --(Psi)--> D_k^Omega -> 0
   where Psi_P(omega_{P/R}) = [Omega_{P/R}(k)] if R < P, and 0 if R = P.
4. Saturated Fusion Stability (Theorem 1.1):
   For a saturated fusion system F over P, an indecomposable capped endopermutation kP-module V
   with [V] in D_k^Omega(P) has an F-stable endosplit p-permutation resolution if and only if
   V is F-stable.
5. Splendid Rickard Equivalence (Theorem 1.2):
   If two blocks kGb and kHc are Morita equivalent via a bimodule with endopermutation kP-source V
   such that [V] in D_k^Omega(P), then kGb and kHc are splendidly Rickard equivalent.
"""

from typing import Dict, List, Tuple, Set, Optional
import itertools


class SuperclassFunction:
    """Integer-valued function on conjugacy classes of subgroups of a p-group."""

    def __init__(self, values: Dict[str, int]):
        self.values = values

    def __call__(self, sub: str) -> int:
        return self.values.get(sub, 0)

    def __add__(self, other: "SuperclassFunction") -> "SuperclassFunction":
        all_keys = set(self.values.keys()) | set(other.values.keys())
        return SuperclassFunction({k: self(k) + other(k) for k in all_keys})

    def __sub__(self, other: "SuperclassFunction") -> "SuperclassFunction":
        all_keys = set(self.values.keys()) | set(other.values.keys())
        return SuperclassFunction({k: self(k) - other(k) for k in all_keys})

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, SuperclassFunction):
            return False
        all_keys = set(self.values.keys()) | set(other.values.keys())
        return all(self(k) == other(k) for k in all_keys)


def build_cp_subgroups() -> List[str]:
    """Subgroup classes for P = C_p: ['1', 'P']."""
    return ["1", "P"]


def build_cp_omega_basis() -> Dict[str, SuperclassFunction]:
    """Basis functions omega_{P/R} for P = C_p:
    omega_{P/1}: 1 at '1', 0 at 'P'
    omega_{P/P}: 1 at '1', 1 at 'P'
    """
    return {
        "P/1": SuperclassFunction({"1": 1, "P": 0}),
        "P/P": SuperclassFunction({"1": 1, "P": 1}),
    }


def check_borel_smith_cp(f: SuperclassFunction, p: int) -> bool:
    """Check if f in C(C_p) satisfies the Borel-Smith condition.
    For p odd, condition (i) requires f('1') - f('P') to be even.
    """
    if p % 2 == 1:
        return (f("1") - f("P")) % 2 == 0
    return True


def build_cp_xcp_subgroups(p: int) -> Tuple[List[str], Dict[str, List[str]]]:
    """Subgroup classes for elementary abelian group P = C_p x C_p.
    Classes: '1', 'U_0', ..., 'U_p' (p+1 order-p subgroups), 'P'.
    Returns (list_of_subgroups, poset_containment).
    """
    subs = ["1"] + [f"U_{i}" for i in range(p + 1)] + ["P"]
    containment = {}
    for s in subs:
        containment[s] = []
    # '1' is contained in everything
    for s in subs:
        containment["1"].append(s)
    # Each U_i is contained in U_i and P
    for i in range(p + 1):
        u = f"U_{i}"
        containment[u] = [u, "P"]
    # P is contained only in P
    containment["P"] = ["P"]
    return subs, containment


def check_borel_smith_linear_cp_xcp(f: SuperclassFunction, p: int) -> bool:
    """Check condition (ii) on P = C_p x C_p with S = '1' and T = 'P':
    f(1) - f(P) == sum_{i=0}^p (f(U_i) - f(P))
    <=> f(1) + p * f(P) == sum_{i=0}^p f(U_i).
    """
    lhs = f("1") + p * f("P")
    rhs = sum(f(f"U_{i}") for i in range(p + 1))
    return lhs == rhs


def verify_bouc_yalcin_basis_triangularity(p: int = 2) -> bool:
    """Verify that the evaluation matrix [omega_{P/R}(Q)] is triangular with 1s on the diagonal."""
    subs, containment = build_cp_xcp_subgroups(p)
    n = len(subs)
    
    # Construct omega_{P/R} for each R
    omega_funcs = {}
    for r in subs:
        # omega_{P/R}(Q) = 1 if Q <= R
        # In our containment dict, R contains Q iff Q in some list, but containment[Q] contains R!
        # That is, Q <= R iff R in containment[Q].
        vals = {q: (1 if r in containment[q] else 0) for q in subs}
        omega_funcs[r] = SuperclassFunction(vals)

    # Check diagonal and triangularity (ordered from '1' to 'P')
    # If Q is strictly larger in order, omega_{P/R}(Q) must be 0 when R < Q
    for i, q in enumerate(subs):
        for j, r in enumerate(subs):
            val = omega_funcs[r](q)
            if i == j and val != 1:
                return False
            # If r is of smaller order than q, q cannot be <= r
            # Order ranking: '1' (order 1) < U_i (order p) < 'P' (order p^2)
            order_q = 1 if q == "1" else (p if q.startswith("U") else p * p)
            order_r = 1 if r == "1" else (p if r.startswith("U") else p * p)
            if order_q > order_r and val != 0:
                return False
    return True


def verify_fusion_stable_resolution_criterion(
    is_v_f_stable: bool,
    is_fusion_saturated: bool,
    dade_class_in_d_omega: bool
) -> Tuple[bool, str]:
    """Theorem 1.1 criterion:
    V has an F-stable endosplit p-permutation resolution iff V is F-stable (when F is saturated).
    """
    if not dade_class_in_d_omega:
        return False, "Dade class not in D_k^Omega(P)"
    if not is_fusion_saturated:
        return False, "Fusion system not saturated"
    
    # Theorem 1.1 states: If V is F-stable and F saturated, resolution exists.
    # Conversely, if resolution exists, V is F-stable.
    has_resolution = is_v_f_stable
    return has_resolution, "Equivalence holds by Theorem 1.1"


def verify_splendid_rickard_deduction(
    has_morita_bimodule: bool,
    source_in_d_omega: bool
) -> bool:
    """Theorem 1.2 folklore deduction:
    Morita equivalence with source in D_k^Omega(P) implies splendid Rickard equivalence.
    """
    return has_morita_bimodule and source_in_d_omega
