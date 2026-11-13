r"""
Unknotting Number and L-Space Satellite Operations.

Grounding: Daren Chen, Ian Zemke, and Hugo Zhou (Sep 13, 2026),
"Unknotting number and L-space satellite operations",
arXiv:2609.14520v1 [math.GT].

Key Invariants and Bounds:
1. Relative 3-genus shift:
   \theta(P) = g_3^{rel}(P) - g_3(P) = R_{\ell/2} - g_3(P) - |\ell|/2 \ge 0.
   For braided L-space patterns, \theta = 0, \ell \ge \omega > 0, \Xi \ge 0.
2. Invariants \omega, \kappa, \Xi:
   \omega = R_{\ell/2} - R_{\ell/2 - 1}
   \kappa = R_{\ell/2 - 1} - g_3(P) + \ell/2
   \Xi = \ell/2 + g_3(P) - R_{\ell/2 - 1} - 1
   Relation: \ell - \kappa = \omega - \theta = \Xi + 1.
3. General L-space satellite torsion bound (Theorem 1.4):
   For K != T_{2,3} nontrivial:
   Ord(P(K, \lambda)) \ge max{|\ell| * (Ord(K) - 1), |\ell|} + \theta.
4. Braided L-space satellite torsion bound (Theorem 1.5):
   Ord(P(K, \lambda)) \ge max{|\ell| * (Ord(K) - 1) + 1, |\ell|}.
5. Iterated unknotting number bounds (Theorems 1.1 and 1.2):
   u(K) \ge Ord(K) by Alishahi-Eftekhary.
   General: u(P_k \circ ... \circ P_1(K)) \ge
     |\ell_k|(...(|\ell_2|(|\ell_1| + \theta_1 - 1) + \theta_2 - 1)... - 1) + \theta_k.
   Braided: u(P_k \circ ... \circ P_1(K)) \ge |\ell_k * ... * \ell_1|.
6. Exceptional companion T_{2,3} bound (Theorem 5.11):
   Ord(P(T_{2,3}, \lambda)) \ge min{max{\ell, \omega}, max{\theta, \kappa} + 1} if \ell > 0,
   and \omega if \ell = 0.
"""

from dataclasses import dataclass
from typing import List, Tuple, Optional


@dataclass(frozen=True)
class LSpacePattern:
    """Represents an L-space satellite operator P in S^1 x D^2."""
    name: str
    ell: int           # winding number (linking number with meridian mu)
    g3: int            # three-genus of P(U) in S^3
    g3_rel: int        # relative three-genus in S^1 x D^2
    R_half_ell: int    # R_{\ell/2} from H-function
    R_half_ell_minus_1: int  # R_{\ell/2 - 1}
    is_braided: bool = False

    @property
    def theta(self) -> int:
        r"""\theta = g_3^{rel}(P) - g_3(P) = R_{\ell/2} - g_3(P) - |\ell|/2."""
        return self.g3_rel - self.g3

    @property
    def omega(self) -> int:
        r"""\omega = R_{\ell/2} - R_{\ell/2 - 1}."""
        return self.R_half_ell - self.R_half_ell_minus_1

    @property
    def kappa(self) -> int:
        r"""\kappa = R_{\ell/2 - 1} - g_3(P) + \ell/2."""
        return self.R_half_ell_minus_1 - self.g3 + abs(self.ell) // 2

    @property
    def xi(self) -> int:
        r"""\Xi = \ell/2 + g_3(P) - R_{\ell/2 - 1} - 1."""
        return abs(self.ell) // 2 + self.g3 - self.R_half_ell_minus_1 - 1

    def verify_redundancy_relation(self) -> bool:
        r"""Verify: \ell - \kappa = \omega - \theta = \Xi + 1."""
        l = abs(self.ell)
        rel1 = l - self.kappa
        rel2 = self.omega - self.theta
        rel3 = self.xi + 1
        return rel1 == rel2 == rel3


def general_torsion_bound(P: LSpacePattern, ord_K: int) -> int:
    r"""Theorem 1.4: Ord(P(K, \lambda)) \ge max{|\ell|*(Ord(K)-1), |\ell|} + \theta."""
    l = abs(P.ell)
    base = max(l * (ord_K - 1), l)
    return base + P.theta


def braided_torsion_bound(P: LSpacePattern, ord_K: int) -> int:
    r"""Theorem 1.5: Ord(P(K, \lambda)) \ge max{|\ell|*(Ord(K)-1) + 1, |\ell|}."""
    assert P.is_braided, "Pattern must be braided"
    l = abs(P.ell)
    return max(l * (ord_K - 1) + 1, l)


def t23_torsion_bound(P: LSpacePattern) -> int:
    r"""Theorem 5.11: Ord(P(T_{2,3}, \lambda)) lower bound."""
    l = abs(P.ell)
    if l > 0:
        return min(max(l, P.omega), max(P.theta, P.kappa) + 1)
    else:
        return P.omega


def iterated_general_unknotting_bound(patterns: List[LSpacePattern], ord_K: int) -> int:
    r"""
    Theorem 1.2: General iterated L-space satellite bound.
    Iteratively applies Theorem 1.4.
    """
    current_ord = ord_K
    for P in patterns:
        current_ord = general_torsion_bound(P, current_ord)
    return current_ord


def iterated_braided_unknotting_bound(patterns: List[LSpacePattern]) -> int:
    r"""Theorem 1.1: u(P_k ... P_1(K)) \ge |\ell_k * ... * \ell_1|."""
    prod = 1
    for P in patterns:
        assert P.is_braided
        prod *= abs(P.ell)
    return prod


def ending_arrow_braided_bounds(
    ell: int, omega: int, n: int, eps_K: int, eta: int, lam_diff: int
) -> int:
    r"""
    Proposition 5.12 certified lower bounds for braided patterns:
    eps_K \in {+1, -1}, eta is sign (+1 or -1), lam_diff = \lambda - 2\tau(K).
    """
    if eps_K == 1:
        if eta > 0:
            if lam_diff <= -2:
                return ell * (n - 1) + 1
            elif lam_diff == -1:
                return ell * (n - 1) + omega
            else:
                return ell * n
        else:  # eta < 0
            if lam_diff <= -2:
                return ell * n - omega + 1
            elif lam_diff == -1:
                return ell * n
            else:
                return ell * (n + 1) - omega
    else:  # eps_K == -1
        if eta > 0:
            if lam_diff < 0:
                return ell * (n + 1) - omega
            else:
                return ell * n
        else:  # eta < 0
            if lam_diff < 0:
                return ell * n - omega + 1
            else:
                return ell * (n - 1) + 1


def non_ending_arrow_braided_bounds(ell: int, omega: int, n: int, arrow_type: str) -> int:
    r"""
    Proposition 5.6 certified lower bounds for non-ending arrows in CFK(K):
    arrow_type in {'(+,+)', '(-,+)', '(+,-)', '(-,-)'}.
    """
    if arrow_type == "(+,+)":
        return ell * n
    elif arrow_type == "(-,+)":
        return ell * (n - 1) + 1
    elif arrow_type == "(+,-)":
        return ell * (n + 1) - omega
    elif arrow_type == "(-,-)":
        return ell * n - omega + 1
    else:
        raise ValueError(f"Unknown arrow type {arrow_type}")
