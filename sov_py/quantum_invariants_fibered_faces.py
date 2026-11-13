"""Quantum Invariants Indexed by Fibered Faces of the Thurston Polytope (Passaro, San Martin Suarez 2026).

Implements:
1. Multivariable Alexander Polynomial Newton Polytope and Cones:
   For an oriented link L with components ell:
   Delta_L(x_1, ..., x_ell) has support supp(Delta_L).
   For an extremal integral vertex v (monic monomial in Delta_L),
   cone C_v = Cone{w - v | w in supp(Delta_L), w != v}.
2. Inverse Alexander Expansion near v (Section 3):
   x^{-v} Delta_L(x) is a unit in Z_{C_v}[[x_1, ..., x_ell]].
   (Delta_L)^{-1}_v(x) = x^{-v} * sum_{k in C_v} c_k x^k with c_k in Z.
3. Gukov-Manolescu Invariants Family {F^{(2v)}_L(x, q)}_v:
   Indexed by fibered vertices v dual to fibered faces of the Thurston norm ball B_T.
   Leading term formula (Proposition 1.5):
   F_L(x, q) = eps_v * q^{alpha(L)} * x^{-chi(L)/2} + O(x^{-chi(L)/2 + 1})
   where alpha(L) = b_1(L)/2 - lambda(L) for homogeneous braid links.
4. Fibered Face Duality and Thurston Polytope:
   2 * N(Delta_L) subseteq B_T^vee.
   Vertices dual to fibered faces of B_T correspond to integral vertices of 2*N(Delta_L)
   where the two polytope boundaries agree (McMullen's theorem).
"""

from dataclasses import dataclass
from typing import Dict, List, Set, Tuple
import math


@dataclass(frozen=True)
class MonomialExponent:
    exponents: Tuple[int, ...]

    def __sub__(self, other: "MonomialExponent") -> "MonomialExponent":
        return MonomialExponent(tuple(a - b for a, b in zip(self.exponents, other.exponents)))

    def __add__(self, other: "MonomialExponent") -> "MonomialExponent":
        return MonomialExponent(tuple(a + b for a, b in zip(self.exponents, other.exponents)))

    def dot(self, functional: Tuple[int, ...]) -> int:
        return sum(e * f for e, f in zip(self.exponents, functional))


class MultivariablePolynomial:
    def __init__(self, terms: Dict[Tuple[int, ...], int]):
        """terms maps exponent tuple to integer coefficient."""
        self.terms = {k: v for k, v in terms.items() if v != 0}

    @property
    def support(self) -> List[MonomialExponent]:
        return [MonomialExponent(k) for k in self.terms.keys()]

    def is_monic_at(self, vertex: MonomialExponent) -> bool:
        coeff = self.terms.get(vertex.exponents, 0)
        return abs(coeff) == 1

    def find_positively_exposed_vertex(self, phi: Tuple[int, ...]) -> MonomialExponent:
        """Find vertex minimizing <phi, w> where phi_i > 0."""
        assert all(p > 0 for p in phi), "phi must be positively oriented"
        supp = self.support
        min_val = min(w.dot(phi) for w in supp)
        minimizers = [w for w in supp if w.dot(phi) == min_val]
        assert len(minimizers) == 1, f"Vertex not strictly exposed: {minimizers}"
        return minimizers[0]

    def expand_inverse_cone(self, v: MonomialExponent, max_order: int = 5) -> Dict[Tuple[int, ...], int]:
        """Expand x^{-v} / (1 - p(x)) where x^{-v} Delta_L = c_v (1 - p(x)).
        Returns series terms in C_v up to total degree max_order.
        """
        c_v = self.terms[v.exponents]
        assert abs(c_v) == 1, f"Not an integral vertex: c_v = {c_v}"

        # Shift polynomial so vertex is at origin with constant 1
        # p(x) = 1 - c_v * x^{-v} * Delta_L
        p_terms: Dict[Tuple[int, ...], int] = {}
        for exp_tuple, coeff in self.terms.items():
            if exp_tuple == v.exponents:
                continue
            shifted_exp = tuple(a - b for a, b in zip(exp_tuple, v.exponents))
            p_terms[shifted_exp] = -c_v * coeff

        # Formal geometric series 1 / (1 - p(x)) = 1 + p + p^2 + p^3 + ...
        # Since all terms in p have positive total degree in the cone, this converges formally.
        result: Dict[Tuple[int, ...], int] = {tuple(0 for _ in v.exponents): c_v}
        current_power = {tuple(0 for _ in v.exponents): 1}

        for _ in range(max_order):
            next_power: Dict[Tuple[int, ...], int] = {}
            for e1, c1 in current_power.items():
                for e2, c2 in p_terms.items():
                    e_sum = tuple(a + b for a, b in zip(e1, e2))
                    if sum(e_sum) <= max_order:
                        next_power[e_sum] = next_power.get(e_sum, 0) + c1 * c2
            for e, c in next_power.items():
                result[e] = result.get(e, 0) + c_v * c
            current_power = next_power

        return result


def gukov_manolescu_leading_term(
    chi_link: int,
    hopf_lambda: int,
    b1_link: int,
) -> Tuple[int, int]:
    """Proposition 1.5: Leading term exponents for homogeneous braid links:
    power of x: -chi(L) / 2
    power of q: alpha(L) = b_1(L)/2 - lambda(L).
    Returns (x_exponent_halves, q_exponent_halves) as integer halves.
    """
    x_half_exp = -chi_link  # exponent of x is -chi(L)/2, so halves = -chi
    q_exp = b1_link - 2 * hopf_lambda  # in units of 1/2
    return x_half_exp, q_exp


def hyp286_master_verification() -> bool:
    """Master verification function for HYP-286."""
    # 1. Test Hopf link L2a1: Delta(x_1, x_2) = (x_1 - 1)(x_2 - 1) / ...
    # For a 2-component link with Delta_L(x1, x2) = x1*x2 - x1 - x2 + 1:
    poly = MultivariablePolynomial({
        (1, 1): 1,
        (1, 0): -1,
        (0, 1): -1,
        (0, 0): 1,
    })
    phi = (1, 1)
    v_pos = poly.find_positively_exposed_vertex(phi)
    if v_pos.exponents != (0, 0):
        return False
    if not poly.is_monic_at(v_pos):
        return False

    # Expand inverse in cone C_v:
    inv_terms = poly.expand_inverse_cone(v_pos, max_order=4)
    # (1 - x1 - x2 + x1 x2)^{-1} = (1 - x1)^{-1} (1 - x2)^{-1} = sum x1^a x2^b
    # All coefficients should be exactly +1
    for i in range(3):
        for j in range(3):
            if inv_terms.get((i, j), 0) != 1:
                return False

    # 2. Leading term formula check for homogeneous braid link
    # e.g. chi = -2, b1 = 2, lambda = 0 => x power = -(-2)/2 = 1, q power = 2/2 - 0 = 1
    x_half, q_half = gukov_manolescu_leading_term(chi_link=-2, hopf_lambda=0, b1_link=2)
    if x_half != 2 or q_half != 2:
        return False

    return True
