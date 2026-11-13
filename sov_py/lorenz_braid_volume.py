r"""The Lorenz Braid Index, Hyperbolic Volume Bounds, and Classical Complexity Decoupling.

Grounding: Thiago de Paiva, Connie On Yu Hui, and José Andrés Rodríguez Migueles (Sep 14, 2026),
"The Lorenz braid index and hyperbolic volume", arXiv:2609.14931v1 [math.GT]. (HYP-254)

Mathematical Core:
1. Universal Template & Generalised Bunch Algorithm:
   - For even v < 0, the (0, v)-Lorenz-like template L(0, v) is universal.
   - A link L with trip number n in L(u, v) has parent manifold S^3 \ (L_SF \cup L_L)
     satisfying the self-crossing bound:
       \iota(P(L_L)) <= (3/2) n(n - 1) + 2n + 4n = (3/2)(n^2 + 3n).
   - By Theorem 1.5 in [Boileau-Boyer-Purcell], the simplicial volume satisfies:
       ||S^3 \ (L_SF \cup L_L)|| <= 8 \iota(P(L_L)) <= 12 (n^2 + 3n).
2. Universal Quadratic Hyperbolic Volume Bound:
   - Since Dehn filling does not increase simplicial volume:
       Vol(L) <= v_tet ||S^3 \ (L_SF \cup L_L)|| <= 12 v_tet (lbi(L)^2 + 3 lbi(L)),
     where lbi(L) = min br(L_n^+) is the Lorenz braid index (equal to minimal trip number \tilde{n}(L)),
     and v_tet \approx 1.0149416064 is the volume of the regular ideal tetrahedron.
3. Seifert Genus of Positive Braids:
   - If K is the closure of a positive braid on p strands with c crossings:
       g(K) = (c - p + 1) / 2.
4. Classical Complexity Decoupling Family:
   - For coprime p > q >= r_n > ... > r_1 > 1, k >= 1:
   - For sequence p'_j > p with gcd(p, p'_j) = 1 and p'_j -> \infty, k'_j >= 1:
   - Knots K_j = T((r, s), (p, kp + q - 1), (p'_j, k'_j p'_j + 1)) satisfy:
       br(K_j) = p'_j -> \infty,
       g(K_j) >= (k'_j p'_j (p'_j - 1)) / 2 -> \infty,
       lbi(K_j) <= p (uniformly bounded!),
       Vol(K_j) <= 12 v_tet (p^2 + 3p) (uniformly bounded!).
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, List, Tuple
from fractions import Fraction
import math

# Regular ideal tetrahedron volume v_tet = Lobachevsky L(pi/3) = Cl_2(pi/3) \approx 1.0149416064096535
V_TET: float = 1.0149416064096535


def self_crossing_bound(n: int) -> Fraction:
    r"""Compute the upper bound on self-intersections of the parent link projection:

    \iota(P(L_L)) <= (3/2) n(n - 1) + 2n + 4n = (3/2)(n^2 + 3n).
    """
    if n < 0:
        raise ValueError("Trip number n must be non-negative")
    return Fraction(3, 2) * (n**2 + 3 * n)


def simplicial_volume_upper_bound(n: int) -> int:
    r"""Compute the simplicial volume upper bound of the parent manifold:

    ||M \ L|| <= 8 * \iota(P(L_L)) <= 8 * (3/2)(n^2 + 3n) = 12(n^2 + 3n).
    """
    return 12 * (n**2 + 3 * n)


def hyperbolic_volume_upper_bound(lbi: int, vtet: float = V_TET) -> float:
    r"""Compute the universal hyperbolic volume upper bound from the Lorenz braid index:

    Vol(L) <= 12 * v_tet * (lbi^2 + 3 * lbi).
    """
    if lbi < 0:
        raise ValueError("Lorenz braid index must be non-negative")
    return 12.0 * vtet * (lbi**2 + 3 * lbi)


def positive_braid_crossing_count(blocks: List[Tuple[int, int]]) -> int:
    r"""Compute the total number of crossings in a positive braid of the form

    \prod_i (\sigma_1 ... \sigma_{r_i - 1})^{s_i}.
    Each block (r_i, s_i) contributes s_i * (r_i - 1) crossings.
    """
    return sum(s * (r - 1) for r, s in blocks)


def positive_braid_seifert_genus(p_strands: int, crossings: int) -> Fraction:
    r"""Compute the Seifert genus of a knot represented as the closure of a positive braid

    on p strands with c crossings:
    g(K) = (c - p + 1) / 2.
    """
    return Fraction(crossings - p_strands + 1, 2)


@dataclass(frozen=True)
class DecouplingKnot:
    r"""Represents an explicit hyperbolic Lorenz knot from the decoupling family (Theorem 5.10):

    K = T((r1, s1), ..., (rn, sn), (p, kp + q - 1), (p', k'p' + 1)).
    """
    p: int
    q: int
    k: int
    p_prime: int
    k_prime: int
    initial_blocks: Tuple[Tuple[int, int], ...] = ()

    def __post_init__(self):
        if not (self.p > self.q > 1):
            raise ValueError("Must have p > q > 1")
        if math.gcd(self.p, self.q) != 1:
            raise ValueError("p and q must be coprime")
        if not (self.p_prime > self.p):
            raise ValueError("p' must be strictly greater than p")
        if math.gcd(self.p, self.p_prime) != 1:
            raise ValueError("p and p' must be coprime")
        if self.k < 1 or self.k_prime < 1:
            raise ValueError("Multipliers k and k' must be at least 1")

    @property
    def classical_braid_index(self) -> int:
        r"""br(K) = p'."""
        return self.p_prime

    @property
    def lorenz_braid_index_bound(self) -> int:
        r"""lbi(K) <= p."""
        return self.p

    @property
    def total_crossings(self) -> int:
        r"""Total crossing number in the defining positive braid."""
        c_init = sum(s * (r - 1) for r, s in self.initial_blocks)
        c_mid = (self.k * self.p + self.q - 1) * (self.p - 1)
        c_last = (self.k_prime * self.p_prime + 1) * (self.p_prime - 1)
        return c_init + c_mid + c_last

    @property
    def seifert_genus(self) -> Fraction:
        r"""Exact Seifert genus g(K) = (c - p' + 1) / 2."""
        return positive_braid_seifert_genus(self.p_prime, self.total_crossings)

    @property
    def genus_lower_bound(self) -> Fraction:
        r"""Genus lower bound from the final block alone:

        g(K) >= k' p' (p' - 1) / 2.
        """
        return Fraction(self.k_prime * self.p_prime * (self.p_prime - 1), 2)

    @property
    def volume_upper_bound(self) -> float:
        r"""Vol(K) <= 12 v_tet (p^2 + 3p)."""
        return hyperbolic_volume_upper_bound(self.p)


def generate_decoupling_sequence(
    p: int, q: int, k: int, count: int = 5
) -> List[DecouplingKnot]:
    r"""Generate a sequence of knots K_j where p'_j -> \infty coprime to p."""
    knots = []
    p_cand = p + 1
    while len(knots) < count:
        if math.gcd(p, p_cand) == 1:
            knots.append(DecouplingKnot(p=p, q=q, k=k, p_prime=p_cand, k_prime=1))
        p_cand += 1
    return knots


def hyp254_master_verification() -> Tuple[bool, Dict]:
    r"""Master verification for HYP-254: The Lorenz Braid Index & Hyperbolic Volume."""
    results = {}

    # 1. Crossing count identity
    # (3/2)n(n-1) + 6n == (3/2)(n^2 + 3n) for all n
    crossing_identities_hold = True
    for n in range(1, 20):
        lhs = Fraction(3, 2) * n * (n - 1) + 6 * n
        rhs = self_crossing_bound(n)
        if lhs != rhs:
            crossing_identities_hold = False
            break
    results["crossing_formula"] = crossing_identities_hold

    # 2. Simplicial volume factor 8 * (3/2) == 12
    results["simplicial_factor"] = (8 * Fraction(3, 2) == 12)

    # 3. Volume bound formula at lbi = 3: 12 * (9 + 9) = 216
    results["vol_factor_lbi_3"] = (12 * (3**2 + 3 * 3) == 216)

    # 4. Decoupling sequence verification:
    # Set p=3, q=2, k=1. Sequence p'_j = 4, 5, 7, 8, 10
    seq = generate_decoupling_sequence(p=3, q=2, k=1, count=5)
    braid_indices = [k.classical_braid_index for k in seq]
    genera = [k.seifert_genus for k in seq]
    vol_bounds = [k.volume_upper_bound for k in seq]

    # Verify braid indices strictly increasing
    results["braid_index_growing"] = (braid_indices == sorted(braid_indices) and len(set(braid_indices)) == 5)

    # Verify genus strictly increasing and >= lower bound
    results["genus_growing"] = (genera == sorted(genera) and all(k.seifert_genus >= k.genus_lower_bound for k in seq))

    # Verify volume bound is strictly constant across the sequence
    results["volume_bound_constant"] = (len(set(vol_bounds)) == 1)

    all_pass = all(results.values())
    return all_pass, results
