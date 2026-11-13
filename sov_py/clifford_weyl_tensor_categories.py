"""Clifford and Weyl Algebras in Symmetric Tensor Categories: Symplectic Witt Groups and Stiefel-Whitney Classes.

Grounding:
    Pavel Etingof (2026),
    "Clifford and Weyl algebras in symmetric tensor categories",
    arXiv:2607.16910v1 [math.RT].

Key Theoretical Results:
1. Category C = Rep(G) ⊠ sVec ≃ Rep(Γ, t) where Γ = G × ⟨t⟩, t^2 = 1.
2. For an orthogonal representation X of G with dim(X) = n:
   - w_1(X) ∈ K = H^1(G, Z/2) with det(X) = (-1)^{w_1(X)}.
   - w_2(X) ∈ H^2(G, Z/2), b_G(X) = j(w_2(X)) ∈ A[2] where A = H^2(G, k^×).
   - β_X ∈ H^2(Γ, k^×) has Künneth image Θ(β_X) = (b_G(X), w_1(X)).
3. Modified multiplication on H^2_*(Γ, k^×) ≅ A × K:
   - (a, χ) * (b, η) = (a · b · j(χ ⌣ η), χ + η).
   - Since j(χ ⌣ χ) = 1 in A[2], (a, χ) * (a, χ) = (a^2, 0).
   - Hence the 2-torsion subgroup as a set is:
     H^2_*(Γ, k^×)[2] = A[2] × K.
4. Whitney Sum Formula:
   - w_1(X ⊕ Y) = w_1(X) + w_1(Y).
   - w_2(X ⊕ Y) = w_2(X) + w_2(Y) + w_1(X) ⌣ w_1(Y).
   - b_G(X ⊕ Y) = b_G(X) · b_G(Y) · j(w_1(X) ⌣ w_1(Y)).
   - Θ(β_{X ⊕ Y}) = Θ(β_X) * Θ(β_Y).
5. Symplectic Witt Group:
   - SW^+(C) = SW(G) × K as sets, where SW(G) = ⟨b_G(X)⟩ ⊂ A[2].
   - ι(SW(C)) = SW(G) × K × μ_2 ⊂ Br_2(C).
   - ι: SW(C) → Br_2(C) is surjective iff SW(G) = H^2(G, k^×)[2] = A[2].
   - If G is abelian, j ∘ ⌣: ⋀^2 H^1(G, Z/2) → H^2(G, k^×)[2] is surjective, so SW(G) = A[2],
     and ι is always surjective.
"""

from typing import Tuple, Dict, List
import itertools


class ModifiedCohomologyGroup:
    """Represents the modified multiplication on H^2_*(Γ, k^×) ≅ A × K.
    
    A is an abelian group (e.g. elementary abelian 2-group).
    K is an elementary abelian 2-group (Z/2)^m.
    cup_product is an alternating bilinear form K × K → A[2].
    """

    def __init__(self, k_dim: int, cup_matrix: List[List[int]]):
        """cup_matrix is a k_dim x k_dim skew/alternating matrix over F_2
        representing j(χ_i ⌣ χ_j) ∈ Z/2.
        """
        self.k_dim = k_dim
        self.cup_matrix = cup_matrix
        for i in range(k_dim):
            assert cup_matrix[i][i] == 0

    def cup(self, chi: Tuple[int, ...], eta: Tuple[int, ...]) -> int:
        """Evaluate j(χ ⌣ η) as a sum over pairs."""
        val = 0
        for i in range(self.k_dim):
            for j in range(self.k_dim):
                val ^= (chi[i] * eta[j] * self.cup_matrix[i][j])
        return val

    def star_product(
        self,
        elem1: Tuple[int, Tuple[int, ...]],
        elem2: Tuple[int, Tuple[int, ...]]
    ) -> Tuple[int, Tuple[int, ...]]:
        """Compute (a, χ) * (b, η) = (a ⊕ b ⊕ j(χ ⌣ η), χ ⊕ η)."""
        a, chi = elem1
        b, eta = elem2
        c_cup = self.cup(chi, eta)
        res_a = a ^ b ^ c_cup
        res_chi = tuple((x ^ y) for x, y in zip(chi, eta))
        return (res_a, res_chi)

    def star_square(self, elem: Tuple[int, Tuple[int, ...]]) -> Tuple[int, Tuple[int, ...]]:
        """(a, χ) * (a, χ) = (a ⊕ a ⊕ j(χ ⌣ χ), χ ⊕ χ) = (0, 0) in additive notation."""
        return self.star_product(elem, elem)


def verify_star_square_is_square() -> bool:
    """Verifies that for any alternating cup form, (a, χ) * (a, χ) = (a^2, 0).
    In F_2 notation, (a ⊕ a ⊕ 0, 0) = (0, 0), so every element has order 2 under *.
    """
    cup_mat = [[0, 1], [1, 0]]
    group = ModifiedCohomologyGroup(k_dim=2, cup_matrix=cup_mat)
    
    for a in [0, 1]:
        for chi in itertools.product([0, 1], repeat=2):
            elem = (a, chi)
            sq = group.star_square(elem)
            if sq != (0, (0, 0)):
                return False
    return True


def verify_whitney_sum_formula(
    w1_X: Tuple[int, ...],
    w2_X: int,
    w1_Y: Tuple[int, ...],
    w2_Y: int,
    cup_matrix: List[List[int]]
) -> bool:
    """Verifies that b_G(X ⊕ Y) and w_1(X ⊕ Y) match the modified star product:
    Θ(β_{X ⊕ Y}) = (b_G(X ⊕ Y), w_1(X ⊕ Y))
                 = (b_G(X) ⊕ b_G(Y) ⊕ j(w1_X ⌣ w1_Y), w1_X ⊕ w1_Y)
                 = (b_G(X), w1_X) * (b_G(Y), w1_Y).
    """
    group = ModifiedCohomologyGroup(k_dim=len(w1_X), cup_matrix=cup_matrix)
    theta_X = (w2_X, w1_X)
    theta_Y = (w2_Y, w1_Y)
    
    star_res = group.star_product(theta_X, theta_Y)
    
    w1_sum = tuple(x ^ y for x, y in zip(w1_X, w1_Y))
    w2_sum = w2_X ^ w2_Y ^ group.cup(w1_X, w1_Y)
    
    return star_res == (w2_sum, w1_sum)


def verify_abelian_group_surjectivity() -> Dict[str, bool]:
    """For G = (Z/2)^2:
    K = H^1(G, Z/2) has dimension 2 (size 4).
    H^2(G, C^×)[2] ≅ ⋀^2 H^1(G, Z/2) has dimension 1 (size 2).
    A[2] = {0, 1}.
    Since the cup product j(χ_1 ⌣ χ_2) = 1 spans A[2],
    SW(G) = A[2], and ι(SW(C)) = SW(G) × K × μ_2 = A[2] × K × μ_2 = Br_2(C).
    Thus ι is surjective.
    """
    cup_mat = [[0, 1], [1, 0]]
    group = ModifiedCohomologyGroup(k_dim=2, cup_matrix=cup_mat)
    
    chi1 = (1, 0)
    chi2 = (0, 1)
    
    theta_L1 = (0, chi1)
    theta_L2 = (0, chi2)
    
    theta_sum = group.star_product(theta_L1, theta_L2)
    has_nonzero_w2 = (theta_sum[0] == 1)
    
    return {
        "cup_spans_a2": has_nonzero_w2,
        "sw_g_equals_a2": has_nonzero_w2,
        "iota_surjective": has_nonzero_w2,
    }


def compute_symplectic_witt_orders(k_dim: int, a2_dim: int) -> Dict[str, int]:
    """Computes group orders for C = Rep(G) ⊠ sVec:
    |K| = 2^{k_dim}
    |A[2]| = 2^{a2_dim}
    |μ_2| = 2
    |Br_2(C)| = |A[2]| × |K| × |μ_2| = 2^{a2_dim + k_dim + 1}.
    """
    card_k = 1 << k_dim
    card_a2 = 1 << a2_dim
    card_mu2 = 2
    card_br2 = card_a2 * card_k * card_mu2
    return {
        "card_K": card_k,
        "card_A2": card_a2,
        "card_mu2": card_mu2,
        "card_Br2": card_br2,
    }
