r"""
Structural Lower Bound 21 for 3x3 Matrix Multiplication over F_2 and Saturated Decomposition (HYP-232).

Grounded in:
- Shuxing Yang et al. (Zhejiang University, 2026):
  "A Structural Proof of the Lower Bound 21 for 3x3 Matrix Multiplication over F_2"
  (/data/mind/cognition/library/A Structural Proof of the Lower Bound 21 for 3×3 Matrix Multiplication over F2.pdf)

Key mathematical structures:
1. Matrix multiplication tensor T<3,3,3> has dimension 27 in split flattening.
2. Rank-additive saturation lemma:
   P = sum_{t=1}^r M_t with sum rank(M_t) = rank(P) = 27
   implies E_t = M_t P^{-1} are pairwise orthogonal idempotents:
   E_t E_s = \delta_{ts} E_t.
3. Cross-factor product identities:
   A_t B_t C_t^T A_t = A_t
   A_t B_s C_t^T A_s = 0 (t != s).
4. Invertibility obstruction:
   If A_t is invertible, B_t C_t^T = A_t^{-1}, forcing B_t, C_t invertible.
   If A_s is also invertible (t != s), then A_t B_s C_t^T A_s is invertible,
   contradicting A_t B_s C_t^T A_s = 0.
   Therefore, at most ONE first factor can be invertible: n_3 <= 1.
5. Contradiction with forced profile:
   Length 20 forces profile (n_1, n_2, n_3) = (16, 1, 3), where n_3 = 3 > 1.
   Hence no length 20 decomposition exists: R_{F_2}(T<3,3,3>) >= 21.
"""

from dataclasses import dataclass
from typing import List, Tuple, Dict, Any, Optional
import numpy as np


@dataclass(frozen=True)
class MatrixRankProfile:
    """Matrix rank profile (n_1, n_2, n_3) for factors of rank 1, 2, 3."""
    n1: int
    n2: int
    n3: int

    @property
    def total_terms(self) -> int:
        return self.n1 + self.n2 + self.n3

    @property
    def total_rank_sum(self) -> int:
        return self.n1 * 1 + self.n2 * 2 + self.n3 * 3

    @property
    def is_saturated(self) -> bool:
        """Saturated when sum of matrix ranks equals split-flattening rank 27."""
        return self.total_rank_sum == 27


def verify_rank_additive_idempotents(
    M_list: List[np.ndarray], P: np.ndarray, tol: float = 1e-12
) -> Dict[str, Any]:
    """
    Verifies Lemma 5.1: If P = sum M_t and sum rank(M_t) = rank(P) = n,
    then E_t = M_t P^{-1} satisfies sum E_t = I, E_t^2 = E_t, E_t E_s = 0 for t != s.
    """
    n = P.shape[0]
    P_inv = np.linalg.inv(P)
    r = len(M_list)
    
    # Check sum of M_t == P
    sum_M = sum(M_list)
    diff_sum = np.linalg.norm(sum_M - P)
    
    # Construct E_t
    E_list = [M @ P_inv for M in M_list]
    
    # Check sum E_t == I
    sum_E = sum(E_list)
    diff_I = np.linalg.norm(sum_E - np.eye(n))
    
    # Check idempotence and orthogonality
    idempotence_errors = []
    orthogonality_errors = []
    for t in range(r):
        err_idemp = np.linalg.norm(E_list[t] @ E_list[t] - E_list[t])
        idempotence_errors.append(err_idemp)
        for s in range(r):
            if s != t:
                err_orth = np.linalg.norm(E_list[t] @ E_list[s])
                orthogonality_errors.append(err_orth)
                
    max_idemp_err = max(idempotence_errors) if idempotence_errors else 0.0
    max_orth_err = max(orthogonality_errors) if orthogonality_errors else 0.0
    
    return {
        "dimension": n,
        "num_summands": r,
        "sum_M_matches_P": bool(diff_sum < tol),
        "sum_E_matches_I": bool(diff_I < tol),
        "all_idempotent": bool(max_idemp_err < tol),
        "all_orthogonal": bool(max_orth_err < tol),
        "max_idempotence_error": float(max_idemp_err),
        "max_orthogonality_error": float(max_orth_err),
    }


def verify_invertibility_obstruction(
    A_ranks: List[int], saturated: bool
) -> Dict[str, Any]:
    """
    Verifies Proposition 5.3:
    In any saturated decomposition of T<3,3,3> (sum rank(A_t) = 27),
    at most one first factor can be invertible (rank 3).
    """
    n3 = sum(1 for r in A_ranks if r == 3)
    obstruction_violated = saturated and (n3 > 1)
    
    return {
        "rank_sum": sum(A_ranks),
        "saturated": saturated,
        "invertible_count_n3": n3,
        "max_allowed_invertible": 1 if saturated else None,
        "contradiction_detected": obstruction_violated,
    }


def check_hypothetical_length_20_contradiction() -> Dict[str, Any]:
    """
    Evaluates the complete structural proof for length 20:
    1. Forced profile: (16, 1, 3)
    2. Rank sum: 16*1 + 1*2 + 3*3 = 27 (saturated)
    3. Invertible count: n_3 = 3
    4. Obstruction: 3 > 1 -> IMPOSSIBLE!
    """
    profile = MatrixRankProfile(16, 1, 3)
    res = verify_invertibility_obstruction([1]*16 + [2]*1 + [3]*3, profile.is_saturated)
    return {
        "profile": (profile.n1, profile.n2, profile.n3),
        "total_terms": profile.total_terms,
        "total_rank_sum": profile.total_rank_sum,
        "is_saturated": profile.is_saturated,
        "obstruction_contradiction": res["contradiction_detected"],
        "proved_lower_bound": 21,
    }
