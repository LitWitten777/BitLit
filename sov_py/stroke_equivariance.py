"""
src/sedenion/stroke_equivariance.py
=============================================================================
Stroke Space Isometric Embedding and Weyl Equivariance Witness
Resolving Claim 1 (Refinement Audit):
    ι_wedge ∘ R_{π/2} = W ∘ ι_wedge
where W ∈ W(D_8) ⊂ W(E_8).
=============================================================================
"""

import numpy as np
from typing import Tuple, Dict


class StrokeSpace:
    """
    Tier 0: Stroke Space (seed_pictographic_scripts.py)
    Orthonormal basis in R^3:
      |DIŠ⟩ = (1, 0, 0)^T  (Vertical wedge)
      |AŠ⟩  = (0, 1, 0)^T  (Horizontal wedge)
      |U⟩   = (0, 0, 1)^T  (Diagonal Winkelhaken)
    """
    DIS = np.array([1, 0, 0], dtype=np.int64)
    AS = np.array([0, 1, 0], dtype=np.int64)
    U = np.array([0, 0, 1], dtype=np.int64)

    # 90-degree CCW rotation matrix in (x,y) plane
    R_PI_2 = np.array([
        [0, -1, 0],
        [1,  0, 0],
        [0,  0, 1]
    ], dtype=np.int64)

    @classmethod
    def rotate(cls, v: np.ndarray) -> np.ndarray:
        return cls.R_PI_2 @ v


def iota_wedge(v: np.ndarray) -> np.ndarray:
    """
    Isometric embedding ι_wedge: R^3 -> R^8 into orthogonal 2-planes:
      ι(|DIŠ⟩) = e_1 + e_2
      ι(|AŠ⟩)  = e_3 + e_4
      ι(|U⟩)   = e_5 + e_6
    Indices in R^8 are 0-indexed (e_0, ..., e_7).
    """
    # v = [x, y, z] -> [0, x, x, y, y, z, z, 0]
    out = np.zeros(8, dtype=np.int64)
    out[1] = v[0]
    out[2] = v[0]
    out[3] = v[1]
    out[4] = v[1]
    out[5] = v[2]
    out[6] = v[2]
    return out


def weyl_witness_correct() -> np.ndarray:
    """
    Verified Weyl element W ∈ W(D_8) ⊂ W(E_8):
      e_1 ↦ e_3
      e_2 ↦ e_4
      e_3 ↦ -e_1
      e_4 ↦ -e_2
      e_0, e_5, e_6, e_7 fixed.
    
    Matrix representation W where W[i, j] = coeff of e_i in W(e_j).
    """
    W = np.zeros((8, 8), dtype=np.int64)
    W[0, 0] = 1
    W[3, 1] = 1   # e_1 -> e_3
    W[4, 2] = 1   # e_2 -> e_4
    W[1, 3] = -1  # e_3 -> -e_1
    W[2, 4] = -1  # e_4 -> -e_2
    W[5, 5] = 1   # e_5 -> e_5
    W[6, 6] = 1   # e_6 -> e_6
    W[7, 7] = 1   # e_7 -> e_7
    return W


def weyl_witness_flawed() -> np.ndarray:
    """
    Flawed witness from previous conversation that erroneously mixed e_0:
      e_0 ↦ e_2
      e_1 ↦ e_3
      e_2 ↦ -e_0
      e_3 ↦ -e_1
      e_k ↦ e_k (k >= 4)
    """
    W = np.zeros((8, 8), dtype=np.int64)
    W[2, 0] = 1   # e_0 -> e_2
    W[3, 1] = 1   # e_1 -> e_3
    W[0, 2] = -1  # e_2 -> -e_0
    W[1, 3] = -1  # e_3 -> -e_1
    for k in range(4, 8):
        W[k, k] = 1
    return W


def is_in_weyl_d8(matrix: np.ndarray) -> Tuple[bool, Dict[str, any]]:
    """
    Decision procedure: verifies if an 8x8 integer matrix belongs to W(D_8).
    Conditions for W(D_8) ≅ 2^7 ⋊ S_8:
    1. Orthogonal signed permutation: exactly one non-zero (±1) per row and column.
    2. Even number of sign changes (product of diagonal / row signs has parity +1).
    3. Transformation preserves root lattice D_8.
    """
    M = matrix
    if M.shape != (8, 8):
        return False, {"error": "Invalid shape"}
    
    # Check signed permutation
    abs_M = np.abs(M)
    is_signed_perm = (
        bool(np.all((M == 0) | (M == 1) | (M == -1))) and
        bool(np.all(np.sum(abs_M, axis=0) == 1)) and
        bool(np.all(np.sum(abs_M, axis=1) == 1))
    )
    if not is_signed_perm:
        return False, {"error": "Not a signed permutation"}
    
    # Count negative entries
    neg_count = int(np.sum(M == -1))
    even_signs = (neg_count % 2 == 0)
    det = int(round(np.linalg.det(M)))
    
    return even_signs, {
        "is_signed_permutation": is_signed_perm,
        "neg_count": neg_count,
        "even_signs": even_signs,
        "det": det,
        "in_W_D8": even_signs and is_signed_perm
    }


def verify_equivariance(W: np.ndarray) -> Tuple[bool, Dict[str, bool]]:
    """
    Decision procedure checking ι_wedge(R_{π/2}(v)) == W(ι_wedge(v))
    for all basis vectors.
    """
    results = {}
    all_ok = True
    for name, v in [("DIS", StrokeSpace.DIS), ("AS", StrokeSpace.AS), ("U", StrokeSpace.U)]:
        rotated_v = StrokeSpace.rotate(v)
        lhs = iota_wedge(rotated_v)
        rhs = W @ iota_wedge(v)
        match = bool(np.array_equal(lhs, rhs))
        results[name] = match
        if not match:
            all_ok = False
    return all_ok, results
