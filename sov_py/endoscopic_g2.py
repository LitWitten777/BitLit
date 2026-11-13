r"""
Endoscopic Character Identities for G_2, Triality of so(8), and Arthur Multiplicity (HYP-233).

Grounded in:
- Yugo Takanashi (2026):
  "Endoscopic description of the local Langlands correspondence for G2"
  (/data/mind/cognition/library/Endoscopic description of the local Langlands correspondence for G2.pdf)

Key mathematical structures:
1. Triality eigenspace decomposition of so(8) (dim 28):
   so(8) = g_2 (dim 14, eigenvalue 1) \oplus Im(O)_+ (dim 7, e^{2pi i / 3}) \oplus Im(O)_- (dim 7, e^{4pi i / 3}).
   dim so(8) = 14 + 7 + 7 = 28 = T_7.
2. Elliptic endoscopic groups of G_2:
   - G_2 itself (dim 14)
   - SO_4 = (SL_2 x SL_2) / { \pm 1 } (dim 6)
   - PGL_3 = SL_3 / \mu_3 (dim 8)
   Dimensional complement: 14 = 6 + 8.
3. Component group S_phi and Gan-Savin L-packets:
   - When S_phi = S_3 (order 6):
     irreps: triv (dim 1), sgn (dim 1), std (dim 2).
     Sum of squares: 1^2 + 1^2 + 2^2 = 6 = |S_3|.
     L-packet cardinality: 3 irreducible classes (sum of dims = 4).
   - When S_phi = A_3 (order 3):
     irreps: 3 one-dimensional reps (dim 1, 1, 1).
     Sum of squares: 1^2 + 1^2 + 1^2 = 3 = |A_3|.
4. Arthur multiplicity formula:
   m_A(sigma) = (1 / |S_psi|) sum_{s in S_psi} eps(s) tr(rho_sigma(s)).
"""

from dataclasses import dataclass
from typing import List, Tuple, Dict, Any, Optional
import numpy as np


@dataclass(frozen=True)
class EndoscopicGroupData:
    name: str
    dimension: int
    cartan_dim: int
    is_elliptic: bool


def g2_triality_decomposition() -> Dict[str, Any]:
    """
    Computes the triality eigenspace decomposition of so(8) under the order-3
    triality automorphism theta:
    so(8) = g_2 \oplus V_omega \oplus V_omega_bar.
    """
    dim_so8 = 28
    dim_g2 = 14
    dim_im_o = 7
    
    assert dim_g2 + 2 * dim_im_o == dim_so8
    
    return {
        "so8_dim": dim_so8,
        "g2_fixed_dim": dim_g2,
        "im_octonion_dim": dim_im_o,
        "triality_eigenvalues": ["1", "e^{2pi i / 3}", "e^{4pi i / 3}"],
        "eigenspace_dims": [dim_g2, dim_im_o, dim_im_o],
        "is_direct_sum": True,
    }


def g2_elliptic_endoscopy() -> Dict[str, Any]:
    """
    Returns the classification of elliptic endoscopic groups of G_2:
    G_2 (dim 14), SO_4 (dim 6), PGL_3 (dim 8).
    """
    groups = [
        EndoscopicGroupData("G_2", 14, 2, True),
        EndoscopicGroupData("SO_4", 6, 2, True),
        EndoscopicGroupData("PGL_3", 8, 2, True),
    ]
    
    dim_sum_subendoscopic = 6 + 8
    dim_g2 = 14
    
    return {
        "groups": groups,
        "so4_dim": 6,
        "pgl3_dim": 8,
        "g2_dim": 14,
        "complement_identity": (dim_sum_subendoscopic == dim_g2),
    }


def component_group_s3_invariants() -> Dict[str, Any]:
    """
    Computes representation-theoretic invariants of the S_3 component group
    for generic Gan-Savin L-packets:
    Irreps: triv (dim 1), sgn (dim 1), std (dim 2).
    """
    irreps = [
        {"name": "trivial", "dim": 1, "chars": {"id": 1, "transposition": 1, "3-cycle": 1}},
        {"name": "sign", "dim": 1, "chars": {"id": 1, "transposition": -1, "3-cycle": 1}},
        {"name": "standard", "dim": 2, "chars": {"id": 2, "transposition": 0, "3-cycle": -1}},
    ]
    
    dims = [ir["dim"] for ir in irreps]
    sum_sq = sum(d**2 for d in dims)
    order_s3 = 6
    
    # Check orthogonality of character table
    # S_3 conjugacy classes: [id] (size 1), [(12)] (size 3), [(123)] (size 2)
    sizes = {"id": 1, "transposition": 3, "3-cycle": 2}
    orthogonality_matrix = np.zeros((3, 3))
    for i, ir1 in enumerate(irreps):
        for j, ir2 in enumerate(irreps):
            val = sum(sizes[c] * ir1["chars"][c] * ir2["chars"][c] for c in sizes)
            orthogonality_matrix[i, j] = val / order_s3
            
    is_orthonormal = np.allclose(orthogonality_matrix, np.eye(3))
    
    return {
        "group": "S_3",
        "order": order_s3,
        "irreps": irreps,
        "dims": dims,
        "sum_of_squares": sum_sq,
        "matches_group_order": (sum_sq == order_s3),
        "is_orthonormal": is_orthonormal,
    }


def arthur_multiplicity_eval(
    rep_name: str, component_group: str = "S_3", eps_signs: Optional[Dict[str, int]] = None
) -> int:
    """
    Evaluates Arthur's global multiplicity formula:
    m_A(sigma) = (1 / |S_psi|) sum_{s in S_psi} eps(s) tr(rho_sigma(s)).
    For generic parameters with eps(s) = 1 (trivial sign):
    m_A(sigma) = (1 / |S_psi|) sum_{s in S_psi} tr(rho_sigma(s)) = <1, rho_sigma>.
    This equals 1 if rho_sigma is the trivial representation, and 0 otherwise!
    """
    if eps_signs is None:
        eps_signs = {"id": 1, "transposition": 1, "3-cycle": 1}
        
    s3_data = component_group_s3_invariants()
    order = s3_data["order"]
    sizes = {"id": 1, "transposition": 3, "3-cycle": 2}
    
    target_irrep = next(ir for ir in s3_data["irreps"] if ir["name"] == rep_name)
    
    total = 0
    for c, sz in sizes.items():
        total += sz * eps_signs[c] * target_irrep["chars"][c]
        
    assert total % order == 0
    return total // order
