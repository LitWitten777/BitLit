r"""
Hiraga-Ichino-Ikeda Formal Degree Conjecture for G_2 and Triality Transfers (HYP-235).

Grounded in:
- Yugo Takanashi (2026):
  "On the Hiraga-Ichino-Ikeda conjecture on formal degrees for G2"
  (/data/mind/cognition/library/On the Hiraga-Ichino-Ikeda conjecture on formal degrees for G2.pdf)

Key mathematical structures:
1. Hiraga-Ichino-Ikeda (HII) formal degree formula:
   For any discrete series representation \pi in the L-packet \Pi_\phi of G_2(F):
   d_\psi^{G_2}(\pi) = \frac{\dim(\rho_\pi) \cdot |\gamma^*(0, \phi, \operatorname{Ad}_{G_2}, \psi)|}{|S_\phi|}
   where \operatorname{Ad}_{G_2} is the 14-dimensional adjoint representation of G_2(C).
2. Weight ratios for S_3 component group (|S_3| = 6):
   - Trivial rep: dim = 1 => ratio = 1/6
   - Sign rep:    dim = 1 => ratio = 1/6
   - Standard rep:dim = 2 => ratio = 2/6 = 1/3
   Sum of squared dimensions: 1^2 + 1^2 + 2^2 = 6 = |S_3|.
3. Plancherel density decomposition:
   \mu_{HII, \psi}^{G_2}(\pi) = \langle \sigma, 1 \rangle \frac{|\gamma^*(0, \phi_\pi^{G_2}, \operatorname{Ad}_{G_2}, \psi)|}{|S_\sigma^\natural|}.
4. Exceptional Lie and Jordan algebra dimensions:
   - Octonions O: dim 8, Aut(O) = G_2 (dim 14)
   - Albert algebra J_3(O): dim 27 = 3 + 3 * 8
   - Aut(J_3(O)) = F_4 (dim 52 = 28 + 24)
   - Structure group = E_6 (dim 78 = 52 + 26)
   - Spin(8) triality: dim so(8) = 28.
"""

from dataclasses import dataclass
from typing import List, Tuple, Dict, Any, Optional
import numpy as np


@dataclass(frozen=True)
class HIIFormalDegreeRatio:
    rep_name: str
    dim: int
    group_order: int

    @property
    def ratio(self) -> float:
        return self.dim / self.group_order


def get_g2_hii_ratios() -> List[HIIFormalDegreeRatio]:
    """
    Returns the formal degree coefficient ratios dim(\rho_\pi) / |S_\phi|
    for discrete series representations of G_2 with S_3 component group.
    """
    return [
        HIIFormalDegreeRatio("trivial", 1, 6),
        HIIFormalDegreeRatio("sign", 1, 6),
        HIIFormalDegreeRatio("standard", 2, 6),
    ]


def verify_hii_formal_degree_partition() -> Dict[str, Any]:
    """
    Verifies the HII partition of unity for the S_3 component group:
    \sum_{\pi \in \Pi_\phi} \dim(\rho_\pi)^2 = |S_3| = 6.
    """
    ratios = get_g2_hii_ratios()
    dims = [r.dim for r in ratios]
    sum_sq = sum(d**2 for d in dims)
    order = 6
    
    # Check normalized sum of squares
    normalized_sum = sum(r.dim * r.ratio for r in ratios)
    
    return {
        "group_order": order,
        "irreps": [r.rep_name for r in ratios],
        "dims": dims,
        "sum_of_squares": sum_sq,
        "matches_order": (sum_sq == order),
        "normalized_sum": float(normalized_sum),
        "is_partition_of_unity": (normalized_sum == 1.0),
    }


def exceptional_albert_e6_chain() -> Dict[str, Any]:
    """
    Verifies the exceptional chain connecting O, G_2, Spin(8), Albert algebra J_3(O), F_4, and E_6:
    - O: dim 8
    - G_2 = Aut(O): dim 14
    - Spin(8) = SO(8): dim 28
    - J_3(O): dim 27 = 3 + 3*8
    - F_4 = Aut(J_3(O)): dim 52 = 28 + 24
    - E_6 = Isom(J_3(O)): dim 78 = 52 + 26
    """
    dim_o = 8
    dim_g2 = 14
    dim_so8 = 28
    dim_j3o = 3 + 3 * dim_o  # 27
    dim_f4 = dim_so8 + 3 * dim_o  # 28 + 24 = 52
    dim_e6 = dim_f4 + (dim_j3o - 1)  # 52 + 26 = 78
    
    return {
        "octonion_dim": dim_o,
        "g2_dim": dim_g2,
        "so8_dim": dim_so8,
        "albert_j3o_dim": dim_j3o,
        "f4_dim": dim_f4,
        "e6_dim": dim_e6,
        "chain_matches": (dim_j3o == 27 and dim_f4 == 52 and dim_e6 == 78),
    }
