"""Gauged AKSZ Sigma Models, Higher Courant Algebroids, and Homotopy Momentum Maps.

Grounding:
    Noriaki Ikeda (Sep 16, 2026),
    "Gauged AKSZ sigma models",
    arXiv:2609.16043v1 [math-ph].

Key Mathematical Results:
1. Target Graded Manifold:
   - Target QP-manifold N = T*[n](T[1]M ⊕ A[1]) of degree n.
   - Homological vector field Q = Q_S + Q_A + Q_F satisfying Q^2 = 0, or {Θ_∇, Θ_∇} = 0.
2. Flatness & Lie Algebroid Horizontal Anchor (Theorem 5.1 & Proposition 5.2):
   - Affine curvature R = 0, vector bundle curvature F = 0, basic curvature AS = 0.
   - Anchor map is horizontal: ∇ρ = 0.
   - E is locally isomorphic to an action Lie algebroid M × g.
3. Flux Cocycle & Descent Chain (Theorem 6.1):
   - dH = 0 for H = H^(n+1) ∈ Ω^{n+1}(M).
   - A_d^∇ H^(s+1) - ∇ H^(s) = 0 for s = 0, ..., n.
   - A_d^∇ H^(0) = 0.
   - Solution when A-torsion T = 0: H^(s) = (ι_ρ)^{n+1-s} H.
4. Classical Master Equation (CME, Corollary 6.2):
   - {S_GF^∇, S_GF^∇} = 0 iff the conditions in Theorem 6.1 hold.
5. Boundary Homotopy Momentum Sections (Theorem 6.3):
   - On boundary T[1]∂Σ with Lagrangian boundary conditions Z^i = 0, P_i = 0, W_a = 0:
     d μ^(n) - H = 0
     A_d^∇ μ^(s+1) + ∇ μ^(s) - H^(s+1) = 0,  s = 0, ..., n-1
     A_d^∇ μ^(0) - H^(0) = 0.
   - For an action Lie algebroid M × g with equivariant action, μ^(s) are genuine homotopy moment maps.
"""

from typing import Dict, List, Tuple, Optional, Callable


class GaugedAKSZTarget:
    """Represents the graded QP-manifold target data for a gauged AKSZ sigma model."""

    def __init__(
        self,
        n_dim: int,
        m_dim: int,
        g_dim: int,
        is_r_flat: bool = True,
        is_f_flat: bool = True,
        is_as_flat: bool = True,
        is_anchor_horizontal: bool = True,
        is_flux_closed: bool = True
    ):
        self.n_dim = n_dim  # QP degree
        self.m_dim = m_dim  # Base manifold M dimension
        self.g_dim = g_dim  # Gauge Lie algebra / Lie algebroid fiber dimension
        self.is_r_flat = is_r_flat
        self.is_f_flat = is_f_flat
        self.is_as_flat = is_as_flat
        self.is_anchor_horizontal = is_anchor_horizontal
        self.is_flux_closed = is_flux_closed

    def check_classical_master_equation_target_conditions(self) -> bool:
        """Theorem 5.1 & Theorem 6.1:
        {Θ_∇, Θ_∇} = 0 iff R = F = AS = 0, ∇ρ = 0, and dH = 0.
        """
        return (
            self.is_r_flat and
            self.is_f_flat and
            self.is_as_flat and
            self.is_anchor_horizontal and
            self.is_flux_closed
        )


def verify_flux_descent_chain(
    n_dim: int,
    flux_components: Dict[int, int],
    descent_relations: Dict[int, bool]
) -> bool:
    """Verifies the descent chain (Theorem 6.1, Eq. 84-86):
    s from 0 to n:
    Ad_nabla(H^(s+1)) - nabla(H^(s)) == 0.
    Also Ad_nabla(H^(0)) == 0 and dH^(n+1) == 0.
    """
    for s in range(n_dim + 1):
        if not descent_relations.get(s, False):
            return False
    # Check top and bottom
    if not descent_relations.get(-1, False):  # dH = 0
        return False
    if not descent_relations.get(n_dim + 1, False):  # Ad_nabla H^(0) = 0
        return False
    return True


def verify_boundary_homotopy_momentum_chain(
    n_dim: int,
    boundary_relations: Dict[int, bool]
) -> bool:
    """Verifies the boundary consistency conditions (Theorem 6.3, Eq. 96-98):
    d μ^(n) - H = 0
    Ad_nabla(μ^(s+1)) + nabla(μ^(s)) - H^(s+1) = 0 for s = 0, ..., n-1
    Ad_nabla(μ^(0)) - H^(0) = 0.
    """
    # d mu^(n) - H = 0
    if not boundary_relations.get("d_mu_top", False):
        return False
    # Intermediates
    for s in range(n_dim):
        if not boundary_relations.get(f"step_{s}", False):
            return False
    # Base
    if not boundary_relations.get("base_zero", False):
        return False
    return True


def compute_superfield_degrees(n_dim: int) -> Dict[str, Tuple[int, int]]:
    """Computes the ghost/form degrees of superfields in Map(T[1]Σ, T*[n](T[1]M ⊕ A[1])):
    Base coordinates:
      X^i: degree 0 (form degree 0, ghost degree 0)
      Q^i: degree 1 (form degree 1)
      A^a: degree 1 (form degree 1, gauge field)
    Momenta / dual fiber:
      Z_i: degree n (form degree n)
      P_i: degree n-1 (form degree n-1)
      W_a: degree n-1 (form degree n-1)
    """
    return {
        "X": (0, 0),
        "Q": (1, 1),
        "A": (1, 1),
        "Z": (n_dim, n_dim),
        "P": (n_dim - 1, n_dim - 1),
        "W": (n_dim - 1, n_dim - 1),
    }
