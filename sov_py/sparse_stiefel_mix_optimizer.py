"""Sparse Stiefel Optimization on Moving Intersections (MIX Algorithm).

Grounding:
    Shixiang Chen, Wen Huang (2026),
    "From Manifold Identification to Newton Acceleration on Intersections: Sparse Stiefel Optimization",
    arXiv preprint.

Key Mathematical Invariants & Theoretical Theorems:
1. Active Support Graph G(Y) = (V, E) and Codimension gamma(Y) (Section 4.2 & Theorem 2):
   Vertices V = [r] = {0, ..., r-1}.
   Edges: {i, j} in E iff there exists a row ell in [n] such that {i, j} subseteq J_ell^Y,
   where J_ell^Y = {k in [r] : Y_{ell, k} != 0}.
   Edge count gamma(Y) = |E|.
   The structured symmetric subspace S_{r, gamma(Y)} consists of Lambda in S_r with
   Lambda_{ij} = 0 whenever {i, j} not in E.

2. Clean-Intersection Rank Theorem (Theorem 2 & Assumption 2):
   Under the clean-intersection condition (e.g. 2/3-row cover or r <= 3, Delta = 0):
     rank(D H_Y(X)) = gamma(Y)
   where H_Y(X) = X^T X - (I_r + Delta).
   Consequently:
     dim(M_Delta(Y) cap U_s(Y)) = dim(M_g(Y)) - gamma(Y) = nnz(Y) - gamma(Y).
     T_X M_Delta(Y) = T_X St_Delta(n, r) cap T_X M_g(Y).

3. Moving Identified Intersection (Section 4, Eq. 4.1):
   M_k = St_{Delta_k}(n, r) cap M_g(Y_k), where Delta_k = Delta + V_k^T V_k.
   For Y_k = X_k + V_k with V_k in T_{X_k} St_Delta(n, r):
     Y_k^T Y_k = (X_k + V_k)^T (X_k + V_k) = X_k^T X_k + X_k^T V_k + V_k^T X_k + V_k^T V_k
               = I_r + Delta + 0 + V_k^T V_k = I_r + Delta_k.
   Thus Y_k in M_k automatically (nonempty by construction).

4. Safeguarded ManPG/Newton-CG Global Descent (Algorithm 1 & 2):
   Newton trial accepted only if:
     F(X_k^{trial}) <= F(X_k) - tau_bar * ||V_k||_F^2 / t_k.
   Guarantees strict global descent and stationarity limit ||V_k||_F / t_k -> 0.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple
import numpy as np


@dataclass(frozen=True)
class SupportGraph:
    """Support graph G(Y) = (V, E) of an n x r matrix Y."""
    n_rows: int
    r_cols: int
    edges: Set[Tuple[int, int]]  # Ordered pairs (i, j) with i <= j

    @property
    def edge_count(self) -> int:
        """gamma(Y) = |E|."""
        return len(self.edges)

    @property
    def off_diagonal_edges(self) -> Set[Tuple[int, int]]:
        """E_off = {{i, j} in E : i < j}."""
        return {e for e in self.edges if e[0] < e[1]}


def build_support_graph(Y: np.ndarray, tol: float = 1e-10) -> SupportGraph:
    """Construct G(Y) = (V, E) for Y in R^{n x r}."""
    n, r = Y.shape
    edges: Set[Tuple[int, int]] = set()

    for ell in range(n):
        active_cols = [k for k in range(r) if abs(Y[ell, k]) > tol]
        for i in active_cols:
            for j in active_cols:
                if i <= j:
                    edges.add((i, j))

    return SupportGraph(n_rows=n, r_cols=r, edges=edges)


def check_2_3_row_cover(Y: np.ndarray, tol: float = 1e-10) -> bool:
    """Verify Assumption 3 (2/3-row cover):

    Every off-diagonal edge {i, j} in E_off is witnessed by at least one row
    ell with |J_ell^Y| in {2, 3}.
    """
    n, r = Y.shape
    graph = build_support_graph(Y, tol)
    e_off = graph.off_diagonal_edges

    if not e_off:
        return True

    # Find rows with active set size 2 or 3
    witnessed_edges: Set[Tuple[int, int]] = set()
    for ell in range(n):
        active_cols = [k for k in range(r) if abs(Y[ell, k]) > tol]
        if len(active_cols) in (2, 3):
            for i in active_cols:
                for j in active_cols:
                    if i < j:
                        witnessed_edges.add((i, j))

    return e_off.issubset(witnessed_edges)


def compute_intersection_tangent_dimension(
    Y: np.ndarray,
    Delta: Optional[np.ndarray] = None,
    tol: float = 1e-10,
) -> Tuple[int, int, int]:
    """Compute (nnz(Y), gamma(Y), dim(T_Y M_Delta(Y))).

    Verifies Theorem 2:
      dim(T_Y M_Delta(Y)) = nnz(Y) - gamma(Y).
    """
    n, r = Y.shape
    if Delta is None:
        Delta = np.zeros((r, r))

    graph = build_support_graph(Y, tol)
    gamma = graph.edge_count

    # Non-zero entries (active manifold M_g(Y) coordinates)
    coords = list(zip(*np.where(abs(Y) > tol)))
    nnz = len(coords)

    # Constraint matrix A_mat for H in T_Y M_g(Y) satisfying H^T Y + Y^T H = 0
    # There are r(r+1)/2 symmetric constraint pairs
    n_constraints = r * (r + 1) // 2
    A_mat = np.zeros((n_constraints, nnz))

    row_idx = 0
    for a in range(r):
        for b in range(a, r):
            for var_idx, (k, l) in enumerate(coords):
                coeff = 0.0
                if l == a:
                    coeff += Y[k, b]
                if l == b:
                    coeff += Y[k, a]
                A_mat[row_idx, var_idx] = coeff
            row_idx += 1

    svd_vals = np.linalg.svd(A_mat, compute_uv=False)
    rank_A = int(np.sum(svd_vals > tol))

    dim_tangent = nnz - rank_A
    return nnz, gamma, dim_tangent


def verify_moving_stiefel_identity(
    X: np.ndarray,
    V: np.ndarray,
    Delta: np.ndarray,
    tol: float = 1e-10,
) -> Tuple[bool, np.ndarray]:
    """Verify Section 4 moving Stiefel identity:

      Y = X + V
      Delta_k = Delta + V^T V
      Y^T Y = I_r + Delta_k
    given X^T X = I_r + Delta and X^T V + V^T X = 0 (V in T_X St_Delta).
    """
    r = X.shape[1]
    # Check X in St_Delta
    gram_X = X.T @ X
    target_X = np.eye(r) + Delta
    if not np.allclose(gram_X, target_X, atol=tol):
        return False, np.zeros((r, r))

    # Check V in T_X St_Delta
    sym_XV = X.T @ V + V.T @ X
    if not np.allclose(sym_XV, np.zeros((r, r)), atol=tol):
        return False, np.zeros((r, r))

    Y = X + V
    Delta_k = Delta + V.T @ V
    gram_Y = Y.T @ Y
    target_Y = np.eye(r) + Delta_k

    is_valid = bool(np.allclose(gram_Y, target_Y, atol=tol))
    return is_valid, Delta_k


def check_mix_descent_criterion(
    f_Xk: float,
    f_trial: float,
    norm_Vk: float,
    tk: float,
    tau_bar: float = 0.1,
) -> bool:
    """Verify MIX Armijo-like global descent condition (Line 19 of Algorithm 2):

      F(X_{trial}) <= F(X_k) - tau_bar * ||V_k||_F^2 / t_k.
    """
    target = f_Xk - tau_bar * (norm_Vk**2) / tk
    return f_trial <= target
