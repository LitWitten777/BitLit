"""Stiefel Manifold Dynamical Approximation Scheme for Wasserstein Gradient Flows.

Grounding:
    Isabella Carla Gonnella, Olga Mula, Federico Pichi, Gianluigi Rozza (2026),
    "A Dynamical Approximation Scheme on the Stiefel manifold for Wasserstein Gradient Flows",
    arXiv:2607.17235v1 [math.NA].

Key Structural Invariants & Theoretical Results:
1. Stiefel Decoder:
   T_t = phi(theta_t) = sum_{i=1}^n c_{t,i} v_{t,i}
   where c_t in R^n and v_t = (v_{t,1}, ..., v_{t,n}) in St(n, W_m; L^2_{mu_0})
   with m >= n. The tangent space of the decoder image Tan_{phi(theta)} V_phi
   equals span{v} if c = 0, and W_m if c != 0.

2. Dirac-Frenkel Least-Squares Minimizer (Theorem 4.1 & Lemma C.1-C.2):
   dot{T}_t = P_{W_m}(v_{nu_t} circ T_t) for c_t != 0.
   The parameter dynamics decouple as:
     dot{c}_{t,i} = <v_{nu_t} circ T_t, v_{t,i}>_{L^2_{mu_0}}
     dot{v}_{t,i} = sum_{j=1}^k a_{t,ij} psi_{t,j}
   where k = m - n, {psi_{t,j}}_{j=1}^k is an orthonormal basis of L_{v_t} = W_m cap span{v_t}^perp,
   and A_t in R^{n x k} minimizes |A^T c_t - b_t|^2 with b_{t,j} = <v_{nu_t} circ T_t, psi_{t,j}>.
   The optimal rank-one horizontal matrix with pairwise orthogonal components is:
     A_t = (1 / c_{t, i_0}) e_{i_0} b_t^T (for c_{t, i_0} != 0).

3. Componentwise Closed-Form Stiefel Geodesic Exponential Map (Eq. 56):
   For horizontal tangent vectors w with pairwise orthogonal components:
     Exp_v(w)_i = cos(||w_i||) v_i + (sin(||w_i||) / ||w_i||) w_i   (if ||w_i|| != 0)
                  v_i                                                (if ||w_i|| == 0).

4. Energy Dissipation Identity (Proposition 4.2):
   d/dt F(nu_t) = -||dot{T}_t||_{L^2_{mu_0}}^2 = -||v_{nu_t}||_{L^2_{nu_t}}^2 + ||r_t||_{L^2_{mu_0}}^2 <= 0
   where r_t = (I - P_{W_m})(v_{nu_t} circ T_t).

5. Geodesic A Posteriori Gronwall Wasserstein Error Bound (Theorem 4.2):
   For lambda-geodesically convex energies F:
     W_2(mu_t, nu_t) <= int_0^t e^{-lambda (t - s)} ||r_s||_{L^2_{mu_0}} ds.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, List, Tuple
import numpy as np


@dataclass(frozen=True)
class StiefelParameter:
    """Parameters theta = (c, v) for the Stiefel decoder.

    c: shape (n,)
    v: shape (n, dim_ambient) representing an orthonormal frame.
    """
    c: np.ndarray
    v: np.ndarray

    def __post_init__(self):
        c_arr = np.asarray(self.c, dtype=float)
        v_arr = np.asarray(self.v, dtype=float)
        if c_arr.ndim != 1:
            raise ValueError(f"c must be 1D, got shape {c_arr.shape}")
        if v_arr.ndim != 2:
            raise ValueError(f"v must be 2D, got shape {v_arr.shape}")
        if c_arr.shape[0] != v_arr.shape[0]:
            raise ValueError(f"Dimension mismatch: c has {c_arr.shape[0]}, v has {v_arr.shape[0]}")
        object.__setattr__(self, "c", c_arr)
        object.__setattr__(self, "v", v_arr)

    @property
    def n(self) -> int:
        return self.c.shape[0]

    @property
    def ambient_dim(self) -> int:
        return self.v.shape[1]

    def decode(self) -> np.ndarray:
        """Transport map T = sum_{i=1}^n c_i v_i."""
        return self.c @ self.v

    def check_orthonormality(self, tol: float = 1e-10) -> bool:
        """Verify that v is in St(n, ambient_dim): <v_i, v_j> = delta_{ij}."""
        gram = self.v @ self.v.T
        return bool(np.allclose(gram, np.eye(self.n), atol=tol))


def construct_orthogonal_complement_basis(v: np.ndarray, W_basis: np.ndarray, tol: float = 1e-10) -> np.ndarray:
    """Compute an orthonormal basis {psi_j}_{j=1}^k for L_v = W_m cap span{v}^perp.

    Parameters:
        v: shape (n, d), orthonormal frame.
        W_basis: shape (m, d), orthonormal basis of background space W_m with m >= n,
                 such that span{v} subseteq W_m.

    Returns:
        psi: shape (k, d) where k = m - n, an orthonormal basis of L_v.
    """
    n, d = v.shape
    m, _ = W_basis.shape
    k = m - n
    if k == 0:
        return np.zeros((0, d))

    # Project each basis vector of W_basis onto span{v}^perp:
    # proj_perp = w - sum_i <w, v_i> v_i
    projections = W_basis - (W_basis @ v.T) @ v

    # Perform SVD to obtain k orthonormal vectors
    u, s, vh = np.linalg.svd(projections, full_matrices=False)
    idx = np.where(s > tol)[0]
    if len(idx) < k:
        raise ValueError(f"Could not extract {k} orthogonal directions: found {len(idx)}")

    psi = vh[idx[:k]]
    # Ensure exact orthonormality via QR
    q, _ = np.linalg.qr(psi.T)
    return q[:, :k].T


def compute_dirac_frenkel_velocities(
    c: np.ndarray,
    v: np.ndarray,
    psi: np.ndarray,
    target_xi: np.ndarray,
    optimal_rank_one: bool = True,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Compute Dirac-Frenkel velocities (dot{c}, dot{v}) and projected velocity dot{T}.

    Parameters:
        c: shape (n,)
        v: shape (n, d), orthonormal frame
        psi: shape (k, d), orthonormal basis of L_v
        target_xi: shape (d,), target vector (e.g. pulled-back velocity v_{nu} circ T)
        optimal_rank_one: if True, use the rank-one choice A = (1/c_{i_0}) e_{i_0} b^T
                          (Remark 4.1) which gives pairwise orthogonal components for w.
                          If False, use the pseudoinverse solution A = (1/|c|^2) c b^T.

    Returns:
        dot_c: shape (n,)
        dot_v: shape (n, d)
        dot_T: shape (d,)
        residual_r: shape (d,) = target_xi - dot_T
    """
    n, d = v.shape
    k = psi.shape[0]

    # dot_c_i = <xi, v_i>
    dot_c = v @ target_xi

    # b_j = <xi, psi_j>
    if k > 0:
        b = psi @ target_xi
        c_norm_sq = float(np.sum(c**2))

        if c_norm_sq < 1e-14:
            A = np.zeros((n, k))
        elif optimal_rank_one:
            i_0 = int(np.argmax(np.abs(c)))
            A = np.zeros((n, k))
            A[i_0, :] = b / c[i_0]
        else:
            A = np.outer(c, b) / c_norm_sq

        # dot_v_i = sum_j A_{ij} psi_j
        dot_v = A @ psi
    else:
        A = np.zeros((n, 0))
        dot_v = np.zeros((n, d))

    # dot_T = sum_i (c_i dot_v_i + dot_c_i v_i)
    dot_T = c @ dot_v + dot_c @ v
    residual_r = target_xi - dot_T

    return dot_c, dot_v, dot_T, residual_r


def stiefel_exponential_map_horizontal_orthogonal(v: np.ndarray, w: np.ndarray) -> np.ndarray:
    """Componentwise closed formula for Stiefel exponential map (Equation 56 in paper).

    Valid when w is horizontal and has pairwise orthogonal components:
      Exp_v(w)_i = cos(||w_i||) v_i + (sin(||w_i||) / ||w_i||) w_i   (if ||w_i|| != 0)
                   v_i                                                (if ||w_i|| == 0).

    Preserves exact orthonormality: Exp_v(w) in St(n, d).
    """
    n, d = v.shape
    v_next = np.zeros_like(v)
    for i in range(n):
        norm_wi = float(np.linalg.norm(w[i]))
        if norm_wi > 1e-14:
            v_next[i] = np.cos(norm_wi) * v[i] + (np.sin(norm_wi) / norm_wi) * w[i]
        else:
            v_next[i] = v[i]
    return v_next


def explicit_stiefel_euler_step(
    param: StiefelParameter,
    dt: float,
    psi: np.ndarray,
    target_xi: np.ndarray,
    optimal_rank_one: bool = True,
) -> Tuple[StiefelParameter, np.ndarray, np.ndarray]:
    """Perform one explicit Euler step on the Stiefel decoder manifold:

      theta_{t + dt} = (c_t + dt * dot_c_t, Exp_{v_t}(dt * dot_v_t))

    Returns:
        next_param: StiefelParameter at t + dt
        dot_T: projected transport map velocity
        residual_r: projection residual
    """
    dot_c, dot_v, dot_T, residual_r = compute_dirac_frenkel_velocities(
        param.c, param.v, psi, target_xi, optimal_rank_one=optimal_rank_one
    )

    c_next = param.c + dt * dot_c
    v_next = stiefel_exponential_map_horizontal_orthogonal(param.v, dt * dot_v)
    next_param = StiefelParameter(c=c_next, v=v_next)
    return next_param, dot_T, residual_r


def verify_energy_dissipation_identity(
    v_exact: np.ndarray,
    dot_T: np.ndarray,
    residual_r: np.ndarray,
    tol: float = 1e-10,
) -> Tuple[bool, float, float]:
    """Verify Proposition 4.2 energy dissipation identity:

      ||v_exact||^2 = ||dot_T||^2 + ||r||^2

    which implies:
      d/dt F(nu_t) = -||dot_T||^2 = -||v_exact||^2 + ||r||^2 <= 0.
    """
    norm_v_sq = float(np.sum(v_exact**2))
    norm_dotT_sq = float(np.sum(dot_T**2))
    norm_r_sq = float(np.sum(residual_r**2))

    diff = abs(norm_v_sq - (norm_dotT_sq + norm_r_sq))
    is_valid = diff < tol
    return is_valid, norm_dotT_sq, diff


def compute_gronwall_wasserstein_bound(
    residual_norms: List[float],
    dt: float,
    lambda_param: float,
) -> float:
    """Compute the discrete a posteriori Gronwall error bound (Theorem 4.2):

      W_2(mu_t, nu_t) <= int_0^t e^{-lambda (t - s)} ||r_s|| ds.

    Using trapezoidal rule over discrete time points.
    """
    N = len(residual_norms)
    if N == 0:
        return 0.0
    t_final = (N - 1) * dt
    weights = np.zeros(N)
    for i in range(N):
        s = i * dt
        decay = np.exp(-lambda_param * (t_final - s))
        trap_w = 0.5 if (i == 0 or i == N - 1) else 1.0
        weights[i] = trap_w * dt * decay

    return float(np.sum(weights * np.array(residual_norms)))


def run_stiefel_wgf_simulation(
    m_dim: int,
    n_dim: int,
    ambient_dim: int,
    n_steps: int,
    dt: float,
    lambda_param: float,
    target_field_generator: Callable[[float, np.ndarray], np.ndarray],
    seed: int = 42,
) -> dict:
    """Run a full simulation of the Dirac-Frenkel Stiefel dynamical approximation."""
    rng = np.random.default_rng(seed)

    # 1. Construct random orthonormal background space W_m (m x d)
    raw_W = rng.standard_normal((m_dim, ambient_dim))
    W_basis, _ = np.linalg.qr(raw_W.T)
    W_basis = W_basis[:, :m_dim].T  # m x ambient_dim

    # 2. Initial frame v_0 in St(n, W_m)
    v_0 = W_basis[:n_dim].copy()
    c_0 = rng.uniform(0.5, 2.0, size=n_dim)
    param = StiefelParameter(c=c_0, v=v_0)

    orthonormality_errors = []
    orthogonality_residuals = []
    dissipation_checks = []
    residual_norms = []

    for step in range(n_steps):
        t = step * dt
        T_curr = param.decode()

        gram = param.v @ param.v.T
        ortho_err = float(np.max(np.abs(gram - np.eye(n_dim))))
        orthonormality_errors.append(ortho_err)

        psi = construct_orthogonal_complement_basis(param.v, W_basis)
        xi_target = target_field_generator(t, T_curr)

        next_param, dot_T, r = explicit_stiefel_euler_step(
            param, dt, psi, xi_target, optimal_rank_one=True
        )

        dot_product = float(abs(np.dot(dot_T, r)))
        orthogonality_residuals.append(dot_product)

        valid_diss, _, diss_err = verify_energy_dissipation_identity(xi_target, dot_T, r)
        dissipation_checks.append(diss_err)

        residual_norms.append(float(np.linalg.norm(r)))
        param = next_param

    w2_bound = compute_gronwall_wasserstein_bound(residual_norms, dt, lambda_param)

    return {
        "max_orthonormality_error": max(orthonormality_errors),
        "max_orthogonality_residual": max(orthogonality_residuals),
        "max_dissipation_error": max(dissipation_checks),
        "mean_residual_norm": float(np.mean(residual_norms)),
        "gronwall_w2_bound": w2_bound,
        "all_orthonormal": max(orthonormality_errors) < 1e-10,
        "all_dissipation_preserved": max(dissipation_checks) < 1e-10,
    }
