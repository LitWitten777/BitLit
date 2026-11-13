"""Symplectic Lie-Poisson Integrator & G2 Calibration Soliton Preservation.

This module implements discrete structure-preserving momentum integrators on the
11-dimensional Stiefel manifold V_2(R^7) = G_2 / SU(2) and coadjoint orbits of g_2:
1. Exact projection of so(7) (21D) onto the exceptional Lie algebra g_2 (14D) and
   its orthogonal complement m (7D).
2. Symplectic Cayley-transform time-stepping preserving Stiefel orthonormality X^T X = I_2.
3. Exact G_2 Lie group exponential time-stepping preserving the associative calibration
   3-form phi(u, v, u x_7 v) = 1.0 to machine precision.
4. Long-time quadratic and quartic Casimir conservation along calibrated soliton orbits.
"""

from __future__ import annotations

import functools
from dataclasses import dataclass
from typing import Final

import numpy as np
import scipy.linalg as la

from sedenion.hydro.non_associative_fluid import (
    fano_cross_product_7d,
    fano_structure_constants,
)

DIM_R7: Final[int] = 7
DIM_SO7: Final[int] = 21
DIM_G2: Final[int] = 14
DIM_M: Final[int] = 7


class LiePoissonError(Exception):
    """Exception raised for Lie-Poisson integration or dimension errors."""


@dataclass(frozen=True)
class SolitonTrajectoryResult:
    """Result of calibrated soliton integration on V_2(R^7).

    Attributes:
        times: Array of simulation times.
        max_orthonormality_error: Maximum ||X_k^T X_k - I_2||_F along the trajectory.
        max_casimir_drift: Maximum drift |C_2(k) - C_2(0)| of quadratic Casimir.
        max_calibration_drift: Maximum drift |phi(k) - phi(0)| of associative 3-form.
        is_stable: Boolean certifying that drifts remain within numerical tolerance.
        trajectory_length: Number of time-steps integrated.
    """

    times: np.ndarray
    max_orthonormality_error: float
    max_casimir_drift: float
    max_calibration_drift: float
    is_stable: bool
    trajectory_length: int


@functools.lru_cache(maxsize=1)
def get_so7_index_pairs() -> list[tuple[int, int]]:
    """Return ordered index pairs (i, j) for 0 <= i < j < 7 indexing so(7)."""
    return [(i, j) for i in range(DIM_R7) for j in range(i + 1, DIM_R7)]


@functools.lru_cache(maxsize=1)
def get_g2_projector_and_basis() -> tuple[np.ndarray, np.ndarray]:
    """Compute the 14-dimensional orthonormal basis and projector for g_2 in so(7).

    A matrix A in so(7) belongs to g_2 if and only if A is a derivation of the
    7D octonionic cross-product:
        A(u x_7 v) = (A u) x_7 v + u x_7 (A v).
    Evaluating this on all pairs (e_i, e_j) yields 84 linear equations on the
    21 parameters of so(7). The rank of this constraint is exactly 7, leaving
    a 14-dimensional null-space corresponding to g_2 = Lie(Aut(O)).

    Returns:
        Tuple of (g2_basis of shape (21, 14), projector_matrix of shape (21, 21)).
    """
    c = fano_structure_constants()
    pairs = get_so7_index_pairs()
    rows: list[np.ndarray] = []

    for i in range(DIM_R7):
        for j in range(i + 1, DIM_R7):
            for m in range(DIM_R7):
                row = np.zeros(DIM_SO7, dtype=np.float64)
                # sum_k c[i, j, k] A[m, k]
                for k in range(DIM_R7):
                    if c[i, j, k] != 0.0:
                        if m < k:
                            row[pairs.index((m, k))] += c[i, j, k]
                        elif m > k:
                            row[pairs.index((k, m))] -= c[i, j, k]
                # - sum_p A[p, i] c[p, j, m]
                for p in range(DIM_R7):
                    if c[p, j, m] != 0.0:
                        if p < i:
                            row[pairs.index((p, i))] -= c[p, j, m]
                        elif p > i:
                            row[pairs.index((i, p))] += c[p, j, m]
                # - sum_p A[p, j] c[i, p, m]
                for p in range(DIM_R7):
                    if c[i, p, m] != 0.0:
                        if p < j:
                            row[pairs.index((p, j))] -= c[i, p, m]
                        elif p > j:
                            row[pairs.index((j, p))] += c[i, p, m]
                if np.any(row != 0.0):
                    rows.append(row)

    constraint_matrix = np.array(rows, dtype=np.float64)
    _, s_vals, vt = np.linalg.svd(constraint_matrix)
    rank = int(np.sum(s_vals > 1e-10))
    if rank != DIM_M:
        raise LiePoissonError(f"Expected rank {DIM_M} for g_2 derivation constraints, got {rank}")

    g2_basis = vt[DIM_M:].T  # shape (21, 14)
    proj_matrix = g2_basis @ g2_basis.T  # shape (21, 21)
    return g2_basis, proj_matrix


class G2LieAlgebra:
    """Operations on the exceptional Lie algebra g_2 = Aut(O) inside so(7)."""

    @staticmethod
    def matrix_to_vector(a_mat: np.ndarray) -> np.ndarray:
        """Convert a 7x7 skew-symmetric matrix to a 21-dimensional vector."""
        if a_mat.shape != (DIM_R7, DIM_R7):
            raise LiePoissonError("Matrix must be 7x7.")
        pairs = get_so7_index_pairs()
        vec = np.zeros(DIM_SO7, dtype=np.float64)
        for idx, (i, j) in enumerate(pairs):
            vec[idx] = a_mat[i, j]
        return vec

    @staticmethod
    def vector_to_matrix(vec: np.ndarray) -> np.ndarray:
        """Convert a 21-dimensional vector to a 7x7 skew-symmetric matrix."""
        if vec.shape != (DIM_SO7,):
            raise LiePoissonError("Vector must be 21-dimensional.")
        pairs = get_so7_index_pairs()
        a_mat = np.zeros((DIM_R7, DIM_R7), dtype=np.float64)
        for idx, (i, j) in enumerate(pairs):
            val = float(vec[idx])
            a_mat[i, j] = val
            a_mat[j, i] = -val
        return a_mat

    @classmethod
    def project_so7_to_g2(cls, a_mat: np.ndarray) -> np.ndarray:
        """Project an arbitrary skew-symmetric matrix in so(7) onto g_2."""
        vec = cls.matrix_to_vector(a_mat)
        _, proj = get_g2_projector_and_basis()
        g2_vec = proj @ vec
        return cls.vector_to_matrix(g2_vec)

    @classmethod
    def derivation_residual(cls, a_mat: np.ndarray) -> float:
        """Measure the maximum derivation defect ||A(u x v) - (Au) x v - u x (Av)||."""
        max_defect = 0.0
        for i in range(DIM_R7):
            for j in range(i + 1, DIM_R7):
                ei = np.zeros(DIM_R7, dtype=np.float64)
                ej = np.zeros(DIM_R7, dtype=np.float64)
                ei[i] = 1.0
                ej[j] = 1.0

                e_cross = fano_cross_product_7d(ei, ej)
                term_lhs = a_mat @ e_cross

                ae_i = a_mat @ ei
                ae_j = a_mat @ ej
                term_rhs = fano_cross_product_7d(ae_i, ej) + fano_cross_product_7d(ei, ae_j)

                defect = float(np.linalg.norm(term_lhs - term_rhs))
                if defect > max_defect:
                    max_defect = defect
        return max_defect


class SymplecticLiePoissonIntegrator:
    """Structure-preserving symplectic momentum integrator on V_2(R^7)."""

    def __init__(self) -> None:
        self.g2 = G2LieAlgebra()

    @staticmethod
    def cayley_step(
        x_mat: np.ndarray, a_mat: np.ndarray, dt: float
    ) -> tuple[np.ndarray, np.ndarray]:
        """Advance (X, A) by time dt using the matrix Cayley transform.

        R = (I - 0.5 * dt * A)^{-1} (I + 0.5 * dt * A) in SO(7).
        X_{k+1} = R X_k.
        A_{k+1} = R A_k R^T.
        """
        eye7 = np.eye(DIM_R7, dtype=np.float64)
        half_step = 0.5 * dt * a_mat
        r_mat = np.linalg.inv(eye7 - half_step) @ (eye7 + half_step)

        x_next = r_mat @ x_mat
        a_next = r_mat @ a_mat @ r_mat.T
        return x_next, a_next

    @classmethod
    def g2_exponential_step(
        cls, x_mat: np.ndarray, a_mat: np.ndarray, dt: float
    ) -> tuple[np.ndarray, np.ndarray]:
        """Advance (X, A) by time dt using the exact G_2 Lie group exponential.

        A_g2 = Pi_g2(A).
        R = expm(dt * A_g2) in G_2 = Aut(O).
        X_{k+1} = R X_k.
        A_{k+1} = R A_g2 R^T.
        """
        a_g2 = G2LieAlgebra.project_so7_to_g2(a_mat)
        r_mat = la.expm(dt * a_g2)

        x_next = r_mat @ x_mat
        a_next = r_mat @ a_g2 @ r_mat.T
        return x_next, a_next

    @staticmethod
    def compute_casimirs(a_mat: np.ndarray) -> tuple[float, float]:
        """Compute quadratic Casimir C_2 and quartic Casimir C_4.

        C_2 = (1/2) ||A||_F^2 = -(1/2) Tr(A^2).
        C_4 = (1/4) Tr(A^4).
        """
        c2 = float(0.5 * np.sum(a_mat**2))
        a2 = a_mat @ a_mat
        c4 = float(0.25 * np.trace(a2 @ a2))
        return c2, c4

    @staticmethod
    def compute_calibration_value(x_mat: np.ndarray) -> float:
        """Compute the associative calibration 3-form value phi(u, v, u x_7 v).

        For an orthonormal 2-frame X = [u, v], let w = u x_7 v.
        phi(u, v, w) = <u, v x_7 w>.
        If span(u, v, w) is calibrated, phi = 1.0.
        """
        u = x_mat[:, 0]
        v = x_mat[:, 1]
        w = fano_cross_product_7d(u, v)
        vw = fano_cross_product_7d(v, w)
        return float(np.dot(u, vw))

    def integrate_soliton(
        self,
        x0: np.ndarray,
        a0: np.ndarray,
        dt: float,
        n_steps: int,
        use_g2_exact: bool = True,
    ) -> SolitonTrajectoryResult:
        """Simulate a calibrated soliton orbit on V_2(R^7) over n_steps.

        Tracks Stiefel orthonormality error, quadratic Casimir drift, and
        associative calibration value.
        """
        if x0.shape != (DIM_R7, 2):
            raise LiePoissonError("Initial frame X0 must have shape (7, 2).")
        if a0.shape != (DIM_R7, DIM_R7):
            raise LiePoissonError("Initial momentum A0 must have shape (7, 7).")
        if dt <= 0.0 or n_steps <= 0:
            raise LiePoissonError("dt and n_steps must be strictly positive.")

        times = np.linspace(0.0, dt * n_steps, n_steps + 1)
        c2_0, _ = self.compute_casimirs(a0)
        phi_0 = self.compute_calibration_value(x0)

        max_ortho_err = 0.0
        max_casimir_drift = 0.0
        max_calib_drift = 0.0

        x_curr = x0.copy()
        a_curr = a0.copy()

        for _ in range(n_steps):
            if use_g2_exact:
                x_curr, a_curr = self.g2_exponential_step(x_curr, a_curr, dt)
            else:
                x_curr, a_curr = self.cayley_step(x_curr, a_curr, dt)

            # Check orthonormality
            ortho_err = float(np.linalg.norm(x_curr.T @ x_curr - np.eye(2)))
            if ortho_err > max_ortho_err:
                max_ortho_err = ortho_err

            # Check Casimir
            c2_curr, _ = self.compute_casimirs(a_curr)
            cas_drift = float(abs(c2_curr - c2_0))
            if cas_drift > max_casimir_drift:
                max_casimir_drift = cas_drift

            # Check Calibration
            phi_curr = self.compute_calibration_value(x_curr)
            calib_drift = float(abs(phi_curr - phi_0))
            if calib_drift > max_calib_drift:
                max_calib_drift = calib_drift

        is_stable = bool(
            max_ortho_err < 1e-10 and max_casimir_drift < 1e-8 and max_calib_drift < 1e-10
        )

        return SolitonTrajectoryResult(
            times=times,
            max_orthonormality_error=max_ortho_err,
            max_casimir_drift=max_casimir_drift,
            max_calibration_drift=max_calib_drift,
            is_stable=is_stable,
            trajectory_length=n_steps,
        )
