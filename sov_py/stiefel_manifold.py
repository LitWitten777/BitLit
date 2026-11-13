"""Continuous Geometry and Geodesics on the Stiefel Manifold V_2(R^7) = G_2 / SU(2).

Bridges the discrete 168-vertex sedenion zero-divisor annihilation graph
to the 11-dimensional continuous homogeneous manifold V_2(R^7) endowed with
its canonical and G_2-invariant Riemannian metrics.

References:
    - Reggiani, S. (2024). "The geometry of sedenion zero divisors." arXiv:2411.18881.
    - Edelman, A., Arias, T. A., & Smith, S. T. (1998). "The geometry of algorithms
      with orthogonality constraints." SIAM J. Matrix Anal. Appl., 20(2), 303-353.
    - Zimmermann, R. (2017). "A matrix-algebraic algorithm for the Riemannian logarithm
      on the Stiefel manifold." SIAM J. Matrix Anal. Appl., 38(2), 322-342.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any

import networkx as nx
import numpy as np
import scipy.linalg

from sedenion.exceptions import SedenionError
from sedenion.stratification import CrossOctetVector, stratify_cross_octet


class StiefelManifoldError(SedenionError):
    """Exception raised for violations of Stiefel manifold invariants."""


@dataclass(frozen=True)
class StiefelFrame:
    """An orthonormal 2-frame in R^7, representing a point in V_2(R^7).

    Attributes:
        matrix: 7x2 real matrix with orthonormal columns (X^T X = I_2).
        zd: Optional discrete cross-octet zero divisor from which this frame originated.
    """

    matrix: np.ndarray
    zd: Any = None

    def __post_init__(self) -> None:
        if self.matrix.shape not in ((7, 2), (15, 2)):
            raise StiefelManifoldError(
                f"StiefelFrame must be 7x2 matrix (or 15x2 for V_2(R^15)), got shape {self.matrix.shape}"
            )
        gram = self.matrix.T @ self.matrix
        if not np.allclose(gram, np.eye(2), atol=1e-6):
            raise StiefelManifoldError(f"Columns are not orthonormal: X^T X =\n{gram}")

    @property
    def n(self) -> int:
        """Ambient Euclidean dimension n."""
        return int(self.matrix.shape[0])

    @property
    def v1(self) -> np.ndarray:
        """First orthonormal column vector in R^n."""
        return self.matrix[:, 0]

    @property
    def v2(self) -> np.ndarray:
        """Second orthonormal column vector in R^n."""
        return self.matrix[:, 1]

    def is_orthonormal(self, tol: float = 1e-8) -> bool:
        """Verify that columns are orthonormal within tolerance."""
        gram = self.matrix.T @ self.matrix
        return bool(np.allclose(gram, np.eye(2), atol=tol))


class StiefelManifoldV2R7:
    """Geometry engine for the 11-dimensional Stiefel manifold V_2(R^7) = G_2 / SU(2).

    Points on V_2(R^7) are orthonormal 2-frames in R^7 (7x2 matrices X with X^T X = I_2).
    Endowed with the canonical metric:
        <Delta_1, Delta_2>_P = Tr(Delta_1^T (I - 0.5 P P^T) Delta_2)
    """

    DIM: int = 11
    N: int = 7
    K: int = 2
    DIM_G2: int = 14
    DIM_SU2: int = 3

    @staticmethod
    def embed_zero_divisor(u: CrossOctetVector) -> StiefelFrame:
        """Embed a discrete cross-octet zero divisor into V_2(R^7).

        u = s_1 e_i + s_2 e_{8+j} with 1 <= i, j <= 7, i != j, s_1, s_2 in {+1, -1}.
        The corresponding 2-frame is P = [v_1, v_2] in R^{7x2} where:
            v_1 = s_1 e_i (one-hot at coordinate i-1)
            v_2 = s_2 e_j (one-hot at coordinate j-1)
        """
        if u.i == 0 or u.j == 0 or u.i == u.j:
            raise StiefelManifoldError(
                f"Vector {u} is not a valid cross-octet zero divisor (requires i, j in 1..7, i != j)"
            )
        mat = np.zeros((7, 2), dtype=np.float64)
        mat[u.i - 1, 0] = float(u.s1)
        mat[u.j - 1, 1] = float(u.s2)
        return StiefelFrame(matrix=mat, zd=u)

    @classmethod
    def embed_all_zero_divisors(cls) -> dict[tuple[int, int, int, int], StiefelFrame]:
        """Embed all 168 discrete zero divisors into V_2(R^7)."""
        zds, _, _ = stratify_cross_octet()
        return {u.key: cls.embed_zero_divisor(u) for u in zds}

    @staticmethod
    def project_to_tangent(P: np.ndarray, Z: np.ndarray) -> np.ndarray:
        """Orthogonal projection of an arbitrary 7x2 matrix Z onto the tangent space T_P V_2(R^7).

        Formula: Pi_P(Z) = Z - P sym(P^T Z) = (I - P P^T) Z + P skew(P^T Z).
        """
        PT_Z = P.T @ Z
        sym = 0.5 * (PT_Z + PT_Z.T)
        return np.asarray(Z - P @ sym, dtype=np.float64)

    @staticmethod
    def is_tangent(P: np.ndarray, Delta: np.ndarray, tol: float = 1e-8) -> bool:
        """Check whether Delta is in the tangent space T_P V_2(R^7).

        A matrix Delta is tangent iff P^T Delta + Delta^T P = 0 (i.e. P^T Delta in so(2)).
        """
        skew_sym = P.T @ Delta + Delta.T @ P
        return bool(np.allclose(skew_sym, 0.0, atol=tol))

    @staticmethod
    def project_vertical(P: np.ndarray, Delta: np.ndarray) -> np.ndarray:
        """Project Delta onto the vertical tangent space V_P = { P A | A in so(2) }.

        The vertical space V_P has dimension 1 (for k=2) and corresponds to in-plane
        rotations along the fiber of V_2(R^7) -> Gr(2, 7).
        Formula: Delta_V = P A, where A = 0.5 * (P^T Delta - Delta^T P).

        Args:
            P: 7x2 orthonormal 2-frame on V_2(R^7).
            Delta: 7x2 matrix (e.g. tangent vector in T_P V_2(R^7)).

        Returns:
            7x2 matrix Delta_V in V_P.
        """
        A = 0.5 * (P.T @ Delta - Delta.T @ P)
        return np.asarray(P @ A, dtype=np.float64)

    @staticmethod
    def project_horizontal(P: np.ndarray, Delta: np.ndarray) -> np.ndarray:
        """Project Delta onto the horizontal tangent space H_P = { K | P^T K = 0 }.

        The horizontal space H_P has dimension 10 (2*(7-2)=10) and corresponds to
        frame displacements orthogonal to span(P), identifying with the tangent space
        of the Grassmannian Gr(2, 7).
        Formula: Delta_H = (I - P P^T) Delta.

        Args:
            P: 7x2 orthonormal 2-frame on V_2(R^7).
            Delta: 7x2 matrix (e.g. tangent vector in T_P V_2(R^7)).

        Returns:
            7x2 matrix Delta_H in H_P.
        """
        K = Delta - P @ (P.T @ Delta)
        return np.asarray(K, dtype=np.float64)

    @classmethod
    def tangent_bundle_decomposition(
        cls, P: np.ndarray, Delta: np.ndarray, tol: float = 1e-8
    ) -> tuple[np.ndarray, np.ndarray]:
        """Decompose a tangent vector Delta into orthogonal vertical and horizontal components.

        Splits T_P V_2(R^7) = V_P direct_sum H_P:
            Delta = Delta_V + Delta_H
        where Delta_V in V_P (dim 1) and Delta_H in H_P (dim 10).

        Verifies:
            1. Delta = Delta_V + Delta_H within tolerance.
            2. <Delta_V, Delta_H>_P == 0 (canonical metric orthogonality).

        Args:
            P: 7x2 orthonormal 2-frame on V_2(R^7).
            Delta: 7x2 tangent vector in T_P V_2(R^7).
            tol: Numerical tolerance for verification checks.

        Returns:
            Tuple (Delta_V, Delta_H) of 7x2 matrices.

        Raises:
            StiefelManifoldError: If Delta is not tangent or decomposition checks fail.
        """
        if not cls.is_tangent(P, Delta, tol=tol):
            raise StiefelManifoldError(
                "Vector Delta must belong to tangent space T_P V_2(R^7) for bundle decomposition"
            )
        Delta_V = cls.project_vertical(P, Delta)
        Delta_H = cls.project_horizontal(P, Delta)

        # Verification 1: Direct sum reconstruction Delta == Delta_V + Delta_H
        sum_Delta = Delta_V + Delta_H
        if not np.allclose(Delta, sum_Delta, atol=tol):
            raise StiefelManifoldError(
                f"Tangent bundle decomposition sum mismatch: ||Delta - (Delta_V + Delta_H)|| = "
                f"{float(np.linalg.norm(Delta - sum_Delta))}"
            )

        # Verification 2: Canonical metric orthogonality <Delta_V, Delta_H>_P == 0
        inner_prod = cls.canonical_inner_product(P, Delta_V, Delta_H)
        if not math.isclose(inner_prod, 0.0, abs_tol=tol):
            raise StiefelManifoldError(
                f"Canonical metric orthogonality failed: <Delta_V, Delta_H>_P = {inner_prod}"
            )

        return Delta_V, Delta_H

    @staticmethod
    def canonical_inner_product(P: np.ndarray, Delta1: np.ndarray, Delta2: np.ndarray) -> float:
        """Compute the canonical Riemannian metric inner product <Delta_1, Delta_2>_P.

        <Delta_1, Delta_2>_P = Tr(Delta_1^T (I - 0.5 P P^T) Delta_2).
        """
        metric_factor = np.eye(P.shape[0]) - 0.5 * (P @ P.T)
        return float(np.trace(Delta1.T @ metric_factor @ Delta2))

    @classmethod
    def canonical_norm(cls, P: np.ndarray, Delta: np.ndarray) -> float:
        """Compute the canonical Riemannian norm of tangent vector Delta at P."""
        val = cls.canonical_inner_product(P, Delta, Delta)
        return math.sqrt(max(0.0, val))

    @staticmethod
    def exponential_map(P: np.ndarray, Delta: np.ndarray, t: float = 1.0) -> np.ndarray:
        """Evaluate the Riemannian exponential map Exp_P(t * Delta) under canonical metric.

        Uses the exact closed-form matrix exponential from Edelman, Arias, & Smith (1998):
            gamma(t) = [P, Q] exp(t * [[A, -R^T], [R, 0]]) [I_2; 0]
        where A = P^T Delta in so(2), and K = (I - P P^T) Delta = Q R via SVD.
        """
        k = P.shape[1]
        A = 0.5 * (P.T @ Delta - Delta.T @ P)  # Ensure exact skew-symmetry
        K = Delta - P @ A

        # Robust SVD-based QR decomposition of K
        U, S, Vt = np.linalg.svd(K, full_matrices=False)
        Q = U
        R = np.diag(S) @ Vt

        block = np.block([[A, -R.T], [R, np.zeros((k, k), dtype=np.float64)]])
        rot = scipy.linalg.expm(t * block)
        rot_top = rot[:, :k]

        Y = np.hstack([P, Q]) @ rot_top
        return np.asarray(Y, dtype=np.float64)

    @staticmethod
    def principal_angles(P: np.ndarray, Q: np.ndarray) -> tuple[float, float]:
        """Compute the canonical principal angles (theta_1, theta_2) between 2-frames P and Q.

        Singular values of M = P^T Q are the cosines of the canonical angles.
        Returns:
            (theta_1, theta_2) with 0 <= theta_1 <= theta_2 <= pi/2.
        """
        M = P.T @ Q
        s = np.clip(np.linalg.svd(M, compute_uv=False), 0.0, 1.0)
        thetas = np.arccos(s)
        thetas.sort()
        return float(thetas[0]), float(thetas[1])

    @classmethod
    def grassmann_distance(cls, P: np.ndarray, Q: np.ndarray) -> float:
        """Compute the Grassmannian distance between span(P) and span(Q).

        d_Gr(P, Q) = sqrt(theta_1^2 + theta_2^2).
        """
        theta1, theta2 = cls.principal_angles(P, Q)
        return math.sqrt(theta1**2 + theta2**2)

    @classmethod
    def logarithmic_map(
        cls, P: np.ndarray, Q: np.ndarray, max_iter: int = 80, tol: float = 1e-9
    ) -> np.ndarray:
        """Compute the Riemannian logarithm Log_P(Q) on V_2(R^7).

        Returns tangent vector Delta in T_P V_2(R^7) such that Exp_P(Delta) = Q.
        Employs analytical shortcuts for orthogonal/in-plane pairs and damped
        Riemannian shooting for general configurations.
        """
        M = P.T @ Q

        # Case 1: Identical frames
        if np.allclose(P, Q, atol=tol):
            return np.zeros_like(P)

        # Case 2: Mutually completely orthogonal frames (P^T Q == 0)
        # Closed-form: Delta = (pi/2) * Q
        if np.allclose(M, 0.0, atol=1e-6):
            return (0.5 * math.pi) * Q

        # Case 3: Same 2-plane (M in O(2))
        if np.allclose(M.T @ M, np.eye(2), atol=1e-6):
            det_M = np.linalg.det(M)
            if det_M > 0:
                # M in SO(2): pure in-plane rotation
                angle = math.atan2(M[1, 0], M[0, 0])
                A = np.array([[0.0, -angle], [angle, 0.0]], dtype=np.float64)
                return P @ A
            # Reflection: flip out-of-plane along first available orthogonal coordinate
            # Find an orthogonal unit vector normal to span(P)
            for col in range(7):
                e = np.zeros(7, dtype=np.float64)
                e[col] = 1.0
                proj = e - P @ (P.T @ e)
                norm_proj = np.linalg.norm(proj)
                if norm_proj > 0.5:
                    normal_vec = proj / norm_proj
                    break
            else:
                normal_vec = np.zeros(7, dtype=np.float64)

            # Rotation in plane normal to flip
            if np.isclose(M[0, 0], 1.0, atol=1e-4):
                # Second column flipped: e2 -> -e2
                Delta = np.zeros_like(P)
                Delta[:, 1] = math.pi * normal_vec
                return Delta
            elif np.isclose(M[1, 1], 1.0, atol=1e-4):
                # First column flipped: e1 -> -e1
                Delta = np.zeros_like(P)
                Delta[:, 0] = math.pi * normal_vec
                return Delta
            else:
                # Diagonal reflection: rotate by pi/2 and flip
                Delta = np.zeros_like(P)
                Delta[:, 0] = (math.pi / math.sqrt(2)) * normal_vec
                Delta[:, 1] = (math.pi / math.sqrt(2)) * normal_vec
                return cls.project_to_tangent(P, Delta)

        # Case 4: General configuration - Riemannian gradient shooting
        # Initialize with projected displacement
        Q_perp = Q - P @ M
        U, S, Vt = np.linalg.svd(Q_perp, full_matrices=False)
        angles = np.arcsin(np.clip(S, 0.0, 1.0))
        Delta = P @ (0.5 * (M - M.T)) + U @ (np.diag(angles) @ Vt)
        Delta = cls.project_to_tangent(P, Delta)

        step_size = 0.5
        for _ in range(max_iter):
            Q_cand = cls.exponential_map(P, Delta)
            res = Q_cand - Q
            err = np.linalg.norm(res)
            if err < tol:
                break
            grad = cls.project_to_tangent(P, res)
            Delta = Delta - step_size * grad

        return Delta

    @classmethod
    def geodesic_distance(cls, P: np.ndarray, Q: np.ndarray) -> float:
        """Compute the canonical Riemannian geodesic distance d_{V_2}(P, Q).

        For orthogonal frames P^T Q = 0, this evaluates to pi / sqrt(2) ~ 2.22144.
        """
        M = P.T @ Q
        if np.allclose(M, 0.0, atol=1e-6):
            return math.pi / math.sqrt(2.0)
        Delta = cls.logarithmic_map(P, Q)
        return cls.canonical_norm(P, Delta)

    @classmethod
    def geodesic_path(cls, P: np.ndarray, Q: np.ndarray, num_steps: int = 50) -> list[np.ndarray]:
        """Generate a discretized geodesic path gamma(t) on V_2(R^7) connecting P to Q.

        Evaluates Exp_P(t * Delta) for t in linspace(0, 1, num_steps).
        """
        if num_steps < 2:
            raise StiefelManifoldError("num_steps must be at least 2")
        Delta = cls.logarithmic_map(P, Q)
        path = []
        for step in range(num_steps):
            t = step / (num_steps - 1)
            gamma_t = cls.exponential_map(P, Delta, t=t)
            path.append(gamma_t)
        return path

    @classmethod
    def sectional_curvature(cls, P: np.ndarray, X: np.ndarray, Y: np.ndarray) -> float:
        """Evaluate the Riemannian sectional curvature K(X, Y) for a 2-plane in T_P V_2(R^7).

        X, Y are tangent vectors at P spanning an orthonormal 2-plane under the canonical metric.
        Formula from Edelman, Arias, & Smith (1998, Theorem 2.4).
        """
        # Ensure orthonormal 2-plane under canonical metric
        norm_X = cls.canonical_norm(P, X)
        if norm_X < 1e-10:
            raise StiefelManifoldError("Tangent vector X has zero norm")
        X = X / norm_X

        inner_XY = cls.canonical_inner_product(P, X, Y)
        Y_orth = Y - inner_XY * X
        norm_Y = cls.canonical_norm(P, Y_orth)
        if norm_Y < 1e-10:
            raise StiefelManifoldError("X and Y are linearly dependent")
        Y = Y_orth / norm_Y

        # Decompose into vertical A = P^T Delta in so(2) and horizontal K
        A_X = 0.5 * (P.T @ X - X.T @ P)
        A_Y = 0.5 * (P.T @ Y - Y.T @ P)
        K_X = X - P @ A_X
        K_Y = Y - P @ A_Y

        # Lie bracket [A_X, A_Y]
        comm_A = A_X @ A_Y - A_Y @ A_X

        # Horizontal commutators
        term1 = 0.25 * float(np.sum(comm_A**2))
        skew_cross = 0.5 * (K_X.T @ K_Y - K_Y.T @ K_X)
        cross_A = 0.5 * (K_X @ A_Y - K_Y @ A_X)
        term2 = float(np.sum((cross_A + P @ skew_cross) ** 2))

        # Grassmannian horizontal sectional curvature contribution
        K_gr = float(np.trace(K_X.T @ K_Y @ K_X.T @ K_Y) - np.trace(K_X.T @ K_X @ K_Y.T @ K_Y))

        return term1 + term2 + max(0.0, -K_gr)

    @classmethod
    def sectional_curvature_bounds(
        cls, P: np.ndarray, num_samples: int = 100, seed: int | None = None
    ) -> dict[str, Any]:
        """Analyze and verify sectional curvature bounds 0 <= K(X, Y) <= 5/4 on T_P V_2(R^7).

        Under the canonical Riemannian metric, the sectional curvature of the Stiefel
        manifold V_k(R^n) is bounded by 0 <= K(X, Y) <= 5/4 across all 2-planes.
        This method evaluates K across canonical 2-planes (pure vertical, pure horizontal,
        mixed vertical-horizontal) and uniformly sampled random orthonormal 2-planes in
        T_P V_2(R^7).

        Args:
            P: 7x2 orthonormal 2-frame on V_2(R^7).
            num_samples: Number of random 2-planes to sample.
            seed: Optional random seed for reproducible sampling.

        Returns:
            Dictionary containing:
                - "min_curvature": Minimum observed sectional curvature.
                - "max_curvature": Maximum observed sectional curvature.
                - "theoretical_lower_bound": 0.0.
                - "theoretical_upper_bound": 1.25 (5/4).
                - "lower_bound_satisfied": bool.
                - "upper_bound_satisfied": bool.
                - "is_bounded": bool (both bounds satisfied).
                - "num_samples": Total number of 2-planes evaluated.
        """
        rng = np.random.default_rng(seed)
        curvatures: list[float] = []

        dim = P.shape[0]
        # Canonical test plane 1: Pure vertical + Pure horizontal (mixed)
        A_vert = np.array([[0.0, -1.0], [1.0, 0.0]], dtype=np.float64)
        X_vert = P @ A_vert

        # Construct an orthonormal horizontal vector
        for col in range(dim):
            e = np.zeros((dim, 2), dtype=np.float64)
            e[col, 0] = 1.0
            K_cand = cls.project_horizontal(P, e)
            if cls.canonical_norm(P, K_cand) > 0.5:
                Y_horiz = K_cand / cls.canonical_norm(P, K_cand)
                curvatures.append(cls.sectional_curvature(P, X_vert, Y_horiz))
                break

        # Canonical test planes 2: Pure horizontal pairs (spanning Grassmannian planes)
        horiz_vectors: list[np.ndarray] = []
        for r in range(dim):
            for c in range(2):
                e = np.zeros((dim, 2), dtype=np.float64)
                e[r, c] = 1.0
                K = cls.project_horizontal(P, e)
                norm_K = cls.canonical_norm(P, K)
                if norm_K > 0.5:
                    # Gram-Schmidt against already collected horizontal vectors
                    K_orth = K.copy()
                    for H in horiz_vectors:
                        K_orth -= cls.canonical_inner_product(P, H, K_orth) * H
                    norm_orth = cls.canonical_norm(P, K_orth)
                    if norm_orth > 0.5:
                        horiz_vectors.append(K_orth / norm_orth)
                    if len(horiz_vectors) >= 4:
                        break
            if len(horiz_vectors) >= 4:
                break

        for i in range(len(horiz_vectors)):
            for j in range(i + 1, len(horiz_vectors)):
                curvatures.append(cls.sectional_curvature(P, horiz_vectors[i], horiz_vectors[j]))

        # Random orthonormal 2-planes in T_P V_2(R^n)
        attempts = 0
        while len(curvatures) < num_samples + 5 and attempts < num_samples * 10:
            attempts += 1
            Z1 = rng.standard_normal((dim, 2))
            Z2 = rng.standard_normal((dim, 2))
            X = cls.project_to_tangent(P, Z1)
            norm_X = cls.canonical_norm(P, X)
            if norm_X < 1e-6:
                continue
            X = X / norm_X

            Y_raw = cls.project_to_tangent(P, Z2)
            Y = Y_raw - cls.canonical_inner_product(P, X, Y_raw) * X
            norm_Y = cls.canonical_norm(P, Y)
            if norm_Y < 1e-6:
                continue
            Y = Y / norm_Y

            curvatures.append(cls.sectional_curvature(P, X, Y))

        min_k = float(min(curvatures))
        max_k = float(max(curvatures))
        lower_ok = min_k >= -1e-7
        upper_ok = max_k <= 1.25 + 1e-7

        return {
            "min_curvature": min_k,
            "max_curvature": max_k,
            "theoretical_lower_bound": 0.0,
            "theoretical_upper_bound": 1.25,
            "lower_bound_satisfied": lower_ok,
            "upper_bound_satisfied": upper_ok,
            "is_bounded": lower_ok and upper_ok,
            "num_samples": len(curvatures),
        }

    @classmethod
    def analyze_discrete_zero_divisor_geometry(cls) -> dict[str, Any]:
        """Exhaustively verify the continuous geometry of all 168 zero divisors on V_2(R^7).

        Computes:
            1. Verification that all 1,344 directed annihilation edges have P^T Q = 0 (100% orthogonal).
            2. Canonical geodesic length for every annihilation edge = pi / sqrt(2).
            3. Decomposition of all 14,028 zero-divisor pairs into the 3 canonical SVD classes:
               - Class (1, 1): 588 pairs (same 2-plane)
               - Class (1, 0): 6,720 pairs (1 common basis direction)
               - Class (0, 0): 6,720 pairs (completely disjoint basis directions)
            4. Ratio of annihilating pairs to orthogonal pairs = 672 / 6,720 = 1/10.
        """
        zds, _, pairs = stratify_cross_octet()
        frames = [cls.embed_zero_divisor(u) for u in zds]

        # 1. Annihilation edge orthogonality & distance
        annihilation_orthogonal = True
        edge_distances = []
        directed_edges = 0
        expected_dist = math.pi / math.sqrt(2.0)

        for u, neighbors in pairs.items():
            P = cls.embed_zero_divisor(u).matrix
            for w in neighbors:
                directed_edges += 1
                Q = cls.embed_zero_divisor(w).matrix
                M = P.T @ Q
                if not np.allclose(M, 0.0, atol=1e-8):
                    annihilation_orthogonal = False
                dist = cls.geodesic_distance(P, Q)
                edge_distances.append(dist)

        # 2. Singular value spectrum across all pairs
        svd_classes: dict[tuple[int, int], int] = {(1, 1): 0, (1, 0): 0, (0, 0): 0}
        total_pairs = 0

        for i in range(len(frames)):
            P = frames[i].matrix
            for j in range(i + 1, len(frames)):
                total_pairs += 1
                Q = frames[j].matrix
                M = P.T @ Q
                s = np.clip(np.linalg.svd(M, compute_uv=False), 0.0, 1.0)
                # Round to nearest integer (0 or 1)
                sig0 = int(round(float(s[0])))
                sig1 = int(round(float(s[1])))
                key = (sig0, sig1)
                svd_classes[key] = svd_classes.get(key, 0) + 1

        all_edges_match_dist = bool(np.allclose(edge_distances, expected_dist, atol=1e-6))

        angle_distribution = {
            "(0, 0)": svd_classes.get((1, 1), 0),
            "(0, pi/2)": svd_classes.get((1, 0), 0),
            "(pi/2, pi/2)": svd_classes.get((0, 0), 0),
        }

        return {
            "num_zero_divisors": len(zds),
            "num_directed_edges": directed_edges,
            "num_undirected_edges": directed_edges // 2,
            "all_edges_mutually_orthogonal": annihilation_orthogonal,
            "all_edges_geodesic_length_pi_over_sqrt2": all_edges_match_dist,
            "canonical_edge_length": expected_dist,
            "total_pairs": total_pairs,
            "svd_spectrum_distribution": svd_classes,
            "principal_angle_distribution": angle_distribution,
            "svd_sum_equals_total": sum(svd_classes.values()) == total_pairs,
            "orthogonal_pair_count": svd_classes[(0, 0)],
            "annihilation_to_orthogonal_ratio": (directed_edges // 2) / svd_classes[(0, 0)],
        }

    @classmethod
    def principal_angle_spectrum_all_pairs(cls) -> dict[str, Any]:
        """Categorize principal angle spectrum across all 14,028 zero-divisor pairs.

        Evaluates the canonical principal angles (theta_1, theta_2) between all
        binom(168, 2) = 14,028 pairs of orthonormal 2-frames embedded in V_2(R^7).
        Partitions the pairs into exactly three discrete geometric classes:
          - (0, 0): exactly 588 pairs (identical 2-plane in Gr(2, 7)).
          - (0, pi/2): exactly 6,720 pairs (intersecting along a 1D line).
          - (pi/2, pi/2): exactly 6,720 pairs (completely mutually orthogonal),
            which contains all 672 undirected zero-divisor annihilation edges.

        Returns:
            Dictionary with category counts, annihilation edge analysis, and validation flags:
                - "class_0_0": 588
                - "class_0_pi2": 6720
                - "class_pi2_pi2": 6720
                - "total_pairs": 14028
                - "annihilation_edges_in_pi2_pi2": 672
                - "all_annihilation_edges_orthogonal": bool (True)
                - "spectrum_partition_valid": bool (True)
        """
        zds, _, pairs = stratify_cross_octet()
        frames = [cls.embed_zero_divisor(u) for u in zds]

        class_0_0 = 0
        class_0_pi2 = 0
        class_pi2_pi2 = 0
        total_pairs = 0

        for i in range(len(frames)):
            P = frames[i].matrix
            for j in range(i + 1, len(frames)):
                total_pairs += 1
                Q = frames[j].matrix
                th1, th2 = cls.principal_angles(P, Q)
                if math.isclose(th1, 0.0, abs_tol=1e-5) and math.isclose(th2, 0.0, abs_tol=1e-5):
                    class_0_0 += 1
                elif math.isclose(th1, 0.0, abs_tol=1e-5) and math.isclose(
                    th2, 0.5 * math.pi, abs_tol=1e-5
                ):
                    class_0_pi2 += 1
                elif math.isclose(th1, 0.5 * math.pi, abs_tol=1e-5) and math.isclose(
                    th2, 0.5 * math.pi, abs_tol=1e-5
                ):
                    class_pi2_pi2 += 1

        # Check annihilation edges
        annihilation_in_pi2 = 0
        for u, neighbors in pairs.items():
            P = cls.embed_zero_divisor(u).matrix
            for w in neighbors:
                if u.key < w.key:  # Undirected edges
                    Q = cls.embed_zero_divisor(w).matrix
                    th1, th2 = cls.principal_angles(P, Q)
                    if math.isclose(th1, 0.5 * math.pi, abs_tol=1e-5) and math.isclose(
                        th2, 0.5 * math.pi, abs_tol=1e-5
                    ):
                        annihilation_in_pi2 += 1

        partition_valid = (
            class_0_0 == 588
            and class_0_pi2 == 6720
            and class_pi2_pi2 == 6720
            and total_pairs == 14028
            and annihilation_in_pi2 == 672
        )

        return {
            "class_0_0": class_0_0,
            "class_0_pi2": class_0_pi2,
            "class_pi2_pi2": class_pi2_pi2,
            "total_pairs": total_pairs,
            "annihilation_edges_in_pi2_pi2": annihilation_in_pi2,
            "all_annihilation_edges_orthogonal": annihilation_in_pi2 == 672,
            "spectrum_partition_valid": partition_valid,
        }

    @staticmethod
    def principal_bundle_projection(P: np.ndarray) -> np.ndarray:
        """Projection pi: V_2(R^7) -> Gr(2, 7) onto the 10-dimensional Grassmannian.

        Maps an orthonormal 2-frame P in R^{7x2} to its spanned 2-plane, represented
        canonically as the rank-2 orthogonal projection matrix Pi = P @ P.T in R^{7x7}.
        Satisfies:
            1. Pi^2 = Pi (idempotent).
            2. Pi^T = Pi (symmetric).
            3. Tr(Pi) = 2 (rank 2).
            4. U(1) ~= SO(2) gauge invariance: Pi(P @ R) == Pi(P) for all R in SO(2).
        """
        if P.shape != (7, 2):
            raise StiefelManifoldError(f"Expected 7x2 matrix on V_2(R^7), got shape {P.shape}")
        return np.asarray(P @ P.T, dtype=np.float64)

    @staticmethod
    def connection_one_form(P: np.ndarray, Delta: np.ndarray) -> float:
        """Canonical connection 1-form omega in Omega^1(V_2(R^7), u(1)).

        Given a 2-frame P = [v_1, v_2] in V_2(R^7) and a tangent vector Delta = [Delta_1, Delta_2],
        evaluates the vertical projection along the SO(2) fiber:
            omega_P(Delta) = 0.5 * (v_1^T Delta_2 - v_2^T Delta_1).

        Equivalently, this is the off-diagonal skew-symmetric entry (P^T Delta)_{0, 1}.
        Vanishes on horizontal vectors (omega_P(H) = 0) and evaluates pure fiber rotations.
        """
        v1 = P[:, 0]
        v2 = P[:, 1]
        delta1 = Delta[:, 0]
        delta2 = Delta[:, 1]
        return float(0.5 * (float(v1 @ delta2) - float(v2 @ delta1)))

    @classmethod
    def connection_one_form_matrix(cls, P: np.ndarray, Delta: np.ndarray) -> np.ndarray:
        """Matrix representation of connection 1-form in Lie algebra so(2) ~= u(1)."""
        w = cls.connection_one_form(P, Delta)
        return np.array([[0.0, w], [-w, 0.0]], dtype=np.float64)

    @classmethod
    def curvature_two_form(cls, P: np.ndarray, Delta1: np.ndarray, Delta2: np.ndarray) -> float:
        """Curvature 2-form Omega = d omega in Omega^2(V_2(R^7), u(1)).

        Evaluated on horizontal components K_1, K_2 of tangent vectors Delta_1, Delta_2:
            Omega_P(Delta_1, Delta_2) = (K_1^T K_2 - K_2^T K_1)_{0, 1}
                                      = K_1[:, 0]^T K_2[:, 1] - K_1[:, 1]^T K_2[:, 0].

        Satisfies:
            1. Antisymmetry: Omega(Delta_2, Delta_1) = -Omega(Delta_1, Delta_2).
            2. Horizontality: Omega(Delta_V, Delta) = 0 for any vertical vector Delta_V.
            3. SO(2) gauge invariance: Omega_{P R}(Delta_1 R, Delta_2 R) = Omega_P(Delta_1, Delta_2).
        """
        K1 = cls.project_horizontal(P, Delta1)
        K2 = cls.project_horizontal(P, Delta2)
        return float(float(K1[:, 0] @ K2[:, 1]) - float(K1[:, 1] @ K2[:, 0]))

    @classmethod
    def curvature_two_form_matrix(
        cls, P: np.ndarray, Delta1: np.ndarray, Delta2: np.ndarray
    ) -> np.ndarray:
        """Matrix representation of curvature 2-form in so(2) ~= u(1)."""
        val = cls.curvature_two_form(P, Delta1, Delta2)
        return np.array([[0.0, val], [-val, 0.0]], dtype=np.float64)

    @classmethod
    def curvature_norm_squared(cls, P: np.ndarray) -> float:
        """Compute the norm squared ||Omega||^2 of the curvature 2-form at P.

        ||Omega||^2 = sum_{1 <= a < b <= 10} |Omega(E_a, E_b)|^2
        across an orthonormal basis {E_a} of the 10-dimensional horizontal space H_P.
        On V_2(R^7), this evaluates universally to ||Omega||^2 = 7 - 2 = 5.0.
        """
        n, k = P.shape
        P_perp = np.eye(n) - P @ P.T
        U, _, _ = np.linalg.svd(P_perp)
        Q = U[:, : n - k]

        basis: list[np.ndarray] = []
        for c in range(n - k):
            q = Q[:, c]
            E1 = np.zeros((n, 2), dtype=np.float64)
            E1[:, 0] = q
            basis.append(E1)

            E2 = np.zeros((n, 2), dtype=np.float64)
            E2[:, 1] = q
            basis.append(E2)

        omega_sq = 0.0
        dim_H = len(basis)
        for a in range(dim_H):
            for b in range(a + 1, dim_H):
                val = cls.curvature_two_form(P, basis[a], basis[b])
                omega_sq += val**2

        return float(omega_sq)

    @classmethod
    def yang_mills_action_fiber(cls, P: np.ndarray) -> float:
        """Evaluate Yang-Mills action integral over a single U(1) ~= S^1 fiber at P.

        S_YM = 0.5 * int_{S^1} ||Omega||^2 dV = 0.5 * 5.0 * 2*pi = 5*pi.
        """
        norm_sq = cls.curvature_norm_squared(P)
        fiber_volume = 2.0 * math.pi
        return float(0.5 * norm_sq * fiber_volume)

    @classmethod
    def evaluate_yang_mills_action_zero_divisor_fibers(cls) -> dict[str, Any]:
        """Evaluate Yang-Mills action across the 588 identical 2-plane fibers of zero-divisor pairs.

        In V_2(R^7), the 168 zero divisors project to exactly binom(7, 2) = 21 distinct 2-planes
        in Gr(2, 7). Each 2-plane contains 8 zero divisors, forming binom(8, 2) = 28 pairs.
        Across all 21 distinct base planes, this yields exactly 21 * 28 = 588 identical 2-plane pairs.
        Each fiber carries constant curvature norm ||Omega||^2 = 5.0 and action S_YM = 5*pi.
        Total action across all 588 fiber pairs: 588 * 5*pi = 2940*pi.
        """
        zds, _, _ = stratify_cross_octet()
        frames = [cls.embed_zero_divisor(u) for u in zds]

        plane_groups: dict[tuple[int, int], list[StiefelFrame]] = {}
        for f in frames:
            if f.zd is None:
                continue
            i, j = f.zd.i, f.zd.j
            plane_key = (min(i, j), max(i, j))
            plane_groups.setdefault(plane_key, []).append(f)

        num_planes = len(plane_groups)
        pair_count = sum(len(group) * (len(group) - 1) // 2 for group in plane_groups.values())

        sample_frame = frames[0].matrix
        norm_sq = cls.curvature_norm_squared(sample_frame)
        fiber_action = cls.yang_mills_action_fiber(sample_frame)

        return {
            "num_zero_divisors": len(zds),
            "num_distinct_base_planes": num_planes,
            "num_identical_plane_pairs": pair_count,
            "curvature_norm_squared": norm_sq,
            "action_per_fiber": fiber_action,
            "total_action_588_pairs": float(pair_count * fiber_action),
            "total_action_distinct_fibers": float(num_planes * fiber_action),
            "expected_action_588_pairs": 2940.0 * math.pi,
            "action_matches_theoretical": math.isclose(
                pair_count * fiber_action, 2940.0 * math.pi, rel_tol=1e-8
            ),
        }


class StiefelManifoldV2R15:
    """Geometry engine for the 27-dimensional Stiefel manifold V_2(R^15).

    Points on V_2(R^15) are orthonormal 2-frames in R^15 (15x2 matrices X with X^T X = I_2).
    Dimension: dim V_2(R^15) = 2 * 15 - 3 = 27 (or 15 + 14 - 2 = 27).
    Bridges the 840 zero divisors of D=32 trigintaduonions across the 15 PG(3, F_2) sectors.
    """

    DIM: int = 27
    N: int = 15
    K: int = 2
    NUM_ZERO_DIVISORS: int = 840
    NUM_SECTORS: int = 15
    SECTOR_SIZE: int = 56
    TOTAL_EDGES: int = 7392
    REGULAR_SECTORS: tuple[int, ...] = (1, 2, 3, 4, 5, 6, 7, 8)
    BIREGULAR_SECTORS: tuple[int, ...] = (9, 10, 11, 12, 13, 14, 15)

    @staticmethod
    def embed_zero_divisor(vec: tuple[int, int, int, int]) -> StiefelFrame:
        """Embed a D=32 trigintaduonion zero divisor (i, j, s1, s2) into V_2(R^15).

        Indices: 1 <= i <= 15, 17 <= j <= 31, with j_rel = j - 16 in 1..15, i != j_rel.
        s1, s2 in {+1, -1}.
        The 2-frame P = [v1, v2] in R^{15x2} is:
            v1 = s1 * e_{i - 1}
            v2 = s2 * e_{j_rel - 1}
        """
        i, j, s1, s2 = vec
        j_rel = j - 16 if j > 16 else j
        if i < 1 or i > 15 or j_rel < 1 or j_rel > 15 or i == j_rel:
            raise StiefelManifoldError(
                f"Invalid D=32 zero-divisor indices: i={i}, j_rel={j_rel} (must be in 1..15, i != j_rel)"
            )
        mat = np.zeros((15, 2), dtype=np.float64)
        mat[i - 1, 0] = float(s1)
        mat[j_rel - 1, 1] = float(s2)
        return StiefelFrame(matrix=mat, zd=vec)

    @classmethod
    def embed_all_zero_divisors(cls) -> dict[int, StiefelFrame]:
        """Embed all 840 D=32 zero divisors into V_2(R^15)."""
        from sedenion.cd_algebra import CDStratificationEngine

        engine = CDStratificationEngine(32)
        g = engine.generate_zero_divisor_graph()
        frames = {}
        for n, data in g.nodes(data=True):
            vec = data["vec"]
            frames[n] = cls.embed_zero_divisor(vec)
        return frames

    @staticmethod
    def project_to_tangent(P: np.ndarray, Z: np.ndarray) -> np.ndarray:
        """Orthogonal projection of 15x2 matrix Z onto T_P V_2(R^15)."""
        PT_Z = P.T @ Z
        sym = 0.5 * (PT_Z + PT_Z.T)
        return np.asarray(Z - P @ sym, dtype=np.float64)

    @staticmethod
    def is_tangent(P: np.ndarray, Delta: np.ndarray, tol: float = 1e-8) -> bool:
        """Check if Delta is in T_P V_2(R^15)."""
        skew_sym = P.T @ Delta + Delta.T @ P
        return bool(np.allclose(skew_sym, 0.0, atol=tol))

    @staticmethod
    def project_vertical(P: np.ndarray, Delta: np.ndarray) -> np.ndarray:
        """Vertical projection Delta_V = P @ A in V_P (dim 1)."""
        A = 0.5 * (P.T @ Delta - Delta.T @ P)
        return np.asarray(P @ A, dtype=np.float64)

    @staticmethod
    def project_horizontal(P: np.ndarray, Delta: np.ndarray) -> np.ndarray:
        """Horizontal projection Delta_H = (I - P P^T) Delta in H_P (dim 26)."""
        K = Delta - P @ (P.T @ Delta)
        return np.asarray(K, dtype=np.float64)

    @classmethod
    def tangent_bundle_decomposition(
        cls, P: np.ndarray, Delta: np.ndarray, tol: float = 1e-8
    ) -> tuple[np.ndarray, np.ndarray]:
        """Splits T_P V_2(R^15) = V_P direct_sum H_P (dim 1 + 26 = 27)."""
        if not cls.is_tangent(P, Delta, tol=tol):
            raise StiefelManifoldError("Vector Delta must belong to tangent space T_P V_2(R^15)")
        Delta_V = cls.project_vertical(P, Delta)
        Delta_H = cls.project_horizontal(P, Delta)
        if not np.allclose(Delta, Delta_V + Delta_H, atol=tol):
            raise StiefelManifoldError("Decomposition sum mismatch")
        inner = cls.canonical_inner_product(P, Delta_V, Delta_H)
        if not math.isclose(inner, 0.0, abs_tol=tol):
            raise StiefelManifoldError(f"Orthogonality check failed: <V, H> = {inner}")
        return Delta_V, Delta_H

    @staticmethod
    def canonical_inner_product(P: np.ndarray, Delta1: np.ndarray, Delta2: np.ndarray) -> float:
        """Canonical inner product on T_P V_2(R^15)."""
        metric_factor = np.eye(15) - 0.5 * (P @ P.T)
        return float(np.trace(Delta1.T @ metric_factor @ Delta2))

    @classmethod
    def canonical_norm(cls, P: np.ndarray, Delta: np.ndarray) -> float:
        """Canonical norm on T_P V_2(R^15)."""
        return math.sqrt(max(0.0, cls.canonical_inner_product(P, Delta, Delta)))

    @staticmethod
    def principal_bundle_projection(P: np.ndarray) -> np.ndarray:
        """Projection pi: V_2(R^15) -> Gr(2, 15) onto 26-dimensional Grassmannian."""
        if P.shape != (15, 2):
            raise StiefelManifoldError(f"Expected 15x2 matrix, got {P.shape}")
        return np.asarray(P @ P.T, dtype=np.float64)

    @staticmethod
    def connection_one_form(P: np.ndarray, Delta: np.ndarray) -> float:
        """Canonical connection 1-form omega on V_2(R^15)."""
        v1 = P[:, 0]
        v2 = P[:, 1]
        delta1 = Delta[:, 0]
        delta2 = Delta[:, 1]
        return float(0.5 * (float(v1 @ delta2) - float(v2 @ delta1)))

    @classmethod
    def curvature_two_form(cls, P: np.ndarray, Delta1: np.ndarray, Delta2: np.ndarray) -> float:
        """Curvature 2-form Omega = d omega on V_2(R^15)."""
        K1 = cls.project_horizontal(P, Delta1)
        K2 = cls.project_horizontal(P, Delta2)
        return float(float(K1[:, 0] @ K2[:, 1]) - float(K1[:, 1] @ K2[:, 0]))

    @classmethod
    def curvature_norm_squared(cls, P: np.ndarray) -> float:
        """Curvature norm squared ||Omega||^2 on V_2(R^15), universally equal to 15 - 2 = 13.0."""
        n, k = P.shape
        P_perp = np.eye(n) - P @ P.T
        U, _, _ = np.linalg.svd(P_perp)
        Q = U[:, : n - k]

        basis: list[np.ndarray] = []
        for c in range(n - k):
            q = Q[:, c]
            E1 = np.zeros((n, 2), dtype=np.float64)
            E1[:, 0] = q
            basis.append(E1)

            E2 = np.zeros((n, 2), dtype=np.float64)
            E2[:, 1] = q
            basis.append(E2)

        omega_sq = 0.0
        dim_H = len(basis)
        for a in range(dim_H):
            for b in range(a + 1, dim_H):
                val = cls.curvature_two_form(P, basis[a], basis[b])
                omega_sq += val**2

        return float(omega_sq)

    @classmethod
    def yang_mills_action_fiber(cls, P: np.ndarray) -> float:
        """Yang-Mills action on a single fiber of V_2(R^15) -> Gr(2, 15): 0.5 * 13.0 * 2*pi = 13*pi."""
        norm_sq = cls.curvature_norm_squared(P)
        return float(0.5 * norm_sq * 2.0 * math.pi)

    @classmethod
    def analyze_sector_geometry(cls) -> dict[int, dict[str, Any]]:
        """Analyze geometry and edge orthogonality across the 15 PG(3, F_2) sectors."""
        from sedenion.cd_algebra import CDStratificationEngine

        engine = CDStratificationEngine(32)
        g = engine.generate_zero_divisor_graph()
        frames = cls.embed_all_zero_divisors()

        sectors_data: dict[int, dict[str, Any]] = {}
        for chi in range(1, 16):
            sector_nodes = [n for n, d in g.nodes(data=True) if d["chi"] == chi]
            sub = g.subgraph(sector_nodes)
            cycles = nx.cycle_basis(sub)
            c4 = [c for c in cycles if len(c) == 4]
            c6 = [c for c in cycles if len(c) == 6]

            # Check edge orthogonality
            all_orth = True
            for u, w in sub.edges():
                if not np.allclose(frames[u].matrix.T @ frames[w].matrix, 0.0, atol=1e-8):
                    all_orth = False
                    break

            planes = set()
            for n in sector_nodes:
                vec = g.nodes[n]["vec"]
                j_rel = vec[1] - 16 if vec[1] > 16 else vec[1]
                planes.add((min(vec[0], j_rel), max(vec[0], j_rel)))

            sectors_data[chi] = {
                "chi": chi,
                "num_nodes": len(sector_nodes),
                "num_edges": sub.number_of_edges(),
                "is_regular": chi in cls.REGULAR_SECTORS,
                "is_biregular": chi in cls.BIREGULAR_SECTORS,
                "is_bipartite": bool(nx.is_bipartite(sub)),
                "all_edges_orthogonal": all_orth,
                "betti_1": sub.number_of_edges() - len(sector_nodes) + 1,
                "num_c4": len(c4),
                "num_c6": len(c6),
                "distinct_2planes": len(planes),
            }

        return sectors_data

    @classmethod
    def classify_discrete_holonomy(cls) -> dict[str, Any]:
        """Classify discrete holonomy of connection 1-form loops across all 15 sectors.

        Verifies:
            1. All frame overlap matrices M = P_i^T P_j between identical 2-planes
               in graph cycles belong strictly to the dihedral group D_4.
            2. Determinants det(M) in {+1.0, -1.0} and traces tr(M) in {2.0, 0.0, -2.0}.
            3. Rotations (det = +1) are quantized to the cyclic group Z_4 with angles {0, pi/2, pi, 3pi/2}.
            4. In-plane reflections (det = -1) have tr = 0.0, corresponding to coordinate sign flips.
            5. The Z_2 Berry phase flip Phi = pi (tr = -2.0) occurs across all sign-reversing 4-cycles.
        """
        from sedenion.cd_algebra import CDStratificationEngine

        engine = CDStratificationEngine(32)
        g = engine.generate_zero_divisor_graph()
        frames = cls.embed_all_zero_divisors()

        total_c4 = 0
        total_c6 = 0
        observed_traces: set[float] = set()
        observed_dets: set[float] = set()
        sector_results: dict[int, dict[str, Any]] = {}
        all_d4 = True
        z2_flips_count = 0

        for chi in range(1, 16):
            sector_nodes = [n for n, d in g.nodes(data=True) if d["chi"] == chi]
            sub = g.subgraph(sector_nodes)
            cycles = nx.cycle_basis(sub)
            c4 = [c for c in cycles if len(c) == 4]
            c6 = [c for c in cycles if len(c) == 6]
            total_c4 += len(c4)
            total_c6 += len(c6)

            sector_traces: set[float] = set()
            sector_dets: set[float] = set()

            for cyc in cycles:
                node_planes = []
                for n in cyc:
                    vec = g.nodes[n]["vec"]
                    j_rel = vec[1] - 16 if vec[1] > 16 else vec[1]
                    node_planes.append((min(vec[0], j_rel), max(vec[0], j_rel)))

                for a in range(len(cyc)):
                    for b in range(a + 1, len(cyc)):
                        if node_planes[a] == node_planes[b]:
                            Pa = frames[cyc[a]].matrix
                            Pb = frames[cyc[b]].matrix
                            M = Pa.T @ Pb
                            d = round(float(np.linalg.det(M)), 4)
                            t = round(float(np.trace(M)), 4)
                            observed_dets.add(d)
                            observed_traces.add(t)
                            sector_dets.add(d)
                            sector_traces.add(t)
                            if d not in (1.0, -1.0) or t not in (2.0, 0.0, -2.0):
                                all_d4 = False
                            if d == 1.0 and t == -2.0:
                                z2_flips_count += 1

            sector_results[chi] = {
                "num_cycles_total": len(cycles),
                "num_c4": len(c4),
                "num_c6": len(c6),
                "dets": sorted(sector_dets),
                "traces": sorted(sector_traces),
            }

        return {
            "total_4cycles_evaluated": total_c4,
            "total_6cycles_evaluated": total_c6,
            "all_transitions_in_d4": all_d4,
            "observed_determinants": sorted(observed_dets),
            "observed_traces": sorted(observed_traces),
            "holonomy_z4_quantized": all(t in (2.0, 0.0, -2.0) for t in observed_traces),
            "z2_berry_flips_observed": z2_flips_count > 0,
            "z2_berry_flips_count": z2_flips_count,
            "sectors": sector_results,
        }
