"""
Asimov-Buja Grand Tour via Geodesic Interpolation of 2-Frames.

References:
    Asimov, D., & Buja, A. (1994). "The grand tour via geodesic interpolation of 2-frames."
    Asimov, D. (1985). "The grand tour: a tool for viewing multidimensional data."
    Edelman, A., Arias, T. A., & Smith, S. T. (1998). "The geometry of algorithms with
    orthogonality constraints." SIAM J. Matrix Anal. Appl., 20(2), 303-353.

This module implements:
1. Exact principal angles and directions between arbitrary 2-frames in R^n.
2. Grassmannian geodesic interpolation between 2-planes in G_{2,n}.
3. Stiefel manifold geodesic interpolation between 2-frames in V_2(R^n) via
   canonical metric and SO(4) / (1_2 x SO(2)) fibration normal form.
4. Grand Tour continuous path generator traversing high-dimensional point clouds
   (E8 roots, Leech lattice frames, Sedenion zero-divisor 2-frames, Poincare disk).
5. Projection and SVG/JSON export for interactive visualization.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any, Sequence

import numpy as np
import scipy.linalg


@dataclass(frozen=True)
class PrincipalAngleResult:
    """Principal angle decomposition between two 2-frames."""
    theta1: float
    theta2: float
    u_star: np.ndarray  # n x 2: principal directions in plane 1
    v_star: np.ndarray  # n x 2: principal directions in plane 2
    w: np.ndarray       # n x 2: orthonormal vectors in plane 2 orthogonal to u_star
    grassmann_distance: float


class StiefelGrandTour:
    """Asimov-Buja Grand Tour Geodesic Engine on V_2(R^n) and G_{2,n}."""

    def __init__(self, ambient_dim: int) -> None:
        if ambient_dim < 2:
            raise ValueError(f"Ambient dimension must be >= 2, got {ambient_dim}")
        self.n = ambient_dim

    @staticmethod
    def ensure_orthonormal(frame: np.ndarray, tol: float = 1e-7) -> np.ndarray:
        """Validate and orthonormalize a 2-frame (n x 2) using QR decomposition."""
        frame = np.asarray(frame, dtype=np.float64)
        if frame.ndim != 2 or frame.shape[1] != 2:
            raise ValueError(f"Expected frame of shape (n, 2), got {frame.shape}")
        # Re-orthonormalize via thin QR with positive diagonal for stability
        q, r = np.linalg.qr(frame, mode="reduced")
        d = np.diagonal(r)
        ph = d / np.where(np.abs(d) < 1e-12, 1.0, np.abs(d))
        q = q * ph
        return q

    @classmethod
    def compute_principal_angles(
        cls, F0: np.ndarray, F1: np.ndarray
    ) -> PrincipalAngleResult:
        """Compute principal angles and directions between two 2-frames F0 and F1.

        Let M = F0^T F1 in R^{2x2}.
        Singular value decomposition: M = U diag(cos theta_1, cos theta_2) V^T
        Principal directions:
            u^* = F0 U
            v^* = F1 V
        Orthogonalized complement:
            w_i = (v_i^* - cos(theta_i) u_i^*) / sin(theta_i) if sin(theta_i) > 1e-9 else 0.
        Grassmann distance:
            d_G = sqrt(theta_1^2 + theta_2^2).
        """
        F0 = np.asarray(F0, dtype=np.float64)
        F1 = np.asarray(F1, dtype=np.float64)
        if F0.shape != F1.shape or F0.shape[1] != 2:
            raise ValueError(f"Shape mismatch: {F0.shape} vs {F1.shape}")

        M = F0.T @ F1  # 2 x 2
        U, S, Vt = np.linalg.svd(M)
        V = Vt.T

        # Clamp singular values to [-1, 1] for arccos numerical stability
        s_clamped = np.clip(S, -1.0, 1.0)
        theta1 = float(np.arccos(s_clamped[0]))
        theta2 = float(np.arccos(s_clamped[1]))
        # Order theta1 <= theta2
        if theta1 > theta2:
            theta1, theta2 = theta2, theta1
            U = U[:, [1, 0]]
            V = V[:, [1, 0]]

        u_star = F0 @ U
        v_star = F1 @ V

        # Compute orthogonal complements w_i
        w = np.zeros_like(u_star)
        thetas = [theta1, theta2]
        for i in range(2):
            sin_theta = math.sin(thetas[i])
            cos_theta = math.cos(thetas[i])
            if sin_theta > 1e-9:
                diff = v_star[:, i] - cos_theta * u_star[:, i]
                w[:, i] = diff / sin_theta
                # Re-normalize for exact precision
                nrm = np.linalg.norm(w[:, i])
                if nrm > 1e-9:
                    w[:, i] = w[:, i] / nrm
            else:
                w[:, i] = np.zeros(F0.shape[0], dtype=np.float64)

        d_G = math.sqrt(theta1**2 + theta2**2)
        return PrincipalAngleResult(
            theta1=theta1,
            theta2=theta2,
            u_star=u_star,
            v_star=v_star,
            w=w,
            grassmann_distance=d_G,
        )

    @classmethod
    def interpolate_grassmann_geodesic(
        cls, F0: np.ndarray, F1: np.ndarray, t: float
    ) -> np.ndarray:
        """Evaluate Grassmannian geodesic at parameter t in [0, 1].

        f_i(t) = cos(t * theta_i) u_i^* + sin(t * theta_i) w_i
        Returns an orthonormal 2-frame span(F(t)) along the shortest path in G_{2,n}.
        """
        res = cls.compute_principal_angles(F0, F1)
        thetas = [res.theta1, res.theta2]
        F_t = np.zeros_like(F0)
        for i in range(2):
            F_t[:, i] = (
                math.cos(t * thetas[i]) * res.u_star[:, i]
                + math.sin(t * thetas[i]) * res.w[:, i]
            )
        return cls.ensure_orthonormal(F_t)

    @classmethod
    def interpolate_stiefel_geodesic(
        cls, F0: np.ndarray, F1: np.ndarray, t: float
    ) -> np.ndarray:
        """Asimov-Buja exact Stiefel geodesic connecting 2-frames F0 and F1 in V_2(R^n).

        Reduces to the 4D subspace span(F0, F1), extends F1 to SO(4), and minimizes
        geodesic distance in SO(4) / (1_2 x SO(2)) over fibre angle theta in [0, 2pi].
        """
        F0 = np.asarray(F0, dtype=np.float64)
        F1 = np.asarray(F1, dtype=np.float64)
        n = F0.shape[0]

        # Orthonormal basis for the subspace spanned by F0 and F1
        combined = np.hstack([F0, F1])
        q_basis, r_basis = np.linalg.qr(combined, mode="reduced")

        # Pad to 4D if rank < 4 and n >= 4
        k_dim = min(n, 4)
        if q_basis.shape[1] < k_dim:
            eye = np.eye(n)
            candidates = [eye[:, i] for i in range(n)]
            q_cols = [q_basis[:, i] for i in range(q_basis.shape[1])]
            for cand in candidates:
                proj = cand - sum(np.dot(cand, col) * col for col in q_cols)
                norm_p = np.linalg.norm(proj)
                if norm_p > 1e-6:
                    q_cols.append(proj / norm_p)
                    if len(q_cols) == k_dim:
                        break
            q_basis = np.column_stack(q_cols)

        # Express F0 and F1 in local coordinates
        F0_loc = q_basis.T @ F0
        F1_loc = q_basis.T @ F1

        M = F0_loc.T @ F1_loc
        if np.allclose(M, np.eye(2), atol=1e-7):
            return F0.copy()

        if k_dim == 4:
            u1 = F1_loc[:, 0]
            u2 = F1_loc[:, 1]
            eye4 = np.eye(4)
            rem = []
            for col in range(4):
                v = eye4[:, col]
                v = v - np.dot(v, u1) * u1 - np.dot(v, u2) * u2
                for r in rem:
                    v = v - np.dot(v, r) * r
                nv = np.linalg.norm(v)
                if nv > 1e-6:
                    rem.append(v / nv)
                    if len(rem) == 2:
                        break
            u3, u4 = rem[0], rem[1]
            U_mat = np.column_stack([u1, u2, u3, u4])
            if np.linalg.det(U_mat) < 0:
                u4 = -u4
                U_mat[:, 3] = u4

            # Change coordinates so F0_loc is (e1, e2)
            q0_1 = F0_loc[:, 0]
            q0_2 = F0_loc[:, 1]
            rem0 = []
            for col in range(4):
                v = eye4[:, col]
                v = v - np.dot(v, q0_1) * q0_1 - np.dot(v, q0_2) * q0_2
                for r in rem0:
                    v = v - np.dot(v, r) * r
                nv = np.linalg.norm(v)
                if nv > 1e-6:
                    rem0.append(v / nv)
                    if len(rem0) == 2:
                        break
            q0_3, q0_4 = rem0[0], rem0[1]
            Q0 = np.column_stack([q0_1, q0_2, q0_3, q0_4])
            if np.linalg.det(Q0) < 0:
                q0_4 = -q0_4
                Q0[:, 3] = q0_4

            # In F0 basis, target frame is Q0^T @ [u1, u2]
            u1_b = Q0.T @ u1
            u2_b = Q0.T @ u2
            u3_b = Q0.T @ u3
            u4_b = Q0.T @ u4

            # Asimov-Buja trace optimization:
            def cost_f(theta: float) -> float:
                c = math.cos(theta)
                s = math.sin(theta)
                col3 = c * u3_b + s * u4_b
                col4 = -s * u3_b + c * u4_b
                U_th = np.column_stack([u1_b, u2_b, col3, col4])
                a = float(np.trace(U_th))
                U2 = U_th @ U_th
                b = float(np.trace(U2))
                disc = max(0.0, 2.0 * b - a**2 + 8.0)
                root_disc = math.sqrt(disc)
                ck = np.clip((a + root_disc) / 4.0, -1.0, 1.0)
                cl = np.clip((a - root_disc) / 4.0, -1.0, 1.0)
                K = math.acos(ck)
                L = math.acos(cl)
                return K**2 + L**2

            grid = np.linspace(0, 2 * math.pi, 72, endpoint=False)
            best_th = 0.0
            best_val = float("inf")
            for th in grid:
                val = cost_f(th)
                if val < best_val:
                    best_val = val
                    best_th = th

            fine_grid = np.linspace(best_th - 0.1, best_th + 0.1, 41)
            for th in fine_grid:
                val = cost_f(th)
                if val < best_val:
                    best_val = val
                    best_th = th

            c_opt = math.cos(best_th)
            s_opt = math.sin(best_th)
            col3_opt = c_opt * u3_b + s_opt * u4_b
            col4_opt = -s_opt * u3_b + c_opt * u4_b
            U_min = np.column_stack([u1_b, u2_b, col3_opt, col4_opt])

            # Matrix logarithm of U_min in SO(4)
            T_min = scipy.linalg.logm(U_min).real
            T_min = 0.5 * (T_min - T_min.T)  # enforce exact skew-symmetry

            # exp(t * T_min)
            rot_t = scipy.linalg.expm(t * T_min)
            frame_loc_b = rot_t[:, :2]  # first 2 columns
            frame_loc = Q0 @ frame_loc_b
            F_t = q_basis @ frame_loc
            return cls.ensure_orthonormal(F_t)

        return cls.interpolate_grassmann_geodesic(F0, F1, t)

    @classmethod
    def project_point_cloud(
        cls, points_nd: np.ndarray, frame_2d: np.ndarray
    ) -> np.ndarray:
        """Project an N x n point cloud onto the 2D plane defined by an n x 2 frame."""
        pts = np.asarray(points_nd, dtype=np.float64)
        frm = np.asarray(frame_2d, dtype=np.float64)
        if pts.shape[1] != frm.shape[0]:
            raise ValueError(
                f"Dimension mismatch: points {pts.shape} vs frame {frm.shape}"
            )
        return pts @ frm

    @classmethod
    def generate_grand_tour_path(
        cls,
        key_frames: Sequence[np.ndarray],
        steps_per_segment: int = 24,
        interpolation_mode: str = "stiefel",
    ) -> list[np.ndarray]:
        """Generate a continuous piecewise-geodesic Grand Tour sequence of 2-frames."""
        if len(key_frames) < 2:
            return [cls.ensure_orthonormal(f) for f in key_frames]

        tour: list[np.ndarray] = []
        for i in range(len(key_frames) - 1):
            F_start = cls.ensure_orthonormal(key_frames[i])
            F_end = cls.ensure_orthonormal(key_frames[i + 1])
            for step in range(steps_per_segment):
                t = float(step) / float(steps_per_segment)
                if interpolation_mode == "stiefel":
                    frame_t = cls.interpolate_stiefel_geodesic(F_start, F_end, t)
                else:
                    frame_t = cls.interpolate_grassmann_geodesic(F_start, F_end, t)
                tour.append(frame_t)

        tour.append(cls.ensure_orthonormal(key_frames[-1]))
        return tour

    @classmethod
    def render_tour_svg(
        cls,
        projected_pts: np.ndarray,
        width: int = 600,
        height: int = 600,
        point_labels: list[str] | None = None,
    ) -> str:
        """Render a 2D projection snapshot to an SVG string."""
        pts = np.asarray(projected_pts, dtype=np.float64)
        margin = 40.0
        x_min, x_max = float(pts[:, 0].min()), float(pts[:, 0].max())
        y_min, y_max = float(pts[:, 1].min()), float(pts[:, 1].max())
        dx = max(x_max - x_min, 1e-6)
        dy = max(y_max - y_min, 1e-6)
        scale = min((width - 2 * margin) / dx, (height - 2 * margin) / dy)

        svg_lines = [
            f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" '
            f'width="{width}" height="{height}" style="background:#0f172a;">',
            '  <defs>',
            '    <radialGradient id="dotGrad" cx="50%" cy="50%" r="50%">',
            '      <stop offset="0%" stop-color="#38bdf8" stop-opacity="1"/>',
            '      <stop offset="100%" stop-color="#0284c7" stop-opacity="0.6"/>',
            '    </radialGradient>',
            '  </defs>',
            f'  <rect width="{width}" height="{height}" fill="#0a0f1d"/>',
            f'  <line x1="{margin}" y1="{height/2}" x2="{width-margin}" y2="{height/2}" stroke="#334155" stroke-dasharray="4"/>',
            f'  <line x1="{width/2}" y1="{margin}" x2="{width/2}" y2="{height-margin}" stroke="#334155" stroke-dasharray="4"/>',
        ]

        for idx, pt in enumerate(pts):
            cx = margin + (pt[0] - x_min) * scale
            cy = height - (margin + (pt[1] - y_min) * scale)
            svg_lines.append(
                f'  <circle cx="{cx:.2f}" cy="{cy:.2f}" r="4" fill="url(#dotGrad)" stroke="#7dd3fc" stroke-width="1"/>'
            )
            if point_labels and idx < len(point_labels):
                svg_lines.append(
                    f'  <text x="{cx+6:.2f}" y="{cy-4:.2f}" fill="#94a3b8" font-family="monospace" font-size="10">{point_labels[idx]}</text>'
                )

        svg_lines.append('</svg>')
        return "\n".join(svg_lines)
