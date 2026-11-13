"""TowerStiefelEngine: Higher-Dimensional Stiefel Manifold Discrete-Continuous Bridge.

Extends the discrete 2-frame geometry from V_2(R^7) (D=16) to arbitrary Cayley-Dickson
dimensions D = 2^n >= 16 on the Stiefel manifolds V_2(R^{D/2 - 1}).

Key Universal Theorems:
1. Universal Frame Census: For all D = 2^n >= 16 with m = D/2 - 1, the (D-2)(D-4)
   cross-half zero divisors span every coordinate 2-plane in R^m, with exactly
   T = binom(m, 2) = (D-2)(D-4)/8 planes, 8 frames per plane, and 4 signs per ordered pair.
2. Principal-Angle Trichotomy Law: Frame pairs partition into:
   - C_2(D) = 28 * T (same coordinate 2-plane)
   - C_1(D) = 64 * T * (D/2 - 3) (share 1 axis)
   - C_0(D) = 16 * T * (D/2 - 3) * (D/2 - 4) (completely orthogonal 2-frames)
   with C_2 + C_1 + C_0 = N(N - 1) / 2 identically.
3. Transversality & Complete Orthogonality: Same-charge pairs cannot share 1 axis.
   Every annihilating pair in any CD algebra carries completely orthogonal 2-frames
   (P_u^T P_w = 0), with geodesic distance pi / sqrt(2) on V_2(R^m).
4. Exact Linear Cubature & Vanishing Projection:
   - M_lin^T M_lin = 2(D - 4) * I_{2m}, where weight W(D) = 2(D - 4) is the exact size
     of a single connected component / charge sector across the entire tower.
   - M_lin^T A M_lin = 0_{(2m) x (2m)} vanishes identically.
5. 2-Form Tight Frame & Tracelessness:
   - M_wedge^T M_wedge = 8 * I_T.
   - Tr(M_wedge^T A M_wedge) = 0 identically for all D >= 16.
"""

from __future__ import annotations

import math
from typing import Dict, List, Tuple
import numpy as np

from sedenion.cd_algebra import cd_cross_vec_annihilates


class TowerStiefelEngine:
    """Analytical and computational engine for Stiefel frame geometry across the CD tower."""

    @staticmethod
    def ambient_dim(dim: int) -> int:
        """Dimension m of the ambient imaginary subspace R^m = Im(A_{n-1}) where m = D/2 - 1."""
        if dim < 16 or (dim & (dim - 1)) != 0:
            raise ValueError(f"Dimension must be a power of 2 >= 16, got {dim}")
        return dim // 2 - 1

    @staticmethod
    def stiefel_dim(dim: int) -> int:
        """Dimension of the Stiefel manifold V_2(R^m) = 2m - 3 = D - 5."""
        return dim - 5

    @staticmethod
    def num_coordinate_planes(dim: int) -> int:
        """Number of coordinate 2-planes T = binom(m, 2) = (D-2)(D-4)/8."""
        m = TowerStiefelEngine.ambient_dim(dim)
        return m * (m - 1) // 2

    @staticmethod
    def num_zero_divisors(dim: int) -> int:
        """Total number of cross-half zero divisors N = (D-2)(D-4) = 8 * T."""
        return (dim - 2) * (dim - 4)

    @classmethod
    def frame_census(cls, dim: int) -> Dict[str, int]:
        """Compute the principal-angle trichotomy counts for dimension dim."""
        m = cls.ambient_dim(dim)
        T = cls.num_coordinate_planes(dim)
        N = cls.num_zero_divisors(dim)

        c2 = 28 * T
        c1 = 64 * T * (dim // 2 - 3)
        c0 = 16 * T * (dim // 2 - 3) * (dim // 2 - 4)
        total_pairs = N * (N - 1) // 2

        if c2 + c1 + c0 != total_pairs:
            raise RuntimeError(f"Trichotomy sum {c2 + c1 + c0} != total pairs {total_pairs}")

        return {
            "dimension": dim,
            "ambient_dim": m,
            "stiefel_dim": cls.stiefel_dim(dim),
            "num_planes": T,
            "num_frames": N,
            "share_two_axes": c2,
            "share_one_axis": c1,
            "share_zero_axes": c0,
            "total_pairs": total_pairs,
        }

    @classmethod
    def cubature_weight(cls, dim: int) -> int:
        """Cubature weight of the linear coordinates W(D) = 2(D - 4)."""
        m = cls.ambient_dim(dim)
        return 4 * (m - 1)

    @classmethod
    def enumerate_cross_half_zds(cls, dim: int) -> List[Tuple[int, int, int, int]]:
        """Enumerate all (D-2)(D-4) cross-half zero divisors as (s1, i, s2, j)."""
        m = cls.ambient_dim(dim)
        zds: List[Tuple[int, int, int, int]] = []
        for i in range(1, m + 1):
            for j in range(1, m + 1):
                if i == j:
                    continue
                for s1 in (1, -1):
                    for s2 in (1, -1):
                        zds.append((s1, i, s2, j))
        return zds

    @classmethod
    def build_linear_harmonic_matrix(cls, dim: int) -> np.ndarray:
        """Build the N x (2m) matrix M_lin of linear coordinates (u, v)."""
        m = cls.ambient_dim(dim)
        zds = cls.enumerate_cross_half_zds(dim)
        N = len(zds)
        m_lin = np.zeros((N, 2 * m), dtype=float)
        for row, (s1, i, s2, j) in enumerate(zds):
            m_lin[row, i - 1] = float(s1)
            m_lin[row, m + j - 1] = float(s2)
        return m_lin

    @classmethod
    def build_wedge_harmonic_matrix(cls, dim: int) -> np.ndarray:
        """Build the N x T matrix M_wedge of 2-form coordinates u wedge v."""
        m = cls.ambient_dim(dim)
        T = cls.num_coordinate_planes(dim)
        zds = cls.enumerate_cross_half_zds(dim)
        N = len(zds)

        plane_to_idx: Dict[Tuple[int, int], int] = {}
        idx = 0
        for i in range(1, m + 1):
            for j in range(i + 1, m + 1):
                plane_to_idx[(i, j)] = idx
                idx += 1

        m_wedge = np.zeros((N, T), dtype=float)
        for row, (s1, i, s2, j) in enumerate(zds):
            plane = (min(i, j), max(i, j))
            pidx = plane_to_idx[plane]
            sign = float(s1 * s2) if i < j else float(-s1 * s2)
            m_wedge[row, pidx] = sign
        return m_wedge

    @classmethod
    def verify_linear_cubature(cls, dim: int) -> Tuple[bool, float]:
        """Verify M_lin^T M_lin = 2(D - 4) * I_{2m}."""
        m = cls.ambient_dim(dim)
        expected_weight = float(cls.cubature_weight(dim))
        m_lin = cls.build_linear_harmonic_matrix(dim)
        gram = m_lin.T @ m_lin
        expected = expected_weight * np.eye(2 * m)
        max_err = float(np.max(np.abs(gram - expected)))
        is_exact = bool(np.allclose(gram, expected, atol=1e-10))
        return is_exact, max_err

    @classmethod
    def verify_wedge_cubature(cls, dim: int) -> Tuple[bool, float]:
        """Verify M_wedge^T M_wedge = 8 * I_T."""
        T = cls.num_coordinate_planes(dim)
        m_wedge = cls.build_wedge_harmonic_matrix(dim)
        gram = m_wedge.T @ m_wedge
        expected = 8.0 * np.eye(T)
        max_err = float(np.max(np.abs(gram - expected)))
        is_exact = bool(np.allclose(gram, expected, atol=1e-10))
        return is_exact, max_err

    @classmethod
    def build_adjacency_matrix(cls, dim: int) -> np.ndarray:
        """Build the N x N annihilation adjacency matrix for dimension dim."""
        n = int(math.log2(dim)) - 1
        zds = cls.enumerate_cross_half_zds(dim)
        N = len(zds)
        adj = np.zeros((N, N), dtype=float)
        for a in range(N):
            s1, i, s2, j = zds[a]
            for b in range(a + 1, N):
                t1, k, t2, m_idx = zds[b]
                if cd_cross_vec_annihilates(n, s1, i, s2, j, t1, k, t2, m_idx):
                    adj[a, b] = 1.0
                    adj[b, a] = 1.0
        return adj

    @classmethod
    def verify_linear_projection_vanishes(cls, dim: int) -> Tuple[bool, float]:
        """Verify M_lin^T A M_lin = 0_{(2m) x (2m)} identically."""
        m_lin = cls.build_linear_harmonic_matrix(dim)
        adj = cls.build_adjacency_matrix(dim)
        proj = m_lin.T @ adj @ m_lin
        max_val = float(np.max(np.abs(proj)))
        return bool(max_val < 1e-10), max_val

    @classmethod
    def verify_wedge_projection_traceless(cls, dim: int) -> Tuple[bool, float]:
        """Verify Tr(M_wedge^T A M_wedge) = 0 identically."""
        m_wedge = cls.build_wedge_harmonic_matrix(dim)
        adj = cls.build_adjacency_matrix(dim)
        proj = m_wedge.T @ adj @ m_wedge
        trace_val = float(np.trace(proj))
        return bool(abs(trace_val) < 1e-10), trace_val

    @classmethod
    def wedge_projection_spectrum(cls, dim: int) -> Dict[float, int]:
        """Compute the exact eigenvalue spectrum of the normalized wedge projection operator.

        The normalized operator is (M_wedge^T A M_wedge) / 8.0.
        At D=16, eigenvalues are {-8 (x7), +4 (x14)}, matching the Lambda^2(R^7) = 7 + g2 decomposition.
        At D=32, eigenvalues are {-24 (x1), -12 (x21), -4 (x28), +4 (x27), +8 (x14), +12 (x14)}.
        """
        m_wedge = cls.build_wedge_harmonic_matrix(dim)
        adj = cls.build_adjacency_matrix(dim)
        proj = (m_wedge.T @ adj @ m_wedge) / 8.0

        evals = np.linalg.eigvalsh(proj)
        evals_rounded = np.round(evals, 4)
        unique, counts = np.unique(evals_rounded, return_counts=True)
        return {float(u): int(c) for u, c in zip(unique, counts)}
