r"""
Random Knots via Stiefel Manifolds, Beta Distance Laws, and Sedenion 2-Frames (HYP-236).

Grounded in:
- Alexander Kolpakov & Igor Rivin (2026):
  "Random Knots via Stiefel manifolds"
  (/data/mind/cognition/library/Random Knots via Stiefel manifolds.pdf)
- Jorge A. Calvo (2001):
  "Geometric knot spaces and polygonal isotopy", J. Knot Theory Ramifications 10 (2001), 245-267.

Key Mathematical Invariants:
1. Stiefel Projection Equivalence:
   Let H = 1^\perp \subset \mathbb{R}^N be the zero-centroid hyperplane (dim = N-1),
   with projector \Pi_H = I_N - \frac{1}{N} 1 1^\top.
   For Gaussian matrix P \in \mathbb{R}^{3 \times N}, polar decomposition:
       \widetilde{P} = P \Pi_H = A Q,
   where A \in GL^+(3, \mathbb{R}) and Q \in St_3(H) is Haar distributed on the Stiefel manifold.
   The stick knot \Gamma(P; C) and \Gamma(Q; C) have identical knot types.

2. Beta Marginal Distance Law:
   For Q \in St_3(H) Haar-distributed and i \ne j, N \ge 5:
       Z_{ij} = \frac{\|Q(e_i - e_j)\|^2}{2} \sim \operatorname{Beta}\left(\frac{3}{2}, \frac{N-4}{2}\right).
   First two moments:
       \mathbb{E}[\|Q(e_i - e_j)\|^2] = \frac{6}{N-1},
       \operatorname{Var}(\|Q(e_i - e_j)\|^2) = \frac{24(N-4)}{(N-1)^2 (N+1)}.
   Deterministic all-pair sum:
       \sum_{i < j} \|Q(e_i - e_j)\|^2 = 3 N.

3. Planar Shadow Crossing Expectation:
   The expected number of crossings in the planar shadow of the random polygon is:
       \mathbb{E}[C_N] = \frac{N(N-3)}{\pi} \arcsin(1/3).
   The number of disjoint edge pairs is \binom{N}{2} - N = \frac{N(N-3)}{2}, each crossing with
   probability p_\times = \frac{2}{\pi} \arcsin(1/3) \approx 0.216347.

4. Calvo 6-Stick Knot Classifier:
   For N = 6, the \binom{6}{4} = 15 tetrahedral orientations determine the knot type.
   Let I(a, b, c; p, q) \in \{-1, 0, 1\} be the oriented piercing number between triangle (a,b,c)
   and directed segment [p, q]. Define:
       \Delta_2 = I(v_1, v_2, v_3; v_4, v_5) + I(v_1, v_2, v_3; v_5, v_6)
       \Delta_4 = I(v_3, v_4, v_5; v_6, v_1) + I(v_3, v_4, v_5; v_1, v_2)
       \Delta_6 = I(v_5, v_6, v_1; v_2, v_3) + I(v_5, v_6, v_1; v_3, v_4)
   Then:
       - (\Delta_2, \Delta_4, \Delta_6) = (+1, +1, +1) \iff Right Trefoil (3_1^+)
       - (\Delta_2, \Delta_4, \Delta_6) = (-1, -1, -1) \iff Left Trefoil (3_1^-)
       - At least one \Delta_i = 0 \iff Unknot (0_1)

5. Sedenion Zero-Divisor 2-Frame Bridge:
   Every sedenion zero-divisor pair u, v \in \mathbb{S} (u \cdot v = 0, \|u\|=\|v\|=1) forms
   an orthonormal 2-frame in V_2(\mathbb{R}^{16}) \subset St_3(\mathbb{R}^{16}).
"""

from dataclasses import dataclass
import math
from typing import Dict, List, Optional, Tuple, Union, Any
import numpy as np


@dataclass(frozen=True)
class BetaDistanceMoments:
    N: int
    alpha: float
    beta: float
    mean_Z: float
    var_Z: float
    mean_sq_dist: float
    var_sq_dist: float
    total_pair_sum: float


def stiefel_dimension(n: int, k: int = 3) -> int:
    """
    Dimension of the Stiefel manifold St_k(R^n) = V_k(R^n):
    dim St_k(R^n) = k*n - k*(k+1)/2.
    """
    if k > n or k < 0 or n < 0:
        raise ValueError(f"Invalid Stiefel indices: k={k}, n={n}")
    return k * n - (k * (k + 1)) // 2


def disjoint_edge_pairs_count(N: int) -> int:
    """
    Number of pairs of non-adjacent edges in an N-gon:
    binom(N, 2) - N = N*(N - 3) / 2.
    """
    if N < 4:
        return 0
    return N * (N - 3) // 2


def single_crossing_probability() -> float:
    """
    Single crossing probability between two non-adjacent edges under isotropic projection:
    p_x = (2 / pi) * arcsin(1/3) ~ 0.216347.
    """
    return (2.0 / math.pi) * math.asin(1.0 / 3.0)


def expected_planar_crossings(N: int) -> float:
    """
    Kolpakov-Rivin exact expected planar crossing count:
    E[C_N] = N*(N-3)/pi * arcsin(1/3).
    """
    return (N * (N - 3) / math.pi) * math.asin(1.0 / 3.0)


def compute_beta_distance_moments(N: int) -> BetaDistanceMoments:
    """
    Computes exact theoretical moments for Z_ij = ||Q(e_i - e_j)||^2 / 2 ~ Beta(3/2, (N-4)/2).
    """
    if N < 4:
        raise ValueError(f"N must be >= 4, got {N}")
    if N == 4:
        return BetaDistanceMoments(
            N=4,
            alpha=1.5,
            beta=0.0,
            mean_Z=1.0,
            var_Z=0.0,
            mean_sq_dist=2.0,
            var_sq_dist=0.0,
            total_pair_sum=12.0,
        )

    alpha = 1.5
    beta = (N - 4) / 2.0
    mean_Z = 3.0 / (N - 1)
    var_Z = (6.0 * (N - 4)) / ((N - 1) ** 2 * (N + 1))
    mean_sq_dist = 6.0 / (N - 1)
    var_sq_dist = 4.0 * var_Z
    total_pair_sum = 3.0 * N

    return BetaDistanceMoments(
        N=N,
        alpha=alpha,
        beta=beta,
        mean_Z=mean_Z,
        var_Z=var_Z,
        mean_sq_dist=mean_sq_dist,
        var_sq_dist=var_sq_dist,
        total_pair_sum=total_pair_sum,
    )


def sample_stiefel_frame(N: int, k: int = 3, rng: Optional[np.random.Generator] = None) -> np.ndarray:
    r"""
    Generates a Haar-distributed k-frame Q in St_k(H) where H = 1^\perp \subset R^N.
    Returns a (k, N) row-orthonormal matrix Q such that:
      Q @ Q.T = I_k
      Q @ 1_N = 0
    """
    if rng is None:
        rng = np.random.default_rng()

    P = rng.normal(loc=0.0, scale=1.0, size=(k, N))
    P_H = P - P.mean(axis=1, keepdims=True)
    Q_cols, _ = np.linalg.qr(P_H.T)
    Q = Q_cols[:, :k].T
    return Q


def polar_decomposition_stiefel(P: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    """
    Given a (3, N) matrix P with centered rows, computes the polar decomposition:
    P = A Q, where A in GL+(3, R) is symmetric positive-definite and Q in St_3(H).
    """
    P_H = P - P.mean(axis=1, keepdims=True)
    M = P_H @ P_H.T
    U, s, Vt = np.linalg.svd(M)
    A = U @ np.diag(np.sqrt(s)) @ Vt
    A_inv = U @ np.diag(1.0 / np.sqrt(s)) @ Vt
    Q = A_inv @ P_H
    return A, Q


def det4(p1: np.ndarray, p2: np.ndarray, p3: np.ndarray, p4: np.ndarray) -> float:
    """
    Computes the 4x4 determinant of homogeneous coordinates [p_i, 1]^T.
    """
    M = np.ones((4, 4), dtype=float)
    M[:3, 0] = p1
    M[:3, 1] = p2
    M[:3, 2] = p3
    M[:3, 3] = p4
    return float(np.linalg.det(M))


def oriented_piercing(
    a: np.ndarray,
    b: np.ndarray,
    c: np.ndarray,
    p: np.ndarray,
    q: np.ndarray,
    eps: float = 1e-9,
) -> int:
    """
    Computes Calvo's oriented intersection / piercing number I(a, b, c; p, q) in {-1, 0, 1}
    between the oriented triangle (a, b, c) and the directed segment [p, q].
    """
    d_p = det4(a, b, c, p)
    d_q = det4(a, b, c, q)
    if d_p * d_q >= -eps**2:
        return 0

    s1 = det4(p, q, a, b)
    s2 = det4(p, q, b, c)
    s3 = det4(p, q, c, a)

    if (s1 > eps and s2 > eps and s3 > eps) or (s1 < -eps and s2 < -eps and s3 < -eps):
        return 1 if s1 > 0 else -1
    return 0


def classify_6_stick_knot(vertices: List[np.ndarray], eps: float = 1e-9) -> Dict[str, Any]:
    r"""
    Classifies a generic 6-stick polygon in R^3 using Calvo's tetrahedral invariants:
        \Delta_2 = I(v_0, v_1, v_2; v_3, v_4) + I(v_0, v_1, v_2; v_4, v_5)
        \Delta_4 = I(v_2, v_3, v_4; v_5, v_0) + I(v_2, v_3, v_4; v_0, v_1)
        \Delta_6 = I(v_4, v_5, v_0; v_1, v_2) + I(v_4, v_5, v_0; v_2, v_3)
    (Using 0-based indexing for vertices v_0 .. v_5).

    Returns:
        knot_type: "3_1^+" (right trefoil), "3_1^-" (left trefoil), or "0_1" (unknot).
    """
    if len(vertices) != 6:
        raise ValueError(f"Expected 6 vertices, got {len(vertices)}")

    v = vertices
    d2 = oriented_piercing(v[0], v[1], v[2], v[3], v[4], eps) + oriented_piercing(v[0], v[1], v[2], v[4], v[5], eps)
    d4 = oriented_piercing(v[2], v[3], v[4], v[5], v[0], eps) + oriented_piercing(v[2], v[3], v[4], v[0], v[1], eps)
    d6 = oriented_piercing(v[4], v[5], v[0], v[1], v[2], eps) + oriented_piercing(v[4], v[5], v[0], v[2], v[3], eps)

    deltas = (d2, d4, d6)
    if deltas == (1, 1, 1):
        knot_type = "3_1^+"  # Right trefoil
    elif deltas == (-1, -1, -1):
        knot_type = "3_1^-"  # Left trefoil
    else:
        knot_type = "0_1"    # Unknot

    return {
        "knot_type": knot_type,
        "deltas": deltas,
        "delta_2": d2,
        "delta_4": d4,
        "delta_6": d6,
    }


def compute_all_tetrahedral_signs(vertices: List[np.ndarray], eps: float = 1e-9) -> Dict[Tuple[int, int, int, int], int]:
    """
    Computes orientation signs for all binom(N, 4) tetrahedra.
    For N = 6, there are exactly 15 tetrahedra.
    """
    N = len(vertices)
    signs = {}
    for i in range(N):
        for j in range(i + 1, N):
            for k in range(j + 1, N):
                for l in range(k + 1, N):
                    val = det4(vertices[i], vertices[j], vertices[k], vertices[l])
                    s = 1 if val > eps else (-1 if val < -eps else 0)
                    signs[(i, j, k, l)] = s
    return signs


def sedenion_zd_frame_to_knot(
    zd_u: np.ndarray,
    zd_v: np.ndarray,
    rng: Optional[np.random.Generator] = None,
) -> np.ndarray:
    """
    Embeds an orthonormal sedenion zero-divisor 2-frame (u, v) in R^16 into a 3-frame Q in St_3(R^16),
    producing a 16-stick knot whose first two coordinates are governed by the zero-divisor annihilation geometry.
    """
    if rng is None:
        rng = np.random.default_rng(42)

    u = zd_u / np.linalg.norm(zd_u)
    v = zd_v / np.linalg.norm(zd_v)
    v = v - np.dot(u, v) * u
    v = v / np.linalg.norm(v)

    w_raw = rng.normal(size=16)
    w = w_raw - np.dot(u, w_raw) * u - np.dot(v, w_raw) * v
    w = w / np.linalg.norm(w)

    Q = np.vstack([u, v, w])
    return Q
