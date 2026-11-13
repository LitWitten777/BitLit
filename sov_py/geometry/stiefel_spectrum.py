"""Representation-Theoretic Laplace-Beltrami Spectrum on V_2(R^7) = G_2 / SU(2).

Formalizes the discrete-continuous geometric bridge between the 168-vertex
sedenion zero-divisor annihilation graph and the continuous 11-dimensional
Stiefel manifold V_2(R^7) endowed with its canonical G_2-invariant metric.

Key Mathematical Invariants:
1. Homogeneous quotient: V_2(R^7) = G_2 / SU(2), dim = 14 - 3 = 11.
2. Highest weights of G_2: lambda = p * omega_1 + q * omega_2 (p, q in N_0).
3. Weyl dimension of G_2:
   dim V_(p, q) = (p+1)(q+1)(p+q+2)(p+2q+3)(p+3q+4)(2p+3q+5) / 120.
4. Multiplicity of SU(2) singlets:
   m(p, q) = dim(V_(p, q)^SU(2)) = (p+1)(q+1)(p+q+2)/2 = dim_SU(3)(W_(p, q)).
5. Laplace-Beltrami Casimir eigenvalue:
   lambda_(p, q) = p^2 + 3pq + 3q^2 + 5p + 9q in N_0.
6. Spectral degeneracy: D(p, q) = m(p, q) * dim V_(p, q).
7. Discrete cubature / spherical 2-design:
   Evaluation of the 21 spherical harmonics of degree (1, 0) across the 168
   discrete zero-divisor 2-frames satisfies M^T M = 24 * I_(21 x 21).
8. Projected adjacency spectrum:
   M_norm^T A M_norm has spectrum {-8^7, 0^14}, directly identifying the
   7-fold negative Perron-Frobenius ground states of the 7 Ramanujan components.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

import numpy as np

from sedenion.fast_algebra import fast_annihilate_cross_octet
from sedenion.stratification import CrossOctetVector, stratify_cross_octet


# Standard oriented Fano plane lines in Im(O) = R^7
FANO_TRIPLES = [
    (1, 2, 3),
    (1, 4, 5),
    (1, 7, 6),
    (2, 4, 6),
    (2, 5, 7),
    (3, 4, 7),
    (3, 6, 5),
]


def octonion_cross_product(u: np.ndarray, v: np.ndarray) -> np.ndarray:
    """Compute the octonionic cross-product u x v on Im(O) = R^7."""
    res = np.zeros(7, dtype=float)
    for i in range(7):
        if u[i] == 0:
            continue
        for j in range(7):
            if i == j or v[j] == 0:
                continue
            u_i_v_j = u[i] * v[j]
            for a, b, c in FANO_TRIPLES:
                p1, p2 = i + 1, j + 1
                if (p1, p2) == (a, b):
                    res[c - 1] += u_i_v_j
                elif (p1, p2) == (b, c):
                    res[a - 1] += u_i_v_j
                elif (p1, p2) == (c, a):
                    res[b - 1] += u_i_v_j
                elif (p1, p2) == (b, a):
                    res[c - 1] -= u_i_v_j
                elif (p1, p2) == (c, b):
                    res[a - 1] -= u_i_v_j
                elif (p1, p2) == (a, c):
                    res[b - 1] -= u_i_v_j
    return res


@dataclass(frozen=True)
class SpectralLevel:
    """Represents a discrete eigenvalue level on V_2(R^7)."""

    p: int
    q: int
    eigenvalue: int
    dimension: int
    singlet_multiplicity: int
    degeneracy: int


class StiefelSpectrumEngine:
    """Analytical representation-theoretic spectrum engine for V_2(R^7) = G_2/SU(2)."""

    DIMENSION = 11

    @staticmethod
    def dim_g2(p: int, q: int) -> int:
        """Weyl dimension formula for irreducible G_2 representation V_(p, q)."""
        if p < 0 or q < 0:
            raise ValueError("Dynkin labels (p, q) must be non-negative integers.")
        num = (
            (p + 1)
            * (q + 1)
            * (p + q + 2)
            * (p + 2 * q + 3)
            * (p + 3 * q + 4)
            * (2 * p + 3 * q + 5)
        )
        return num // 120

    @staticmethod
    def su2_singlet_multiplicity(p: int, q: int) -> int:
        """Multiplicity of SU(2) singlets in V_(p, q), equaling dim_SU(3)(W_(p, q))."""
        if p < 0 or q < 0:
            raise ValueError("Dynkin labels (p, q) must be non-negative integers.")
        return (p + 1) * (q + 1) * (p + q + 2) // 2

    @staticmethod
    def casimir_eigenvalue(p: int, q: int) -> int:
        """Laplace-Beltrami eigenvalue lambda_(p, q) on V_2(R^7)."""
        if p < 0 or q < 0:
            raise ValueError("Dynkin labels (p, q) must be non-negative integers.")
        return p**2 + 3 * p * q + 3 * q**2 + 5 * p + 9 * q

    @classmethod
    def get_level(cls, p: int, q: int) -> SpectralLevel:
        """Construct a complete SpectralLevel for (p, q)."""
        dim = cls.dim_g2(p, q)
        m = cls.su2_singlet_multiplicity(p, q)
        lam = cls.casimir_eigenvalue(p, q)
        return SpectralLevel(
            p=p,
            q=q,
            eigenvalue=lam,
            dimension=dim,
            singlet_multiplicity=m,
            degeneracy=m * dim,
        )

    @classmethod
    def compute_spectrum(cls, max_lambda: int = 2000) -> List[SpectralLevel]:
        """Compute all spectral levels up to a maximum eigenvalue cutoff."""
        levels: List[SpectralLevel] = []
        max_idx = int(math.isqrt(max_lambda)) + 2
        for p in range(max_idx):
            for q in range(max_idx):
                lam = cls.casimir_eigenvalue(p, q)
                if 0 < lam <= max_lambda:
                    levels.append(cls.get_level(p, q))
        levels.sort(key=lambda lvl: (lvl.eigenvalue, lvl.p, lvl.q))
        return levels

    @classmethod
    def heat_kernel_trace(cls, t: float, max_lambda: int = 3000) -> float:
        """Compute the heat kernel trace K(t) = Tr(exp(-t Delta)) = 1 + sum D_k exp(-t lambda_k)."""
        if t <= 0:
            raise ValueError("Diffusion parameter t must be strictly positive.")
        levels = cls.compute_spectrum(max_lambda=max_lambda)
        total = 1.0  # Ground state (0, 0) with lambda = 0, D = 1
        for lvl in levels:
            total += float(lvl.degeneracy) * math.exp(-t * lvl.eigenvalue)
        return total

    @classmethod
    def spectral_zeta(cls, s: float, max_lambda: int = 5000) -> float:
        """Compute the spectral zeta function zeta_(V_2)(s) = sum_(k >= 1) D_k lambda_k^(-s).

        Converges absolutely for Re(s) > dim / 2 = 11 / 2 = 5.5.
        """
        if s <= 5.5:
            raise ValueError("Spectral zeta function on V_2(R^7) only converges for s > 11/2 = 5.5.")
        levels = cls.compute_spectrum(max_lambda=max_lambda)
        total = 0.0
        for lvl in levels:
            total += float(lvl.degeneracy) * (lvl.eigenvalue ** (-s))
        return total

    @classmethod
    def compute_weyl_asymptotic_slope(
        cls, min_lambda: int = 500, max_lambda: int = 4000
    ) -> float:
        """Verify Weyl's asymptotic law N(lambda) ~ c * lambda^(11/2) by log-log slope fitting."""
        levels = cls.compute_spectrum(max_lambda=max_lambda)
        grouped: Dict[int, int] = {}
        for lvl in levels:
            grouped[lvl.eigenvalue] = grouped.get(lvl.eigenvalue, 0) + lvl.degeneracy

        sorted_lams = sorted(grouped.keys())
        lams_fit = []
        ns_fit = []
        cum_n = 0
        for lam in sorted_lams:
            cum_n += grouped[lam]
            if min_lambda <= lam <= max_lambda:
                lams_fit.append(lam)
                ns_fit.append(cum_n)

        if len(lams_fit) < 5:
            raise RuntimeError("Insufficient eigenvalues in range for asymptotic slope fitting.")

        log_lams = np.log(lams_fit)
        log_ns = np.log(ns_fit)
        slope, _ = np.polyfit(log_lams, log_ns, 1)
        return float(slope)

    @classmethod
    def build_harmonic_matrix(cls) -> Tuple[np.ndarray, List[CrossOctetVector]]:
        """Construct the 168 x 21 spherical harmonic evaluation matrix M.

        Evaluates the 21 degree-(1, 0) spherical harmonics:
          F_(i, 1)(P) = u_i
          F_(i, 2)(P) = v_i
          F_(i, 3)(P) = (u x v)_i
        for i in {1..7} across all 168 discrete zero-divisor 2-frames.
        """
        zds, _, _ = stratify_cross_octet()
        m_mat = np.zeros((168, 21), dtype=float)
        for k, zd in enumerate(zds):
            u = np.zeros(7, dtype=float)
            v = np.zeros(7, dtype=float)
            u[zd.i - 1] = float(zd.s1)
            v[zd.j - 1] = float(zd.s2)
            w = octonion_cross_product(u, v)
            m_mat[k, 0:7] = u
            m_mat[k, 7:14] = v
            m_mat[k, 14:21] = w
        return m_mat, zds

    @classmethod
    def verify_cubature_orthogonality(cls) -> Tuple[bool, float]:
        """Verify the spherical 2-design identity M^T M = 24 * I_21."""
        m_mat, _ = cls.build_harmonic_matrix()
        gram = m_mat.T @ m_mat
        expected = 24.0 * np.eye(21)
        max_err = float(np.max(np.abs(gram - expected)))
        is_ortho = bool(np.allclose(gram, expected, atol=1e-10))
        return is_ortho, max_err

    @classmethod
    def project_annihilation_adjacency(cls) -> Tuple[np.ndarray, np.ndarray]:
        """Project the 168x168 annihilation graph adjacency operator onto the 21 harmonics.

        Returns:
            A_proj: 21x21 symmetric matrix M_norm^T A M_norm.
            eigenvalues: sorted eigenvalues of A_proj (identically {-8^7, 0^14}).
        """
        m_mat, zds = cls.build_harmonic_matrix()
        n = len(zds)
        adj = np.zeros((n, n), dtype=float)
        for i in range(n):
            ui, uj, us1, us2 = zds[i].i, zds[i].j, zds[i].s1, zds[i].s2
            for j in range(i + 1, n):
                wi, wj, ws1, ws2 = zds[j].i, zds[j].j, zds[j].s1, zds[j].s2
                if fast_annihilate_cross_octet(ui, uj, us1, us2, wi, wj, ws1, ws2):
                    adj[i, j] = 1.0
                    adj[j, i] = 1.0

        m_norm = m_mat / math.sqrt(24.0)
        a_proj = m_norm.T @ adj @ m_norm
        eigvals = np.linalg.eigvalsh(a_proj)
        return a_proj, eigvals

    @classmethod
    def pell_ray_coincidences(cls, num_terms: int = 6) -> List[Tuple[int, int]]:
        """Generate the infinite family of Pell ray coincidences lambda(p, 0) = lambda(0, q).

        Generated by the recurrence:
            (p, q) -> (2p + 3q + 7, p + 2q + 4)
        starting from (0, 0).
        Classifies all ray coincidences via infinite descent (StiefelSpectrumStrong.lean).
        """
        pairs: List[Tuple[int, int]] = []
        p, q = 0, 0
        for _ in range(num_terms):
            pairs.append((p, q))
            p, q = 2 * p + 3 * q + 7, p + 2 * q + 4
        return pairs

    @classmethod
    def eisenstein_norm_form(cls, p: int, q: int) -> int:
        """Compute the completed-square Eisenstein norm form:

            4 * lambda(p, q) + 28 = (2p + 3q + 5)^2 + 3(q + 1)^2.
        """
        return (2 * p + 3 * q + 5) ** 2 + 3 * (q + 1) ** 2

    @classmethod
    def antidiagonal_singlet_sum(cls, n: int) -> int:
        """Compute the antidiagonal sum of SU(2) singlet multiplicities:

            sum_{a+b=n} m(a, b) = (n + 1)(n + 2)^2(n + 3) / 12.
        """
        return sum(cls.su2_singlet_multiplicity(a, n - a) for a in range(n + 1))

    @classmethod
    def verify_frame_census(cls) -> Dict[str, int]:
        """Verify the discrete 2-frame census and angle trichotomy on the 168 zero divisors."""
        zds, _, _ = stratify_cross_octet()
        planes = set()
        index_pairs = set()
        for zd in zds:
            planes.add((min(zd.i, zd.j), max(zd.i, zd.j)))
            index_pairs.add((zd.i, zd.j))

        c2, c1, c0 = 0, 0, 0
        annihilating = 0
        n = len(zds)
        for i in range(n):
            s1 = {zds[i].i, zds[i].j}
            for j in range(i + 1, n):
                s2 = {zds[j].i, zds[j].j}
                shared = len(s1 & s2)
                if shared == 2:
                    c2 += 1
                elif shared == 1:
                    c1 += 1
                else:
                    c0 += 1

                if fast_annihilate_cross_octet(
                    zds[i].i, zds[i].j, zds[i].s1, zds[i].s2,
                    zds[j].i, zds[j].j, zds[j].s1, zds[j].s2,
                ):
                    annihilating += 1
                    if shared != 0:
                        raise ValueError(f"Annihilating pair ({i}, {j}) shares {shared} axes!")

        return {
            "num_frames": n,
            "num_index_pairs": len(index_pairs),
            "num_coordinate_planes": len(planes),
            "share_two_axes": c2,
            "share_one_axis": c1,
            "orthogonal_pairs": c0,
            "total_pairs": c2 + c1 + c0,
            "annihilating_pairs": annihilating,
            "orthogonal_to_edge_ratio": c0 // annihilating,
        }

    @classmethod
    def verify_annihilation_bipartition(cls) -> Dict[str, any]:
        """Verify the bipartite 2-colouring and 7-fold -8 eigenvector of the annihilation graph.

        The 2-colouring is defined by the cross-product harmonic sign:
            sigma(zd) = s * t * sgn(e_i x e_j) in {+1, -1}.
        """
        zds, _, _ = stratify_cross_octet()
        n = len(zds)

        signs = np.zeros(n, dtype=float)
        for k, zd in enumerate(zds):
            u = np.zeros(7, dtype=float)
            v = np.zeros(7, dtype=float)
            u[zd.i - 1] = float(zd.s1)
            v[zd.j - 1] = float(zd.s2)
            w = octonion_cross_product(u, v)
            idx = np.nonzero(w)[0][0]
            signs[k] = w[idx]

        edges = []
        sectors: Dict[int, List[int]] = {}
        for i in range(n):
            charge = zds[i].i ^ zds[i].j
            sectors.setdefault(charge, []).append(i)
            for j in range(i + 1, n):
                if fast_annihilate_cross_octet(
                    zds[i].i, zds[i].j, zds[i].s1, zds[i].s2,
                    zds[j].i, zds[j].j, zds[j].s1, zds[j].s2,
                ):
                    edges.append((i, j))
                    if signs[i] * signs[j] != -1.0:
                        raise ValueError(f"Edge ({i}, {j}) violates bipartite 2-colouring!")

        # Verify -8 eigenvector in each charge sector
        sector_eigenvalue_verified = True
        for charge, idxs in sectors.items():
            sub_adj = np.zeros((24, 24), dtype=float)
            for a_idx, i in enumerate(idxs):
                for b_idx, j in enumerate(idxs):
                    if fast_annihilate_cross_octet(
                        zds[i].i, zds[i].j, zds[i].s1, zds[i].s2,
                        zds[j].i, zds[j].j, zds[j].s1, zds[j].s2,
                    ):
                        sub_adj[a_idx, b_idx] = 1.0
            sub_signs = signs[idxs]
            res = sub_adj @ sub_signs
            if not np.allclose(res, -8.0 * sub_signs):
                sector_eigenvalue_verified = False
                break

        return {
            "is_bipartite": True,
            "num_edges": len(edges),
            "num_sectors": len(sectors),
            "sector_eigenvalue_verified": sector_eigenvalue_verified,
            "extremal_eigenvalue": -8.0,
            "regularity": 8,
        }

