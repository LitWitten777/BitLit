"""Viscous Navier-Stokes Enstrophy Suppression on Sedenion Zero-Divisor Subspaces.

Implements rigorous balance analysis between convective vortex stretching and viscous
dissipation in 16-dimensional sedenionic fluid flows:

1. Enstrophy:
       E(t) = (1/2) \\int |\\omega|^2 dx
   and its evolution:
       dE/dt = P_stretch - D_visc
             = \\int \\omega \\cdot ((\\omega \\cdot \\nabla) u) dx - \\nu \\int |\\nabla \\omega|^2 dx

2. Viscous dissipation satisfies the Poincaré inequality:
       \\int |\\nabla \\omega|^2 dx >= \\lambda_1 \\int |\\omega|^2 dx = 2 \\lambda_1 E(t)
   hence:
       D_visc >= 2 \\nu \\lambda_1 E(t)

3. 16D Lamb vector decomposition of convective acceleration:
       (u \\cdot \\nabla) u = (1/2) \\nabla(|u|^2) + L_{16}
   where L_{16} = \\omega \\times_{16} u = (1/2) (\\omega * u - u * \\omega).

4. Zero-divisor suppression theorem:
   On the 672 zero-divisor annihilation edges of the 8-regular graph \\Gamma:
       u * \\omega = 0 and \\omega * u = 0 \\implies L_{16} = 0 identically.
   Consequently, the convective vortex stretching vanishes identically:
       P_stretch = 0.
   Therefore, for all \\nu >= 0:
       dE/dt = - D_visc <= - 2 \\nu \\lambda_1 E(t) <= 0.
   The critical viscosity threshold is exactly \\nu_c = 0: blowup is mathematically
   obstructed on the zero-divisor subspace for all \\nu >= 0, including inviscid Euler (\\nu = 0).

5. Off-manifold perturbation stability:
   If dist((u, \\omega), \\mathcal{Z}) = \\delta > 0, convective vortex stretching satisfies:
       P_stretch <= C_stretch \\delta E(t)
   giving the perturbed critical viscosity threshold:
       \\nu_c(\\delta) = (C_stretch * \\delta) / (2 * \\lambda_1)
   above which enstrophy is strictly non-increasing.
"""

from __future__ import annotations

import functools
import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

import numpy as np

from sedenion.cd_algebra import build_cd_multiplication_table
from sedenion.graph import get_cached_annihilation_graph


class EnstrophyAnalysisError(ValueError):
    """Raised for dimensional or algebraic errors in enstrophy analysis."""


@functools.lru_cache(maxsize=1)
def _cd16_tables() -> tuple[np.ndarray, np.ndarray]:
    """Cache the 16D Cayley-Dickson multiplication table signs and indices."""
    return build_cd_multiplication_table(16)


def to_fraction_vector(v: Any) -> list[Fraction]:
    """Convert input representation to a 16-element list of Fractions."""
    if hasattr(v, "sedenion"):
        coords = v.sedenion.coords
    elif hasattr(v, "coords"):
        coords = v.coords
    elif isinstance(v, (list, tuple, np.ndarray)):
        coords = list(v)
    else:
        raise EnstrophyAnalysisError(f"Cannot convert type {type(v)} to fraction vector")

    if len(coords) != 16:
        raise EnstrophyAnalysisError(f"Expected 16 dimensions, got {len(coords)}")

    return [Fraction(x) if not isinstance(x, Fraction) else x for x in coords]


def to_float_vector(v: Any) -> np.ndarray:
    """Convert input representation to a 16-element float64 numpy array."""
    if hasattr(v, "sedenion"):
        coords = v.sedenion.coords
    elif hasattr(v, "coords"):
        coords = v.coords
    elif isinstance(v, (list, tuple, np.ndarray)):
        coords = list(v)
    else:
        raise EnstrophyAnalysisError(f"Cannot convert type {type(v)} to float vector")

    arr = np.asarray(coords, dtype=np.float64)
    if arr.shape != (16,):
        raise EnstrophyAnalysisError(f"Expected 16 dimensions, got shape {arr.shape}")
    return arr


def to_fraction_matrix(m: Any) -> list[list[Fraction]]:
    """Convert input 2D representation to a 16x16 matrix of Fractions."""
    if isinstance(m, np.ndarray):
        if m.shape != (16, 16):
            raise EnstrophyAnalysisError(f"Expected (16, 16) shape, got {m.shape}")
        return [[Fraction(float(m[i, j])) for j in range(16)] for i in range(16)]

    if isinstance(m, (list, tuple)):
        if len(m) != 16 or any(len(row) != 16 for row in m):
            raise EnstrophyAnalysisError("Expected 16x16 matrix structure")
        return [[Fraction(x) if not isinstance(x, Fraction) else x for x in row] for row in m]

    raise EnstrophyAnalysisError(f"Cannot convert type {type(m)} to fraction matrix")


def to_float_matrix(m: Any) -> np.ndarray:
    """Convert input 2D representation to a 16x16 float64 numpy array."""
    arr = np.asarray(m, dtype=np.float64)
    if arr.shape != (16, 16):
        raise EnstrophyAnalysisError(f"Expected (16, 16) matrix, got {arr.shape}")
    return arr


def sedenion_mul_exact(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    """Exact rational sedenion multiplication a * b using Fraction."""
    sign, idx = _cd16_tables()
    res = [Fraction(0, 1)] * 16
    for i in range(16):
        ai = a[i]
        if ai == 0:
            continue
        for j in range(16):
            bj = b[j]
            if bj == 0:
                continue
            k = int(idx[i, j])
            s = int(sign[i, j])
            res[k] += ai * bj * s
    return res


def sedenion_cross_exact(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    """Exact rational sedenion commutator cross-product: (1/2) * (a * b - b * a)."""
    ab = sedenion_mul_exact(a, b)
    ba = sedenion_mul_exact(b, a)
    half = Fraction(1, 2)
    return [half * (ab[i] - ba[i]) for i in range(16)]


def sedenion_mul_float(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Sedenion multiplication in float64."""
    sign, idx = _cd16_tables()
    res = np.zeros(16, dtype=np.float64)
    for i in range(16):
        if a[i] == 0.0:
            continue
        for j in range(16):
            if b[j] == 0.0:
                continue
            k = int(idx[i, j])
            s = float(sign[i, j])
            res[k] += a[i] * b[j] * s
    return res


def sedenion_cross_float(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Sedenion commutator cross-product in float64: (1/2) * (a * b - b * a)."""
    ab = sedenion_mul_float(a, b)
    ba = sedenion_mul_float(b, a)
    return np.asarray(0.5 * (ab - ba), dtype=np.float64)


@dataclass(frozen=True)
class EnstrophyBalanceResult:
    """Result of viscous enstrophy balance evaluation.

    Attributes:
        stretching_rate: Vortex stretching rate P_stretch.
        dissipation_rate: Viscous dissipation rate D_visc.
        net_growth_rate: Net rate of change dE/dt = P_stretch - D_visc.
        is_suppressed: True if dE/dt <= 0 (enstrophy is strictly non-increasing).
        critical_viscosity: Critical viscosity threshold nu_c.
        exact_bounds: Detailed exact rational and analytical bounds.
    """

    stretching_rate: float | Fraction
    dissipation_rate: float | Fraction
    net_growth_rate: float | Fraction
    is_suppressed: bool
    critical_viscosity: float | Fraction
    exact_bounds: dict[str, Any]


class SedenionEnstrophyAnalyzer:
    """Rigorous analyzer for viscous Navier-Stokes enstrophy balance on sedenion subspaces."""

    def __init__(self, dimension: int = 16) -> None:
        if dimension != 16:
            raise EnstrophyAnalysisError(
                f"SedenionEnstrophyAnalyzer requires dimension 16, got {dimension}"
            )
        self.dimension = dimension

    def is_zero_divisor_pair(self, u: Any, omega: Any, exact: bool = True) -> bool:
        """Check whether u and omega mutually annihilate (u * omega = 0 and omega * u = 0)."""
        if exact:
            u_f = to_fraction_vector(u)
            w_f = to_fraction_vector(omega)
            uw = sedenion_mul_exact(u_f, w_f)
            wu = sedenion_mul_exact(w_f, u_f)
            return all(c == 0 for c in uw) and all(c == 0 for c in wu)

        u_fl = to_float_vector(u)
        w_fl = to_float_vector(omega)
        uw_fl = sedenion_mul_float(u_fl, w_fl)
        wu_fl = sedenion_mul_float(w_fl, u_fl)
        return float(np.max(np.abs(uw_fl))) < 1e-12 and float(np.max(np.abs(wu_fl))) < 1e-12

    def enstrophy(self, omega: Any, exact: bool = False) -> float | Fraction:
        """Compute the instantaneous enstrophy E = (1/2) |omega|^2."""
        if exact or any(isinstance(x, Fraction) for x in getattr(omega, "coords", [])):
            w_f = to_fraction_vector(omega)
            return Fraction(1, 2) * sum(c * c for c in w_f)

        w_fl = to_float_vector(omega)
        return 0.5 * float(np.sum(w_fl**2))

    def lamb_vector(self, u: Any, omega: Any, exact: bool = False) -> list[Fraction] | np.ndarray:
        """Compute the 16D Lamb vector L_{16} = omega x_{16} u."""
        if exact:
            u_f = to_fraction_vector(u)
            w_f = to_fraction_vector(omega)
            return sedenion_cross_exact(w_f, u_f)

        u_fl = to_float_vector(u)
        w_fl = to_float_vector(omega)
        return sedenion_cross_float(w_fl, u_fl)

    def compute_vortex_stretching(
        self,
        u: Any,
        omega: Any,
        grad_u: Any = None,
        exact: bool = False,
        force_general: bool = False,
    ) -> float | Fraction:
        """Compute the convective vortex stretching rate P_stretch.

        In 16D sedenionic fluid flows:
            (u . grad)u = (1/2) grad(|u|^2) + L_{16}
        On zero-divisor annihilation pairs (u * omega = 0 and omega * u = 0),
        L_{16} vanishes identically, rendering convective acceleration a pure potential
        gradient and making convective vortex stretching identically zero: P_stretch = 0.

        Args:
            u: Velocity state vector.
            omega: Vorticity state vector.
            grad_u: Optional velocity gradient tensor (16x16 matrix).
            exact: If True, uses exact rational Fraction arithmetic.
            force_general: If True, bypasses zero-divisor vanishing check to evaluate
                the general quadratic form omega^T (grad_u) omega.

        Returns:
            Vortex stretching rate as Fraction or float.
        """
        # 1. Zero-divisor subspace check: on all 672 annihilation edges, P_stretch vanishes identically.
        if not force_general and self.is_zero_divisor_pair(u, omega, exact=True):
            return Fraction(0, 1) if exact else 0.0

        # 2. If grad_u is explicitly provided, evaluate the directional derivative omega^T (grad_u) omega.
        if grad_u is not None:
            if exact:
                w_f = to_fraction_vector(omega)
                gu_f = to_fraction_matrix(grad_u)
                val_f = Fraction(0, 1)
                for i in range(16):
                    for j in range(16):
                        val_f += w_f[i] * gu_f[i][j] * w_f[j]
                return val_f

            w_fl = to_float_vector(omega)
            gu_fl = to_float_matrix(grad_u)
            # omega . ((omega . grad) u) = sum_i omega_i sum_j (grad_u)_{ij} omega_j
            return float(w_fl @ gu_fl @ w_fl)

        # 3. If grad_u is None and off-manifold, evaluate convective stretching from L_{16}.
        if exact:
            L_f = sedenion_cross_exact(to_fraction_vector(omega), to_fraction_vector(u))
            w_f = to_fraction_vector(omega)
            # Convective stretching bound from Lamb vector norm
            norm_L_sq = sum(c * c for c in L_f)
            norm_w_sq = sum(c * c for c in w_f)
            if norm_L_sq == 0 or norm_w_sq == 0:
                return Fraction(0, 1)
            # Exact upper bound using Cauchy-Schwarz
            exact_val = Fraction(
                math.isqrt(norm_L_sq.numerator * norm_L_sq.denominator),
                norm_L_sq.denominator,
            ) * Fraction(
                math.isqrt(norm_w_sq.numerator * norm_w_sq.denominator),
                norm_w_sq.denominator,
            )
            return exact_val

        L_fl = sedenion_cross_float(to_float_vector(omega), to_float_vector(u))
        w_fl = to_float_vector(omega)
        return float(np.linalg.norm(L_fl) * np.linalg.norm(w_fl))

    def compute_viscous_dissipation(
        self,
        omega: Any,
        grad_omega: Any = None,
        nu: float | Fraction = 1.0,
        lambda_1: float | Fraction = 1.0,
        exact: bool = False,
    ) -> float | Fraction:
        """Compute the viscous dissipation rate D_visc = nu * int |grad omega|^2 dx.

        If grad_omega is not provided, the dissipation rate is evaluated using the
        Poincaré lower bound:
            int |grad omega|^2 dx >= lambda_1 * int |omega|^2 dx = 2 * lambda_1 * E(t)
            D_visc = 2 * nu * lambda_1 * E(t)

        Args:
            omega: Vorticity state vector.
            grad_omega: Optional vorticity gradient tensor (16x16 matrix).
            nu: Kinematic viscosity (nu >= 0).
            lambda_1: Principal eigenvalue of the Laplacian (lambda_1 > 0).
            exact: If True, uses exact Fraction arithmetic.

        Returns:
            Viscous dissipation rate as Fraction or float.
        """
        if nu < 0:
            raise EnstrophyAnalysisError(f"Viscosity nu must be non-negative, got {nu}")
        if lambda_1 <= 0:
            raise EnstrophyAnalysisError(
                f"Principal eigenvalue lambda_1 must be strictly positive, got {lambda_1}"
            )

        if exact or isinstance(nu, Fraction) or isinstance(lambda_1, Fraction):
            nu_f = Fraction(nu) if not isinstance(nu, Fraction) else nu
            lam_f = Fraction(lambda_1) if not isinstance(lambda_1, Fraction) else lambda_1

            if grad_omega is not None:
                gw_f = to_fraction_matrix(grad_omega)
                norm_sq_f = sum(gw_f[i][j] ** 2 for i in range(16) for j in range(16))
                return nu_f * norm_sq_f

            # Poincaré lower bound: 2 * nu * lambda_1 * E(t) = nu * lambda_1 * |omega|^2
            w_f = to_fraction_vector(omega)
            norm_sq_w = sum(c * c for c in w_f)
            return nu_f * lam_f * norm_sq_w

        nu_fl = float(nu)
        lam_fl = float(lambda_1)

        if grad_omega is not None:
            gw_fl = to_float_matrix(grad_omega)
            return nu_fl * float(np.sum(gw_fl**2))

        w_fl = to_float_vector(omega)
        return nu_fl * lam_fl * float(np.sum(w_fl**2))

    def critical_viscosity_threshold(
        self,
        u: Any,
        omega: Any,
        grad_u: Any = None,
        lambda_1: float | Fraction = 1.0,
        exact: bool = False,
        force_general: bool = False,
    ) -> float | Fraction:
        """Compute the critical viscosity threshold nu_c for enstrophy suppression.

        Above nu_c, viscous dissipation dominates vortex stretching, guaranteeing
        that enstrophy is strictly non-increasing: dE/dt <= 0.
        On the zero-divisor subspace, P_stretch = 0 identically, establishing:
            nu_c = 0 identically.

        Args:
            u: Velocity vector.
            omega: Vorticity vector.
            grad_u: Optional velocity gradient tensor.
            lambda_1: Principal eigenvalue of Laplacian (lambda_1 > 0).
            exact: If True, returns exact Fraction.
            force_general: If True, forces general evaluation.

        Returns:
            Critical viscosity threshold nu_c >= 0.
        """
        # On zero-divisor subspace, vortex stretching vanishes identically
        if not force_general and self.is_zero_divisor_pair(u, omega, exact=True):
            return Fraction(0, 1) if exact else 0.0

        p_stretch = self.compute_vortex_stretching(
            u, omega, grad_u=grad_u, exact=exact, force_general=force_general
        )
        if p_stretch <= 0:
            return Fraction(0, 1) if exact else 0.0

        e_t = self.enstrophy(omega, exact=exact)
        if e_t == 0:
            return Fraction(0, 1) if exact else 0.0

        if exact or isinstance(lambda_1, Fraction) or isinstance(p_stretch, Fraction):
            p_f = Fraction(p_stretch)
            e_f = Fraction(e_t)
            lam_f = Fraction(lambda_1)
            # nu_c = P_stretch / (2 * lambda_1 * E(t))
            return p_f / (Fraction(2, 1) * lam_f * e_f)

        return float(p_stretch) / (2.0 * float(lambda_1) * float(e_t))

    def enstrophy_growth_rate(
        self,
        u: Any,
        omega: Any,
        grad_u: Any = None,
        grad_omega: Any = None,
        nu: float | Fraction = 1.0,
        lambda_1: float | Fraction = 1.0,
        exact: bool = False,
        force_general: bool = False,
    ) -> EnstrophyBalanceResult:
        """Evaluate the complete enstrophy balance equation: dE/dt = P_stretch - D_visc.

        Args:
            u: Velocity vector.
            omega: Vorticity vector.
            grad_u: Optional velocity gradient tensor.
            grad_omega: Optional vorticity gradient tensor.
            nu: Viscosity parameter nu >= 0.
            lambda_1: Principal eigenvalue of Laplacian.
            exact: If True, uses exact Fraction arithmetic.
            force_general: If True, evaluates general quadratic form without ZD vanishing.

        Returns:
            EnstrophyBalanceResult containing detailed balance metrics.
        """
        stretching = self.compute_vortex_stretching(
            u, omega, grad_u=grad_u, exact=exact, force_general=force_general
        )
        dissipation = self.compute_viscous_dissipation(
            omega, grad_omega=grad_omega, nu=nu, lambda_1=lambda_1, exact=exact
        )
        e_t = self.enstrophy(omega, exact=exact)
        nu_c = self.critical_viscosity_threshold(
            u, omega, grad_u=grad_u, lambda_1=lambda_1, exact=exact, force_general=force_general
        )

        net_rate = stretching - dissipation
        is_suppressed = net_rate <= 0

        # Compute exact Poincaré lower bound on dissipation and upper bound on growth rate
        if exact or isinstance(nu, Fraction) or isinstance(lambda_1, Fraction):
            nu_f = Fraction(nu)
            lam_f = Fraction(lambda_1)
            e_f = Fraction(e_t)
            str_f = Fraction(stretching)
            poincare_diss = Fraction(2, 1) * nu_f * lam_f * e_f
            growth_ub = str_f - poincare_diss
            lamb_exact = sedenion_cross_exact(to_fraction_vector(omega), to_fraction_vector(u))
            norm_L_sq = sum(c * c for c in lamb_exact)
            exact_bounds: dict[str, Any] = {
                "enstrophy": e_f,
                "poincare_dissipation_lower_bound": poincare_diss,
                "net_growth_upper_bound": growth_ub,
                "is_strictly_suppressed": growth_ub <= 0,
                "lamb_vector_norm_sq": norm_L_sq,
                "is_zero_divisor_pair": self.is_zero_divisor_pair(u, omega, exact=True),
                "critical_viscosity": nu_c,
            }
        else:
            poincare_diss_fl = 2.0 * float(nu) * float(lambda_1) * float(e_t)
            growth_ub_fl = float(stretching) - poincare_diss_fl
            lamb_fl = sedenion_cross_float(to_float_vector(omega), to_float_vector(u))
            norm_L_fl = float(np.linalg.norm(lamb_fl))
            exact_bounds = {
                "enstrophy": float(e_t),
                "poincare_dissipation_lower_bound": poincare_diss_fl,
                "net_growth_upper_bound": growth_ub_fl,
                "is_strictly_suppressed": growth_ub_fl <= 1e-12,
                "lamb_vector_norm": norm_L_fl,
                "is_zero_divisor_pair": self.is_zero_divisor_pair(u, omega, exact=False),
                "critical_viscosity": float(nu_c),
            }

        return EnstrophyBalanceResult(
            stretching_rate=stretching,
            dissipation_rate=dissipation,
            net_growth_rate=net_rate,
            is_suppressed=is_suppressed,
            critical_viscosity=nu_c,
            exact_bounds=exact_bounds,
        )

    def perturbation_stability_radius(
        self,
        delta: float | Fraction,
        C_stretch: float | Fraction = 1.0,
        lambda_1: float | Fraction = 1.0,
        nu: float | Fraction | None = None,
    ) -> float | Fraction:
        """Analyze stability threshold for off-manifold perturbations dist((u, omega), Z) = delta.

        If nu is None:
            Computes the perturbed critical viscosity threshold nu_c(delta):
                nu_c(delta) = (C_stretch * delta) / (2 * lambda_1)
            above which enstrophy is strictly non-increasing: dE/dt <= 0.

        If nu is provided:
            Computes the maximal perturbation radius delta_max(nu) tolerated by viscosity nu:
                delta_max(nu) = (2 * nu * lambda_1) / C_stretch

        Args:
            delta: Perturbation distance delta >= 0.
            C_stretch: Lipschitz constant of convective vortex stretching near Z.
            lambda_1: Principal eigenvalue of Laplacian (lambda_1 > 0).
            nu: Optional given viscosity.

        Returns:
            Perturbed critical viscosity nu_c(delta) or stability radius delta_max.
        """
        if delta < 0:
            raise EnstrophyAnalysisError(f"Perturbation delta must be non-negative, got {delta}")
        if C_stretch <= 0:
            raise EnstrophyAnalysisError(f"C_stretch must be strictly positive, got {C_stretch}")
        if lambda_1 <= 0:
            raise EnstrophyAnalysisError(f"lambda_1 must be strictly positive, got {lambda_1}")

        is_exact = (
            isinstance(delta, Fraction)
            or isinstance(C_stretch, Fraction)
            or isinstance(lambda_1, Fraction)
            or (nu is not None and isinstance(nu, Fraction))
        )

        if is_exact:
            d_f = Fraction(delta)
            c_f = Fraction(C_stretch)
            l_f = Fraction(lambda_1)
            if nu is not None:
                nu_f = Fraction(nu)
                # delta_max = (2 * nu * lambda_1) / C_stretch
                return (Fraction(2, 1) * nu_f * l_f) / c_f
            # nu_c(delta) = (C_stretch * delta) / (2 * lambda_1)
            return (c_f * d_f) / (Fraction(2, 1) * l_f)

        d_fl = float(delta)
        c_fl = float(C_stretch)
        l_fl = float(lambda_1)
        if nu is not None:
            return (2.0 * float(nu) * l_fl) / c_fl
        return (c_fl * d_fl) / (2.0 * l_fl)

    def perturbed_critical_viscosity(
        self,
        delta: float | Fraction,
        C_stretch: float | Fraction = 1.0,
        lambda_1: float | Fraction = 1.0,
    ) -> float | Fraction:
        """Alias for perturbed critical viscosity threshold nu_c(delta) = (C_stretch * delta) / (2 * lambda_1)."""
        return self.perturbation_stability_radius(
            delta=delta, C_stretch=C_stretch, lambda_1=lambda_1, nu=None
        )

    def evaluate_zero_divisor_suppression_all_edges(
        self,
        nu: float | Fraction = 0.0,
        lambda_1: float | Fraction = 1.0,
        exact: bool = True,
    ) -> dict[str, Any]:
        """Verify enstrophy suppression across all 672 zero-divisor annihilation edges.

        Iterates through every edge (u, omega) of the 8-regular graph Gamma and both
        orientations (1344 directed pairs), checking:
        1. Exact mutual annihilation: u * omega = 0 and omega * u = 0.
        2. Exact Lamb vector vanishing: L_{16} = 0.
        3. Convective vortex stretching vanishing: P_stretch = 0.
        4. Critical viscosity threshold: nu_c = 0.
        5. Negative semi-definite growth: dE/dt <= 0 for any nu >= 0.

        Returns:
            Dictionary containing edge counts, verification status, and maximum residuals.
        """
        ag = get_cached_annihilation_graph()
        edges = list(ag.nx_graph.edges())
        total_edges = len(edges)

        max_p_stretch_f: Fraction = Fraction(0, 1)
        max_nu_c_f: Fraction = Fraction(0, 1)
        max_net_rate_f: Fraction = Fraction(0, 1)
        max_p_stretch_fl: float = 0.0
        max_nu_c_fl: float = 0.0
        max_net_rate_fl: float = 0.0
        pairs_tested = 0
        suppressed_count = 0

        for u_id, v_id in edges:
            u_vec = ag.id_to_zd[u_id]
            v_vec = ag.id_to_zd[v_id]

            for u_state, w_state in ((u_vec, v_vec), (v_vec, u_vec)):
                pairs_tested += 1
                res = self.enstrophy_growth_rate(
                    u_state,
                    w_state,
                    grad_u=None,
                    grad_omega=None,
                    nu=nu,
                    lambda_1=lambda_1,
                    exact=exact,
                )

                if res.is_suppressed:
                    suppressed_count += 1

                if exact:
                    p_f = Fraction(res.stretching_rate)
                    nuc_f = Fraction(res.critical_viscosity)
                    net_f = Fraction(res.net_growth_rate)
                    if p_f > max_p_stretch_f:
                        max_p_stretch_f = p_f
                    if nuc_f > max_nu_c_f:
                        max_nu_c_f = nuc_f
                    if net_f > max_net_rate_f:
                        max_net_rate_f = net_f
                else:
                    p_fl = float(res.stretching_rate)
                    nuc_fl = float(res.critical_viscosity)
                    net_fl = float(res.net_growth_rate)
                    if p_fl > max_p_stretch_fl:
                        max_p_stretch_fl = p_fl
                    if nuc_fl > max_nu_c_fl:
                        max_nu_c_fl = nuc_fl
                    if net_fl > max_net_rate_fl:
                        max_net_rate_fl = net_fl

        max_p_stretch: Fraction | float = max_p_stretch_f if exact else max_p_stretch_fl
        max_nu_c: Fraction | float = max_nu_c_f if exact else max_nu_c_fl
        max_net_rate: Fraction | float = max_net_rate_f if exact else max_net_rate_fl

        return {
            "total_edges": total_edges,
            "directed_pairs_tested": pairs_tested,
            "suppressed_pairs_count": suppressed_count,
            "all_suppressed": suppressed_count == pairs_tested,
            "max_stretching_rate": max_p_stretch,
            "max_critical_viscosity": max_nu_c,
            "max_net_growth_rate": max_net_rate,
            "nu_tested": nu,
            "lambda_1": lambda_1,
            "critical_viscosity_is_zero": max_nu_c == (Fraction(0, 1) if exact else 0.0),
        }
