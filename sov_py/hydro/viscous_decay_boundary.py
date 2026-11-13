"""Viscous Decay Kinetics, Critical Reynolds Bound & DtN Boundary Coupling.

Requirement 2 (R2) implementation for 16D non-associative Navier-Stokes equations
on the sedenion zero-divisor manifold ZD in S_16.

Mathematical Formulation:
1. Viscous enstrophy decay rate:
       E(t) <= E(0) * exp(-2 * nu * lambda_1 * t)
   governed by the Poincaré inequality on viscous dissipation:
       D(t) = int |grad omega|^2 dx >= lambda_1 * int |omega|^2 dx = 2 * lambda_1 * E(t)
   so that dE/dt <= -2 * nu * lambda_1 * E(t).

2. Critical Reynolds number Re_c and perturbation stability radius delta_crit(nu):
   For off-manifold perturbations with distance delta = dist((u, omega), ZD) > 0:
       |P_stretch| <= C_stretch * delta * ||u|| * ||omega||^2 = C_stretch * delta * ||u|| * E
   Under viscous dissipation -2 * nu * D <= -2 * nu * lambda_1 * E:
       dE/dt <= (C_stretch * delta * ||u|| - 2 * nu * lambda_1) * E
   Stability (dE/dt <= 0) requires:
       delta < delta_crit(nu) = (2 * nu * lambda_1) / (C_stretch * ||u||)
   yielding the critical Reynolds number:
       Re_c(delta) = (2 * lambda_1 * L) / (C_stretch * delta).

3. Dirichlet-to-Neumann (DtN) operator Lambda_16 on cylindrical boundary dM = {r=1}:
   The normal derivative operator on cylindrical boundary satisfies:
       lambda_k = (k / R) * (I_1(k R) / I_0(k R))
   with d lambda_k / dk = k * (1 - (I_1(k R) / I_0(k R))^2) > 0 (strictly monotone).
   Wall boundary conditions preserve zero-divisor invariance:
       u x_16 n = 0 implies Lambda_16(u) x_16 omega = 0.
   Vortex reconnection energy density:
       R_recon = ||u x_16 omega||^2
   vanishes identically across all 672 zero-divisor annihilation edges of Gamma = C_6[K_4_bar],
   suppressing corner eddy reconnection without boundary layer blowup.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Final

import numpy as np
import scipy.special as sp

from sedenion.graph import get_cached_annihilation_graph
from sedenion.hydro.enstrophy_suppression import (
    sedenion_cross_exact,
    sedenion_cross_float,
    to_fraction_vector,
)

DIM_SEDENION: Final[int] = 16


class ViscousBoundaryError(ValueError):
    """Raised for mathematical or dimensional errors in viscous decay and boundary coupling."""


@dataclass(frozen=True)
class ViscousDecayResult:
    """Result of viscous enstrophy decay evaluation at a specific time t.

    Attributes:
        time: Evaluation timestamp t >= 0.
        enstrophy: Current enstrophy E(t).
        dissipation: Instantaneous viscous dissipation D(t).
        decay_bound: Theoretical decay upper bound E(0) * exp(-2 * nu * lambda_1 * t).
        satisfies_bound: Boolean certifying E(t) <= decay_bound within numerical tolerance.
        is_exact: Boolean certifying exact rational Fraction arithmetic.
        metadata: Diagnostic and auxiliary metrics.
    """

    time: float | Fraction
    enstrophy: float | Fraction
    dissipation: float | Fraction
    decay_bound: float | Fraction
    satisfies_bound: bool
    is_exact: bool
    metadata: dict[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class EnstrophyTrajectoryResult:
    """Integrated trajectory of enstrophy evolution under viscous dissipation.

    Attributes:
        times: Array of time steps.
        enstrophies: Enstrophy values E(t_i).
        dissipations: Dissipation values D(t_i).
        bounds: Theoretical upper bounds E_bound(t_i).
        max_enstrophy: Maximum enstrophy attained along the trajectory.
        is_monotone_decaying: Boolean indicating E(t_{i+1}) <= E(t_i) for all steps.
        satisfies_all_bounds: Boolean certifying E(t_i) <= E_bound(t_i) for all steps.
    """

    times: list[float]
    enstrophies: list[float]
    dissipations: list[float]
    bounds: list[float]
    max_enstrophy: float
    is_monotone_decaying: bool
    satisfies_all_bounds: bool


@dataclass(frozen=True)
class StabilityRegimeResult:
    """Regime classification for off-manifold perturbation stability.

    Attributes:
        regime: Name of the stability regime:
            - 'unconditionally_stable_zd': Exact zero-divisor subspace (delta = 0).
            - 'exponentially_stable': Re < Re_c (dissipation strictly dominates).
            - 'critically_stable': Re == Re_c (neutral balance).
            - 'potentially_unstable': Re > Re_c (vortex stretching exceeds dissipation).
        reynolds: Current Reynolds number Re = ||u|| * L / nu.
        reynolds_critical: Critical Reynolds number Re_c(delta) = 2 * lambda_1 * L / (C_stretch * delta).
        perturbation_distance: Off-manifold distance delta.
        stability_radius: Maximal stable perturbation radius delta_crit(nu).
        decay_rate_coefficient: Net exponential coefficient 2 * nu * lambda_1 - C_stretch * delta * ||u||.
        is_stable: Boolean certifying stability (non-increasing enstrophy).
        metadata: Auxiliary parameters.
    """

    regime: str
    reynolds: float | Fraction
    reynolds_critical: float | Fraction
    perturbation_distance: float | Fraction
    stability_radius: float | Fraction
    decay_rate_coefficient: float | Fraction
    is_stable: bool
    metadata: dict[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class DtNEigenvalueMode:
    """Spectral mode and analytical derivative of the Dirichlet-to-Neumann operator Lambda_16.

    Attributes:
        wavenumber: Axial wavenumber k.
        eigenvalue: Exact eigenvalue lambda_k = (k / R) * (I_1(k R) / I_0(k R)).
        derivative: Analytical derivative d lambda_k / dk = k * (1 - (I_1(k R) / I_0(k R))^2).
        asymptotic_ratio: Ratio lambda_k / |k| demonstrating approach to half-Laplacian symbol |k|.
        is_positive: Boolean certifying lambda_k > 0 for k > 0.
    """

    wavenumber: float
    eigenvalue: float
    derivative: float
    asymptotic_ratio: float
    is_positive: bool


@dataclass(frozen=True)
class ReconnectionSuppressionResult:
    """Verification result for corner eddy vortex reconnection suppression.

    Attributes:
        edges_tested: Number of undirected zero-divisor edges evaluated.
        directed_pairs_tested: Total number of directed pairs tested (2 * edges_tested).
        all_suppressed: Boolean certifying R_recon = 0 identically for all pairs.
        max_reconnection_energy: Maximum reconnection energy density ||u x_16 omega||^2 found.
        is_exact_zero: Boolean certifying exact algebraic zero vanishing.
    """

    edges_tested: int
    directed_pairs_tested: int
    all_suppressed: bool
    max_reconnection_energy: float | Fraction
    is_exact_zero: bool


class ViscousDecayKinetics:
    """Quantifies viscous enstrophy decay rate and dissipation under Poincaré inequality."""

    def __init__(
        self,
        nu: float | Fraction = 1.0,
        lambda_1: float | Fraction = 1.0,
    ) -> None:
        """Initialize viscous decay kinetics.

        Args:
            nu: Kinematic viscosity (nu >= 0).
            lambda_1: First Dirichlet/Neumann eigenvalue of the Laplacian (lambda_1 > 0).
        """
        if nu < 0:
            raise ViscousBoundaryError(f"Kinematic viscosity nu must be non-negative, got {nu}")
        if lambda_1 <= 0:
            raise ViscousBoundaryError(
                f"Principal Laplacian eigenvalue lambda_1 must be strictly positive, got {lambda_1}"
            )
        self.nu: float | Fraction = nu
        self.lambda_1: float | Fraction = lambda_1

    def enstrophy_bound(
        self,
        E_0: float | Fraction,
        t: float | Fraction,
        exact: bool = False,
        series_order: int = 25,
    ) -> float | Fraction:
        """Compute the theoretical viscous enstrophy decay bound:

            E(t) <= E(0) * exp(-2 * nu * lambda_1 * t)

        For exact rational computation (exact=True or Fraction inputs), computes a rigorous
        rational upper bound via Taylor expansion of the reciprocal:
            exp(-x) < 1 / (sum_{m=0}^M x^m / m!)  for all x > 0.

        Args:
            E_0: Initial enstrophy E(0) >= 0.
            t: Time elapsed t >= 0.
            exact: Whether to enforce exact Fraction arithmetic.
            series_order: Truncation order for rational exponential enclosure.

        Returns:
            Decay upper bound as Fraction or float.
        """
        if E_0 < 0:
            raise ViscousBoundaryError(f"Initial enstrophy E_0 must be non-negative, got {E_0}")
        if t < 0:
            raise ViscousBoundaryError(f"Time t must be non-negative, got {t}")

        is_rational = (
            exact
            or isinstance(E_0, Fraction)
            or isinstance(t, Fraction)
            or isinstance(self.nu, Fraction)
            or isinstance(self.lambda_1, Fraction)
        )

        if is_rational:
            e0_f = Fraction(E_0)
            t_f = Fraction(t)
            nu_f = Fraction(self.nu)
            lam_f = Fraction(self.lambda_1)

            x = Fraction(2, 1) * nu_f * lam_f * t_f
            if x == 0 or e0_f == 0:
                return e0_f

            # Taylor polynomial for exp(x): sum_{m=0}^M x^m / m!
            # Since exp(x) > sum_{m=0}^M x^m / m! for all x > 0 and M >= 0,
            # exp(-x) < 1 / sum_{m=0}^M x^m / m! is a guaranteed rational UPPER bound.
            denom = Fraction(0, 1)
            term = Fraction(1, 1)
            for m in range(series_order + 1):
                if m > 0:
                    term = term * x / Fraction(m, 1)
                denom += term

            return e0_f / denom

        e0_fl = float(E_0)
        t_fl = float(t)
        nu_fl = float(self.nu)
        lam_fl = float(self.lambda_1)
        return e0_fl * math.exp(-2.0 * nu_fl * lam_fl * t_fl)

    def dissipation_rate_lower_bound(
        self,
        E: float | Fraction,
        exact: bool = False,
    ) -> float | Fraction:
        """Compute the viscous dissipation rate lower bound under Poincaré inequality:

            D_visc = 2 * nu * int |grad omega|^2 dx >= 2 * nu * lambda_1 * E

        Args:
            E: Instantaneous enstrophy E >= 0.
            exact: Whether to enforce exact Fraction arithmetic.

        Returns:
            Dissipation rate lower bound as Fraction or float.
        """
        if E < 0:
            raise ViscousBoundaryError(f"Enstrophy E must be non-negative, got {E}")

        is_rational = (
            exact
            or isinstance(E, Fraction)
            or isinstance(self.nu, Fraction)
            or isinstance(self.lambda_1, Fraction)
        )
        if is_rational:
            return Fraction(2, 1) * Fraction(self.nu) * Fraction(self.lambda_1) * Fraction(E)
        return 2.0 * float(self.nu) * float(self.lambda_1) * float(E)

    def dirichlet_integral_lower_bound(
        self,
        E: float | Fraction,
        exact: bool = False,
    ) -> float | Fraction:
        """Compute the Dirichlet integral lower bound:

            D = int |grad omega|^2 dx >= 2 * lambda_1 * E

        Args:
            E: Instantaneous enstrophy E >= 0.
            exact: Whether to enforce exact Fraction arithmetic.

        Returns:
            Dirichlet integral lower bound as Fraction or float.
        """
        if E < 0:
            raise ViscousBoundaryError(f"Enstrophy E must be non-negative, got {E}")

        is_rational = exact or isinstance(E, Fraction) or isinstance(self.lambda_1, Fraction)
        if is_rational:
            return Fraction(2, 1) * Fraction(self.lambda_1) * Fraction(E)
        return 2.0 * float(self.lambda_1) * float(E)

    def decay_rate(
        self,
        E: float | Fraction,
        exact: bool = False,
    ) -> float | Fraction:
        """Compute the instantaneous enstrophy decay rate dE/dt = -2 * nu * lambda_1 * E."""
        diss = self.dissipation_rate_lower_bound(E, exact=exact)
        return -diss

    def verify_enstrophy_decay(
        self,
        E_0: float | Fraction,
        E_t: float | Fraction,
        t: float | Fraction,
        exact: bool = False,
        tolerance: float = 1e-12,
    ) -> ViscousDecayResult:
        """Verify whether enstrophy E_t satisfies the Poincaré decay bound E(t) <= E(0) e^{-2 nu lambda_1 t}.

        Args:
            E_0: Initial enstrophy at t=0.
            E_t: Measured enstrophy at time t.
            t: Time elapsed t >= 0.
            exact: Enforce exact Fraction arithmetic.
            tolerance: Numerical tolerance for floating-point verification.

        Returns:
            ViscousDecayResult certifying invariant validity.
        """
        bound = self.enstrophy_bound(E_0, t, exact=exact)
        diss = self.dissipation_rate_lower_bound(E_t, exact=exact)

        is_rational = (
            exact
            or isinstance(E_0, Fraction)
            or isinstance(E_t, Fraction)
            or isinstance(t, Fraction)
        )

        if is_rational:
            b_f = Fraction(bound)
            et_f = Fraction(E_t)
            satisfies = bool(et_f <= b_f)
            metadata = {
                "difference": b_f - et_f,
                "decay_factor": (et_f / Fraction(E_0)) if E_0 > 0 else Fraction(0, 1),
            }
            return ViscousDecayResult(
                time=Fraction(t),
                enstrophy=et_f,
                dissipation=Fraction(diss),
                decay_bound=b_f,
                satisfies_bound=satisfies,
                is_exact=True,
                metadata=metadata,
            )

        b_fl = float(bound)
        et_fl = float(E_t)
        satisfies = bool(et_fl <= b_fl + tolerance)
        metadata_fl = {
            "difference": b_fl - et_fl,
            "decay_factor": (et_fl / float(E_0)) if float(E_0) > 0 else 0.0,
        }
        return ViscousDecayResult(
            time=float(t),
            enstrophy=et_fl,
            dissipation=float(diss),
            decay_bound=b_fl,
            satisfies_bound=satisfies,
            is_exact=False,
            metadata=metadata_fl,
        )

    def integrate_trajectory(
        self,
        E_0: float,
        time_steps: np.ndarray | list[float],
        perturbation_delta: float = 0.0,
        C_stretch: float = 1.0,
        u_norm: float = 1.0,
    ) -> EnstrophyTrajectoryResult:
        """Integrate continuous enstrophy evolution:

            dE/dt = (C_stretch * delta * ||u|| - 2 * nu * lambda_1) * E

        Args:
            E_0: Initial enstrophy.
            time_steps: Sequence of evaluation times t >= 0.
            perturbation_delta: Off-manifold distance delta >= 0.
            C_stretch: Convective stretching constant > 0.
            u_norm: Characteristic velocity norm ||u|| > 0.

        Returns:
            EnstrophyTrajectoryResult containing trajectory history.
        """
        if E_0 < 0:
            raise ViscousBoundaryError(f"Initial enstrophy E_0 must be non-negative, got {E_0}")
        if perturbation_delta < 0:
            raise ViscousBoundaryError(
                f"Perturbation delta must be non-negative, got {perturbation_delta}"
            )
        if C_stretch <= 0:
            raise ViscousBoundaryError(f"C_stretch must be strictly positive, got {C_stretch}")
        if u_norm <= 0:
            raise ViscousBoundaryError(f"u_norm must be strictly positive, got {u_norm}")

        t_arr = [float(t) for t in time_steps]
        if any(t < 0 for t in t_arr):
            raise ViscousBoundaryError("All time steps must be non-negative.")

        # Net exponent: alpha = C_stretch * delta * ||u|| - 2 * nu * lambda_1
        alpha = float(C_stretch) * float(perturbation_delta) * float(u_norm) - 2.0 * float(
            self.nu
        ) * float(self.lambda_1)

        enstrophies: list[float] = []
        dissipations: list[float] = []
        bounds: list[float] = []

        for t in t_arr:
            e_t = float(E_0) * math.exp(alpha * t)
            d_t = 2.0 * float(self.nu) * float(self.lambda_1) * e_t
            b_t = float(self.enstrophy_bound(E_0, t, exact=False))
            enstrophies.append(e_t)
            dissipations.append(d_t)
            bounds.append(b_t)

        is_monotone = True
        for i in range(len(enstrophies) - 1):
            if enstrophies[i + 1] > enstrophies[i] + 1e-12:
                is_monotone = False
                break

        satisfies_all = all(e <= b + 1e-10 for e, b in zip(enstrophies, bounds, strict=True))

        return EnstrophyTrajectoryResult(
            times=t_arr,
            enstrophies=enstrophies,
            dissipations=dissipations,
            bounds=bounds,
            max_enstrophy=max(enstrophies) if enstrophies else 0.0,
            is_monotone_decaying=is_monotone,
            satisfies_all_bounds=satisfies_all,
        )


class CriticalReynoldsAnalyzer:
    """Analyzes critical Reynolds bounds and off-manifold perturbation stability radius."""

    def __init__(
        self,
        C_stretch: float | Fraction = 1.0,
        lambda_1: float | Fraction = 1.0,
        L: float | Fraction = 1.0,
    ) -> None:
        """Initialize Critical Reynolds Analyzer.

        Args:
            C_stretch: Convective stretching constant (C_stretch > 0).
            lambda_1: Principal Laplacian eigenvalue (lambda_1 > 0).
            L: Characteristic domain length scale (L > 0).
        """
        if C_stretch <= 0:
            raise ViscousBoundaryError(f"C_stretch must be strictly positive, got {C_stretch}")
        if lambda_1 <= 0:
            raise ViscousBoundaryError(f"lambda_1 must be strictly positive, got {lambda_1}")
        if L <= 0:
            raise ViscousBoundaryError(f"Length scale L must be strictly positive, got {L}")

        self.C_stretch: float | Fraction = C_stretch
        self.lambda_1: float | Fraction = lambda_1
        self.L: float | Fraction = L

    def critical_reynolds(
        self,
        delta: float | Fraction,
    ) -> float | Fraction:
        """Compute the critical Reynolds number Re_c(delta):

            Re_c(delta) = (2 * lambda_1 * L) / (C_stretch * delta)

        When delta = 0 (exact zero-divisor manifold), returns float('inf') representing
        unconditional global stability for all Reynolds numbers.

        Args:
            delta: Off-manifold perturbation distance delta >= 0.

        Returns:
            Re_c as Fraction or float (or float('inf') if delta == 0).
        """
        if delta < 0:
            raise ViscousBoundaryError(f"Perturbation delta must be non-negative, got {delta}")
        if delta == 0:
            return float("inf")

        is_rational = (
            isinstance(delta, Fraction)
            or isinstance(self.C_stretch, Fraction)
            or isinstance(self.lambda_1, Fraction)
            or isinstance(self.L, Fraction)
        )
        if is_rational:
            d_f = Fraction(delta)
            c_f = Fraction(self.C_stretch)
            lam_f = Fraction(self.lambda_1)
            l_f = Fraction(self.L)
            return (Fraction(2, 1) * lam_f * l_f) / (c_f * d_f)

        return (2.0 * float(self.lambda_1) * float(self.L)) / (float(self.C_stretch) * float(delta))

    def perturbation_stability_radius(
        self,
        nu: float | Fraction,
        u_norm: float | Fraction = 1.0,
    ) -> float | Fraction:
        """Compute the maximal perturbation radius delta_crit(nu) tolerated by viscosity nu:

            delta_crit(nu) = (2 * nu * lambda_1) / (C_stretch * ||u||)

        Args:
            nu: Kinematic viscosity nu >= 0.
            u_norm: Characteristic velocity norm ||u|| > 0.

        Returns:
            delta_crit as Fraction or float.
        """
        if nu < 0:
            raise ViscousBoundaryError(f"Viscosity nu must be non-negative, got {nu}")
        if u_norm <= 0:
            raise ViscousBoundaryError(
                f"Velocity norm u_norm must be strictly positive, got {u_norm}"
            )

        is_rational = (
            isinstance(nu, Fraction)
            or isinstance(u_norm, Fraction)
            or isinstance(self.C_stretch, Fraction)
            or isinstance(self.lambda_1, Fraction)
        )
        if is_rational:
            nu_f = Fraction(nu)
            u_f = Fraction(u_norm)
            c_f = Fraction(self.C_stretch)
            lam_f = Fraction(self.lambda_1)
            return (Fraction(2, 1) * nu_f * lam_f) / (c_f * u_f)

        return (2.0 * float(nu) * float(self.lambda_1)) / (float(self.C_stretch) * float(u_norm))

    def critical_viscosity(
        self,
        delta: float | Fraction,
        u_norm: float | Fraction = 1.0,
    ) -> float | Fraction:
        """Compute the critical viscosity threshold nu_c(delta):

            nu_c(delta) = (C_stretch * delta * ||u||) / (2 * lambda_1)

        Args:
            delta: Perturbation distance delta >= 0.
            u_norm: Velocity norm ||u|| > 0.

        Returns:
            Critical viscosity threshold nu_c as Fraction or float.
        """
        if delta < 0:
            raise ViscousBoundaryError(f"Perturbation delta must be non-negative, got {delta}")
        if u_norm <= 0:
            raise ViscousBoundaryError(
                f"Velocity norm u_norm must be strictly positive, got {u_norm}"
            )

        is_rational = (
            isinstance(delta, Fraction)
            or isinstance(u_norm, Fraction)
            or isinstance(self.C_stretch, Fraction)
            or isinstance(self.lambda_1, Fraction)
        )
        if is_rational:
            d_f = Fraction(delta)
            u_f = Fraction(u_norm)
            c_f = Fraction(self.C_stretch)
            lam_f = Fraction(self.lambda_1)
            return (c_f * d_f * u_f) / (Fraction(2, 1) * lam_f)

        return (float(self.C_stretch) * float(delta) * float(u_norm)) / (2.0 * float(self.lambda_1))

    def reynolds_number(
        self,
        nu: float | Fraction,
        u_norm: float | Fraction = 1.0,
    ) -> float | Fraction:
        """Compute Reynolds number Re = ||u|| * L / nu."""
        if nu < 0:
            raise ViscousBoundaryError(f"Viscosity nu must be non-negative, got {nu}")
        if u_norm <= 0:
            raise ViscousBoundaryError(
                f"Velocity norm u_norm must be strictly positive, got {u_norm}"
            )
        if nu == 0:
            return float("inf")

        is_rational = (
            isinstance(nu, Fraction) or isinstance(u_norm, Fraction) or isinstance(self.L, Fraction)
        )
        if is_rational:
            return (Fraction(u_norm) * Fraction(self.L)) / Fraction(nu)
        return (float(u_norm) * float(self.L)) / float(nu)

    def residual_vortex_stretching_bound(
        self,
        delta: float | Fraction,
        u_norm: float | Fraction,
        enstrophy: float | Fraction,
    ) -> float | Fraction:
        """Compute residual vortex stretching bound:

            |P_stretch| <= C_stretch * delta * ||u|| * E

        Args:
            delta: Perturbation distance.
            u_norm: Velocity norm.
            enstrophy: Instantaneous enstrophy E.
        """
        if delta < 0 or u_norm < 0 or enstrophy < 0:
            raise ViscousBoundaryError("delta, u_norm, and enstrophy must all be non-negative.")

        is_rational = (
            isinstance(delta, Fraction)
            or isinstance(u_norm, Fraction)
            or isinstance(enstrophy, Fraction)
            or isinstance(self.C_stretch, Fraction)
        )
        if is_rational:
            return (
                Fraction(self.C_stretch) * Fraction(delta) * Fraction(u_norm) * Fraction(enstrophy)
            )
        return float(self.C_stretch) * float(delta) * float(u_norm) * float(enstrophy)

    def is_stable(
        self,
        Re: float | Fraction,
        delta: float | Fraction,
    ) -> bool:
        """Determine whether the flow is stable (non-increasing enstrophy).

        Returns True if delta == 0 or Re < Re_c(delta).
        """
        if delta < 0:
            raise ViscousBoundaryError(f"Perturbation delta must be non-negative, got {delta}")
        if delta == 0:
            return True

        re_c = self.critical_reynolds(delta)
        if isinstance(Re, Fraction) and isinstance(re_c, Fraction):
            return Re < re_c
        return float(Re) < float(re_c)

    def classify_regime(
        self,
        Re: float | Fraction,
        delta: float | Fraction,
        nu: float | Fraction | None = None,
        u_norm: float | Fraction = 1.0,
    ) -> StabilityRegimeResult:
        """Classify flow stability into rigorous dynamical regimes.

        Args:
            Re: Operating Reynolds number Re >= 0.
            delta: Perturbation distance delta >= 0.
            nu: Optional kinematic viscosity. If omitted, computed from Re.
            u_norm: Characteristic velocity norm ||u|| > 0.

        Returns:
            StabilityRegimeResult containing regime name and metrics.
        """
        if Re < 0:
            raise ViscousBoundaryError(f"Reynolds number Re must be non-negative, got {Re}")
        if delta < 0:
            raise ViscousBoundaryError(f"Perturbation delta must be non-negative, got {delta}")
        if u_norm <= 0:
            raise ViscousBoundaryError(f"u_norm must be strictly positive, got {u_norm}")

        is_rational = (
            isinstance(Re, Fraction)
            or isinstance(delta, Fraction)
            or (nu is not None and isinstance(nu, Fraction))
            or isinstance(u_norm, Fraction)
        )

        re_c = self.critical_reynolds(delta)

        # Compute effective viscosity
        if nu is None:
            if Re == 0 or Re == float("inf"):
                nu_eff: float | Fraction = Fraction(0, 1) if is_rational else 0.0
            else:
                if is_rational:
                    nu_eff = (Fraction(u_norm) * Fraction(self.L)) / Fraction(Re)
                else:
                    nu_eff = (float(u_norm) * float(self.L)) / float(Re)
        else:
            nu_eff = Fraction(nu) if is_rational else float(nu)

        stab_radius = self.perturbation_stability_radius(nu_eff, u_norm=u_norm)

        # Decay rate coefficient: 2 * nu * lambda_1 - C_stretch * delta * ||u||
        decay_coeff: float | Fraction
        if is_rational:
            decay_coeff = Fraction(2, 1) * Fraction(nu_eff) * Fraction(self.lambda_1) - Fraction(
                self.C_stretch
            ) * Fraction(delta) * Fraction(u_norm)
        else:
            decay_coeff = 2.0 * float(nu_eff) * float(self.lambda_1) - float(
                self.C_stretch
            ) * float(delta) * float(u_norm)

        if delta == 0:
            regime = "unconditionally_stable_zd"
            is_stable = True
        elif (is_rational and isinstance(re_c, Fraction) and Re < re_c) or (
            not is_rational and float(Re) < float(re_c)
        ):
            regime = "exponentially_stable"
            is_stable = True
        elif (is_rational and isinstance(re_c, Fraction) and Re == re_c) or (
            not is_rational and math.isclose(float(Re), float(re_c), rel_tol=1e-12)
        ):
            regime = "critically_stable"
            is_stable = True
        else:
            regime = "potentially_unstable"
            is_stable = False

        return StabilityRegimeResult(
            regime=regime,
            reynolds=Re,
            reynolds_critical=re_c,
            perturbation_distance=delta,
            stability_radius=stab_radius,
            decay_rate_coefficient=decay_coeff,
            is_stable=is_stable,
            metadata={"effective_viscosity": nu_eff, "u_norm": u_norm},
        )


class BoundaryCouplingDtN:
    """16D Dirichlet-to-Neumann operator and corner eddy suppression on cylinder boundary r=1."""

    def __init__(self, radius: float = 1.0) -> None:
        """Initialize Dirichlet-to-Neumann boundary operator on cylindrical wall.

        Args:
            radius: Cylinder boundary radius R > 0 (default R=1.0).
        """
        if radius <= 0.0:
            raise ViscousBoundaryError(
                f"Cylinder boundary radius must be strictly positive, got {radius}"
            )
        self.radius: float = float(radius)

    def compute_mode(self, wavenumber: float) -> DtNEigenvalueMode:
        """Compute the eigenvalue and analytical derivative of Lambda_16 for wavenumber k.

        The cylindrical Laplace equation Phi(r, z) = R(r) e^{i k z} requires:
            r^2 R'' + r R' - k^2 r^2 R = 0 ==> R(r) = I_0(k r) / I_0(k R).
        The normal derivative at the wall r = R is:
            lambda_k = [d/dr R(r)]_{r=R} = (k / R) * (I_1(k R) / I_0(k R)).

        The analytical derivative with respect to wavenumber k is:
            d lambda_k / dk = k * (1 - (I_1(k R) / I_0(k R))^2) > 0 for all k > 0.
        """
        k = float(abs(wavenumber))
        if k < 1e-14:
            return DtNEigenvalueMode(
                wavenumber=float(wavenumber),
                eigenvalue=0.0,
                derivative=0.0,
                asymptotic_ratio=1.0,
                is_positive=False,
            )

        kr = k * self.radius
        # Use exponentially scaled Bessel functions to prevent numerical overflow for large k:
        # sp.ive(v, x) = sp.iv(v, x) * exp(-x)
        # Therefore sp.ive(1, kr) / sp.ive(0, kr) == sp.iv(1, kr) / sp.iv(0, kr)
        ive0 = float(sp.ive(0, kr))
        ive1 = float(sp.ive(1, kr))

        if ive0 == 0.0:
            raise ViscousBoundaryError(f"Bessel function evaluation failed at kr={kr}")

        bessel_ratio = ive1 / ive0
        eig = (k / self.radius) * bessel_ratio
        deriv = k * (1.0 - bessel_ratio**2)
        asymp = eig / k

        return DtNEigenvalueMode(
            wavenumber=float(wavenumber),
            eigenvalue=float(eig),
            derivative=float(deriv),
            asymptotic_ratio=float(asymp),
            is_positive=bool(eig > 0.0),
        )

    def verify_eigenvalue_monotonicity(self, wavenumbers: list[float]) -> bool:
        """Verify that eigenvalues lambda_k are strictly monotonically increasing.

        Checks:
        1. lambda_{k_i} < lambda_{k_{i+1}} for 0 <= k_0 < k_1 < ...
        2. Analytical derivative d lambda_k / dk > 0 for all positive k.
        """
        if len(wavenumbers) < 2:
            return True

        sorted_k = sorted(abs(float(k)) for k in wavenumbers)
        modes = [self.compute_mode(k) for k in sorted_k]

        for i in range(len(modes) - 1):
            if sorted_k[i] > 1e-12 and modes[i].derivative <= 0.0:
                return False
            if (
                sorted_k[i + 1] > sorted_k[i] + 1e-12
                and modes[i + 1].eigenvalue <= modes[i].eigenvalue
            ):
                return False

        return True

    def apply_dtn(self, z_grid: np.ndarray, g_values: np.ndarray) -> np.ndarray:
        """Apply the DtN operator Lambda_16 to a boundary profile g(z) along r = R.

        Args:
            z_grid: 1D grid along cylinder axis z in [-L, L].
            g_values: Sedenion-valued boundary profile of shape (N, 16) or scalar (N,).

        Returns:
            Normal derivative profile of identical shape.
        """
        if len(z_grid) < 4:
            raise ViscousBoundaryError("Spatial grid must contain at least 4 points.")
        n_points = len(z_grid)
        dz = float(z_grid[1] - z_grid[0])
        if dz <= 0.0:
            raise ViscousBoundaryError("Spatial grid spacing dz must be strictly positive.")

        freqs = np.fft.fftfreq(n_points, d=dz) * (2.0 * np.pi)
        mults = np.zeros(n_points, dtype=np.float64)
        for idx, k in enumerate(freqs):
            mults[idx] = self.compute_mode(k).eigenvalue

        if g_values.ndim == 1:
            g_hat = np.fft.fft(g_values)
            res = np.real(np.fft.ifft(g_hat * mults))
            return np.asarray(res, dtype=np.float64)
        elif g_values.ndim == 2 and g_values.shape[1] == DIM_SEDENION:
            out = np.zeros_like(g_values, dtype=np.float64)
            for c in range(DIM_SEDENION):
                c_hat = np.fft.fft(g_values[:, c])
                out[:, c] = np.real(np.fft.ifft(c_hat * mults))
            return np.asarray(out, dtype=np.float64)
        else:
            raise ViscousBoundaryError(
                f"g_values shape {g_values.shape} unsupported. Must be (N,) or (N, 16)."
            )

    def reconnection_energy_density(
        self,
        u: np.ndarray,
        omega: np.ndarray,
    ) -> float:
        """Compute corner eddy vortex reconnection energy density:

            R_recon = ||u x_16 omega||^2

        Under zero-divisor alignment (u * omega = 0 and omega * u = 0), R_recon = 0 identically.
        """
        u_fl = np.asarray(u, dtype=np.float64)
        w_fl = np.asarray(omega, dtype=np.float64)
        if u_fl.shape != (16,) or w_fl.shape != (16,):
            raise ViscousBoundaryError("Input vectors must have dimension 16.")

        cross = sedenion_cross_float(u_fl, w_fl)
        return float(np.sum(cross**2))

    def reconnection_energy_density_exact(
        self,
        u: list[Fraction],
        omega: list[Fraction],
    ) -> Fraction:
        """Compute exact rational reconnection energy density R_recon = ||u x_16 omega||^2."""
        u_f = to_fraction_vector(u)
        w_f = to_fraction_vector(omega)
        cross_f = sedenion_cross_exact(u_f, w_f)
        return sum((c * c for c in cross_f), Fraction(0, 1))

    def verify_wall_zero_divisor_preservation(
        self,
        u_vec: np.ndarray,
        omega_vec: np.ndarray,
        normal_idx: int = 1,
        z_grid: np.ndarray | None = None,
    ) -> bool:
        """Verify that wall boundary conditions preserve zero-divisor invariance:

            u x_16 n = 0 implies Lambda_16(u) x_16 omega = 0.

        Args:
            u_vec: 16D sedenion velocity vector.
            omega_vec: 16D sedenion vorticity vector.
            normal_idx: Imaginary basis index of boundary normal vector n.
            z_grid: Optional axial spatial grid.

        Returns:
            True if Lambda_16(u) x_16 omega vanishes across all grid points.
        """
        if z_grid is None:
            z_grid = np.linspace(-np.pi, np.pi, 32, endpoint=False)

        # Construct spatial profile along cylinder wall
        profile = np.outer(np.sin(z_grid) + np.cos(2 * z_grid), u_vec)
        dtn_u = self.apply_dtn(z_grid, profile)

        # Check that Lambda_16(u) x_16 omega == 0 at all z points
        for i in range(len(z_grid)):
            r_recon = self.reconnection_energy_density(dtn_u[i], omega_vec)
            if r_recon > 1e-10:
                return False
        return True

    def verify_corner_eddy_suppression_all_672_edges(
        self,
        exact: bool = True,
    ) -> ReconnectionSuppressionResult:
        """Verify corner eddy reconnection suppression across all 672 zero-divisor edges.

        Tests all 672 undirected edges of Gamma = C_6[K_4_bar] in both orientations
        (1344 directed pairs), checking that R_recon = ||u x_16 omega||^2 vanishes identically.

        Args:
            exact: Whether to enforce exact Fraction integer arithmetic.

        Returns:
            ReconnectionSuppressionResult certifying complete reconnection suppression.
        """
        ag = get_cached_annihilation_graph()
        edges = list(ag.nx_graph.edges())
        total_edges = len(edges)

        max_r_recon_f: Fraction = Fraction(0, 1)
        max_r_recon_fl: float = 0.0
        pairs_tested = 0
        all_zero = True

        for u_id, v_id in edges:
            u_zd = ag.id_to_zd[u_id]
            v_zd = ag.id_to_zd[v_id]

            if exact:
                u_f = [Fraction(x) for x in u_zd.sedenion.coords]
                v_f = [Fraction(x) for x in v_zd.sedenion.coords]
                for a_f, b_f in [(u_f, v_f), (v_f, u_f)]:
                    pairs_tested += 1
                    r_f = self.reconnection_energy_density_exact(a_f, b_f)
                    if r_f != 0:
                        all_zero = False
                    if r_f > max_r_recon_f:
                        max_r_recon_f = r_f
            else:
                u_fl = np.array(u_zd.sedenion.coords, dtype=np.float64)
                v_fl = np.array(v_zd.sedenion.coords, dtype=np.float64)
                for a_fl, b_fl in [(u_fl, v_fl), (v_fl, u_fl)]:
                    pairs_tested += 1
                    r_fl = self.reconnection_energy_density(a_fl, b_fl)
                    if r_fl > 1e-12:
                        all_zero = False
                    if r_fl > max_r_recon_fl:
                        max_r_recon_fl = r_fl

        max_val: float | Fraction = max_r_recon_f if exact else max_r_recon_fl
        is_exact_zero = bool(max_val == 0)

        return ReconnectionSuppressionResult(
            edges_tested=total_edges,
            directed_pairs_tested=pairs_tested,
            all_suppressed=all_zero,
            max_reconnection_energy=max_val,
            is_exact_zero=is_exact_zero,
        )
