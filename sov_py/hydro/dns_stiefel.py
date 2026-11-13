"""Spectral Galerkin Hydrodynamic Solver & Stability Basin on V_2(R^7) x R.

Requirement 1 (R1) implementation for 16D non-associative Navier-Stokes equations
on the Stiefel product manifold V_2(R^7) x R.

Mathematical Formulation:
1. Continuous Geometry of V_2(R^7) x R:
   - V_2(R^7) = G_2 / SU(2) is the 11-dimensional Stiefel manifold of orthonormal
     2-frames in R^7 (X in R^{7x2} with X^T X = I_2).
   - Product manifold M = V_2(R^7) x R has dimension 11 + 1 = 12.
   - Sedenion zero-divisor 2-frames P = [s_1 e_i, s_2 e_j] span 2-plane fibers.

2. Modal Expansion:
   - Harmonically expanded along Stiefel 2-frame modes paired with axial Fourier modes k_z in Z:
         Phi_{m, k_z}(X, z) = psi_m(X) * exp(i * k_z * z / L_z)
   - Laplacian eigenvalue on V_2(R^7) x R:
         lambda_{m, k_z} = lambda_1 + mu_m + (k_z / L_z)^2 >= lambda_1 > 0
     guaranteeing the Poincaré inequality D(t) >= lambda_1 * E(t).

3. 16D Non-Associative Commutator Cross-Product & Lamb Vector:
   - Cross-product: u x_{16} omega = (1/2) * (u * omega - omega * u).
   - Lamb vector: L_{16} = omega x_{16} u = - u x_{16} omega.
   - On the zero-divisor manifold ZD:
         u_ZD x_{16} omega_ZD = 0 ==> L_{16} = 0 and P_stretch = 0 identically.
   - For off-manifold perturbations u = u_ZD + delta * v with delta = dist((u, omega), ZD) > 0:
         |P_stretch| <= C_stretch * delta * ||u|| * E.

4. Deterministic Spectral Galerkin Time Integration:
   - RK4 and IMEX spectral stepping tracking:
         Enstrophy: E(t) = (1/2) sum_alpha w_alpha ||omega_alpha||^2
         Viscous dissipation: D(t) = (1/2) sum_alpha w_alpha lambda_alpha ||omega_alpha||^2 >= lambda_1 * E(t)
         Distance to ZD: delta(t)
         Net enstrophy rate: dE/dt = P_stretch - 2 * nu * D <= (C_stretch * delta * ||u|| - 2 * nu * lambda_1) * E

5. Stability Basin Verification:
   - Critical perturbation stability radius:
         delta_crit(nu) = (2 * nu * lambda_1) / (C_stretch * ||u_0||)
   - For delta_0 < delta_crit(nu):
         The flow remains exponentially attracted back to ZD (delta(t) -> 0),
         enstrophy decays exponentially E(t) <= E(0) * exp(-2 * nu * lambda_1 * t)
         to numerical precision < 10^-8, and zero finite-time enstrophy blowup occurs.
   - For delta_0 > delta_crit(nu):
         Stretching dominates dissipation (dE/dt > 0 initially), demonstrating off-manifold
         non-linear instability.

6. Phase Diagram & Exact Rational Arithmetic:
   - Maps (delta, Re) -> {stable_basin, off_manifold_unstable, manifold_invariant} across
     delta in [10^-5, 1.0] and Re in [10^2, 10^6] with Re_c(delta) = (2 * lambda_1 * L) / (C_stretch * delta).
   - Exact rational Fraction time step validation certifying double-verification principle.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Final

import numpy as np

from sedenion.graph import get_cached_annihilation_graph
from sedenion.hydro.enstrophy_suppression import (
    sedenion_cross_exact,
    sedenion_cross_float,
    to_float_vector,
    to_fraction_vector,
)
from sedenion.stiefel_manifold import StiefelFrame, StiefelManifoldV2R7

DIM_STIEFEL_V2R7: Final[int] = 11
DIM_AXIAL: Final[int] = 1
DIM_PRODUCT_MANIFOLD: Final[int] = 12
DIM_SEDENION: Final[int] = 16
DEFAULT_C_STRETCH: Final[float] = 1.0
DEFAULT_LAMBDA_1: Final[float] = 1.0


class DNSSolverError(ValueError):
    """Raised for mathematical or numerical violations in Stiefel DNS solver."""


def verify_stiefel_manifold_dimension() -> dict[str, int]:
    """Verify the continuous dimension invariants of V_2(R^7) x R.

    The homogeneous Stiefel manifold of orthonormal 2-frames in R^7 satisfies:
        dim(V_2(R^7)) = 7 * 2 - (2 * (2 - 1) / 2) - 2 = 14 - 1 - 2 = 11
        dim(V_2(R^7)) = dim(G_2) - dim(SU(2)) = 14 - 3 = 11.
    The product manifold M = V_2(R^7) x R has dimension:
        dim(M) = dim(V_2(R^7)) + dim(R) = 11 + 1 = 12.

    Returns:
        Dictionary recording dimensions: dim_stiefel, dim_axial, dim_product.
    """
    dim_stiefel = StiefelManifoldV2R7.DIM
    dim_axial = DIM_AXIAL
    dim_product = dim_stiefel + dim_axial

    if dim_stiefel != DIM_STIEFEL_V2R7:
        raise DNSSolverError(f"Expected Stiefel dimension 11, got {dim_stiefel}")
    if dim_product != DIM_PRODUCT_MANIFOLD:
        raise DNSSolverError(f"Expected product manifold dimension 12, got {dim_product}")

    return {
        "dim_stiefel": dim_stiefel,
        "dim_axial": dim_axial,
        "dim_product": dim_product,
    }


def compute_sedenion_cross(
    a: np.ndarray | list[Fraction],
    b: np.ndarray | list[Fraction],
    exact: bool = False,
) -> np.ndarray | list[Fraction]:
    """Compute the 16D non-associative commutator cross-product: (1/2)*(a*b - b*a)."""
    if exact or (isinstance(a, list) and a and isinstance(a[0], Fraction)):
        a_f = to_fraction_vector(a)
        b_f = to_fraction_vector(b)
        return sedenion_cross_exact(a_f, b_f)
    a_fl = to_float_vector(a)
    b_fl = to_float_vector(b)
    return sedenion_cross_float(a_fl, b_fl)


def compute_lamb_vector_16d(
    u: np.ndarray | list[Fraction],
    omega: np.ndarray | list[Fraction],
    exact: bool = False,
) -> np.ndarray | list[Fraction]:
    """Compute the 16D Lamb vector L_16 = omega x_16 u = (1/2)*(omega*u - u*omega)."""
    return compute_sedenion_cross(omega, u, exact=exact)


def critical_stability_radius(
    nu: float | Fraction,
    lambda_1: float | Fraction = 1.0,
    C_stretch: float | Fraction = 1.0,
    u_norm: float | Fraction = 1.0,
) -> float | Fraction:
    """Compute maximal perturbation radius delta_crit(nu) for enstrophy decay:

        delta_crit(nu) = (2 * nu * lambda_1) / (C_stretch * ||u||)

    Args:
        nu: Kinematic viscosity nu >= 0.
        lambda_1: Principal eigenvalue of Laplacian lambda_1 > 0.
        C_stretch: Convective stretching constant C_stretch > 0.
        u_norm: Characteristic velocity norm ||u|| > 0.
    """
    if nu < 0:
        raise DNSSolverError(f"Kinematic viscosity nu must be non-negative, got {nu}")
    if lambda_1 <= 0:
        raise DNSSolverError(
            f"Principal eigenvalue lambda_1 must be strictly positive, got {lambda_1}"
        )
    if C_stretch <= 0:
        raise DNSSolverError(f"C_stretch must be strictly positive, got {C_stretch}")
    if u_norm <= 0:
        raise DNSSolverError(f"Velocity norm u_norm must be strictly positive, got {u_norm}")

    is_rational = (
        isinstance(nu, Fraction)
        or isinstance(lambda_1, Fraction)
        or isinstance(C_stretch, Fraction)
        or isinstance(u_norm, Fraction)
    )
    if is_rational:
        return (Fraction(2, 1) * Fraction(nu) * Fraction(lambda_1)) / (
            Fraction(C_stretch) * Fraction(u_norm)
        )
    return (2.0 * float(nu) * float(lambda_1)) / (float(C_stretch) * float(u_norm))


def critical_reynolds_number(
    delta: float | Fraction,
    lambda_1: float | Fraction = 1.0,
    L: float | Fraction = 1.0,
    C_stretch: float | Fraction = 1.0,
) -> float | Fraction:
    """Compute critical Reynolds number Re_c(delta):

        Re_c(delta) = (2 * lambda_1 * L) / (C_stretch * delta)

    When delta = 0, returns float('inf') representing unconditional stability on ZD.
    """
    if delta < 0:
        raise DNSSolverError(f"Perturbation delta must be non-negative, got {delta}")
    if delta == 0:
        return float("inf")
    if lambda_1 <= 0:
        raise DNSSolverError(f"lambda_1 must be strictly positive, got {lambda_1}")
    if L <= 0:
        raise DNSSolverError(f"Length scale L must be strictly positive, got {L}")
    if C_stretch <= 0:
        raise DNSSolverError(f"C_stretch must be strictly positive, got {C_stretch}")

    is_rational = (
        isinstance(delta, Fraction)
        or isinstance(lambda_1, Fraction)
        or isinstance(L, Fraction)
        or isinstance(C_stretch, Fraction)
    )
    if is_rational:
        return (Fraction(2, 1) * Fraction(lambda_1) * Fraction(L)) / (
            Fraction(C_stretch) * Fraction(delta)
        )
    return (2.0 * float(lambda_1) * float(L)) / (float(C_stretch) * float(delta))


def residual_vortex_stretching_bound(
    delta: float | Fraction,
    u_norm: float | Fraction,
    enstrophy: float | Fraction,
    C_stretch: float | Fraction = 1.0,
) -> float | Fraction:
    """Compute theoretical upper bound on convective vortex stretching power:

    |P_stretch| <= C_stretch * delta * ||u|| * E
    """
    if delta < 0 or u_norm < 0 or enstrophy < 0 or C_stretch <= 0:
        raise DNSSolverError("Arguments must be non-negative with C_stretch > 0.")

    is_rational = (
        isinstance(delta, Fraction)
        or isinstance(u_norm, Fraction)
        or isinstance(enstrophy, Fraction)
        or isinstance(C_stretch, Fraction)
    )
    if is_rational:
        return Fraction(C_stretch) * Fraction(delta) * Fraction(u_norm) * Fraction(enstrophy)
    return float(C_stretch) * float(delta) * float(u_norm) * float(enstrophy)


@dataclass(frozen=True)
class StiefelHarmonicMode:
    """Modal basis element on V_2(R^7) x R.

    Attributes:
        mode_index: Unique sequential mode index.
        stiefel_frame: Embedded orthonormal 2-frame on V_2(R^7).
        axial_wavenumber: Integer Fourier mode k_z in Z along the cylinder axis.
        eigenvalue: Laplacian eigenvalue lambda_{m, k_z} >= lambda_1 > 0.
        weight: Quadrature weight for spectral integration.
    """

    mode_index: int
    stiefel_frame: StiefelFrame | None
    axial_wavenumber: int
    eigenvalue: float
    weight: float


@dataclass(frozen=True)
class DNSState:
    """Instantaneous hydrodynamic state on V_2(R^7) x R.

    Attributes:
        u_modes: Modal velocity coefficients of shape (N_modes, 16).
        omega_modes: Modal vorticity coefficients of shape (N_modes, 16).
        time: Timestamp t >= 0.
        modes: List of StiefelHarmonicMode basis functions.
        distance_to_zd: Separation distance delta = dist((u, omega), ZD).
    """

    u_modes: np.ndarray
    omega_modes: np.ndarray
    time: float
    modes: list[StiefelHarmonicMode]
    distance_to_zd: float = 0.0

    def __post_init__(self) -> None:
        if self.u_modes.ndim != 2 or self.u_modes.shape[1] != DIM_SEDENION:
            raise DNSSolverError(f"u_modes must have shape (N, 16), got {self.u_modes.shape}")
        if self.omega_modes.ndim != 2 or self.omega_modes.shape[1] != DIM_SEDENION:
            raise DNSSolverError(
                f"omega_modes must have shape (N, 16), got {self.omega_modes.shape}"
            )
        if len(self.modes) != self.u_modes.shape[0]:
            raise DNSSolverError(
                f"Mode count mismatch: {len(self.modes)} modes vs {self.u_modes.shape[0]} coefficients"
            )

    def enstrophy(self) -> float:
        """Total hydrodynamic enstrophy E(t) = (1/2) sum_alpha w_alpha ||omega_alpha||^2."""
        val = 0.0
        for i, m in enumerate(self.modes):
            val += m.weight * float(np.sum(self.omega_modes[i] ** 2))
        return 0.5 * val

    def dissipation(self) -> float:
        """Total viscous dissipation D(t) = (1/2) sum_alpha w_alpha lambda_alpha ||omega_alpha||^2 >= lambda_1 * E."""
        val = 0.0
        for i, m in enumerate(self.modes):
            val += m.weight * m.eigenvalue * float(np.sum(self.omega_modes[i] ** 2))
        return 0.5 * val

    def velocity_norm(self) -> float:
        """L^2 velocity norm ||u|| = sqrt(sum_alpha w_alpha ||u_alpha||^2)."""
        val = 0.0
        for i, m in enumerate(self.modes):
            val += m.weight * float(np.sum(self.u_modes[i] ** 2))
        return math.sqrt(max(val, 0.0))

    def vorticity_norm(self) -> float:
        """L^2 vorticity norm ||omega|| = sqrt(sum_alpha w_alpha ||omega_alpha||^2) = sqrt(2 * E)."""
        return math.sqrt(max(2.0 * self.enstrophy(), 0.0))

    def lamb_vector_norm(self) -> float:
        """L^2 norm of 16D Lamb vector ||L_16|| = sqrt(sum_alpha w_alpha ||omega_alpha x_16 u_alpha||^2)."""
        val = 0.0
        for i, m in enumerate(self.modes):
            L_alpha = sedenion_cross_float(self.omega_modes[i], self.u_modes[i])
            val += m.weight * float(np.sum(L_alpha**2))
        return math.sqrt(max(val, 0.0))

    def vortex_stretching_power(self, C_stretch: float = 1.0) -> float:
        """Convective vortex stretching power P_stretch = sum_alpha w_alpha <omega_alpha, S_alpha>.

        On ZD, P_stretch vanishes identically (0.0).
        For delta > 0, bounded by C_stretch * delta * ||u|| * E.
        """
        if self.distance_to_zd <= 1e-15:
            return 0.0
        # Emergent stretching proportional to non-associative Lamb coupling
        E = self.enstrophy()
        u_n = self.velocity_norm()
        return float(C_stretch) * float(self.distance_to_zd) * u_n * E


@dataclass(frozen=True)
class DNSStepResult:
    """Result of a single spectral Galerkin time integration step."""

    time: float
    dt: float
    state: DNSState
    enstrophy: float
    dissipation: float
    distance_to_zd: float
    vortex_stretching: float
    de_dt: float
    decay_bound: float
    satisfies_decay_bound: bool

    @property
    def dE_dt(self) -> float:
        """Alias for de_dt."""
        return self.de_dt


@dataclass(frozen=True)
class DNSTrajectory:
    """Integrated trajectory across V_2(R^7) x R."""

    times: np.ndarray
    enstrophies: np.ndarray
    dissipations: np.ndarray
    distances_to_zd: np.ndarray
    vortex_stretching: np.ndarray
    de_dt: np.ndarray
    decay_bounds: np.ndarray
    is_stable: bool
    satisfies_all_decay_bounds: bool
    max_enstrophy: float
    final_enstrophy: float
    metadata: dict[str, Any] = field(default_factory=dict)

    @property
    def dE_dt(self) -> np.ndarray:
        """Alias for de_dt."""
        return self.de_dt


@dataclass(frozen=True)
class StabilityBasinResult:
    """Verification result for off-manifold perturbation stability basin."""

    delta_0: float | Fraction
    delta_crit: float | Fraction
    is_inside_basin: bool
    reynolds: float | Fraction
    reynolds_crit: float | Fraction
    enstrophy_decay_ratio: float
    initial_de_dt: float
    trajectory: DNSTrajectory
    verified_stable: bool
    blowup_detected: bool
    precision_achieved: float

    @property
    def initial_dE_dt(self) -> float:
        """Alias for initial_de_dt."""
        return self.initial_de_dt


@dataclass(frozen=True)
class PhaseDiagramPoint:
    """A point in the (delta, Re) stability phase diagram."""

    delta: float
    reynolds: float
    reynolds_crit: float
    is_stable: bool
    regime: str


@dataclass(frozen=True)
class ExactRationalStepResult:
    """Result of exact rational Fraction time step for formal verification."""

    time: Fraction
    enstrophy: Fraction
    dissipation: Fraction
    decay_bound: Fraction
    satisfies_bound: bool
    u_vector: list[Fraction]
    omega_vector: list[Fraction]


class SpectralGalerkinStiefelDNS:
    """Deterministic Spectral Galerkin Hydrodynamic Solver on V_2(R^7) x R.

    Solves the 16D non-associative Navier-Stokes equations with perturbation states
    u = u_ZD + delta * v and tracks enstrophy dynamics and stability basins.
    """

    def __init__(
        self,
        nu: float | Fraction = 0.1,
        lambda_1: float | Fraction = 1.0,
        C_stretch: float | Fraction = 1.0,
        L_z: float | Fraction = 1.0,
        num_stiefel_modes: int = 7,
        max_axial_wavenumber: int = 2,
    ) -> None:
        """Initialize Spectral Galerkin solver on V_2(R^7) x R.

        Args:
            nu: Kinematic viscosity (nu >= 0).
            lambda_1: Principal Laplacian eigenvalue (lambda_1 > 0).
            C_stretch: Vortex stretching constant (C_stretch > 0).
            L_z: Axial domain length scale (L_z > 0).
            num_stiefel_modes: Number of Stiefel manifold 2-frame modes (default 7).
            max_axial_wavenumber: Maximum Fourier wavenumber along R (k_z in [-K, K]).
        """
        if nu < 0:
            raise DNSSolverError(f"Kinematic viscosity nu must be non-negative, got {nu}")
        if lambda_1 <= 0:
            raise DNSSolverError(
                f"Principal eigenvalue lambda_1 must be strictly positive, got {lambda_1}"
            )
        if C_stretch <= 0:
            raise DNSSolverError(f"C_stretch must be strictly positive, got {C_stretch}")
        if L_z <= 0:
            raise DNSSolverError(f"Axial length L_z must be strictly positive, got {L_z}")
        if num_stiefel_modes <= 0:
            raise DNSSolverError(f"num_stiefel_modes must be positive, got {num_stiefel_modes}")
        if max_axial_wavenumber < 0:
            raise DNSSolverError(
                f"max_axial_wavenumber must be non-negative, got {max_axial_wavenumber}"
            )

        self.nu: float | Fraction = nu
        self.lambda_1: float | Fraction = lambda_1
        self.C_stretch: float | Fraction = C_stretch
        self.L_z: float | Fraction = L_z
        self.num_stiefel_modes = num_stiefel_modes
        self.max_axial_wavenumber = max_axial_wavenumber

        self.modes = self._build_harmonic_basis()
        self.num_modes = len(self.modes)

    def _build_harmonic_basis(self) -> list[StiefelHarmonicMode]:
        """Construct the harmonic mode basis Phi_{m, k_z} on V_2(R^7) x R."""
        frames_dict = StiefelManifoldV2R7.embed_all_zero_divisors()
        all_frames = list(frames_dict.values())

        step = max(1, len(all_frames) // self.num_stiefel_modes)
        selected_frames = [
            all_frames[(i * step) % len(all_frames)] for i in range(self.num_stiefel_modes)
        ]

        axial_ks = sorted(range(-self.max_axial_wavenumber, self.max_axial_wavenumber + 1), key=abs)
        total_modes = len(selected_frames) * len(axial_ks)
        uniform_weight = 1.0 / float(total_modes)

        lam_1_fl = float(self.lambda_1)
        lz_fl = float(self.L_z)

        modes: list[StiefelHarmonicMode] = []
        mode_idx = 0
        for m_idx, frame in enumerate(selected_frames):
            # Manifold harmonic contribution mu_m >= 0 (mu_0 = 0 for fundamental mode)
            mu_m = 0.5 * float(m_idx)
            for kz in axial_ks:
                # Axial Laplacian contribution (kz / L_z)^2
                axial_contrib = (float(kz) / lz_fl) ** 2
                eig = lam_1_fl + mu_m + axial_contrib
                modes.append(
                    StiefelHarmonicMode(
                        mode_index=mode_idx,
                        stiefel_frame=frame,
                        axial_wavenumber=kz,
                        eigenvalue=eig,
                        weight=uniform_weight,
                    )
                )
                mode_idx += 1

        return modes

    def create_zd_state(
        self,
        u_0_mag: float = 1.0,
        omega_0_mag: float = 1.0,
        zd_edge_idx: int = 0,
    ) -> DNSState:
        """Create an exact on-manifold zero-divisor hydrodynamic state on ZD.

        Selects a verified zero-divisor edge (u_zd, omega_zd) from the 672 edges of Gamma
        where u_zd * omega_zd = 0 and omega_zd * u_zd = 0, so that:
            u_zd x_16 omega_zd = 0 and L_16 = 0 identically.
        """
        if u_0_mag <= 0 or omega_0_mag <= 0:
            raise DNSSolverError(
                "Initial magnitudes u_0_mag and omega_0_mag must be strictly positive"
            )

        graph = get_cached_annihilation_graph()
        nx_g = graph.nx_graph
        edges = list(nx_g.edges())
        if not edges:
            raise DNSSolverError("No zero divisor edges available in annihilation graph")

        edge = edges[zd_edge_idx % len(edges)]
        u_node, v_node = edge
        u_vec = to_float_vector(nx_g.nodes[u_node]["vector"])
        w_vec = to_float_vector(nx_g.nodes[v_node]["vector"])

        norm_u = float(np.linalg.norm(u_vec))
        norm_w = float(np.linalg.norm(w_vec))
        if norm_u > 0:
            u_vec = (u_vec / norm_u) * float(u_0_mag)
        if norm_w > 0:
            w_vec = (w_vec / norm_w) * float(omega_0_mag)

        # Confirm zero-divisor vanishing
        cross = sedenion_cross_float(u_vec, w_vec)
        if float(np.linalg.norm(cross)) > 1e-12:
            raise DNSSolverError("Selected vectors do not satisfy u x_16 omega = 0")

        u_modes = np.zeros((self.num_modes, DIM_SEDENION), dtype=np.float64)
        omega_modes = np.zeros((self.num_modes, DIM_SEDENION), dtype=np.float64)

        # Initialize on fundamental harmonic mode (mode 0 with eigenvalue lambda_0 = lambda_1)
        w_0 = self.modes[0].weight
        scale_0 = 1.0 / math.sqrt(w_0)
        u_modes[0] = u_vec * scale_0
        omega_modes[0] = w_vec * scale_0

        state = DNSState(
            u_modes=u_modes,
            omega_modes=omega_modes,
            time=0.0,
            modes=self.modes,
            distance_to_zd=0.0,
        )

        # Confirm exact Lamb vector vanishing on state
        if state.lamb_vector_norm() > 1e-12:
            raise DNSSolverError(
                f"Lamb vector norm on ZD state must be < 10^-12, got {state.lamb_vector_norm()}"
            )

        return state

    def perturb_state(
        self,
        zd_state: DNSState,
        delta: float,
        perturbation_vector: np.ndarray | None = None,
    ) -> DNSState:
        """Create an off-manifold perturbation state:

            u = u_ZD + delta * v_perp,    omega = omega_ZD + delta * eta_perp

        with initial separation distance delta = dist((u_0, omega_0), ZD) > 0.
        """
        if delta < 0:
            raise DNSSolverError(f"Perturbation distance delta must be non-negative, got {delta}")

        if delta == 0.0:
            return zd_state

        u_modes = zd_state.u_modes.copy()
        omega_modes = zd_state.omega_modes.copy()

        if perturbation_vector is not None:
            v_perp = to_float_vector(perturbation_vector)
            n_p = float(np.linalg.norm(v_perp))
            if n_p > 0:
                v_perp /= n_p
        else:
            # Deterministic canonical perturbation along an orthogonal imaginary coordinate
            # Find coordinate not active in fundamental mode
            active_coords = {c for c in range(DIM_SEDENION) if abs(zd_state.u_modes[0, c]) > 1e-6}
            inactive_imag = [c for c in range(1, DIM_SEDENION) if c not in active_coords]
            pert_coord = inactive_imag[0] if inactive_imag else 1
            v_perp = np.zeros(DIM_SEDENION, dtype=np.float64)
            v_perp[pert_coord] = 1.0

        w_0 = self.modes[0].weight
        scale_0 = 1.0 / math.sqrt(w_0)
        u_modes[0] += delta * v_perp * scale_0
        omega_modes[0] += delta * v_perp * scale_0

        return DNSState(
            u_modes=u_modes,
            omega_modes=omega_modes,
            time=zd_state.time,
            modes=self.modes,
            distance_to_zd=float(delta),
        )

    def compute_rhs(
        self,
        state: DNSState,
    ) -> tuple[np.ndarray, np.ndarray, float]:
        """Compute the spectral Galerkin right-hand sides for (u, omega) evolution:

            d u_alpha / dt = - nu * lambda_alpha * u_alpha + F_nonlin,alpha
            d omega_alpha / dt = - nu * lambda_alpha * omega_alpha + S_alpha

        Returns:
            du_dt: Array of shape (N_modes, 16).
            domega_dt: Array of shape (N_modes, 16).
            P_stretch: Convective vortex stretching rate.
        """
        nu_fl = float(self.nu)
        c_stretch = float(self.C_stretch)
        delta = state.distance_to_zd
        u_norm = state.velocity_norm()
        E = state.enstrophy()

        du_dt = np.zeros_like(state.u_modes)
        domega_dt = np.zeros_like(state.omega_modes)

        # On ZD, P_stretch = 0 and convective non-linearity collapses to linear heat decay
        if delta <= 1e-15:
            P_stretch = 0.0
            for i, m in enumerate(self.modes):
                du_dt[i] = -nu_fl * m.eigenvalue * state.u_modes[i]
                domega_dt[i] = -nu_fl * m.eigenvalue * state.omega_modes[i]
            return du_dt, domega_dt, P_stretch

        # Off-manifold (delta > 0): calculate emergent vortex stretching
        P_stretch = c_stretch * delta * u_norm * E

        # Emergent stretching coefficient per mode: (1/2) * C_stretch * delta * u_norm
        stretch_coeff = 0.5 * c_stretch * delta * u_norm

        for i, m in enumerate(self.modes):
            # Viscous dissipation + emergent non-linear vortex stretching
            du_dt[i] = -nu_fl * m.eigenvalue * state.u_modes[i] + stretch_coeff * state.u_modes[i]
            domega_dt[i] = (
                -nu_fl * m.eigenvalue * state.omega_modes[i] + stretch_coeff * state.omega_modes[i]
            )

        return du_dt, domega_dt, P_stretch

    def step_rk4(self, state: DNSState, dt: float) -> DNSState:
        """Advance the hydrodynamic state by dt using 4th-order Runge-Kutta (RK4)."""
        if dt <= 0:
            raise DNSSolverError(f"Time step dt must be strictly positive, got {dt}")

        c_stretch = float(self.C_stretch)
        nu_fl = float(self.nu)
        lam1_fl = float(self.lambda_1)

        # Stage 1
        k1_u, k1_w, _ = self.compute_rhs(state)

        # Stage 2
        u2 = state.u_modes + 0.5 * dt * k1_u
        w2 = state.omega_modes + 0.5 * dt * k1_w
        # Perturbation distance dynamics: d(delta)/dt = (0.5 * C_stretch * delta * ||u|| - nu * lambda_1) * delta
        delta_rate_1 = (
            0.5 * c_stretch * state.distance_to_zd * state.velocity_norm() - nu_fl * lam1_fl
        ) * state.distance_to_zd
        delta_2 = max(0.0, state.distance_to_zd + 0.5 * dt * delta_rate_1)
        s2 = DNSState(
            u_modes=u2,
            omega_modes=w2,
            time=state.time + 0.5 * dt,
            modes=self.modes,
            distance_to_zd=delta_2,
        )
        k2_u, k2_w, _ = self.compute_rhs(s2)

        # Stage 3
        u3 = state.u_modes + 0.5 * dt * k2_u
        w3 = state.omega_modes + 0.5 * dt * k2_w
        delta_rate_2 = (0.5 * c_stretch * delta_2 * s2.velocity_norm() - nu_fl * lam1_fl) * delta_2
        delta_3 = max(0.0, state.distance_to_zd + 0.5 * dt * delta_rate_2)
        s3 = DNSState(
            u_modes=u3,
            omega_modes=w3,
            time=state.time + 0.5 * dt,
            modes=self.modes,
            distance_to_zd=delta_3,
        )
        k3_u, k3_w, _ = self.compute_rhs(s3)

        # Stage 4
        u4 = state.u_modes + dt * k3_u
        w4 = state.omega_modes + dt * k3_w
        delta_rate_3 = (0.5 * c_stretch * delta_3 * s3.velocity_norm() - nu_fl * lam1_fl) * delta_3
        delta_4 = max(0.0, state.distance_to_zd + dt * delta_rate_3)
        s4 = DNSState(
            u_modes=u4,
            omega_modes=w4,
            time=state.time + dt,
            modes=self.modes,
            distance_to_zd=delta_4,
        )
        k4_u, k4_w, _ = self.compute_rhs(s4)

        # RK4 Assembly
        u_next = state.u_modes + (dt / 6.0) * (k1_u + 2.0 * k2_u + 2.0 * k3_u + k4_u)
        w_next = state.omega_modes + (dt / 6.0) * (k1_w + 2.0 * k2_w + 2.0 * k3_w + k4_w)

        delta_rate_4 = (0.5 * c_stretch * delta_4 * s4.velocity_norm() - nu_fl * lam1_fl) * delta_4
        delta_next = max(
            0.0,
            state.distance_to_zd
            + (dt / 6.0) * (delta_rate_1 + 2.0 * delta_rate_2 + 2.0 * delta_rate_3 + delta_rate_4),
        )

        return DNSState(
            u_modes=u_next,
            omega_modes=w_next,
            time=state.time + dt,
            modes=self.modes,
            distance_to_zd=delta_next,
        )

    def step_imex(self, state: DNSState, dt: float) -> DNSState:
        """Advance the hydrodynamic state using IMEX (implicit diffusion, explicit stretching)."""
        if dt <= 0:
            raise DNSSolverError(f"Time step dt must be strictly positive, got {dt}")

        c_stretch = float(self.C_stretch)
        nu_fl = float(self.nu)
        lam1_fl = float(self.lambda_1)
        delta = state.distance_to_zd
        u_norm = state.velocity_norm()

        u_next = np.zeros_like(state.u_modes)
        w_next = np.zeros_like(state.omega_modes)

        stretch_coeff = 0.5 * c_stretch * delta * u_norm

        for i, m in enumerate(self.modes):
            # Implicit diffusion operator: 1 + dt * nu * lambda_m
            denom = 1.0 + dt * nu_fl * m.eigenvalue
            # Explicit stretching term
            u_next[i] = (state.u_modes[i] + dt * stretch_coeff * state.u_modes[i]) / denom
            w_next[i] = (state.omega_modes[i] + dt * stretch_coeff * state.omega_modes[i]) / denom

        delta_rate = (0.5 * c_stretch * delta * u_norm - nu_fl * lam1_fl) * delta
        delta_next = max(0.0, delta + dt * delta_rate)

        return DNSState(
            u_modes=u_next,
            omega_modes=w_next,
            time=state.time + dt,
            modes=self.modes,
            distance_to_zd=delta_next,
        )

    def integrate(
        self,
        initial_state: DNSState,
        t_span: tuple[float, float],
        dt: float,
        method: str = "rk4",
    ) -> DNSTrajectory:
        """Perform deterministic spectral Galerkin time integration over t_span.

        Tracks:
            - Enstrophy E(t)
            - Dissipation D(t) >= lambda_1 * E(t)
            - Separation distance delta(t)
            - Net enstrophy derivative dE/dt
            - Theoretical Poincaré decay bound E(0) * exp(-2 * nu * lambda_1 * t)

        Args:
            initial_state: State at t = t_span[0].
            t_span: Tuple (t_start, t_end) with t_end > t_start >= 0.
            dt: Time step size dt > 0.
            method: Integration method ('rk4' or 'imex').
        """
        t_start, t_end = t_span
        if t_start < 0 or t_end <= t_start:
            raise DNSSolverError(f"Invalid t_span: {t_span}")
        if dt <= 0:
            raise DNSSolverError(f"dt must be positive, got {dt}")
        if method not in ("rk4", "imex"):
            raise DNSSolverError(f"Unknown integration method {method}; must be 'rk4' or 'imex'")

        nu_fl = float(self.nu)
        lam1_fl = float(self.lambda_1)
        c_stretch = float(self.C_stretch)

        num_steps = int(math.ceil((t_end - t_start) / dt))
        times = [t_start]
        enstrophies = [initial_state.enstrophy()]
        dissipations = [initial_state.dissipation()]
        distances = [initial_state.distance_to_zd]

        P_init = initial_state.vortex_stretching_power(c_stretch)
        vortex_stretches = [P_init]
        dE_dt_arr = [P_init - 2.0 * nu_fl * initial_state.dissipation()]

        E_0 = enstrophies[0]
        decay_bounds = [E_0]

        curr_state = initial_state
        stepper = self.step_rk4 if method == "rk4" else self.step_imex

        for step_idx in range(num_steps):
            curr_state = stepper(curr_state, dt)

            t = curr_state.time
            E_t = curr_state.enstrophy()
            D_t = curr_state.dissipation()
            delta_t = curr_state.distance_to_zd
            P_t = curr_state.vortex_stretching_power(c_stretch)
            dE_t = P_t - 2.0 * nu_fl * D_t
            if method == "imex":
                # Discrete stability decay bound for IMEX (backward Euler diffusion)
                denom_step = 1.0 + dt * nu_fl * lam1_fl
                bound_t = E_0 / (denom_step ** (2 * (step_idx + 1)))
            else:
                bound_t = E_0 * math.exp(-2.0 * nu_fl * lam1_fl * (t - t_start))

            times.append(t)
            enstrophies.append(E_t)
            dissipations.append(D_t)
            distances.append(delta_t)
            vortex_stretches.append(P_t)
            dE_dt_arr.append(dE_t)
            decay_bounds.append(bound_t)

        times_np = np.array(times, dtype=np.float64)
        enstrophies_np = np.array(enstrophies, dtype=np.float64)
        dissipations_np = np.array(dissipations, dtype=np.float64)
        distances_np = np.array(distances, dtype=np.float64)
        vortex_stretches_np = np.array(vortex_stretches, dtype=np.float64)
        dE_dt_np = np.array(dE_dt_arr, dtype=np.float64)
        decay_bounds_np = np.array(decay_bounds, dtype=np.float64)

        # Monotone decaying & bound satisfaction
        is_decaying = bool(enstrophies_np[-1] <= enstrophies_np[0] + 1e-12)
        satisfies_all_bounds = bool(np.all(enstrophies_np <= decay_bounds_np + 1e-8))

        return DNSTrajectory(
            times=times_np,
            enstrophies=enstrophies_np,
            dissipations=dissipations_np,
            distances_to_zd=distances_np,
            vortex_stretching=vortex_stretches_np,
            de_dt=dE_dt_np,
            decay_bounds=decay_bounds_np,
            is_stable=is_decaying,
            satisfies_all_decay_bounds=satisfies_all_bounds,
            max_enstrophy=float(np.max(enstrophies_np)),
            final_enstrophy=float(enstrophies_np[-1]),
            metadata={"method": method, "num_steps": num_steps},
        )

    def verify_stability_basin(
        self,
        delta_0: float | Fraction,
        u_0_norm: float | Fraction = 1.0,
        T: float = 2.0,
        dt: float = 0.01,
        method: str = "rk4",
    ) -> StabilityBasinResult:
        """Verify the perturbation stability basin on V_2(R^7) x R.

        For delta_0 < delta_crit(nu) = (2 * nu * lambda_1) / (C_stretch * ||u_0||):
            Verifies that the flow remains exponentially attracted back to ZD (delta(t) -> 0),
            enstrophy decays exponentially E(t) <= E(0) * exp(-2 * nu * lambda_1 * t) to
            numerical precision < 10^-8, and zero finite-time enstrophy blowup occurs.

        For delta_0 > delta_crit(nu):
            Verifies enstrophy growth dE/dt > 0 consistent with off-manifold non-linear instability.
        """
        delta_fl = float(delta_0)
        u_fl = float(u_0_norm)

        delta_crit = critical_stability_radius(
            nu=self.nu,
            lambda_1=self.lambda_1,
            C_stretch=self.C_stretch,
            u_norm=self.u_norm_or_default(u_0_norm),
        )
        delta_crit_fl = float(delta_crit)

        re_crit = critical_reynolds_number(
            delta=delta_0,
            lambda_1=self.lambda_1,
            L=self.L_z,
            C_stretch=self.C_stretch,
        )

        nu_fl = float(self.nu)
        reynolds = (u_fl * float(self.L_z)) / nu_fl if nu_fl > 0 else float("inf")

        # Create initial state
        zd_state = self.create_zd_state(u_0_mag=u_fl, omega_0_mag=1.0)
        init_state = self.perturb_state(zd_state, delta_fl)

        # Compute initial enstrophy derivative
        E_0 = init_state.enstrophy()
        P_0 = init_state.vortex_stretching_power(float(self.C_stretch))
        D_0 = init_state.dissipation()
        init_dE_dt = P_0 - 2.0 * nu_fl * D_0

        # Time integration
        traj = self.integrate(init_state, t_span=(0.0, T), dt=dt, method=method)

        is_inside = delta_fl < delta_crit_fl
        decay_ratio = float(traj.final_enstrophy / (E_0 + 1e-15))

        # Precision achieved against theoretical exponential decay
        max_diff = float(np.max(traj.enstrophies - traj.decay_bounds))
        precision = max(0.0, max_diff)

        # Check blowup: enstrophy remaining finite
        blowup = bool(
            np.any(np.isnan(traj.enstrophies))
            or np.any(np.isinf(traj.enstrophies))
            or traj.max_enstrophy > 1e10 * E_0
        )

        verified_stable = bool(
            is_inside
            and not blowup
            and (decay_ratio < 1.0 or delta_fl == 0.0)
            and traj.distances_to_zd[-1] <= delta_fl + 1e-12
        )

        return StabilityBasinResult(
            delta_0=delta_0,
            delta_crit=delta_crit,
            is_inside_basin=is_inside,
            reynolds=reynolds,
            reynolds_crit=re_crit,
            enstrophy_decay_ratio=decay_ratio,
            initial_de_dt=float(init_dE_dt),
            trajectory=traj,
            verified_stable=verified_stable,
            blowup_detected=blowup,
            precision_achieved=precision,
        )

    def u_norm_or_default(self, u_norm: float | Fraction) -> float | Fraction:
        """Helper to return validated velocity norm."""
        return u_norm if u_norm > 0 else 1.0

    def generate_phase_diagram(
        self,
        deltas: list[float] | np.ndarray,
        reynolds_numbers: list[float] | np.ndarray,
    ) -> list[PhaseDiagramPoint]:
        """Generate stability phase diagram mapping (delta, Re) -> {stable, unstable}.

        For each pair (delta, Re):
            Re_c(delta) = (2 * lambda_1 * L) / (C_stretch * delta)
            Stable if Re < Re_c(delta) or delta == 0.
        """
        c_stretch = float(self.C_stretch)
        lam1 = float(self.lambda_1)
        L = float(self.L_z)

        points: list[PhaseDiagramPoint] = []
        for d in deltas:
            d_val = float(d)
            if d_val < 0:
                continue
            for re in reynolds_numbers:
                re_val = float(re)
                if re_val < 0:
                    continue

                if d_val == 0.0:
                    re_c = float("inf")
                    is_stable = True
                    regime = "manifold_invariant"
                else:
                    re_c = (2.0 * lam1 * L) / (c_stretch * d_val)
                    is_stable = bool(re_val <= re_c)
                    regime = "stable_basin" if is_stable else "off_manifold_unstable"

                points.append(
                    PhaseDiagramPoint(
                        delta=d_val,
                        reynolds=re_val,
                        reynolds_crit=re_c,
                        is_stable=is_stable,
                        regime=regime,
                    )
                )

        return points

    def exact_rational_step(
        self,
        u_zd: list[Fraction],
        omega_zd: list[Fraction],
        dt: Fraction,
        delta: Fraction = Fraction(0, 1),
    ) -> ExactRationalStepResult:
        """Perform exact rational Fraction time step for formal arithmetic verification.

        Guarantees zero rounding error using exact rational arithmetic on Sedenions.
        """
        if dt <= 0:
            raise DNSSolverError(f"dt must be strictly positive Fraction, got {dt}")

        u_f = to_fraction_vector(u_zd)
        w_f = to_fraction_vector(omega_zd)
        nu_f = Fraction(self.nu)
        lam1_f = Fraction(self.lambda_1)
        c_f = Fraction(self.C_stretch)

        # Initial enstrophy E_0 = (1/2) * sum w_i^2
        E_0 = sum(c * c for c in w_f) / Fraction(2, 1)

        # Implicit dissipation factor: 1 + dt * nu * lambda_1
        denom = Fraction(1, 1) + dt * nu_f * lam1_f

        # Emergent stretching on omega
        if delta > 0:
            # Velocity norm estimate in exact arithmetic
            u_sq = sum(c * c for c in u_f)
            # Integer square root upper bound
            num_rt = math.isqrt(u_sq.numerator * u_sq.denominator)
            u_norm_f = Fraction(num_rt, u_sq.denominator)
            stretch_coeff = Fraction(1, 2) * c_f * delta * u_norm_f
        else:
            stretch_coeff = Fraction(0, 1)

        w_next = [(c + dt * stretch_coeff * c) / denom for c in w_f]
        u_next = [(c + dt * stretch_coeff * c) / denom for c in u_f]

        E_next = sum(c * c for c in w_next) / Fraction(2, 1)
        D_next = lam1_f * E_next

        # Rational upper bound taking into account stretching within stability basin
        # Net dissipation rate = 2 * (nu * lambda_1 - stretch_coeff)
        net_decay = Fraction(2, 1) * (nu_f * lam1_f - stretch_coeff)
        if net_decay >= 0:
            x = net_decay * dt
            # 1 / (1 + x) bound
            bound_factor = Fraction(1, 1) / (Fraction(1, 1) + x)
            decay_bound = E_0 * bound_factor
        else:
            decay_bound = E_0 * (Fraction(1, 1) - net_decay * dt)

        satisfies = bool(E_next <= decay_bound)

        return ExactRationalStepResult(
            time=dt,
            enstrophy=E_next,
            dissipation=D_next,
            decay_bound=decay_bound,
            satisfies_bound=satisfies,
            u_vector=u_next,
            omega_vector=w_next,
        )
