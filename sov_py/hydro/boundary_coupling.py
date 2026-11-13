"""Dirichlet-to-Neumann non-associative boundary coupling and corner eddy suppression.

This module implements the Dirichlet-to-Neumann (DtN) operator Lambda_16 for 16D sedenion
fluid equations on the cylindrical domain M = {0 <= r <= 1, z in R}, evaluating
boundary conditions u x_16 n = 0, boundary Lamb vector vanishing, and corner eddy
vortex reconnection suppression at the Hou-Chen collapse corner (r=1, z=0).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

import numpy as np
import scipy.special as sp

from sedenion.hydro.non_associative_fluid import (
    sedenion_cross_product_16d,
    sedenion_product,
)

DIM_SEDENION: Final[int] = 16


class BoundaryCouplingError(Exception):
    """Exception raised for boundary coupling and DtN operator errors."""


@dataclass(frozen=True)
class DtNSpectralMode:
    """Spectral mode of the Dirichlet-to-Neumann operator Lambda_16.

    Attributes:
        wavenumber: Axial wavenumber k.
        eigenvalue: Exact eigenvalue lambda_k = k * I_1(k) / I_0(k).
        asymptotic_ratio: Ratio lambda_k / |k| showing approach to half-Laplacian.
        is_positive: Boolean certifying positivity lambda_k > 0 for k > 0.
    """

    wavenumber: float
    eigenvalue: float
    asymptotic_ratio: float
    is_positive: bool


@dataclass(frozen=True)
class CornerEddyReconnectionResult:
    """Result of corner eddy vortex reconnection rate evaluation.

    Attributes:
        classical_reconnection_rate: Reconnection rate in classical 3D fluid.
        sedenion_reconnection_rate: Reconnection rate under zero-divisor alignment.
        suppression_factor: Ratio sedenion / classical (identically 0.0 on ZD edges).
        is_exact_zero: Boolean certifying complete suppression.
        pair_u: Sedenion velocity vector.
        pair_omega: Sedenion vorticity vector.
    """

    classical_reconnection_rate: float
    sedenion_reconnection_rate: float
    suppression_factor: float
    is_exact_zero: bool
    pair_u: tuple[float, ...]
    pair_omega: tuple[float, ...]


class DirichletToNeumannOperator:
    """Dirichlet-to-Neumann operator Lambda_16 on cylindrical boundary r = 1."""

    def __init__(self, radius: float = 1.0) -> None:
        if radius <= 0.0:
            raise BoundaryCouplingError("Cylinder radius must be strictly positive.")
        self.radius: float = float(radius)

    def compute_mode(self, wavenumber: float) -> DtNSpectralMode:
        """Compute the eigenvalue of the DtN operator for wavenumber k.

        The cylindrical Laplace equation in (r, z) with Phi(r, z) = R(r) e^{i k z}
        yields the modified Bessel equation r^2 R'' + r R' - k^2 r^2 R = 0.
        Regularity at r = 0 requires R(r) = C * I_0(k r).
        Normalizing at r = 1 gives R(r) = I_0(k r) / I_0(k).
        The normal derivative at r = 1 is:
            Lambda_k = [d/dr R(r)]_{r=1} = k * I_1(k) / I_0(k).
        """
        k = float(abs(wavenumber))
        if k < 1e-14:
            return DtNSpectralMode(
                wavenumber=float(wavenumber),
                eigenvalue=0.0,
                asymptotic_ratio=1.0,
                is_positive=False,
            )

        kr = k * self.radius
        i0_val = float(sp.iv(0, kr))
        i1_val = float(sp.iv(1, kr))

        if i0_val == 0.0:
            raise BoundaryCouplingError(f"Bessel function I_0({kr}) evaluated to zero.")

        eig = float((k / self.radius) * (i1_val / i0_val))
        ratio = float(eig / k)

        return DtNSpectralMode(
            wavenumber=float(wavenumber),
            eigenvalue=eig,
            asymptotic_ratio=ratio,
            is_positive=(eig > 0.0),
        )

    def apply_dtn_map(self, z_grid: np.ndarray, g_values: np.ndarray) -> np.ndarray:
        """Apply the DtN operator Lambda_16 to a boundary profile g(z) along r = 1.

        Args:
            z_grid: 1D spatial grid along the cylinder axis z in [-L, L].
            g_values: Sedenion-valued boundary profile of shape (N, 16) or (N,).
        """
        if len(z_grid) < 4:
            raise BoundaryCouplingError("Grid must contain at least 4 points.")
        n_points = len(z_grid)
        dz = float(z_grid[1] - z_grid[0])
        if dz <= 0.0:
            raise BoundaryCouplingError("Grid spacing dz must be strictly positive.")

        freqs = np.fft.fftfreq(n_points, d=dz) * (2.0 * np.pi)

        # Compute DtN multipliers for each wavenumber
        mults = np.zeros(n_points, dtype=np.float64)
        for idx, k in enumerate(freqs):
            mults[idx] = self.compute_mode(k).eigenvalue

        # Component-wise Fourier transform
        if g_values.ndim == 1:
            g_hat = np.fft.fft(g_values)
            res = np.real(np.fft.ifft(g_hat * mults))
            return np.asarray(res, dtype=np.float64)
        elif g_values.ndim == 2 and g_values.shape[1] == DIM_SEDENION:
            out = np.zeros_like(g_values)
            for c in range(DIM_SEDENION):
                c_hat = np.fft.fft(g_values[:, c])
                out[:, c] = np.real(np.fft.ifft(c_hat * mults))
            return np.asarray(out, dtype=np.float64)
        else:
            raise BoundaryCouplingError(
                f"g_values shape {g_values.shape} unsupported. Must be (N,) or (N, 16)."
            )

    def verify_zero_divisor_sector_invariance(
        self,
        u_vector: np.ndarray,
        v_vector: np.ndarray,
        z_grid: np.ndarray,
    ) -> bool:
        """Verify that the DtN operator preserves zero-divisor annihilation.

        If u(z) = f(z) u_0 and v(z) = h(z) v_0 with u_0 * v_0 = 0,
        then Lambda_16(u)(z) * v_0 = 0 identically everywhere.
        """
        if u_vector.shape != (16,) or v_vector.shape != (16,):
            raise BoundaryCouplingError("Vectors must be 16D sedenions.")

        prod_0 = sedenion_product(u_vector, v_vector)
        if np.linalg.norm(prod_0) > 1e-12:
            raise BoundaryCouplingError("Input vectors do not annihilate.")

        # Construct spatial profile
        f_z = np.sin(np.pi * (z_grid - z_grid[0]) / (z_grid[-1] - z_grid[0]))
        u_profile = np.outer(f_z, u_vector)

        dtn_u = self.apply_dtn_map(z_grid, u_profile)

        # Check annihilation at all z points
        for i in range(len(z_grid)):
            prod_z = sedenion_product(dtn_u[i], v_vector)
            if np.linalg.norm(prod_z) > 1e-10:
                return False
        return True


class NonAssociativeBoundaryCoupling:
    """Non-associative boundary condition and corner eddy analysis."""

    def __init__(self, tol: float = 1e-12, dim: int = DIM_SEDENION) -> None:
        self.tol: float = tol
        self.dim: int = dim

    def sedenion_cross_product(self, u: np.ndarray, v: np.ndarray) -> np.ndarray:
        """Compute the 16D sedenion commutator cross product: (uv - vu)/2."""
        return sedenion_cross_product_16d(u, v)

    def evaluate_corner_reconnection(
        self,
        u_sedenion: np.ndarray,
        omega_sedenion: np.ndarray,
        u_classical_3d: np.ndarray | None = None,
        omega_classical_3d: np.ndarray | None = None,
    ) -> CornerEddyReconnectionResult:
        """Evaluate vortex reconnection rate at the singularity corner (r=1, z=0).

        The vortex reconnection energy density is given by:
            R = ||u x omega||^2.
        Under zero-divisor alignment (u * omega = 0), R_sedenion = 0 identically.
        In classical 3D fluid with non-collinear u and omega, R_classical > 0.
        """
        if u_sedenion.shape != (16,) or omega_sedenion.shape != (16,):
            raise BoundaryCouplingError("Sedenion inputs must be 16D.")

        cross_16 = self.sedenion_cross_product(u_sedenion, omega_sedenion)
        r_sed = float(np.sum(cross_16**2))

        # Default classical 3D cross-product if not provided
        if u_classical_3d is None:
            u_classical_3d = np.array([1.0, 0.5, 0.0], dtype=np.float64)
        if omega_classical_3d is None:
            omega_classical_3d = np.array([0.0, 0.0, 2.0], dtype=np.float64)

        cross_3d = np.cross(u_classical_3d, omega_classical_3d)
        r_class = float(np.sum(cross_3d**2))

        suppression = 1.0 if r_class < 1e-14 else float(r_sed / r_class)
        is_zero = bool(r_sed < 1e-12)

        return CornerEddyReconnectionResult(
            classical_reconnection_rate=r_class,
            sedenion_reconnection_rate=r_sed,
            suppression_factor=suppression,
            is_exact_zero=is_zero,
            pair_u=tuple(float(x) for x in u_sedenion),
            pair_omega=tuple(float(x) for x in omega_sedenion),
        )

    def check_boundary_normal_condition(
        self,
        u: np.ndarray,
        normal_idx: int = 1,
    ) -> tuple[float, float, bool]:
        """Check no-penetration (u . n = 0) and non-associative condition (u x_16 n = 0).

        Args:
            u: 16D sedenion velocity vector.
            normal_idx: Imaginary basis index of the normal vector (default e_1 = e_r).

        Returns:
            Tuple of (penetration_magnitude, cross_norm, satisfies_both).
        """
        n_vec = np.zeros(DIM_SEDENION, dtype=np.float64)
        n_vec[normal_idx] = 1.0

        penetration = float(abs(np.dot(u, n_vec)))
        cross = self.sedenion_cross_product(u, n_vec)
        cross_norm = float(np.linalg.norm(cross))

        satisfies = bool(penetration < 1e-12 and cross_norm < 1e-12)
        return penetration, cross_norm, satisfies
