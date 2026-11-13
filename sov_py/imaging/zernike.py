"""
Zernike Polynomial Modal Wavefront Aberration Decomposition.

Implements standard Noll / Fringe Zernike polynomials on circular and annular pupils,
least-squares modal fitting, and optical alignment offset estimation (defocus, astigmatism,
coma, spherical aberration).
"""

from __future__ import annotations

import math
import cv2
import numpy as np


# Standard Noll index mapping: (n, m, name)
NOLL_ZERNIKE_MODES: list[tuple[int, int, str]] = [
    (0, 0, "Z1: Piston"),
    (1, 1, "Z2: Tip (X-tilt)"),
    (1, -1, "Z3: Tilt (Y-tilt)"),
    (2, 0, "Z4: Defocus"),
    (2, -2, "Z5: Astigmatism 45 deg"),
    (2, 2, "Z6: Astigmatism 0/90 deg"),
    (3, -1, "Z7: Coma Y"),
    (3, 1, "Z8: Coma X"),
    (3, -3, "Z9: Trefoil Y"),
    (3, 3, "Z10: Trefoil X"),
    (4, 0, "Z11: Primary Spherical"),
    (4, 2, "Z12: Secondary Astigmatism 0/90"),
    (4, -2, "Z13: Secondary Astigmatism 45"),
    (4, 4, "Z14: Quadrafoil X"),
    (4, -4, "Z15: Quadrafoil Y"),
]


def zernike_radial(n: int, m: int, rho: np.ndarray) -> np.ndarray:
    """Compute the radial polynomial R_n^{|m|}(rho)."""
    m_abs = abs(m)
    if (n - m_abs) % 2 != 0:
        return np.zeros_like(rho)

    R = np.zeros_like(rho, dtype=np.float64)
    for s in range((n - m_abs) // 2 + 1):
        num = ((-1) ** s) * math.factorial(n - s)
        den = (
            math.factorial(s)
            * math.factorial((n + m_abs) // 2 - s)
            * math.factorial((n - m_abs) // 2 - s)
        )
        coeff = num / den
        R += coeff * (rho ** (n - 2 * s))
    return R


def zernike_polynomial(n: int, m: int, rho: np.ndarray, theta: np.ndarray) -> np.ndarray:
    """Compute the Noll-normalized Zernike polynomial Z_n^m(rho, theta)."""
    R = zernike_radial(n, m, rho)
    m_abs = abs(m)

    # Noll normalization factor
    if m == 0:
        norm = math.sqrt(n + 1)
        return norm * R
    else:
        norm = math.sqrt(2 * (n + 1))
        if m > 0:
            return norm * R * np.cos(m_abs * theta)
        else:
            return norm * R * np.sin(m_abs * theta)


def evaluate_zernike_basis(
    rho: np.ndarray,
    theta: np.ndarray,
    mask: np.ndarray,
    num_modes: int = 15,
) -> tuple[np.ndarray, list[str]]:
    """Evaluate the Zernike basis matrix A of shape (N_pixels, num_modes) over masked pixels."""
    n_modes = min(num_modes, len(NOLL_ZERNIKE_MODES))
    rho_m = rho[mask]
    theta_m = theta[mask]
    n_pts = len(rho_m)

    A = np.zeros((n_pts, n_modes), dtype=np.float64)
    names = []

    for j in range(n_modes):
        n, m, name = NOLL_ZERNIKE_MODES[j]
        A[:, j] = zernike_polynomial(n, m, rho_m, theta_m)
        names.append(name)

    return A, names


def fit_zernike_aberrations(
    wavefront_phase: np.ndarray,
    center: tuple[float, float] | None = None,
    radius: float | None = None,
    num_modes: int = 15,
    central_obscuration: float = 0.0,
) -> dict:
    """Fit Zernike polynomials to a 2D wavefront phase surface.

    Parameters
    ----------
    wavefront_phase : np.ndarray
        2D array of recovered optical wavefront phase (H, W).
    center : tuple[float, float] | None
        (cx, cy) pupil center. If None, uses image center.
    radius : float | None
        Pupil radius in pixels. If None, uses min(H, W) / 2.
    num_modes : int
        Number of Zernike modes to fit (up to 15).
    central_obscuration : float
        Inner radius ratio epsilon in [0, 1) for Cassegrain secondary mirror.

    Returns
    -------
    dict
        Dictionary with fitted coefficients, names, synthesized wavefront,
        residual wavefront, and optical alignment metrics.
    """
    h, w = wavefront_phase.shape
    if center is None:
        cx, cy = w / 2.0, h / 2.0
    else:
        cx, cy = center

    if radius is None:
        radius = min(h, w) / 2.0 - 2.0

    ys, xs = np.mgrid[:h, :w]
    x_norm = (xs - cx) / radius
    y_norm = (ys - cy) / radius

    rho = np.sqrt(x_norm**2 + y_norm**2)
    theta = np.arctan2(y_norm, x_norm)

    # Pupil mask
    pupil_mask = (rho <= 1.0) & (rho >= central_obscuration)
    if not np.any(pupil_mask):
        raise ValueError("Pupil mask is empty. Check center, radius, and central_obscuration.")

    # Evaluate basis
    A, names = evaluate_zernike_basis(rho, theta, pupil_mask, num_modes=num_modes)
    b = wavefront_phase[pupil_mask].astype(np.float64)

    # Solve least-squares: A * c = b
    coeffs, residuals, rank, s = np.linalg.lstsq(A, b, rcond=None)

    # Synthesize fitted wavefront on the full grid
    fitted_wavefront = np.zeros((h, w), dtype=np.float64)
    for j in range(len(coeffs)):
        n, m, _ = NOLL_ZERNIKE_MODES[j]
        Z_full = zernike_polynomial(n, m, rho, theta)
        fitted_wavefront += coeffs[j] * Z_full

    fitted_wavefront[~pupil_mask] = np.nan

    # Residual wavefront
    residual = np.zeros((h, w), dtype=np.float64)
    residual[pupil_mask] = wavefront_phase[pupil_mask] - fitted_wavefront[pupil_mask]
    residual[~pupil_mask] = np.nan

    # RMS wavefront error (excluding piston Z1)
    aberration_coeffs = coeffs[1:]  # Exclude piston
    rms_wfe = float(np.sqrt(np.mean(aberration_coeffs**2)))
    peak_to_valley = float(np.nanmax(fitted_wavefront) - np.nanmin(fitted_wavefront))

    # Identify dominant aberrations
    modes_summary = []
    for j in range(len(coeffs)):
        modes_summary.append({
            "index": j + 1,
            "name": names[j],
            "coefficient": float(coeffs[j]),
            "abs_weight": float(abs(coeffs[j])),
        })

    # Optical alignment estimation:
    # Roman Telescope specs: Primary D = 2.4 m, F/# = 7.8, f = 18.72 m
    # Defocus coefficient Z4 (n=2, m=0) is proportional to axial secondary mirror despace delta_z
    defocus_coeff = float(coeffs[3]) if len(coeffs) > 3 else 0.0
    astig_x = float(coeffs[5]) if len(coeffs) > 5 else 0.0
    astig_y = float(coeffs[4]) if len(coeffs) > 4 else 0.0
    coma_x = float(coeffs[7]) if len(coeffs) > 7 else 0.0
    coma_y = float(coeffs[6]) if len(coeffs) > 6 else 0.0
    spherical = float(coeffs[10]) if len(coeffs) > 10 else 0.0

    return {
        "coefficients": coeffs.tolist(),
        "names": names,
        "modes_summary": modes_summary,
        "rms_wavefront_error": rms_wfe,
        "peak_to_valley": peak_to_valley,
        "fitted_wavefront": fitted_wavefront,
        "residual_wavefront": residual,
        "pupil_mask": pupil_mask,
        "alignment_metrics": {
            "defocus_z4": defocus_coeff,
            "astigmatism_magnitude": float(math.hypot(astig_x, astig_y)),
            "astigmatism_angle_deg": float(math.degrees(0.5 * math.atan2(astig_y, astig_x))),
            "coma_magnitude": float(math.hypot(coma_x, coma_y)),
            "coma_angle_deg": float(math.degrees(math.atan2(coma_y, coma_x))),
            "spherical_z11": spherical,
        },
    }
