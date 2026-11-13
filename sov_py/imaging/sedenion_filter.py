"""
16D Sedenion Zero-Divisor Annihilation Filter Engine.

Lifts multi-spectral and optical fields into the 16-dimensional sedenion algebra S = R^16,
evaluates non-associative zero-divisor interactions across the 168 cross-octet zero divisors,
and performs algebraic noise suppression via the 8-regular Ramanujan expander graph C_6[4].
"""

from __future__ import annotations

import cv2
import numpy as np

from src.sedenion.fast_algebra import SEDENION_SIGN_TABLE
from src.sedenion.graph import AnnihilationGraph


OMEGA = np.array(SEDENION_SIGN_TABLE, dtype=np.float64)


def get_sedenion_left_mult_matrix(u_vec: np.ndarray) -> np.ndarray:
    """Compute the 16x16 left-multiplication matrix L_u such that L_u * x = u * x."""
    M = np.zeros((16, 16), dtype=np.float64)
    for j in range(16):
        for i in range(16):
            k = i ^ j
            M[k, j] += OMEGA[i, j] * u_vec[i]
    return M


# Cache precomputed normalized zero divisors and their left multiplication matrices
_GRAPH_CACHE: AnnihilationGraph | None = None
_ZD_MATRICES: list[np.ndarray] | None = None
_ZD_VECTORS: np.ndarray | None = None


def _get_zd_cache() -> tuple[AnnihilationGraph, list[np.ndarray], np.ndarray]:
    global _GRAPH_CACHE, _ZD_MATRICES, _ZD_VECTORS
    if _GRAPH_CACHE is None or _ZD_MATRICES is None or _ZD_VECTORS is None:
        _GRAPH_CACHE = AnnihilationGraph()
        mats = []
        vecs = np.zeros((168, 16), dtype=np.float64)
        for idx in range(168):
            zd = _GRAPH_CACHE.id_to_zd[idx]
            u = np.zeros(16, dtype=np.float64)
            u[zd.i] = zd.s1
            u[8 + zd.j] = zd.s2
            u /= np.linalg.norm(u)
            vecs[idx] = u
            mats.append(get_sedenion_left_mult_matrix(u))
        _ZD_MATRICES = mats
        _ZD_VECTORS = vecs
    return _GRAPH_CACHE, _ZD_MATRICES, _ZD_VECTORS


def lift_to_sedenion_16d(
    img_rgb: np.ndarray,
    extra_channels: list[np.ndarray] | None = None,
) -> np.ndarray:
    """Lift an image to a canonical 16-dimensional sedenion field S(x, y) in R^16.

    Parameters
    ----------
    img_rgb : np.ndarray
        Array of shape (H, W, 3) in RGB format.
    extra_channels : list[np.ndarray] | None
        Optional additional physical channels (e.g. multi-wavelength bands).

    Returns
    -------
    np.ndarray
        Standardized 16-channel array of shape (H, W, 16).
    """
    if img_rgb.ndim != 3 or img_rgb.shape[2] != 3:
        raise ValueError(f"Expected shape (H, W, 3), got {img_rgb.shape}")

    h, w, _ = img_rgb.shape
    img_f = img_rgb.astype(np.float64) / 255.0
    r, g, b = img_f[:, :, 0], img_f[:, :, 1], img_f[:, :, 2]

    # --- Octet 0 (e0..e7): Physical continuum & primary derivatives ---
    # e0: Base continuum intensity (Luminance)
    L = 0.299 * r + 0.587 * g + 0.114 * b

    # e1, e2: Chrominance opponents
    c1 = r - g
    c2 = b - 0.5 * (r + g)

    # e3, e4: First-order spatial gradients
    gx = cv2.Sobel(L, cv2.CV_64F, 1, 0, ksize=3)
    gy = cv2.Sobel(L, cv2.CV_64F, 0, 1, ksize=3)

    # e5: Curvature / Laplacian
    lap = cv2.Laplacian(L, cv2.CV_64F, ksize=3)

    # e6: High-pass annular texture
    blur_fine = cv2.GaussianBlur(L, (7, 7), 1.5)
    tex = L - blur_fine

    # e7: Spatial divergence / shear
    div = cv2.Sobel(c1, cv2.CV_64F, 1, 0, ksize=3) + cv2.Sobel(c2, cv2.CV_64F, 0, 1, ksize=3)

    # --- Octet 1 (e8..e15): Multi-scale, Hessian, and topological observables ---
    # e8: Coarse-scale multi-scale continuum (second octave)
    blur_coarse = cv2.GaussianBlur(L, (21, 21), 5.0)

    # e9, e10: Hessian diagonal components
    gxx = cv2.Sobel(gx, cv2.CV_64F, 1, 0, ksize=3)
    gyy = cv2.Sobel(gy, cv2.CV_64F, 0, 1, ksize=3)

    # e11: Cross-Hessian component
    gxy = cv2.Sobel(gx, cv2.CV_64F, 0, 1, ksize=3)

    # e12, e13: Directional diagonal and anti-diagonal shears
    shear_diag = (gx + gy) / np.sqrt(2.0)
    shear_antidiag = (gx - gy) / np.sqrt(2.0)

    # e14: TIE phase proxy
    phase = cv2.GaussianBlur(lap, (15, 15), 3.0)

    # e15: High-frequency residual
    hf_res = L - blur_coarse

    raw_channels = [
        L, c1, c2, gx, gy, lap, tex, div,
        blur_coarse, gxx, gyy, gxy, shear_diag, shear_antidiag, phase, hf_res,
    ]

    # If extra channels provided, replace tail channels
    if extra_channels:
        for idx, ch in enumerate(extra_channels[:8]):
            if ch.shape == (h, w):
                raw_channels[8 + idx] = ch.astype(np.float64)

    norm_channels = []
    for ch in raw_channels:
        m = np.mean(ch)
        s = np.std(ch)
        if s > 1e-8:
            norm_channels.append((ch - m) / s)
        else:
            norm_channels.append(ch - m)

    return np.stack(norm_channels, axis=-1)


def sedenion_zero_divisor_filter(
    field_16d: np.ndarray,
    num_iterations: int = 3,
    dt: float = 0.25,
    sigma_spatial: float = 1.2,
    annihilation_threshold: float = 0.35,
) -> np.ndarray:
    """Filter non-associative zero-divisor noise across the 16D sedenion field.

    Applies algebraic diffusion where weight between neighboring pixels is modulated
    by whether their difference contains zero-divisor annihilation modes:
    - Pure noise differences trigger mutual annihilation (u * Delta S = 0), yielding high diffusion weights.
    - True physical edges and filaments have non-zero products (||u * Delta S|| > 0), preserving sharpness.
    """
    h, w, c = field_16d.shape
    if c != 16:
        raise ValueError(f"Expected 16 channels, got {c}")

    _, zd_mats, _ = _get_zd_cache()
    # Sample a representative subset of zero divisors for rapid vectorized evaluation (e.g. 14 basis ZDs, 2 per component)
    sampled_indices = [0, 12, 24, 36, 48, 60, 72, 84, 96, 108, 120, 132, 144, 156]
    active_mats = [zd_mats[i] for i in sampled_indices]

    current = field_16d.copy()

    # Spatial neighbor offsets (4-connectivity)
    neighbors = [(-1, 0), (1, 0), (0, -1), (0, 1)]

    for _ in range(num_iterations):
        diff_accum = np.zeros_like(current)
        weight_accum = np.zeros((h, w, 1), dtype=np.float64)

        for dy, dx in neighbors:
            # Shifted neighbor array
            shifted = np.roll(np.roll(current, dy, axis=0), dx, axis=1)
            delta = shifted - current

            # Metric distance in R^16
            delta_sq = np.sum(delta ** 2, axis=-1, keepdims=True)

            # Sedenion zero-divisor annihilation penalty
            # Flatten delta to (H*W, 16)
            flat_delta = delta.reshape(-1, 16)
            min_zd_norm_sq = np.full(flat_delta.shape[0], np.inf, dtype=np.float64)

            for Lu in active_mats:
                prod = np.dot(flat_delta, Lu.T)
                prod_sq = np.sum(prod ** 2, axis=-1)
                min_zd_norm_sq = np.minimum(min_zd_norm_sq, prod_sq)

            min_zd_norm_sq = min_zd_norm_sq.reshape(h, w, 1)

            # Weight function:
            # If min_zd_norm_sq is near 0, delta lies in a zero-divisor kernel (noise) -> smooth it (high weight)
            # If min_zd_norm_sq is large, delta is an associative physical edge -> preserve it (low weight)
            is_noise = np.exp(-min_zd_norm_sq / (2.0 * annihilation_threshold**2))
            spatial_decay = np.exp(-delta_sq / (2.0 * sigma_spatial**2))
            weight = spatial_decay * (0.3 + 0.7 * is_noise)

            diff_accum += weight * delta
            weight_accum += weight

        weight_accum = np.maximum(weight_accum, 1e-6)
        current += dt * (diff_accum / weight_accum)

    return current


def compute_zero_divisor_annihilation_spectrum(field_16d: np.ndarray) -> dict:
    """Evaluate energy and SNR metrics across the 7 XOR charge sectors chi in {1..7}."""
    h, w, c = field_16d.shape
    if c != 16:
        raise ValueError(f"Expected 16 channels, got {c}")

    graph, zd_mats, _ = _get_zd_cache()
    comps = list(graph.connected_components())

    total_energy = float(np.sum(field_16d ** 2))
    sector_energies = {}

    flat_field = field_16d.reshape(-1, 16)

    for idx, comp in enumerate(comps):
        chi = graph.id_to_zd[list(comp)[0]].chi
        # Sample 4 zero divisors per component
        sample_zd_ids = list(comp)[:4]
        comp_energy = 0.0
        for zid in sample_zd_ids:
            Lu = zd_mats[zid]
            prod = np.dot(flat_field, Lu.T)
            comp_energy += float(np.sum(prod ** 2))
        sector_energies[f"chi_{chi}"] = comp_energy / len(sample_zd_ids)

    # Estimate SNR improvement proxy
    mean_val = float(np.mean(field_16d))
    std_val = float(np.std(field_16d))
    snr_db = float(20.0 * np.log10(abs(mean_val) / (std_val + 1e-8))) if abs(mean_val) > 1e-8 else 0.0

    return {
        "total_energy": total_energy,
        "sector_energies": sector_energies,
        "mean": mean_val,
        "std": std_val,
        "snr_db": snr_db,
    }
