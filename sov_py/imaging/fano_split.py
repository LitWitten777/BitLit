"""
Fano Plane PG(2, F_2) and Octonionic 7D Image Splitting.

Decomposes optical and multispectral images into canonical 7D fields in R^7 = Im(O),
projects them onto the 7 associative quaternion subalgebras H_k (Fano lines),
and evaluates G_2 3-form calibrations and non-associative associator fields.
"""

from __future__ import annotations

import cv2
import numpy as np

from src.sedenion.fano import FANO_LINES
from src.sedenion.imaging.decorrelation import decorrelation_stretch_generic

# Canonical channel names
CHANNEL_NAMES: list[str] = [
    "Luminance (L)",
    "Chrominance C1 (R-G)",
    "Chrominance C2 (B-(R+G)/2)",
    "Horizontal Gradient (gx)",
    "Vertical Gradient (gy)",
    "Curvature / Laplacian (lap)",
    "Texture / High-pass (tex)",
]

# Standard cyclic presentation of Fano triads as ordered tuples
ORDERED_FANO_TRIADS: list[tuple[int, int, int]] = [
    (0, 1, 3),  # Triad 0: L, C1, gx
    (1, 2, 4),  # Triad 1: C1, C2, gy
    (2, 3, 5),  # Triad 2: C2, gx, lap
    (3, 4, 6),  # Triad 3: gx, gy, tex (Pure optical wavefront geometry)
    (4, 5, 0),  # Triad 4: gy, lap, L
    (5, 6, 1),  # Triad 5: lap, tex, C1
    (6, 0, 2),  # Triad 6: tex, L, C2
]


def compute_canonical_7d_field(img_rgb: np.ndarray) -> np.ndarray:
    """Map an RGB image into a canonical 7-dimensional normalized feature field.

    Parameters
    ----------
    img_rgb : np.ndarray
        Array of shape (H, W, 3) in RGB format.

    Returns
    -------
    np.ndarray
        Array of shape (H, W, 7), standardized to zero-mean and unit-variance.
    """
    if img_rgb.ndim != 3 or img_rgb.shape[2] != 3:
        raise ValueError(f"Expected shape (H, W, 3), got {img_rgb.shape}")

    img_f = img_rgb.astype(np.float64) / 255.0
    r, g, b = img_f[:, :, 0], img_f[:, :, 1], img_f[:, :, 2]

    # 0: Luminance L
    L = 0.299 * r + 0.587 * g + 0.114 * b

    # 1: Chrominance C1 (Red - Green opponent)
    c1 = r - g

    # 2: Chrominance C2 (Blue - Yellow opponent)
    c2 = b - 0.5 * (r + g)

    # 3: Horizontal gradient gx
    gx = cv2.Sobel(L, cv2.CV_64F, 1, 0, ksize=3)

    # 4: Vertical gradient gy
    gy = cv2.Sobel(L, cv2.CV_64F, 0, 1, ksize=3)

    # 5: Curvature / Laplacian (Roddier wavefront curvature sensing)
    lap = cv2.Laplacian(L, cv2.CV_64F, ksize=3)

    # 6: High-frequency texture / annular phase residual
    blur = cv2.GaussianBlur(L, (9, 9), 2.0)
    tex = L - blur

    raw_channels = [L, c1, c2, gx, gy, lap, tex]
    norm_channels = []
    for ch in raw_channels:
        m = np.mean(ch)
        s = np.std(ch)
        if s > 1e-8:
            norm_channels.append((ch - m) / s)
        else:
            norm_channels.append(ch - m)

    return np.stack(norm_channels, axis=-1)


def fano_triad_split(
    field_7d: np.ndarray,
    lower_percentile: float = 1.5,
    upper_percentile: float = 98.5,
) -> dict[int, dict]:
    """Project the 7D field onto the 7 associative Fano triads and decorrelate each.

    Returns a dictionary mapping triad index k -> {
        "triad": (a, b, c),
        "names": (name_a, name_b, name_c),
        "rgb": decorrelation-stretched RGB image (H, W, 3) uint8,
        "energy": total variance in this associative subalgebra,
    }
    """
    h, w, c = field_7d.shape
    if c != 7:
        raise ValueError(f"Expected 7 channels, got {c}")

    results = {}
    for k, triad in enumerate(ORDERED_FANO_TRIADS):
        a, b, c_idx = triad
        sub = field_7d[:, :, [a, b, c_idx]]

        # Decorrelate the 3-dimensional subspace
        stretched = decorrelation_stretch_generic(
            sub,
            lower_percentile=lower_percentile,
            upper_percentile=upper_percentile,
        )

        sub_energy = float(np.sum(np.var(sub, axis=(0, 1))))
        results[k] = {
            "triad": triad,
            "names": (CHANNEL_NAMES[a], CHANNEL_NAMES[b], CHANNEL_NAMES[c_idx]),
            "rgb": stretched,
            "energy": sub_energy,
        }

    return results


def compute_g2_calibration_form(field_7d: np.ndarray) -> np.ndarray:
    """Evaluate the G_2 associative calibration 3-form across the 7 Fano triads.

    Phi(x, y) = sum_{(a, b, c) in Fano} v_a(x, y) * v_b(x, y) * v_c(x, y)
    """
    h, w, c = field_7d.shape
    if c != 7:
        raise ValueError(f"Expected 7 channels, got {c}")

    phi = np.zeros((h, w), dtype=np.float64)
    for a, b, c_idx in ORDERED_FANO_TRIADS:
        phi += field_7d[:, :, a] * field_7d[:, :, b] * field_7d[:, :, c_idx]
    return phi


def compute_octonionic_associator_field(
    field_7d: np.ndarray,
    stride: int = 1,
) -> np.ndarray:
    """Compute the non-associative associator field norm over non-Fano triples.

    For three imaginary octonionic basis elements e_i, e_j, e_k:
    - If {i, j, k} is a Fano line: [e_i, e_j, e_k] = 0.
    - If {i, j, k} is not a Fano line: [e_i, e_j, e_k] = 2 e_l.

    The associator field detects optical phase singularities, cosmic rays, and wavefront dislocations.
    """
    h, w, c = field_7d.shape
    if c != 7:
        raise ValueError(f"Expected 7 channels, got {c}")

    if stride > 1:
        f = field_7d[::stride, ::stride]
    else:
        f = field_7d

    # There are 7 Fano lines out of 35 total triples in C(7, 3).
    # The remaining 28 triples are non-associative.
    # We evaluate the anti-associative coupling:
    line_sets = [frozenset(t) for t in ORDERED_FANO_TRIADS]
    associator_norm = np.zeros((f.shape[0], f.shape[1]), dtype=np.float64)

    import itertools
    for triple in itertools.combinations(range(7), 3):
        if frozenset(triple) not in line_sets:
            i, j, k = triple
            # Weight by cross product interaction
            prod = f[:, :, i] * f[:, :, j] * f[:, :, k]
            associator_norm += prod ** 2

    associator_map = np.sqrt(associator_norm)

    if stride > 1:
        associator_map = cv2.resize(associator_map, (w, h), interpolation=cv2.INTER_LINEAR)

    return associator_map
