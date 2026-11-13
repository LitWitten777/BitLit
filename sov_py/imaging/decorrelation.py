"""
Multi-space Decorrelation Stretch (DStretch).

Implements Karhunen-Loeve / PCA-based decorrelation stretch across arbitrary
spectral and spatial channels, as well as specialized RGB and LAB color transforms.
"""

from __future__ import annotations

import cv2
import numpy as np


def decorrelation_stretch_generic(
    data: np.ndarray,
    lower_percentile: float = 1.0,
    upper_percentile: float = 99.0,
    target_mean: float = 127.5,
    target_std: float = 50.0,
) -> np.ndarray:
    """Apply decorrelation stretch to an image with C channels.

    Parameters
    ----------
    data : np.ndarray
        Array of shape (H, W, C) with arbitrary number of channels C >= 2.
    lower_percentile : float
        Lower percentile cutoff for contrast stretching.
    upper_percentile : float
        Upper percentile cutoff for contrast stretching.
    target_mean : float
        Target mean value for the stretched output.
    target_std : float
        Target standard deviation along each principal component.

    Returns
    -------
    np.ndarray
        Decorrelation-stretched array of shape (H, W, C), uint8 in [0, 255].
    """
    if data.ndim != 3:
        raise ValueError(f"Expected 3D array (H, W, C), got ndim={data.ndim}")
    h, w, c = data.shape
    if c < 2:
        raise ValueError(f"Need at least 2 channels for decorrelation stretch, got {c}")

    flat = data.reshape(-1, c).astype(np.float64)
    mu = np.mean(flat, axis=0)
    centered = flat - mu

    # Covariance matrix (C x C)
    cov = np.cov(centered, rowvar=False)
    if cov.ndim == 0:
        cov = np.array([[cov]])

    # Eigendecomposition of symmetric positive semi-definite covariance
    evals, evecs = np.linalg.eigh(cov)

    # Sort eigenvalues in descending order
    idx = np.argsort(evals)[::-1]
    evals = np.maximum(evals[idx], 1e-12)
    evecs = evecs[:, idx]

    # Project to principal components
    pc = np.dot(centered, evecs)  # Shape: (N, C)

    # Scale each principal component to target standard deviation
    std = np.std(pc, axis=0)
    std = np.where(std < 1e-8, 1.0, std)
    pc_scaled = (pc / std) * target_std

    # Rotate back to original coordinate basis
    reconstructed = np.dot(pc_scaled, evecs.T) + target_mean

    # Percentile contrast stretch per channel
    out = np.zeros_like(reconstructed)
    for i in range(c):
        p_low = np.percentile(reconstructed[:, i], lower_percentile)
        p_high = np.percentile(reconstructed[:, i], upper_percentile)
        if p_high - p_low > 1e-6:
            out[:, i] = np.clip((reconstructed[:, i] - p_low) / (p_high - p_low) * 255.0, 0, 255)
        else:
            out[:, i] = np.clip(reconstructed[:, i], 0, 255)

    return out.reshape(h, w, c).astype(np.uint8)


def decorrelation_stretch_rgb(
    img_rgb: np.ndarray,
    lower_percentile: float = 1.0,
    upper_percentile: float = 99.0,
) -> np.ndarray:
    """Apply standard RGB decorrelation stretch."""
    if img_rgb.ndim != 3 or img_rgb.shape[2] != 3:
        raise ValueError("img_rgb must have shape (H, W, 3)")
    return decorrelation_stretch_generic(
        img_rgb,
        lower_percentile=lower_percentile,
        upper_percentile=upper_percentile,
    )


def decorrelation_stretch_lab(
    img_rgb: np.ndarray,
    lower_percentile: float = 1.0,
    upper_percentile: float = 99.0,
) -> np.ndarray:
    """Apply decorrelation stretch in CIELAB color space.

    Decorrelates chromatic channels (a, b) while preserving/enhancing lightness L.
    """
    if img_rgb.ndim != 3 or img_rgb.shape[2] != 3:
        raise ValueError("img_rgb must have shape (H, W, 3)")

    # Convert RGB to LAB via OpenCV (expects BGR or RGB)
    lab = cv2.cvtColor(img_rgb, cv2.COLOR_RGB2LAB).astype(np.float64)
    h, w, _ = lab.shape

    # Apply DStretch to the full 3 channels of LAB
    stretched_lab = decorrelation_stretch_generic(
        lab,
        lower_percentile=lower_percentile,
        upper_percentile=upper_percentile,
    )

    # Convert back to RGB
    res_rgb = cv2.cvtColor(stretched_lab, cv2.COLOR_LAB2RGB)
    return res_rgb


def decorrelation_stretch_local(
    img: np.ndarray,
    tile_size: int = 256,
    overlap: int = 64,
) -> np.ndarray:
    """Apply block-based local decorrelation stretch for faint extended features."""
    h, w, c = img.shape
    step = tile_size - overlap
    weight_map = np.zeros((h, w), dtype=np.float32)
    output_accum = np.zeros((h, w, c), dtype=np.float32)

    # 2D Hanning window for smooth cross-blending between tiles
    wy = np.hanning(tile_size)
    wx = np.hanning(tile_size)
    window = np.outer(wy, wx)

    for y0 in range(0, h, step):
        y1 = min(y0 + tile_size, h)
        actual_th = y1 - y0
        for x0 in range(0, w, step):
            x1 = min(x0 + tile_size, w)
            actual_tw = x1 - x0

            sub = img[y0:y1, x0:x1]
            if np.std(sub) < 1e-4:
                stretched_sub = sub
            else:
                stretched_sub = decorrelation_stretch_generic(sub)

            win_crop = window[:actual_th, :actual_tw]
            for ch in range(c):
                output_accum[y0:y1, x0:x1, ch] += stretched_sub[:, :, ch] * win_crop
            weight_map[y0:y1, x0:x1] += win_crop

    weight_map = np.maximum(weight_map, 1e-6)
    for ch in range(c):
        output_accum[:, :, ch] /= weight_map

    return np.clip(output_accum, 0, 255).astype(np.uint8)
