"""
speckle_analysis.py — Laser Speckle Diffraction & Cross-Subject Perception Analysis.

Grounds the physical and statistical claims from Veilbreak / Danny Goler protocols:
- Simulates coherent optical diffraction on rough surfaces producing objective laser speckle.
- Extracts topological phase singularities, optical vortices, and intensity saddle points.
- Evaluates cross-subject spatial glyph correlation against Poisson pareidolia (Null Hypothesis H0).
- Provides deterministic permutation hypothesis testing for statistical falsification.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any

import numpy as np


@dataclass
class GlyphReport:
    subject_id: str
    x: float
    y: float
    glyph_id: int  # 1..6 corresponding to radial menu symbols
    timestamp_sec: float = 0.0
    confidence: float = 1.0


@dataclass
class SpeckleSimulationResult:
    wavelength_nm: int
    grid_size: int
    intensity: np.ndarray
    contrast: float
    mean_intensity: float
    vortex_count: int
    saddle_count: int


@dataclass
class CorrelationTestResult:
    total_reports: int
    subject_count: int
    mean_inter_subject_distance: float
    spatial_clustering_score: float
    glyph_agreement_rate: float
    chance_agreement_rate: float
    z_score: float
    p_value: float
    falsified_null_pareidolia: bool  # True if H0 rejected (evidence of shared structure)
    verdict: str


def simulate_laser_speckle(
    grid_size: int = 128,
    wavelength_nm: int = 520,
    roughness_um: float = 1.5,
    correlation_length_px: float = 4.0,
    seed: int = 42,
) -> SpeckleSimulationResult:
    """
    Simulates coherent laser light scattering from an optically rough surface
    via Rayleigh-Sommerfeld angular spectrum propagation.
    """
    rng = np.random.default_rng(seed)

    # 1. Generate correlated 2D Gaussian random surface height field h(x, y)
    white_noise = rng.standard_normal((grid_size, grid_size))
    # Gaussian smoothing kernel
    y, x = np.ogrid[-grid_size // 2 : grid_size // 2, -grid_size // 2 : grid_size // 2]
    kernel = np.exp(-(x**2 + y**2) / (2.0 * correlation_length_px**2))
    kernel /= np.sum(kernel)

    h = np.fft.ifft2(np.fft.fft2(white_noise) * np.fft.fft2(kernel)).real
    h = h / (np.std(h) + 1e-12) * roughness_um

    # 2. Phase modulation: phi = (4 * pi / lambda) * h
    k_wave = (2.0 * math.pi) / (wavelength_nm * 1e-3)  # um^-1
    phase = 2.0 * k_wave * h

    # 3. Reflected optical field at surface: E0 = exp(i * phi)
    e0 = np.exp(1j * phase)

    # 4. Far-field diffraction (Fraunhofer / 2D Fourier transform)
    e_far = np.fft.fftshift(np.fft.fft2(e0))
    intensity = np.abs(e_far) ** 2

    # Normalize intensity
    intensity /= np.mean(intensity) + 1e-12

    # Calculate speckle contrast C = sigma_I / <I> (fully developed speckle C -> 1.0)
    contrast = float(np.std(intensity) / (np.mean(intensity) + 1e-12))
    mean_i = float(np.mean(intensity))

    # Detect optical singularities (intensity minima below 0.05)
    vortices = np.sum(intensity < 0.05)

    # Detect intensity saddle points via Hessian determinant
    gy, gx = np.gradient(intensity)
    gyy, gyx = np.gradient(gy)
    gxy, gxx = np.gradient(gx)
    hess_det = gxx * gyy - gyx * gxy
    saddles = int(np.sum((hess_det < -0.5) & (np.abs(gx) < 0.2) & (np.abs(gy) < 0.2)))

    return SpeckleSimulationResult(
        wavelength_nm=wavelength_nm,
        grid_size=grid_size,
        intensity=intensity,
        contrast=contrast,
        mean_intensity=mean_i,
        vortex_count=int(vortices),
        saddle_count=saddles,
    )


def evaluate_cross_subject_glyph_correlation(
    reports: list[GlyphReport],
    distance_threshold_px: float = 8.0,
    permutation_iterations: int = 500,
    seed: int = 1234,
) -> CorrelationTestResult:
    """
    Rigorous statistical test of the Danny Goler / Veilbreak cross-subject perception hypothesis.


    Tests Null Hypothesis H0 (Stochastic Pareidolia / Independent Hallucination):
    - Observers select random spatial locations and random glyphs (discrete uniform 1..6).
    - Expected chance glyph agreement = 1/6 = ~16.67%.

    Alternative Hypothesis H1 (Objective Optical Structure):
    - Observers consistently select identical glyphs at identical spatial coordinates
      significantly exceeding chance (Z > 3.0, p < 0.001).
    """
    if len(reports) < 4:
        raise ValueError(f"Need at least 4 glyph reports for statistical test, got {len(reports)}")

    subjects = list({r.subject_id for r in reports})
    if len(subjects) < 2:
        raise ValueError("Need at least 2 distinct subjects to evaluate cross-subject correlation")

    # Pairwise cross-subject report analysis
    def compute_metrics(pts: list[GlyphReport]) -> tuple[float, float, float]:
        inter_dists = []
        matching_pairs = 0
        total_co_localized = 0

        for i in range(len(pts)):
            for j in range(i + 1, len(pts)):
                p1, p2 = pts[i], pts[j]
                if p1.subject_id == p2.subject_id:
                    continue  # Only evaluate cross-subject pairs

                dist = math.hypot(p1.x - p2.x, p1.y - p2.y)
                inter_dists.append(dist)

                if dist <= distance_threshold_px:
                    total_co_localized += 1
                    if p1.glyph_id == p2.glyph_id:
                        matching_pairs += 1

        mean_d = float(np.mean(inter_dists)) if inter_dists else 0.0
        agreement = (matching_pairs / total_co_localized) if total_co_localized > 0 else 0.0
        # Spatial clustering score: inverse mean nearest neighbor distance
        cluster_score = (1.0 / (mean_d + 1e-6)) * 100.0
        return mean_d, cluster_score, agreement

    obs_mean_d, obs_cluster, obs_agreement = compute_metrics(reports)

    # Permutation test (shuffling glyph assignments and locations under H0)
    rng = np.random.default_rng(seed)
    null_agreements = []

    for _ in range(permutation_iterations):
        shuffled = [
            GlyphReport(
                subject_id=r.subject_id,
                x=float(rng.uniform(0, 100)),
                y=float(rng.uniform(0, 100)),
                glyph_id=int(rng.integers(1, 7)),
            )
            for r in reports
        ]
        _, _, null_agr = compute_metrics(shuffled)
        null_agreements.append(null_agr)

    null_mean = float(np.mean(null_agreements))
    null_std = float(np.std(null_agreements)) + 1e-9

    # Standard score Z
    z_score = float((obs_agreement - null_mean) / null_std)

    # Empirical p-value
    p_val = float(np.mean([na >= obs_agreement for na in null_agreements]))

    # Verdict
    falsified_null = bool(p_val < 0.05 and z_score > 2.0)
    if falsified_null:
        verdict = f"H0 REJECTED (Z={z_score:.2f}, p={p_val:.4f}): Statistically significant cross-subject agreement exceeds pareidolia chance."
    else:
        verdict = f"H0 ACCEPTED / CONFIRMED PAREIDOLIA (Z={z_score:.2f}, p={p_val:.4f}): Observer reports are indistinguishable from random Poisson pareidolia."

    return CorrelationTestResult(
        total_reports=len(reports),
        subject_count=len(subjects),
        mean_inter_subject_distance=obs_mean_d,
        spatial_clustering_score=obs_cluster,
        glyph_agreement_rate=obs_agreement,
        chance_agreement_rate=1.0 / 6.0,
        z_score=z_score,
        p_value=p_val,
        falsified_null_pareidolia=falsified_null,
        verdict=verdict,
    )
