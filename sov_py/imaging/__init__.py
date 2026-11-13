"""
Sedenion Imaging Module.

Provides mathematical image analysis algorithms:
- Multi-space Decorrelation Stretch (DStretch).
- Fano plane PG(2, F_2) octonionic 7D splitting and G_2 3-form calibrations.
- Optical wavefront curvature sensing and 3D surface/mesh reconstruction.
- Zernike polynomial modal aberration decomposition and optical alignment estimation.
- 16D Sedenion Zero-Divisor Annihilation Filtering and Ramanujan spectral analysis.
"""

from src.sedenion.imaging.decorrelation import (
    decorrelation_stretch_rgb,
    decorrelation_stretch_lab,
    decorrelation_stretch_generic,
)
from src.sedenion.imaging.fano_split import (
    compute_canonical_7d_field,
    fano_triad_split,
    compute_g2_calibration_form,
    compute_octonionic_associator_field,
)
from src.sedenion.imaging.wavefront_3d import (
    reconstruct_wavefront_phase,
    export_wavefront_to_ply,
    export_wavefront_to_obj,
    generate_interactive_3d_html,
)
from src.sedenion.imaging.zernike import (
    NOLL_ZERNIKE_MODES,
    zernike_polynomial,
    evaluate_zernike_basis,
    fit_zernike_aberrations,
)
from src.sedenion.imaging.sedenion_filter import (
    lift_to_sedenion_16d,
    sedenion_zero_divisor_filter,
    compute_zero_divisor_annihilation_spectrum,
    get_sedenion_left_mult_matrix,
)

__all__ = [
    "decorrelation_stretch_rgb",
    "decorrelation_stretch_lab",
    "decorrelation_stretch_generic",
    "compute_canonical_7d_field",
    "fano_triad_split",
    "compute_g2_calibration_form",
    "compute_octonionic_associator_field",
    "reconstruct_wavefront_phase",
    "export_wavefront_to_ply",
    "export_wavefront_to_obj",
    "generate_interactive_3d_html",
    "NOLL_ZERNIKE_MODES",
    "zernike_polynomial",
    "evaluate_zernike_basis",
    "fit_zernike_aberrations",
    "lift_to_sedenion_16d",
    "sedenion_zero_divisor_filter",
    "compute_zero_divisor_annihilation_spectrum",
    "get_sedenion_left_mult_matrix",
]
