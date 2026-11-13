"""
src/sedenion/geometry
=============================================================================
Differential and Hyperbolic Geometry for Sedenion and Poincare Memory Manifolds.
=============================================================================
"""

from .poincare_memory import PoincareMemoryManifold, SephirotNode
from .hopf_lift import HopfFibration, BulkBoundaryExtension, HopfBundleChart
from .hodge_cycle_varieties import (
    HodgeDiamond,
    AlgebraicCycle,
    HodgeClass,
    ComplexVarietyHodgeTheory,
)
from .stiefel_spectrum import (
    StiefelSpectrumEngine,
    SpectralLevel,
    octonion_cross_product,
)
from .tower_stiefel import TowerStiefelEngine
from .orthogonal_frame_field import OrthogonalFrameField
from .projective_pencil import ProjectivePencilFibration, ProjectivePencilMetrics

__all__ = [
    "PoincareMemoryManifold",
    "SephirotNode",
    "HopfFibration",
    "BulkBoundaryExtension",
    "HopfBundleChart",
    "HodgeDiamond",
    "AlgebraicCycle",
    "HodgeClass",
    "ComplexVarietyHodgeTheory",
    "StiefelSpectrumEngine",
    "SpectralLevel",
    "octonion_cross_product",
    "TowerStiefelEngine",
    "OrthogonalFrameField",
    "ProjectivePencilFibration",
    "ProjectivePencilMetrics",
]

