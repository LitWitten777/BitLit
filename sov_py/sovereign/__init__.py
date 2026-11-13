"""
Sovereign Engine Subpackage.
===========================
Unified algebraic, projective, cosmohedral, quantum walk, and sheaf cohomology
engine for Cayley-Dickson algebras and zero-divisor expander varieties.
"""

from .projective_geometry import (
    FanoTetrahedron,
    ProjectiveSpaceF2,
    verify_all as verify_projective_geometry,
)
from .cosmo_kernel import (
    CosmoCanonicalForm,
    DevadossBracketAssociahedron,
    Matryoshka,
    MatryoshkaEngine,
    PoleProduct,
    PolygonGeometry,
    RationalPoleForm,
    SubmodularEnergyPoles,
    verify_all as verify_cosmo_kernel,
)
from .quantum_kernel import (
    CanonicalIsomorphismSigma,
    CrossHalfVector16,
    FanoCoupledExpander168,
    GroverZeroDivisorSearch,
    RamanujanExpanderC6K4,
    RankNTowerPredictor,
    SedenionZeroDivisorGraph16,
    ThreeGenerationsFibration32,
    build_cd_multiplication_table,
    construct_grover_coin_8,
    multiply_cd_vectors,
    verify_all as verify_quantum_kernel,
)
from .sheaf_guard import (
    CayleyDicksonCocycle,
    CechCohomologySheafGuard,
    SovereignSheafGuard,
    UnifiedTopologicalSheafGuard,
    verify_all as verify_sheaf_guard,
)

__all__ = [
    # Projective Geometry
    "ProjectiveSpaceF2",
    "FanoTetrahedron",
    "verify_projective_geometry",
    # Cosmohedral Kernel
    "PolygonGeometry",
    "Matryoshka",
    "MatryoshkaEngine",
    "DevadossBracketAssociahedron",
    "SubmodularEnergyPoles",
    "PoleProduct",
    "RationalPoleForm",
    "CosmoCanonicalForm",
    "verify_cosmo_kernel",
    # Quantum Kernel
    "build_cd_multiplication_table",
    "multiply_cd_vectors",
    "CrossHalfVector16",
    "SedenionZeroDivisorGraph16",
    "RamanujanExpanderC6K4",
    "construct_grover_coin_8",
    "GroverZeroDivisorSearch",
    "ThreeGenerationsFibration32",
    "CanonicalIsomorphismSigma",
    "FanoCoupledExpander168",
    "RankNTowerPredictor",
    "verify_quantum_kernel",
    # Sheaf Guard
    "CayleyDicksonCocycle",
    "CechCohomologySheafGuard",
    "UnifiedTopologicalSheafGuard",
    "SovereignSheafGuard",
    "verify_sheaf_guard",
]
