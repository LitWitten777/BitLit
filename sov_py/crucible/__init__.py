"""
src/sedenion/crucible
=============================================================================
Crucible Hypergraph Runtime and Operator Suite.
Provides typed RepresentationObject, HyperEdge, and the 7 canonical operators:
Generate, Associate, Reflect, Verify, Compose, Integrate, Decompose.
=============================================================================
"""

from .context import CrucibleContext
from .justification import Justification, JustificationChain, JustificationStatus
from .operators import (
    Associate,
    Compose,
    CrucibleOperator,
    Decompose,
    Generate,
    Integrate,
    Reflect,
    Verify,
)
from .verify import batch_verify, decide_status
from ..hypergraph import HyperEdge, Hypergraph, RepresentationObject, make_provenance, validate_provenance

__all__ = [
    "CrucibleContext",
    "Justification",
    "JustificationChain",
    "JustificationStatus",
    "CrucibleOperator",
    "Generate",
    "Associate",
    "Reflect",
    "Verify",
    "Compose",
    "Integrate",
    "Decompose",
    "decide_status",
    "batch_verify",
    "HyperEdge",
    "Hypergraph",
    "RepresentationObject",
    "make_provenance",
    "validate_provenance",
]
