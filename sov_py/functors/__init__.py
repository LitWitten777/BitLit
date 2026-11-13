"""
Functorial Manifold Learner Package — Endofunctor optimization on geometric lattices.
"""

from .endofunctor_learner import (
    DIAGRAM_ENTROPY_THRESHOLD,
    EndofunctorLearner,
    LearnerResult,
)

__all__ = [
    "EndofunctorLearner",
    "LearnerResult",
    "DIAGRAM_ENTROPY_THRESHOLD",
]
