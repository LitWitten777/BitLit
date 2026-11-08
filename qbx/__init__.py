"""
QBX Phase 0 Kernel, and the end-to-end entry point ``qbx.process`` (see ``qbx/process.py``).

Minimal, auditable kernel that enforces the most critical invariants
of the QBX / Categorical Ledger system.
"""

__version__ = "0.1.0"

from qbx.core.enforced_functor import EnforcedFunctor, EnforcementMode
from qbx.core.exceptions import (
    FunctorLawViolation,
    CanonicalizationError,
    PathValidationError,
    CapabilityRequiredError,
)
from qbx.path.signature import PathSignature
from qbx.path.validator import PathValidator
from qbx.weyl.engine import WeylEngine
from qbx.hebrew.mixing import HebrewMixer
from qbx.process import Options, Result, process

__all__ = [
    "EnforcedFunctor",
    "EnforcementMode",
    "FunctorLawViolation",
    "CanonicalizationError",
    "PathValidationError",
    "CapabilityRequiredError",
    "PathSignature",
    "PathValidator",
    "WeylEngine",
    "HebrewMixer",
    "process",
    "Options",
    "Result",
]
