"""Core primitives: EnforcedFunctor, canonical serialization, hashing, signing."""

from qbx.core.enforced_functor import EnforcedFunctor, EnforcementMode
from qbx.core.canonical import canonical_cbor, canonical_json, canonical_bytes
from qbx.core.hashing import pq_hash, sha3_256_hex
from qbx.core.signing import HybridSigner, StubSigner
from qbx.core.exceptions import (
    FunctorLawViolation,
    CanonicalizationError,
    CapabilityRequiredError,
)

__all__ = [
    "EnforcedFunctor",
    "EnforcementMode",
    "canonical_cbor",
    "canonical_json",
    "canonical_bytes",
    "pq_hash",
    "sha3_256_hex",
    "HybridSigner",
    "StubSigner",
    "FunctorLawViolation",
    "CanonicalizationError",
    "CapabilityRequiredError",
]
