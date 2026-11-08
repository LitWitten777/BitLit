"""
PathSignature: a canonical, hashable, signable representation of a morphism chain.

A path signature captures:

- a chain of morphism IDs (the path)
- the start and end objects
- optional metadata (category, universe, tags, coords)
- a canonical CBOR encoding of the above
- a PQ-hash of the canonical bytes
- an AddressV2 hash

The canonical bytes are the source of truth for integrity.
"""

from __future__ import annotations

import uuid
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional

from qbx.core.canonical import canonical_cbor
from qbx.core.exceptions import CanonicalizationError, PathValidationError
from qbx.core.hashing import pq_hash
from qbx.core.signing import SignedBlob, StubSigner


@dataclass(frozen=True)
class PathSignature:
    """Immutable path signature."""

    path_id: str
    category_id: str
    start_object_id: str
    end_object_id: str
    morphism_chain: List[str]
    canonical_bytes: bytes
    proof_hash: str
    address_hash: str
    metadata: Dict[str, Any] = field(default_factory=dict)

    @classmethod
    def build(
        cls,
        category_id: str,
        start_object_id: str,
        end_object_id: str,
        morphism_chain: List[str],
        metadata: Optional[Dict[str, Any]] = None,
        universe_id: Optional[str] = None,
        coords: Optional[bytes] = None,
        semantic_tags: Optional[List[bytes]] = None,
        trust_score: float = 0.0,
        verification_depth: int = 0,
    ) -> "PathSignature":
        """Build a PathSignature from its components."""
        if not morphism_chain:
            raise PathValidationError("morphism_chain cannot be empty")

        path_id = str(uuid.uuid4())
        meta = metadata or {}

        payload = {
            "version": 1,
            "path_id": path_id,
            "category_id": category_id,
            "start_object_id": start_object_id,
            "end_object_id": end_object_id,
            "morphism_chain": morphism_chain,
            "metadata": meta,
        }
        try:
            canonical = canonical_cbor(payload)
        except CanonicalizationError as e:
            raise PathValidationError(f"Failed to canonicalize path: {e}") from e

        proof_hash = pq_hash(canonical)

        # Build AddressV2 payload and hash it.
        address_payload = {
            "version": 2,
            "universe_id": universe_id or "00000000-0000-0000-0000-000000000000",
            "artifact_id": None,
            "path_signature": canonical.hex(),
            "coords": (coords or b"").hex(),
            "coords_scale": 0,
            "semantic_tags": [t.hex() for t in (semantic_tags or [])],
            "trust_hint": {
                "trust_score": float(trust_score),
                "verification_depth": int(verification_depth),
            },
            "routing_hint": None,
            "timestamp": 0,
            "nonce": uuid.uuid4().bytes.hex(),
        }
        try:
            address_bytes = canonical_cbor(address_payload)
        except CanonicalizationError as e:
            raise PathValidationError(f"Failed to canonicalize address: {e}") from e
        address_hash = pq_hash(address_bytes)

        return cls(
            path_id=path_id,
            category_id=category_id,
            start_object_id=start_object_id,
            end_object_id=end_object_id,
            morphism_chain=list(morphism_chain),
            canonical_bytes=canonical,
            proof_hash=proof_hash,
            address_hash=address_hash,
            metadata=meta,
        )

    def recompute_proof_hash(self) -> str:
        """Recompute proof hash from canonical bytes."""
        return pq_hash(self.canonical_bytes)

    def is_integrity_ok(self) -> bool:
        """Verify that stored proof_hash matches recomputed hash."""
        return self.proof_hash == self.recompute_proof_hash()

    def sign(self, signer: StubSigner) -> SignedBlob:
        """Sign the proof hash."""
        return signer.sign(self.proof_hash)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "path_id": self.path_id,
            "category_id": self.category_id,
            "start_object_id": self.start_object_id,
            "end_object_id": self.end_object_id,
            "morphism_chain": self.morphism_chain,
            "canonical_bytes_hex": self.canonical_bytes.hex(),
            "proof_hash": self.proof_hash,
            "address_hash": self.address_hash,
            "metadata": self.metadata,
        }
