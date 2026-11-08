"""
PathValidator: validate a PathSignature end-to-end.

Checks:

1. Canonical bytes are well-formed CBOR.
2. proof_hash matches PQ-hash(canonical_bytes).
3. If a SignedBlob is provided, signature verifies.
4. Optional: chain well-formedness (each morphism's target = next morphism's source).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from qbx.core.canonical import decode_cbor
from qbx.core.hashing import pq_hash
from qbx.core.signing import SignedBlob, StubSigner
from qbx.path.signature import PathSignature


@dataclass
class ValidationResult:
    ok: bool
    checks: Dict[str, bool]
    diagnostics: List[str]

    def __bool__(self) -> bool:
        return self.ok


class PathValidator:
    """Validate PathSignatures and signed blobs."""

    def __init__(self, signer: Optional[StubSigner] = None):
        self.signer = signer or StubSigner()

    def validate(
        self,
        signature: PathSignature,
        signed_blob: Optional[SignedBlob] = None,
        morphism_endpoints: Optional[Dict[str, Tuple[str, str]]] = None,
    ) -> ValidationResult:
        """
        Validate a path signature.

        morphism_endpoints: optional dict morphism_id → (src_obj, tgt_obj).
        If provided, chain well-formedness is checked.
        """
        checks: Dict[str, bool] = {}
        diagnostics: List[str] = []

        # 1. Canonical bytes are well-formed CBOR.
        try:
            payload = decode_cbor(signature.canonical_bytes)
            checks["cbor_well_formed"] = isinstance(payload, dict)
        except Exception as e:
            checks["cbor_well_formed"] = False
            diagnostics.append(f"CBOR decode failed: {e}")
            payload = {}

        # 2. proof_hash matches recomputed hash.
        recomputed = pq_hash(signature.canonical_bytes)
        checks["proof_hash_matches"] = recomputed == signature.proof_hash
        if not checks["proof_hash_matches"]:
            diagnostics.append(
                f"proof_hash mismatch: stored={signature.proof_hash} recomputed={recomputed}"
            )

        # 3. Signature verification (if provided).
        if signed_blob is not None:
            checks["signature_key_id_matches"] = (
                signed_blob.key_id == self.signer.key_id
            )
            checks["signature_payload_hash_matches"] = (
                signed_blob.payload_hash == signature.proof_hash
            )
            checks["signature_valid"] = self.signer.verify(signed_blob)
            if not checks["signature_valid"]:
                diagnostics.append("signature does not verify")
        else:
            checks["signature_valid"] = True  # not provided, not required

        # 4. Chain well-formedness (if endpoints provided).
        if morphism_endpoints is not None:
            chain = signature.morphism_chain
            ok_chain = True
            if len(chain) > 1:
                for i in range(len(chain) - 1):
                    m1 = chain[i]
                    m2 = chain[i + 1]
                    if m1 not in morphism_endpoints or m2 not in morphism_endpoints:
                        ok_chain = False
                        diagnostics.append(f"missing endpoints for {m1} or {m2}")
                        break
                    if morphism_endpoints[m1][1] != morphism_endpoints[m2][0]:
                        ok_chain = False
                        diagnostics.append(
                            f"chain broken at {m1}→{m2}: "
                            f"{morphism_endpoints[m1][1]} ≠ {morphism_endpoints[m2][0]}"
                        )
                        break
            checks["chain_well_formed"] = ok_chain
        else:
            checks["chain_well_formed"] = True

        overall = all(checks.values())
        return ValidationResult(ok=overall, checks=checks, diagnostics=diagnostics)
