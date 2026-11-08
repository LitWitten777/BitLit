"""
Hybrid signing pipeline (classical + PQ).

For Phase 0, we provide a StubSigner that uses Ed25519 (via `cryptography`).
The interface is designed so that a production HybridSigner (with HSM/KMS
integration and PQ keys) can be dropped in without changing callers.

Signed payloads always carry:

- signature bytes
- key_id
- algorithm identifier
"""

from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)


@dataclass(frozen=True)
class SignedBlob:
    """A signed payload."""

    payload_hash: str
    signature: bytes
    key_id: str
    algorithm: str

    def to_dict(self) -> dict:
        return {
            "payload_hash": self.payload_hash,
            "signature": self.signature.hex(),
            "key_id": self.key_id,
            "algorithm": self.algorithm,
        }


class StubSigner:
    """
    Development signer using Ed25519.

    In production, replace with a HybridSigner that:

    - uses HSM-backed keys
    - produces both a classical and PQ signature
    - returns a combined signature blob
    """

    ALGORITHM = "Ed25519-STUB"

    def __init__(self, key_path: Optional[str] = None, key_id: str = "dev-key-001"):
        self.key_id = key_id
        self.key_path = Path(key_path or os.getenv(
            "QBX_SIGNING_KEY_PATH", "./keys/dev_signing_key.pem"
        ))
        self._private_key: Optional[Ed25519PrivateKey] = None
        self._load_or_create()

    def _load_or_create(self) -> None:
        if self.key_path.exists():
            data = self.key_path.read_bytes()
            self._private_key = serialization.load_pem_private_key(
                data, password=None
            )
        else:
            self.key_path.parent.mkdir(parents=True, exist_ok=True)
            self._private_key = Ed25519PrivateKey.generate()
            pem = self._private_key.private_bytes(
                encoding=serialization.Encoding.PEM,
                format=serialization.PrivateFormat.PKCS8,
                encryption_algorithm=serialization.NoEncryption(),
            )
            self.key_path.write_bytes(pem)

    @property
    def public_key(self) -> Ed25519PublicKey:
        assert self._private_key is not None
        return self._private_key.public_key()

    def public_key_bytes(self) -> bytes:
        return self.public_key.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )

    def sign(self, payload_hash: str) -> SignedBlob:
        """Sign a hex payload hash. Returns a SignedBlob."""
        assert self._private_key is not None
        sig = self._private_key.sign(payload_hash.encode("utf-8"))
        return SignedBlob(
            payload_hash=payload_hash,
            signature=sig,
            key_id=self.key_id,
            algorithm=self.ALGORITHM,
        )

    def verify(self, blob: SignedBlob) -> bool:
        try:
            self.public_key.verify(
                blob.signature, blob.payload_hash.encode("utf-8")
            )
            return True
        except Exception:
            return False


class HybridSigner:
    """
    Placeholder for production hybrid classical + PQ signer.

    In Phase 0, this delegates to StubSigner. In production, it would:

    - Call HSM/KMS for classical (Ed25519/ECDSA) signing
    - Call PQ module (Dilithium / SPHINCS+) for PQ signing
    - Return a combined signature blob with both
    """

    ALGORITHM = "HYBRID-CLASSICAL+PQ-STUB"

    def __init__(self, key_id: str = "prod-key-001"):
        self._stub = StubSigner(key_id=key_id)
        self.key_id = key_id

    def sign(self, payload_hash: str) -> SignedBlob:
        return self._stub.sign(payload_hash)

    def verify(self, blob: SignedBlob) -> bool:
        return self._stub.verify(blob)
