"""
Post-quantum-ready hashing pipeline.

Current algorithm: SHA3-256 (NIST-approved, quantum-resistant at appropriate
output sizes for our purposes).

We also support a "PQ-HASH" identifier so that a future PQ hash algorithm
can be substituted without changing downstream code.
"""

from __future__ import annotations

import hashlib
from typing import Union

from qbx.core.exceptions import HashingError

SUPPORTED_ALGOS = ("SHA3-256", "SHA3-512", "SHA-256", "PQ-HASH-1")


def sha3_256_hex(data: bytes) -> str:
    """SHA3-256 hex digest."""
    return hashlib.sha3_256(data).hexdigest()


def sha3_512_hex(data: bytes) -> str:
    return hashlib.sha3_512(data).hexdigest()


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def pq_hash(data: bytes, algo: str = "SHA3-256") -> str:
    """
    Compute a post-quantum-ready hash.

    For "PQ-HASH-1", we currently fall back to SHA3-512 as a stand-in
    (a real PQ hash like SPHINCS+ or a lattice-based hash would be substituted
    in production). The algorithm identifier is stored alongside the digest,
    so downstream code can adapt.
    """
    algo = algo.upper()
    if algo == "SHA3-256":
        return sha3_256_hex(data)
    if algo == "SHA3-512":
        return sha3_512_hex(data)
    if algo == "SHA-256":
        return sha256_hex(data)
    if algo == "PQ-HASH-1":
        # Placeholder: SHA3-512 as PQ-resistant stand-in.
        # TODO: replace with actual PQ hash (e.g., SPHINCS+ or lattice hash).
        return "PQ1:" + sha3_512_hex(data)
    raise HashingError(f"Unsupported hash algorithm: {algo}")


def hash_bytes(data: Union[bytes, bytearray, str]) -> str:
    """Convenience: hash bytes or string with default SHA3-256."""
    if isinstance(data, str):
        data = data.encode("utf-8")
    return pq_hash(bytes(data))
