"""
DHT routing in the XOR metric (Kademlia): the reference for ``addr_xor``,
``addr_bucket``, ``address_dht_key`` and ``dht_closest_nodes`` in migration
``013_addressing_protocol.sql``.

Node ids and keys are 256-bit (32-byte) big-endian strings.  The database
sorts nodes by the bytewise XOR compared as ``BYTEA``; ``Formal/Addressing.lean``
proves that this is the XOR-distance order (``bytea_xor_order``), that no two
nodes are at the same distance from a key (``xorDist_unidirectional``), and so
that the ``k`` closest nodes are well defined (``kClosest_exists``,
``kClosest_unique``).
"""

from __future__ import annotations

import hashlib
from typing import Iterable, List, Optional

NODE_ID_BYTES = 32


def xor_distance(a: bytes, b: bytes) -> bytes:
    """Bytewise XOR of two ids of the same length."""
    if len(a) != len(b):
        raise ValueError("ids of different lengths")
    return bytes(x ^ y for x, y in zip(a, b))


def distance(a: bytes, b: bytes) -> int:
    """The XOR distance as an integer."""
    return int.from_bytes(a, "big") ^ int.from_bytes(b, "big")


def bucket_index(a: bytes, b: bytes) -> Optional[int]:
    """Index of the highest differing bit (``⌊log₂ d⌋``); ``None`` when ``a == b``."""
    d = distance(a, b) if len(a) == len(b) else 0
    return d.bit_length() - 1 if d else None


def dht_key(address_hash: str) -> bytes:
    """The DHT key of an address: SHA3-256 of its hash text."""
    return hashlib.sha3_256(address_hash.encode("utf-8")).digest()


def closest_nodes(key: bytes, nodes: Iterable[bytes], k: int) -> List[bytes]:
    """The ``k`` well-formed nodes nearest to ``key``, nearest first."""
    if len(key) != NODE_ID_BYTES:
        raise ValueError("the key must be 32 bytes")
    if k < 0:
        raise ValueError("k must be non-negative")
    ok = sorted({n for n in nodes if len(n) == NODE_ID_BYTES}, key=lambda n: xor_distance(n, key))
    return ok[:k]


def is_k_closest(key: bytes, nodes: Iterable[bytes], chosen: Iterable[bytes], k: int) -> bool:
    """``IsKClosest`` of the Lean file: ``k`` nodes of the set, each at most as far
    from ``key`` as every node outside the selection."""
    s = set(nodes)
    a = set(chosen)
    if not a <= s or len(a) != k:
        return False
    return all(distance(key, x) <= distance(key, y) for x in a for y in s - a)
