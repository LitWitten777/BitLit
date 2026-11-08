"""
In-memory address book: the reference for the tables, row checks, writers and
resolution of migration ``013_addressing_protocol.sql``.

Every ``*_problems`` function returns the same ``(reason, details)`` pairs as
the database function of the same name (``addr_registry_problems``,
``addr_cache_problems``, ``addr_gateway_problems``, ``addr_dht_problems``,
``addr_discovery_problems``), and :class:`AddressBook` implements the writers
(``register_address``, ``cache_address_resolution``, ``register_gateway``,
``register_dht_node``), ``resolve_address`` and ``purge_expired_cache``.
"""

from __future__ import annotations

import ipaddress
import re
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from typing import Any, Dict, List, Optional, Set

from qbx.addressing.address import (
    Problem,
    address_problems,
    is_address_hash,
    pointer_problems,
    trust_hint_of,
)
from qbx.addressing.cbor_strict import decode_strict
from qbx.addressing.dht import NODE_ID_BYTES, closest_nodes

PROTOCOLS = ("tcp", "udp", "quic", "http", "https", "ws", "wss")
INT_MAX = 2 ** 31 - 1

_V6_PORT = re.compile(r"\[([^\]]*)\]:([0-9]+)")
_V4_PORT = re.compile(r"([0-9.]+):([0-9]+)")
_V4 = re.compile(r"(0|[1-9][0-9]{0,2})(\.(0|[1-9][0-9]{0,2})){3}")
_PORT = re.compile(r"[1-9][0-9]{0,4}")


class AddressingError(ValueError):
    """A writer refused its input."""


def endpoint_ok(endpoint: Any) -> bool:
    """``addr_endpoint_ok``: ``a.b.c.d``, ``a.b.c.d:port``, an IPv6 address, or
    ``[v6]:port`` (no prefix length, no zone id, no whitespace)."""
    if not isinstance(endpoint, str) or re.search(r"[%/\s]", endpoint):
        return False
    m = _V6_PORT.fullmatch(endpoint)
    fam: Optional[int] = None
    port: Optional[str] = None
    if m:
        host, port, fam = m.group(1), m.group(2), 6
    else:
        m = _V4_PORT.fullmatch(endpoint)
        if m:
            host, port, fam = m.group(1), m.group(2), 4
        else:
            host = endpoint
    if port is not None and not (_PORT.fullmatch(port) and int(port) <= 65535):
        return False
    if ":" not in host and not _V4.fullmatch(host):
        return False
    try:
        v = ipaddress.ip_address(host)
    except ValueError:
        return False
    return fam is None or v.version == fam


def cache_valid_at(cached_at: datetime, ttl: Any, at: datetime) -> bool:
    """``addr_cache_valid_at``: ``cached_at <= at < cached_at + ttl``."""
    return (isinstance(ttl, int) and ttl > 0
            and cached_at <= at < cached_at + timedelta(seconds=ttl))


# ---------------------------------------------------------------------------
# Rows and their problems
# ---------------------------------------------------------------------------
@dataclass
class RegistryRow:
    address_hash: str
    address_cbor: bytes
    hash_algo: str = "SHA3-256"
    pointers: Any = field(default_factory=list)
    trust_score: Optional[float] = None
    verification_depth: Optional[int] = None
    owner: Optional[bytes] = None


@dataclass
class CacheRow:
    address_hash: str
    pointers: Any
    ttl: Any
    cached_at: datetime
    source: Optional[str] = None


@dataclass
class GatewayRow:
    address_hash: str
    ip_endpoint: Any
    protocol: Any


@dataclass
class DhtRow:
    node_id: bytes
    endpoint: Optional[str] = None


@dataclass
class DiscoveryRow:
    k: Any
    results: Any
    latency_ms: Any = None


def registry_problems(r: RegistryRow) -> List[Problem]:
    return (address_problems(r.address_cbor, r.address_hash, r.hash_algo, r.trust_score,
                             r.verification_depth)
            + pointer_problems(r.pointers))


def cache_problems(r: CacheRow) -> List[Problem]:
    out: List[Problem] = []
    if not is_address_hash(r.address_hash):
        out.append(("cache_typing", {"error": "hash_format"}))
    if not (isinstance(r.ttl, int) and r.ttl > 0):
        out.append(("cache_typing", {"error": "ttl"}))
    if pointer_problems(r.pointers):
        out.append(("cache_typing", {"error": "pointers"}))
    return out


def gateway_problems(r: GatewayRow, registered: Set[str]) -> List[Problem]:
    out: List[Problem] = []
    if not endpoint_ok(r.ip_endpoint):
        out.append(("gateway_typing", {"error": "endpoint"}))
    if r.protocol not in PROTOCOLS:
        out.append(("gateway_typing", {"error": "protocol"}))
    if r.address_hash not in registered:
        out.append(("gateway_unregistered", {}))
    return out


def dht_problems(r: DhtRow) -> List[Problem]:
    return [] if len(r.node_id) == NODE_ID_BYTES else [("dht_typing", {"error": "node_id"})]


def discovery_problems(r: DiscoveryRow) -> List[Problem]:
    out: List[Problem] = []
    k_ok = isinstance(r.k, int) and r.k > 0
    if not k_ok:
        out.append(("discovery_typing", {"error": "k"}))
    if isinstance(r.latency_ms, int) and r.latency_ms < 0:
        out.append(("discovery_typing", {"error": "latency"}))
    if not isinstance(r.results, list) or (isinstance(r.k, int) and len(r.results) > max(r.k, 0)):
        out.append(("discovery_typing", {"error": "results"}))
    return out


# ---------------------------------------------------------------------------
# The address book
# ---------------------------------------------------------------------------
@dataclass
class AddressBook:
    registry: Dict[str, RegistryRow] = field(default_factory=dict)
    cache: List[CacheRow] = field(default_factory=list)
    gateways: List[GatewayRow] = field(default_factory=list)
    nodes: Dict[bytes, DhtRow] = field(default_factory=dict)

    # -- writers -------------------------------------------------------
    def register_address(self, address_hash: str, address_cbor: bytes,
                         owner: Optional[bytes] = None, pointers: Any = None,
                         trust: Optional[float] = None, depth: Optional[int] = None,
                         algo: str = "SHA3-256") -> RegistryRow:
        pointers = [] if pointers is None else pointers
        d = decode_strict(address_cbor)
        score, vdepth = trust_hint_of(d.value) if d.ok else (None, None)
        trust = score if trust is None else trust
        if depth is None and vdepth is not None and vdepth <= INT_MAX:
            depth = vdepth
        probs = (address_problems(address_cbor, address_hash, algo, trust, depth)
                 + pointer_problems(pointers))
        if probs:
            raise AddressingError(f"register_address: {probs[0]}")
        ex = self.registry.get(address_hash)
        if ex is not None:
            if ex.address_cbor != address_cbor or ex.hash_algo != algo:
                raise AddressingError("registered with other content")
            if owner is not None and ex.owner != owner:
                raise AddressingError("registered to another owner")
            ex.pointers = ex.pointers + [p for p in pointers if p not in ex.pointers]
            return ex
        row = RegistryRow(address_hash, bytes(address_cbor), algo, list(pointers), trust, depth,
                          owner)
        self.registry[address_hash] = row
        return row

    def cache_resolution(self, address_hash: str, pointers: Any, ttl: Any, at: datetime,
                         source: Optional[str] = None) -> CacheRow:
        row = CacheRow(address_hash, pointers, ttl, at, source)
        if cache_problems(row):
            raise AddressingError(f"cache_address_resolution: {cache_problems(row)[0]}")
        self.cache.append(row)
        return row

    def register_gateway(self, address_hash: str, ip: Any, protocol: Any) -> GatewayRow:
        row = GatewayRow(address_hash, ip, protocol)
        probs = gateway_problems(row, set(self.registry))
        if probs:
            raise AddressingError(f"register_gateway: {probs[0]}")
        for g in self.gateways:
            if (g.address_hash, g.ip_endpoint, g.protocol) == (address_hash, ip, protocol):
                return g
        self.gateways.append(row)
        return row

    def register_node(self, node_id: bytes, endpoint: Optional[str] = None) -> DhtRow:
        if len(node_id) != NODE_ID_BYTES:
            raise AddressingError("a node id is 32 bytes")
        ex = self.nodes.get(node_id)
        if ex is not None:
            if endpoint is not None and ex.endpoint is not None and ex.endpoint != endpoint:
                raise AddressingError("node is registered at another endpoint")
            ex.endpoint = ex.endpoint if ex.endpoint is not None else endpoint
            return ex
        row = DhtRow(node_id, endpoint)
        self.nodes[node_id] = row
        return row

    # -- resolution and routing ----------------------------------------
    def resolve(self, address_hash: str, at: datetime) -> Optional[List[str]]:
        """``resolve_address``: the registry's pointers, else the newest valid cache entry."""
        if address_hash in self.registry:
            return self.registry[address_hash].pointers
        valid = [c for c in self.cache
                 if c.address_hash == address_hash and cache_valid_at(c.cached_at, c.ttl, at)
                 and not pointer_problems(c.pointers)]
        if not valid:
            return None
        return max(valid, key=lambda c: c.cached_at).pointers

    def purge(self, at: datetime) -> int:
        """``purge_expired_cache``: drop the entries that are no longer valid at ``at``."""
        keep = [c for c in self.cache
                if isinstance(c.ttl, int) and c.ttl > 0
                and at < c.cached_at + timedelta(seconds=c.ttl)]
        n = len(self.cache) - len(keep)
        self.cache = keep
        return n

    def closest(self, key: bytes, k: int) -> List[bytes]:
        return closest_nodes(key, self.nodes, k)
