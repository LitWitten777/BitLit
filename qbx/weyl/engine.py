"""
Weyl reflection engine for E8.

The Weyl group W(E8) has order 696,729,600. It acts on the root system by
reflections s_α(v) = v - 2·⟨v,α⟩/⟨α,α⟩ · α.

This engine provides:

- Deterministic reflection of a vector by a root.
- Orbit generation with caching of canonical representatives.
- Capability-gated expansion beyond cache (to prevent DoS).
- Orbit size sanity checks.

For Phase 0, "canonical representative" is the lexicographically smallest
vector in the orbit (up to a fixed tolerance).
"""

from __future__ import annotations

import logging
import os
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

import numpy as np

from qbx.core.exceptions import CapabilityRequiredError, WeylEngineError
from qbx.weyl.e8_roots import E8_ROOTS

logger = logging.getLogger(__name__)

Vector = Tuple[float, ...]


def _to_tuple(v: np.ndarray) -> Vector:
    return tuple(float(x) for x in v)


def _round_vec(v: Vector, tol: float = 1e-6) -> Vector:
    """Round each component to a rational with denominator 2 (roots live in (1/2)Z)."""
    return tuple(round(x * 2) / 2 for x in v)


def reflect(v: np.ndarray, alpha: np.ndarray) -> np.ndarray:
    """Reflect v across the hyperplane orthogonal to alpha."""
    denom = float(np.dot(alpha, alpha))
    if denom == 0:
        raise WeylEngineError("Cannot reflect across zero vector")
    return v - 2.0 * float(np.dot(v, alpha)) / denom * alpha


@dataclass
class Orbit:
    """A Weyl orbit with cached representatives."""

    seed: Vector
    members: Tuple[Vector, ...]
    canonical: Vector

    def __len__(self) -> int:
        return len(self.members)


class WeylEngine:
    """
    Weyl reflection engine.

    Caches orbits by their canonical representative. Any request to expand
    an orbit beyond the cached set requires a valid capability token (unless
    QBX_WEYL_EXPANSION_REQUIRES_CAPABILITY=false).
    """

    def __init__(
        self,
        cache_max: Optional[int] = None,
        require_capability: Optional[bool] = None,
    ):
        self.cache_max = cache_max if cache_max is not None else int(
            os.getenv("QBX_WEYL_CACHE_MAX", "10000")
        )
        self.require_capability = (
            require_capability
            if require_capability is not None
            else os.getenv("QBX_WEYL_EXPANSION_REQUIRES_CAPABILITY", "true").lower()
            == "true"
        )
        self._roots_np = [np.array(r, dtype=np.float64) for r in E8_ROOTS]
        # orbit cache: canonical representative → Orbit
        self._orbit_cache: Dict[Vector, Orbit] = {}
        # simple in-memory capability tokens
        self._valid_capabilities: set = set()

    # ---- Capability management -------------------------------------------

    def grant_capability(self, token: str) -> None:
        """Register a capability token (dev-mode; in prod, verify signature)."""
        self._valid_capabilities.add(token)

    def revoke_capability(self, token: str) -> None:
        self._valid_capabilities.discard(token)

    def _require_capability(self, token: Optional[str]) -> None:
        if not self.require_capability:
            return
        if token is None or token not in self._valid_capabilities:
            raise CapabilityRequiredError(
                "Weyl orbit expansion requires a valid capability token"
            )

    # ---- Reflection -------------------------------------------------------

    def reflect(self, v: Vector, root_index: int) -> Vector:
        if not (0 <= root_index < len(self._roots_np)):
            raise WeylEngineError(f"Root index out of range: {root_index}")
        v_np = np.array(v, dtype=np.float64)
        result = reflect(v_np, self._roots_np[root_index])
        return _round_vec(_to_tuple(result))

    # ---- Orbit generation -------------------------------------------------

    def orbit(
        self,
        seed: Vector,
        max_size: int = 5000,
        capability_token: Optional[str] = None,
    ) -> Orbit:
        """
        Generate the Weyl orbit of `seed`.

        If the orbit size may exceed `max_size`, a capability token is required
        (unless require_capability is False).
        """
        seed = _round_vec(seed)

        # Check cache first
        canonical = self._find_canonical(seed)
        if canonical in self._orbit_cache:
            cached = self._orbit_cache[canonical]
            if seed in cached.members:
                return cached

        # Determine if we need to expand beyond cache
        if len(self._orbit_cache) >= self.cache_max:
            self._require_capability(capability_token)

        # BFS over roots
        visited: set = set()
        queue: List[Vector] = [seed]
        visited.add(seed)

        while queue:
            current = queue.pop()
            for i in range(len(self._roots_np)):
                neighbor = self.reflect(current, i)
                if neighbor not in visited:
                    visited.add(neighbor)
                    if len(visited) > max_size:
                        # If we exceed max_size, we require a capability token.
                        self._require_capability(capability_token)
                    queue.append(neighbor)

        members = tuple(sorted(visited))
        canonical = members[0]
        orbit = Orbit(seed=seed, members=members, canonical=canonical)
        self._orbit_cache[canonical] = orbit
        return orbit

    def _find_canonical(self, v: Vector) -> Vector:
        """Find the canonical representative of v, if cached."""
        for canon, orbit in self._orbit_cache.items():
            if v in orbit.members:
                return canon
        return v  # not cached; treat as its own canonical

    def cached_orbit_count(self) -> int:
        return len(self._orbit_cache)

    def clear_cache(self) -> None:
        self._orbit_cache.clear()
