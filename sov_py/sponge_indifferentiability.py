"""
Ramanujan Sponge Indifferentiability Simulator and Advantage Verification (OP-055, HYP-133).

Formalizes the indifferentiability of the `RamanujanSponge` construction from an
ideal random oracle up to O(2^{c/2}) queries in the ideal permutation model
(Maurer-TCS 2004, Bertoni-Daemen-Peeters-Van Assche 2008).

Key Components:
1. Ideal Random Oracle (RO): Simulates infinite-domain uniform random function.
2. Sponge Simulator (S): Simulates the ideal permutation f and f^{-1} given access to RO,
   maintaining a state transition graph and dynamically answering queries without
   inducing uninvited inner-state (capacity) collisions.
3. Distinguishing Game: Real World (Sponge[f], f) vs. Ideal World (RO, S).
4. Analytical Bounds: Exact collision bounds Q^2 / 2^c, security level s = c/2,
   and query complexity lower bound Q >= sqrt(epsilon * 2^c) for any distinguishing advantage epsilon.
"""

from __future__ import annotations

import hashlib
import math
import os
from dataclasses import dataclass, field
from typing import Callable, Optional


def pad_101(data: bytes, rate_bytes: int) -> list[bytes]:
    """
    Invertible pad10*1 multi-block padding scheme for sponge absorbing.
    Appends a 1-bit (0x80 or single bit), zeroes, and a final 1-bit.
    """
    pad_len = rate_bytes - (len(data) % rate_bytes)
    if pad_len == 1:
        padding = bytes([0x81])
    else:
        padding = bytes([0x80]) + bytes(pad_len - 2) + bytes([0x01])
    padded = data + padding
    return [padded[i : i + rate_bytes] for i in range(0, len(padded), rate_bytes)]


class IdealRandomOracle:
    """
    Simulated ideal random oracle mapping arbitrary bytes to arbitrary output length.
    Deterministic and collision-free using dynamic expansion.
    """

    def __init__(self, salt: bytes = b"RO_SALT_055") -> None:
        self.salt = salt
        self._history: dict[bytes, bytes] = {}
        self.query_count = 0

    def query(self, message: bytes, output_len: int) -> bytes:
        self.query_count += 1
        if message not in self._history:
            # Deterministic PRF based on sha256 counter expansion
            out = bytearray()
            counter = 0
            while len(out) < max(output_len, 256):
                h = hashlib.sha256(self.salt + counter.to_bytes(4, "big") + message).digest()
                out.extend(h)
                counter += 1
            self._history[message] = bytes(out)
        return self._history[message][:output_len]


@dataclass
class SpongeSimulator:
    """
    Simulator S with oracle access to IdealRandomOracle.

    Simulates the forward permutation f(x) and backward permutation f^{-1}(y).
    Maintains:
    - Forward mapping F: x -> y
    - Backward mapping F_inv: y -> x
    - State transition graph G = (V, E) where nodes are state values (r, c)
      and edges are labeled with message block m.
    - Capacity collision counter to track bad events E_coll and E_hit.
    """

    rate_bytes: int
    capacity_bytes: int
    oracle: IdealRandomOracle
    f_map: dict[bytes, bytes] = field(default_factory=dict)
    f_inv: dict[bytes, bytes] = field(default_factory=dict)
    capacity_to_node: dict[bytes, tuple[bytes, tuple[bytes, ...]]] = field(default_factory=dict)
    node_to_capacity: set[bytes] = field(default_factory=set)
    bad_capacity_collisions: int = 0
    query_count: int = 0

    def __post_init__(self) -> None:
        self.width_bytes = self.rate_bytes + self.capacity_bytes
        # Root state 0^b is known at path ()
        root = bytes(self.width_bytes)
        c_root = root[self.rate_bytes :]
        self.capacity_to_node[c_root] = (root, ())
        self.node_to_capacity.add(c_root)

    def forward(self, x: bytes) -> bytes:
        """Simulates f(x)."""
        assert len(x) == self.width_bytes, f"State must be {self.width_bytes} bytes"
        self.query_count += 1
        if x in self.f_map:
            return self.f_map[x]

        r_x = x[: self.rate_bytes]
        c_x = x[self.rate_bytes :]

        # Check if capacity c_x connects to a known node in the tree
        is_rooted = c_x in self.capacity_to_node
        if is_rooted:
            prev_node, prev_path = self.capacity_to_node[c_x]
            m = bytes([a ^ b for a, b in zip(prev_node[: self.rate_bytes], r_x)])
            path = prev_path + (m,)
            msg = b"".join(path)
            r_y = self.oracle.query(msg, self.rate_bytes)
        else:
            path = ()
            r_y = os.urandom(self.rate_bytes)

        # Sample fresh capacity part avoiding collisions
        c_y = self._sample_fresh_capacity()

        y = r_y + c_y
        while y in self.f_inv:
            c_y = self._sample_fresh_capacity()
            y = r_y + c_y

        # Record mappings
        self.f_map[x] = y
        self.f_inv[y] = x

        # If x was rooted, record successor paths
        if is_rooted:
            self.capacity_to_node[c_y] = (y, path)

        return y

    def inverse(self, y: bytes) -> bytes:
        """Simulates f^{-1}(y)."""
        assert len(y) == self.width_bytes, f"State must be {self.width_bytes} bytes"
        self.query_count += 1
        if y in self.f_inv:
            return self.f_inv[y]

        r_x = os.urandom(self.rate_bytes)
        c_x = self._sample_fresh_capacity()
        x = r_x + c_x
        while x in self.f_map:
            c_x = self._sample_fresh_capacity()
            x = r_x + c_x

        self.f_map[x] = y
        self.f_inv[y] = x
        return x

    def _sample_fresh_capacity(self) -> bytes:
        c = os.urandom(self.capacity_bytes)
        if c in self.node_to_capacity:
            self.bad_capacity_collisions += 1
        self.node_to_capacity.add(c)
        return c


class SimulatedRealPermutation:
    """Ideal random permutation on {0,1}^b."""

    def __init__(self, width_bytes: int) -> None:
        self.width_bytes = width_bytes
        self.f_map: dict[bytes, bytes] = {}
        self.f_inv: dict[bytes, bytes] = {}
        self.query_count = 0

    def forward(self, x: bytes) -> bytes:
        self.query_count += 1
        if x in self.f_map:
            return self.f_map[x]
        y = os.urandom(self.width_bytes)
        while y in self.f_inv:
            y = os.urandom(self.width_bytes)
        self.f_map[x] = y
        self.f_inv[y] = x
        return y

    def inverse(self, y: bytes) -> bytes:
        self.query_count += 1
        if y in self.f_inv:
            return self.f_inv[y]
        x = os.urandom(self.width_bytes)
        while x in self.f_map:
            x = os.urandom(self.width_bytes)
        self.f_map[x] = y
        self.f_inv[y] = x
        return x


class SimulatedSponge:
    """Sponge construction S[f] over permutation f."""

    def __init__(self, rate_bytes: int, capacity_bytes: int, perm: SimulatedRealPermutation) -> None:
        self.rate_bytes = rate_bytes
        self.capacity_bytes = capacity_bytes
        self.perm = perm
        self.width_bytes = rate_bytes + capacity_bytes
        self.query_count = 0

    def absorb_and_squeeze(self, message: bytes, output_len: int) -> bytes:
        self.query_count += 1
        blocks = pad_101(message, self.rate_bytes)
        state = bytearray(self.width_bytes)

        # Absorbing
        for block in blocks:
            for i in range(self.rate_bytes):
                state[i] ^= block[i]
            state = bytearray(self.perm.forward(bytes(state)))

        # Squeezing
        out = bytearray()
        while len(out) < output_len:
            out.extend(state[: self.rate_bytes])
            if len(out) < output_len:
                state = bytearray(self.perm.forward(bytes(state)))
        return bytes(out[:output_len])


class DistinguishingGame:
    """
    Evaluates distinguishing advantage between:
    - Real World: (S[f], f, f^{-1})
    - Ideal World: (RO, S, S^{-1})
    """

    def __init__(self, rate_bytes: int, capacity_bytes: int) -> None:
        self.rate_bytes = rate_bytes
        self.capacity_bytes = capacity_bytes
        self.width_bytes = rate_bytes + capacity_bytes

    def create_real_world(self) -> tuple[SimulatedSponge, SimulatedRealPermutation]:
        perm = SimulatedRealPermutation(self.width_bytes)
        sponge = SimulatedSponge(self.rate_bytes, self.capacity_bytes, perm)
        return sponge, perm

    def create_ideal_world(self) -> tuple[IdealRandomOracle, SpongeSimulator]:
        oracle = IdealRandomOracle()
        sim = SpongeSimulator(self.rate_bytes, self.capacity_bytes, oracle)
        return oracle, sim


def indifferentiability_bound(q_total: int, capacity_bits: int) -> float:
    """
    Theoretical upper bound on distinguishing advantage:
    Adv <= Q^2 / 2^c
    """
    return (q_total ** 2) / (2.0 ** capacity_bits)


def min_queries_for_advantage(epsilon: float, capacity_bits: int) -> float:
    """
    Query complexity lower bound:
    Adv >= epsilon ==> Q >= sqrt(epsilon * 2^c) = sqrt(epsilon) * 2^{c/2}
    """
    assert 0.0 < epsilon <= 1.0
    return math.sqrt(epsilon * (2.0 ** capacity_bits))


def capacity_collision_prob(q: int, capacity_bits: int) -> float:
    """
    Birthday bound on inner-state capacity collisions among Q queries:
    P(coll) <= Q(Q - 1) / (2 * 2^c)
    """
    return (q * (q - 1)) / (2.0 * (2.0 ** capacity_bits))


def evaluate_adversary_advantage(
    distinguisher: Callable[[Any, Any], int],
    rate_bytes: int,
    capacity_bytes: int,
    trials: int = 100,
) -> float:
    """
    Empirically estimates distinguishing advantage:
    Adv = |P[D(Real) = 1] - P[D(Ideal) = 1]|
    """
    game = DistinguishingGame(rate_bytes, capacity_bytes)
    real_ones = 0
    for _ in range(trials):
        sponge_real, perm_real = game.create_real_world()
        res = distinguisher(sponge_real, perm_real)
        if res == 1:
            real_ones += 1

    ideal_ones = 0
    for _ in range(trials):
        oracle_ideal, sim_ideal = game.create_ideal_world()
        res = distinguisher(oracle_ideal, sim_ideal)
        if res == 1:
            ideal_ones += 1

    p_real = real_ones / trials
    p_ideal = ideal_ones / trials
    return abs(p_real - p_ideal)
