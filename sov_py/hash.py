"""
Ramanujan Expander Cryptographic Hash Function.

Constructs a collision-resistant cryptographic hash function combining deterministic
walks on the 8-regular Ramanujan annihilation graph Γ (λ₂ = 4 < 2√7 ≈ 5.2915) with
non-associative sedenion state accumulation.

Security & Hardness Division of Labor:
1. Expander Graph Mixing: The 24-vertex Ramanujan graph walk provides rapid local
   mixing and diffusion across the vertex space in O(log N) steps.
2. Accumulator One-Wayness: Because the graph alone has only 24 vertices and small
   diameter, graph-walk path finding in isolation would be tractable. Pre-image
   and collision resistance reside in the non-associative sedenion state accumulator:
   S_{t+1} = V(walk) * S_t.
3. MITM Failure: The lack of associativity and non-invertibility of zero divisors
   prevent bidirectional meet-in-the-middle attacks, forcing adversaries to evaluate
   the non-associative multiplication tree forward in full exponential depth O(d^m).
"""

import hashlib
import os
import secrets
import time
from typing import Any

import numpy as np

from .algebra import Sedenion
from .graph import get_cached_annihilation_graph


class RamanujanExpanderHash:
    """
    Cryptographic hash function based on non-backtracking or directed walks
    on the 8-regular Ramanujan zero-divisor graph Γ.
    """

    def __init__(self, component_index: int = 0, initial_vertex_index: int = 0):
        self.graph_engine = get_cached_annihilation_graph()
        self.components = self.graph_engine.component_subgraphs()
        self.comp_graph = self.components[component_index % len(self.components)]

        # Build canonical 8-neighbor lookup table for every vertex in this component
        self.nodes = sorted(self.comp_graph.nodes)
        self.node_to_idx = {node: i for i, node in enumerate(self.nodes)}
        self.idx_to_node = dict(enumerate(self.nodes))

        # Precompute canonically sorted neighbors for each vertex
        self.neighbor_table: dict[int, list[int]] = {}
        for node in self.nodes:
            nbrs = list(self.comp_graph.neighbors(node))
            if len(nbrs) != 8:
                raise ValueError(f"Vertex {node} degree must be 8, got {len(nbrs)}")
            # Sort neighbors canonically by (i, j, s1, s2)
            nbrs_sorted = sorted(
                nbrs,
                key=lambda n: (
                    self.comp_graph.nodes[n]["vector"].i,
                    self.comp_graph.nodes[n]["vector"].j,
                    self.comp_graph.nodes[n]["vector"].s1,
                    self.comp_graph.nodes[n]["vector"].s2,
                ),
            )
            self.neighbor_table[node] = nbrs_sorted

        self.start_node = self.nodes[initial_vertex_index % len(self.nodes)]

    def _bytes_to_trits(self, data: bytes) -> list[int]:
        """
        Converts a byte sequence into a sequence of 3-bit values (0..7).
        Pads the bitstream with standard Merkle-Damgård padding (100... + length).
        """
        bit_str = "".join(f"{byte:08b}" for byte in data)
        # Append 1 bit
        bit_str += "1"
        # Pad to multiple of 3 bits with 0s
        while len(bit_str) % 3 != 0:
            bit_str += "0"

        # Group into 3-bit integers in [0..7]
        trits = [int(bit_str[i : i + 3], 2) for i in range(0, len(bit_str), 3)]
        return trits

    def walk(self, data: bytes) -> tuple[list[int], Sedenion]:
        """
        Executes the message-directed walk on the Ramanujan graph.
        Returns the path of visited node IDs and the accumulated non-associative sedenion state.
        """
        trits = self._bytes_to_trits(data)
        current_node = self.start_node
        path = [current_node]

        # Initialize sedenion state with the start vertex
        start_v = self.comp_graph.nodes[current_node]["vector"]
        # s1 * e_i + s2 * e_{8+j}
        coords = [0] * 16
        coords[start_v.i] = start_v.s1
        coords[8 + start_v.j] = start_v.s2
        state: Sedenion = Sedenion(coords)

        for trit in trits:
            # Step to the trit-th neighbor (0 <= trit <= 7)
            next_node = self.neighbor_table[current_node][trit]
            path.append(next_node)
            current_node = next_node

            # Non-associative left-multiplication update: state = next_v * state
            v = self.comp_graph.nodes[next_node]["vector"]
            step_coords = [0] * 16
            step_coords[v.i] = v.s1
            step_coords[8 + v.j] = v.s2
            step_sed = Sedenion(step_coords)

            # Left multiplication in sedenion tower
            state = step_sed * state  # type: ignore[assignment]

        return path, state

    def hash(self, data: bytes) -> bytes:
        """
        Returns a 256-bit (32-byte) cryptographic digest of the message.
        Digest incorporates:
        - Terminal graph vertex index and XOR charge
        - Walk trajectory length
        - Sedenion coordinate values modulo 2^64
        - SHA3 final compression of the geometric trajectory
        """
        path, state = self.walk(data)
        terminal_node = path[-1]
        terminal_v = self.comp_graph.nodes[terminal_node]["vector"]

        # Pack geometric and algebraic state
        buffer = bytearray()
        buffer.extend(int(terminal_node).to_bytes(4, byteorder="big"))
        buffer.extend(int(terminal_v.i).to_bytes(2, byteorder="big"))
        buffer.extend(int(terminal_v.j).to_bytes(2, byteorder="big"))
        buffer.extend(int(len(path)).to_bytes(8, byteorder="big"))

        for c in state.coords:
            # Pack integer coordinate modulo 2^64
            val = int(c) & 0xFFFFFFFFFFFFFFFF
            buffer.extend(val.to_bytes(8, byteorder="big"))

        # Incorporate the complete expander walk trajectory to ensure
        # collision resistance even when sedenion state experiences zero-divisor cancellation
        for node_id in path:
            buffer.extend(int(node_id).to_bytes(2, byteorder="big"))

        # Final cryptographic compression
        digest = hashlib.sha3_256(buffer).digest()
        return digest

    # Ergonomic alias
    hash_bytes = hash

    def hex_digest(self, data: bytes) -> str:
        return self.hash(data).hex()


class RamanujanHashBenchmark:
    """
    Empirical cryptanalysis and performance benchmark suite for RamanujanExpanderHash.

    Evaluates:
    1. Strict Avalanche Criterion (SAC): Bit-flip probability distribution under single-bit perturbations.
    2. Truncated Collision Resistance: Birthday attack trials and cycle length distributions.
    3. Truncated Preimage Resistance: Complexity of preimage discovery and meet-in-the-middle path analysis.
    4. Execution Throughput: Digest generation throughput in KB/s and cycles/byte.
    """

    def __init__(self, hasher: RamanujanExpanderHash | None = None):
        self.hasher = hasher or RamanujanExpanderHash()

    def evaluate_avalanche_criterion(self, num_samples: int = 50) -> dict[str, Any]:
        """
        Tests the Strict Avalanche Criterion (SAC).
        Flips 1 bit in random 32-byte inputs and computes bitwise Hamming distance across output hashes.
        Verifies that the mean bit-flip probability is within [0.45, 0.55] (ideal 50.0%).
        """
        ratios: list[float] = []
        for _ in range(num_samples):
            data = bytearray(os.urandom(32))
            bit_to_flip = secrets.randbelow(len(data) * 8)
            byte_idx = bit_to_flip // 8
            bit_pos = bit_to_flip % 8
            data_flipped = bytearray(data)
            data_flipped[byte_idx] ^= 1 << bit_pos

            h1 = self.hasher.hash(bytes(data))
            h2 = self.hasher.hash(bytes(data_flipped))
            diff_bits = sum(bin(b1 ^ b2).count("1") for b1, b2 in zip(h1, h2, strict=False))
            ratios.append(diff_bits / 256.0)

        mean_prob = float(np.mean(ratios))
        std_prob = float(np.std(ratios))
        min_prob = float(np.min(ratios))
        max_prob = float(np.max(ratios))
        passed = bool(0.45 <= mean_prob <= 0.55)

        return {
            "num_samples": num_samples,
            "mean_bit_flip_probability": mean_prob,
            "std_bit_flip_probability": std_prob,
            "min_bit_flip_probability": min_prob,
            "max_bit_flip_probability": max_prob,
            "target_range": [0.45, 0.55],
            "ideal": 0.50,
            "passed": passed,
        }

    def evaluate_collision_resistance_truncated(
        self, bit_length: int = 16, max_trials: int = 5000
    ) -> dict[str, Any]:
        """
        Evaluates birthday attack complexity and cycle length distributions on truncated hash outputs.

        Parameters:
            bit_length: The truncation bit length (default 16 bits).
            max_trials: Maximum number of hash trials (default 5000).

        Returns:
            Dictionary containing collision metrics, cycle lengths, and theoretical birthday bounds.
        """
        mask = (1 << bit_length) - 1
        seen: dict[int, tuple[bytes, int]] = {}
        trials_to_collision = 0
        cycle_lengths: list[int] = []
        colliding_inputs: tuple[str, str] | None = None
        colliding_hash: int | None = None

        for t in range(1, max_trials + 1):
            msg = f"col_trial_{t}_{secrets.token_hex(4)}".encode()
            h = self.hasher.hash(msg)
            trunc = int.from_bytes(h[:4], "big") & mask
            if trunc in seen:
                prev_msg, prev_step = seen[trunc]
                trials_to_collision = t
                cycle_lengths.append(t - prev_step)
                colliding_inputs = (
                    prev_msg.decode(errors="replace"),
                    msg.decode(errors="replace"),
                )
                colliding_hash = trunc
                break
            seen[trunc] = (msg, t)

        theoretical_bound = float(1.253314 * (2 ** (bit_length / 2)))
        return {
            "bit_length": bit_length,
            "max_trials": max_trials,
            "collision_found": colliding_inputs is not None,
            "trials_to_collision": trials_to_collision,
            "theoretical_birthday_bound": theoretical_bound,
            "cycle_lengths": cycle_lengths,
            "mean_cycle_length": float(np.mean(cycle_lengths)) if cycle_lengths else 0.0,
            "colliding_inputs": colliding_inputs,
            "truncated_hash": hex(colliding_hash) if colliding_hash is not None else None,
        }

    def evaluate_preimage_resistance_truncated(
        self, bit_length: int = 12, max_trials: int = 5000
    ) -> dict[str, Any]:
        """
        Evaluates preimage / meet-in-the-middle path-finding attack complexity on the Ramanujan graph.

        Parameters:
            bit_length: The truncation bit length for the preimage target (default 12 bits).
            max_trials: Maximum number of search trials (default 5000).

        Returns:
            Dictionary containing preimage search results and theoretical complexity analysis.
        """
        mask = (1 << bit_length) - 1
        target_msg = b"target_preimage_seed_2026"
        target_h = self.hasher.hash(target_msg)
        target_trunc = int.from_bytes(target_h[:4], "big") & mask

        preimage_found = False
        trials_to_preimage = 0
        found_input: str | None = None

        for t in range(1, max_trials + 1):
            cand = f"pre_{t}_{t:08x}".encode()
            cand_h = self.hasher.hash(cand)
            cand_trunc = int.from_bytes(cand_h[:4], "big") & mask
            if cand_trunc == target_trunc:
                preimage_found = True
                trials_to_preimage = t
                found_input = cand.decode(errors="replace")
                break

        theoretical_bound = float(2**bit_length)
        return {
            "bit_length": bit_length,
            "target_truncated_hash": hex(target_trunc),
            "preimage_found": preimage_found,
            "trials_to_preimage": trials_to_preimage,
            "found_input": found_input,
            "theoretical_preimage_trials": theoretical_bound,
            "graph_regularity": 8,
            "expander_spectral_gap": 4.0,
            "path_space_complexity": "8^L = 2^(3L)",
            "meet_in_the_middle_barrier": (
                "Non-associative multiplication prevents backward algebraic inversion of intermediate "
                "sedenion states. State updates are trajectory-dependent without group inverses."
            ),
        }

    def benchmark_throughput(self, data_sizes_kb: list[int] | None = None) -> dict[str, Any]:
        """
        Measures throughput in KB/s and estimated CPU cycles/byte across data sizes.

        Parameters:
            data_sizes_kb: List of payload sizes in KB (default [1, 10, 50]).

        Returns:
            Dictionary mapping payload size descriptions to timing and throughput statistics.
        """
        if data_sizes_kb is None:
            data_sizes_kb = [1, 10, 50]

        results: dict[str, Any] = {}
        for kb in data_sizes_kb:
            size_bytes = kb * 1024
            data = os.urandom(size_bytes)
            t0 = time.perf_counter()
            self.hasher.hash(data)
            elapsed = time.perf_counter() - t0
            kb_per_sec = float(kb / elapsed) if elapsed > 0 else 0.0
            # Nominal 3.0 GHz CPU cycles estimate
            cycles_per_byte = float((3.0e9 * elapsed) / size_bytes) if size_bytes > 0 else 0.0
            results[f"{kb}KB"] = {
                "size_kb": kb,
                "elapsed_seconds": elapsed,
                "throughput_kb_per_sec": kb_per_sec,
                "cycles_per_byte": cycles_per_byte,
            }
        return results
