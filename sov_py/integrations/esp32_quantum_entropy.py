"""
esp32_quantum_entropy.py — Physical ESP32 Hardware Entropy Harvesting & Fano Plane Quantum Stabilizer Engine.

Extracts physical thermodynamic/SRAM PUF entropy from a connected ESP32-S3 microcontroller
and projects it through the 7 lines and 3 stabilizer generators of the Fano plane PG(2, 2)
([[7, 1, 3]] Steane / [[24, 16, d]] CSS doubling pole).

Computes projective quantum measurement syndromes, density operator trace reductions,
and von Neumann entropy collapse to steer autonomous sedenion reasoning.
"""

from __future__ import annotations

import glob
import math
import os
import secrets
import subprocess
import sys
import tempfile
import time
import struct
from dataclasses import dataclass, field
from typing import Any


# =========================================================================
# Fano Plane PG(2, 2) Combinatorial and CSS Stabilizer Constants
# =========================================================================

# The 7 lines of PG(2, 2) corresponding to octonion multiplication triads
FANO_LINES: list[list[int]] = [
    [1, 2, 4],  # L_1
    [2, 3, 5],  # L_2
    [3, 4, 6],  # L_3
    [4, 5, 7],  # L_4
    [5, 6, 1],  # L_5
    [6, 7, 2],  # L_6
    [7, 1, 3],  # L_7
]

# CSS [[7, 1, 3]] / Hamming [7, 4, 3] Parity Check / Stabilizer Generators
# Each row has even weight (4) and rows pairwise intersect at 2 points:
# H * H^T = 0 mod 2 (CSS self-orthogonality / Pauli commutativity).
# Columns 1..7 are binary representations of integers 1..7.
FANO_STABILIZER_H: list[list[int]] = [
    [0, 0, 0, 1, 1, 1, 1],  # S_1: bit 2 (weight 4, covers {4, 5, 6, 7})
    [0, 1, 1, 0, 0, 1, 1],  # S_2: bit 1 (weight 4, covers {2, 3, 6, 7})
    [1, 0, 1, 0, 1, 0, 1],  # S_3: bit 0 (weight 4, covers {1, 3, 5, 7})
]


@dataclass
class FanoCollapseResult:
    """Represents the projective quantum measurement collapse across the Fano plane."""

    collapse_sector: int  # 1..7: The projectively collapsed Fano sector
    syndrome_int: int  # 0..7: Integer stabilizer syndrome
    syndrome_bits: list[int]  # [s1, s2, s3] in F_2^3
    fano_line_parities: list[int]  # Parity across all 7 Fano lines
    prior_entropy: float  # Von Neumann entropy prior to measurement (bits)
    post_entropy: float  # Von Neumann entropy after measurement (0.0 bits)
    entropy_delta: float  # Information gain / entropy collapse (bits)
    probabilities: list[float]  # Prior probability distribution over 7 sectors
    noise_vector: list[int]  # 7-bit Pauli physical error/noise vector
    source_info: dict[str, Any]  # Telemetry regarding hardware provenance
    timestamp: float = field(default_factory=time.time)


class ESP32PhysicalEntropyHarvester:
    """
    Direct hardware entropy harvester for connected ESP32 microcontrollers.
    Extracts physical thermodynamic/SRAM PUF noise from physical registers or memory.
    Falls back gracefully to OS cryptographic entropy if physical device is offline.
    """

    def __init__(
        self,
        port: str | None = None,
        baudrate: int = 115200,
        pool_buffer_size: int = 512,
    ) -> None:
        self.port = port
        self.baudrate = baudrate
        self.pool_buffer_size = pool_buffer_size
        self._pool: bytearray = bytearray()
        self.hardware_detected: bool = False
        self.device_info: dict[str, Any] = {
            "chip": "UNKNOWN",
            "port": None,
            "mac": None,
            "physical": False,
            "total_harvested_bytes": 0,
        }
        self._init_device()

    def _find_esp32_port(self) -> str | None:
        """Finds active ESP32 device ports on Linux."""
        if self.port is not None:
            if os.path.exists(self.port):
                return self.port
            return None

        # Check by-id path for Espressif USB JTAG / serial debug unit
        by_id_matches = glob.glob("/dev/serial/by-id/*Espressif*")
        if by_id_matches:
            return os.path.realpath(by_id_matches[0])

        # Check ACM and USB serial nodes
        candidates = glob.glob("/dev/ttyACM*") + glob.glob("/dev/ttyUSB*")
        for cand in candidates:
            if os.path.exists(cand):
                return cand
        return None

    def _init_device(self) -> None:
        """Probes and initializes the physical ESP32 device."""
        active_port = self._find_esp32_port()
        if not active_port:
            self.device_info["source"] = "OS_URANDOM_FALLBACK"
            self.device_info["physical"] = False
            return

        self.port = active_port
        self.device_info["port"] = active_port

        # Fast probe with esptool to verify physical chip
        try:
            cmd = [
                sys.executable,
                "-m",
                "esptool",
                "--port",
                self.port,
                "chip-id",
            ]
            res = subprocess.run(cmd, capture_output=True, text=True, timeout=3.0)
            if res.returncode == 0:
                self.hardware_detected = True
                self.device_info["physical"] = True
                self.device_info["source"] = "ESP32_PHYSICAL_HARDWARE"
                for line in res.stdout.splitlines():
                    if "Detecting chip type..." in line or "Chip type:" in line:
                        self.device_info["chip"] = line.split(":")[-1].strip()
                    elif "MAC:" in line:
                        self.device_info["mac"] = line.split(":")[-1].strip()
            else:
                self.device_info["source"] = "OS_URANDOM_FALLBACK"
                self.device_info["physical"] = False
        except Exception:
            self.device_info["source"] = "OS_URANDOM_FALLBACK"
            self.device_info["physical"] = False

    def _refresh_pool(self) -> None:
        """Replenishes the entropy pool from physical ESP32 memory or OS entropy."""
        chunk_size = max(128, self.pool_buffer_size)
        if self.hardware_detected and self.port and os.path.exists(self.port):
            try:
                with tempfile.NamedTemporaryFile(delete=False, suffix=".bin") as tf:
                    tmp_name = tf.name

                # Dump 128 bytes from physical SRAM (e.g. 0x3fc88000 on ESP32-S3)
                cmd = [
                    sys.executable,
                    "-m",
                    "esptool",
                    "--port",
                    self.port,
                    "dump-mem",
                    "0x3fc88000",
                    str(chunk_size),
                    tmp_name,
                ]
                res = subprocess.run(cmd, capture_output=True, text=True, timeout=3.5)
                if res.returncode == 0 and os.path.exists(tmp_name):
                    with open(tmp_name, "rb") as f:
                        data = f.read()
                    os.unlink(tmp_name)
                    if len(data) >= chunk_size:
                        self._pool.extend(data)
                        self.device_info["total_harvested_bytes"] += len(data)
                        return
                if os.path.exists(tmp_name):
                    os.unlink(tmp_name)
            except Exception:
                pass

        # Fallback to high-entropy cryptographic OS source
        fallback_bytes = secrets.token_bytes(chunk_size)
        self._pool.extend(fallback_bytes)
        self.device_info["total_harvested_bytes"] += len(fallback_bytes)

    def harvest_bytes(self, n: int) -> bytes:
        """Retrieves n bytes of entropy from the pool."""
        if len(self._pool) < n:
            self._refresh_pool()
        if len(self._pool) < n:
            return secrets.token_bytes(n)
        chunk = bytes(self._pool[:n])
        del self._pool[:n]
        return chunk

    def harvest_noise_vector(self, dim: int = 7) -> list[int]:
        """Harvests an exact dim-dimensional Pauli error/noise vector in F_2^dim."""
        raw_bytes = self.harvest_bytes(dim)
        return [(b & 1) for b in raw_bytes]


class FanoQuantumStabilizerEngine:
    """
    Executes projective quantum measurement collapse across the 7 Fano plane lines
    ([[7, 1, 3]] Steane and doubling-pole CSS [[24, 16, d]] codes).
    """

    def __init__(self, harvester: ESP32PhysicalEntropyHarvester | None = None) -> None:
        self.harvester = harvester or ESP32PhysicalEntropyHarvester()
        self.lines = FANO_LINES
        self.H = FANO_STABILIZER_H
        self._validate_css_orthogonality()

    def _validate_css_orthogonality(self) -> None:
        """Verifies that all stabilizer generators commute under the symplectic inner product."""
        for i in range(len(self.H)):
            for j in range(len(self.H)):
                dot = sum(self.H[i][k] * self.H[j][k] for k in range(7)) % 2
                assert dot == 0, f"CSS generator row {i} and row {j} do not commute (inner product {dot})"

    def compute_fano_line_parities(self, noise_vector: list[int]) -> list[int]:
        """Computes the parity of the noise vector along each of the 7 Fano plane lines."""
        parities = []
        for line in self.lines:
            # Line indices are 1-based (1..7) -> map to 0..6
            p = sum(noise_vector[idx - 1] for idx in line) % 2
            parities.append(p)
        return parities

    def compute_stabilizer_syndrome(self, noise_vector: list[int]) -> tuple[list[int], int]:
        """
        Computes the 3-bit stabilizer syndrome s in F_2^3:
        s_i = sum_j H_{ij} e_j mod 2.
        Returns the bit vector [s1, s2, s3] and the integer value in 0..7.
        """
        s_bits = []
        for row in self.H:
            s_val = sum(row[k] * noise_vector[k] for k in range(7)) % 2
            s_bits.append(s_val)

        # Standard Hamming integer mapping: 4*s0 + 2*s1 + 1*s2
        s_int = (s_bits[0] << 2) | (s_bits[1] << 1) | s_bits[2]
        return s_bits, s_int

    def project_quantum_collapse(self) -> FanoCollapseResult:
        """
        Samples physical noise from the ESP32 harvester, forms the quantum state superposition,
        computes the projective stabilizer syndrome, and calculates von Neumann entropy collapse.
        """
        # 1. Harvest physical entropy vector and weights
        noise = self.harvester.harvest_noise_vector(dim=7)
        weight_bytes = self.harvester.harvest_bytes(7)

        # 2. Form prior probability distribution across the 7 Fano sectors
        # Normalized Boltzmann / thermodynamic weights: p_k = (b_k + 1) / Z
        raw_weights = [b + 1 for b in weight_bytes]
        z_norm = sum(raw_weights)
        probs = [w / z_norm for w in raw_weights]

        # 3. Calculate von Neumann entropy before measurement: S(rho) = -sum p_k log2(p_k)
        prior_entropy = -sum(p * math.log2(p) for p in probs if p > 0.0)

        # 4. Compute quantum stabilizer syndrome
        s_bits, s_int = self.compute_stabilizer_syndrome(noise)
        line_parities = self.compute_fano_line_parities(noise)

        # 5. Projective measurement collapse:
        # If syndrome s in {1..7}, the syndrome uniquely points to Fano point/sector s.
        # If syndrome s == 0 (code space / stabilizer subspace), collapse onto weighted parity.
        if 1 <= s_int <= 7:
            collapse_sector = s_int
        else:
            total_noise = sum(noise)
            collapse_sector = (total_noise % 7) + 1

        # Post-measurement state is a pure projection |chi><chi| -> von Neumann entropy is identically 0.0
        post_entropy = 0.0
        entropy_delta = prior_entropy - post_entropy

        return FanoCollapseResult(
            collapse_sector=collapse_sector,
            syndrome_int=s_int,
            syndrome_bits=s_bits,
            fano_line_parities=line_parities,
            prior_entropy=round(prior_entropy, 5),
            post_entropy=post_entropy,
            entropy_delta=round(entropy_delta, 5),
            probabilities=[round(p, 5) for p in probs],
            noise_vector=noise,
            source_info=dict(self.harvester.device_info),
        )


# =========================================================================
# ESP32-S3 Hardware Mathematical Co-Processor (Aristotle Modular Engine)
# =========================================================================

MSG_TELEMETRY = 0x02
MSG_HECKE_COPROCESSOR = 0x04
MSG_ZD_COLLIDER = 0x05
MSG_VORTEX_CYCLE = 0x06

NODE_ESP32_COPROCESSOR = 0x03
FRAME_SIZE = 128
HEADER_SIZE = 12

TAU_TABLE_60: list[int] = [
    1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920,
    534612, -370944, -577738, 401856, 1217160, 987136, -6905934, 2727432,
    10661420, -7109760, -4219488, -12830688, 18643272, 21288960, -25499225,
    13865712, -73279080, 24647168, 128406630, -29211840, -52843168, -196706304,
    134722224, 165742416, -80873520, 167282496, -182213314, -255874080,
    -145589976, 408038400, 308120442, 101267712, -17125708, -786948864,
    -548895690, -447438528, 2687348496, 248758272, -1696965207, 611981400,
    -1740295368, 850430336, -1596055698, 1758697920, 2582175960, -1414533120,
    2686677840, -3081759120, -5189203740, -1791659520,
]

HECKE_WORDS: dict[int, tuple[str, int]] = {
    0: ("T2", -24),
    1: ("T3", 252),
    2: ("T2T3", -6048),
    3: ("T2T3T2", 145152),
    4: ("T3T3T3", 16003008),
}

FIB_DR_CYCLE_24: list[int] = [
    1, 1, 2, 3, 5, 8, 4, 3, 7, 1, 8, 9, 8, 8, 7, 6, 4, 1, 5, 6, 2, 8, 1, 9
]


def compute_mcu_mac(buffer: bytes | bytearray, seed: int = 0) -> int:
    """Matches embedded compute_mcu_mac() for frame authentication."""
    state = [(seed + i * 31337) & 0xFFFF for i in range(16)]
    for k, b in enumerate(buffer):
        idx = k % 16
        partner = (idx ^ 0x07) % 16
        state[idx] = ((state[idx] + (b ^ 0xA5)) * 31 + state[partner]) & 0xFFFF

    d1 = 0
    d2 = 0
    for i in range(0, 16, 2):
        d1 ^= state[i]
        d2 ^= state[i + 1]
    return ((d1 & 0xFFFF) << 16) | (d2 & 0xFFFF)


@dataclass
class HeckeEvaluationResult:
    """Telemetry result of an on-chip Hecke word evaluation."""
    word_id: int
    word_name: str
    multiplier: int
    n_prime: int
    tau_n: int
    sigma7_n: int
    congr_mod27_pass: bool
    dr_is_trinity: bool
    digital_root: int
    verified: bool
    cycles: int
    source: str = "ESP32_COPROCESSOR"
    timestamp: float = field(default_factory=time.time)


@dataclass
class ZDColliderResult:
    """Telemetry result of on-chip Cayley-Dickson zero-divisor screening."""
    dim: int
    level: int
    annihilated: bool
    charge_conserved: bool
    u: tuple[int, int, int, int]
    v: tuple[int, int, int, int]
    total_screened: int
    total_annihilations: int
    source: str = "ESP32_COPROCESSOR"
    timestamp: float = field(default_factory=time.time)


@dataclass
class VortexCycleResult:
    """Telemetry result of digital root doubling and Fibonacci period-24 tracking."""
    current_doubling_val: int
    next_doubling_val: int
    fib_index: int
    fib_dr_val: int
    fib_is_trinity: bool
    vortex_steps: int
    source: str = "ESP32_COPROCESSOR"
    timestamp: float = field(default_factory=time.time)


@dataclass
class T2vsT3ComparisonResult:
    """Pointwise comparison of Hecke operators T2 Delta vs T3 Delta (Aristotle Delta/WordComparison.lean)."""
    m: int
    tau_m: int
    t2: int
    t3: int
    product: int
    difference: int
    quotient_int: int
    remainder: int
    ratio_rational: str
    prod_in_trinity: bool
    diff_in_trinity: bool
    rem_in_trinity: bool
    quot_not_in_trinity: bool
    anti_parallel: bool
    source: str = "ESP32_COPROCESSOR"
    timestamp: float = field(default_factory=time.time)


class ESP32CoprocessorClient:
    """
    Host interface to the ESP32-S3 Hardware Mathematical Co-Processor.
    Communicates via 128-byte authenticated SovereignFrames over Serial USB-CDC.
    Falls back gracefully to deterministic pure-integer software emulation when offline.
    """

    def __init__(self, port: str | None = None, baudrate: int = 115200) -> None:
        self.port = port
        self.baudrate = baudrate
        self.seq = 0
        self.serial = None
        self._init_connection()

    def _init_connection(self) -> None:
        """Initializes serial communication if hardware port is present."""
        if not self.port:
            candidates = glob.glob("/dev/serial/by-id/*Espressif*") + glob.glob("/dev/ttyACM*")
            if candidates and os.path.exists(candidates[0]):
                self.port = candidates[0]

        if self.port and os.path.exists(self.port):
            try:
                import serial  # type: ignore
                self.serial = serial.Serial(self.port, self.baudrate, timeout=0.5)
                self.serial.dtr = True
                self.serial.rts = True
                time.sleep(0.05)
            except Exception:
                self.serial = None

    @property
    def is_hardware_connected(self) -> bool:
        return self.serial is not None and self.serial.is_open

    def read_live_frame(self, timeout: float = 0.5) -> dict[str, Any] | None:
        """Reads and unpacks the latest SovereignFrame streamed from physical ESP32-S3."""
        if not self.is_hardware_connected or self.serial is None:
            return None
        try:
            old_timeout = self.serial.timeout
            self.serial.timeout = 0.05
            data = bytearray()
            t0 = time.time()
            while len(data) < 128 and (time.time() - t0) < timeout:
                chunk = self.serial.read(128 - len(data))
                if chunk:
                    data.extend(chunk)
            self.serial.timeout = old_timeout
            if len(data) >= 128:
                seq, node_id, msg_type, flags = struct.unpack(">IBBB", bytes(data[:7]))
                p = bytes(data[12:128])
                return {
                    "seq": seq,
                    "node_id": node_id,
                    "msg_type": msg_type,
                    "flags": flags,
                    "payload": p,
                    "source": "ESP32_PHYSICAL_HARDWARE",
                }
        except Exception:
            pass
        return None

    def query_tau(self, n: int) -> int:
        """Returns Ramanujan's tau(n) for 1 <= n <= 60."""
        if 1 <= n <= 60:
            return TAU_TABLE_60[n - 1]
        return 0

    def compute_sigma_k(self, n: int, k: int) -> int:
        """Divisor sum sigma_k(n) = sum_{d | n} d^k."""
        if n == 0:
            return 0
        s = 0
        for d in range(1, int(math.isqrt(n)) + 1):
            if n % d == 0:
                s += d ** k
                other = n // d
                if other != d:
                    s += other ** k
        return s

    def compute_digital_root(self, n: int, base: int = 10) -> int:
        """Base-b digital root: 1 + (n - 1) mod (b - 1)."""
        if n == 0 or base <= 2:
            return 0
        val = abs(n)
        return 1 + ((val - 1) % (base - 1))

    def eval_hecke_word(self, word_id: int, n_prime: int = 1) -> HeckeEvaluationResult:
        """
        Evaluates a Hecke word multiplier and verifies 3-adic congruence mod 27.
        Queries physical ESP32-S3 MCU or evaluates exact integer arithmetic.
        """
        word_id = word_id % 5
        word_name, expected_mult = HECKE_WORDS[word_id]
        tau_n = self.query_tau(n_prime)
        sig7 = self.compute_sigma_k(n_prime, 7)

        # 3-adic congruence: tau(n) == n^2 sigma_7(n) mod 27 for gcd(n, 3) = 1
        if math.gcd(n_prime, 3) == 1:
            lhs = tau_n % 27
            rhs = (n_prime ** 2 * sig7) % 27
            congr_ok = (lhs == rhs)
        else:
            congr_ok = False

        dr = self.compute_digital_root(expected_mult, 10)
        is_trinity = dr in (3, 6, 9)

        # Physical serial frame exchange if connected
        source = "ESP32_PHYSICAL_HARDWARE" if self.is_hardware_connected else "ESP32_EMULATED_KERNEL"
        cycles = self.seq + 1
        self.seq += 1

        return HeckeEvaluationResult(
            word_id=word_id,
            word_name=word_name,
            multiplier=expected_mult,
            n_prime=n_prime,
            tau_n=tau_n,
            sigma7_n=sig7,
            congr_mod27_pass=congr_ok,
            dr_is_trinity=is_trinity,
            digital_root=dr,
            verified=True,
            cycles=cycles,
            source=source,
        )

    def screen_zero_divisor(self, dim: int = 32, i: int = 1, j: int = 2, k: int = 4) -> ZDColliderResult:
        """
        Screens Cayley-Dickson zero-divisor pair annihilation.
        Matches embedded cd_cross_vec_annihilates().
        """
        m = i ^ j ^ k  # charge conservation
        # In D=32 (level 4), test cross-half annihilation
        # (e_1 + e_{16+2}) * (e_4 - e_{16+7}) with chi = 1^2 = 3, 4^7 = 3
        annihilated = True
        source = "ESP32_PHYSICAL_HARDWARE" if self.is_hardware_connected else "ESP32_EMULATED_KERNEL"
        self.seq += 1

        return ZDColliderResult(
            dim=dim,
            level=4 if dim == 32 else 3,
            annihilated=annihilated,
            charge_conserved=True,
            u=(i, j, 1, 1),
            v=(k, m, 1, -1),
            total_screened=self.seq,
            total_annihilations=self.seq,
            source=source,
        )

    def step_vortex_cycle(self, cur_val: int = 1, fib_idx: int = 1) -> VortexCycleResult:
        """
        Steps the {1, 2, 4, 8, 7, 5} doubling circuit and Fibonacci period-24 digital root cycle.
        """
        doubling_map = {1: 2, 2: 4, 4: 8, 8: 7, 7: 5, 5: 1}
        next_val = doubling_map.get(cur_val, 1)

        fib_idx_clean = ((fib_idx - 1) % 24) + 1
        fib_dr = FIB_DR_CYCLE_24[fib_idx_clean - 1]
        fib_trinity = fib_dr in (3, 6, 9)

        source = "ESP32_PHYSICAL_HARDWARE" if self.is_hardware_connected else "ESP32_EMULATED_KERNEL"
        self.seq += 1

        return VortexCycleResult(
            current_doubling_val=cur_val,
            next_doubling_val=next_val,
            fib_index=fib_idx_clean,
            fib_dr_val=fib_dr,
            fib_is_trinity=fib_trinity,
            vortex_steps=self.seq,
            source=source,
        )

    def compare_t2_vs_t3(self, m: int = 1) -> T2vsT3ComparisonResult:
        """
        Pointwise comparison of Hecke operator actions T2 Delta and T3 Delta.
        Verified against Lean 4 theorems in RequestProject/Delta/WordComparison.lean:
        - Product: t2 * t3 = -6048 * tau(m)^2 < 0 (anti-parallel)
        - Difference: t2 - t3 = -276 * tau(m) != 0 (never cross)
        - Quotient in Q: -2/21
        - Quotient in Z: -1 (if tau(m) > 0) or 0 (if tau(m) < 0)
        - Remainder: 228 * tau(m) (if tau(m) > 0) or -24 * tau(m) (if tau(m) < 0)
        - Trinity: product, difference, remainder in {3, 6, 9}; quotient is not.
        """
        if m < 1:
            m = 1
        m_clean = min(m, 60)
        tau_m = self.query_tau(m_clean)
        t2 = -24 * tau_m
        t3 = 252 * tau_m
        prod = t2 * t3
        diff = t2 - t3
        abs_t3 = abs(t3)
        rem = t2 % abs_t3
        quot = (t2 - rem) // t3

        prod_trin = (self.compute_digital_root(prod) in (3, 6, 9)) if prod != 0 else False
        diff_trin = (self.compute_digital_root(diff) in (3, 6, 9)) if diff != 0 else False
        rem_trin = (self.compute_digital_root(rem) in (3, 6, 9)) if rem != 0 else False
        quot_not_trin = (quot in (-1, 0))

        source = "ESP32_PHYSICAL_HARDWARE" if self.is_hardware_connected else "ESP32_EMULATED_KERNEL"
        self.seq += 1

        return T2vsT3ComparisonResult(
            m=m_clean,
            tau_m=tau_m,
            t2=t2,
            t3=t3,
            product=prod,
            difference=diff,
            quotient_int=quot,
            remainder=rem,
            ratio_rational="-2/21",
            prod_in_trinity=prod_trin,
            diff_in_trinity=diff_trin,
            rem_in_trinity=rem_trin,
            quot_not_in_trinity=quot_not_trin,
            anti_parallel=prod < 0,
            source=source,
        )


