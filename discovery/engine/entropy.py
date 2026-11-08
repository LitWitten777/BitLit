"""Entropy pool for the discovery loop.

Raw samples come from one or more *sources*:

* ``os.urandom`` (always available);
* a byte stream from a device or file, e.g. the ESP32-S3 USB-serial stream produced by
  ``discovery/firmware/esp32s3_entropy_stream.ino`` (``--entropy-device /dev/ttyACM0``).

Each source's raw bytes go through the two continuous health tests of NIST SP 800-90B §4.4
(repetition count test and adaptive proportion test) under a *declared* min-entropy per byte.
A source that fails is dropped from the pool (it is never silently trusted).  The surviving
bytes are conditioned with SHA-256 into a 256-bit seed, which keys an HMAC-DRBG
(SP 800-90A, HMAC-SHA-256).  The DRBG drives every random choice of the loop.

The seed is recorded in the run ledger, so any run can be replayed exactly with
``--seed-hex``.  Entropy decides *which* conjectures are explored, never whether a claim is
accepted: acceptance is decided by the Lean kernel alone.
"""

from __future__ import annotations

import hashlib
import hmac
import math
import os
import random
from dataclasses import dataclass, field


# ---------------------------------------------------------------------------
# SP 800-90B continuous health tests
# ---------------------------------------------------------------------------

ALPHA_EXP = 20  # false-positive probability 2^-20 per test, as recommended in SP 800-90B


def rct_cutoff(h: float) -> int:
    """Repetition count test cutoff ``C = 1 + ceil(20 / H)`` (SP 800-90B §4.4.1)."""
    return 1 + math.ceil(ALPHA_EXP / h)


def apt_cutoff(h: float, window: int = 512) -> int:
    """Adaptive proportion test cutoff (SP 800-90B §4.4.2): the smallest ``C`` with
    ``P[Binomial(W, 2^-H) >= C] <= 2^-20`` (capped at ``W``)."""
    p = 2.0 ** (-h)
    alpha = 2.0 ** (-ALPHA_EXP)
    if p >= 1.0:
        return window
    logs = [
        math.lgamma(window + 1) - math.lgamma(k + 1) - math.lgamma(window - k + 1)
        + k * math.log(p) + (window - k) * math.log1p(-p)
        for k in range(window + 1)
    ]
    tail = 0.0
    for c in range(window, -1, -1):
        new_tail = tail + math.exp(logs[c])
        if new_tail > alpha:
            return min(window, c + 1)
        tail = new_tail
    return 1


def repetition_count_test(samples: bytes, h: float) -> bool:
    """True iff no value repeats ``rct_cutoff(h)`` or more times in a row."""
    cutoff = rct_cutoff(h)
    run = 0
    prev = None
    for b in samples:
        run = run + 1 if b == prev else 1
        prev = b
        if run >= cutoff:
            return False
    return True


def adaptive_proportion_test(samples: bytes, h: float, window: int = 512) -> bool:
    """True iff, in every complete window of ``window`` samples, the first sample of the window
    occurs fewer than ``apt_cutoff(h, window)`` times."""
    cutoff = apt_cutoff(h, window)
    for start in range(0, len(samples) - window + 1, window):
        w = samples[start:start + window]
        if w.count(w[0]) >= cutoff:
            return False
    return True


# ---------------------------------------------------------------------------
# Sources
# ---------------------------------------------------------------------------

@dataclass
class SourceReport:
    name: str
    declared_h_per_byte: float
    n_bytes: int
    rct_ok: bool
    apt_ok: bool
    credited_bits: float
    note: str = ""

    @property
    def healthy(self) -> bool:
        return self.rct_ok and self.apt_ok and self.n_bytes > 0


class Source:
    name = "abstract"
    declared_h = 1.0

    def read(self, n: int) -> bytes:  # pragma: no cover - interface
        raise NotImplementedError


class OsUrandomSource(Source):
    name = "os.urandom"
    declared_h = 7.5  # conservative declaration for the OS CSPRNG

    def read(self, n: int) -> bytes:
        return os.urandom(n)


class StreamSource(Source):
    """Raw bytes from a character device or file (ESP32-S3 serial stream, captured dump, ...).

    ``declared_h`` is the min-entropy per byte that the operator vouches for; for the ADC
    least-significant-bit stream of the ESP32 firmware a cautious value is 1 bit per byte.
    """

    def __init__(self, path: str, declared_h: float = 1.0):
        self.path = path
        self.name = f"stream:{path}"
        self.declared_h = declared_h

    def read(self, n: int) -> bytes:
        with open(self.path, "rb", buffering=0) as f:
            out = bytearray()
            while len(out) < n:
                chunk = f.read(n - len(out))
                if not chunk:
                    break
                out.extend(chunk)
        return bytes(out)


class BytesSource(Source):
    """Fixed bytes (for tests and for replaying a captured hardware dump)."""

    def __init__(self, data: bytes, declared_h: float = 1.0, name: str = "bytes"):
        self.data = data
        self.declared_h = declared_h
        self.name = name

    def read(self, n: int) -> bytes:
        return self.data[:n]


# ---------------------------------------------------------------------------
# HMAC-DRBG (SP 800-90A, HMAC-SHA-256), without reseed-counter enforcement
# ---------------------------------------------------------------------------

class HmacDrbg:
    def __init__(self, seed: bytes, personalization: bytes = b""):
        self.K = b"\x00" * 32
        self.V = b"\x01" * 32
        self._update(seed + personalization)

    @staticmethod
    def _hmac(key: bytes, data: bytes) -> bytes:
        return hmac.new(key, data, hashlib.sha256).digest()

    def _update(self, data: bytes = b"") -> None:
        self.K = self._hmac(self.K, self.V + b"\x00" + data)
        self.V = self._hmac(self.K, self.V)
        if data:
            self.K = self._hmac(self.K, self.V + b"\x01" + data)
            self.V = self._hmac(self.K, self.V)

    def generate(self, n: int) -> bytes:
        out = bytearray()
        while len(out) < n:
            self.V = self._hmac(self.K, self.V)
            out.extend(self.V)
        self._update()
        return bytes(out[:n])


class DrbgRandom(random.Random):
    """``random.Random`` whose bits come from an ``HmacDrbg``, so every helper of the standard
    ``random`` API (``choice``, ``randrange``, ``shuffle``, ...) is driven by the pool."""

    def __init__(self, seed: bytes):
        self._drbg = HmacDrbg(seed)
        super().__init__(0)

    def seed(self, a=None, version=2):  # the DRBG is keyed once, in __init__
        pass

    def getrandbits(self, k: int) -> int:
        if k <= 0:
            return 0
        nbytes = (k + 7) // 8
        x = int.from_bytes(self._drbg.generate(nbytes), "big")
        return x >> (nbytes * 8 - k)

    def random(self) -> float:
        return self.getrandbits(53) / float(1 << 53)

    def getstate(self):
        return (self._drbg.K, self._drbg.V)

    def setstate(self, state):
        self._drbg.K, self._drbg.V = state


# ---------------------------------------------------------------------------
# Pool
# ---------------------------------------------------------------------------

@dataclass
class EntropySeed:
    seed: bytes
    reports: list = field(default_factory=list)
    replayed: bool = False

    @property
    def hex(self) -> str:
        return self.seed.hex()

    @property
    def credited_bits(self) -> float:
        return min(256.0, sum(r.credited_bits for r in self.reports if r.healthy))

    def summary(self) -> dict:
        return {
            "seed_hex": self.hex,
            "replayed": self.replayed,
            "credited_bits": self.credited_bits,
            "sources": [dict(r.__dict__, healthy=r.healthy) for r in self.reports],
        }

    def rng(self) -> DrbgRandom:
        return DrbgRandom(self.seed)


def harvest(sources: list, n_bytes: int = 4096) -> EntropySeed:
    """Read ``n_bytes`` from every source, health-test them and condition the healthy ones with
    SHA-256.  Raises ``RuntimeError`` if no source is healthy."""
    reports = []
    h = hashlib.sha256(b"QBX-discovery-pool-v1")
    for src in sources:
        try:
            data = src.read(n_bytes)
            note = ""
        except OSError as e:
            data, note = b"", f"read failed: {e}"
        rct = repetition_count_test(data, src.declared_h)
        apt = adaptive_proportion_test(data, src.declared_h)
        healthy = rct and apt and len(data) > 0
        rep = SourceReport(src.name, src.declared_h, len(data), rct, apt,
                           credited_bits=src.declared_h * len(data) if healthy else 0.0,
                           note=note)
        reports.append(rep)
        if healthy:
            h.update(len(src.name).to_bytes(2, "big") + src.name.encode())
            h.update(len(data).to_bytes(4, "big") + data)
    if not any(r.healthy for r in reports):
        raise RuntimeError("no healthy entropy source: " + repr([r.__dict__ for r in reports]))
    return EntropySeed(h.digest(), reports)


def replay(seed_hex: str) -> EntropySeed:
    """The pool state of an earlier run, from the seed recorded in its ledger."""
    return EntropySeed(bytes.fromhex(seed_hex), [], replayed=True)
