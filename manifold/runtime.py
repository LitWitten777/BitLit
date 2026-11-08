"""The running manifold: a tick engine with start / stop / speed, self-healing and self-tuning.

Per tick the governor (controller.py, proved in Control.lean) sets the speed = number of 64-sample
blocks processed.  Per block:

 1. **store**   bytes -> cells of Q6 with the [6,3,3] code (heal.py, Heal.lean);
 2. **attack**  the Adversarial Critic flips bits; **heal** repairs single flips per cell;
 3. **split**   samples -> Walsh spectrum (spectrum.py, Spectrum.lean), band energies by
                shells / Hopf fibres / octaves;
 4. **shape**   denoise (threshold tuned by the Structural Engineer), chip away / blow up bands;
 5. **double**  if two consecutive blocks resonate (nearly equal), join them by Cayley-Dickson
                doubling: the spectrum of (a, b) is (A + B, A - B); when the A - B half carries
                < 1 % of the energy it is dropped (2:1 compression, error = dropped energy / 128);
 6. **join**    back to samples and bytes; the Pipeline Auditor checks the invariants
                (lossless split/join, band energies add up, speed <= vmax, replicas agree) and
                triggers self-healing on any violation.

The control state is kept in three replicas; a corrupted replica is repaired by bitwise majority
(Heal.lean `maj_heals`).
"""
import math
import random
import threading
import time

from . import agents as agents_mod
from . import heal, spectrum
from .controller import Governor


# ------------------------------------------------------------------ sources
class Source:
    """A stream of bytes, optionally with a clean reference (for measuring quality)."""
    has_reference = False

    def next_block(self, n=64):
        raise NotImplementedError


class BytesSource(Source):
    def __init__(self, data, loop=True):
        self.data, self.pos, self.loop = bytes(data) or b"\0", 0, loop

    def next_block(self, n=64):
        out = bytearray()
        while len(out) < n:
            if self.pos >= len(self.data):
                if not self.loop:
                    out += bytes(n - len(out))
                    break
                self.pos = 0
            take = self.data[self.pos:self.pos + n - len(out)]
            out += take
            self.pos += len(take)
        return bytes(out), None


class TextSource(BytesSource):
    def __init__(self, text, loop=True):
        super().__init__(text.encode("utf-8"), loop)


class SyntheticSource(Source):
    """Slowly drifting structured signal (two Walsh tones + a sinusoid) plus Gaussian noise."""
    has_reference = True

    def __init__(self, noise=12.0, seed=3, repeat=0.0):
        self.rnd, self.noise, self.t, self.repeat = random.Random(seed), noise, 0, repeat
        self.last = None

    def next_block(self, n=64):
        if self.last is not None and self.rnd.random() < self.repeat:
            clean = self.last
        else:
            clean = []
            for i in range(n):
                k = self.t + i
                v = 40 * (-1) ** bin(i & 0b000011).count("1") + 25 * (-1) ** bin(i & 0b010100).count("1")
                v += 20 * math.sin(2 * math.pi * k / 50.0)
                clean.append(v)
            self.last = clean
        self.t += n
        noisy = [c + self.rnd.gauss(0, self.noise) for c in clean]
        to_byte = lambda v: max(0, min(255, int(round(v + 128))))
        return bytes(to_byte(v) for v in noisy), [to_byte(v) - 128 for v in clean]


def source_from_spec(spec, seed=3):
    """'synthetic', 'synthetic-repeat', 'text:<string>', 'file:<path>', 'torah'."""
    if spec == "synthetic":
        return SyntheticSource(seed=seed)
    if spec == "synthetic-repeat":
        return SyntheticSource(seed=seed, repeat=0.7)
    if spec.startswith("text:"):
        return TextSource(spec[5:])
    if spec.startswith("file:"):
        with open(spec[5:], "rb") as f:
            return BytesSource(f.read())
    if spec == "torah":
        from .gematria_lab import torah_letter_values
        vals = torah_letter_values(limit_words=20000)
        return BytesSource(bytes(min(255, v // 2) for v in vals))
    raise ValueError(spec)


# ------------------------------------------------------------------ the engine
class Manifold:
    def __init__(self, source, bands="shells", team=None, accel=2, brake=3, vmax=10,
                 tick_seconds=0.05):
        self.source = source
        self.gov = Governor(accel=accel, brake=brake, vmax=vmax)
        self.band_kind = bands
        self.bands = {"shells": spectrum.shell_bands(6), "octaves": spectrum.octave_bands(6),
                      "hopf": None}[bands] if bands != "hopf" else spectrum.hopf_bands()
        self.team = agents_mod.default_team() if team is None else team
        self.critic = next((a for a in self.team if isinstance(a, agents_mod.AdversarialCritic)), None)
        self.threshold_mult = 1.0
        self.chipped, self.boost = set(), {}
        self.double_blocks = False
        self.tick_seconds = tick_seconds
        self.lock = threading.RLock()
        self.thread, self.alive = None, False
        self.output = bytearray()
        self.stats = {"ticks": 0, "blocks": 0, "flips": 0, "repaired": 0, "suspicious": 0,
                      "heals": 0, "doubled": 0, "compressed": 0, "replica_repairs": 0}
        self.last_report, self.log = {}, []
        self._prev_spec = None
        self._replicas = [self._pack()] * 3

    # ---------------- control (thread-safe)
    def start(self):
        with self.lock:
            self.gov.start()
            self._sync_replicas()

    def stop(self):
        with self.lock:
            self.gov.stop()
            self._sync_replicas()

    def set_speed(self, v):
        with self.lock:
            self.gov.set_speed(v)
            self._sync_replicas()

    def chip(self, *bands_):
        with self.lock:
            self.chipped |= set(bands_)

    def unchip(self, *bands_):
        with self.lock:
            self.chipped -= set(bands_)

    def blow(self, band, g):
        with self.lock:
            self.boost[band] = g

    # ---------------- replicated control state
    def _pack(self):
        g = self.gov
        return int(g.running) | (g.target & 0xFFFF) << 1

    def _sync_replicas(self):
        self._replicas = [self._pack()] * 3

    def corrupt_replica(self, k, value):
        self._replicas[k] = value

    def replicas_agree(self):
        return len(set(self._replicas)) == 1

    def self_heal(self, problems):
        self.stats["heals"] += 1
        if "control replicas disagree" in problems:
            good = heal.maj(*self._replicas)
            self.gov.running, self.gov.target = bool(good & 1), good >> 1 & 0xFFFF
            self._sync_replicas()
            self.stats["replica_repairs"] += 1
        if "split/join not lossless" in problems or "band energies do not add up" in problems:
            self.chipped, self.boost, self.threshold_mult = set(), {}, 1.0
        self.log.append(("heal", self.stats["ticks"], problems))

    # ---------------- one block
    def _process_block(self, raw, ref):
        cells = heal.encode_bytes(raw)
        flips = self.critic.corrupt_cells(cells) if self.critic else 0
        data, repaired, suspicious = heal.decode_cells(cells)
        self.stats["flips"] += flips
        self.stats["repaired"] += repaired
        self.stats["suspicious"] += suspicious
        x = [b - 128 for b in data]
        F = spectrum.wht(x)
        join_error = max(abs(a - b) for a, b in zip(spectrum.iwht(F), x))
        comps = spectrum.split(x, self.bands)
        be = {b: spectrum.energy(c) for b, c in comps.items()}
        energy_error = abs(sum(be.values()) - spectrum.energy(x)) / (1 + spectrum.energy(x))
        y, thr = spectrum.denoise(x)
        if self.threshold_mult != 1.0:
            y, thr = spectrum.denoise(x, threshold=thr * self.threshold_mult)
        if self.chipped or self.boost:
            g = [0.0 if b in self.chipped else self.boost.get(b, 1.0) for b in self.bands]
            y = spectrum.gain(y, g)
        resonance = None
        Y = spectrum.wht(y)
        if self._prev_spec is not None:
            A, B = self._prev_spec, Y
            num = sum((a - b) ** 2 for a, b in zip(A, B))
            den = sum(a * a for a in A) + sum(b * b for b in B) or 1.0
            resonance = 1 - num / den
        if self.double_blocks and self._prev_spec is not None:
            self.stats["doubled"] += 1
            diff = [a - b for a, b in zip(self._prev_spec, Y)]
            frac = sum(d * d for d in diff) / (sum(a * a for a in self._prev_spec) + sum(b * b for b in Y) or 1)
            if frac < 0.01:
                self.stats["compressed"] += 1
                y = spectrum.iwht(self._prev_spec)  # (A+B, 0) half kept: block = previous block
        self._prev_spec = spectrum.wht(y)
        quality = snr_in = None
        if ref is not None:
            sig = sum(r * r for r in ref) or 1.0
            err = sum((a - b) ** 2 for a, b in zip(y, ref))
            quality = 10 * math.log10(sig / (err or 1e-12))
            err_in = sum((a - b) ** 2 for a, b in zip(x, ref))
            snr_in = 10 * math.log10(sig / (err_in or 1e-12))
        out = bytes(max(0, min(255, int(round(v + 128)))) for v in y)
        return out, {"join_error": join_error, "energy_error": energy_error, "band_energy": be,
                     "threshold": thr, "resonance": resonance, "quality": quality, "snr_in": snr_in, "flips": flips,
                     "repaired": repaired}

    # ---------------- one tick
    def tick(self):
        with self.lock:
            speed = self.gov.tick()
            report = {"speed": speed, "goal": self.gov.goal}
            qs, qin = [], []
            for _ in range(speed):
                raw, ref = self.source.next_block(64)
                out, rep = self._process_block(raw, ref)
                self.output += out
                self.stats["blocks"] += 1
                report.update(rep)
                if rep["quality"] is not None:
                    qs.append(rep["quality"])
                    qin.append(rep["snr_in"])
            if qs:
                report["quality"] = sum(qs) / len(qs)
                report["snr_in"] = sum(qin) / len(qin)
            elif "quality" in report:
                report["quality"] = None
            self.stats["ticks"] += 1
            report["agents"] = {}
            for a in self.team:
                r = a.act(self, report)
                if r:
                    report["agents"][a.name] = r
            self.last_report = report
            return report

    # ---------------- background loop
    def run_background(self):
        if self.thread and self.thread.is_alive():
            return
        self.alive = True

        def loop():
            while self.alive:
                self.tick()
                time.sleep(self.tick_seconds)

        self.thread = threading.Thread(target=loop, daemon=True)
        self.thread.start()

    def shutdown(self):
        self.alive = False
        if self.thread:
            self.thread.join(timeout=2)

    def status(self):
        g = self.gov
        r = self.last_report
        return (f"tick {self.stats['ticks']:4d} | {'RUN ' if g.running else 'STOP'} speed {g.speed:2d} -> "
                f"goal {g.goal:2d} (target {g.target}) | blocks {self.stats['blocks']} | flips "
                f"{self.stats['flips']} repaired {self.stats['repaired']} | heals {self.stats['heals']} | "
                f"thr x{self.threshold_mult:.1f} | "
                f"SNR in {r.get('snr_in') if r.get('snr_in') is None else round(r['snr_in'], 1)} -> out "
                f"{r.get('quality') if r.get('quality') is None else round(r['quality'], 1)} dB | "
                f"res {None if r.get('resonance') is None else round(r['resonance'], 3)}")
