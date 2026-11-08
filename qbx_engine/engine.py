"""The engine: ingest -> channels -> torus + eigenmode multivectors -> store.

    from qbx_engine.engine import Engine
    eng = Engine(torus=(16, 16))
    rec = eng.process("בראשית ברא אלהים")      # any str / bytes / path / numbers / JSON
    eng.store.append(rec)                       # JSON lines on disk

A record contains, for every channel:
  * `multivector`  -- exact Walsh spectrum on Cl(bits) as {blade: coeff}
  * `colours`      -- energy per grade, with colour name and wavelength label
  * `torus`        -- band energies and bispectrum samples on Z/N x Z/M
  * `checks`       -- exact / numerical re-derivation of the Lean invariants
and, for text, the alphabet reading (letters with written and spoken geometry)
and the braid traced by its words.

Every check is a re-derivation of a theorem in `QBX/Formal/Engine/`; a failed
check means the computation was corrupted, not that a theorem is false.
"""

import hashlib
import json
import os

from . import alphabets, braidlines, ingest as _ingest, multivector, torus as _torus


class EigenStore:
    """Append-only JSON-lines store of eigen records, keyed by content hash."""

    def __init__(self, path=None):
        self.path = path
        self.records = []
        if path and os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                for line in fh:
                    if line.strip():
                        self.records.append(json.loads(line))

    def append(self, rec):
        self.records.append(rec)
        if self.path:
            with open(self.path, "a", encoding="utf-8") as fh:
                fh.write(json.dumps(rec, ensure_ascii=False, sort_keys=True) + "\n")
        return rec["id"]

    def get(self, rid):
        for r in self.records:
            if r["id"] == rid:
                return r
        return None

    def signal(self, rid, channel):
        """Recover a stored channel exactly from its multivector (inverse transform)."""
        from . import spectrum
        r = self.get(rid)
        ch = r["channels"][channel]
        spec = multivector.from_blades({int(k): v for k, v in ch["multivector"].items()},
                                       ch["bits"])
        return spectrum.iwht(spec)


class Engine:
    def __init__(self, torus=(16, 16), bits=None, store=None):
        self.N, self.M = torus
        self.bits = bits
        self.store = store if store is not None else EigenStore()

    def channel_record(self, samples):
        mv = multivector.EigenMultivector(samples, self.bits)
        T = _torus.HarmonicTorus(self.N, self.M).load(samples)
        inv = T.invariants()
        return {
            "length": len(samples),
            "bits": mv.bits,
            "multivector": {str(k): v for k, v in mv.blades.items()},
            "colours": mv.colours(),
            "torus": {"N": self.N, "M": self.M, "energy": inv["energy"],
                      "band_energy": inv["band_energy"], "colours": inv["colours"],
                      "bispectrum": inv["bispectrum"]},
            "checks": mv.checks(),
        }

    def process(self, obj):
        data = _ingest.ingest(obj)
        raw = json.dumps(data["channels"], sort_keys=True).encode()
        rec = {
            "id": hashlib.sha256(raw).hexdigest()[:16],
            "kind": data["kind"],
            "scale_bits": data["scale_bits"],
            "channels": {name: self.channel_record(xs)
                         for name, xs in data["channels"].items() if xs},
        }
        text = data.get("text")
        if text:
            rec["letters"] = [alphabets.letter_of(c).as_dict() for c in text
                              if alphabets.letter_of(c) is not None]
            words = [w for w in text.split() if any(alphabets.letter_of(c) for c in w)]
            if 2 <= len(words) <= 12:
                rec["braid"] = {m: braidlines.read(words, m) for m in ("written", "spoken")}
        return rec

    def flow_check(self, obj, p=1, q=2, t=3):
        """Oscillate every channel along the (p, q) direction and compare invariants."""
        data = _ingest.ingest(obj)
        return {name: _torus.check_flow_invariance(xs, min(self.N, 8), min(self.M, 8), p, q, t)
                for name, xs in data["channels"].items() if xs}
