"""How closely each part of an output set can match observation.

Every field of an output set falls in one of four tiers:

  exact        proved structure, re-derived on the data (the checks).  No error, but it is a
               statement about the model, not a measurement of the world.
  digitised    a measured or rendered quantity with a proved error bound
               (`QBX/Formal/Engine/Reality.lean`).
  reference    values entered by hand from a chosen reference (sounds of letters, glyph shapes,
               letter values).  Exactly as good as that reference and the chosen text edition.
  convention   a choice of the engine (base frequency, colours, beast families, torus size,
               tick length).  No observation can confirm or refute it: every check is blind to it
               (`ratio_checks_blind_to_base`).

`report(text, N, M)` returns the tier of every file and field, the numeric error bounds, and the
values of this input that the torus node cannot tell apart (`harmonicNode_collision`).
"""

from . import alphabets

TIERS = {
    "exact": "proved structure re-derived on this data; no error, but says nothing about the world",
    "digitised": "measured or rendered quantity with a proved error bound",
    "reference": "hand-entered from a chosen reference; as good as that reference and edition",
    "convention": "engine choice; no observation can confirm or refute it",
}

FIELDS = [
    # (file, field, tier, note)
    ("checks.json", "*", "exact", "Lean statements re-checked on this data"),
    ("record.json", "channels.bytes / code", "exact", "UTF-8 bytes and code points of the input"),
    ("record.json", "channels.samples", "digitised",
     "real numbers scaled by 2^16 and rounded: error <= 2^-17 (ingest_error)"),
    ("record.json", "multivectors, spectra", "exact", "lossless: spec_inversion, spec_parseval"),
    ("record.json", "colours (names, wavelengths)", "convention", "labels for energy bands"),
    ("letters.*", "value", "reference",
     "standard gematria (finals 500-900, decision GEM-001) / isopsephy / Latin ordinal"),
    ("letters.*", "ipa, spoken.features", "reference",
     "Tiberian Hebrew, Classical Greek, Classical Latin; reconstructed, not recorded speech"),
    ("letters.*", "written.holes, symmetry", "reference", "plain typeface; other scripts and hands differ"),
    ("letters.*", "beasts", "convention", "grouping of sound features into four families"),
    ("letters.*", "harmonic.frequency_hz", "convention",
     "value x 27 Hz; only ratios are model content (ratio_checks_blind_to_base)"),
    ("letters.*", "harmonic.pitch_class_cents", "exact", "log2(value) mod 1, independent of base"),
    ("letters.*", "harmonic.torus_node", "exact",
     "value mod N, value mod M: remembers the value only modulo N*M"),
    ("letters.*", "relations", "reference", "computed from the hand-entered sound features"),
    ("session.json", "clock, offset, braid, merkaba", "exact", "command semantics (Controls.lean)"),
    ("session.json", "schedule, tick length", "convention", "how often letters are read / controls applied"),
    ("braids.json", "*", "exact", "braid algebra (BraidBraid.lean)"),
    ("*.svg", "colour scale", "convention", "heat map; positions are exact"),
    ("standing.wav", "samples", "digitised",
     "16-bit, error < 1/32000 per sample (wav_sample_error); partials limited below 4000 Hz "
     "(alias_fold)"),
    ("standing.wav", "pitch (110 Hz base, 1/8 s per tick)", "convention", "rendering choice"),
]


def word_values(text):
    out = []
    for w in text.split():
        vals = [alphabets.letter_of(ch) for ch in w]
        vals = [l.value for l in vals if l is not None]
        if vals:
            out.append((w, sum(vals)))
    return out


def letter_values(text):
    return [(ch, l.value) for ch in text for l in [alphabets.letter_of(ch)] if l is not None]


def node_collisions(text, N, M):
    """Distinct values in this input (letters and whole words) that share a torus node."""
    items = {}
    for label, v in letter_values(text) + word_values(text):
        items.setdefault(v, set()).add(label)
    groups = {}
    for v in sorted(items):
        groups.setdefault((v % N, v % M), []).append(v)
    return [{"node": list(k), "values": vs, "labels": {str(v): sorted(items[v]) for v in vs}}
            for k, vs in groups.items() if len(vs) > 1]


def report(text, N=16, M=25):
    return {
        "tiers": TIERS,
        "fields": [{"file": f, "field": x, "tier": t, "note": n} for f, x, t, n in FIELDS],
        "error_bounds": {
            "ingest_real_number": 2.0 ** -17,
            "wav_sample": 1.0 / 32000,
            "wav_highest_frequency_hz": 4000,
        },
        "torus": {"N": N, "M": M, "distinct_nodes": N * M,
                  "values_kept_modulo": N * M,
                  "collisions_in_this_input": node_collisions(text or "", N, M)},
        "lean": "QBX/Formal/Engine/Reality.lean",
    }
