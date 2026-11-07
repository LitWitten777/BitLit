"""Music vortexes on the hypercube Hopf bundle, the Tonnetz and the lattices.

Three kinds of "vortex":

1. Octave vortex (Hopf bundle of Q6).  The octave (frequency x2) is squaring in GF(64) (the
   Frobenius map).  The k-th harmonic is the cell x^k.  The octave sends harmonic k to 2k.  It
   maps the GF(8) fibre over base point r onto the fibre over 2r mod 9, so on the 9 base points
   it runs the circuit 1-2-4-8-7-5, swaps 3 and 6 and fixes 0 (= "9").  The base point of x^k is
   the digit sum of k mod 9.  Inside the 7-cell fibres it doubles the phase (1-2-4, 3-6-5).
2. Tonnetz vortex.  On the Tonnetz torus (12 notes, 36 edges, 24 triads), the 6 triads that
   contain a note form a closed loop P,L,R,P,L,R around it.  Interval cycles wind round the
   pitch circle: the circle of fifths 7 times, fourths 5 times.
3. Lattices.  Octave equivalence: just lattice -> 12-TET (commas vanish), Z^6 / 2Z^6 = Q6 cells,
   E8 / 2E8 (roots in 120 classes; with the norm-4 vectors: 1 + 120 + 135 = 256 classes).

Plus the musical concepts of psalm_119.md (heptatonic/diatonic and pentatonic scales, the octave
"sheminith", tonic, thirds, unequal steps, harmony = triads, circle of fifths, relative minor),
and a letter-to-tone convention (Sefer Yetzirah split 3 + 7 + 12) for rendering Psalm 119's
22 x 8 acrostic.  The convention is a choice, not a historical claim.

Proved counterparts (Lean): RequestProject/MusicVortex.lean, RequestProject/MusicTonnetz.lean,
RequestProject/MusicLattices.lean.  Standard library only.
"""
import math
import struct
import wave

from . import hopf as H

# ----------------------------------------------------------------------------------------------
# 1. octave vortex on the Hopf bundle


def octave(v):
    """Squaring in GF(64): the octave map on cells."""
    return H.gmul(v, v)


def harmonic_cell(k):
    """The k-th harmonic x^k (k >= 1)."""
    return H.GPOW[k % 63]


def digit_sum(k):
    return sum(int(c) for c in str(k))


def octave_class(v):
    out, w = [], v
    while w not in out:
        out.append(w)
        w = octave(w)
    return out


def octave_classes():
    seen, classes = set(), []
    for v in range(64):
        if v not in seen:
            c = octave_class(v)
            seen.update(c)
            classes.append(c)
    return classes


def base_orbits():
    seen, orbits = set(), []
    for r in range(9):
        if r not in seen:
            o, s = [], r
            while s not in o:
                o.append(s)
                s = 2 * s % 9
            seen.update(o)
            orbits.append(o)
    return orbits


VORTEX_ORDER = [1, 2, 4, 8, 7, 5, 3, 6, 0]


def fibre_harmonics(r):
    """Harmonic numbers 1..63 whose cell lies over GF(8) base point r: k = r (mod 9)."""
    return [k for k in range(1, 64) if k % 9 == r]


def hopf_vortex_report():
    cells = []
    for v in range(1, 64):
        k = H.DLOG[v] or 63
        cells.append({"cell": v, "harmonic": k, "base": H.hopf(9, v), "phase": H.DLOG[v] % 7,
                      "octave_to": octave(v), "octave_base": H.hopf(9, octave(v))})
    return {
        "octave_map": "v -> v*v in GF(64) (Frobenius); harmonic k -> harmonic 2k",
        "base_orbits_doubling_mod_9": base_orbits(),
        "fibre_phase_orbits_doubling_mod_7": [[0], [1, 2, 4], [3, 6, 5]],
        "fundamental_octaves_base_points": [H.hopf(9, harmonic_cell(2 ** n)) for n in range(7)],
        "fifth_octaves_base_points": [H.hopf(9, harmonic_cell(3 * 2 ** n)) for n in range(7)],
        "fibre_harmonics": {r: fibre_harmonics(r) for r in VORTEX_ORDER},
        "axis_369_cells_are_cubes": sorted(v for v in range(1, 64) if H.hopf(9, v) % 3 == 0),
        "octave_classes": octave_classes(),
        "octave_class_sizes": sorted(len(c) for c in octave_classes()),
        "fixed_points": {"sigma": [v for v in range(64) if octave(v) == v],
                         "sigma^2": [v for v in range(64) if octave(octave(v)) == v],
                         "sigma^3": [v for v in range(64) if octave(octave(octave(v))) == v]},
        "caveat": "octave(8) = 3: linear over GF(2) but not a symmetry of the cube graph",
        "cells": cells,
    }


# ----------------------------------------------------------------------------------------------
# 2. scales and the Tonnetz

NAMES = ["C", "C#", "D", "Eb", "E", "F", "F#", "G", "Ab", "A", "Bb", "B"]
DIATONIC = [0, 2, 4, 5, 7, 9, 11]
SOLFEGE = ["Do", "Re", "Mi", "Fa", "Sol", "La", "Si"]
DEGREE_NAMES = ["tonic", "supertonic", "mediant", "subdominant", "dominant", "submediant",
                "leading tone"]


def specific(i, j, scale=DIATONIC):
    n = len(scale)
    return (scale[(i + j) % n] - scale[i % n]) % 12


def notes(t):
    r, major = t
    return frozenset({r % 12, (r + (4 if major else 3)) % 12, (r + 7) % 12})


def P(t):
    return (t[0], not t[1])


def R(t):
    return ((t[0] + 9) % 12, False) if t[1] else ((t[0] + 3) % 12, True)


def L(t):
    return ((t[0] + 4) % 12, False) if t[1] else ((t[0] + 8) % 12, True)


def tname(t):
    return NAMES[t[0]] if t[1] else NAMES[t[0]].lower()


def vertex_vortex(p):
    loop, t = [(p, True)], (p, True)
    for op in (P, L, R, P, L, R):
        t = op(t)
        loop.append(t)
    return loop


def walk(ops, start=(0, True), steps=24):
    out, t = [start], start
    for k in range(steps):
        t = ops[k % len(ops)](t)
        out.append(t)
    return out


def cycle_length(g):
    return 12 // math.gcd(g, 12)


def scales_report():
    return {
        "diatonic": [NAMES[p] for p in DIATONIC],
        "diatonic_as_fifths": [NAMES[(7 * k + 5) % 12] for k in range(7)],
        "pentatonic_complement": [NAMES[(7 * k + 6) % 12] for k in range(5)],
        "steps": [specific(i, 1) for i in range(7)],
        "myhill_sizes": {j: sorted({specific(i, j) for i in range(7)}) for j in range(1, 7)},
        "triads": {SOLFEGE[i]: {(4, 3): "major", (3, 4): "minor", (3, 3): "diminished"}
                   [(specific(i, 2), specific(i + 2, 2))] for i in range(7)},
        "degrees": dict(zip(SOLFEGE, DEGREE_NAMES)),
        "relative_minor_same_notes": sorted(DIATONIC[(i + 5) % 7] for i in range(7)) == DIATONIC,
        "interval_cycles": {name: {"steps": cycle_length(g), "winding": g * cycle_length(g) // 12}
                            for name, g in [("fifths", 7), ("fourths", 5), ("major thirds", 4),
                                            ("minor thirds", 3), ("whole tones", 2),
                                            ("semitones", 1)]},
        "pythagorean_comma": "3^12 / 2^19 = 531441 / 524288 (12 pure fifths overshoot 7 octaves)",
    }


def tonnetz_report():
    edges = {frozenset({a, b}) for a in range(12) for b in range(12)
             if (b - a) % 12 in (3, 4, 5, 7, 8, 9)}
    triads = [(r, m) for r in range(12) for m in (True, False)]
    lr = walk([R, L])
    return {
        "vertices": 12, "edges": len(edges), "triangles": len(triads),
        "euler_characteristic": 12 - len(edges) + len(triads),
        "vertex_vortices": {NAMES[p]: [tname(t) for t in vertex_vortex(p)] for p in range(12)},
        "RL_walk_24": [tname(t) for t in lr],
        "LP_hexatonic": [tname(t) for t in walk([L, P], steps=6)],
        "RP_octatonic": [tname(t) for t in walk([R, P], steps=8)],
        "kernel_of_(a,b)->7a+4b": {"(0,3)": "3 major thirds = octave (diesis 128/125)",
                                   "(4,-1)": "syntonic comma 81/80", "(12,0)": "Pythagorean comma"},
    }


# ----------------------------------------------------------------------------------------------
# 3. lattices


def e8_vectors(norm2):
    """E8 vectors (doubled coordinates) with doubled squared norm 4*norm2."""
    out = []
    target = 4 * norm2
    m = int(math.isqrt(target))
    rng = range(-m, m + 1)

    def rec(prefix, rem):
        if len(prefix) == 8:
            if rem == 0:
                out.append(tuple(prefix))
            return
        for a in rng:
            if a * a <= rem:
                rec(prefix + [a], rem - a * a)

    rec([], target)
    return [y for y in out if (all(a % 2 == 0 for a in y) or all(a % 2 for a in y))
            and sum(y) % 4 == 0]


def in_e8(y):
    return (all(a % 2 == 0 for a in y) or all(a % 2 for a in y)) and sum(y) % 4 == 0


def lattice_report():
    roots, n4 = e8_vectors(2), e8_vectors(4)

    def classes(vs):
        groups = []
        for v in vs:
            for g in groups:
                d = [a - b for a, b in zip(v, g[0])]
                if all(a % 2 == 0 for a in d) and in_e8([a // 2 for a in d]):
                    g.append(v)
                    break
            else:
                groups.append([v])
        return groups

    rc, nc = classes(roots), classes(n4)
    return {
        "just_to_12TET": "(a,b,c) for 2^a 3^b 5^c -> 7b + 4c mod 12; octave forgets a",
        "Z6_mod_2": "Z^6 / 2Z^6 = the 64 cells of Q6 (proved)",
        "E8": {"roots": len(roots), "root_classes": len(rc),
               "root_class_sizes": sorted({len(g) for g in rc}),
               "norm4_vectors": len(n4), "norm4_classes": len(nc),
               "norm4_class_sizes": sorted({len(g) for g in nc}),
               "total_classes": 1 + len(rc) + len(nc),
               "note": "root classes proved in Lean; norm-4 classes computed here only"},
    }


# ----------------------------------------------------------------------------------------------
# Psalm 119 (22 stanzas x 8 verses) with the Sefer Yetzirah 3 + 7 + 12 letter split

ALEPHBET = "אבגדהוזחטיכלמנסעפצקרשת"
MOTHERS = "אמש"
DOUBLES = "בגדכפרת"
SIMPLES = "הוזחטילנסעצק"


def letter_tone(ch):
    """Convention: doubles -> the 7 diatonic degrees, simples -> the 12 chromatic pitch classes,
    mothers -> the tones of the C major triad (C, E, G)."""
    if ch in DOUBLES:
        return DIATONIC[DOUBLES.index(ch)]
    if ch in SIMPLES:
        return SIMPLES.index(ch)
    return [0, 4, 7][MOTHERS.index(ch)]


def psalm119_report():
    return {
        "stanzas": 22, "verses_per_stanza": 8, "verses": 22 * 8,
        "reading": "8 verses per stanza = the 8 degrees of an octave (sheminith), 8th = tonic again",
        "split": {"mothers": MOTHERS, "doubles": DOUBLES, "simples": SIMPLES},
        "stanza_tones": {ch: NAMES[letter_tone(ch)] for ch in ALEPHBET},
        "convention": "letter-to-tone assignment is a chosen convention, not a historical mapping",
    }


# ----------------------------------------------------------------------------------------------
# audio


def _tone(freqs, seconds, rate, amp=0.5):
    n = int(seconds * rate)
    out = []
    w = amp / max(1.0, math.sqrt(len(freqs)))
    for i in range(n):
        env = min(1.0, i / (0.02 * rate), (n - i) / (0.05 * rate))
        t = i / rate
        out.append(env * w * sum(math.sin(2 * math.pi * f * t) for f in freqs))
    return out


def pc_hz(pc, octave_=4):
    return 440.0 * 2 ** ((pc - 9) / 12 + (octave_ - 4))


def render_wav(path, rate=22050, f0=27.5):
    """Sections: (1) Hopf octave vortex: each GF(8) fibre as a chord of its 7 harmonics of f0, in
    the order 1 2 4 8 7 5 | 3 6 | 9; (2) the octaves of f0 (base points 1 2 4 8 7 5 1);
    (3) the Tonnetz vortex around C; (4) the circle of fifths (winding 7);
    (5) the R-L walk through all 24 triads; (6) Psalm 119: the 22 stanza tones, each an
    8-note ascending octave."""
    s = []
    for r in VORTEX_ORDER:
        s += _tone([f0 * k for k in fibre_harmonics(r) or [63]], 0.9, rate)
    s += _tone([], 0.3, rate)
    for n in range(7):
        s += _tone([f0 * 4 * 2 ** n], 0.45, rate)
    s += _tone([], 0.3, rate)
    for t in vertex_vortex(0):
        s += _tone([pc_hz(p) for p in sorted(notes(t))], 0.6, rate)
    s += _tone([], 0.3, rate)
    for k in range(13):
        s += _tone([pc_hz(0, 2) * 2 ** (7 * k / 12) / 2 ** (k * 7 // 12)], 0.3, rate)
    s += _tone([], 0.3, rate)
    for t in walk([R, L]):
        s += _tone([pc_hz(p) for p in sorted(notes(t))], 0.35, rate)
    s += _tone([], 0.3, rate)
    for ch in ALEPHBET:
        tonic = letter_tone(ch)
        for i in range(8):
            s += _tone([pc_hz(tonic, 3) * 2 ** ((DIATONIC[i % 7] + 12 * (i // 7)) / 12)], 0.09, rate)
    peak = max(1e-9, max(abs(x) for x in s))
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(b"".join(struct.pack("<h", int(x / peak * 0.9 * 32000)) for x in s))
    return path


def render_svg(path):
    """The 9 base points of the GF(8) Hopf bundle on a circle, with the octave arrows r -> 2r."""
    W, cx, cy, rad = 560, 280, 280, 200
    pos = {}
    for r in range(9):
        a = math.pi / 2 - 2 * math.pi * r / 9
        pos[r] = (cx + rad * math.cos(a), cy - rad * math.sin(a))
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{W + 60}" font-family="sans-serif">',
           f'<rect width="{W}" height="{W + 60}" fill="#0b0d17"/>',
           '<defs><marker id="a" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto">'
           '<path d="M0,0 L8,4 L0,8 z" fill="#ffd166"/></marker></defs>',
           '<text x="12" y="24" fill="#eee" font-size="15">Octave vortex on the 9 base points of the '
           'GF(8) Hopf bundle of Q6 (r -> 2r mod 9)</text>']
    for r in range(9):
        s = 2 * r % 9
        if s == r:
            continue
        (x1, y1), (x2, y2) = pos[r], pos[s]
        col = "#ffd166" if r % 3 else "#ef476f"
        out.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x1 + 0.9 * (x2 - x1):.1f}" '
                   f'y2="{y1 + 0.9 * (y2 - y1):.1f}" stroke="{col}" stroke-width="2" marker-end="url(#a)"/>')
    for r in range(9):
        x, y = pos[r]
        col = "#ef476f" if r % 3 == 0 else "#06d6a0"
        out.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="22" fill="{col}"/>')
        out.append(f'<text x="{x:.1f}" y="{y + 6:.1f}" font-size="17" text-anchor="middle" fill="#000">'
                   f'{r if r else 9}</text>')
        cells = ",".join(str(c) for c in H.fiber(9, r))
        out.append(f'<text x="{x:.1f}" y="{y + 38:.1f}" font-size="9" text-anchor="middle" fill="#aaa">{cells}</text>')
    out.append(f'<text x="12" y="{W + 30}" fill="#888" font-size="11">Green: circuit 1-2-4-8-7-5. Red: axis 3-6 '
               f'(swapped) and 9 = base point 0 (fixed). Small numbers: the 7 cells of each fibre.</text>')
    out.append(f'<text x="12" y="{W + 48}" fill="#888" font-size="11">Base point of the cell x^k = digit sum of k '
               f'mod 9 (Lean: hopf9_harmonic_digits).</text>')
    out.append("</svg>")
    with open(path, "w") as f:
        f.write("\n".join(out))
    return path


# ----------------------------------------------------------------------------------------------


def report():
    return {"hopf_octave_vortex": hopf_vortex_report(), "scales": scales_report(),
            "tonnetz": tonnetz_report(), "lattices": lattice_report(), "psalm119": psalm119_report()}


def selfcheck():
    assert all(octave(a ^ b) == octave(a) ^ octave(b) for a in range(64) for b in range(64))
    assert all(H.hopf(9, octave(v)) == 2 * H.hopf(9, v) % 9 for v in range(1, 64))
    assert sorted(map(sorted, base_orbits())) == [[0], [1, 2, 4, 5, 7, 8], [3, 6]]
    assert [H.hopf(9, harmonic_cell(2 ** n)) for n in range(7)] == [1, 2, 4, 8, 7, 5, 1]
    assert all(H.hopf(9, harmonic_cell(k)) == digit_sum(k) % 9 for k in range(1, 2000))
    cubes = {H.gmul(w, H.gmul(w, w)) for w in range(1, 64)}
    assert cubes == {v for v in range(1, 64) if H.hopf(9, v) % 3 == 0}
    sizes = sorted(len(c) for c in octave_classes())
    assert len(sizes) == 14 and sizes == [1, 1, 2, 3, 3] + [6] * 9
    assert octave(8) == 3
    tr = tonnetz_report()
    assert (tr["edges"], tr["triangles"], tr["euler_characteristic"]) == (36, 24, 0)
    for p in range(12):
        loop = vertex_vortex(p)
        assert loop[-1] == loop[0] and len(set(loop[:6])) == 6 and all(p in notes(t) for t in loop)
    assert len(set(walk([R, L])[:24])) == 24
    assert all(len({specific(i, j) for i in range(7)}) == 2 for j in range(1, 7))
    assert 2 ** 19 < 3 ** 12
    lr = lattice_report()["E8"]
    assert (lr["roots"], lr["root_classes"], lr["norm4_vectors"], lr["norm4_classes"]) == (240, 120, 2160, 135)
    assert lr["total_classes"] == 256
    return True


if __name__ == "__main__":
    import json
    selfcheck()
    print(json.dumps(report(), indent=1, ensure_ascii=False, default=str))
