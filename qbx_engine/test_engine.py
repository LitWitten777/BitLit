"""Tests: `cd QBX/src && python -m unittest qbx_engine.test_engine` (no dependencies)."""

import random
import unittest

from . import alphabets, braidlines, ingest, multivector, spectrum, torus
from .engine import Engine, EigenStore


class SpectrumTests(unittest.TestCase):
    def test_wht_inversion_parseval(self):
        rng = random.Random(1)
        for bits in range(0, 8):
            xs = [rng.randint(-50, 50) for _ in range(1 << bits)]
            ys = spectrum.wht(xs)
            self.assertEqual(spectrum.iwht(ys), xs)
            self.assertEqual(sum(y * y for y in ys), (1 << bits) * sum(x * x for x in xs))

    def test_dyadic_shift_and_permutation(self):
        rng = random.Random(2)
        xs = [rng.randint(-9, 9) for _ in range(32)]
        ys = spectrum.wht(xs)
        for a in range(32):
            zs = spectrum.wht(spectrum.dyadic_shift(xs, a))
            self.assertEqual([z * z for z in zs], [y * y for y in ys])
        pe = spectrum.grade_energy(spectrum.wht(spectrum.permute_bits(xs, [3, 0, 4, 1, 2])))
        self.assertEqual(pe, spectrum.grade_energy(ys))

    def test_double_halve_lift_lower(self):
        a, b = [1, 2, 3, 4], [5, -6, 7, 0]
        c = multivector.double(a, b)
        self.assertEqual(multivector.halve(c), (a, b))
        sa, sb, sc = spectrum.wht(a), spectrum.wht(b), spectrum.wht(c)
        self.assertEqual(sc, [x + y for x, y in zip(sa, sb)] + [x - y for x, y in zip(sa, sb)])
        self.assertEqual(spectrum.wht(multivector.lower(c, 1)), sc[:4])
        self.assertEqual(spectrum.wht(multivector.lift(a, 2))[:4], [4 * v for v in sa])


class TorusTests(unittest.TestCase):
    def test_flow_invariance(self):
        rng = random.Random(3)
        xs = [rng.randint(-5, 5) for _ in range(40)]
        for (p, q) in ((1, 0), (2, 3), (3, 10)):
            self.assertTrue(all(torus.check_flow_invariance(xs, 6, 5, p, q, 2).values()))


class AlphabetTests(unittest.TestCase):
    def test_tables(self):
        self.assertEqual([len(alphabets.letters(a)) for a in ("hebrew", "greek", "latin")],
                         [22, 24, 26])
        self.assertEqual(alphabets.homophones("hebrew"), [])
        self.assertEqual(alphabets.homophones("greek"), [])
        self.assertEqual(alphabets.homophones("latin"), [["C", "K"], ["V", "W"]])
        for a in alphabets.ALPHABETS:
            for l in alphabets.letters(a):
                self.assertTrue(alphabets.symmetry_closed(l.sym))

    def test_lineage_vowel_split(self):
        for h, g, d in alphabets.lineage_distances():
            vowel = "vowel" in alphabets.features(alphabets.letter_of(g).sound)
            self.assertEqual(d >= 4, vowel)
            if not vowel:
                self.assertLessEqual(d, 2)


class BraidTests(unittest.TestCase):
    def test_concatenation_multiplies(self):
        # permutation of a concatenated reading = composite of the readings
        r = braidlines.read(["שלום", "ΛΟΓΟΣ", "VERBUM"])
        self.assertTrue(all(r["integrity"].values()))

    def test_parallel_commute(self):
        # words on strands {0,1} and {3,4}: generators 1 and 4 commute
        from qbx_micro import braid
        u, v = [1, 1, -1, 1], [4, -4, 4]
        self.assertEqual(braid.fold(5, u + v), braid.fold(5, v + u))
        self.assertEqual(braid.clifford_key(5, u + v), braid.clifford_key(5, v + u))


class EngineTests(unittest.TestCase):
    def test_any_input_roundtrip(self):
        eng = Engine(torus=(4, 4))
        for obj in ("ΕΝ ΑΡΧΗ", [1.5, -2, 3], b"\x00\xff\x10", '{"x": [1, 2]}', "1 2\n3 4\n"):
            rec = eng.process(obj)
            st = EigenStore()
            st.append(rec)
            data = ingest.ingest(obj)
            for name, ch in rec["channels"].items():
                self.assertTrue(all(ch["checks"].values()), (obj, name))
                self.assertEqual(st.signal(rec["id"], name),
                                 multivector.EigenMultivector(data["channels"][name]).signal)

    def test_cd_lost_properties(self):
        self.assertEqual(multivector.lost_properties(3), ["commutative", "associative"])
        self.assertIn("norm-multiplicative", multivector.lost_properties(4))
        self.assertIn("norm-multiplicative", multivector.lost_properties(5))


if __name__ == "__main__":
    unittest.main()


class ConnectedEngineTests(unittest.TestCase):
    """Braids with braids, standing waves, clock, harmonic map, beasts, merkaba, command
    language, letter cards, output sets and the HTTP API."""

    def test_module_checks(self):
        from . import beasts, braidbraid, harmonic, merkaba
        for name, d in (("beasts", beasts.checks()), ("harmonic", harmonic.checks()),
                        ("merkaba", merkaba.checks()), ("braidbraid", braidbraid.checks())):
            for k, v in d.items():
                self.assertTrue(v, "%s.%s" % (name, k))

    def test_standing_and_clock(self):
        from . import clock, standing
        rng = random.Random(5)
        for N, M, p, q in ((5, 6, 1, 2), (8, 8, 3, 1), (7, 4, 2, 2)):
            g = [[rng.randint(-9, 9) for _ in range(M)] for _ in range(N)]
            for t in (0, 1, 3, 7):
                self.assertTrue(all(standing.check(g, p, q, t).values()))
        c = clock.MasterClock().add("a", 6).add("b", 4).add("c", 9)
        self.assertEqual(c.joint_period(), 36)
        self.assertTrue(all(c.check().values()))

    def test_beasts_on_glyphs(self):
        from . import beasts
        self.assertEqual(beasts.trivial_on(""), ["LION", "OX", "MAN", "EAGLE"])
        self.assertEqual(beasts.trivial_on("V"), ["LION", "MAN"])
        self.assertEqual(beasts.trivial_on("H"), ["LION", "OX"])
        self.assertEqual(beasts.trivial_on("VHR"), ["LION"])
        for a in alphabets.ALPHABETS:
            for l in alphabets.letters(a):
                self.assertEqual(len(beasts.trivial_on(l.sym)) * (1 + len(l.sym)), 4)

    def test_harmonic_map(self):
        from . import harmonic
        self.assertTrue(harmonic.is_bijective(16, 25))
        self.assertEqual(harmonic.collisions(range(400), 16, 25), {})
        self.assertNotEqual(harmonic.collisions(range(16 * 24), 16, 24), {})
        self.assertEqual(harmonic.crt_inverse(*harmonic.node(237, 16, 25), 16, 25), 237)

    def test_merkaba_controls(self):
        from . import merkaba
        m = merkaba.Merkaba().run(["turnX", "diag", "invert", "spin", "turnZ"])
        self.assertEqual(m.swapped(), m.swap_count() % 2 == 1)
        self.assertFalse(m.is_rigid())  # spin is in the history
        self.assertTrue(merkaba.Merkaba().run(["turnX", "turnY", "diag"]).is_rigid())
        self.assertIn("<svg", merkaba.svg(m))

    def test_command_language(self):
        from .controls import Session, parse
        self.assertEqual(len(parse("repeat 3 { flow 1 0; turnX }; cross -1")), 7)
        s = Session("בראשית ברא אלהים", N=8, M=9)
        st = s.run("flow 1 2; turnX; repeat 5 { read; diag }; spin; cross 1; invert")
        self.assertTrue(all(st["checks"].values()))
        s.advance(100)
        self.assertTrue(all(s.checks().values()))
        with self.assertRaises(ValueError):
            s.run("cross 7")

    def test_schedule_returns_after_joint_period(self):
        from .controls import Session
        s = Session("ABC CAB BCA", N=6, M=4)
        P = s.master_clock().joint_period()
        s.advance(P)
        self.assertEqual(tuple(s.offset), (0, 0))
        self.assertEqual(s.merk.perm, tuple(range(8)))
        self.assertEqual(s.read_pos % len(s._prefix_words), 0)

    def test_letter_cards(self):
        from . import letters
        c = letters.card("ב")
        self.assertEqual(c["value"], 2)
        self.assertEqual(c["relations"]["lineage"], {"greek": "Β"})
        self.assertEqual(len(letters.alphabet_cards("greek")), 24)
        self.assertIsNone(letters.card("?"))

    def test_outset(self):
        import os
        import tempfile
        from . import outsets
        with tempfile.TemporaryDirectory() as d:
            r = outsets.outset("ΕΝ ΑΡΧΗ ΗΝ Ο ΛΟΓΟΣ", d, frames=20, N=8, M=9)
            self.assertTrue(r["ok"])
            for f in ("index.md", "record.json", "letters.csv", "merkaba.svg", "standing.wav"):
                self.assertTrue(os.path.exists(os.path.join(d, f)), f)

    def test_http_api(self):
        from . import server
        st, _, body = server.handle("POST", "/api/session", {}, {"text": "IN PRINCIPIO", "N": 6,
                                                                 "M": 5})
        self.assertEqual(st, 200)
        st, _, body = server.handle("POST", "/api/run", {}, {"program": "read; turnY; flow 2 3"})
        self.assertEqual(st, 200)
        self.assertTrue(all(body["checks"].values()))
        st, _, body = server.handle("POST", "/api/control", {}, {"control": "nope"})
        self.assertEqual(st, 400)
        st, _, body = server.handle("GET", "/api/alphabet", {"name": ["latin"]}, {})
        self.assertEqual(len(body), 26)

    def test_gematria_convention(self):
        """Finals follow the project table (migration 014, `Gematria.standard`): 500-900;
        the strict mispar hechrachi reading is available by name."""
        from . import fidelity
        self.assertEqual([alphabets.value_of(c) for c in "ךםןףץ"], [500, 600, 700, 800, 900])
        self.assertEqual([alphabets.value_of(c, "hechrachi") for c in "ךםןףץ"],
                         [20, 40, 50, 80, 90])
        self.assertEqual(dict(fidelity.word_values("שלום")), {"שלום": 936})
        fin, base = alphabets.letter_of("ם"), alphabets.letter_of("מ")
        self.assertEqual((fin.index, fin.sound), (base.index, base.sound))
        with self.assertRaises(ValueError):
            alphabets.value_of("א", "gadol")

    def test_fidelity_and_nyquist(self):
        from . import fidelity, standing
        col = fidelity.node_collisions("בראשית ברא אלהים את השמים ואת הארץ", 16, 25)
        self.assertTrue(any(c["values"] == [1, 401] for c in col))
        # a grid whose strongest mode is the top corner (a + b = 39): it must not be rendered,
        # since 110 Hz * 40 = 4400 Hz is above the 4000 Hz limit at 8 kHz
        import math
        N, M = 16, 25
        g = [[math.cos(2 * math.pi * (15 * j / N + 24 * k / M)) * 100 for k in range(M)]
             for j in range(N)]
        s = standing.sonify(g, seconds=0.25)
        self.assertTrue(all(abs(x) <= 1.0 for x in s))
        rep = fidelity.report("ΛΟΓΟΣ")
        self.assertEqual({f["tier"] for f in rep["fields"]},
                         {"exact", "digitised", "reference", "convention"})
