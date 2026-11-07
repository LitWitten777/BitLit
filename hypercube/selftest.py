"""End-to-end checks of the hypercube engine (`python3 -m hypercube selftest`)."""
import base64
import random

from . import cells, codec, eclipses, scripture, sky, state
from .timescale import calendar_from_jd, jd_from_calendar, parse_time

# Solar eclipses 2017-2027 with type and Saros series, as published in NASA's Five Millennium
# Canon (Espenak & Meeus).  The engine computes them from the ephemeris; this list only checks it.
SOLAR_2017_2027 = [
    ("2017-02-26", "annular", 140), ("2017-08-21", "total", 145), ("2018-02-15", "partial", 150),
    ("2018-07-13", "partial", 117), ("2018-08-11", "partial", 155), ("2019-01-06", "partial", 122),
    ("2019-07-02", "total", 127), ("2019-12-26", "annular", 132), ("2020-06-21", "annular", 137),
    ("2020-12-14", "total", 142), ("2021-06-10", "annular", 147), ("2021-12-04", "total", 152),
    ("2022-04-30", "partial", 119), ("2022-10-25", "partial", 124), ("2023-04-20", "hybrid", 129),
    ("2023-10-14", "annular", 134), ("2024-04-08", "total", 139), ("2024-10-02", "annular", 144),
    ("2025-03-29", "partial", 149), ("2025-09-21", "partial", 154), ("2026-02-17", "annular", 121),
    ("2026-08-12", "total", 126), ("2027-02-06", "annular", 131), ("2027-08-02", "total", 136),
]
LUNAR_TOTAL_2018_2026 = ["2018-01-31", "2018-07-27", "2019-01-21", "2021-05-26", "2022-05-16",
                         "2022-11-08", "2025-03-14", "2025-09-07", "2026-03-03"]


def run():
    fails = []

    def check(name, ok, detail=""):
        print(("PASS " if ok else "FAIL ") + name + (f"  [{detail}]" if detail else ""))
        if not ok:
            fails.append(name)

    rng = random.Random(20261023)
    ok = True
    for _ in range(300):
        data = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 40)))
        cs = codec.encode_bytes(data)
        ok &= codec.decode_cells(cs) == data
        ok &= codec.render(cs) == base64.b64encode(data).decode().rstrip("=")
    check("cell codec is lossless and equals Base64 (300 random byte strings)", ok)
    check("codec: Hebrew/Greek text round trip",
          codec.decode_text(codec.encode_text("בראשית ברא — Ἐν ἀρχῇ")) == "בראשית ברא — Ἐν ἀρχῇ")
    check("Atbash: ששך -> בבל (Jer 25:26)", codec.atbash("ששך", "he") == "בבל")
    check("Atbash: לב קמי -> כש דימ (Jer 51:1)", codec.atbash("לב קמי", "he") == "כש דימ")

    ok = True
    for _ in range(2000):
        ra, dec, mag = rng.uniform(0, 24), rng.uniform(-89, 89), rng.uniform(-2, 3)
        if abs(dec) < 1e-3:
            continue
        ok &= cells.sky_cell((ra + 12) % 24, -dec, mag) == cells.sky_cell(ra, dec, mag) ^ 3
    check("anti-solar cell = cell XOR 3 (2000 random positions; proved in Lean)", ok)
    check("codon convention: cell 10, 11, 14 are the stop codons",
          [c for c in range(64) if cells.amino(c) == "*"] == [10, 11, 14])

    for jd in (jd_from_calendar(-762, 6, 15, 7.5), jd_from_calendar(2026, 10, 23, 12)):
        y, m, d, h = calendar_from_jd(jd)
        check(f"calendar round trip {y}-{m}-{d}", abs(jd_from_calendar(y, m, d, h) - jd) < 1e-6)

    check("canon: 66 books, 1189 chapters", len(scripture.chapter_counts()) == 66 and sum(scripture.chapter_counts()) == 1189)
    check("Genesis 1:1 (OSHB) gematria 2701", codec.gematria(scripture.original_verse("Gen.1.1")) == 2701)
    p = scripture.placement(15.9917, 15)
    check("T CrB with 15 deg shift -> Ezekiel 40 / 2 Corinthians / Benjamin (NovaScripture.lean)",
          (p["chapter"], p["isaiah_book"], p["tribe"]) == ("Ezekiel 40", "2 Corinthians", "Benjamin"))

    eph = sky.default_ephemeris()
    rows = eclipses.eclipses_between(parse_time("2017-01-01"), parse_time("2028-01-01"), eph, kinds=("solar",))
    got = [(r["date"][:10], r["type"], r["saros"]) for r in rows]
    check("solar eclipses 2017-2027: dates, types and Saros numbers match the canon", got == SOLAR_2017_2027,
          f"{len(got)} found")
    rows = eclipses.eclipses_between(parse_time("2018-01-01"), parse_time("2026-12-31"), eph, kinds=("lunar",))
    tot = [r["date"][:10] for r in rows if r["type"] == "total"]
    check("total lunar eclipses 2018-2026 match the canon", tot == LUNAR_TOTAL_2018_2026, ",".join(tot))
    r = eclipses.nearest_eclipse(parse_time("2017-08-21"), "solar", eph)
    lc = eclipses.local_circumstances(r, 36.97, -87.67, eph)
    check("2017-08-21 total at Hopkinsville KY", lc["phase_seen"] == "total", lc["ut"])
    r = eclipses.nearest_eclipse(jd_from_calendar(-762, 6, 15), "solar", eph)
    check("Bur-Sagale -762-06-15 is a total solar eclipse", r["date"].startswith("-0762-06-15") and r["type"] == "total")
    r = eclipses.nearest_eclipse(jd_from_calendar(33, 4, 3), "lunar", eph)
    lc = eclipses.local_circumstances(r, 31.778, 35.235, eph)
    check("AD 33-04-03 partial lunar eclipse, still in the umbra at moonrise in Jerusalem",
          r["type"] == "partial" and lc["contacts"]["U4"][1] > 0 > lc["moon_alt"], str(lc["contacts"]["U4"]))

    s = state.state(parse_time("2026-10-23T12:00"), (31.778, 35.235))
    check("state: anti-solar cell equals Sun cell XOR 3",
          s["earth"]["anti_solar_cell"] == s["bodies"]["Sun"]["cell"] ^ 3)
    v = scripture.kjv_text(43, 1, 1)
    top = codec.deobfuscate(codec.vigenere(scripture.kjv_text(1, 1, 1) + " " + scripture.kjv_text(1, 1, 2), "light",
                                           decrypt=False))[0]
    check("deobfuscate: Vigenere (key 'light') on Gen 1:1-2 recovered", top["text"].startswith("In the beginning God"),
          " > ".join(top["chain"]))
    top = codec.deobfuscate(base64.b64encode(codec.caesar(v, 13).encode()).decode())[0]
    check("deobfuscate: Base64 of ROT13 of John 1:1 recovered", top["text"] == v, " > ".join(top["chain"]))

    from . import gauge, gears, lattice
    rep = lattice.report()
    check("lattice: Q6 shells 1,6,15,20,15,6,1 from every cell; 240 squares (proved in Lean)",
          rep["q6_same_shells_for_every_source"] and rep["q6_shells_from_any_cell"] == [1, 6, 15, 20, 15, 6, 1]
          and rep["q6_square_faces"] == 240)
    th = rep["theta_shells_by_true_norm_0_2_4_6_8"]
    check("lattice: Golay weights 1/759/2576/759/1; Leech 196560 minimal vectors, 0 roots; E8^3 has 720 roots",
          rep["golay_weights"] == {0: 1, 8: 759, 12: 2576, 16: 759, 24: 1}
          and rep["leech_minimal_vectors_constructed"] == 196560 == th["Leech"][2]
          and rep["leech_minimal_vectors_failing_membership"] == 0 and th["Leech"][1] == 0 and th["E8+E8+E8"][1] == 720)
    w = gears.wind(parse_time("2026-08-12T17:46"), "saros", (-3, 3), "solar", eph)
    check("wind: 3 Saros back / forward from 2026-08-12 lands on the 1972-07-10 and 2080-09-13 eclipses",
          [r["eclipse"][:10] for r in w] == ["1972-07-10", "2080-09-13"] and all(r["saros"] == 126 for r in w))
    check("wind: state(t) is unchanged after winding a century back and forward",
          gears.reversible(parse_time("2026-10-23T12:00"), (-36525.0, 36525.0)))
    ok = all(abs(gauge.monte_carlo(3, b, sweeps=6000, seed=7)[0] - gauge.exact_mean_plaquette(3, b)) < 0.02
             for b in (0.3, 0.8))
    check("gauge: Z/2 Monte Carlo on Q3 matches the exact sum over all 4096 configurations", ok)
    from . import crossdomain as X
    comps, _ = X.codon_crystal()
    check("crystal: sl3 triples split 10+8+8+1; codons split 16+4x8+4x4 (proved in Lean)",
          sorted(map(len, X.crystal_components(3, 3).values())) == [1, 8, 8, 10]
          and sorted(map(len, comps.values())) == [4, 4, 4, 4, 8, 8, 8, 8, 16])
    rt = X.reading_operator_test()
    check("crystal: spins+weights collide on 19 classes; linear reading operators form a 1-dim space",
          rt["spin_weight_classes_with_two_or_more_amino_acids"] == 19
          and rt["linear_operators_constant_on_synonyms_dimension"] == 1)
    cr = X.circuit_report()
    check("circuits: R(Q6 antipodal)=13/30, R(Q6 adjacent)=21/64, codon graph 7/32 and 25/96 (proved in Lean)",
          [cr[k] for k in ("Q6_antipodal_resistance (Lean)", "Q6_adjacent_resistance (Lean)",
                           "codon_graph_adjacent_resistance (Lean)", "codon_graph_far_resistance UUU-GGG (Lean)")]
          == ["13/30", "21/64", "7/32", "25/96"])
    check("circuits: matrix-tree count of Q6 spanning trees equals the closed formula",
          cr["Q6_spanning_trees_matrix_tree"] == cr["Q6_spanning_trees_closed_formula"])
    check("circuits: synonymous mutations leave 22 pieces, only serine split (proved in Lean)",
          cr["synonymous_pieces"] == 22 and list(cr["amino_acids_in_more_than_one_piece"]) == ["S"])
    cd = X.cocycle_report(4)
    check("cocycles: octonion associator = -1 exactly on 168 independent triples; sedenions 672 exceptions",
          cd["dim 8"]["non-associative triples"] == 168 == cd["dim 8"]["independent triples"]
          and cd["dim 16"]["independent but associative"] == 672)
    check("topology: boundary of Q6 has the GF(2) Betti numbers of S^5",
          X.cube_homology_gf2(6, True) == [1, 0, 0, 0, 0, 1])
    sb = X.sky_braid_windings(jd_from_calendar(2000, 1, 1), jd_from_calendar(2000, 1, 1) + 8 * 365.25, 4.0)
    check("sky braid: Venus-Earth heliocentric winding over 8 years is 5 (the 8:13 resonance)",
          abs(sb["pair_windings"]["Venus-Earth"] - 5) < 0.05, str(sb["pair_windings"]["Venus-Earth"]))

    # --- calibration (2026-10-23) ---------------------------------------------------------
    from . import calibrate, hebcal, patterns
    known = {(2017, 9, 21): "1 Tishri 5778", (2023, 9, 16): "1 Tishri 5784", (2024, 4, 23): "15 Nisan 5784",
             (2017, 8, 21): "29 Av 5777", (2024, 4, 8): "29 Adar II 5784", (2045, 8, 12): "29 Av 5805"}
    got = {k: hebcal.label(hebcal.hebrew_from_civil(*k)) for k in known}
    check("Hebrew calendar: Rosh Hashana / Pesach / eclipse dates (proved in Lean)", got == known)
    r = eclipses.nearest_eclipse(parse_time("2024-04-08"), "solar", eph)
    seen = {n: eclipses.local_circumstances(r, *pl, eph)["phase_seen"] for n, pl in
            {"Dallas": (32.78, -96.80), "Indianapolis": (39.77, -86.16), "Chicago": (41.88, -87.63),
             "Jerusalem": (31.778, 35.235)}.items()}
    check("2024-04-08 local circumstances: Dallas and Indianapolis total, Chicago partial, Jerusalem none "
          "(the Sun is below the horizon there)",
          seen == {"Dallas": "total", "Indianapolis": "total", "Chicago": "partial", "Jerusalem": "none"}, str(seen))
    st = calibrate.torah_stats()
    check("Torah: 304,805 letters, gematria 21,009,826, ordinal 3,271,024, 1,820 YHVH (proved in Lean)",
          (st["letters"], st["standard"], st["ordinal"], st["yhvh"]) == (304805, 21009826, 3271024, 1820))
    check("calibration ledger: every statement evaluates",
          all(row["verdict"] != "error" for row in calibrate.run(ids={"PE-07", "PE-30", "TO-03", "GE-01", "NU-08"})))
    check("factorions: base 10 = 1, 2, 145, 40585 (proved in Lean); base 6 pair 25, 26",
          patterns.factorions(10) == [1, 2, 145, 40585] and patterns.factorions(6) == [1, 2, 25, 26])
    check("nets: square 1, cube 11 (proved in Lean), tesseract 261",
          [patterns.count_nets(n)["nets"] for n in (2, 3, 4)] == [1, 11, 261])
    mog = patterns.mog_report()
    check("MOG: hexacode 64 words; Golay 4096 words 1/759/2576/759/1; 1771 sextets; 3795 trios; columns a sextet",
          mog["hexacode_words"] == 64 and mog["golay_weights"] == {0: 1, 8: 759, 12: 2576, 16: 759, 24: 1}
          and mog["sextets"] == 1771 and mog["trios"] == 3795 and mog["columns_form_a_sextet"]
          and mog["golay_linear"])
    from . import hopf
    check("Hopf fibrations of Q6: 9 GF(8) fibres of 7 and 21 GF(4) fibres of 3, all subspaces, pairwise "
          "complementary; 18 edges inside / 168 between fibres; clutching t -> t (proved in Lean)",
          hopf.selfcheck())
    from . import music
    check("music vortexes: octave = squaring, base circuit 1-2-4-8-7-5 / 3-6 / 9, base = digit sum mod 9, "
          "14 octave classes; Tonnetz torus 12/36/24 with 6-triad vertex loops; E8 roots in 120 octave classes "
          "(proved in Lean)", music.selfcheck())
    print(f"\n{len(fails)} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    raise SystemExit(run())
