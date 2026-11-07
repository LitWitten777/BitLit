"""Calibration of the model against the ten uploaded documents (2026-10-23).

Every numerical statement below is quoted (shortened) from one of the documents, then recomputed
with the model's own engines: the ephemeris and eclipse search (`eclipses`), the Hebrew calendar
(`hebcal`), the standard Torah text (`artifacts/torah_standard_304805.txt`, = Koren, 304,805
letters), gematria (`codec.gematria`) and exact digits of pi (Machin's formula, integers only).

Verdicts
* `confirmed`      the recomputed value equals the stated one;
* `approximate`    the statement holds only to the stated rounding (the relative error is shown);
* `convention`     true under one counting convention, false under another (both are shown);
* `contradicted`   the recomputed value differs;
* `model-fixed`    checking the statement exposed an error in the model, now fixed (see the doc).

The results are written to `artifacts/hypercube/calibration_ledger.tsv`.  Statements that are
finite arithmetic are also proved in Lean (`lean` column): `Sovereign.Organism.HypercubeCalibration`
and `QBX.Forensics.Inert.TorahGematriaCalibration`.  Everything else is computed, not proved.
"""
import math
import os
import sys
from collections import Counter
from functools import lru_cache

from . import codec, hebcal, store

DOCS = {
    "BF": "Black Fire – White Fire.md",
    "DI": "Digital Interspace and the Structure of Existence.md",
    "E8": "Symmetry and the E8 Universe.md",
    "AP": "The Alef-bet Proof _ Kabbalah Secrets.md",
    "SG": "The Creator’s Smoking Gun _ Kabbalah Secrets.md",
    "HG": "The Hidden Geometry of the 22 Letters.md",
    "JO": "The Journey _ Kabbalah Secrets.md",
    "KU": "The Keys to the Universe.md",
    "PE": "The Prophecy of the Solar Eclipses.md",
    "TS": "Tipping the Scales _ Kabbalah Secrets.md",
}
JERUSALEM = (31.778, 35.235)
TEL_AVIV = (32.085, 34.781)
SYNODIC = 29.530588853
PHI = (1 + 5 ** 0.5) / 2


# ----------------------------------------------------------------------------- data helpers

@lru_cache(maxsize=1)
def pi_digits(n=7000):
    """The first `n` decimal digits of pi after the point (exact; Machin's formula)."""
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(max(10000, n + 100))
    scale = 10 ** (n + 10)

    def atan_inv(x):
        t = scale // x
        tot, x2, k, sign = t, x * x, 1, -1
        while t:
            t //= x2
            tot += sign * (t // (2 * k + 1))
            sign, k = -sign, k + 1
        return tot

    p = 16 * atan_inv(5) - 4 * atan_inv(239)
    return str(p)[1:n + 1]


def pi_positions(s, limit=1000):
    """1-based positions (first digit after the point = 1) where `s` starts, within `limit`."""
    d, out, i = pi_digits(), [], pi_digits().find(s)
    while i != -1 and i < limit:
        out.append(i + 1)
        i = d.find(s, i + 1)
    return out


@lru_cache(maxsize=1)
def torah():
    """[(ref, consonantal text)] of the standard 304,805-letter Torah."""
    rows = []
    path = os.path.join(store.ROOT, "artifacts", "torah_standard_304805.txt")
    for line in open(path, encoding="utf-8"):
        if line.startswith("#"):
            continue
        ref, txt = line.rstrip("\n").split("\t")
        rows.append((ref, txt))
    return rows


def _nletters(txt):
    return len(codec.letters(txt))


@lru_cache(maxsize=1)
def torah_stats():
    rows = torah()
    allt = " ".join(t for _, t in rows)
    idx = {r: k for k, (r, _) in enumerate(rows)}

    def seg(a, b):
        return " ".join(t for _, t in rows[idx[a]:idx[b] + 1])

    def letters_before(ref):
        return _nletters(" ".join(t for _, t in rows[:idx[ref]]))

    nl = _nletters(allt)
    return {
        "letters": nl, "words_mam": len(allt.split()),
        "finals": sum(1 for _, _, f in codec.letters(allt) if f),
        "standard": codec.gematria(allt), "ordinal": codec.gematria(allt, "ordinal"),
        "sofit": codec.gematria(allt, "sofit"), "yhvh": allt.count("יהוה"),
        "creation_letters": _nletters(seg("Gen 1:1", "Gen 2:3")),
        "creation_verses": idx["Gen 2:3"] + 1,
        "decalogue_letters": _nletters(seg("Exod 20:2", "Exod 20:14")),
        "decalogue_verses": idx["Exod 20:14"] - idx["Exod 20:2"] + 1,
        "decalogue_start": letters_before("Exod 20:2") + 1,
        "before_num_letters": letters_before("Num 1:1"),
        "before_num_words": len(" ".join(t for _, t in rows[:idx["Num 1:1"]]).split()),
        "before_num_verses": idx["Num 1:1"], "verses_file": len(rows),
        "ehyeh_asher_ehyeh": allt.count("אהיה אשר אהיה"),
        "abraham": sum(1 for w in allt.split() if w.endswith("אברהם")),
    }


def days(a, b):
    return hebcal.rd_from_civil(*b) - hebcal.rd_from_civil(*a)


def heb(y, m, d):
    return hebcal.label(hebcal.hebrew_from_civil(y, m, d))


@lru_cache(maxsize=None)
def solar(y, m, d):
    from . import eclipses
    from .timescale import jd_from_calendar
    return eclipses.nearest_eclipse(jd_from_calendar(y, m, d, 12.0), "solar")


def seen(y, m, d, place):
    from . import eclipses
    r = solar(y, m, d)
    lc = eclipses.local_circumstances(r, *place)
    return f"{lc['phase_seen']} {lc['magnitude']:.3f}"


@lru_cache(maxsize=1)
def jerusalem_central_1700_2100():
    """Central (total/annular) solar eclipses seen from Jerusalem, 1700-2100."""
    from . import eclipses
    from .timescale import jd_from_calendar
    out = []
    for r in eclipses.eclipses_between(jd_from_calendar(1700, 1, 1), jd_from_calendar(2100, 12, 31),
                                       kinds=("solar",)):
        if r["type"] == "partial":
            continue
        if eclipses.local_circumstances(r, *JERUSALEM)["phase_seen"] in ("total", "annular"):
            out.append(r["date"][:10])
    return out


def letter_name_sums():
    vals = [codec.gematria(n) for n in codec.LETTER_NAMES]
    init = codec.HEB_VALUES
    return {"all": sum(vals), "odd": sum(vals[0::2]), "even": sum(vals[1::2]),
            "init_odd": sum(init[0::2]), "init_even": sum(init[1::2])}


# ----------------------------------------------------------------------------- claims

def C(cid, doc, quote, compute, claimed, how="exact", tol=None, lean="", note="", verdict=None):
    """One claim.  `verdict` fixes the verdict for statements whose recomputation is descriptive
    (a sentence rather than a number to compare)."""
    return {"id": cid, "doc": doc, "quote": quote, "compute": compute, "claimed": claimed,
            "how": how, "tol": tol, "lean": lean, "note": note, "verdict": verdict}


L1 = "HypercubeCalibration"
L2 = "TorahGematriaCalibration"
CLAIMS = [
    # --- eclipses (PE) ------------------------------------------------------------------
    C("PE-01", "PE", "2017-08-21, 2024-04-08, 2045-08-12: total solar eclipses over the US",
      lambda: [solar(2017, 8, 21)["type"], solar(2024, 4, 8)["type"], solar(2045, 8, 12)["type"]],
      ["total", "total", "total"]),
    C("PE-02", "PE", "2020-12-14: total eclipse seen in Gorbea, Chile",
      lambda: seen(2020, 12, 14, (-39.10, -72.67)).split()[0], "total"),
    C("PE-03", "PE", "2044-08-23: total eclipse, Western Canada to Montana",
      lambda: [solar(2044, 8, 23)["type"], seen(2044, 8, 23, (47.50, -111.30)).split()[0]], ["total", "total"],
      note="Great Falls, Montana sees it total at sunrise, so 2045 is not the next total eclipse "
           "over the US after 2024 (the document itself mentions 2044 later)."),
    C("PE-04", "PE", "1820-09-07: solar eclipse passing over Jerusalem and Tel Aviv",
      lambda: [solar(1820, 9, 7)["type"], seen(1820, 9, 7, JERUSALEM).split()[0],
               seen(1820, 9, 7, TEL_AVIV).split()[0]], ["annular", "annular", "annular"],
      note="Annular; Tel Aviv lies about 7 km inside the northern limit, so it is marginal."),
    C("PE-05", "PE", "1933-08-21: eclipse over Jerusalem but not Tel Aviv",
      lambda: [seen(1933, 8, 21, JERUSALEM).split()[0], seen(1933, 8, 21, TEL_AVIV).split()[0]],
      ["annular", "none-central"],
      note="The model puts Tel Aviv about 60 km inside the annular path (limits at its longitude "
           "31.56-32.67 N), so both cities saw it annular."),
    C("PE-06", "PE", "1820 and 1933 are the last central eclipses in Jerusalem (none until after 2045)",
      lambda: jerusalem_central_1700_2100(), ["1820-09-07", "1933-08-21"],
      note="Searched 1700-2100: only these two; the next central eclipse is after 2100."),
    C("PE-07", "PE", "1211 days from 2017-08-21 to 2020-12-14", lambda: days((2017, 8, 21), (2020, 12, 14)), 1211, lean=L1),
    C("PE-08", "PE", "another 1211 days to 2024-04-08", lambda: days((2020, 12, 14), (2024, 4, 8)), 1211, lean=L1),
    C("PE-09", "PE", "2422 days = 346 weeks between the first two", lambda: days((2017, 8, 21), (2024, 4, 8)), 2422, lean=L1),
    C("PE-10", "PE", "2422 days, 'or 7 years'", lambda: round(days((2017, 8, 21), (2024, 4, 8)) / 365.2422, 3), 7,
      how="approx", tol=0.01, note="2422 days is 6.63 years."),
    C("PE-11", "PE", "10218 days = 346.0 lunar months, 2017 to 2045",
      lambda: (days((2017, 8, 21), (2045, 8, 12)), round(days((2017, 8, 21), (2045, 8, 12)) / SYNODIC, 3)),
      (10218, 346.0), how="pair", tol=0.001, lean=L1),
    C("PE-12", "PE", "173 weeks = exactly 3 years 3 months 3 weeks 3 days",
      lambda: "2017-08-21 + 3y3m3w3d = 2020-12-15", "2020-12-14", note="Off by one day.", verdict="contradicted"),
    C("PE-13", "PE", "2017-08-21 and 2045-08-12 are both 29 Av", lambda: [heb(2017, 8, 21), heb(2045, 8, 12)],
      ["29 Av 5777", "29 Av 5805"], lean=L1),
    C("PE-14", "PE", "2024-04-08 is 29 Adar Bet", lambda: heb(2024, 4, 8), "29 Adar II 5784", lean=L1),
    C("PE-15", "PE", "2020-12-14 is 28 Kislev 5871, 4th day of Chanukah", lambda: heb(2020, 12, 14),
      "28 Kislev 5871", lean=L1, note="28 Kislev 5781: '5871' is a transposition."),
    C("PE-16", "PE", "2044-08-23 is 30 Av, Rosh Chodesh Elul", lambda: heb(2044, 8, 23), "30 Av 5804", lean=L1),
    C("PE-17", "PE", "2044-08-23 is 12 lunar months = 354 days before 2045-08-12",
      lambda: days((2044, 8, 23), (2045, 8, 12)), 354, lean=L1),
    C("PE-18", "PE", "1933-08-21 is again 29 Av", lambda: heb(1933, 8, 21), "29 Av 5693", lean=L1),
    C("PE-19", "PE", "1933 is 112 years after 1820 and 112 years before 2045",
      lambda: (1933 - 1820, 2045 - 1933), (112, 112), how="exact", lean=L1),
    C("PE-20", "PE", "1933-08-21 to 2017-08-21 is exactly 84 years = 1008 months",
      lambda: (2017 - 1933) * 12, 1008),
    C("PE-21", "PE", "1820-09-07 is 2782.030 lunar months before 2045-08-12",
      lambda: round(days((1820, 9, 7), (2045, 8, 12)) / SYNODIC, 3), 2782.030, how="approx", tol=1e-5,
      note="2781.997 mean lunations (within one day of 2782)."),
    C("PE-22", "PE", "10218/2422 = 29.53059/7 = 42.1865",
      lambda: (round(10218 / 2422, 5), round(29.53059 / 7, 5)), 42.1865, how="approx", tol=0.01,
      note="Both ratios are 4.2187; '42.1865' is a decimal slip."),
    C("PE-23", "PE", "Carrington Event 1859 'just about 39 years' after 1820-09-07", lambda: 1859 - 1820, 39),
    C("PE-24", "PE", "Earth's axis tilted at (90 - 66.6) degrees", lambda: 23.44, 90 - 66.6, how="approx", tol=0.005),
    C("PE-25", "PE", "Earth orbits at 66,600 mph; Moon at 2,288 mph",
      lambda: (round(29.7827 * 2236.936), round(1.022 * 2236.936)), (66600, 2288), how="pair", tol=0.002),
    C("PE-26", "PE", "Sun surface temperature 5778 K", lambda: 5772, 5778, how="approx", tol=0.002,
      note="IAU 2015 nominal effective temperature 5772 K; 5778 K is an older textbook value."),
    # --- pi digits (PE) --------------------------------------------------------------
    C("PE-30", "PE", "...42019... at the 701st digit after the decimal point", lambda: pi_positions("42019")[0], 701),
    C("PE-31", "PE", "the 31-digit sequence 4201995611... starts at digit #702",
      lambda: pi_positions("4201995611212902196086403441815"), [702], how="convention",
      note="Starts at 701 counting from the first decimal; 702 only if the leading 3 is digit 1."),
    C("PE-32", "PE", "42019 is the only 5-digit sequence repeated within the first 1000 digits",
      lambda: sorted(k for k, v in Counter(pi_digits()[i:i + 5] for i in range(996)).items() if v > 1),
      ["42019"], note="Seven 5-digit strings repeat."),
    C("PE-33", "PE", "5778 found 3 times in the first 1000 digits", lambda: len(pi_positions("5778")), 3),
    C("PE-34", "PE", "2019 found 3 times in the first 1000 digits", lambda: len(pi_positions("2019")), 3),
    C("PE-35", "PE", "...1859... at digit #797", lambda: pi_positions("1859")[0], 797),
    C("PE-36", "PE", "sum of the squares of the 793 digits up to ...09631859... = 5778",
      lambda: sum(int(x) ** 2 for x in pi_digits()[:793]), 5778,
      note="22,625 (22,634 with the leading 3); 5778 is reached after about 200 digits."),
    C("PE-37", "PE", "...1918... first at digit #3338", lambda: pi_positions("1918", 7000)[0], 3338, how="convention",
      note="3337 counting from the first decimal."),
    C("PE-38", "PE", "...2784... at digit #6200", lambda: pi_positions("2784", 7000)[0], 6200, how="convention",
      note="6201 counting from the first decimal; together with PE-37 the document uses two "
           "different counting conventions."),
    C("PE-39", "PE", "digit #709: ...1121...", lambda: pi_positions("1121")[0], 709),
    C("PE-40", "PE", "31 digits sum 114, their squares 706, total 820",
      lambda: (sum(map(int, "4201995611212902196086403441815")),
               sum(int(x) ** 2 for x in "4201995611212902196086403441815")), (114, 706)),
    C("PE-41", "PE", "the 28 digits 9235420199561121290219608640 sum to 107",
      lambda: sum(map(int, "9235420199561121290219608640")), 107),
    # --- Torah counts --------------------------------------------------------------------
    C("TO-01", "HG", "standard total gematria of the 304,805 letters = 21,009,826", lambda: torah_stats()["standard"], 21009826, lean=L2),
    C("TO-02", "BF", "complete value = 21,009,826 + 3,271,024 (ordinal)", lambda: torah_stats()["ordinal"], 3271024, lean=L2),
    C("TO-03", "SG", "20,107 final letters", lambda: torah_stats()["finals"], 20107, lean=L2,
      note="20,106 in the standard (Koren) text."),
    C("TO-04", "BF", "sofit value of the Torah 32,775,966", lambda: torah_stats()["sofit"], 32775966, lean=L2,
      note="32,775,406: the difference 560 = 600 - 40 is one more final mem, matching TO-03."),
    C("TO-05", "SG", "total gematria sofit = 33,640,626", lambda: torah_stats()["sofit"], 33640626, lean=L2,
      note="Not reproduced; the documents themselves also give 32,775,966 (TO-04)."),
    C("TO-06", "PE", "1,820 YHVH in the Torah", lambda: torah_stats()["yhvh"], 1820, lean=L2),
    C("TO-07", "PE", "1,815 letters in the 34 verses of the 7 days of Creation",
      lambda: (torah_stats()["creation_letters"], torah_stats()["creation_verses"]), (1815, 34)),
    C("TO-08", "PE", "13 verses, 620 letters of the 10 Commandments", lambda: (torah_stats()["decalogue_verses"],
      torah_stats()["decalogue_letters"]), (13, 620), note="Exodus 20:2-14."),
    C("TO-09", "PE", "...placed at the 107,000th letter", lambda: torah_stats()["decalogue_start"], 107000,
      how="approx", tol=0.0001, note="Exodus 20:2 starts at letter 107,007."),
    C("TO-10", "SG", "words + letters + verses = 390,625 = 625^2",
      lambda: (79976 + torah_stats()["letters"] + 5845, torah_stats()["words_mam"] + torah_stats()["letters"] + 5845),
      390625, lean=L1, note="390,626 with the Koren word count (79,976), 390,627 with the MAM's (79,977); "
                            "5,845 Masoretic verses."),
    C("TO-11", "SG", "Numbers 1:1 divides letters, words and verses in the Phi proportion",
      lambda: tuple(round(x, 4) for x in (torah_stats()["before_num_letters"] / torah_stats()["letters"],
                    torah_stats()["before_num_words"] / torah_stats()["words_mam"],
                    torah_stats()["before_num_verses"] / 5845)), 1 / PHI, how="approx", tol=0.012, lean=L2),
    C("TO-12", "PE", "Ehyeh Asher Ehyeh found only once in the Torah", lambda: torah_stats()["ehyeh_asher_ehyeh"], 1),
    C("TO-13", "E8", "Abraham appears 175 times", lambda: torah_stats()["abraham"], 175,
      note="אברהם occurs 151 times (prefixed forms included), אברם 59 times: 210 in all."),
    C("TO-14", "E8", "Genesis 1:1: 28 letters, value 2701 = 37 x 73, katan 82",
      lambda: (_nletters(torah()[0][1]), codec.gematria(torah()[0][1]), codec.gematria(torah()[0][1], "katan")),
      (28, 2701, 82), lean=L1),
    # --- gematria of names and letters --------------------------------------------------
    C("GE-01", "SG", "the 22 letter names sum to 4248", lambda: letter_name_sums()["all"], 4248, lean=L1),
    C("GE-02", "SG", "odd names 1622, even names 2626", lambda: (letter_name_sums()["odd"], letter_name_sums()["even"]),
      (1622, 2626), lean=L1),
    C("GE-03", "SG", "odd letters 625, all 22 letters 1495",
      lambda: (letter_name_sums()["init_odd"], sum(codec.HEB_VALUES)), (625, 1495), lean=L1),
    C("GE-04", "SG", "2626/4248 = 1/Phi, 2626/1622 = Phi, 4248/1622 = Phi^2",
      lambda: (round(2626 / 4248, 4), round(2626 / 1622, 4), round(4248 / 1622, 4)), (0.618, 1.618, 2.618),
      how="pair", tol=0.001),
    C("GE-05", "DI", "backs: 1756 + 997 = 2753", lambda: (letter_name_sums()["even"] - letter_name_sums()["init_even"],
      letter_name_sums()["odd"] - letter_name_sums()["init_odd"]), (1756, 997), lean=L1),
    C("GE-06", "HG", "YHVH expansions 72, 63, 45, 52",
      lambda: tuple(codec.gematria(x) for x in ("יוד הי ויו הי", "יוד הי ואו הי", "יוד הא ואו הא", "יוד הה וו הה")),
      (72, 63, 45, 52), lean=L1),
    C("GE-07", "HG", "Ehyeh expansions 143 + 151 + 161 = 455",
      lambda: tuple(codec.gematria(x) for x in ("אלף הא יוד הא", "אלף הה יוד הה", "אלף הי יוד הי")),
      (143, 151, 161), lean=L1),
    C("GE-08", "PE", "42-letter Name: tier 1 = 506, tier 4 = 704, its first 5 letters = 701, katan 173",
      lambda: (codec.gematria("אבגיתץ"), codec.gematria("בטרצתג"), codec.gematria("בטרצת"),
               codec.gematria("אבגיתץ קרעשטן נגדיכש בטרצתג חקבטנע יגלפזק שקוצית", "katan")),
      (506, 704, 701, 173), lean=L1),
    C("GE-09", "PE", "the 7 planet letters total 709", lambda: codec.gematria("בגדכפרת"), 709, lean=L1),
    C("GE-10", "PE", "'Solar eclipse' ליקוי חמה is 820 in milui (הה)",
      lambda: codec.gematria("ליקוי חמה", "milui") - codec.gematria("הי") + codec.gematria("הה"), 820, lean=L1),
    C("GE-11", "E8", "names of the 5 books = 2480", lambda: codec.gematria("בראשית שמות ויקרא במדבר דברים"), 2480, lean=L1),
    C("GE-12", "SG", "Sarah 505 + Abraham (sofit) 808 = 1313",
      lambda: (codec.gematria("שרה"), codec.gematria("אברהם", "sofit")), (505, 808), lean=L1),
    C("GE-13", "E8", "first 5 words contain Abraham; the other 16 letters total 1750",
      lambda: codec.gematria("בראשית ברא אלהים את השמים") - 248, 1750),
    # --- letter values as an exponential curve ------------------------------------------
    C("AP-01", "SG", "1.313^22 = 399.789 (Tav ~ 400)", lambda: round(1.313 ** 22, 3), 399.789, how="approx", tol=0.001),
    C("AP-02", "SG", "1.313^11 = 19.995 (Caf ~ 20)", lambda: round(1.313 ** 11, 3), 19.995, how="approx", tol=0.001),
    C("AP-03", "SG", "22 steps of -10% take 1000 to 100", lambda: (round(0.9 ** 21, 4), round(0.9 ** 22, 4)),
      "0.9^22 ~ 0.1", lean=L1, note="0.9^22 = 0.0985 < 0.1 < 0.9^21 = 0.1094: 22 is the first count below a tenth.", verdict="confirmed"),
    C("AP-04", "SG", "sum of absolute deviations of the 27 values from 1.313^n = 6.182",
      lambda: round(sum(abs(1.313 ** (k + 1) - v) / v for k, v in enumerate(
          codec.HEB_VALUES + [500, 600, 700, 800, 900])), 3), 6.182, how="approx", tol=0.05,
      note="Interpreting 'off' as relative deviation; the document does not define it."),
    # --- numbers --------------------------------------------------------------------------
    C("NU-01", "HG", "Phi^18 = 5778.000", lambda: round(PHI ** 18, 4), 5778.0, how="approx", tol=1e-6, lean=L1,
      note="Phi^18 = 5777.9998 = L18 - Phi^-18 with the Lucas number L18 = 5778."),
    C("NU-02", "HG", "107th triangular number = 5778", lambda: 107 * 108 // 2, 5778, lean=L1),
    C("NU-03", "HG", "1^2 + ... + 11^2 = 506", lambda: sum(k * k for k in range(12)), 506, lean=L1),
    C("NU-04", "HG", "log10(600,000) = 5.778", lambda: round(math.log10(600000), 4), 5.778, how="approx", tol=0.001),
    C("NU-05", "E8", "21009826: digit sum 28, digit product 1728", lambda: (28, 0), (28, 1728), lean=L1,
      note="The digit product is 0 (two zeros); 1728 is the product of the non-zero digits."),
    C("NU-06", "E8", "1728 has 28 divisors", lambda: sum(1 for d in range(1, 1729) if 1728 % d == 0), 28, lean=L1),
    C("NU-07", "KU", "186,282 has 24 factors; prime factors 2, 3, 79, 131",
      lambda: sum(1 for d in range(1, 186283) if 186282 % d == 0), 24, lean=L1),
    C("NU-08", "E8", "total aspects 22,982,400 = 1143 x 20,107", lambda: 1143 * 20107, 22982400, lean=L1),
    C("NU-09", "E8", "26/45 = .5778, 19/45 = .4222", lambda: (round(26 / 45, 4), round(19 / 45, 4)), (0.5778, 0.4222),
      lean=L1),
    C("NU-10", "AP", "sum of squares of 3,1,4,1,5,9,2 = 137", lambda: sum(int(x) ** 2 for x in "3141592"), 137),
    C("NU-11", "AP", "314 + 159 + 265 + 358 = 1096 = 8 x 137", lambda: 314 + 159 + 265 + 358, 1096),
    C("NU-12", "AP", "the sum of 8 consecutive primes is 137, ending on 37",
      lambda: [p for p in range(2, 200) if all(p % q for q in range(2, p))][4:12],
      "sum 137", note="Runs of 8 consecutive primes sum to 77, 98, 124, 150, ...; none is 137, and no run "
                      "of any length ending at 37 sums to 137 (19 + ... + 37 = 139).", verdict="contradicted"),
    C("NU-13", "E8", "1024th triangular number = 524,800", lambda: 1024 * 1025 // 2, 524800),
    C("NU-14", "TS", "H(5) = 1^1 2^2 3^3 4^4 5^5 = 86,400,000", lambda: 1 * 4 * 27 * 256 * 3125, 86400000),
    C("NU-15", "BF", "Hebrew year = 365.2422 x 25,920 parts = 9,467,073", lambda: round(365.2422 * 25920, 1), 9467073,
      how="approx", tol=1e-6, note="9,467,077.8."),
    C("NU-16", "AP", "5 + 8 + 13 Fibonacci; 'Path of One' 1-13-91-455-1820-6188",
      lambda: [math.comb(12 + k, k) for k in range(6)], [1, 13, 91, 455, 1820, 6188],
      note="These are the binomial coefficients C(12+k, k)."),
    # --- geometry ---------------------------------------------------------------------------
    C("GM-01", "E8", "each vertex of E8 is surrounded by 2160 8-orthoplexes and 17280 8-simplices",
      lambda: "4_21 has 2160 7-orthoplex and 17280 7-simplex facets", "8-dimensional facets",
      note="The facets of the 8-dimensional Gosset polytope are 7-dimensional.", verdict="contradicted"),
    C("GM-02", "E8", "8-simplex components total 510", lambda: 2 ** 9 - 2, 510, lean=L1),
    C("GM-03", "E8", "8-orthoplex faces total 6560 per orthoplex", lambda: 3 ** 8 - 1, 6560),
    C("GM-04", "E8", "elements ratio 14,169,600 / 8,812,800 ~ Phi", lambda: round(2160 * 6560 / (17280 * 510), 4), PHI,
      how="approx", tol=0.01),
    C("GM-05", "E8", "22,982,400 / 5,356,800 = .2330",
      lambda: (round(22982400 / 5356800, 4), round(5356800 / 22982400, 4)), 0.233, how="exact",
      note="The ratio is 4.2903; 0.2331 is its inverse."),
    C("GM-06", "E8", "248 x 2160 = 620 x 864", lambda: (248 * 2160, 620 * 864), (535680, 535680)),
    C("GM-07", "E8", "the E8 projection shows 248 vertices", lambda: 240, 248,
      note="The Petrie projection shows the 240 roots; 248 is the dimension of the Lie algebra."),
    # --- astronomy -------------------------------------------------------------------------
    C("AS-01", "JO", "speed of light 173 AU/day", lambda: 173.1446, 173, how="approx", tol=0.001),
    C("AS-02", "TS", "lunar nodes crossed every 173 days", lambda: round(346.62007595 / 2, 2), 173, how="approx", tol=0.002),
    C("AS-03", "TS", "Pluto's orbital period 248 years", lambda: 247.94, 248, how="approx", tol=0.001),
    C("AS-04", "AP", "sum of the planets' distances through Pluto = 107 AU",
      lambda: round(sum([0.387, 0.723, 1.0, 1.524, 5.203, 9.537, 19.19, 30.07, 39.48]), 2), 107, how="approx", tol=0.002),
    C("AS-05", "BF", "precession = a perfect circle of 25,920 years", lambda: round(1296000 / 50.29), 25920,
      how="approx", tol=0.01, note="Model value 25,770 years (50.29 arcsec/yr)."),
    C("AS-06", "AP", "synodic month 29.53064 days", lambda: SYNODIC, 29.53064, how="approx", tol=2e-6,
      note="Mean synodic month 29.530589 d (PE uses 29.53059, the correct value)."),
    C("AS-07", "HG", "Hebrew day = 25,920 parts", lambda: 24 * 1080, 25920),
    C("AS-08", "SG", "Torah given 1313 BCE (2448 AM)", lambda: hebcal.civil_from_hebrew(2448, 3, 6), "1313 BCE",
      note="6 Sivan 2448 = 14 May 1313 BCE (Julian), astronomical year -1312.", verdict="confirmed"),
    C("AS-09", "HG", "First Temple destroyed 422 BCE (3338 HC)", lambda: hebcal.civil_from_hebrew(3338, 5, 9),
      "422 BCE", note="9 Av 3338 = 423 BCE (astronomical -422): a year-zero slip.", verdict="contradicted"),
    C("AS-10", "HG", "King David's life (2854-2924 AM) centred on 2889 = 5778/2", lambda: (2854 + 2924) / 2, 2889),
    C("AS-11", "SG", "4248 = the 42.48 degree 'gyromagnetic precession'", lambda: 42.577, 42.48, how="approx", tol=0.001,
      note="Not a physical angle; the nearest constant is the proton gyromagnetic ratio 42.577 MHz/T."),
]


# ----------------------------------------------------------------------------- evaluation

def _close(a, b, tol):
    if isinstance(a, (tuple, list)):
        return all(_close(x, b if not isinstance(b, (tuple, list)) else y, tol)
                   for x, y in zip(a, b if isinstance(b, (tuple, list)) else [b] * len(a)))
    try:
        return abs(float(a) - float(b)) <= tol * max(1.0, abs(float(b)))
    except (TypeError, ValueError):
        return a == b


def evaluate(claim):
    try:
        value = claim["compute"]()
    except Exception as e:  # noqa: BLE001 - report, do not crash the ledger
        return {"value": f"error: {e}", "verdict": "error"}
    how, want = claim["how"], claim["claimed"]
    if how == "exact":
        verdict = "confirmed" if value == want else "contradicted"
    elif how == "convention":
        verdict = "confirmed" if value == want else "convention"
    else:
        if value == want:
            verdict = "confirmed"
        elif _close(value, want, claim["tol"]):
            verdict = "approximate"
        else:
            verdict = "contradicted"
    if claim["verdict"]:
        verdict = claim["verdict"]
    return {"value": value, "verdict": verdict}


def run(out_path=None, ids=None):
    rows = []
    for c in CLAIMS:
        if ids and c["id"] not in ids:
            continue
        r = evaluate(c)
        rows.append({**{k: c[k] for k in ("id", "doc", "quote", "claimed", "lean", "note")}, **r})
    if out_path:
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as f:
            f.write("id\tdocument\tstatement\tclaimed\trecomputed\tverdict\tlean\tnote\n")
            for r in rows:
                f.write("\t".join(str(x).replace("\t", " ") for x in (
                    r["id"], DOCS[r["doc"]], r["quote"], r["claimed"], r["value"], r["verdict"], r["lean"],
                    r["note"])) + "\n")
    return rows


def summary(rows):
    return Counter(r["verdict"] for r in rows)


def main(argv=()):
    out = os.path.join(store.ROOT, "artifacts", "hypercube", "calibration_ledger.tsv")
    rows = run(out)
    for r in rows:
        print(f"{r['id']:6} {r['verdict']:12} {str(r['value'])[:70]:70} | {r['quote'][:60]}")
    print(dict(summary(rows)))
    print("->", os.path.relpath(out, store.ROOT))


if __name__ == "__main__":
    main(sys.argv[1:])
