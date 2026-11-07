"""Build `hypercube/data/system.json`: the model's configuration and its anchor data.

Everything in the file is either a declared convention (labelled as such) or computed here from
the committed sources, so `python3 -m hypercube build` reproduces it byte for byte.
"""
import json
import os
import sys

from . import cells, eclipses, scripture, sky, state, store
from .timescale import format_jd, jd_from_calendar

OUT = os.path.join(store.ROOT, "hypercube", "data")

# The seven dated events of docs/MAP_TIME.md (scripts/event_cells.py): Jerusalem local mean time
# (UT + 2h21m), Julian calendar, astronomical years.
EVENTS = [
    ("Bur-Sagale eclipse / Amos 8:9", (-762, 6, 15, 12.0), "Amos 8:9"),
    ("Jerusalem taken, 2 Adar", (-596, 3, 16, 12.0), "2 Kings 24:12"),
    ("Herod's eclipse", (-3, 3, 13, 0.0), "Matthew 2:19"),
    ("Crucifixion AD 30", (30, 4, 7, 15.0), "Mark 15:33"),
    ("Crucifixion AD 33", (33, 4, 3, 15.0), "Mark 15:33"),
    ("Pentecost AD 33", (33, 5, 24, 9.0), "Acts 2:1"),
    ("Temple burned AD 70", (70, 8, 30, 12.0), "Matthew 24:2"),
]
JERUSALEM = (31.778, 35.235)

# Mean orbital elements (semi-major axis AU, sidereal period days).  Planets: JPL approximate
# elements (Standish); Ceres: the largest body of the asteroid belt.
ORBITS = [("Mercury", 0.38709927, 87.9691), ("Venus", 0.72333566, 224.701), ("Earth", 1.00000261, 365.256363),
          ("Mars", 1.52371034, 686.980), ("Ceres (asteroid belt)", 2.7675, 1680.0), ("Jupiter", 5.20288700, 4332.59),
          ("Saturn", 9.53667594, 10759.22), ("Uranus", 19.18916464, 30685.4), ("Neptune", 30.06992276, 60189.0),
          ("Pluto", 39.48211675, 90560.0)]
TITIUS_BODE_N = [None, 0, 1, 2, 3, 4, 5, 6, 7, 8]



def _round3(v):
    if isinstance(v, float):
        return round(v, 3)
    if isinstance(v, dict):
        return {k: _round3(x) for k, x in v.items()}
    return v

def titius_bode(n):
    return 0.4 if n is None else 0.4 + 0.3 * 2 ** n


def solar_system():
    rows = []
    for (name, a, p), n in zip(ORBITS, TITIUS_BODE_N):
        syn = None if name == "Earth" else 1 / abs(1 / p - 1 / 365.256363)
        rows.append({"body": name, "a_au": a, "period_days": p, "synodic_days": None if syn is None else round(syn, 3),
                     "titius_bode_n": n, "titius_bode_au": round(titius_bode(n), 3),
                     "titius_bode_error": round(a / titius_bode(n) - 1, 4)})
    return {"orbits": rows,
            "note": ("Titius-Bode a = 0.4 + 0.3 * 2^n is an empirical rule.  Its n = 3 slot (2.8 AU) is "
                     "occupied by the asteroid belt (Ceres 2.77 AU).  The belt's total mass is a few percent "
                     "of the Moon's, and the idea that it is a broken-up planet (Olbers) is not supported; "
                     "Jupiter's resonances are the accepted reason no planet formed there.  The rule fails "
                     "for Neptune (30.1 vs 38.8 AU).")}


def cycles():
    S = eclipses.SYNODIC
    return {"synodic_month": S, "draconic_month": 27.212220817, "anomalistic_month": 27.554549878,
            "sidereal_month": 27.321661547, "tropical_year": 365.242189, "sidereal_year": 365.256363,
            "eclipse_year": state.ECLIPSE_YEAR, "saros_days": 223 * S, "inex_days": 358 * S,
            "exeligmos_days": 3 * 223 * S, "metonic_days": 235 * S, "callippic_days": 4 * 235 * S,
            "precession_arcsec_per_year": 50.29, "precession_period_years": state.PRECESSION_PERIOD_YR,
            "lean": "Sovereign.Organism.HypercubeModel: saros_draconic, saros_anomalistic, metonic, "
                    "eclipse_year_bounds, inex_inverse"}


def anchors(eph):
    sys.path.insert(0, store.SCRIPTS)
    import sky_ephem as S
    out = []
    for label, (y, m, d, h), ref in EVENTS:
        jd_ut = jd_from_calendar(y, m, d, h - 2.35, "julian")
        st = state.state(jd_ut, JERUSALEM, eph=eph, bodies=sky.CLASSICAL)
        tjd = st["time"]["jd_tt"]
        bodies = {}
        for b, row in st["bodies"].items():
            old = S.body_state(b, S.jerusalem_tt("julian", y, m, d, h))
            old_cell = cells.sky_cell(old["ra_j2000"], old["dec_j2000"], old["mag"])
            bodies[b] = {"cell": row["cell"], "cell_date": row["cell_date"], "ra_j2000_h": row["ra_j2000_h"],
                         "dec_j2000": row["dec_j2000"], "mag": row["mag"], "wall_margin": row["wall_margin"],
                         "cell_previous_ephemeris": old_cell,
                         "ra_diff_min_vs_previous": round((row["ra_j2000_h"] - old["ra_j2000"]) * 60, 3)}
        near = {}
        for kind in ("solar", "lunar"):
            r = eclipses.nearest_eclipse(jd_ut, kind, eph)
            if r:
                lc = eclipses.local_circumstances(r, *JERUSALEM, eph)
                near[kind] = {"date": r["date"], "type": r["type"], "magnitude": round(r["magnitude"], 3),
                              "saros": r["saros"], "days_from_event": round(r["jd_ut"] - jd_ut, 2),
                              "jerusalem": {k: _round3(v) for k, v in lc.items() if k != "jd_ut"}}
        out.append({"event": label, "verse": ref, "jerusalem_local": f"{y}-{m:02d}-{d:02d} {h:05.2f} (Julian)",
                    "ut": format_jd(jd_ut), "bodies": bodies, "moon": st["moon"], "nearest_eclipses": near,
                    "scripture_at_sun": st["bodies"]["Sun"]["scripture"]})
    return out


def eclipse_catalogue(eph, y0, y1):
    rows = eclipses.eclipses_between(jd_from_calendar(y0, 1, 1), jd_from_calendar(y1, 1, 1), eph)
    keep = ("date", "kind", "type", "magnitude", "saros", "gamma", "jd_ut")
    return [{k: (round(r[k], 5) if isinstance(r.get(k), float) else r.get(k)) for k in keep if k in r} for r in rows]


def build(ancient=False):
    os.makedirs(OUT, exist_ok=True)
    eph = sky.default_ephemeris()
    data = {
        "meta": {
            "name": "QBX hypercube model, stage 1",
            "doc": "docs/HYPERCUBE_MODEL_2026-10-23.md",
            "sources": {k: {"file": v[0], "md5": v[1]} for k, v in store.ARCHIVES.items()},
            "ephemeris_coverage_jd": [eph.start, eph.end],
            "ephemeris_coverage": [format_jd(eph.start), format_jd(eph.end)],
            "lean": "sovereign/Sovereign/Organism/HypercubeModel.lean",
        },
        "address_rule": {"bits": ["dec > 0", "RA >= 12h", "RA mod 12h >= 6h", "RA mod 6h >= 3h",
                                  "|dec| >= 30", "mag < 1.00"],
                         "source": "Star.vertex in sovereign/Sovereign/Organism/HouseSky.lean",
                         "anti_solar": "cell XOR 3 (Lean antipode_vertex)"},
        "conventions": {
            "codon": "CodonCells.lean: U=0 C=1 A=2 G=3, first base bits 4-5 (chosen bijection)",
            "hexagram": "bit i = line i+1 from the bottom, 1 = solid (chosen bijection)",
            "tone": "RA sector -> major-scale degree, declination band -> octave (A2..A5)",
            "colour": "hue = RA sector, lightness = declination band, saturation = brightness",
            "scripture": "phase = RA*15 + shift; chapter = floor(phase*1189/360)+1 (NovaScripture.lean)",
        },
        "cells": cells.table(),
        "house_stars": [{"name": n, "ra_h": ra, "dec": de, "mag": mg, "cell": c} for n, ra, de, mg, c in state.house_stars()],
        "solar_system": solar_system(),
        "cycles": cycles(),
        "scripture": {"books": [{"n": i + 1, "name": b, "chapters": c, "first_index": o + 1}
                                for i, (b, c, o) in enumerate(zip(scripture.BOOKS, scripture.chapter_counts(),
                                                                  scripture.offsets()))],
                      "total_chapters": sum(scripture.chapter_counts()),
                      "tribes_numbers_1": dict(zip(scripture.TRIBES, scripture.CENSUS_NUM1))},
        "anchors": anchors(eph),
        "eclipses_2000_2100": eclipse_catalogue(eph, 2000, 2100),
    }
    path = os.path.join(OUT, "system.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=1)
    paths = [path]
    if ancient:
        p2 = os.path.join(OUT, "eclipses_-0800_0100.json")
        with open(p2, "w", encoding="utf-8") as f:
            json.dump(eclipse_catalogue(eph, -800, 100), f, ensure_ascii=False, separators=(",", ":"))
        paths.append(p2)
    return paths
