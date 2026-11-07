"""The multidimensional state of the system at any time and place.

`state(time, place)` returns one JSON-ready record with these axes:

* **time**: UT and TT Julian days, Delta T, Julian and Gregorian calendar dates;
* **bodies**: for the Sun, Moon and eight planets: ecliptic and equatorial coordinates (J2000 and
  of date), distance, magnitude, dome cell in both frames, distance to the nearest cell wall,
  altitude/azimuth at the place, colour, tone, codon, hexagram, scripture placement;
* **earth**: heliocentric longitude and the anti-solar cell (= Sun cell ^ 3, proved);
* **moon**: elongation, phase angle, illuminated fraction, age, lunation number, node, and the
  eclipse-season flags (the Sun close enough to a lunar node for an eclipse);
* **cycles**: phases of the Saros, inex, Metonic cycle, eclipse year and precession;
* **eclipses** (optional, slower): previous and next solar and lunar eclipse, with local
  circumstances at the place;
* **cube**: which bodies occupy which of the 64 cells, and which house stars share them.
"""
import math
import os
import re
from functools import lru_cache

from . import cells, eclipses, hebcal, scripture, sky, store
from .timescale import J2000, calendar_from_jd, delta_t_seconds, decimal_year, format_jd, ut_to_tt

SAROS = 223 * eclipses.SYNODIC
INEX = 358 * eclipses.SYNODIC
METONIC = 235 * eclipses.SYNODIC
ECLIPSE_YEAR = 1 / (1 / 27.212220817 - 1 / eclipses.SYNODIC)
PRECESSION_PERIOD_YR = 1296000 / 50.29  # 360 deg at 50.29"/yr ~ 25,770 yr
BODY_COLOUR = {"Sun": "#ffd84d", "Moon": "#d9d9e6", "Mercury": "#9e9e9e", "Venus": "#f5e6b3",
               "Mars": "#d9542b", "Jupiter": "#d9a066", "Saturn": "#e6cc80", "Uranus": "#8fd9e6",
               "Neptune": "#4d6be6", "Pluto": "#b39980"}


@lru_cache(maxsize=1)
def house_stars():
    """The 64 house stars of HouseSky.lean: (name, RA h, Dec deg, mag, J2000 cell)."""
    src = open(os.path.join(store.ROOT, "sovereign/Sovereign/Organism/HouseSky.lean"), encoding="utf-8").read()
    rows = re.findall(r'⟨(\d+), "([^"]+)", (\d+), (-?\d+), (-?\d+), "\w+"⟩', src)
    out = []
    for _, name, ra, de, mg in rows:
        ra_h, dec, mag = int(ra) / 1000, int(de) / 1000, int(mg) / 100
        out.append((name, ra_h, dec, mag, cells.sky_cell(ra_h, dec, mag)))
    return out


def _moon_node(eph, tjd):
    """Mean-free (osculating) ascending node longitude of the Moon's orbit, ecliptic J2000."""
    dt = 0.01
    r = eph.moon_geo(tjd)
    r2 = eph.moon_geo(tjd + dt)
    v = [(b - a) / dt for a, b in zip(r, r2)]
    h = [r[1] * v[2] - r[2] * v[1], r[2] * v[0] - r[0] * v[2], r[0] * v[1] - r[1] * v[0]]
    return math.degrees(math.atan2(h[0], -h[1])) % 360


def hebrew_date(jd_ut, place=None):
    """Hebrew calendar date at the place (Jerusalem if none).  The Hebrew day is taken to begin at
    18:00 local mean time, a stand-in for sunset (accurate to about an hour)."""
    lon = place[1] if place is not None else 35.235
    local = jd_ut + lon / 360.0
    y, m, d, hour = calendar_from_jd(local)
    rd = hebcal.rd_from_civil(y, m, d) + (1 if hour >= 18 else 0)
    h = hebcal.hebrew_from_rd(rd)
    return {"date": hebcal.label(h), "year": h[0], "month": h[1], "day": h[2],
            "weekday": ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"][hebcal.weekday(rd)],
            "rule": "day begins 18:00 local mean time (approximate sunset)"}


def state(jd_ut, place=None, shift_deg=0.0, with_eclipses=False, eph=None, bodies=None):
    eph = eph or sky.default_ephemeris()
    bodies = bodies or sky.BODIES
    tjd = ut_to_tt(jd_ut)
    out = {"time": {"jd_ut": jd_ut, "jd_tt": tjd, "delta_t_s": round(delta_t_seconds(decimal_year(jd_ut)), 1),
                    "ut": format_jd(jd_ut), "julian": format_jd(jd_ut, "julian"),
                    "gregorian": format_jd(jd_ut, "gregorian"), "decimal_year": round(decimal_year(jd_ut), 4)},
           "place": None if place is None else {"lat": place[0], "lon": place[1]},
           "hebrew": hebrew_date(jd_ut, place),
           "conventions": {"scripture_shift_deg": shift_deg, "cell_rule": "HouseSky Star.vertex"}}
    hs = house_stars()
    rows = {}
    for b in bodies:
        st = sky.body_state(b, jd_ut, eph, place)
        c = cells.sky_cell(st["ra_j2000_h"], st["dec_j2000"], st["mag"])
        cd = cells.sky_cell(st["ra_date_h"], st["dec_date"], st["mag"])
        dra, ddec, dmag = cells.wall_margin(st["ra_j2000_h"], st["dec_j2000"], st["mag"])
        st.update({
            "cell": c, "cell_date": cd, "wall_margin": {"ra_min": round(dra, 2), "dec_deg": round(ddec, 3),
                                                         "mag": round(dmag, 2)},
            "colour": BODY_COLOUR[b], "cell_colour": cells.colour(c), "tone_hz": round(cells.tone_hz(c), 2),
            "codon": cells.codon(c), "amino": cells.amino(c), "hexagram_lines": cells.hexagram_lines(c),
            "scripture": scripture.placement(st["ra_j2000_h"], shift_deg),
            "house_stars_in_cell": [h[0] for h in hs if h[4] == c],
        })
        for k in ("lon_j2000", "lat_j2000", "ra_j2000_h", "dec_j2000", "ra_date_h", "dec_date", "lon_date",
                  "lat_date", "mag", "alt", "az"):
            if k in st:
                st[k] = round(st[k], 5)
        st["dist_au"] = round(st["dist_au"], 7)
        del st["jd_tt"]
        rows[b] = st
    out["bodies"] = rows

    sun = rows.get("Sun") or sky.body_state("Sun", jd_ut, eph)
    sun_cell = cells.sky_cell(sun["ra_j2000_h"], sun["dec_j2000"], sun["mag"])
    earth_h = sky.lonlat(eph.helio("Earth", tjd))
    out["earth"] = {"helio_lon_j2000": round(earth_h[0], 5), "helio_dist_au": round(earth_h[2], 7),
                    "anti_solar_cell": cells.sky_antipode(sun_cell),
                    "note": "anti-solar cell = Sun cell XOR 3 (Lean: antipode_vertex), not 63 - cell"}

    elong = eclipses._elong(eph, tjd)
    node = _moon_node(eph, tjd)
    sun_lon = sky.lonlat(eph.geo("Sun", tjd))[0]
    d_node = min(abs((sun_lon - node + 180) % 360 - 180), abs((sun_lon - node) % 360 - 180))
    k = (tjd - eclipses.NEW_MOON_EPOCH) / eclipses.SYNODIC
    phase_angle = 180 - elong if elong <= 180 else elong - 180
    names = ["new", "waxing crescent", "first quarter", "waxing gibbous", "full", "waning gibbous",
             "last quarter", "waning crescent"]
    out["moon"] = {"elongation_deg": round(elong, 3), "illuminated": round((1 + math.cos(math.radians(phase_angle))) / 2, 4),
                   "phase": names[int(((elong + 22.5) % 360) // 45)], "age_days": round((elong / 360) * eclipses.SYNODIC, 2),
                   "lunation": math.floor(k), "node_lon_j2000": round(node, 3),
                   "sun_from_node_deg": round(d_node, 3),
                   "solar_eclipse_season": d_node < 18.5, "lunar_eclipse_season": d_node < 12.2}

    ref = eclipses.SOLAR_ANCHOR[0]
    dy = (jd_ut - J2000) / 365.25
    out["cycles"] = {
        "saros_phase": round(((tjd - ref) / SAROS) % 1, 5), "inex_phase": round(((tjd - ref) / INEX) % 1, 5),
        "metonic_phase": round(((tjd - J2000) / METONIC) % 1, 5),
        "eclipse_year_phase": round(((tjd - J2000) / ECLIPSE_YEAR) % 1, 5),
        "precession_deg_since_j2000": round(50.29 * dy / 3600, 4),
        "precession_phase": round((dy / PRECESSION_PERIOD_YR) % 1, 6),
        "vernal_point_lon_j2000": round((-50.29 * dy / 3600) % 360, 4),
    }

    occ = {}
    for b, st in rows.items():
        occ.setdefault(st["cell"], []).append(b)
    out["cube"] = {"occupied": {str(c): v for c, v in sorted(occ.items())},
                   "parity_of_cells": {b: cells.weight(st["cell"]) % 2 for b, st in rows.items()},
                   "classical_codons": " ".join(rows[b]["codon"] for b in sky.CLASSICAL if b in rows),
                   "classical_aminos": "".join(rows[b]["amino"] for b in sky.CLASSICAL if b in rows)}

    if with_eclipses:
        ev = {}
        for kind in ("solar", "lunar"):
            rows_e = eclipses.eclipses_between(jd_ut - 400, jd_ut + 400, eph, kinds=(kind,))
            prev = [r for r in rows_e if r["jd_ut"] <= jd_ut]
            nxt = [r for r in rows_e if r["jd_ut"] > jd_ut]
            for label, r in (("previous", prev[-1] if prev else None), ("next", nxt[0] if nxt else None)):
                if r is None:
                    continue
                rec = {k2: (round(v, 5) if isinstance(v, float) else v) for k2, v in r.items()}
                if place is not None:
                    lc = eclipses.local_circumstances(r, place[0], place[1], eph)
                    rec["local"] = {k2: (round(v, 4) if isinstance(v, float) else v) for k2, v in lc.items()}
                ev[f"{label}_{kind}"] = rec
        out["eclipses"] = ev
    return out


def series(jd_start, jd_end, step_days, place=None, bodies=None, shift_deg=0.0):
    """A list of compact frames for animation / sonification."""
    frames = []
    eph = sky.default_ephemeris()
    t = jd_start
    while t <= jd_end + 1e-9:
        s = state(t, place, shift_deg, eph=eph, bodies=bodies)
        frames.append({"jd_ut": round(t, 5), "ut": s["time"]["ut"],
                       "cells": {b: v["cell"] for b, v in s["bodies"].items()},
                       "lon": {b: v["lon_j2000"] for b, v in s["bodies"].items()},
                       "moon": s["moon"]})
        t += step_days
    return frames
