"""The gears of the system: the mean lunar/solar periods, the cycles they mesh into, and winding.

Two kinds of "winding" are offered, and they must not be confused:

* `wind` steps the *real* sky forward or backward by a whole number of cycles (Saros, inex, Metonic,
  ...) and evaluates the ephemeris there.  This is exact to ephemeris accuracy, in both directions,
  but only inside the ephemeris range (about 4200 BC .. AD 2400).  `state(t)` is a pure function of
  `t`, so winding back to a date always reproduces the same state (`reversible`).
* `mean_gear_drift` extrapolates with mean periods only (what a gear train such as the Antikythera
  mechanism does).  It works for any date but drifts, because the true periods are not exact
  ratios; the drift per cycle is reported.

Lean: `HypercubeModel.lean` proves the cycle arithmetic used here (`saros_draconic`, `metonic`, ...).
"""
from . import eclipses, sky, state
from .timescale import format_jd

SYNODIC = eclipses.SYNODIC          # new Moon to new Moon
DRACONIC = 27.212220817             # node to node
ANOMALISTIC = 27.554549878          # perigee to perigee
SIDEREAL_MONTH = 27.321661547
TROPICAL_YEAR = 365.242189
ECLIPSE_YEAR = 1 / (1 / DRACONIC - 1 / SYNODIC)

# name: (synodic months, comparison period name, count of that period)
CYCLES = {
    "saros": (223, "draconic", 242),
    "inex": (358, "draconic", 388.5),       # half-integer: next eclipse at the opposite node
    "metonic": (235, "tropical_year", 19),
    "exeligmos": (669, "draconic", 726),
    "callippic": (940, "tropical_year", 76),
    "octaeteris": (99, "tropical_year", 8),
    "tritos": (135, "draconic", 146.5),
}
PERIOD = {"draconic": DRACONIC, "anomalistic": ANOMALISTIC, "tropical_year": TROPICAL_YEAR,
          "synodic": SYNODIC}


def gear_table():
    """Each cycle: length in days, and how far the meshing period is off (days per cycle)."""
    rows = []
    for name, (m, other, n) in CYCLES.items():
        days = m * SYNODIC
        rows.append({"cycle": name, "synodic_months": m, "days": round(days, 4),
                     "years": round(days / TROPICAL_YEAR, 4), "meshes_with": f"{n} {other}",
                     "mismatch_days": round(days - n * PERIOD[other], 4),
                     "anomalistic_months": round(days / ANOMALISTIC, 3)})
    return rows


def mean_gear_drift(cycle, n):
    """Accumulated mismatch after n cycles of mean-period gearing (days; negative n = backward)."""
    m, other, k = CYCLES[cycle]
    return n * (m * SYNODIC - k * PERIOD[other])


def wind(jd_ut, cycle="saros", steps=(-3, -2, -1, 0, 1, 2, 3), kind=None, eph=None):
    """Step from `jd_ut` by whole cycles; at each step report the nearest computed eclipse.

    Starting from an eclipse, a Saros or inex step lands on another eclipse of the family; the
    printed offsets show how well the gear meshes in the real (ephemeris) sky."""
    eph = eph or sky.default_ephemeris()
    m = CYCLES[cycle][0]
    out = []
    for k in steps:
        t = jd_ut + k * m * SYNODIC
        if not (eph.start + 800 < t < eph.end - 800):
            out.append({"step": k, "jd_ut": t, "outside_ephemeris": True})
            continue
        kinds = [kind] if kind else ["solar", "lunar"]
        best = None
        for kd in kinds:
            r = eclipses.nearest_eclipse(t, kd, eph)
            if r and (best is None or abs(r["jd_ut"] - t) < abs(best["jd_ut"] - t)):
                best = r
        row = {"step": k, "target": format_jd(t)}
        if best:
            row.update({"eclipse": best["date"], "kind": best["kind"], "type": best["type"],
                        "saros": best["saros"], "offset_hours": round((best["jd_ut"] - t) * 24, 2),
                        "magnitude": round(best["magnitude"], 3)})
        out.append(row)
    return out


def reversible(jd_ut, detour_days=(-36525.0, 36525.0)):
    """Evaluate the state at t, wind away to other dates, wind back: the state is identical."""
    eph = sky.default_ephemeris()
    first = state.state(jd_ut, eph=eph)
    for d in detour_days:
        state.state(jd_ut + d, eph=eph)
    again = state.state(jd_ut, eph=eph)
    return first == again
