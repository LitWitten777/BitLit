"""Solar and lunar eclipses computed from the ephemeris (not from a catalogue).

Method (classical, geocentric):
1. find every new and full Moon (elongation 0 deg / 180 deg) by root finding;
2. find the minimum geocentric separation beta of the Moon from the Sun (solar) or from the
   centre of the Earth's shadow (lunar) within +/- 0.6 day;
3. compare beta with the parallaxes pi and semi-diameters s of Sun and Moon:
   * solar eclipse somewhere on Earth  iff beta < pi_M - pi_S + s_M + s_S;
     central (the shadow axis meets the Earth) iff beta < pi_M - pi_S (approximately);
     total if the Moon's disc seen from the sub-lunar surface point exceeds the Sun's, annular if
     even that does not, hybrid in between;
   * lunar: umbra radius 1.02 (pi_M + pi_S - s_S), penumbra 1.02 (pi_M + pi_S + s_S) (Chauvenet's
     enlargement); umbral magnitude (rho_U + s_M - beta) / (2 s_M).
4. Saros: 223 lunations keep the series, 358 lunations (one inex) add 1, so the series number is
   fixed modulo 223 by the lunation count; it is lifted to an integer using the series active
   at the date (anchored on 2017-08-21 = solar Saros 145 and 2022-11-08 = lunar Saros 136).

Accuracy: eclipse dates and types are robust; magnitudes are good to a few hundredths; the
geocentric approximation can mislabel grazing (non-central total/annular) cases and 'hybrid'.
Local circumstances (`local_circumstances`) use topocentric positions on a spherical Earth.
"""
import math

from . import sky
from .timescale import format_jd, tt_to_ut, ut_to_tt

SYNODIC = 29.530588853
NEW_MOON_EPOCH = 2451550.09766  # TT, 2000-01-06 new Moon (Meeus 49.1, k = 0)
SAROS_INV = 38                  # 358 * 38 = 13604 = 61 * 223 + 1, so 358^-1 = 38 (mod 223)
SOLAR_ANCHOR = (2457987.27, 145, 139)   # (JD of 2017-08-21 eclipse, its Saros, centre of active series)
LUNAR_ANCHOR = (2459891.96, 136, 130)   # (JD of 2022-11-08 eclipse, its Saros, centre of active series)
ABERRATION_DEG = 20.4955 / 3600


def _elong(eph, tjd):
    """Moon minus apparent Sun ecliptic longitude, degrees in [0, 360)."""
    sl = sky.lonlat(eph.geo("Sun", tjd))[0] - ABERRATION_DEG
    ml = sky.lonlat(eph.moon_geo(tjd))[0]
    return (ml - sl) % 360


def syzygy(eph, k_half):
    """TT of lunation `k_half` (integer: new Moon, integer + 0.5: full Moon)."""
    target = (k_half % 1) * 360
    t = NEW_MOON_EPOCH + SYNODIC * k_half
    for _ in range(12):
        d = (_elong(eph, t) - target + 180) % 360 - 180
        t -= d / 12.19
        if abs(d) < 1e-7:
            break
    return t


def _sun_moon(eph, tjd):
    s, m = eph.geo("Sun", tjd), eph.moon_geo(tjd)
    # apparent Sun: aberration shifts it back along the ecliptic by ~20.5"
    lon, lat, r = sky.lonlat(s)
    lon -= ABERRATION_DEG
    s = [r * math.cos(math.radians(lat)) * math.cos(math.radians(lon)),
         r * math.cos(math.radians(lat)) * math.sin(math.radians(lon)), r * math.sin(math.radians(lat))]
    return s, m


def _golden(f, a, b, tol=1e-6):
    g = (math.sqrt(5) - 1) / 2
    c, d = b - g * (b - a), a + g * (b - a)
    fc, fd = f(c), f(d)
    while b - a > tol:
        if fc < fd:
            b, d, fd = d, c, fc
            c = b - g * (b - a)
            fc = f(c)
        else:
            a, c, fc = c, d, fd
            d = a + g * (b - a)
            fd = f(d)
    return (a + b) / 2


def _saros(k_half, tjd, solar):
    jd0, s0, centre = SOLAR_ANCHOR if solar else LUNAR_ANCHOR
    k0 = round((jd0 - NEW_MOON_EPOCH) / SYNODIC * 2) / 2
    dk = int(round(k_half - k0))
    b = (dk * SAROS_INV) % 223
    expect = centre - s0 + (tjd - jd0) / (358 * SYNODIC)
    while b - expect > 111.5:
        b -= 223
    while expect - b > 111.5:
        b += 223
    return s0 + b


def _radii(s, m):
    ds, dm = sky._norm(s), sky._norm(m)
    return (math.degrees(math.asin(sky.EARTH_RADIUS_AU / dm)), math.degrees(math.asin(sky.EARTH_RADIUS_AU / ds)),
            math.degrees(math.asin(sky.MOON_RADIUS_AU / dm)), math.degrees(math.asin(sky.SUN_RADIUS_AU / ds)), dm)


def eclipse_at(eph, k_half):
    """Eclipse record for lunation `k_half`, or None if there is no eclipse."""
    solar = (k_half % 1) == 0
    t0 = syzygy(eph, k_half)

    def beta(t):
        s, m = _sun_moon(eph, t)
        return sky.angsep(s if solar else [-c for c in s], m)

    tmax = _golden(beta, t0 - 0.6, t0 + 0.6)
    b = beta(tmax)
    s, m = _sun_moon(eph, tmax)
    pm, ps, sm, ss, dm = _radii(s, m)
    rec = {"kind": "solar" if solar else "lunar", "lunation": k_half, "jd_tt": tmax,
           "jd_ut": tt_to_ut(tmax), "beta_deg": b, "moon_sd_deg": sm, "sun_sd_deg": ss}
    if solar:
        limit = pm - ps + sm + ss
        if b >= limit:
            return None
        rec["gamma"] = b / (pm - ps)  # ~ distance of the shadow axis from the Earth's centre, in Earth radii
        rec["magnitude"] = (limit - b) / (2 * ss)
        if b < pm - ps:
            sm_near = math.degrees(math.asin(sky.MOON_RADIUS_AU / (dm - sky.EARTH_RADIUS_AU)))
            if sm > ss:
                kind = "total"
            elif sm_near > ss:
                kind = "hybrid"
            else:
                kind = "annular"
            rec["magnitude"] = sm / ss
        else:
            kind = "partial"
        rec["type"] = kind
    else:
        ru = 1.02 * (pm + ps - ss)
        rp = 1.02 * (pm + ps + ss)
        if b >= rp + sm:
            return None
        rec["umbral_magnitude"] = (ru + sm - b) / (2 * sm)
        rec["penumbral_magnitude"] = (rp + sm - b) / (2 * sm)
        rec["type"] = "total" if b < ru - sm else ("partial" if b < ru + sm else "penumbral")
        rec["magnitude"] = rec["umbral_magnitude"] if rec["type"] != "penumbral" else rec["penumbral_magnitude"]
    rec["saros"] = _saros(k_half, tmax, solar)
    rec["date"] = format_jd(rec["jd_ut"])
    return rec


def eclipses_between(jd_ut_start, jd_ut_end, eph=None, kinds=("solar", "lunar")):
    eph = eph or sky.default_ephemeris()
    t0, t1 = ut_to_tt(jd_ut_start), ut_to_tt(jd_ut_end)
    k = math.floor((t0 - NEW_MOON_EPOCH) / SYNODIC) - 1
    out = []
    while True:
        for kh in (k, k + 0.5):
            if ("solar" if kh % 1 == 0 else "lunar") not in kinds:
                continue
            approx = NEW_MOON_EPOCH + SYNODIC * kh
            if approx < eph.start + 2 or approx > eph.end - 2:
                continue
            if approx < t0 - 2:
                continue
            if approx > t1 + 2:
                return [r for r in out if jd_ut_start <= r["jd_ut"] <= jd_ut_end]
            r = eclipse_at(eph, kh)
            if r:
                out.append(r)
        k += 1


def nearest_eclipse(jd_ut, kind="solar", eph=None):
    """The eclipse of `kind` closest in time to `jd_ut` (searching +/- 2 years)."""
    rows = eclipses_between(jd_ut - 731, jd_ut + 731, eph, kinds=(kind,))
    return min(rows, key=lambda r: abs(r["jd_ut"] - jd_ut)) if rows else None


def local_circumstances(rec, lat, lon, eph=None):
    """Greatest phase seen from (lat, lon): topocentric obscuration (solar) or Moon altitude
    (lunar).  Returns a dict with UT of maximum, magnitude seen there and altitudes."""
    eph = eph or sky.default_ephemeris()
    t_mid = rec["jd_tt"]

    def topo(t):
        jd_ut = tt_to_ut(t)
        P = sky.precession_matrix(t)
        s, m = _sun_moon(eph, t)
        s_e = sky.matvec(P, sky.ecl_to_equ_vec(s))
        m_e = sky.matvec(P, sky.ecl_to_equ_vec(m))
        o = sky.observer_equ_date(lat, lon, jd_ut)
        return jd_ut, [a - b for a, b in zip(s_e, o)], [a - b for a, b in zip(m_e, o)]

    if rec["kind"] == "solar":
        def look(t):
            jd_ut, s, m = topo(t)
            d = sky.angsep(s, m)
            ss = math.degrees(math.asin(sky.SUN_RADIUS_AU / sky._norm(s)))
            sm = math.degrees(math.asin(sky.MOON_RADIUS_AU / sky._norm(m)))
            alt, az = sky.alt_az(s, lat, lon, jd_ut)
            return jd_ut, d, ss, sm, alt, az

        def sep(t):
            return look(t)[1]

        # Geometric maximum (may fall while the Sun is below the horizon).
        tm = _golden(sep, t_mid - 0.25, t_mid + 0.25)
        jd_g, d_g, ss_g, sm_g, alt_g, _ = look(tm)
        mag_g = max(0.0, (ss_g + sm_g - d_g) / (2 * ss_g))
        # Visible maximum: only instants with the Sun's upper limb above the horizon
        # (altitude > -0.83 deg, refraction included) count.  Calibration fix 2026-10-23: the
        # earlier version reported the obscuration at the geometric maximum even when the Sun
        # was below the horizon (e.g. 2024-04-08 "partial 0.99" for Jerusalem at night).
        HORIZON = -0.833
        step = 2.0 / 1440
        best, t = None, t_mid - 0.25
        while t <= t_mid + 0.25:
            jd_u, d, ss, sm, alt, az = look(t)
            if alt > HORIZON and d < ss + sm and (best is None or d < best[1]):
                best = (t, d)
            t += step
        if best is not None:
            lo, hi = best[0] - step, best[0] + step
            tv = _golden(lambda x: look(x)[1] if look(x)[4] > HORIZON else 10.0, lo, hi, tol=1e-7)
            jd_ut, d, ss, sm, alt, az = look(tv)
            if alt <= HORIZON:
                jd_ut, d, ss, sm, alt, az = look(best[0])
            mag = max(0.0, (ss + sm - d) / (2 * ss))
            if d < abs(sm - ss):
                phase = "total" if sm > ss else "annular"
            elif d < sm + ss:
                phase = "partial"
            else:
                phase = "none"
        else:
            jd_ut, d, ss, sm, alt, az = look(tm)
            mag, phase = 0.0, "none"
        return {"ut": format_jd(jd_ut), "jd_ut": jd_ut, "separation_deg": d, "magnitude": mag,
                "phase_seen": phase, "sun_alt": alt, "sun_az": az,
                "geometric_max": {"ut": format_jd(jd_g), "magnitude": mag_g, "sun_alt": alt_g}}
    jd_ut, s, m = topo(t_mid)
    alt, az = sky.alt_az(m, lat, lon, jd_ut)
    out = {"ut": format_jd(jd_ut), "jd_ut": jd_ut, "moon_alt": alt, "moon_az": az,
           "visible_at_maximum": alt > 0, "contacts": {}}
    for name, t in lunar_contacts(rec, eph).items():
        ju, _, mm = topo(t)
        out["contacts"][name] = (format_jd(ju), round(sky.alt_az(mm, lat, lon, ju)[0], 2))
    return out


def lunar_contacts(rec, eph=None):
    """TT of the penumbral (P1, P4), umbral (U1, U4) and total (U2, U3) contacts that occur."""
    eph = eph or sky.default_ephemeris()
    tm = rec["jd_tt"]

    def excess(t, which):
        s, m = _sun_moon(eph, t)
        b = sky.angsep([-c for c in s], m)
        pm, ps, sm, ss, _ = _radii(s, m)
        r = {"P": 1.02 * (pm + ps + ss) + sm, "U": 1.02 * (pm + ps - ss) + sm,
             "T": 1.02 * (pm + ps - ss) - sm}[which]
        return b - r

    def root(a, b, which):
        fa = excess(a, which)
        for _ in range(60):
            c = (a + b) / 2
            fc = excess(c, which)
            if (fc > 0) == (fa > 0):
                a, fa = c, fc
            else:
                b = c
        return (a + b) / 2

    out = {}
    for which, (n1, n2) in (("P", ("P1", "P4")), ("U", ("U1", "U4")), ("T", ("U2", "U3"))):
        if excess(tm, which) < 0:
            out[n1] = root(tm - 0.3, tm, which)
            out[n2] = root(tm + 0.3, tm, which)
    return dict(sorted(out.items(), key=lambda kv: kv[1]))
