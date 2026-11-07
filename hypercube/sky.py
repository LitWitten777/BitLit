"""Positions of the Sun, Moon and planets from the committed Swiss Ephemeris files.

Source: `sources/ephemeris.tar.lzma` -> `sepl*.se1` / `semo*.se1` (JPL DE441 compressed by
Astrodienst), read by `scripts/se1_reader.py` (a pure-Python reimplementation of `sweph.c`).
Coverage JD 186997.5 - 2597651 (about 4200 BC - AD 2400).

What is computed
* geocentric positions, ecliptic and equator of J2000, with light-time for the Sun and planets
  (the Earth is the Earth-Moon barycentre minus the Moon / (1 + M_earth/M_moon));
* apparent-Sun aberration (-20.5" / R) for eclipse work;
* precession to the mean equator/ecliptic of date (IAU 1976);
* topocentric altitude/azimuth for an observer (spherical Earth, no refraction).
Nutation is not applied (at most 17" in longitude).
"""
import math
import os
import sys

from . import store
from .timescale import J2000, gmst_deg, ut_to_tt

sys.path.insert(0, store.SCRIPTS)
from se1_reader import SE1, to_ecliptic  # noqa: E402

D2R = math.pi / 180
C_AU_PER_DAY = 173.1446326846693
EARTH_RADIUS_AU = 6378.137 / 149597870.7
SUN_RADIUS_AU = 696000.0 / 149597870.7
MOON_RADIUS_AU = 1737.4 / 149597870.7
EPS2000 = 23.4392911

BODIES = ["Sun", "Moon", "Mercury", "Venus", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune", "Pluto"]
CLASSICAL = BODIES[:7]
_IDX = {"Mercury": 2, "Venus": 3, "Mars": 4, "Jupiter": 5, "Saturn": 6, "Uranus": 7, "Neptune": 8,
        "Pluto": 9}


class OutOfRange(ValueError):
    pass


class Ephemeris:
    """Geocentric positions from the Swiss Ephemeris files."""

    def __init__(self, folder=None):
        folder = folder or store.ephe_dir()
        self.planet_files, self.moon_files = [], []
        for f in sorted(os.listdir(folder)):
            if f.endswith(".se1"):
                (self.planet_files if f.startswith("sepl") else self.moon_files).append(
                    SE1(os.path.join(folder, f)))
        if not self.planet_files or not self.moon_files:
            raise FileNotFoundError(f"no .se1 files in {folder}")
        self.start = max(min(s.tfstart for s in self.planet_files), min(s.tfstart for s in self.moon_files))
        self.end = min(max(s.tfend for s in self.planet_files), max(s.tfend for s in self.moon_files))

    @staticmethod
    def _pick(files, tjd):
        for s in files:
            if s.tfstart <= tjd <= s.tfend:
                return s
        raise OutOfRange(f"JD {tjd} outside the ephemeris ({files[0].tfstart}..{files[-1].tfend})")

    # ---------------------------------------------------------------- raw vectors (ecl. J2000)
    def moon_geo(self, tjd):
        return to_ecliptic(self._pick(self.moon_files, tjd).position(1, tjd), False)

    def _bary(self, s, idx, tjd):
        p = s.position(idx, tjd)
        if s.planets[idx].iflg & 1:  # stored heliocentric: add the Sun's barycentric position
            emb, hemb = s.position(0, tjd), s.position(10, tjd)
            p = [a + (b - c) for a, b, c in zip(p, emb, hemb)]
        return p

    def earth_bary(self, tjd):
        s = self._pick(self.planet_files, tjd)
        emb = s.position(0, tjd)
        moon_eq = self._pick(self.moon_files, tjd).position(1, tjd)
        moon = to_ecliptic(moon_eq, False)
        emb_ecl = to_ecliptic(emb, False)
        return [a - b / (1 + s.ratme) for a, b in zip(emb_ecl, moon)]

    def sun_bary(self, tjd):
        s = self._pick(self.planet_files, tjd)
        emb, hemb = s.position(0, tjd), s.position(10, tjd)
        return to_ecliptic([a - b for a, b in zip(emb, hemb)], False)

    def body_bary(self, body, tjd):
        if body == "Sun":
            return self.sun_bary(tjd)
        s = self._pick(self.planet_files, tjd)
        return to_ecliptic(self._bary(s, _IDX[body], tjd), False)

    def geo(self, body, tjd, light_time=True):
        """Geocentric ecliptic-J2000 vector (AU) of `body` at TT `tjd`."""
        if body == "Moon":
            return self.moon_geo(tjd)
        e = self.earth_bary(tjd)
        t = tjd
        for _ in range(2 if light_time else 1):
            p = self.body_bary(body, t)
            v = [a - b for a, b in zip(p, e)]
            t = tjd - _norm(v) / C_AU_PER_DAY
        return v

    def helio(self, body, tjd):
        """Heliocentric ecliptic-J2000 vector (AU); 'Earth' is allowed."""
        sun = self.sun_bary(tjd)
        p = self.earth_bary(tjd) if body == "Earth" else self.body_bary(body, tjd)
        return [a - b for a, b in zip(p, sun)]


# -------------------------------------------------------------------- geometry helpers
def _norm(v):
    return math.sqrt(sum(c * c for c in v))


def lonlat(v):
    r = _norm(v)
    return math.degrees(math.atan2(v[1], v[0])) % 360, math.degrees(math.asin(v[2] / r)), r


def ecl_to_equ_vec(v, eps_deg=EPS2000):
    ce, se = math.cos(eps_deg * D2R), math.sin(eps_deg * D2R)
    x, y, z = v
    return [x, ce * y - se * z, se * y + ce * z]


def equ_to_ecl_vec(v, eps_deg=EPS2000):
    ce, se = math.cos(eps_deg * D2R), math.sin(eps_deg * D2R)
    x, y, z = v
    return [x, ce * y + se * z, -se * y + ce * z]


def radec(v_equ):
    lon, lat, r = lonlat(v_equ)
    return lon / 15.0, lat, r


def mean_obliquity(tjd):
    t = (tjd - J2000) / 36525
    return 23.4392911 - (46.8150 * t + 0.00059 * t * t - 0.001813 * t ** 3) / 3600


def precession_matrix(tjd):
    """IAU 1976 precession, mean equator J2000 -> mean equator of date."""
    t = (tjd - J2000) / 36525
    s = D2R / 3600
    zeta = (2306.2181 * t + 0.30188 * t * t + 0.017998 * t ** 3) * s
    z = (2306.2181 * t + 1.09468 * t * t + 0.018203 * t ** 3) * s
    th = (2004.3109 * t - 0.42665 * t * t - 0.041833 * t ** 3) * s
    cz, sz, cZ, sZ, ct, st = math.cos(zeta), math.sin(zeta), math.cos(z), math.sin(z), math.cos(th), math.sin(th)
    return [[cz * cZ * ct - sz * sZ, -sz * cZ * ct - cz * sZ, -cZ * st],
            [cz * sZ * ct + sz * cZ, -sz * sZ * ct + cz * cZ, -sZ * st],
            [cz * st, -sz * st, ct]]


def matvec(m, v):
    return [sum(m[i][k] * v[k] for k in range(3)) for i in range(3)]


def angsep(v, w):
    """Angle between two vectors, degrees (robust for small angles)."""
    cx = v[1] * w[2] - v[2] * w[1]
    cy = v[2] * w[0] - v[0] * w[2]
    cz = v[0] * w[1] - v[1] * w[0]
    return math.degrees(math.atan2(math.sqrt(cx * cx + cy * cy + cz * cz), sum(a * b for a, b in zip(v, w))))


def observer_equ_date(lat_deg, lon_deg, jd_ut, height_m=0.0):
    """Observer's geocentric vector (AU) in the equator of date.

    `lat_deg` is geodetic (WGS84) latitude, as on maps and GPS.  Calibration fix 2026-10-23: the
    earlier version used a spherical Earth, which puts the observer up to ~21 km (0.19 deg of
    latitude at 45 deg) away from the true position and shifts eclipse-path edges accordingly.
    """
    lst = (gmst_deg(jd_ut) + lon_deg) * D2R
    a = 6378137.0
    f = 1 / 298.257223563
    e2 = f * (2 - f)
    phi = lat_deg * D2R
    n = a / math.sqrt(1 - e2 * math.sin(phi) ** 2)
    rho_cos = (n + height_m) * math.cos(phi) / a
    rho_sin = (n * (1 - e2) + height_m) * math.sin(phi) / a
    return [EARTH_RADIUS_AU * rho_cos * math.cos(lst), EARTH_RADIUS_AU * rho_cos * math.sin(lst),
            EARTH_RADIUS_AU * rho_sin]


def alt_az(v_equ_date_topo, lat_deg, lon_deg, jd_ut):
    """Altitude and azimuth (deg, azimuth from north through east) of a topocentric vector."""
    ra, dec, _ = radec(v_equ_date_topo)
    ha = ((gmst_deg(jd_ut) + lon_deg) - ra * 15) * D2R
    d, p = dec * D2R, lat_deg * D2R
    alt = math.asin(math.sin(p) * math.sin(d) + math.cos(p) * math.cos(d) * math.cos(ha))
    az = math.atan2(-math.sin(ha) * math.cos(d), math.cos(p) * math.sin(d) - math.sin(p) * math.cos(d) * math.cos(ha))
    return math.degrees(alt), math.degrees(az) % 360


def magnitude(eph, body, tjd):
    """Apparent visual magnitude (Astronomical Almanac 1984 / Meeus ch. 41)."""
    if body == "Sun":
        return -26.74
    if body == "Moon":
        sun, moon = eph.geo("Sun", tjd), eph.geo("Moon", tjd)
        i = 180 - angsep(sun, moon)  # phase angle (Sun-Moon-Earth), small-parallax approximation
        return -12.73 + 0.026 * abs(i) + 4e-9 * i ** 4
    g = eph.geo(body, tjd)
    h = eph.helio(body, tjd)
    E = eph.helio("Earth", tjd)
    r, D, R = _norm(h), _norm(g), _norm(E)
    i = math.degrees(math.acos(max(-1, min(1, (r * r + D * D - R * R) / (2 * r * D)))))
    l5 = 5 * math.log10(r * D)
    if body == "Mercury":
        return -0.42 + l5 + 0.0380 * i - 0.000273 * i ** 2 + 0.000002 * i ** 3
    if body == "Venus":
        return -4.40 + l5 + 0.0009 * i + 0.000239 * i ** 2 - 0.00000065 * i ** 3
    if body == "Mars":
        return -1.52 + l5 + 0.016 * i
    if body == "Jupiter":
        return -9.40 + l5 + 0.005 * i
    if body == "Saturn":
        # Astronomical Almanac 1984 (Meeus 41.x, with B and Delta-U from ch. 45), ecliptic of date.
        P = precession_matrix(tjd)
        eps_d = mean_obliquity(tjd)

        def to_date(v):
            return equ_to_ecl_vec(matvec(P, ecl_to_equ_vec(v)), eps_d)
        t = (tjd - J2000) / 36525
        inc = (28.075216 - 0.012998 * t + 0.000004 * t * t) * D2R
        node = (169.508470 + 1.394681 * t + 0.000412 * t * t) * D2R
        pole = [math.sin(inc) * math.sin(node), -math.sin(inc) * math.cos(node), math.cos(inc)]
        to_earth = [-c for c in to_date(g)]
        to_sun = [-c for c in to_date(h)]

        def ring_lon_lat(v):
            n = _norm(v)
            sb = sum(a * b for a, b in zip(v, pole)) / n
            proj = [a - sb * n * b for a, b in zip(v, pole)]
            return proj, sb
        pe, sB = ring_lon_lat(to_earth)
        ps, _ = ring_lon_lat(to_sun)
        dU = angsep(pe, ps)
        return -8.88 + l5 + 0.044 * dU - 2.60 * abs(sB) + 1.25 * sB * sB
    if body == "Uranus":
        return -7.19 + l5
    if body == "Neptune":
        return -6.87 + l5
    return -1.01 + l5  # Pluto


_EPH = None


def default_ephemeris():
    global _EPH
    if _EPH is None:
        _EPH = Ephemeris()
    return _EPH


def body_state(body, jd_ut, eph=None, place=None):
    """Everything the model needs about one body at one UT instant (and optional place)."""
    eph = eph or default_ephemeris()
    tjd = ut_to_tt(jd_ut)
    g = eph.geo(body, tjd)
    lon, lat, dist = lonlat(g)
    equ = ecl_to_equ_vec(g)
    ra, dec, _ = radec(equ)
    P = precession_matrix(tjd)
    equ_d = matvec(P, equ)
    ra_d, dec_d, _ = radec(equ_d)
    eps_d = mean_obliquity(tjd)
    lon_d, lat_d, _ = lonlat(equ_to_ecl_vec(equ_d, eps_d))
    st = {"body": body, "jd_tt": tjd, "lon_j2000": lon, "lat_j2000": lat, "dist_au": dist,
          "ra_j2000_h": ra, "dec_j2000": dec, "ra_date_h": ra_d, "dec_date": dec_d,
          "lon_date": lon_d, "lat_date": lat_d, "mag": magnitude(eph, body, tjd)}
    if place is not None:
        plat, plon = place
        topo = [a - b for a, b in zip(equ_d, observer_equ_date(plat, plon, jd_ut))]
        st["alt"], st["az"] = alt_az(topo, plat, plon, jd_ut)
    return st
