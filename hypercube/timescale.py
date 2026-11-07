"""Calendars, Julian days, Delta T and sidereal time.

Conventions
* Years are astronomical: 1 BC = year 0, 763 BC = year -762.
* `calendar="auto"` uses the Julian calendar before 1582-10-15 and the Gregorian one from then on
  (the usual historical convention, and the one of NASA's eclipse catalogues).
* Times given by the user are UT; the ephemeris is evaluated in TT = UT + Delta T.
* Delta T: the polynomials of Espenak and Meeus (NASA Five Millennium Canon, 2006), which are
  built on Morrison and Stephenson (2004).  Before -500 and after 2150 they reduce to the
  parabola -20 + 32 u^2 s, u = (year - 1820)/100.  Uncertainty grows to hours in the far past;
  it moves eclipse *tracks* in longitude, not eclipse *dates*.
"""
import math
import re

J2000 = 2451545.0


def jd_from_calendar(y, m, d, hour=0.0, calendar="auto"):
    """Julian day (UT or TT, whichever the hour is in) of a calendar date."""
    if calendar == "auto":
        calendar = "gregorian" if (y, m, d) >= (1582, 10, 15) else "julian"
    yy, mm = (y - 1, m + 12) if m <= 2 else (y, m)
    b = 0
    if calendar == "gregorian":
        a = math.floor(yy / 100)
        b = 2 - a + math.floor(a / 4)
    return (math.floor(365.25 * (yy + 4716)) + math.floor(30.6001 * (mm + 1)) + d + b - 1524.5
            + hour / 24.0)


def calendar_from_jd(jd, calendar="auto"):
    """(year, month, day, hour) of a Julian day (Meeus, ch. 7)."""
    z = math.floor(jd + 0.5)
    f = jd + 0.5 - z
    if calendar == "auto":
        calendar = "gregorian" if z >= 2299161 else "julian"
    if calendar == "gregorian":
        alpha = math.floor((z - 1867216.25) / 36524.25)
        a = z + 1 + alpha - math.floor(alpha / 4)
    else:
        a = z
    b = a + 1524
    c = math.floor((b - 122.1) / 365.25)
    d = math.floor(365.25 * c)
    e = math.floor((b - d) / 30.6001)
    day = b - d - math.floor(30.6001 * e)
    month = e - 1 if e < 14 else e - 13
    year = c - 4716 if month > 2 else c - 4715
    return year, month, day, f * 24.0


def format_jd(jd, calendar="auto"):
    y, m, d, h = calendar_from_jd(jd, calendar)
    hh = int(h)
    mi = int(round((h - hh) * 60))
    if mi == 60:
        hh, mi = hh + 1, 0
    era = f"{y:+05d}" if y <= 0 else f"{y:04d}"
    return f"{era}-{m:02d}-{d:02d} {hh:02d}:{mi:02d}"


_ISO = re.compile(r"^\s*([+-]?\d+)-(\d{1,2})-(\d{1,2})(?:[T ](\d{1,2})(?::(\d{2}))?(?::(\d{2}(?:\.\d*)?))?)?\s*$")


def parse_time(text, calendar="auto"):
    """Parse 'YYYY-MM-DD[THH[:MM[:SS]]]' (UT, astronomical year) to a UT Julian day.  A bare
    float is taken as a Julian day.  'BC' suffix: '763-06-15 BC' means year -762."""
    text = text.strip()
    try:
        return float(text)
    except ValueError:
        pass
    bc = text.upper().endswith("BC")
    if bc:
        text = text[:-2].strip()
    mt = _ISO.match(text)
    if not mt:
        raise ValueError(f"cannot parse time {text!r}")
    y, mo, d = int(mt.group(1)), int(mt.group(2)), int(mt.group(3))
    if bc:
        y = 1 - y
    h = int(mt.group(4) or 0) + int(mt.group(5) or 0) / 60 + float(mt.group(6) or 0) / 3600
    return jd_from_calendar(y, mo, d, h, calendar)


def decimal_year(jd):
    return 2000.0 + (jd - J2000) / 365.25


def delta_t_seconds(year):
    """Delta T = TT - UT in seconds for a (decimal) year (Espenak & Meeus 2006)."""
    y = year
    if y < -500 or y >= 2150:
        u = (y - 1820) / 100
        return -20 + 32 * u * u
    if y < 500:
        u = y / 100
        return (10583.6 - 1014.41 * u + 33.78311 * u ** 2 - 5.952053 * u ** 3
                - 0.1798452 * u ** 4 + 0.022174192 * u ** 5 + 0.0090316521 * u ** 6)
    if y < 1600:
        u = (y - 1000) / 100
        return (1574.2 - 556.01 * u + 71.23472 * u ** 2 + 0.319781 * u ** 3
                - 0.8503463 * u ** 4 - 0.005050998 * u ** 5 + 0.0083572073 * u ** 6)
    if y < 1700:
        t = y - 1600
        return 120 - 0.9808 * t - 0.01532 * t ** 2 + t ** 3 / 7129
    if y < 1800:
        t = y - 1700
        return 8.83 + 0.1603 * t - 0.0059285 * t ** 2 + 0.00013336 * t ** 3 - t ** 4 / 1174000
    if y < 1860:
        t = y - 1800
        return (13.72 - 0.332447 * t + 0.0068612 * t ** 2 + 0.0041116 * t ** 3 - 0.00037436 * t ** 4
                + 0.0000121272 * t ** 5 - 0.0000001699 * t ** 6 + 0.000000000875 * t ** 7)
    if y < 1900:
        t = y - 1860
        return (7.62 + 0.5737 * t - 0.251754 * t ** 2 + 0.01680668 * t ** 3
                - 0.0004473624 * t ** 4 + t ** 5 / 233174)
    if y < 1920:
        t = y - 1900
        return -2.79 + 1.494119 * t - 0.0598939 * t ** 2 + 0.0061966 * t ** 3 - 0.000197 * t ** 4
    if y < 1941:
        t = y - 1920
        return 21.20 + 0.84493 * t - 0.076100 * t ** 2 + 0.0020936 * t ** 3
    if y < 1961:
        t = y - 1950
        return 29.07 + 0.407 * t - t ** 2 / 233 + t ** 3 / 2547
    if y < 1986:
        t = y - 1975
        return 45.45 + 1.067 * t - t ** 2 / 260 - t ** 3 / 718
    if y < 2005:
        t = y - 2000
        return (63.86 + 0.3345 * t - 0.060374 * t ** 2 + 0.0017275 * t ** 3
                + 0.000651814 * t ** 4 + 0.00002373599 * t ** 5)
    if y < 2050:
        t = y - 2000
        return 62.92 + 0.32217 * t + 0.005589 * t ** 2
    u = (y - 1820) / 100
    return -20 + 32 * u * u - 0.5628 * (2150 - y)


def ut_to_tt(jd_ut):
    return jd_ut + delta_t_seconds(decimal_year(jd_ut)) / 86400.0


def tt_to_ut(jd_tt):
    jd = jd_tt - delta_t_seconds(decimal_year(jd_tt)) / 86400.0
    return jd_tt - delta_t_seconds(decimal_year(jd)) / 86400.0


def gmst_deg(jd_ut):
    """Greenwich mean sidereal time in degrees (IAU 1982, Meeus 12.4)."""
    t = (jd_ut - J2000) / 36525
    th = (280.46061837 + 360.98564736629 * (jd_ut - J2000) + 0.000387933 * t * t
          - t ** 3 / 38710000)
    return th % 360
