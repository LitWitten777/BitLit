"""The fixed (arithmetic) Hebrew calendar, after Dershowitz & Reingold, *Calendrical Calculations*.

Added 2026-10-23 for calibration: several of the source documents date events by the Hebrew
calendar ("29 Av", "5778 HC"), and the model had no Hebrew calendar to check them against.

Conventions
* Months are numbered from Nisan: 1 Nisan ... 6 Elul, 7 Tishri ... 12 Adar (Adar I in a leap
  year), 13 Adar II.  The year number changes on 1 Tishri.
* `hebrew_from_civil(y, m, d)` gives the Hebrew date of the *daytime* of the civil (Gregorian
  from 1582-10-15, Julian before) date.  The Hebrew day begins at the preceding sunset, so an
  evening event belongs to the next Hebrew day.
* Rata Die (RD) day 1 = 1 January AD 1 (proleptic Gregorian); JD = RD + 1721424.5 at midnight.
"""
import math

from .timescale import calendar_from_jd, jd_from_calendar

MONTHS = {1: "Nisan", 2: "Iyyar", 3: "Sivan", 4: "Tammuz", 5: "Av", 6: "Elul", 7: "Tishri",
          8: "Marheshvan", 9: "Kislev", 10: "Tevet", 11: "Shevat", 12: "Adar", 13: "Adar II"}
EPOCH_RD = -1373427          # 1 Tishri AM 1 = 7 October 3761 BC (Julian), R.D.


def is_leap(year):
    return (7 * year + 1) % 19 < 7


def last_month(year):
    return 13 if is_leap(year) else 12


def _elapsed_days(year):
    months = (235 * year - 234) // 19
    parts = 12084 + 13753 * months
    days = 29 * months + parts // 25920
    return days + 1 if (3 * (days + 1)) % 7 < 3 else days


def _year_length_correction(year):
    ny0, ny1, ny2 = _elapsed_days(year - 1), _elapsed_days(year), _elapsed_days(year + 1)
    if ny2 - ny1 == 356:
        return 2
    if ny1 - ny0 == 382:
        return 1
    return 0


def new_year_rd(year):
    return EPOCH_RD + _elapsed_days(year) + _year_length_correction(year)


def days_in_year(year):
    return new_year_rd(year + 1) - new_year_rd(year)


def days_in_month(month, year):
    n = days_in_year(year)
    if month in (2, 4, 6, 10, 13):
        return 29
    if month == 12 and not is_leap(year):
        return 29
    if month == 8 and n % 10 != 5:      # long Marheshvan only in 355/385-day years
        return 29
    if month == 9 and n % 10 == 3:      # short Kislev in 353/383-day years
        return 29
    return 30


def rd_from_hebrew(year, month, day):
    rd = new_year_rd(year) + day - 1
    if month < 7:
        for m in range(7, last_month(year) + 1):
            rd += days_in_month(m, year)
        for m in range(1, month):
            rd += days_in_month(m, year)
    else:
        for m in range(7, month):
            rd += days_in_month(m, year)
    return rd


def hebrew_from_rd(rd):
    approx = int((rd - EPOCH_RD) // (35975351 / 98496)) + 1
    year = approx - 1
    while new_year_rd(year + 1) <= rd:
        year += 1
    month = 7 if rd < rd_from_hebrew(year, 1, 1) else 1
    while rd > rd_from_hebrew(year, month, days_in_month(month, year)):
        month += 1
    return year, month, rd - rd_from_hebrew(year, month, 1) + 1


def rd_from_civil(y, m, d):
    return math.floor(jd_from_calendar(y, m, d, 12.0) - 1721424.5)


def civil_from_rd(rd):
    y, m, d, _ = calendar_from_jd(rd + 1721425.0)
    return y, m, d


def hebrew_from_civil(y, m, d):
    return hebrew_from_rd(rd_from_civil(y, m, d))


def civil_from_hebrew(year, month, day):
    return civil_from_rd(rd_from_hebrew(year, month, day))


def label(hdate):
    y, m, d = hdate
    name = MONTHS[m]
    if m == 12 and is_leap(y):
        name = "Adar I"
    return f"{d} {name} {y}"


def weekday(rd):
    """0 = Sunday ... 6 = Saturday."""
    return rd % 7
