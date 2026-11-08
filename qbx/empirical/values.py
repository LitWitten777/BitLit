"""Value helpers shared by the empirical-grounding checks (migration 016).

*Numbers* are JSON numbers: ``int`` or finite ``float``, never ``bool``.  The
database stores them in ``jsonb`` as exact decimals and computes with
``numeric``; :func:`exact` gives the same exact value here (a float is read
through its shortest ``repr``, which is the text ``json.dumps`` sends).
"""

from __future__ import annotations

import math
import re
from decimal import Decimal
from fractions import Fraction
from typing import Any, List, Optional, Tuple

Problem = Tuple[str, dict]

_BLANK = " \t\n\r\f\v"
SEMVER = re.compile(r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)")


def is_blank(s: Optional[str]) -> bool:
    """``None`` or text of only space, tab, LF, CR, FF, VT (the empty text included)."""
    return s is None or all(ch in _BLANK for ch in s)


def is_name(x: Any) -> bool:
    """A JSON string that is not blank."""
    return isinstance(x, str) and not is_blank(x)


def is_number(x: Any) -> bool:
    if isinstance(x, bool):
        return False
    if isinstance(x, int):
        return True
    return isinstance(x, float) and math.isfinite(x)


def exact(x: Any) -> Fraction:
    """The exact value of a JSON number."""
    if isinstance(x, int):
        return Fraction(x)
    return Fraction(Decimal(repr(x)))


def is_semver(v: Optional[str]) -> bool:
    return v is not None and SEMVER.fullmatch(v) is not None


def is_name_list(x: Any) -> bool:
    """A JSON array of non-blank strings (repeats allowed)."""
    return isinstance(x, list) and all(is_name(s) for s in x)


def repeats(xs: List[str]) -> List[str]:
    """Each element equal to an earlier one, in order."""
    seen, out = set(), []
    for s in xs:
        if s in seen:
            out.append(s)
        seen.add(s)
    return out


def as_json_number(q: Fraction) -> Any:
    """How the database's ``to_jsonb(numeric)`` reads back through ``json``:
    an ``int`` when integral, else the nearest ``float``."""
    return int(q) if q.denominator == 1 else float(q)
