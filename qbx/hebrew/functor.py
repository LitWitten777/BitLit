"""
Gematria functors and their naturality obligations (rules R1–R3).

A gematria functor (table ``gematria_functor``) maps the category of Hebrew
words (one object; morphisms are words, composition is concatenation) to the
category of numbers (one object; morphisms are naturals, composition is
addition).  It is given by ``mapping_rules``:

* ``{}`` — the seeded table (``hebrew_letter``, :data:`GEMATRIA`);
* otherwise a JSON object with exactly one key per letter (all 27, final forms
  included) and a non-negative integer value (at most 2³¹ − 1) for each.

A word's value is the sum of its letters' values; marks and other characters
count 0.  By ``Formal/Gematria.lean`` (``additive_eq_wordValue``) an additive
map on words is determined by the 27 letter values, so checking the rules is
checking the functor; the naturality square ``gem(u ++ w) = gem(u) + gem(w)``
holds for every valid scheme (``wordValue_append``).

A naturality obligation (table ``gematria_obligation``) records values
claimed for ``u``, ``w`` and ``u ++ w`` (e.g. by another implementation).
:func:`obligation_problems` is the reference for
``gematria_obligation_problems``; :func:`functor_problems` for
``gematria_functor_problems``.
"""

from __future__ import annotations

import math
from typing import Any, Dict, List, Optional

from qbx.hebrew.gematria import GEMATRIA
from qbx.hebrew.text import LETTER_TABLE, LETTERS, Problem, text_problems

INT_MAX = 2 ** 31 - 1


def _rule_value_ok(v: Any) -> bool:
    if isinstance(v, bool) or not isinstance(v, (int, float)):
        return False
    if isinstance(v, float) and (not math.isfinite(v) or not v.is_integer()):
        return False
    return 0 <= v <= INT_MAX


def rules_problems(rules: Any) -> List[Problem]:
    """``functor_rules`` problems: {error: not_object}; else, for keys in code
    point order, {error: unknown_letter, key} or {error: value, key}; then
    {error: missing, letter} for each absent letter in seed order.  ``{}`` has
    none (it means the seeded table)."""
    if not isinstance(rules, dict):
        return [("functor_rules", {"error": "not_object"})]
    if not rules:
        return []
    out: List[Problem] = []
    for k in sorted(rules):
        if k not in LETTERS:
            out.append(("functor_rules", {"error": "unknown_letter", "key": k}))
        elif not _rule_value_ok(rules[k]):
            out.append(("functor_rules", {"error": "value", "key": k}))
    for letter, *_ in LETTER_TABLE:
        if letter not in rules:
            out.append(("functor_rules", {"error": "missing", "letter": letter}))
    return out


def letter_values(rules: Any) -> Optional[Dict[str, int]]:
    """The scheme's letter values, or ``None`` when the rules are invalid."""
    if rules_problems(rules):
        return None
    if not rules:
        return dict(GEMATRIA)
    return {k: int(v) for k, v in rules.items()}


def functor_value(rules: Any, text: Optional[str]) -> Optional[int]:
    """``gematria_functor_value``: the value of ``text`` under the scheme."""
    table = letter_values(rules)
    if table is None or text is None:
        return None
    return sum(table.get(ch, 0) for ch in text)


def functor_problems(base: Any, target: Any, rules: Any,
                     obligations: Optional[int] = None) -> List[Problem]:
    """``gematria_functor_problems``: ``functor_typing`` {error ∈ base_category,
    target_category, same_category}, the ``functor_rules`` problems, and — when
    ``obligations`` (the number of recorded obligations) is given, as in the
    batch check — ``naturality_missing`` when it is 0 (rule R2)."""
    out: List[Problem] = []
    if base is None:
        out.append(("functor_typing", {"error": "base_category"}))
    if target is None:
        out.append(("functor_typing", {"error": "target_category"}))
    if base is not None and base == target:
        out.append(("functor_typing", {"error": "same_category"}))
    out += rules_problems(rules)
    if obligations is not None and obligations == 0:
        out.append(("naturality_missing", {}))
    return out


def obligation_problems(rules: Any, left: Optional[str], right: Optional[str],
                        left_value: int, right_value: int, concat_value: int) -> List[Problem]:
    """``gematria_obligation_problems``.

    ``obligation_typing`` {error: left | right} when that side is not a word,
    {error: rules} when the functor's rules are invalid; otherwise one
    ``naturality_value`` {which, recorded, computed} per recorded value that is
    not the scheme's value (which ∈ left, right, concat); and
    ``naturality_square`` {left, right, concat} when the recorded values do not
    add up.  By ``obligation_value_mismatch_of_square`` a square failure always
    comes with a value failure.
    """
    out: List[Problem] = []
    if text_problems(left, "word"):
        out.append(("obligation_typing", {"error": "left"}))
    if text_problems(right, "word"):
        out.append(("obligation_typing", {"error": "right"}))
    table = letter_values(rules)
    if table is None:
        out.append(("obligation_typing", {"error": "rules"}))
    else:
        concat = (left or "") + (right or "")
        for which, recorded, text in (("left", left_value, left or ""),
                                      ("right", right_value, right or ""),
                                      ("concat", concat_value, concat)):
            computed = sum(table.get(ch, 0) for ch in text)
            if recorded != computed:
                out.append(("naturality_value", {"which": which, "recorded": recorded,
                                                 "computed": computed}))
    if left_value + right_value != concat_value:
        out.append(("naturality_square", {"left": left_value, "right": right_value,
                                          "concat": concat_value}))
    return out
