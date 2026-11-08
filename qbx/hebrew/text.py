"""
Hebrew text checks: the letter table, words, roots and verse texts.

The reference for the text checks of migration ``014_hebrew_primacy.sql``:
every ``*_problems`` function returns the same ``(reason, details)`` pairs as
the database function of the same name (``hebrew_letter_table_problems``,
``hebrew_text_problems``, ``hebrew_root_problems``, ``hebrew_word_problems``).

Conventions (skill ``hebrew_primacy_rules.md``):

* The 27 letters are the 22 letters ``א … ת`` and the five final forms
  ``ך ם ן ף ץ``; final forms are distinct letters (R7).  Their values are the
  seeded table :data:`qbx.hebrew.gematria.GEMATRIA` (R3).
* A word is NFC text made of letters and the Hebrew combining marks (points
  and cantillation, general category Mn in U+0591–U+05C7).  Marks carry no
  value and must follow a letter.
* A verse text may also contain the space, maqaf ``־``, paseq ``׀``,
  sof pasuq ``׃``, nun hafukha ``׆``, geresh ``׳`` and gershayim ``״``.
* Offsets count code points from 0; a code point is written ``U+XXXX``.
"""

from __future__ import annotations

import hashlib
import unicodedata
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from qbx.hebrew.gematria import GEMATRIA, gematria_value

Problem = Tuple[str, Dict[str, Any]]

#: The seeded table in seed order: (letter, value, ordinal, is_final).
LETTER_TABLE: Tuple[Tuple[str, int, int, bool], ...] = tuple(
    (letter, value, i + 1, i >= 22) for i, (letter, value) in enumerate(GEMATRIA.items())
)
LETTERS = frozenset(GEMATRIA)

#: Hebrew combining marks (Mn) in U+0591–U+05C7.
MARKS = frozenset(
    [chr(c) for c in range(0x0591, 0x05BE)] + ["\u05BF", "\u05C1", "\u05C2", "\u05C4", "\u05C5", "\u05C7"]
)

#: Punctuation allowed in a verse text besides letters and marks.
VERSE_PUNCTUATION = frozenset([" ", "\u05BE", "\u05C0", "\u05C3", "\u05C6", "\u05F3", "\u05F4"])


def codepoint(ch: str) -> str:
    return "U+%04X" % ord(ch)


def letter_table_problems(rows: Iterable[Tuple[str, Any, Any, Any]]) -> List[Problem]:
    """``hebrew_letter_table_problems``: compare the rows (letter, value,
    ordinal, is_final) with the seeded table.

    In seed order: ``letter_missing`` {letter}, or one ``letter_value``
    {letter, field, expected, found} per differing field (gematria_value,
    ordinal, is_final); then ``letter_unknown`` {letter} for every other row,
    in code point order.
    """
    found: Dict[str, Tuple[Any, Any, Any]] = {r[0]: (r[1], r[2], r[3]) for r in rows}
    out: List[Problem] = []
    for letter, value, ordinal, is_final in LETTER_TABLE:
        if letter not in found:
            out.append(("letter_missing", {"letter": letter}))
            continue
        fv, fo, ff = found[letter]
        for field, exp, got in (("gematria_value", value, fv), ("ordinal", ordinal, fo),
                                ("is_final", is_final, ff)):
            if got != exp:
                out.append(("letter_value", {"letter": letter, "field": field,
                                             "expected": exp, "found": got}))
    for letter in sorted(set(found) - LETTERS):
        out.append(("letter_unknown", {"letter": letter}))
    return out


def text_problems(text: Optional[str], kind: str = "word") -> List[Problem]:
    """``hebrew_text_problems``: problems of a word (``kind='word'``, reason
    ``word_typing``) or a verse text (``kind='verse'``, reason
    ``section_text_typing``).

    ``empty`` (NULL or ''), else ``non_nfc``, else one ``character`` {offset,
    codepoint} per disallowed code point and one ``leading_mark`` {offset} per
    mark that does not follow a letter directly or through other marks, in
    offset order; finally ``no_letter`` when there is no letter.
    """
    reason = "word_typing" if kind == "word" else "section_text_typing"
    if not text:
        return [(reason, {"error": "empty"})]
    if unicodedata.normalize("NFC", text) != text:
        return [(reason, {"error": "non_nfc"})]
    out: List[Problem] = []
    attached = False      # the previous code point is a letter or an attached mark
    letters = 0
    for i, ch in enumerate(text):
        if ch in LETTERS:
            letters += 1
            attached = True
        elif ch in MARKS:
            if not attached:
                out.append((reason, {"error": "leading_mark", "offset": i}))
        elif kind == "verse" and ch in VERSE_PUNCTUATION:
            attached = False
        else:
            out.append((reason, {"error": "character", "offset": i, "codepoint": codepoint(ch)}))
            attached = False
    if letters == 0:
        out.append((reason, {"error": "no_letter"}))
    return out


def root_problems(root: Optional[str]) -> List[Problem]:
    """``hebrew_root_problems``: a root (when given) is a non-empty string of
    letters: ``root_typing`` {error: empty} or one {error: character, offset,
    codepoint} per other code point."""
    if root is None:
        return []
    if root == "":
        return [("root_typing", {"error": "empty"})]
    return [("root_typing", {"error": "character", "offset": i, "codepoint": codepoint(ch)})
            for i, ch in enumerate(root) if ch not in LETTERS]


def expected_embedding(text: str) -> List[float]:
    """The embedding a word must carry (rule R4): ``gematria_vector(text, 256)``."""
    total = gematria_value(text)
    h = hashlib.sha256(str(total).encode("utf-8")).digest()
    return [(h[i % 32] - 128) / 128.0 for i in range(256)]


def word_row_problems(text: Optional[str], root: Optional[str], total: Any,
                      embedding: Optional[Sequence[float]]) -> List[Problem]:
    """``hebrew_word_problems``: the problems of a ``hebrew_word`` row.

    ``word_typing`` and ``root_typing`` as above; ``gematria_mismatch``
    {recorded, computed} when the stored total is not the value of the text;
    ``embedding_mismatch`` {index} — the first component that differs from
    :func:`expected_embedding` — when an embedding is stored.
    """
    out = text_problems(text, "word") + root_problems(root)
    computed = gematria_value(text or "")
    if total != computed:
        out.append(("gematria_mismatch", {"recorded": total, "computed": computed}))
    if embedding is not None:
        exp = expected_embedding(text or "")
        for i, (a, b) in enumerate(zip(embedding, exp)):
            if float(a) != b:
                out.append(("embedding_mismatch", {"index": i}))
                break
    return out
