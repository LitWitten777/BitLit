"""
Torah sites (rule R5) and language adjunctions (rule R6).

The reference for the Torah and language checks of migration
``014_hebrew_primacy.sql`` (``torah_section_problems``,
``torah_site_problems``, ``language_adjunction_problems``) and for the passage
presheaf built by ``build_torah_presheaf``.

Torah sections are sections of a sheaf, never a flat corpus: a ``torah_site``
names a finite site of migration 012 whose points are verse references and a
presheaf on it.  The passage presheaf has, over an open set ``U``, the single
section ``passage_label({v: text(v) | v ∈ U})`` when every verse of ``U`` has a
recorded text, and none otherwise; restrictions forget verses.  It is a sheaf
(``Formal/Gematria.lean``: ``textSheaf_locality_and_gluing``,
``textSheaf_subsingleton``, ``textSheaf_nonempty_iff``).

A verse reference is ``"<book> <chapter>:<verse>"`` with a book of the Torah
(English or Hebrew name), a chapter between 1 and the book's number of
chapters, and a verse number between 1 and 999.
"""

from __future__ import annotations

import json
import re
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from qbx.hebrew.text import Problem, text_problems

#: Books of the Torah: English name, Hebrew name, number of chapters.
BOOKS: Tuple[Tuple[str, str, int], ...] = (
    ("Genesis", "בראשית", 50),
    ("Exodus", "שמות", 40),
    ("Leviticus", "ויקרא", 27),
    ("Numbers", "במדבר", 36),
    ("Deuteronomy", "דברים", 34),
)
CHAPTERS: Dict[str, int] = {}
for _en, _he, _n in BOOKS:
    CHAPTERS[_en] = _n
    CHAPTERS[_he] = _n

_VERSE_REF = re.compile(r"([^:]+) ([1-9][0-9]{0,2}):([1-9][0-9]{0,2})", re.DOTALL)

LANGUAGE_STATUSES = ("provisional", "lean_verified")


def parse_verse_ref(ref: Any) -> Optional[Tuple[str, int, int]]:
    """``(book, chapter, verse)``, or ``None`` when ``ref`` is not well formed."""
    if not isinstance(ref, str):
        return None
    m = _VERSE_REF.fullmatch(ref)
    if not m or m.group(1) not in CHAPTERS or int(m.group(2)) > CHAPTERS[m.group(1)]:
        return None
    return m.group(1), int(m.group(2)), int(m.group(3))


def verse_ref_problems(ref: Any) -> List[Problem]:
    """``verse_ref_format`` {error ∈ syntax, book, chapter}."""
    m = _VERSE_REF.fullmatch(ref) if isinstance(ref, str) else None
    if not m:
        return [("verse_ref_format", {"error": "syntax"})]
    if m.group(1) not in CHAPTERS:
        return [("verse_ref_format", {"error": "book"})]
    if int(m.group(2)) > CHAPTERS[m.group(1)]:
        return [("verse_ref_format", {"error": "chapter"})]
    return []


def section_problems(ref: Any, text: Optional[str],
                     points: Optional[Iterable[str]]) -> List[Problem]:
    """``torah_section_problems``: ``verse_ref_format``; ``verse_not_point`` {}
    when the Torah site has a site (``points`` = the points of its base, else
    ``None``) and the reference is not one of them; ``section_text_typing``."""
    out = verse_ref_problems(ref)
    if points is not None and ref not in set(points):
        out.append(("verse_not_point", {}))
    out += text_problems(text, "verse")
    return out


def passage_label(texts: Mapping[str, str]) -> str:
    """The label of the passage section: compact JSON, keys in code point order."""
    return json.dumps(dict(sorted(texts.items())), ensure_ascii=False, separators=(",", ":"))


def passage_sections(opens: Mapping[str, Sequence[str]],
                     texts: Mapping[str, str]) -> Dict[str, List[str]]:
    """The passage presheaf's sections: open name → [label] or []."""
    out: Dict[str, List[str]] = {}
    for name, pts in opens.items():
        if all(p in texts for p in pts):
            out[name] = [passage_label({p: texts[p] for p in pts})]
        else:
            out[name] = []
    return out


def site_problems(site_id: Any, presheaf_id: Any, presheaf_site: Any, batch: bool = False,
                  is_sheaf: Optional[bool] = None,
                  singleton_sections: Optional[Sequence[Tuple[str, str, List[str]]]] = None
                  ) -> List[Problem]:
    """``torah_site_problems``.

    ``torah_no_site`` {} and ``torah_presheaf_typing`` {presheaf} (the
    presheaf is on another site).  The batch check (``batch``) adds
    ``torah_no_presheaf`` {} (a site under construction has none yet) and, for
    a well-typed presheaf, ``torah_not_sheaf`` {presheaf} when ``is_sheaf`` is
    false (``check_sheaf_condition``) and ``torah_section_mismatch`` {verse}
    for each ``(verse, text, sections over the open {verse})`` in
    ``singleton_sections`` (verses in code point order, only those whose
    singleton is an open) where the sections are not exactly
    ``[passage_label({verse: text})]``.
    """
    out: List[Problem] = []
    if site_id is None:
        out.append(("torah_no_site", {}))
    if presheaf_id is None:
        if batch:
            out.append(("torah_no_presheaf", {}))
    elif presheaf_site != site_id or site_id is None:
        out.append(("torah_presheaf_typing", {"presheaf": str(presheaf_id)}))
    elif batch:
        if not is_sheaf:
            out.append(("torah_not_sheaf", {"presheaf": str(presheaf_id)}))
        for verse, text, secs in singleton_sections or []:
            if text is None or sorted(secs) != [passage_label({verse: text})]:
                out.append(("torah_section_mismatch", {"verse": verse}))
    return out


def _blank(s: Optional[str]) -> bool:
    return s is None or s.strip(" ") == ""


def language_adjunction_problems(left: Optional[str], right: Optional[str], functor_id: Any,
                                 adjunction: Optional[Tuple[Any, Any]], status: Any,
                                 artifact_type: Optional[str], has_artifact: bool
                                 ) -> List[Problem]:
    """``language_adjunction_problems``.

    ``language_typing`` {error ∈ left, right, same}; ``adjunction_mismatch`` {}
    when the adjunction's left and right functors (``adjunction``) do not
    include ``functor_id``; ``status_value`` {status} unless the status is
    ``provisional`` or ``lean_verified``; ``unverified_claim`` {error:
    no_artifact} or {error: artifact_type, found} when the status claims a
    Lean proof (rule R6) without a proof artifact of type ``lean4``.
    """
    out: List[Problem] = []
    if _blank(left):
        out.append(("language_typing", {"error": "left"}))
    if _blank(right):
        out.append(("language_typing", {"error": "right"}))
    if not _blank(left) and left == right:
        out.append(("language_typing", {"error": "same"}))
    if adjunction is not None and functor_id not in adjunction:
        out.append(("adjunction_mismatch", {}))
    if status not in LANGUAGE_STATUSES:
        out.append(("status_value", {"status": status}))
    if status == "lean_verified":
        if not has_artifact:
            out.append(("unverified_claim", {"error": "no_artifact"}))
        elif artifact_type != "lean4":
            out.append(("unverified_claim", {"error": "artifact_type", "found": artifact_type}))
    return out
