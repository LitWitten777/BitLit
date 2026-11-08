"""
Bible corpora: loading verses and selecting passages.

Two input formats are supported, both read offline:

* **TSV** — one verse per line, ``<reference>\\t<text>``.  Lines that are empty
  or start with ``#`` are ignored.  References may be written either as
  ``"Genesis 1:1"`` or in OSIS form ``"Gen.1.1"``.
* **OSIS XML** — e.g. a book file of the Open Scriptures Hebrew Bible
  (``morphhb/wlc/Gen.xml``).  Each ``<verse osisID=...>`` becomes one verse;
  the text is the written (ketiv) text of its ``<w>`` elements, with the
  morpheme separators ``/`` removed, words separated by spaces, maqqef and
  sof pasuq kept, and notes (qere readings, variants) skipped.

Every verse is normalised to an English reference ``"<Book> <chapter>:<verse>"``
(:func:`normalize_ref`).  :func:`select` picks verses with a passage
specification such as ``"Genesis 1"``, ``"Genesis 1:1"``, ``"Genesis 1:1-5"``,
``"Gen.1.3"`` or ``"Genesis 1:31-2:3"``.
"""

from __future__ import annotations

import os
import re
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

#: (English name, OSIS abbreviation) for the 66 books, in canonical order.
BOOKS: Tuple[Tuple[str, str], ...] = (
    ("Genesis", "Gen"), ("Exodus", "Exod"), ("Leviticus", "Lev"), ("Numbers", "Num"),
    ("Deuteronomy", "Deut"), ("Joshua", "Josh"), ("Judges", "Judg"), ("Ruth", "Ruth"),
    ("1 Samuel", "1Sam"), ("2 Samuel", "2Sam"), ("1 Kings", "1Kgs"), ("2 Kings", "2Kgs"),
    ("1 Chronicles", "1Chr"), ("2 Chronicles", "2Chr"), ("Ezra", "Ezra"),
    ("Nehemiah", "Neh"), ("Esther", "Esth"), ("Job", "Job"), ("Psalms", "Ps"),
    ("Proverbs", "Prov"), ("Ecclesiastes", "Eccl"), ("Song of Songs", "Song"),
    ("Isaiah", "Isa"), ("Jeremiah", "Jer"), ("Lamentations", "Lam"), ("Ezekiel", "Ezek"),
    ("Daniel", "Dan"), ("Hosea", "Hos"), ("Joel", "Joel"), ("Amos", "Amos"),
    ("Obadiah", "Obad"), ("Jonah", "Jonah"), ("Micah", "Mic"), ("Nahum", "Nah"),
    ("Habakkuk", "Hab"), ("Zephaniah", "Zeph"), ("Haggai", "Hag"), ("Zechariah", "Zech"),
    ("Malachi", "Mal"),
    ("Matthew", "Matt"), ("Mark", "Mark"), ("Luke", "Luke"), ("John", "John"),
    ("Acts", "Acts"), ("Romans", "Rom"), ("1 Corinthians", "1Cor"),
    ("2 Corinthians", "2Cor"), ("Galatians", "Gal"), ("Ephesians", "Eph"),
    ("Philippians", "Phil"), ("Colossians", "Col"), ("1 Thessalonians", "1Thess"),
    ("2 Thessalonians", "2Thess"), ("1 Timothy", "1Tim"), ("2 Timothy", "2Tim"),
    ("Titus", "Titus"), ("Philemon", "Phlm"), ("Hebrews", "Heb"), ("James", "Jas"),
    ("1 Peter", "1Pet"), ("2 Peter", "2Pet"), ("1 John", "1John"), ("2 John", "2John"),
    ("3 John", "3John"), ("Jude", "Jude"), ("Revelation", "Rev"),
)

_BOOK_KEYS: Dict[str, str] = {}
for _name, _osis in BOOKS:
    for _k in (_name, _osis, _name.replace(" ", ""), _osis.replace(" ", "")):
        _BOOK_KEYS[_k.lower()] = _name
_BOOK_KEYS.update({"psalm": "Psalms", "song of solomon": "Song of Songs",
                   "canticles": "Song of Songs", "qoheleth": "Ecclesiastes"})
_BOOK_INDEX = {name: i for i, (name, _) in enumerate(BOOKS)}

_SOURCE_DIR = os.path.dirname(os.path.abspath(__file__))
#: The bundled sample corpus: Genesis 1 (Westminster Leningrad Codex).
DEFAULT_CORPUS = os.path.normpath(
    os.path.join(_SOURCE_DIR, "..", "..", "data", "bible", "genesis_1_wlc.tsv"))

_OSIS_NS = "{http://www.bibletechnologies.net/2003/OSIS/namespace}"


def book_name(token: str) -> Optional[str]:
    """English book name for an English name or OSIS abbreviation (case-insensitive)."""
    return _BOOK_KEYS.get(token.strip().lower()) or _BOOK_KEYS.get(
        token.strip().lower().replace(" ", ""))


_REF_ENGLISH = re.compile(r"^\s*(.+?)\s+(\d+):(\d+)\s*$")
_REF_OSIS = re.compile(r"^\s*([1-3]?[A-Za-z]+)\.(\d+)\.(\d+)\s*$")


def parse_ref(ref: str) -> Tuple[str, int, int]:
    """``(book, chapter, verse)`` of ``"Genesis 1:1"`` or ``"Gen.1.1"`` (ValueError if malformed)."""
    m = _REF_OSIS.match(ref) or _REF_ENGLISH.match(ref)
    if not m:
        raise ValueError(f"Malformed verse reference: {ref!r}")
    book = book_name(m.group(1))
    if book is None:
        raise ValueError(f"Unknown book in reference: {ref!r}")
    return book, int(m.group(2)), int(m.group(3))


def normalize_ref(ref: str) -> str:
    """The English form ``"<Book> <chapter>:<verse>"`` of a reference."""
    book, ch, vs = parse_ref(ref)
    return f"{book} {ch}:{vs}"


@dataclass(frozen=True)
class Verse:
    """One verse of a corpus."""

    ref: str      # normalised, e.g. "Genesis 1:1"
    text: str     # as stored in the corpus (points and accents included)

    @property
    def key(self) -> Tuple[int, int, int]:
        book, ch, vs = parse_ref(self.ref)
        return _BOOK_INDEX[book], ch, vs


def load_tsv(path: str) -> List[Verse]:
    """Verses of a ``<reference>\\t<text>`` file."""
    out: List[Verse] = []
    with open(path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            line = line.rstrip("\r\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            if "\t" not in line:
                raise ValueError(f"{path}:{lineno}: expected '<reference><TAB><text>'")
            ref, text = line.split("\t", 1)
            out.append(Verse(normalize_ref(ref), text.strip()))
    return out


def _word_text(w: ET.Element) -> str:
    parts: List[str] = []

    def walk(e: ET.Element) -> None:
        if e.tag == _OSIS_NS + "note":
            return
        if e.text:
            parts.append(e.text)
        for c in e:
            walk(c)
            if c.tail:
                parts.append(c.tail)

    walk(w)
    return "".join(parts).replace("/", "").strip()


def load_osis(path: str) -> List[Verse]:
    """Verses of an OSIS XML file (e.g. an Open Scriptures Hebrew Bible book)."""
    root = ET.parse(path).getroot()
    out: List[Verse] = []
    for verse in root.iter(_OSIS_NS + "verse"):
        osis_id = verse.get("osisID")
        if not osis_id:
            continue
        text = ""
        for child in verse:
            tag = child.tag[len(_OSIS_NS):] if child.tag.startswith(_OSIS_NS) else child.tag
            if tag == "w":
                word = _word_text(child)
                if word:
                    if text and not text.endswith("\u05BE"):
                        text += " "
                    text += word
            elif tag == "seg":
                seg = (child.text or "").strip()
                kind = child.get("type", "")
                if kind in ("x-maqqef", "x-sof-pasuq"):
                    text += seg
                elif kind == "x-paseq":
                    text += " " + seg
                # x-pe / x-samekh (paragraph markers) carry no letters; skip.
        out.append(Verse(normalize_ref(osis_id.split()[0]), text.strip()))
    return out


def load_corpus(path: Optional[str] = None) -> List[Verse]:
    """Load a corpus file (``.xml`` → OSIS, anything else → TSV).  Default: Genesis 1."""
    path = path or DEFAULT_CORPUS
    if path.lower().endswith(".xml"):
        return load_osis(path)
    return load_tsv(path)


def write_tsv(verses: Iterable[Verse], path: str, header: Sequence[str] = ()) -> None:
    """Write verses as a TSV corpus (with optional ``#`` header lines)."""
    with open(path, "w", encoding="utf-8") as fh:
        for h in header:
            fh.write(f"# {h}\n")
        for v in verses:
            fh.write(f"{v.ref}\t{v.text}\n")


# ---------------------------------------------------------------------------
# Passage selection
# ---------------------------------------------------------------------------

_SPEC_CHAPTER = re.compile(r"^\s*(.+?)\s+(\d+)\s*$")
_SPEC_RANGE = re.compile(r"^\s*(.+?)\s+(\d+):(\d+)\s*(?:-\s*(?:(\d+):)?(\d+))?\s*$")


def _parse_spec(spec: str) -> Tuple[str, Tuple[int, int], Tuple[int, int]]:
    m = _REF_OSIS.match(spec)
    if m:
        book = book_name(m.group(1))
        if book is None:
            raise ValueError(f"Unknown book in passage: {spec!r}")
        ch, vs = int(m.group(2)), int(m.group(3))
        return book, (ch, vs), (ch, vs)
    m = _SPEC_RANGE.match(spec)
    if m:
        book = book_name(m.group(1))
        if book is None:
            raise ValueError(f"Unknown book in passage: {spec!r}")
        ch, vs = int(m.group(2)), int(m.group(3))
        if m.group(5) is None:
            return book, (ch, vs), (ch, vs)
        end_ch = int(m.group(4)) if m.group(4) else ch
        return book, (ch, vs), (end_ch, int(m.group(5)))
    m = _SPEC_CHAPTER.match(spec)
    if m:
        book = book_name(m.group(1))
        if book is None:
            raise ValueError(f"Unknown book in passage: {spec!r}")
        ch = int(m.group(2))
        return book, (ch, 1), (ch, 10 ** 6)
    book = book_name(spec)
    if book is not None:
        return book, (1, 1), (10 ** 6, 10 ** 6)
    raise ValueError(f"Malformed passage specification: {spec!r}")


def select(verses: Sequence[Verse], spec: str) -> List[Verse]:
    """The verses of ``spec`` (a book, chapter, verse or verse range), in corpus order.

    Raises ValueError when the specification is malformed or selects nothing.
    """
    book, start, end = _parse_spec(spec)
    out = []
    for v in verses:
        b, ch, vs = parse_ref(v.ref)
        if b == book and start <= (ch, vs) <= end:
            out.append(v)
    if not out:
        raise ValueError(f"No verses in the corpus match {spec!r}")
    return out
