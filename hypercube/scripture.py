"""The text axis: the 66-book canon as a circle of 1,189 chapters, plus verse access.

Text source: `kjv_strongs.json` in `sources/bible.tar.lzma` (KJV, 31,102 verses).  Hebrew and
Greek verse text: OSHB 2.2 and Tischendorf 8 from the same archive (via `scripts/braid_walk.py`).

Placement rules (the ones proved in `Sovereign.Organism.NovaScripture`, integer arithmetic in
milli-degrees, so Python and Lean agree to the unit):
* phase  = (RA * 15 deg + shift) mod 360 deg;
* continuous chapter = floor(phase * 1189 / 360) + 1 (Genesis 1 = 1, Revelation 22 = 1189);
* Isaiah sector = floor(phase * 66 / 360) + 1 (Isaiah chapter k <-> book k);
* tribe = floor(phase / 30 deg), in the census order of Numbers 1.
These are conventions.  Each chapter arc is 1.2 minutes of RA wide, so every sky position is
near some chapter boundary, and the shift is a free parameter.
"""
import json
import os
import sys
from functools import lru_cache

from . import store

BOOKS = ["Genesis", "Exodus", "Leviticus", "Numbers", "Deuteronomy", "Joshua", "Judges", "Ruth",
         "1 Samuel", "2 Samuel", "1 Kings", "2 Kings", "1 Chronicles", "2 Chronicles", "Ezra",
         "Nehemiah", "Esther", "Job", "Psalms", "Proverbs", "Ecclesiastes", "Song of Solomon", "Isaiah",
         "Jeremiah", "Lamentations", "Ezekiel", "Daniel", "Hosea", "Joel", "Amos", "Obadiah", "Jonah",
         "Micah", "Nahum", "Habakkuk", "Zephaniah", "Haggai", "Zechariah", "Malachi", "Matthew", "Mark",
         "Luke", "John", "Acts", "Romans", "1 Corinthians", "2 Corinthians", "Galatians", "Ephesians",
         "Philippians", "Colossians", "1 Thessalonians", "2 Thessalonians", "1 Timothy", "2 Timothy",
         "Titus", "Philemon", "Hebrews", "James", "1 Peter", "2 Peter", "1 John", "2 John", "3 John",
         "Jude", "Revelation"]
TRIBES = ["Reuben", "Simeon", "Gad", "Judah", "Issachar", "Zebulun", "Ephraim", "Manasseh", "Benjamin",
          "Dan", "Asher", "Naphtali"]
CENSUS_NUM1 = [46500, 59300, 45650, 74600, 54400, 57400, 40500, 32200, 35400, 62700, 41500, 53400]


@lru_cache(maxsize=1)
def kjv():
    with open(os.path.join(store.bible_dir(), "kjv_strongs.json"), encoding="utf-8") as f:
        return json.load(f)["verses"]


@lru_cache(maxsize=1)
def chapter_counts():
    counts = [0] * 66
    for v in kjv():
        counts[v["book"] - 1] = max(counts[v["book"] - 1], v["chapter"])
    return counts


@lru_cache(maxsize=1)
def verse_counts():
    out = {}
    for v in kjv():
        key = (v["book"], v["chapter"])
        out[key] = max(out.get(key, 0), v["verse"])
    return out


def offsets():
    o, acc = [], 0
    for c in chapter_counts():
        o.append(acc)
        acc += c
    return o


def continuous_index(book, chapter):
    return offsets()[book - 1] + chapter


def locate(index):
    """(book number, chapter) of a continuous chapter index, wrapping after 1189."""
    total = sum(chapter_counts())
    i = (index - 1) % total + 1
    for b, (off, c) in enumerate(zip(offsets(), chapter_counts()), start=1):
        if i <= off + c:
            return b, i - off
    raise AssertionError


def phase_mdeg(ra_h, shift_deg=0.0):
    return (round(ra_h * 1000) * 15 + round(shift_deg * 1000)) % 360000


def placement(ra_h, shift_deg=0.0):
    ph = phase_mdeg(ra_h, shift_deg)
    idx = ph * 1189 // 360000 + 1
    b, ch = locate(idx)
    isa = ph * 66 // 360000 + 1
    tribe = ph // 30000
    return {"phase_deg": ph / 1000, "chapter_index": idx, "chapter": f"{BOOKS[b - 1]} {ch}",
            "isaiah_sector": isa, "isaiah_book": BOOKS[isa - 1], "tribe": TRIBES[tribe]}


def kjv_text(book, chapter, verse):
    for v in kjv():
        if v["book"] == book and v["chapter"] == chapter and v["verse"] == verse:
            import re
            return re.sub(r"\{[^}]*\}", "", v["text"]).replace("  ", " ").strip()
    return None


def book_number(name):
    low = name.lower().replace(" ", "")
    for i, b in enumerate(BOOKS, start=1):
        if b.lower().replace(" ", "") == low:
            return i
    for i, b in enumerate(BOOKS, start=1):
        if b.lower().replace(" ", "").startswith(low):
            return i
    raise KeyError(name)


def parse_ref(ref):
    """'John 1:1' -> (43, 1, 1)."""
    name, cv = ref.rsplit(" ", 1)
    ch, vs = cv.split(":")
    return book_number(name), int(ch), int(vs)


def original_verse(osis_id):
    """Hebrew (OSHB) or Greek (Tischendorf) text of an OSIS verse id such as 'Gen.1.1'."""
    sys.path.insert(0, store.SCRIPTS)
    import braid_walk as B
    d = store.bible_dir()
    book = osis_id.split(".")[0]
    if os.path.exists(os.path.join(d, "OSHB-v.2.2", book + ".xml")):
        return B.oshb_verse(d, osis_id)
    return B.tischendorf_verse(os.path.join(d, "tischendorfmorph.OSIS.xml"), osis_id)


@lru_cache(maxsize=4)
def corpus(lang):
    """Plain letter corpus for language models: 'en' (KJV), 'he' (OSHB), 'el' (Tischendorf)."""
    import re
    import unicodedata
    if lang == "en":
        return " ".join(re.sub(r"\{[^}]*\}", "", v["text"]) for v in kjv())
    d = store.bible_dir()
    if lang == "he":
        import glob
        import xml.etree.ElementTree as ET
        parts = []
        for p in sorted(glob.glob(os.path.join(d, "OSHB-v.2.2", "*.xml"))):
            if p.endswith("VerseMap.xml"):
                continue
            for w in ET.parse(p).getroot().iter("{http://www.bibletechnologies.net/2003/OSIS/namespace}w"):
                parts.append("".join(w.itertext()))
        text = " ".join(parts)
    else:
        import xml.etree.ElementTree as ET
        root = ET.parse(os.path.join(d, "tischendorfmorph.OSIS.xml")).getroot()
        text = " ".join("".join(w.itertext()) for w in root.iter("{http://www.bibletechnologies.net/2003/OSIS/namespace}w"))
    text = unicodedata.normalize("NFD", text)
    return "".join(c for c in text if not unicodedata.combining(c)).replace("/", "")
