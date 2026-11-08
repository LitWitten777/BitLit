"""Torah counts from the Westminster Leningrad Codex (Open Scriptures Hebrew Bible XML).

Usage: python3 QBX/scripts/torah_wlc_stats.py DIR
where DIR holds Gen.xml Exod.xml Lev.xml Num.xml Deut.xml from
https://github.com/openscriptures/morphhb/tree/master/wlc (text public domain; OSHB markup
CC BY 4.0, not redistributed here).  Writes QBX/data/bible/torah_wlc_stats.json and
QBX/data/bible/exodus_14_19-21_wlc.tsv.

Rules: notes (qere readings, accent alternatives) are dropped, so the written text (ketiv) is
counted; a word is a <w> element (maqqef-joined words count separately); a letter is a code
point U+05D0..U+05EA.
"""

import json
import os
import re
import sys
from collections import Counter

BOOKS = ("Gen", "Exod", "Lev", "Num", "Deut")
OUT = os.path.join(os.path.dirname(__file__), "..", "data", "bible")


def is_letter(c):
    return "\u05d0" <= c <= "\u05ea"


def parse(path):
    s = open(path, encoding="utf-8").read()
    s = re.sub(r"<note\b.*?</note>", "", s, flags=re.S)
    verses = {}
    for m in re.finditer(r'<verse osisID="([^"]+)">(.*?)</verse>', s, re.S):
        verses[m.group(1)] = [w.replace("/", "") for w in re.findall(r"<w\b[^>]*>(.*?)</w>", m.group(2), re.S)]
    return verses


def consonants(words):
    return "".join(c for w in words for c in w if is_letter(c))


def main(src):
    stats, allv = {"books": {}}, {}
    letters = Counter()
    for b in BOOKS:
        V = parse(os.path.join(src, b + ".xml"))
        allv.update(V)
        cs = "".join(consonants(w) for w in V.values())
        letters.update(cs)
        stats["books"][b] = {
            "chapters": len(set(k.rsplit(".", 1)[0] for k in V)),
            "verses": len(V),
            "words": sum(len(w) for w in V.values()),
            "letters": len(cs),
        }
    tot = dict((k, sum(v[k] for v in stats["books"].values())) for k in ("chapters", "verses", "words", "letters"))
    stats["total"] = tot
    stats["letter_frequency"] = dict(sorted(letters.items()))
    v = [consonants(allv["Exod.14.%d" % k]) for k in (19, 20, 21)]
    stats["exodus_14_19_21_letters"] = [len(x) for x in v]
    stats["names72"] = [v[0][i] + v[1][71 - i] + v[2][i] for i in range(72)]
    stats["genesis_1_1"] = {"words": len(allv["Gen.1.1"]), "letters": len(consonants(allv["Gen.1.1"]))}
    with open(os.path.join(OUT, "torah_wlc_stats.json"), "w", encoding="utf-8") as fh:
        json.dump(stats, fh, ensure_ascii=False, indent=1)
    with open(os.path.join(OUT, "exodus_14_19-21_wlc.tsv"), "w", encoding="utf-8") as fh:
        fh.write("# Exodus 14:19-21, Westminster Leningrad Codex (WLC 4.20), pointed words and consonants.\n")
        fh.write("# Text: public domain. Extracted from the Open Scriptures Hebrew Bible OSIS file morphhb/wlc/Exod.xml\n")
        fh.write("# (https://github.com/openscriptures/morphhb; OSHB markup/morphology CC BY 4.0, not included here).\n")
        fh.write("ref\tpointed\tconsonants\n")
        for k in (19, 20, 21):
            ws = allv["Exod.14.%d" % k]
            fh.write("Exodus 14:%d\t%s\t%s\n" % (k, " ".join(ws), consonants(ws)))
    print(json.dumps(tot))


if __name__ == "__main__":
    main(sys.argv[1])
