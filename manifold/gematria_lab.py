"""Gematria experiments on the Hebrew Torah (OSHB / WLC text, ketiv), with null models.

Run: python3 -m manifold gematria   (writes artifacts/manifold/gematria_lab.txt)

What is tested (the arithmetic facts are proved in Gematria.lean; the statistics are measured
here and compared with shuffled-text controls):

 1. mod 9: standard, ordinal and katan agree mod 9 for every word (proved; checked on the corpus);
    sofit does not.
 2. collisions: how many distinct values the distinct words take; words per value.
 3. "hits": how often a target number (26, 86, 72, 358, 541, 913, 2701 ...) occurs as the value
    of a word / of a run of consecutive words, in the real text and in letter-shuffled controls
    (same letters, same word lengths).  If the real counts sit inside the control spread, the
    hits are what letter frequencies alone produce.
 4. verse sums: residues mod 9 and mod 7, triangular verse values, compared with controls.
"""
import math
import os
import random
import xml.etree.ElementTree as ET
from collections import Counter

from hypercube import codec, store

OSIS = "{http://www.bibletechnologies.net/2003/OSIS/namespace}"
TORAH = ["Gen", "Exod", "Lev", "Num", "Deut"]
HEB_VALUES = codec.HEB_VALUES


def _book_verses(book):
    path = os.path.join(store.bible_dir(), "OSHB-v.2.2", f"{book}.xml")
    root = ET.parse(path).getroot()
    for v in root.iter(OSIS + "verse"):
        words = ["".join(el.itertext()) for el in v if el.tag == OSIS + "w"]
        yield v.get("osisID"), words


def torah_verses():
    """[(osisID, [word letters as (index, final)])]."""
    out = []
    for b in TORAH:
        for vid, words in _book_verses(b):
            ws = []
            for w in words:
                ls = [(i, fin) for s, i, fin in codec.letters(w) if s == "he"]
                if ls:
                    ws.append(ls)
            out.append((vid, ws))
    return out


def torah_letter_values(limit_words=None):
    vals, n = [], 0
    for _, ws in torah_verses():
        for w in ws:
            vals += [HEB_VALUES[i] for i, _ in w]
            n += 1
            if limit_words and n >= limit_words:
                return vals
    return vals


def value(ls, method="standard"):
    if method == "standard":
        return sum(HEB_VALUES[i] for i, _ in ls)
    if method == "ordinal":
        return sum(i + 1 for i, _ in ls)
    if method == "katan":
        t = 0
        for i, _ in ls:
            v = HEB_VALUES[i]
            while v % 10 == 0:
                v //= 10
            t += v
        return t
    if method == "sofit":
        return sum((500 + 100 * [10, 12, 13, 16, 17].index(i)) if f else HEB_VALUES[i] for i, f in ls)
    raise ValueError(method)


def shuffled(verses, rnd):
    """Same word lengths and verse structure, letters permuted across the whole corpus
    (final-form flags follow the word-final position)."""
    letters = [i for _, ws in verses for w in ws for i, _ in w]
    rnd.shuffle(letters)
    k, out = 0, []
    for vid, ws in verses:
        nws = []
        for w in ws:
            nl = letters[k:k + len(w)]
            k += len(w)
            nws.append([(i, j == len(nl) - 1 and i in (10, 12, 13, 16, 17)) for j, i in enumerate(nl)])
        out.append((vid, nws))
    return out


def word_shuffled(verses, rnd):
    """Same words, order shuffled across the corpus (keeps vocabulary, destroys sequence)."""
    ws = [w for _, v in verses for w in v]
    rnd.shuffle(ws)
    k, out = 0, []
    for vid, v in verses:
        out.append((vid, ws[k:k + len(v)]))
        k += len(v)
    return out


def run_hits(verses, targets, maxrun=3):
    words = [value(w) for _, ws in verses for w in ws]
    hits = Counter()
    for t in targets:
        hits[(t, 1)] = sum(1 for v in words if v == t)
    for r in range(2, maxrun + 1):
        s = sum(words[:r])
        sums = Counter([s])
        for i in range(r, len(words)):
            s += words[i] - words[i - r]
            sums[s] += 1
        for t in targets:
            hits[(t, r)] = sums[t]
    return hits


def is_triangular(n):
    k = int((math.isqrt(8 * n + 1) - 1) // 2)
    return k * (k + 1) // 2 == n


def lab(n_controls=20, seed=11):
    rnd = random.Random(seed)
    verses = torah_verses()
    words = [w for _, ws in verses for w in ws]
    lines = []
    P = lines.append
    P("# Gematria lab: Torah (Genesis-Deuteronomy, OSHB/WLC ketiv)")
    P(f"verses {len(verses)}, words {len(words)}, letters {sum(len(w) for w in words)}")
    # 1. mod 9
    bad = sum(1 for w in words if not (value(w, 'standard') % 9 == value(w, 'ordinal') % 9 == value(w, 'katan') % 9))
    bad_sofit = sum(1 for w in words if value(w, 'sofit') % 9 != value(w) % 9)
    P("\n## 1. Methods mod 9")
    P(f"words where standard, ordinal, katan disagree mod 9: {bad}  (Lean `methods_agree_mod9`: always 0)")
    P(f"words where sofit differs from standard mod 9: {bad_sofit} (final kaf/mem/nun/pe/tsade change the residue)")
    # 2. collisions
    forms = Counter(tuple(i for i, _ in w) for w in words)
    vals = Counter()
    for f in forms:
        vals[sum(HEB_VALUES[i] for i in f)] += 1
    P("\n## 2. Collisions")
    P(f"distinct letter strings {len(forms)}, distinct standard values {len(vals)}, "
      f"mean strings per value {len(forms) / len(vals):.2f}, max {max(vals.values())} (value {vals.most_common(1)[0][0]})")
    anag = Counter(tuple(sorted(f)) for f in forms)
    P(f"distinct letter multisets {len(anag)}: {len(forms) - len(anag)} strings are anagrams of another "
      f"string (equal value forced, Lean `gematria_perm`)")
    # 3. hits
    targets = [26, 72, 86, 314, 358, 541, 613, 913, 2701]
    real = run_hits(verses, targets)
    ctrl = [run_hits(shuffled(verses, rnd), targets) for _ in range(n_controls)]
    wctrl = [run_hits(word_shuffled(verses, rnd), targets) for _ in range(n_controls)]
    P("\n## 3. Target hits: real text vs two controls")
    P("run = number of consecutive words summed.  letter-shuffle keeps letter frequencies and word")
    P("lengths but destroys words; word-shuffle keeps every word but destroys their order.")
    P("target  run  real | letter-shuffle mean +- sd   z | word-shuffle mean +- sd   z")

    def ms(c):
        mu = sum(c) / len(c)
        sd = (sum((x - mu) ** 2 for x in c) / max(1, len(c) - 1)) ** 0.5
        return mu, sd

    for t in targets:
        for r in (1, 2, 3):
            mu, sd = ms([h[(t, r)] for h in ctrl])
            mu2, sd2 = ms([h[(t, r)] for h in wctrl])
            z = (real[(t, r)] - mu) / sd if sd > 0 else float("nan")
            z2 = (real[(t, r)] - mu2) / sd2 if sd2 > 0 else float("nan")
            P(f"{t:6d}  {r:3d}  {real[(t, r)]:5d} | {mu:8.1f} +- {sd:6.1f} {z:+7.2f} | "
              f"{mu2:8.1f} +- {sd2:6.1f} {z2:+7.2f}")
    # which phrases produce the order-dependent excesses
    flat = [w for _, ws in verses for w in ws]
    heb = lambda w: "".join(codec.HEB_TO_FINAL.get(codec.HEBREW[i], codec.HEBREW[i]) if f else codec.HEBREW[i]
                            for i, f in w)
    for t in targets:
        for r in (2, 3):
            mu2, sd2 = ms([h[(t, r)] for h in wctrl])
            if sd2 > 0 and abs(real[(t, r)] - mu2) / sd2 > 3:
                ph = Counter(" ".join(heb(w) for w in flat[i:i + r]) for i in range(len(flat) - r + 1)
                             if sum(value(w) for w in flat[i:i + r]) == t)
                P(f"  {t} as {r} consecutive words: top phrases " +
                  "; ".join(f"{k} x{c}" for k, c in ph.most_common(3)))
    top = Counter(value(w) for w in words).most_common(8)
    P("most frequent word values (value: count): " + ", ".join(f"{v}: {c}" for v, c in top))
    # 4. verse sums
    vs = [sum(value(w) for w in ws) for _, ws in verses]
    P("\n## 4. Verse sums")
    for m in (9, 7):
        c = Counter(v % m for v in vs)
        chi = sum((c[k] - len(vs) / m) ** 2 / (len(vs) / m) for k in range(m))
        P(f"mod {m}: counts {[c[k] for k in range(m)]}, chi-square vs uniform {chi:.1f} (df {m - 1})")
    tri_real = sum(1 for v in vs if is_triangular(v))
    tri_ctrl = []
    for _ in range(n_controls):
        sv = shuffled(verses, rnd)
        tri_ctrl.append(sum(1 for _, ws in sv if is_triangular(sum(value(w) for w in ws))))
    mu = sum(tri_ctrl) / len(tri_ctrl)
    P(f"triangular verse sums: real {tri_real}, controls mean {mu:.1f} (range {min(tri_ctrl)}-{max(tri_ctrl)})")
    g11 = vs[0]
    P(f"Genesis 1:1 = {g11} = T73 = 37*73: triangular {is_triangular(g11)}")
    # word length vs value
    L = Counter()
    S = Counter()
    for w in words:
        L[len(w)] += 1
        S[len(w)] += value(w)
    P("\n## 5. Value grows with length (the dominant structure)")
    P("letters  words  mean value")
    for k in sorted(L)[:10]:
        P(f"{k:7d}  {L[k]:5d}  {S[k] / L[k]:9.1f}")
    return "\n".join(lines)


if __name__ == "__main__":
    print(lab())
