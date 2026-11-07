"""The language layer: a lossless codec of any text onto the 64 cells, letter-level views of
Hebrew, Greek and English, and a deobfuscation toolkit scored by language models trained on
the committed Bible texts.

1. **Cell codec** (`encode_text`, `decode_cells`).  UTF-8 bytes -> bits (most significant
   first) -> 6-bit cells, last cell zero-padded; decoding reads 8 bits at a time and drops the
   incomplete tail.  This is exactly `encode`/`decode` of `Sovereign.Organism.HypercubeModel`,
   where `decode_encode` proves it lossless for every byte string; written with the Base64
   alphabet it is standard Base64 without '=' padding.  Every cell can also be shown as a codon
   or a hexagram (`render`), so any text has a reversible "DNA" and "I Ching" spelling.
2. **Letters** (`letters`, `gematria`, `braid_word`, `walk`).  Script detection, final forms,
   standard gematria (Hebrew mispar hechrechi, Greek isopsephy, English ordinal), and the
   letter -> braid-generator map of `scripts/braid_walk.py` (proved to act on Q6 in
   `Sovereign.Organism.BraidWalk`).
3. **Deobfuscation** (`deobfuscate`).  Searches chains of standard decoders and classical
   ciphers (Base64, hex, binary, cell lists, URL escapes, reversal, Atbash, Albam, Caesar,
   affine, Vigenere) and ranks candidates by a character-bigram model of the KJV, the Hebrew
   Bible (OSHB) or the Greek New Testament (Tischendorf).  It recovers text that was hidden
   with these methods; it does not find messages that were never put there, and its score says
   how much a candidate looks like the training text, nothing more.
"""
import base64
import binascii
import json
import math
import os
import re
import sys
import unicodedata
import urllib.parse
from functools import lru_cache

from . import cells, store

B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
HEBREW = "אבגדהוזחטיכלמנסעפצקרשת"
HEB_FINAL = {"ך": "כ", "ם": "מ", "ן": "נ", "ף": "פ", "ץ": "צ"}
HEB_TO_FINAL = {v: k for k, v in HEB_FINAL.items()}
GREEK = "αβγδεζηθικλμνξοπρστυφχψω"
LATIN = "abcdefghijklmnopqrstuvwxyz"
HEB_VALUES = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 200, 300, 400]
GREEK_VALUES = [1, 2, 3, 4, 5, 7, 8, 9, 10, 20, 30, 40, 50, 60, 70, 80, 100, 200, 300, 400, 500,
                600, 700, 800]  # stigma (6) and koppa (90) are not in the 24-letter alphabet
ALPHABETS = {"he": HEBREW, "el": GREEK, "en": LATIN}


# ====================================================================== 1. the cell codec
def encode_bytes(data):
    bits = "".join(format(b, "08b") for b in data)
    if len(bits) % 6:
        bits += "0" * (6 - len(bits) % 6)
    return [int(bits[i:i + 6], 2) for i in range(0, len(bits), 6)]


def decode_cells(cs):
    bits = "".join(format(c, "06b") for c in cs)
    return bytes(int(bits[i:i + 8], 2) for i in range(0, len(bits) - len(bits) % 8, 8))


def encode_text(text):
    return encode_bytes(text.encode("utf-8"))


def decode_text(cs):
    return decode_cells(cs).decode("utf-8", errors="replace")


def render(cs, style="base64"):
    if style == "base64":
        return "".join(B64[c] for c in cs)
    if style == "codon":
        return " ".join(cells.codon(c) for c in cs)
    if style == "amino":
        return "".join(cells.amino(c) for c in cs)
    if style == "hexagram":
        return " ".join(chr(0x4DC0 + _king_wen_free_index(c)) for c in cs)
    if style == "cells":
        return " ".join(str(c) for c in cs)
    raise ValueError(style)


def _king_wen_free_index(c):
    """Index into the Unicode hexagram block by binary value (the block is in King Wen order,
    so the glyph is a label only; the line pattern itself is `cells.hexagram_lines`)."""
    return c


def parse_rendered(s, style="base64"):
    if style == "base64":
        return [B64.index(ch) for ch in s if ch in B64]
    if style == "codon":
        return [16 * cells.BASES.index(w[0]) + 4 * cells.BASES.index(w[1]) + cells.BASES.index(w[2])
                for w in s.replace("T", "U").split()]
    if style == "cells":
        return [int(x) for x in s.split()]
    raise ValueError(style)


# ====================================================================== 2. letters
def strip_marks(text):
    return "".join(c for c in unicodedata.normalize("NFD", text) if not unicodedata.combining(c))


def letters(text):
    """[(script, index 0-based, is_final)] for every Hebrew, Greek or Latin letter."""
    out = []
    for c in strip_marks(text):
        if c in HEB_FINAL:
            out.append(("he", HEBREW.index(HEB_FINAL[c]), True))
        elif c in HEBREW:
            out.append(("he", HEBREW.index(c), False))
        else:
            lc = c.lower()
            if lc == "ς":
                out.append(("el", GREEK.index("σ"), True))
            elif lc in GREEK:
                out.append(("el", GREEK.index(lc), False))
            elif lc in LATIN:
                out.append(("en", LATIN.index(lc), False))
    return out


def detect_script(text):
    counts = {"he": 0, "el": 0, "en": 0}
    for s, _, _ in letters(text):
        counts[s] += 1
    return max(counts, key=counts.get) if any(counts.values()) else None


# Letter names (milui).  These spellings are the ones that reproduce the subtotals quoted in the
# calibration documents (22 names = 4248, odd positions 1622, even 2626; docs/HYPERCUBE_CALIBRATION_
# 2026-10-23.md and HypercubeCalibration.letterNames).  Other spellings are in use (הא/הה for he,
# ויו/ואו for vav, פה/פי for pe, תיו/תאו for tav).
LETTER_NAMES = ["אלף", "בית", "גימל", "דלת", "הי", "וו", "זין", "חית", "טית", "יוד", "כף", "למד", "מם",
                "נון", "סמך", "עין", "פא", "צדי", "קוף", "ריש", "שין", "תו"]
GEMATRIA_METHODS = ("standard", "sofit", "ordinal", "katan", "milui", "complete")


def gematria(text, method="standard"):
    """Letter-value sum.

    * `standard` (mispar hechrachi): Hebrew finals = base values, Greek isopsephy, English ordinal
      (a = 1 ... z = 26);
    * `sofit` (mispar gadol): Hebrew finals ך ם ן ף ץ = 500 ... 900;
    * `ordinal` (mispar siduri): position in the alphabet (Hebrew 1..22, finals as base letter);
    * `katan` (mispar katan): standard value with its zeros dropped (400 -> 4, 90 -> 9);
    * `milui`: sum of the spelled-out letter names (`LETTER_NAMES`), Hebrew only;
    * `complete` (as used in the calibration documents): standard + ordinal.
    """
    if method == "complete":
        return gematria(text, "standard") + gematria(text, "ordinal")
    total = 0
    for s, i, fin in letters(text):
        if s != "he":
            v = GREEK_VALUES[i] if s == "el" else i + 1
            if method == "ordinal":
                v = i + 1
            elif method == "katan":
                while v % 10 == 0:
                    v //= 10
            total += v
            continue
        if method == "standard":
            total += HEB_VALUES[i]
        elif method == "sofit":
            total += (500 + 100 * [10, 12, 13, 16, 17].index(i)) if fin else HEB_VALUES[i]
        elif method == "ordinal":
            total += i + 1
        elif method == "katan":
            v = HEB_VALUES[i]
            while v % 10 == 0:
                v //= 10
            total += v
        elif method == "milui":
            total += gematria(LETTER_NAMES[i])
        else:
            raise ValueError(f"unknown gematria method {method!r}; use one of {GEMATRIA_METHODS}")
    return total


def braid_word(text, strands=6):
    """Signed generators (+i = sigma_i, -i = inverse; finals invert) as in scripts/braid_walk.py."""
    word = []
    for _, i, final in letters(text):
        g = i % (strands - 1) + 1
        word.append(-g if final else g)
    return word


def act(g, x):
    i = abs(g) - 1
    a, b = (x >> i) & 1, (x >> (i + 1)) & 1
    na, nb = (1 - b, a) if g > 0 else (b, 1 - a)
    x &= ~((1 << i) | (1 << (i + 1)))
    return x | (na << i) | (nb << (i + 1))


def walk(text, start=0):
    path = [start]
    for g in braid_word(text):
        path.append(act(g, path[-1]))
    return path


# ====================================================================== 3. language models
def _norm_for_model(text, lang):
    t = strip_marks(text).lower()
    alpha = ALPHABETS[lang]
    out = []
    for c in t:
        if lang == "he":
            c = HEB_FINAL.get(c, c)
        if lang == "el" and c == "ς":
            c = "σ"
        if c in alpha:
            out.append(c)
        elif out and out[-1] != " ":
            out.append(" ")
    return "".join(out).strip()


@lru_cache(maxsize=3)
def model(lang):
    """Character bigram log-probabilities (add-one smoothing) from the Bible corpus of `lang`,
    cached in .cache/lm_<lang>.json."""
    path = os.path.join(store.CACHE, f"lm_{lang}.json")
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    from .scripture import corpus
    t = _norm_for_model(corpus(lang), lang)
    sym = " " + ALPHABETS[lang]
    big = {a + b: 1 for a in sym for b in sym}
    uni = {a: len(sym) for a in sym}
    for a, b in zip(t, t[1:]):
        big[a + b] += 1
        uni[a] += 1
    lm = {k: math.log(v / uni[k[0]]) for k, v in big.items()}
    freq = {a: 0 for a in ALPHABETS[lang]}
    for c in t:
        if c != " ":
            freq[c] += 1
    n = sum(freq.values())
    m = {"bigram": lm, "unigram": {a: v / n for a, v in freq.items()}}
    from collections import Counter
    m["vocab"] = dict(Counter(t.split()).most_common(40000))
    probe = t[:200000]
    m["corpus_score"] = sum(lm[a + b] for a, b in zip(probe, probe[1:])) / (len(probe) - 1)
    m["corpus_score"] += _word_hits(probe, m["vocab"])
    os.makedirs(store.CACHE, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(m, f)
    return m


def _word_hits(t, vocab):
    """Mean over words of log(1 + count) / log(1 + max count): 1 for the commonest corpus word,
    0 for a word never seen."""
    words = t.split()
    if not words:
        return 0.0
    top = math.log1p(max(vocab.values()))
    return sum(math.log1p(vocab.get(w, 0)) for w in words) / (len(words) * top)


@lru_cache(maxsize=3)
def _vocab(lang):
    return model(lang)["vocab"]


def score(text, lang=None):
    """(lang, score, coverage).  Score = mean bigram log-probability per character + the
    fraction of words found in the corpus vocabulary.  Higher is more text-like; compare with
    model(lang)['corpus_score'] (the same score on the training text)."""
    langs = [lang] if lang else ["en", "he", "el"]
    best = (None, -99.0, 0.0)
    for lg in langs:
        t = _norm_for_model(text, lg)
        if len(t) < 2:
            continue
        cover = sum(1 for c in strip_marks(text).lower() if c in ALPHABETS[lg] or c in HEB_FINAL or c == "ς") / max(
            1, sum(1 for c in text if not c.isspace()))
        lm = model(lg)["bigram"]
        s = sum(lm.get(a + b, -12) for a, b in zip(t, t[1:])) / (len(t) - 1)
        s = s * cover + (-12) * (1 - cover) + _word_hits(t, _vocab(lg))
        if s > best[1]:
            best = (lg, s, cover)
    return best


# ====================================================================== 4. transforms
def _map_letters(text, lang, f):
    alpha = ALPHABETS[lang]
    out = []
    for ch in text:
        base = ch
        final = False
        if lang == "he" and ch in HEB_FINAL:
            base, final = HEB_FINAL[ch], True
        low = base.lower()
        if low in alpha:
            r = alpha[f(alpha.index(low)) % len(alpha)]
            out.append(r.upper() if base != low else r)
        else:
            out.append(ch)
    return "".join(out)


def atbash(text, lang="en"):
    n = len(ALPHABETS[lang])
    return _map_letters(text, lang, lambda i: n - 1 - i)


def caesar(text, k, lang="en"):
    return _map_letters(text, lang, lambda i: i + k)


def albam(text):
    """Hebrew Albam: the alphabet split in two halves of 11 letters which are exchanged."""
    return _map_letters(text, "he", lambda i: (i + 11) % 22)


def affine_decrypt(text, a, b, lang="en"):
    n = len(ALPHABETS[lang])
    ainv = pow(a, -1, n)
    return _map_letters(text, lang, lambda i: ainv * (i - b))


def vigenere(text, key, decrypt=True, lang="en"):
    alpha = ALPHABETS[lang]
    ks = [alpha.index(c) for c in key.lower() if c in alpha]
    out, j = [], 0
    for ch in text:
        low = ch.lower()
        if low in alpha:
            k = ks[j % len(ks)] * (-1 if decrypt else 1)
            r = alpha[(alpha.index(low) + k) % len(alpha)]
            out.append(r.upper() if ch != low else r)
            j += 1
        else:
            out.append(ch)
    return "".join(out)


def _try_decoders(text):
    """Standard encodings that a string might be in; yields (name, decoded)."""
    s = text.strip()
    compact = re.sub(r"\s+", "", s)
    if len(compact) >= 4 and re.fullmatch(r"[A-Za-z0-9+/]+=*", compact):
        try:
            pad = compact + "=" * (-len(compact) % 4)
            d = base64.b64decode(pad, validate=True).decode("utf-8")
            if d and all(c.isprintable() or c.isspace() for c in d):
                yield "base64", d
        except (binascii.Error, UnicodeDecodeError, ValueError):
            pass
    if len(compact) >= 4 and len(compact) % 2 == 0 and re.fullmatch(r"[0-9a-fA-F]+", compact):
        try:
            yield "hex", bytes.fromhex(compact).decode("utf-8")
        except (ValueError, UnicodeDecodeError):
            pass
    if len(compact) >= 8 and re.fullmatch(r"[01]+", compact) and len(compact) % 8 == 0:
        try:
            yield "binary", bytes(int(compact[i:i + 8], 2) for i in range(0, len(compact), 8)).decode("utf-8")
        except UnicodeDecodeError:
            pass
    if re.fullmatch(r"\d{1,2}(\s+\d{1,2})+", s) and all(int(x) < 64 for x in s.split()):
        try:
            yield "cells", decode_cells([int(x) for x in s.split()]).decode("utf-8")
        except UnicodeDecodeError:
            pass
    if "%" in s:
        u = urllib.parse.unquote(s)
        if u != s:
            yield "url", u


def caesar_solve(text, lang="en"):
    n = len(ALPHABETS[lang])
    return max(((f"caesar-{k}", caesar(text, -k, lang)) for k in range(1, n)), key=lambda c: score(c[1], lang)[1])


def affine_solve(text):
    best = None
    for a in (1, 3, 5, 7, 9, 11, 15, 17, 19, 21, 23, 25):
        for b in range(26):
            if a == 1 and b == 0:
                continue
            cand = affine_decrypt(text, a, b)
            s = score(cand, "en")[1]
            if best is None or s > best[0]:
                best = (s, f"affine(a={a},b={b})", cand)
    return best[1], best[2]


def index_of_coincidence(seq):
    n = len(seq)
    if n < 2:
        return 0.0
    from collections import Counter
    return sum(v * (v - 1) for v in Counter(seq).values()) / (n * (n - 1))


def vigenere_solve(text, max_key=12):
    """Vigenere: candidate key lengths by the index of coincidence, initial key letters by
    chi-square against the KJV letter frequencies, then each key letter refined to maximise the
    language score.  Returns (name, plaintext)."""
    letters_only = [c for c in text.lower() if c in LATIN]
    if len(letters_only) < 16:
        return None
    freq = model("en")["unigram"]
    lengths = []
    for L in range(1, min(max_key, len(letters_only) // 3) + 1):
        cols = [letters_only[i::L] for i in range(L)]
        lengths.append((sum(index_of_coincidence(c) for c in cols) / L, L))
    lengths.sort(reverse=True)
    best = None
    for ioc, L in lengths[:4]:
        cols = [letters_only[i::L] for i in range(L)]
        key = []
        for col in cols:
            chi = []
            for k in range(26):
                dec = [LATIN[(LATIN.index(c) - k) % 26] for c in col]
                chi.append((sum((dec.count(a) - len(col) * freq[a]) ** 2 / max(1e-9, len(col) * freq[a])
                                for a in LATIN), k))
            key.append(min(chi)[1])
        for _ in range(2):
            for i in range(L):
                key[i] = max(range(26), key=lambda k: score(
                    vigenere(text, "".join(LATIN[x] for x in key[:i] + [k] + key[i + 1:])), "en")[1])
        ks = "".join(LATIN[x] for x in key)
        cand = vigenere(text, ks)
        s = score(cand, "en")[1] - 0.03 * L
        if best is None or s > best[0]:
            best = (s, f"vigenere(key={ks})", cand)
    return best[1], best[2]


def _cipher_moves(text):
    lang = detect_script(text) or "en"
    yield "reverse", text[::-1]
    yield f"atbash-{lang}", atbash(text, lang)
    if lang == "he":
        yield "albam", albam(text)
    yield caesar_solve(text, lang)
    if lang == "en":
        yield affine_solve(text)
        v = vigenere_solve(text)
        if v:
            yield v


def deobfuscate(text, depth=3, beam=6):
    """Beam search over decoder/cipher chains.  Returns candidates sorted best first:
    [{'chain': [...], 'text': ..., 'lang': ..., 'score': ..., 'corpus_score': ...}]."""
    def rec(chain, t):
        lg, s, cov = score(t)
        s -= 0.05 * len(chain)  # prefer the shorter explanation
        return {"chain": chain, "text": t, "lang": lg, "score": round(s, 3), "coverage": round(cov, 3),
                "corpus_score": round(model(lg)["corpus_score"], 3) if lg else None}

    frontier = [rec([], text)]
    seen = {text}
    results = list(frontier)
    for _ in range(depth):
        nxt = []
        for node in frontier:
            moves = list(_try_decoders(node["text"]))
            if not moves:
                moves = list(_cipher_moves(node["text"]))
            for name, t in moves:
                if t in seen or not t:
                    continue
                seen.add(t)
                nxt.append(rec(node["chain"] + [name], t))
        if not nxt:
            break
        nxt.sort(key=lambda r: r["score"], reverse=True)
        frontier = nxt[:beam]
        results.extend(frontier)
    results.sort(key=lambda r: (r["score"], -len(r["chain"])), reverse=True)
    return results


def letter_profile(text):
    """Script, letter count, gematria, braid word and walk summary for a text."""
    w = walk(text)
    return {"script": detect_script(text), "letters": len(letters(text)), "gematria": gematria(text),
            "braid_word_length": len(w) - 1, "walk_end_from_0": w[-1],
            "cells": encode_text(text), "base64": render(encode_text(text))}


if __name__ == "__main__":
    print(json.dumps(deobfuscate(" ".join(sys.argv[1:]))[:3], ensure_ascii=False, indent=1))
