"""
Bible text → QBX-IR braid.

Encoding ``letter-ordinal-v1``
------------------------------
The conversion is a fixed, documented rule; nothing in it is inferred from
meaning.

1. **Normalise.**  The text is decomposed (Unicode NFKD, which also splits the
   Hebrew presentation forms U+FB1D–U+FB4F) and every combining mark is
   dropped: Hebrew points (niqqud), cantillation accents, Greek accents and
   breathings, Latin diacritics.  What remains are base letters.
2. **Words.**  Words are maximal runs of letters.  Anything else — spaces,
   maqqef ``־``, paseq ``׀``, sof pasuq ``׃``, punctuation, digits — separates
   words and contributes no crossings.
3. **Letters.**  Each letter has an ordinal in its alphabet:

   * Hebrew ``אבגדהוזחטיכלמנסעפצקרשת`` → 1…22; the final (sofit) forms
     ``ך ם ן ף ץ`` take the ordinal of their base letter (כ מ נ פ צ);
   * Greek ``αβγδεζηθικλμνξοπρστυφχψω`` → 1…24 (upper case folded); final
     sigma ``ς`` takes the ordinal of ``σ``;
   * Latin ``a``…``z`` → 1…26 (upper case folded).

4. **Generators.**  On ``n`` strands (default 8, so the generators are
   σ₁…σ₇) a letter of ordinal ``k`` becomes the generator σᵢ with
   ``i = ((k − 1) mod (n − 1)) + 1``.  Its exponent is ``+1``, except that a
   final form (Hebrew sofit, Greek ``ς``) gives the **inverse** generator σᵢ⁻¹
   when the sofit rule is on (the default).  With ``sofit_rule=False`` a final
   form is encoded exactly like its base letter.
5. **Composition.**  A word's braid is the product of its letters' generators
   in reading order (Hebrew right-to-left reading order is the logical order of
   the Unicode string, so no reversal is needed).  A verse's braid is the
   product of its word braids, and a passage's braid is the product of its
   verse braids.

When ``n − 1`` is at least the alphabet size (e.g. ``n = 23`` for Hebrew) the
letter → generator map is injective and :func:`decode_short` recovers the
consonantal text from the word (up to the sofit/base distinction when the sofit
rule is off).  With the default 8 strands several letters share a generator,
so the braid is a lossy image of the text; the encoding table is recorded in
each braid's metadata.
"""

from __future__ import annotations

import unicodedata
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Tuple

from qbx_ir.core.braid import Braid

SCHEME = "letter-ordinal-v1"

HEBREW = "אבגדהוזחטיכלמנסעפצקרשת"
HEBREW_FINALS = {"ך": "כ", "ם": "מ", "ן": "נ", "ף": "פ", "ץ": "צ"}
GREEK = "αβγδεζηθικλμνξοπρστυφχψω"
GREEK_FINALS = {"ς": "σ"}
LATIN = "abcdefghijklmnopqrstuvwxyz"

ALPHABETS: Dict[str, Tuple[str, Dict[str, str]]] = {
    "hebrew": (HEBREW, HEBREW_FINALS),
    "greek": (GREEK, GREEK_FINALS),
    "latin": (LATIN, {}),
}

DEFAULT_STRANDS = 8


@dataclass(frozen=True)
class Letter:
    """A base letter of the normalised text."""

    char: str          # the letter as written (final forms kept)
    script: str        # "hebrew" | "greek" | "latin"
    ordinal: int       # 1-based position in its alphabet
    final: bool        # Hebrew sofit / Greek final sigma


def classify(ch: str) -> Optional[Letter]:
    """The :class:`Letter` for one base character, or None if it is not a letter we encode."""
    for script, (alphabet, finals) in ALPHABETS.items():
        c = ch if script == "hebrew" else ch.lower()
        if c in finals:
            return Letter(c, script, alphabet.index(finals[c]) + 1, True)
        if c in alphabet:
            return Letter(c, script, alphabet.index(c) + 1, False)
    return None


def strip_marks(text: str) -> str:
    """NFKD-decompose and drop all combining marks (points, accents, diacritics)."""
    return "".join(c for c in unicodedata.normalize("NFKD", text)
                   if not unicodedata.combining(c) and unicodedata.category(c) != "Mn")


def tokenize(text: str) -> List[List[Letter]]:
    """The words of ``text`` as lists of letters (marks dropped, separators removed)."""
    words: List[List[Letter]] = []
    current: List[Letter] = []
    for ch in strip_marks(text):
        letter = classify(ch)
        if letter is None:
            if current:
                words.append(current)
                current = []
            continue
        current.append(letter)
    if current:
        words.append(current)
    return words


def consonantal(text: str) -> str:
    """The letters of ``text`` with words separated by single spaces."""
    return " ".join("".join(l.char for l in w) for w in tokenize(text))


@dataclass(frozen=True)
class Encoding:
    """Parameters of the ``letter-ordinal-v1`` encoding."""

    strand_count: int = DEFAULT_STRANDS
    sofit_rule: bool = True

    def __post_init__(self):
        if self.strand_count < 2:
            raise ValueError("strand_count must be at least 2 (σ₁ needs two strands)")

    @property
    def generators(self) -> int:
        return self.strand_count - 1

    def generator(self, letter: Letter) -> int:
        """Short form (``±i``) of the generator for one letter."""
        i = (letter.ordinal - 1) % self.generators + 1
        return -i if (letter.final and self.sofit_rule) else i

    def injective_for(self, script: str) -> bool:
        return self.generators >= len(ALPHABETS[script][0])

    def describe(self) -> Dict[str, Any]:
        """JSON-serialisable description, including the full letter → generator table."""
        table: Dict[str, Dict[str, int]] = {}
        for script, (alphabet, finals) in ALPHABETS.items():
            t = {c: self.generator(Letter(c, script, k + 1, False))
                 for k, c in enumerate(alphabet)}
            for f, base in finals.items():
                t[f] = self.generator(Letter(f, script, alphabet.index(base) + 1, True))
            table[script] = t
        return {"scheme": SCHEME, "strand_count": self.strand_count,
                "sofit_rule": self.sofit_rule, "table": table}


@dataclass
class EncodedText:
    """A piece of text and its braid, with the word → crossing spans."""

    label: str
    text: str
    braid: Braid
    words: List[str] = field(default_factory=list)
    spans: List[Tuple[int, int]] = field(default_factory=list)   # [start, end) in the word

    @property
    def letters(self) -> int:
        return sum(len(w) for w in self.words)


def encode_text(text: str, label: str = "text", encoding: Encoding = Encoding(),
                extra_metadata: Optional[Dict[str, Any]] = None) -> EncodedText:
    """Encode a verse (or any text) as one braid: the product of its word braids."""
    short: List[int] = []
    words: List[str] = []
    spans: List[Tuple[int, int]] = []
    for w in tokenize(text):
        start = len(short)
        short.extend(encoding.generator(l) for l in w)
        words.append("".join(l.char for l in w))
        spans.append((start, len(short)))
    meta: Dict[str, Any] = {
        "source": "qbx_bible",
        "ref": label,
        "scheme": SCHEME,
        "strand_count": encoding.strand_count,
        "sofit_rule": encoding.sofit_rule,
        "consonantal_text": " ".join(words),
        "words": [{"text": w, "span": list(s)} for w, s in zip(words, spans)],
    }
    if extra_metadata:
        meta.update(extra_metadata)
    braid = Braid.from_short_form(encoding.strand_count, short, name=label)
    braid = Braid(braid.strand_count, braid.word, braid.strands, label, meta)
    return EncodedText(label, text, braid, words, spans)


def encode_word(word: str, encoding: Encoding = Encoding()) -> Braid:
    """The braid of a single word (all its letters, separators ignored)."""
    return encode_text(word, word, encoding).braid


def concat(parts: Sequence[EncodedText], label: str, encoding: Encoding = Encoding()) -> EncodedText:
    """The passage braid: the product of the given verse braids, in order."""
    short: List[int] = []
    words: List[str] = []
    spans: List[Tuple[int, int]] = []
    verses: List[Dict[str, Any]] = []
    for p in parts:
        offset = len(short)
        short.extend(p.braid.short_form())
        words.extend(p.words)
        spans.extend((a + offset, b + offset) for a, b in p.spans)
        verses.append({"ref": p.label, "span": [offset, len(short)]})
    meta = {
        "source": "qbx_bible", "ref": label, "scheme": SCHEME,
        "strand_count": encoding.strand_count, "sofit_rule": encoding.sofit_rule,
        "verses": verses,
    }
    b = Braid.from_short_form(encoding.strand_count, short, name=label)
    b = Braid(b.strand_count, b.word, b.strands, label, meta)
    return EncodedText(label, "\n".join(p.text for p in parts), b, words, spans)


def decode_short(short: Sequence[int], script: str = "hebrew",
                 encoding: Encoding = Encoding(23)) -> str:
    """Invert the letter map on a word when it is injective for ``script``.

    A negative generator decodes to the final form of its letter (when the
    alphabet has one); words are not recovered, only the letter sequence.
    """
    if not encoding.injective_for(script):
        raise ValueError(f"{encoding.strand_count} strands do not encode {script} injectively")
    alphabet, finals = ALPHABETS[script]
    base_to_final = {b: f for f, b in finals.items()}
    out = []
    for g in short:
        c = alphabet[abs(g) - 1]
        if g < 0:
            if c not in base_to_final:
                raise ValueError(f"σ{abs(g)}⁻¹ is not the image of a {script} letter")
            c = base_to_final[c]
        out.append(c)
    return "".join(out)
