"""Alphabets, written and spoken, as geometry.

Three alphabets are tabulated letter by letter: Hebrew (22 letters of the square
script), Greek (24 uppercase letters) and Latin (26 uppercase letters).  Each
letter carries three kinds of data.

Written geometry (of the uppercase / square-script glyph in a plain sans-serif
reference style):
  holes   number of enclosed regions (first Betti number of the glyph);
  sym     the symmetries of the glyph, a subgroup of the Klein four-group
          {id, V (left-right mirror), H (top-bottom mirror), R (half turn)},
          stored as a string over "VHR".

Spoken geometry: the primary sound of the letter (IPA) and its articulatory
features, encoded as a bitmask over FEATURES (22 binary features).  A sound is
thereby a vertex of the 22-cube, i.e. a basis blade of a Clifford algebra on 22
generators, and the distance between two sounds is the Hamming distance of
their masks (the number of features in which they differ).  A two-segment letter
(Greek/Latin X, Greek Psi, Zeta) is encoded by the union of the features of its
two segments.

Numbers: Hebrew uses the project's standard gematria table (1..400 for the 22
letters; the final forms ך ם ן ף ץ count 500..900, as in migration 014 and
`Gematria.standard`; `value_of(ch, "hechrachi")` gives the strict mispar hechrachi
reading, where a final form counts as its base letter), Greek the standard
isopsephy values, Latin the ordinal 1..26 (Latin letters have no traditional
values).  The written and spoken data of a final form are those of its base
letter; final-form glyphs are not tabulated separately.

Sound values follow standard reconstructions:
  Hebrew   Tiberian consonant values, begadkefat letters at their stop value,
           shin as /ʃ/ (sin /s/ not separated), tsade as emphatic /sˤ/, qof as
           emphatic (uvular) /q/;
  Greek    Classical Attic (vowel length distinguishes Ε/Η and Ο/Ω);
  Latin    Classical Latin; J, U, W, Y given their usual later values.
These are reference facts entered by hand; they are not derived by any program.
Glyph features depend on typeface; the values here are for plain sans-serif
capitals (and square-script Hebrew, where no letter is exactly symmetric).

The same tables appear in `QBX/Formal/Engine/AlphabetGeometry.lean`, where the
claims made about them (sizes, distinctness, symmetry closure, the
Phoenician-lineage coincidences) are checked; `python -m qbx_engine lean-tables`
regenerates the Lean tables from this file.
"""

FEATURES = (
    # place (one per segment)
    "labial", "coronal", "posterior", "dorsal", "guttural",
    # manner
    "stop", "fricative", "affricate", "nasal", "lateral", "rhotic", "glide", "vowel",
    # laryngeal / secondary
    "voice", "sibilant", "aspirated", "emphatic",
    # vowel quality
    "high", "low", "back", "round", "long",
)
BIT = {f: i for i, f in enumerate(FEATURES)}


def mask(*fs):
    m = 0
    for f in fs:
        m |= 1 << BIT[f]
    return m


def features(m):
    return [f for f in FEATURES if m >> BIT[f] & 1]


def popcount(x):
    c = 0
    while x:
        x &= x - 1
        c += 1
    return c


def hamming(a, b):
    return popcount(a ^ b)


# Sounds ----------------------------------------------------------------------
S = {
    "ʔ": mask("guttural", "stop"),
    "b": mask("labial", "stop", "voice"),
    "g": mask("dorsal", "stop", "voice"),
    "d": mask("coronal", "stop", "voice"),
    "h": mask("guttural", "fricative"),
    "w": mask("labial", "glide", "voice"),
    "z": mask("coronal", "fricative", "voice", "sibilant"),
    "ħ": mask("guttural", "fricative", "emphatic"),
    "tˤ": mask("coronal", "stop", "emphatic"),
    "j": mask("posterior", "glide", "voice"),
    "k": mask("dorsal", "stop"),
    "l": mask("coronal", "lateral", "voice"),
    "m": mask("labial", "nasal", "voice"),
    "n": mask("coronal", "nasal", "voice"),
    "s": mask("coronal", "fricative", "sibilant"),
    "ʕ": mask("guttural", "fricative", "voice", "emphatic"),
    "p": mask("labial", "stop"),
    "sˤ": mask("coronal", "fricative", "sibilant", "emphatic"),
    "q": mask("dorsal", "stop", "emphatic"),
    "r": mask("coronal", "rhotic", "voice"),
    "ʃ": mask("posterior", "fricative", "sibilant"),
    "t": mask("coronal", "stop"),
    "f": mask("labial", "fricative"),
    "tʰ": mask("coronal", "stop", "aspirated"),
    "pʰ": mask("labial", "stop", "aspirated"),
    "kʰ": mask("dorsal", "stop", "aspirated"),
    "kʷ": mask("dorsal", "labial", "stop", "round"),
    "zd": mask("coronal", "stop", "fricative", "voice", "sibilant"),
    "ks": mask("dorsal", "coronal", "stop", "fricative", "sibilant"),
    "ps": mask("labial", "coronal", "stop", "fricative", "sibilant"),
    # vowels
    "a": mask("vowel", "voice", "low"),
    "e": mask("vowel", "voice"),
    "ɛː": mask("vowel", "voice", "long"),
    "i": mask("vowel", "voice", "high"),
    "o": mask("vowel", "voice", "back", "round"),
    "ɔː": mask("vowel", "voice", "back", "round", "long"),
    "u": mask("vowel", "voice", "high", "back", "round"),
    "y": mask("vowel", "voice", "high", "round"),
}

# (glyph, name, value, ipa, holes, sym)
HEBREW = [
    ("א", "alef", 1, "ʔ", 0, ""), ("ב", "bet", 2, "b", 0, ""),
    ("ג", "gimel", 3, "g", 0, ""), ("ד", "dalet", 4, "d", 0, ""),
    ("ה", "he", 5, "h", 0, ""), ("ו", "vav", 6, "w", 0, ""),
    ("ז", "zayin", 7, "z", 0, ""), ("ח", "het", 8, "ħ", 0, ""),
    ("ט", "tet", 9, "tˤ", 0, ""), ("י", "yod", 10, "j", 0, ""),
    ("כ", "kaf", 20, "k", 0, ""), ("ל", "lamed", 30, "l", 0, ""),
    ("מ", "mem", 40, "m", 0, ""), ("נ", "nun", 50, "n", 0, ""),
    ("ס", "samekh", 60, "s", 1, ""), ("ע", "ayin", 70, "ʕ", 0, ""),
    ("פ", "pe", 80, "p", 0, ""), ("צ", "tsade", 90, "sˤ", 0, ""),
    ("ק", "qof", 100, "q", 0, ""), ("ר", "resh", 200, "r", 0, ""),
    ("ש", "shin", 300, "ʃ", 0, ""), ("ת", "tav", 400, "t", 0, ""),
]

GREEK = [
    ("Α", "alpha", 1, "a", 1, "V"), ("Β", "beta", 2, "b", 2, "H"),
    ("Γ", "gamma", 3, "g", 0, ""), ("Δ", "delta", 4, "d", 1, "V"),
    ("Ε", "epsilon", 5, "e", 0, "H"), ("Ζ", "zeta", 7, "zd", 0, "R"),
    ("Η", "eta", 8, "ɛː", 0, "VHR"), ("Θ", "theta", 9, "tʰ", 2, "VHR"),
    ("Ι", "iota", 10, "i", 0, "VHR"), ("Κ", "kappa", 20, "k", 0, "H"),
    ("Λ", "lambda", 30, "l", 0, "V"), ("Μ", "mu", 40, "m", 0, "V"),
    ("Ν", "nu", 50, "n", 0, "R"), ("Ξ", "xi", 60, "ks", 0, "VHR"),
    ("Ο", "omicron", 70, "o", 1, "VHR"), ("Π", "pi", 80, "p", 0, "V"),
    ("Ρ", "rho", 100, "r", 1, ""), ("Σ", "sigma", 200, "s", 0, "H"),
    ("Τ", "tau", 300, "t", 0, "V"), ("Υ", "upsilon", 400, "y", 0, "V"),
    ("Φ", "phi", 500, "pʰ", 2, "VHR"), ("Χ", "chi", 600, "kʰ", 0, "VHR"),
    ("Ψ", "psi", 700, "ps", 0, "V"), ("Ω", "omega", 800, "ɔː", 0, "V"),
]

LATIN = [
    ("A", "a", 1, "a", 1, "V"), ("B", "be", 2, "b", 2, "H"),
    ("C", "ce", 3, "k", 0, "H"), ("D", "de", 4, "d", 1, "H"),
    ("E", "e", 5, "e", 0, "H"), ("F", "ef", 6, "f", 0, ""),
    ("G", "ge", 7, "g", 0, ""), ("H", "ha", 8, "h", 0, "VHR"),
    ("I", "i", 9, "i", 0, "VHR"), ("J", "jota", 10, "j", 0, ""),
    ("K", "ka", 11, "k", 0, "H"), ("L", "el", 12, "l", 0, ""),
    ("M", "em", 13, "m", 0, "V"), ("N", "en", 14, "n", 0, "R"),
    ("O", "o", 15, "o", 1, "VHR"), ("P", "pe", 16, "p", 1, ""),
    ("Q", "qu", 17, "kʷ", 1, ""), ("R", "er", 18, "r", 1, ""),
    ("S", "es", 19, "s", 0, "R"), ("T", "te", 20, "t", 0, "V"),
    ("U", "u", 21, "u", 0, "V"), ("V", "ve", 22, "w", 0, "V"),
    ("W", "double u", 23, "w", 0, "V"), ("X", "ix", 24, "ks", 0, "VHR"),
    ("Y", "ypsilon", 25, "y", 0, "V"), ("Z", "zeta", 26, "zd", 0, "R"),
]

ALPHABETS = {"hebrew": HEBREW, "greek": GREEK, "latin": LATIN}


class Letter:
    __slots__ = ("alphabet", "index", "glyph", "name", "value", "ipa", "holes", "sym", "sound")

    def __init__(self, alphabet, index, row):
        self.alphabet = alphabet
        self.index = index
        self.glyph, self.name, self.value, self.ipa, self.holes, self.sym = row
        self.sound = S[self.ipa]

    def as_dict(self):
        return {
            "alphabet": self.alphabet, "index": self.index, "glyph": self.glyph,
            "name": self.name, "value": self.value, "ipa": self.ipa,
            "written": {"holes": self.holes, "symmetry": self.sym or "none",
                        "symmetry_group_order": 1 + len(self.sym)},
            "spoken": {"features": features(self.sound), "blade": self.sound,
                       "grade": popcount(self.sound)},
        }


def letters(alphabet):
    return [Letter(alphabet, i, row) for i, row in enumerate(ALPHABETS[alphabet])]


LOOKUP = {}
for _a in ALPHABETS:
    for _l in letters(_a):
        LOOKUP.setdefault(_l.glyph, _l)
for _a in ("latin", "greek"):
    for _l in letters(_a):
        LOOKUP.setdefault(_l.glyph.lower(), _l)
LOOKUP.setdefault("ς", LOOKUP["Σ"])
#: Hebrew final forms: (final, base letter, name, value).  The project's one gematria
#: convention is the seeded standard table -- migration 014 (frozen and signed),
#: ``qbx.hebrew.gematria.GEMATRIA`` and ``Gematria.standard`` in Lean -- which values the
#: final forms 500-900 (decision GEM-001, ``agents/memory/decision_log.md``).
FINAL_FORMS = (("ך", "כ", "final kaf", 500), ("ם", "מ", "final mem", 600),
               ("ן", "נ", "final nun", 700), ("ף", "פ", "final pe", 800),
               ("ץ", "צ", "final tsade", 900))
FINAL_BASE = {f: b for f, b, _, _ in FINAL_FORMS}
for _f, _b, _name, _v in FINAL_FORMS:
    # A final form is its base letter (same position, sound and, untabulated, glyph
    # features) with its own glyph, name and value.
    _base = LOOKUP[_b]
    LOOKUP.setdefault(_f, Letter("hebrew", _base.index,
                                 (_f, _name, _v, _base.ipa, _base.holes, _base.sym)))

#: Gematria conventions: "standard" (finals 500-900, the project default) and
#: "hechrachi" (strict mispar hechrachi: a final form counts as its base letter).
CONVENTIONS = ("standard", "hechrachi")


def value_of(ch, convention="standard"):
    """Letter value of a character under a named convention, or None if untabulated."""
    if convention not in CONVENTIONS:
        raise ValueError(f"unknown gematria convention {convention!r}; use one of {CONVENTIONS}")
    if convention == "hechrachi":
        ch = FINAL_BASE.get(ch, ch)
    l = LOOKUP.get(ch)
    return None if l is None else l.value


def letter_of(ch):
    """The tabulated letter for a character (case- and final-form-insensitive), or None."""
    return LOOKUP.get(ch)


def symmetry_closed(sym):
    """A set of glyph symmetries is a subgroup of the Klein four-group iff any two of
    V, H, R force the third."""
    s = set(sym)
    return len(s & set("VHR")) != 2


def nearest(letter, alphabet):
    """(distance, letters) of `alphabet` whose sound is nearest to `letter`'s."""
    ls = letters(alphabet)
    best = min(hamming(letter.sound, m.sound) for m in ls)
    return best, [m for m in ls if hamming(letter.sound, m.sound) == best]


def transliterate(text, target):
    """Map each tabulated letter to the nearest-sounding letter of `target` (ties
    broken by alphabet order); other characters pass through unchanged."""
    out = []
    for ch in text:
        l = letter_of(ch)
        out.append(ch if l is None else nearest(l, target)[1][0].glyph)
    return "".join(out)


def homophones(alphabet):
    """Groups of letters of one alphabet with identical sound features."""
    groups = {}
    for l in letters(alphabet):
        groups.setdefault(l.sound, []).append(l.glyph)
    return [g for g in groups.values() if len(g) > 1]


# Lineage pairs Hebrew -> Greek (both alphabets descend from the Phoenician one).
LINEAGE_HE_GR = [("א", "Α"), ("ב", "Β"), ("ג", "Γ"), ("ד", "Δ"), ("ה", "Ε"), ("ז", "Ζ"),
                 ("ח", "Η"), ("ט", "Θ"), ("י", "Ι"), ("כ", "Κ"), ("ל", "Λ"), ("מ", "Μ"),
                 ("נ", "Ν"), ("ס", "Ξ"), ("ע", "Ο"), ("פ", "Π"), ("ר", "Ρ"), ("ש", "Σ"),
                 ("ת", "Τ")]


def lineage_distances():
    """Sound distance across each Hebrew-Greek lineage pair."""
    return [(h, g, hamming(LOOKUP[h].sound, LOOKUP[g].sound)) for h, g in LINEAGE_HE_GR]
