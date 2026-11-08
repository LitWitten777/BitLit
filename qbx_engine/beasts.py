"""The four beasts: Lion, Ox, Man, Eagle as the four characters of the Klein four-group.

The rows of the 4 x 4 Hadamard matrix (the project's `BEAST_VECTORS`, first four slots)

    LION   ( 1,  1,  1,  1)
    OX     ( 1, -1,  1, -1)
    MAN    ( 1,  1, -1, -1)
    EAGLE  ( 1, -1, -1,  1)

are the four characters of the Klein four-group V = {id, V, H, R} (index k read as
two bits, the product is bitwise xor).  The same group is the symmetry group of a
glyph (V = left-right mirror, H = top-bottom mirror, R = half turn), so the beasts
can be read off every letter of every alphabet.  Lean
(`QBX/Formal/Engine/Controls.lean`):

  beast_orthogonal   H H^T = 4 I          (the four directions are orthogonal)
  beast_inverse      H^T (H x) = 4 x      (exact recovery of a 4-vector)
  beast_character    beast_i(k xor l) = beast_i(k) beast_i(l)
  beast_closed       beast_i * beast_j = beast_(i xor j)   (Ox * Man = Eagle, ...)
"""

NAMES = ("LION", "OX", "MAN", "EAGLE")
H = (
    (1, 1, 1, 1),
    (1, -1, 1, -1),
    (1, 1, -1, -1),
    (1, -1, -1, 1),
)
# Klein four-group elements in index order; the glyph symmetry of each index.
KLEIN = ("id", "V", "H", "R")
SYM_INDEX = {"V": 1, "H": 2, "R": 3}
# Elements / directions conventionally attached to the beasts in the project's sources.
ELEMENT = {"LION": "fire", "OX": "earth", "MAN": "water", "EAGLE": "air"}
COLOUR = {"LION": "#e8a33d", "OX": "#7a8b3a", "MAN": "#3d7be8", "EAGLE": "#c9d6ea"}


def transform(x):
    """Beast components of a 4-vector: (H x)_i."""
    return [sum(H[i][k] * x[k] for k in range(4)) for i in range(4)]


def inverse(y):
    """Recover the 4-vector from its beast components: x = H^T y / 4 (exact on integers)."""
    s = [sum(H[i][k] * y[i] for i in range(4)) for k in range(4)]
    assert all(v % 4 == 0 for v in s), "not the transform of an integer vector"
    return [v // 4 for v in s]


def kmul(i, j):
    return i ^ j


def trivial_on(sym):
    """The beasts that are trivial on a glyph's symmetry group (the dual subgroup).
    Its size is 4 / |symmetry group|."""
    ks = [0] + [SYM_INDEX[c] for c in sym]
    return [NAMES[i] for i in range(4) if all(H[i][k] == 1 for k in ks)]


def checks():
    ok = {}
    ok["orthogonal"] = all(sum(H[i][k] * H[j][k] for k in range(4)) == (4 if i == j else 0)
                           for i in range(4) for j in range(4))
    ok["character"] = all(H[i][kmul(k, l)] == H[i][k] * H[i][l]
                          for i in range(4) for k in range(4) for l in range(4))
    ok["closed"] = all(H[i][k] * H[j][k] == H[kmul(i, j)][k]
                       for i in range(4) for j in range(4) for k in range(4))
    ok["inverse"] = all(inverse(transform(x)) == x
                        for x in ([1, 0, 0, 0], [0, 1, 0, 0], [3, -1, 4, 1], [2, 7, 1, 8]))
    return ok


def letter_vector(letter):
    """A 4-vector of counts read from a letter's spoken features, one entry per feature
    family: place, manner, laryngeal/secondary, vowel quality.  (Convention of this module.)"""
    from . import alphabets
    fs = set(alphabets.features(letter.sound))
    fam = (alphabets.FEATURES[0:5], alphabets.FEATURES[5:13], alphabets.FEATURES[13:17],
           alphabets.FEATURES[17:22])
    return [len(fs & set(f)) for f in fam]


def letter_beasts(letter):
    v = letter_vector(letter)
    comps = transform(v)
    dominant = NAMES[max(range(1, 4), key=lambda i: (abs(comps[i]), -i))]
    return {"feature_families": v, "components": dict(zip(NAMES, comps)),
            "dominant": dominant, "trivial_on_glyph": trivial_on(letter.sym)}
