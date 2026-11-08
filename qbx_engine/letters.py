"""Letter details: one card per letter, joining every reading the engine has.

For a letter of the Hebrew, Greek or Latin table the card gives

  identity     alphabet, position, glyph, name, number, sound (IPA)
  written      holes, glyph symmetries (a subgroup of the Klein four-group
               {id, V, H, R}), and the beasts trivial on that subgroup
  spoken       the 22 articulatory features, blade, grade
  beasts       the beast components of the feature-family counts (Hadamard
               transform, exactly invertible: `beast_inverse`)
  harmonic     harmonic number = letter value, frequency, pitch class, torus node
               (`harmonicMap`, bijective on a coprime torus)
  braid        height of the letter on the written and on the spoken braid line
  relations    nearest-sounding letters of the other alphabets, Phoenician-lineage
               partner, homophones in its own alphabet
"""

from . import alphabets, beasts, braidlines, harmonic


def _lineage_partner(l):
    for h, g in alphabets.LINEAGE_HE_GR:
        if l.glyph == h:
            return {"greek": g}
        if l.glyph == g:
            return {"hebrew": h}
    return {}


def card(ch, N=16, M=25):
    l = alphabets.letter_of(ch)
    if l is None:
        return None
    d = l.as_dict()
    d["written"]["beasts_trivial_on_symmetry"] = beasts.trivial_on(l.sym)
    d["beasts"] = beasts.letter_beasts(l)
    d["harmonic"] = harmonic.letter_harmonics(l, N, M)
    d["braid"] = {"written_height": round(braidlines.height(l, "written"), 6),
                  "spoken_height": round(braidlines.height(l, "spoken"), 6)}
    rel = {"nearest": {}, "lineage": _lineage_partner(l), "homophones": []}
    for a in alphabets.ALPHABETS:
        if a != l.alphabet:
            dist, ms = alphabets.nearest(l, a)
            rel["nearest"][a] = {"distance": dist, "letters": [m.glyph for m in ms]}
    for g in alphabets.homophones(l.alphabet):
        if l.glyph in g:
            rel["homophones"] = [x for x in g if x != l.glyph]
    d["relations"] = rel
    return d


def cards(text, N=16, M=25):
    out = []
    for ch in text:
        c = card(ch, N, M)
        if c is not None:
            out.append(c)
    return out


def alphabet_cards(name, N=16, M=25):
    return [card(l.glyph, N, M) for l in alphabets.letters(name)]
