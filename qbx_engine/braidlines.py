"""Alphabets running along braid lines.

k texts -- in the same or different alphabets -- are k strands.  At step t each
strand stands at a height on a common circle:

  written height  (index of the letter in its alphabet) / (size of the alphabet)
  spoken height   position of the letter's sound in the common sound order
                  (sound blades sorted as integers; the same order for every
                  alphabet, so different alphabets share one coordinate)

Characters that are not tabulated letters keep the strand at its previous
height.  Between consecutive steps the strands are re-sorted by height (ties
broken by strand number) with adjacent swaps; each swap of the strands in
positions j, j+1 is the braid generator sigma_{j+1}, with exponent +1 when the
strand moving up has the larger sound grade (more articulatory features), and
-1 otherwise.  This crossing-sign rule is a convention of this module.

The braid word is then read by the six channels of `qbx_micro.braid`
(permutation, closure components and linking numbers, Burau, harmonic,
Clifford rotor), whose facts are proved in Lean.  Two consequences that hold
for any crossing-sign rule:

  * the permutation of the braid only depends on the first and last heights;
  * concatenating two texts multiplies their braids (Lean: `braid_word`, the
    word-to-braid map is a monoid homomorphism).
"""

from . import alphabets

try:
    from qbx_micro import braid as _braid
except ImportError:  # pragma: no cover
    _braid = None

_SOUND_ORDER = sorted({m for m in alphabets.S.values()})
_SOUND_RANK = {m: i for i, m in enumerate(_SOUND_ORDER)}


def height(letter, mode):
    if mode == "written":
        return letter.index / len(alphabets.ALPHABETS[letter.alphabet])
    return _SOUND_RANK[letter.sound] / len(_SOUND_ORDER)


def strand_paths(texts, mode="written"):
    """Heights and grades of every strand at every step (texts padded by holding)."""
    T = max(len(t) for t in texts)
    paths = []
    for s, text in enumerate(texts):
        h, g = s * 1e-9, 0
        path = []
        for t in range(T):
            ch = text[t] if t < len(text) else None
            l = alphabets.letter_of(ch) if ch else None
            if l is not None:
                h, g = height(l, mode), alphabets.popcount(l.sound)
            path.append((h, g))
        paths.append(path)
    return paths


def braid_word(texts, mode="written"):
    """The braid word (list of signed generator indices) traced by the texts."""
    paths = strand_paths(texts, mode)
    k = len(texts)
    order = sorted(range(k), key=lambda s: (paths[s][0][0], s))
    word = []
    for t in range(1, len(paths[0])):
        key = {s: (paths[s][t][0], s) for s in range(k)}
        changed = True
        while changed:
            changed = False
            for j in range(k - 1):
                lo, hi = order[j], order[j + 1]
                if key[lo] > key[hi]:
                    # strand `lo` moves up past `hi`
                    up_grade, down_grade = paths[lo][t][1], paths[hi][t][1]
                    word.append((j + 1) if up_grade > down_grade else -(j + 1))
                    order[j], order[j + 1] = hi, lo
                    changed = True
    return word, order


def read(texts, mode="written"):
    word, order = braid_word(texts, mode)
    k = len(texts)
    out = {"strands": k, "mode": mode, "word": word, "final_order": order}
    if _braid is not None and k >= 2:
        out["fold"] = _braid.fold(k, word)
        out["link"] = _braid.link(k, word)
        out["writhe"] = _braid.writhe(word)
        out["integrity"] = _braid.integrity(k, word)
    return out
