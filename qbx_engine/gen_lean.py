"""Generate the Lean alphabet tables of `QBX/Formal/Engine/AlphabetGeometry.lean`
from `alphabets.py` (the single source of the data)."""

from . import alphabets


def _row(l):
    sym = l.sym
    return ('  ⟨"%s", "%s", %d, "%s", %d, %s, %s, %s, %d⟩' % (
        l.glyph, l.name, l.value, l.ipa, l.holes,
        "true" if "V" in sym else "false", "true" if "H" in sym else "false",
        "true" if "R" in sym else "false", l.sound))


def lean_tables():
    out = []
    for a in ("hebrew", "greek", "latin"):
        out.append("/-- The %s alphabet (generated from `qbx_engine/alphabets.py`). -/" % a.capitalize())
        out.append("def %s : List Letter := [" % a)
        out.append(",\n".join(_row(l) for l in alphabets.letters(a)))
        out.append("]\n")
    return "\n".join(out)


if __name__ == "__main__":
    print(lean_tables())
