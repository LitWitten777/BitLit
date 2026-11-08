"""The one-line map of the whole structure, as data.

Every entry of a `.qbx` program lands in exactly one of these layers, so a certificate always
says what *kind* of statement it carries: a fact about the model, a convention (a labelling
choice), a calibration against the documents, or an interpretation (carried, never proved).
"""

LAYERS = [
    # (layer, what it is, examples, where it is proved / computed)
    ("model", "Q6: 64 cells, 192 edges, 240 squares, bipartite, shells 1,6,15,20,15,6,1 from any cell",
     "cells, distances, faces", "RequestProject/Q6Structure.lean"),
    ("boundary", "the boundary of Q6 is a 5-sphere: Euler characteristic 0 = 1 - (-1)^6; "
     "harmonic extension boundary -> interior", "holographic boundary, Dirichlet principle",
     "Q6Structure.boundary_euler_char; sovereign/ (Dirichlet)"),
    ("symmetry", "W(B6) = Z2^6 x| S6 (46,080 isometries); the B6 braid action; parity law; "
     "transitivity in at most 6 letters", "braid walks, writhe, permutation, braid inequality",
     "Q6Structure.braid_*, QBXCheck.domeAction"),
    ("comparison", "objects the model is NOT: E8, E8^3, Leech, Gosset 4_21, torus C4^3",
     "240 squares vs 240 E8 roots (a count coincidence)", "sovereign/.../HypercubeLattices.lean"),
    ("convention", "labels on the 64 cells: codon, hexagram, tone, colour, chapter, tribe",
     "one labelling among 64! possible; carries no evidence by itself", "hypercube/cells.py"),
    ("calibration", "numbers recomputed from the documents: gematria totals, Hebrew calendar, "
     "factorions, nets, MOG", "gematria(...) == N", "calibration ledger; QBXCheck.gematria"),
    ("geodesy", "unrelated fix: WGS84 ellipsoid in the eclipse engine",
     "observer positions, eclipse-path edges", "hypercube/eclipses.py"),
    ("interpretation", "readings (Logos, Christ/antichrist, Lilith, Adam Kadmon, ...) that cite "
     "checks as support; recorded, never proved", "interpret blocks", "not proved by design"),
]

_SYMMETRY_FNS = {"walk", "cell", "parity", "writhe", "perm", "burau", "length", "concat", "inverse"}


def layer_of(fn, lv, rv):
    if fn == "gematria":
        return "calibration"
    if fn == "dist":
        return "model"
    if fn in _SYMMETRY_FNS:
        return "symmetry"
    if isinstance(lv, object) and type(lv).__name__ == "Braid":
        return "symmetry"
    return "model"


def table():
    w = max(len(l[0]) for l in LAYERS)
    lines = []
    for name, what, ex, where in LAYERS:
        lines.append(f"{name:<{w}}  {what}\n{'':<{w}}  e.g. {ex}\n{'':<{w}}  -> {where}")
    return "\n".join(lines)
