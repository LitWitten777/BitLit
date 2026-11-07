"""Stage 3: crystals, circuits, Cayley-Dickson cocycles, topology, sky braids.

Python 3 standard library only.  Every exact statement printed here that is marked "(Lean)" is
proved in `sovereign/Sovereign/Organism/HypercubeCrystals.lean`; everything else is computed
(exact rational arithmetic where it says so, floating point for the ephemeris) and tested, not
proved.  Write-up: `docs/HYPERCUBE_CROSSDOMAIN_2026-10-23.md`.

Conventions match the Lean file and `cells.py`:
  * codon c in 0..63 = 16*b1 + 4*b2 + b3 with U=0, C=1, A=2, G=3 (TCAG table order);
  * crystal letters: colour i acts on letters i ("+") and i+1 ("-"); signature rule with
    "i+1 then i" pairs cancelling; f lowers the rightmost unpaired i, e raises the leftmost
    unpaired i+1;
  * nucleotide labels of Frappat-Sciarrino-Sorba: C=(+,+), U=(-,+), G=(+,-), A=(-,-).
"""
import math
from fractions import Fraction as Fr
from itertools import product
from math import comb

CODE = "FFLLSSSSYY**CC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"
BASES = "UCAG"


def codon_name(c):
    return "".join(BASES[c // 4 ** (2 - p) % 4] for p in range(3))


def base(p, c):
    return c // 4 ** (2 - p) % 4


# ============================================================== 1. crystals
def _scan(w, i):
    un0, opens = [], []
    for p, x in enumerate(w):
        if x == i + 1:
            opens.append(p)
        elif x == i:
            if opens:
                opens.pop()
            else:
                un0.append(p)
    return un0, opens


def ftil(w, i):
    u0, _ = _scan(w, i)
    if not u0:
        return None
    w = list(w)
    w[u0[-1]] = i + 1
    return tuple(w)


def etil(w, i):
    _, u1 = _scan(w, i)
    if not u1:
        return None
    w = list(w)
    w[u1[0]] = i
    return tuple(w)


def highest(w, colours):
    while True:
        for i in colours:
            v = etil(w, i)
            if v is not None:
                w = v
                break
        else:
            return w


def crystal_components(n_letters, length):
    """Components of B(box)^{tensor length} for sl(n_letters): {highest word: [members]}."""
    cols = range(n_letters - 1)
    comps = {}
    for w in product(range(n_letters), repeat=length):
        comps.setdefault(highest(w, cols), []).append(w)
    return comps


def codon_words(c):
    """(H, V) letter words of a codon (FSS labels)."""
    return (tuple(1 - base(p, c) % 2 for p in range(3)), tuple(base(p, c) // 2 for p in range(3)))


def codon_from_words(h, v):
    return sum((2 * v[p] + 1 - h[p]) * 4 ** (2 - p) for p in range(3))


def codon_crystal():
    """The sl(2)+sl(2) crystal on the 64 codons: components, arrows, amino acids."""
    comps = {}
    arrows = []
    for c in range(64):
        h, v = codon_words(c)
        comps.setdefault((highest(h, [0]), highest(v, [0])), []).append(c)
        fh, fv = ftil(h, 0), ftil(v, 0)
        if fh is not None:
            arrows.append((c, codon_from_words(fh, v), "H"))
        if fv is not None:
            arrows.append((c, codon_from_words(h, fv), "V"))
    return comps, arrows


def two_spin(w):
    hw = highest(w, [0])
    return hw.count(0) - hw.count(1)


def two_wt(w):
    return w.count(0) - w.count(1)


def reading_labels(c):
    out = []
    for w in codon_words(c):
        j, j12 = two_spin(w), two_spin(w[:2])
        out += [j * (j + 2), j12 * (j12 + 2), two_wt(w), two_wt(w[2:])]
    return out


def _rank(rows):
    rows = [list(map(Fr, r)) for r in rows]
    rank, col, ncol = 0, 0, len(rows[0]) if rows else 0
    while rank < len(rows) and col < ncol:
        piv = next((r for r in range(rank, len(rows)) if rows[r][col] != 0), None)
        if piv is None:
            col += 1
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for r in range(len(rows)):
            if r != rank and rows[r][col] != 0:
                f = rows[r][col] / rows[rank][col]
                rows[r] = [a - f * b for a, b in zip(rows[r], rows[rank])]
        rank += 1
        col += 1
    return rank


def reading_operator_test():
    """Can the amino acid be read off crystal labels?"""
    by_spin = {}
    for c in range(64):
        h, v = codon_words(c)
        by_spin.setdefault((two_spin(h), two_spin(v), two_wt(h), two_wt(v)), set()).add(CODE[c])
    collisions = sum(1 for s in by_spin.values() if len(s) > 1)
    diffs = []
    groups = {}
    for c in range(64):
        groups.setdefault(CODE[c], []).append(c)
    for cs in groups.values():
        for c in cs[1:]:
            diffs.append([a - b for a, b in zip(reading_labels(c), reading_labels(cs[0]))])
    r = _rank(diffs)
    labels = {tuple(reading_labels(c)) for c in range(64)}
    return {
        "spin_weight_classes": len(by_spin),
        "spin_weight_classes_with_two_or_more_amino_acids": collisions,
        "eight_labels_distinguish_all_64_codons": len(labels) == 64,
        "rank_of_synonymy_constraints_on_linear_operator": r,
        "linear_operators_constant_on_synonyms_dimension": 8 - r,
        "verdict": ("total spins+weights cannot be a reading operator; the eight labels "
                    "determine the codon, so SOME function reads the code, but a LINEAR one in "
                    "these labels cannot (Lean: no_linear_reading_operator)"),
    }


# ============================================================== 2. circuits
def cube_nbrs(n):
    return lambda u: [u ^ (1 << i) for i in range(n)]


def codon_nbrs(u):
    out = []
    for p in range(3):
        sh = 4 ** (2 - p)
        b = base(p, u)
        for o in (1, 2, 3):
            out.append(u - b * sh + ((b + o) % 4) * sh)
    return out


def effective_resistance(N, nbrs, s, t):
    """Exact (Fraction) effective resistance with unit resistors, by Kirchhoff's laws."""
    idx = [i for i in range(N) if i != t]
    pos = {v: k for k, v in enumerate(idx)}
    n = len(idx)
    A = [[Fr(0)] * (n + 1) for _ in range(n)]
    for u in idx:
        r = pos[u]
        for v in nbrs(u):
            A[r][r] += 1
            if v != t:
                A[r][pos[v]] -= 1
        A[r][n] = Fr(1 if u == s else 0)
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return A[pos[s]][n] if s != t else Fr(0)


def det_fraction(M):
    M = [list(map(Fr, r)) for r in M]
    n, d = len(M), Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f:
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return d


def spanning_trees(N, nbrs):
    """Kirchhoff's matrix-tree theorem: a cofactor of the Laplacian."""
    L = [[0] * N for _ in range(N)]
    for u in range(N):
        for v in nbrs(u):
            L[u][v] -= 1
            L[u][u] += 1
    return int(det_fraction([row[1:] for row in L[1:]]))


def synonymous_pieces():
    seen, pieces = set(), []
    for c in range(64):
        if c in seen:
            continue
        piece, stack = {c}, [c]
        while stack:
            u = stack.pop()
            for v in codon_nbrs(u):
                if CODE[v] == CODE[u] and v not in piece:
                    piece.add(v)
                    stack.append(v)
        seen |= piece
        pieces.append(sorted(piece))
    return pieces


def circuit_report():
    q6 = cube_nbrs(6)
    anti_formula = sum(Fr(1, k * comb(6, k)) for k in range(1, 7))
    pieces = synonymous_pieces()
    by_aa = {}
    for p in pieces:
        by_aa.setdefault(CODE[p[0]], []).append(["".join(codon_name(c)) for c in p])
    tau_formula = 2 ** (2 ** 6 - 6 - 1) * math.prod(k ** comb(6, k) for k in range(1, 7))
    return {
        "Q6_antipodal_resistance (Lean)": str(effective_resistance(64, q6, 0, 63)),
        "Q6_antipodal_shell_series_formula": str(anti_formula),
        "Q6_adjacent_resistance (Lean)": str(effective_resistance(64, q6, 0, 1)),
        "codon_graph_adjacent_resistance (Lean)": str(effective_resistance(64, codon_nbrs, 0, 1)),
        "codon_graph_far_resistance UUU-GGG (Lean)": str(effective_resistance(64, codon_nbrs, 0, 63)),
        "Q6_edges": 192, "codon_graph_edges": 288,
        "Q6_spanning_trees_matrix_tree": spanning_trees(64, q6),
        "Q6_spanning_trees_closed_formula": tau_formula,
        "synonymous_pieces": len(pieces),
        "amino_acids_in_more_than_one_piece": {a: v for a, v in by_aa.items() if len(v) > 1},
    }


# ============================================================== particles (empirical)
# Isospin-averaged baryon masses in MeV (PDG, rounded); used only for the mass-formula check.
OCTET = {"N": 938.9, "Lambda": 1115.7, "Sigma": 1193.2, "Xi": 1318.3}
DECUPLET = {"Delta": 1232.0, "Sigma*": 1384.6, "Xi*": 1533.4, "Omega": 1672.5}


def particle_report():
    comps = crystal_components(3, 3)
    sizes = sorted((len(v) for v in comps.values()), reverse=True)
    lhs = 2 * (OCTET["N"] + OCTET["Xi"])
    rhs = 3 * OCTET["Lambda"] + OCTET["Sigma"]
    d = list(DECUPLET.values())
    return {
        "sl3_crystal_component_sizes (Lean)": sizes,
        "singlet_word": "s d u (isolated vertex, weight 0) (Lean)",
        "Gell-Mann-Okubo octet 2(N+Xi) vs 3Lambda+Sigma (MeV)": [round(lhs, 1), round(rhs, 1),
                                                                   f"{100 * (rhs - lhs) / rhs:.2f}%"],
        "decuplet equal-spacing rule (MeV)": [round(b - a, 1) for a, b in zip(d, d[1:])],
        "note": "masses are measured inputs; the crystal fixes multiplet structure only, not masses",
    }


# ============================================================== 4. Cayley-Dickson cocycles
def cd_sign(n, a, b):
    if n == 0:
        return 1
    h = 1 << (n - 1)
    a0, a1, b0, b1 = a & (h - 1), a >> (n - 1), b & (h - 1), b >> (n - 1)
    cj = 1 if b0 == 0 else -1
    if not a1 and not b1:
        return cd_sign(n - 1, a0, b0)
    if not a1:
        return cd_sign(n - 1, b0, a0)
    if not b1:
        return cd_sign(n - 1, a0, b0) * cj
    return -cj * cd_sign(n - 1, b0, a0)


def cocycle_report(max_n=5):
    out = {}
    for n in range(1, max_n + 1):
        N = 1 << n
        F = lambda a, b: cd_sign(n, a, b)
        braid_rule = all((F(a, b) * F(b, a) == -1) == (a != b and a != 0 and b != 0)
                         for a in range(N) for b in range(N))
        indep = neg = indep_assoc = 0
        for a, b, c in product(range(N), repeat=3):
            ind = a and b and c and a != b and a != c and b != c and a ^ b != c
            phi = F(a, b) * F(a ^ b, c) * F(b, c) * F(a, b ^ c)
            indep += bool(ind)
            neg += phi == -1
            indep_assoc += bool(ind) and phi == 1
        out[f"dim {N}"] = {"braiding = -1 iff distinct nonzero": braid_rule,
                           "independent triples": indep, "non-associative triples": neg,
                           "independent but associative": indep_assoc}
    return out


# ============================================================== 5. topology
def cube_faces(n):
    """Faces of Q_n: (free direction mask S, base vertex with zero bits on S)."""
    return [(S, v) for S in range(1 << n) for v in range(1 << n) if v & S == 0]


def _boundary_rows_gf2(n, k, idx_lower):
    rows = []
    for S, v in cube_faces(n):
        if bin(S).count("1") != k:
            continue
        mask = 0
        for i in range(n):
            if S >> i & 1:
                T = S & ~(1 << i)
                mask ^= 1 << idx_lower[(T, v)]
                mask ^= 1 << idx_lower[(T, v | (1 << i))]
        rows.append(mask)
    return rows


def _rank_gf2(rows):
    rank, basis = 0, {}
    for r in rows:
        while r:
            hb = r.bit_length() - 1
            if hb in basis:
                r ^= basis[hb]
            else:
                basis[hb] = r
                rank += 1
                break
    return rank


def cube_homology_gf2(n, boundary_only=False):
    """Betti numbers over GF(2) of Q_n (or of its boundary sphere)."""
    faces = cube_faces(n)
    top = n - 1 if boundary_only else n
    by_dim = {k: [f for f in faces if bin(f[0]).count("1") == k] for k in range(top + 1)}
    idx = {k: {f: i for i, f in enumerate(by_dim[k])} for k in by_dim}
    ranks = {0: 0}
    for k in range(1, top + 1):
        ranks[k] = _rank_gf2(_boundary_rows_gf2(n, k, idx[k - 1]))
    ranks[top + 1] = 0
    return [len(by_dim[k]) - ranks[k] - ranks[k + 1] for k in range(top + 1)]


SKY_BODIES = ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn"]


def sky_braid_windings(jd_from, jd_to, step_days=2.0, bodies=SKY_BODIES, eph=None):
    """Heliocentric ecliptic longitudes as strands of a braid in the solid torus (annulus x time).

    The pairwise linking (winding) number over the window is the number of full relative laps,
    i.e. the number of heliocentric conjunctions; it is an isotopy invariant of the closed braid
    when the configuration returns.  Floating point (DE441), not proved.
    """
    from . import sky
    eph = eph or sky.default_ephemeris()
    lon = {b: [] for b in bodies}
    t = jd_from
    while t <= jd_to + 1e-9:
        for b in bodies:
            lon[b].append(sky.lonlat(eph.helio(b, t))[0])
        t += step_days
    unwrapped = {}
    for b, xs in lon.items():
        acc, out = 0.0, [xs[0]]
        for x0, x1 in zip(xs, xs[1:]):
            d = (x1 - x0 + 180) % 360 - 180
            acc += d
            out.append(xs[0] + acc)
        unwrapped[b] = out
    laps = {b: (u[-1] - u[0]) / 360 for b, u in unwrapped.items()}
    pairs = {}
    for i, a in enumerate(bodies):
        for b in bodies[i + 1:]:
            pairs[f"{a}-{b}"] = round(laps[a] - laps[b], 3)
    return {"laps": {b: round(v, 3) for b, v in laps.items()}, "pair_windings": pairs}


def topology_report(with_sky=True):
    out = {
        "Q_n Euler characteristic = 1 for every n (Lean)": [
            sum((-1) ** k * comb(n, k) * 2 ** (n - k) for k in range(n + 1)) for n in range(1, 9)],
        "Q6 face counts (Lean)": [comb(6, k) * 2 ** (6 - k) for k in range(7)],
        "Q4 Betti numbers GF(2)": cube_homology_gf2(4),
        "boundary of Q4 (= S^3) Betti numbers GF(2)": cube_homology_gf2(4, True),
        "boundary of Q6 (= S^5) Betti numbers GF(2)": cube_homology_gf2(6, True),
        "Saros windings (synodic, anomalistic, draconic) pairwise coprime (Lean)": [223, 239, 242],
    }
    if with_sky:
        from .timescale import jd_from_calendar
        j0 = jd_from_calendar(2000, 1, 1)
        out["sky braid 2000-2008 (Venus 8-year cycle)"] = sky_braid_windings(j0, j0 + 8 * 365.25)
    return out


# ============================================================== simple visual
def crystal_svg(path):
    """The codon crystal graph: 9 components, arrows H (red) and V (blue), labels = amino acid."""
    comps, arrows = codon_crystal()
    pos = {}
    order = sorted(comps.items(), key=lambda kv: -len(kv[1]))
    x0 = 20
    for (hw, members) in order:
        cols = {}
        for c in members:
            h, v = codon_words(c)
            cols.setdefault(two_wt(h), []).append((two_wt(v), c))
        xs = sorted(cols, reverse=True)
        for xi, wh in enumerate(xs):
            for wv, c in cols[wh]:
                pos[c] = (x0 + 40 * xi, 60 + 40 * (3 - wv))
        x0 += 40 * len(xs) + 50
    W = x0
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="340" font-family="monospace" font-size="10">',
           '<rect width="100%" height="100%" fill="white"/>',
           '<text x="10" y="20" font-size="13">Codon crystal of U_q(sl2+sl2) at q=0 (FSS labels): '
           '9 components; red = f_H, blue = f_V</text>']
    for a, b, k in arrows:
        (x1, y1), (x2, y2) = pos[a], pos[b]
        out.append(f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{"#c33" if k == "H" else "#36c"}" stroke-width="1.5"/>')
    for c, (x, y) in pos.items():
        out.append(f'<circle cx="{x}" cy="{y}" r="13" fill="#f6f6f6" stroke="#444"/>')
        out.append(f'<text x="{x}" y="{y - 1}" text-anchor="middle">{codon_name(c)}</text>')
        out.append(f'<text x="{x}" y="{y + 9}" text-anchor="middle" fill="#070">{CODE[c]}</text>')
    out.append("</svg>")
    with open(path, "w") as f:
        f.write("\n".join(out))
    return path


def report(with_sky=True):
    comps, arrows = codon_crystal()
    sl3 = crystal_components(3, 3)
    return {
        "crystal": {
            "sl3 components (u,d,s) sizes (Lean)": sorted((len(v) for v in sl3.values()), reverse=True),
            "codon components sizes (Lean)": sorted((len(v) for v in comps.values()), reverse=True),
            "codon crystal arrows": len(arrows),
            "AAU, AUA, UAA in different components (Lean)": len({
                next(k for k, v in comps.items() if c in v) for c in (40, 34, 10)}) == 3,
            "components and their amino acids": [
                "".join(sorted({CODE[c] for c in v})) for _, v in sorted(comps.items(), key=lambda kv: -len(kv[1]))],
            "reading operator": reading_operator_test(),
        },
        "circuits": circuit_report(),
        "particles": particle_report(),
        "cayley_dickson": cocycle_report(),
        "topology": topology_report(with_sky),
    }
