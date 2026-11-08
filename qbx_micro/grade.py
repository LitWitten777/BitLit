"""Grade a theorem library through the six channels.

Input: a theorem-graph export (`theorem-graph/data/<lib>/decls.jsonl.gz`), i.e. the
fully elaborated statement of every declaration as an AST.  Each statement is
turned into a braid by the structural encoder of `QBX/Formal/StructuralBraid.lean`
(mirrored in `encode`), and the braid is read in all six channels.

What the scores measure, and what they do not:

* They are invariants of the *shape of the statement*, computed from the braid.
  They say nothing about whether the statement is true: the export only contains
  declarations that Lean already checked, and a score cannot replace that check.
* `class_size` counts declarations with exactly the same six readings.  Equal
  statements (up to binder names, `encode_eraseBinders`) always share a class; a
  class that contains different statements is an encoder or channel collision.
* `entropy` is the Burau lower bound for the topological entropy of the braid
  (a dynamical complexity measure of the statement's braid, not of its proof).
* `integrity` re-derives Lean-proved identities (`braid.integrity`); all must
  hold, a failure flags a corrupted computation.
* Graph scores come from the premise data in the export: `used_by` (how many
  proofs in the library use the declaration), `uses` (its own proof premises),
  `height` (longest chain of proof premises inside the library).

Desktop tool (CPython): uses gzip/json/multiprocessing for the corpus; the
per-statement work is done by the MicroPython-compatible modules.
"""

import gzip
import hashlib
import json
import math
import sys
from collections import Counter, defaultdict

from . import braid as B

STRANDS = 4          # m + 2 with m = 2: generator indices taken mod 3
OSC_LEVELS = (5, 7)  # r for the exact (mod p) oscillator (r = 3, 4, 6 give classical, coarse values)


# ----------------------------------------------------------------------------- encoder

def fnv1a(s):
    h = 0x811C9DC5
    for byte in s.encode("utf-8"):
        h = ((h ^ byte) * 0x01000193) & 0xFFFFFFFF
    return h


def to_sexpr(ast):
    """Export AST -> the `SExpr` constructors of StructuralBraid.lean.

    `let x := v; b` becomes `(fun x => b) v`, a projection `S.i e` becomes the
    application of the constant `S.i` to `e`, string literals and non-numeric
    universe levels are hashed to numbers, a truncated subtree is the constant
    `trunc`.  After this translation the Lean theorems about `encode` apply.
    """
    tag = ast[0]
    if tag in ("pi", "lam"):
        return (tag, to_sexpr(ast[3]), to_sexpr(ast[4]))
    if tag == "let":
        return ("app", ("lam", to_sexpr(ast[2]), to_sexpr(ast[4])), to_sexpr(ast[3]))
    if tag == "app":
        node = to_sexpr(ast[1])
        for a in ast[2:]:
            node = ("app", node, to_sexpr(a))
        return node
    if tag == "const":
        return ("const", ast[1])
    if tag == "bvar":
        return ("bvar", ast[1])
    if tag == "sort":
        lvl = str(ast[1])
        return ("sort", int(lvl) if lvl.isdigit() else fnv1a(lvl))
    if tag == "nat":
        return ("lit", int(ast[1]))
    if tag == "str":
        return ("lit", fnv1a(ast[1]))
    if tag == "proj":
        return ("app", ("const", "%s.%s" % (ast[1], ast[2])), to_sexpr(ast[3]))
    return ("const", "trunc")


def encode(e, m=STRANDS - 2):
    """Mirror of `Structural.encode fnv1a m` (closed terms: no free variables)."""
    out = []

    def g(i, pos):
        idx = i % (m + 1) + 1
        out.append(idx if pos else -idx)

    stack = [(e, 0, 0)]  # (node, depth, phase)
    while stack:
        node, d, phase = stack.pop()
        tag = node[0]
        if tag == "emit":
            g(node[1], node[2])
        elif tag == "bvar":
            ell = max(0, d - 1 - node[1])
            g(ell, True)
            g(ell, True)
        elif tag == "const":
            g(fnv1a(node[1]), True)
        elif tag == "sort":
            g(node[1], True)
            g(node[1] + 1, False)
        elif tag == "lit":
            g(node[1], False)
        elif tag == "app":
            stack.append((("emit", 0, True), d, 0))
            stack.append((node[2], d, 0))
            stack.append((node[1], d, 0))
        else:  # lam / pi: enc ty . s_d^{+-1} . enc body (depth d+1) . s_d^{+-1}
            pos = tag == "lam"
            stack.append((("emit", d, pos), d, 0))
            stack.append((node[2], d + 1, 0))
            stack.append((("emit", d, pos), d, 0))
            stack.append((node[1], d, 0))
    return out


# ----------------------------------------------------------------------------- per-statement grade

def _h(x):
    return hashlib.sha256(repr(x).encode()).hexdigest()[:16]


def grade_word(word, n=STRANDS, oscillator=OSC_LEVELS, sweep=B.SWEEP):
    harm = B.harmonic(n, word, sweep)
    osc = tuple(B.oscillator_mod(n, word, r) for r in oscillator)
    ck, cnum = B.clifford_key(n, word)
    readings = {
        "fold": B.fold(n, word),
        "link": B.link(n, word),
        "anchor": _h(B.anchor(n, word)),
        "harmonic": "".join("?" if x is None else ("1" if x else "0") for x in harm),
        "oscillator": osc,
        "clifford": _h((ck, cnum)),
    }
    integ = B.integrity(n, word)
    ent = B.entropy_bound(n, word, sweep)
    ent = 0.0 if ent < 1e-3 else round(ent, 4)
    return {
        "length": len(word),
        "readings": readings,
        "resonance": round(sum(1 for x in harm if x) / len(harm), 4),
        "harmonic_decided": round(sum(1 for x in harm if x is not None) / len(harm), 4),
        "entropy": ent,
        "entropy_per_letter": round(ent / len(word), 5) if word else 0.0,
        "clifford_k": ck,
        "integrity": all(integ.values()),
        "integrity_detail": integ,
    }


def _grade_decl(args):
    x, n = args
    sys.setrecursionlimit(100000)
    word = encode(to_sexpr(x["ast"]), n - 2)
    out = grade_word(word, n)
    out["word"] = _h(word)
    out["name"] = x["name"]
    out["kind"] = x["kind"]
    out["module"] = x["module"]
    out["truncated"] = x["ast_truncated"]
    out["shape"] = _h(_shape(x["ast"]))
    return out


def _shape(ast):
    if not isinstance(ast, list) or not ast:
        return ast
    tag = ast[0]
    if tag in ("pi", "lam"):
        return [tag, _shape(ast[3]), _shape(ast[4])]
    return [tag] + [_shape(a) for a in ast[1:]]


# ----------------------------------------------------------------------------- corpus

def load(paths):
    seen = set()
    for p in paths:
        with gzip.open(p, "rt", encoding="utf-8") as fh:
            for line in fh:
                if line.strip():
                    x = json.loads(line)
                    if x["name"] not in seen:
                        seen.add(x["name"])
                        yield x


def graph_scores(decls):
    names = {x["name"] for x in decls}
    uses = {x["name"]: [u for u in x["proof_uses"] if u in names and u != x["name"]] for x in decls}
    used_by = Counter(u for us in uses.values() for u in set(us))
    height = {}
    for root in uses:
        if root in height:
            continue
        stack = [(root, 0)]
        onpath = set()
        while stack:
            node, state = stack.pop()
            if state == 0:
                if node in height:
                    continue
                onpath.add(node)
                stack.append((node, 1))
                for c in uses[node]:
                    if c not in height and c not in onpath:
                        stack.append((c, 0))
            else:
                onpath.discard(node)
                kids = [height[c] for c in uses[node] if c in height]
                height[node] = 1 + max(kids) if kids else 0
    return {n: {"used_by": used_by.get(n, 0), "uses": len(uses[n]), "height": height.get(n, 0)}
            for n in uses}


def grade_corpus(paths, workers=None, limit=None, n=STRANDS):
    decls = list(load(paths))
    if limit:
        decls = decls[:limit]
    graph = graph_scores(decls)
    if workers == 1:
        rows = [_grade_decl((x, n)) for x in decls]
    else:
        from multiprocessing import Pool
        with Pool(workers) as pool:
            rows = pool.map(_grade_decl, [(x, n) for x in decls], chunksize=16)
    key = lambda r: json.dumps(r["readings"], sort_keys=True)
    classes = defaultdict(list)
    for r in rows:
        classes[key(r)].append(r)
    for r in rows:
        cls = classes[key(r)]
        r["class_size"] = len(cls)
        r["class_shapes"] = len({c["shape"] for c in cls})
        r.update(graph[r["name"]])
    return rows


CHANNELS = ("fold", "link", "anchor", "harmonic", "oscillator", "clifford")


def channel_power(rows):
    """Resolving power of each channel and of channel sets.

    Two denominators: distinct statement shapes (how much of the library the
    whole pipeline separates) and distinct braid words (how much of what the
    encoder hands over the channels separate).  1.0 = separates everything.
    """
    shapes = len({r["shape"] for r in rows})
    words = len({r["word"] for r in rows})
    sets = {c: (c,) for c in CHANNELS}
    sets["all six"] = CHANNELS
    sets["five (no anchor)"] = tuple(c for c in CHANNELS if c != "anchor")
    sets["five (no clifford)"] = tuple(c for c in CHANNELS if c != "clifford")
    out = {}
    for name, cs in sets.items():
        k = len({json.dumps([r["readings"][c] for c in cs]) for r in rows})
        out[name] = {"distinct": k, "per_shape": round(k / shapes, 4), "per_word": round(k / words, 4)}
    return shapes, words, out


def summary(rows):
    thms = [r for r in rows if r["kind"] == "theorem"]
    shapes, words, power = channel_power(rows)
    collisions = [r for r in rows if r["class_shapes"] > 1]
    return {
        "declarations": len(rows),
        "theorems": len(thms),
        "distinct_shapes": shapes,
        "distinct_braid_words": words,
        "channel_resolving_power": power,
        "integrity_failures": sum(1 for r in rows if not r["integrity"]),
        "collision_declarations": len(collisions),
        "mean_entropy": round(sum(r["entropy"] for r in rows) / max(1, len(rows)), 4),
        "mean_resonance": round(sum(r["resonance"] for r in rows) / max(1, len(rows)), 4),
        "top_load_bearing": [(r["name"], r["used_by"]) for r in
                             sorted(thms, key=lambda r: -r["used_by"])[:15]],
        "highest_entropy": [(r["name"], r["entropy"]) for r in
                            sorted(thms, key=lambda r: -r["entropy"])[:10]],
        "deepest": [(r["name"], r["height"]) for r in sorted(thms, key=lambda r: -r["height"])[:10]],
    }


def write_rows(rows, path):
    with gzip.GzipFile(path, "wb", mtime=0, compresslevel=9) as fh:
        for r in rows:
            fh.write((json.dumps(r, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8"))
