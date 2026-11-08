"""Semantic analysis and evaluation: AST -> IR.

The front end turns text into braid words with the letter -> generator map of
`hypercube.codec.braid_word` (the same map `Sovereign.Organism.BraidWalk` proves acts on Q6).
Each check is evaluated here, in Python, and — when it falls in the kernel's claim language —
also lowered to a kernel claim that `lean_emit.py` writes out for Lean to re-check
(`RequestProject/QBXCheck.lean`, theorem `checkAll_sound`).

Status of a check in the IR:
  * `pass` / `fail`  — decided by computation in Python;
  * `kernel`         — field: the Lean claim that re-checks it, or null if the claim is outside
                       the kernel's language (then the result is computed, not kernel-checked);
  * `undecided`      — braid *equality* in B6: the dome action cannot prove two words equal,
                       only distinguish them; when it does not distinguish them the check is
                       reported `undecided`, never `pass`.
"""
from dataclasses import dataclass

from hypercube import codec

from . import layers
from .parser import Call, Check, Convention, Def, Interpret, ListLit, Name, Num, Source, Str

GEMATRIA_KERNEL = {"standard", "sofit", "ordinal", "katan"}


class QbxError(Exception):
    pass


@dataclass(frozen=True)
class Braid:
    word: tuple
    strands: int

    def to_json(self):
        return {"braid": list(self.word), "strands": self.strands}


@dataclass(frozen=True)
class Text:
    name: str
    text: str
    strands: int
    encoding: str

    def to_json(self):
        return {"source": self.name}


IDENTITY = "identity"


# ------------------------------------------------------------------ braid primitives
def act(g, x):
    return codec.act(g, x)


def walk(word, x):
    for g in word:
        x = act(g, x)
    return x


def walk_r(word, x):
    """Last letter first: the left action of the group element (Lean `walkR`)."""
    for g in reversed(word):
        x = act(g, x)
    return x


def weight(x):
    return bin(x & 63).count("1")


def writhe(word):
    return sum(1 if g > 0 else -1 for g in word)


def perm(word, n):
    p = list(range(n))
    for g in word:
        i = abs(g) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
    return p


def burau_m1(word, n):
    """Unreduced Burau matrix at t = -1 (integer).  Computed only; not kernel-checked."""
    m = [[int(r == c) for c in range(n)] for r in range(n)]
    for g in word:
        i = abs(g) - 1
        blk = [[2, -1], [1, 0]] if g > 0 else [[0, 1], [-1, 2]]
        new = [row[:] for row in m]
        for r in range(n):
            a, b = m[r][i], m[r][i + 1]
            new[r][i] = a * blk[0][0] + b * blk[1][0]
            new[r][i + 1] = a * blk[0][1] + b * blk[1][1]
        m = new
    return m


def hebrew_letters(text):
    ls = codec.letters(text)
    if ls and all(s == "he" for s, _, _ in ls):
        return [(i, fin) for _, i, fin in ls]
    return None


# ------------------------------------------------------------------ compiler
class Compiler:
    def __init__(self, program, filename="<qbx>"):
        self.program = program
        self.filename = filename
        self.env = {}
        self.sources = {}
        self.checks = []
        self.interpretations = []
        self.conventions = []
        self.defs = []

    def err(self, line, msg):
        return QbxError(f"{self.filename}:{line}: {msg}")

    # ---- expressions
    def ev(self, e):
        if isinstance(e, Num):
            return e.value
        if isinstance(e, Str):
            return e.value
        if isinstance(e, ListLit):
            return [self.ev(x) for x in e.items]
        if isinstance(e, Name):
            if e.name in self.env:
                return self.env[e.name]
            if e.name in (IDENTITY, "one"):
                return e.name
            # bare words (gematria methods, encodings) evaluate to themselves
            return e.name
        if isinstance(e, Call):
            return self.call(e)
        raise self.err(getattr(e, "line", 0), f"cannot evaluate {e!r}")

    def braid(self, v, line):
        if isinstance(v, Braid):
            return v
        if v == "one":
            return Braid((), 6)
        raise self.err(line, f"expected a braid, got {v!r}")

    def text(self, v, line):
        if isinstance(v, Text):
            return v
        raise self.err(line, f"expected a source, got {v!r}")

    def call(self, e):
        a = [self.ev(x) for x in e.args]
        f, ln = e.fn, e.line
        if f == "braid":
            t = self.text(a[0], ln)
            return Braid(tuple(codec.braid_word(t.text, t.strands)), t.strands)
        if f == "word":
            n = 6
            for g in a:
                if not isinstance(g, int) or g == 0:
                    raise self.err(ln, "word(...) takes non-zero integers")
                n = max(n, abs(g) + 1)
            return Braid(tuple(a), n)
        if f == "concat":
            bs = [self.braid(x, ln) for x in a]
            return Braid(tuple(g for b in bs for g in b.word), max(b.strands for b in bs))
        if f == "inverse":
            b = self.braid(a[0], ln)
            return Braid(tuple(-g for g in reversed(b.word)), b.strands)
        if f == "walk":
            b = self.braid(a[0], ln)
            self.need6(b, ln)
            return walk(b.word, a[1] if len(a) > 1 else 0)
        if f == "parity":
            b = self.braid(a[0], ln)
            self.need6(b, ln)
            return weight(walk(b.word, a[1] if len(a) > 1 else 0)) % 2
        if f == "writhe":
            return writhe(self.braid(a[0], ln).word)
        if f == "length":
            v = a[0]
            return len(v.word) if isinstance(v, Braid) else len(v)
        if f == "perm":
            b = self.braid(a[0], ln)
            return perm(b.word, a[1] if len(a) > 1 else b.strands)
        if f == "burau":
            b = self.braid(a[0], ln)
            return burau_m1(b.word, b.strands)
        if f == "gematria":
            t = self.text(a[0], ln)
            method = a[1] if len(a) > 1 else "standard"
            return codec.gematria(t.text, method)
        if f == "dist":
            return weight(a[0] ^ a[1])
        if f == "cell":
            b = self.braid(a[0], ln)
            return walk(b.word, a[1] if len(a) > 1 else 0)
        raise self.err(ln, f"unknown function {f!r}")

    def need6(self, b, line):
        if b.strands != 6 or any(abs(g) > 5 for g in b.word):
            raise self.err(line, "walks on Q6 need a 6-strand braid (letters ±1..±5)")

    # ---- lowering a check to the kernel claim language
    def kernel_claim(self, c, lv, rv):
        lhs, rhs = c.lhs, c.rhs
        if isinstance(rhs, Call) and not isinstance(lhs, Call):
            lhs, rhs, lv, rv = rhs, lhs, rv, lv
        if c.op == "!=":
            if isinstance(lv, Braid) and isinstance(rv, Braid):
                if all(abs(g) <= 5 for g in lv.word + rv.word):
                    return {"braidNe": [list(lv.word), list(rv.word)]}
            return None
        if not isinstance(lhs, Call) or not isinstance(rv, (int, list)) and rv != IDENTITY:
            return None
        args = [self.ev(x) for x in lhs.args]
        if lhs.fn in ("walk", "cell"):
            return {"walkEnd": [list(args[0].word), args[1] if len(args) > 1 else 0, rv]}
        if lhs.fn == "parity":
            return {"parity": [list(args[0].word), args[1] if len(args) > 1 else 0, rv]}
        if lhs.fn == "writhe":
            return {"writhe": [list(args[0].word), rv]}
        if lhs.fn == "perm":
            n = args[1] if len(args) > 1 else args[0].strands
            p = list(range(n)) if rv == IDENTITY else rv
            return {"perm": [n, list(args[0].word), p]}
        if lhs.fn == "dist":
            return {"cellDist": [args[0], args[1], rv]}
        if lhs.fn == "gematria":
            method = args[1] if len(args) > 1 else "standard"
            ls = hebrew_letters(args[0].text)
            if ls is not None and method in GEMATRIA_KERNEL:
                return {"gematria": [method, [list(x) for x in ls], rv]}
        return None

    # ---- statements
    def run(self):
        for s in self.program.stmts:
            if isinstance(s, Source):
                f = {k: self.ev(v) for k, v in s.fields.items()}
                if "text" not in f:
                    raise self.err(s.line, f"source {s.name} has no text")
                enc = f.get("encoding", "letter-ordinal-v1")
                if enc != "letter-ordinal-v1":
                    raise self.err(s.line, f"unknown encoding {enc!r}")
                t = Text(s.name, f["text"], int(f.get("strands", 6)), enc)
                self.env[s.name] = t
                self.sources[s.name] = {"text": t.text, "encoding": enc, "strands": t.strands,
                                        "script": codec.detect_script(t.text), "line": s.line}
            elif isinstance(s, Def):
                v = self.ev(s.expr)
                self.env[s.name] = v
                self.defs.append({"name": s.name, "line": s.line, "value": jsonable(v)})
            elif isinstance(s, Check):
                self.check(s)
            elif isinstance(s, Interpret):
                f = {k: self.ev(v) for k, v in s.fields.items()}
                support = f.get("support", [])
                support = support if isinstance(support, list) else [support]
                cited = [c for c in self.checks if c["label"] in support]
                self.interpretations.append({
                    "title": s.title, "line": s.line, "claims": f.get("claims", ""),
                    "support": support,
                    "supporting_checks_pass": all(c["status"] == "pass" for c in cited) if cited else None,
                    "status": "interpretation", "layer": "interpretation"})
            elif isinstance(s, Convention):
                f = {k: self.ev(v) for k, v in s.fields.items()}
                self.conventions.append({"name": s.name, "line": s.line,
                                         "fields": {k: jsonable(v) for k, v in f.items()},
                                         "status": "convention", "layer": "convention",
                                         "note": "one labelling of the 64 cells among 64! possible"})
        return self.ir()

    def check(self, s):
        lv, rv = self.ev(s.lhs), self.ev(s.rhs)
        if isinstance(lv, Braid) and rv == "one":
            rv = Braid((), lv.strands)
        if isinstance(rv, Braid) and lv == "one":
            lv = Braid((), rv.strands)
        text = f"{show(s.lhs)} {s.op} {show(s.rhs)}"
        witness = None
        if isinstance(lv, Braid) and isinstance(rv, Braid):
            # Equality in B6 is not decided; inequality is witnessed by the dome action.
            diff = [x for x in range(64) if walk_r(lv.word, x) != walk_r(rv.word, x)] \
                if all(abs(g) <= 5 for g in lv.word + rv.word) else []
            if diff:
                witness = {"cell": diff[0], "ends": [walk_r(lv.word, diff[0]), walk_r(rv.word, diff[0])]}
            if s.op == "!=":
                status = "pass" if diff else "undecided"
            else:
                status = "fail" if diff else "undecided"
        else:
            if rv == IDENTITY and isinstance(lv, list):
                rv = list(range(len(lv)))
            eq = lv == rv
            status = "pass" if eq == (s.op == "==") else "fail"
        claim = self.kernel_claim(s, lv, rv) if status == "pass" else None
        fn = s.lhs.fn if isinstance(s.lhs, Call) else (s.rhs.fn if isinstance(s.rhs, Call) else "")
        self.checks.append({
            "line": s.line, "label": s.label or f"line {s.line}", "claim": text,
            "status": status, "lhs": jsonable(lv), "rhs": jsonable(rv),
            "witness": witness, "kernel": claim, "layer": layers.layer_of(fn, lv, rv)})

    def ir(self):
        return {
            "qbxir": "1.0",
            "program": self.filename,
            "sources": self.sources,
            "defs": self.defs,
            "checks": self.checks,
            "conventions": self.conventions,
            "interpretations": self.interpretations,
            "summary": {
                "checks": len(self.checks),
                "pass": sum(c["status"] == "pass" for c in self.checks),
                "fail": sum(c["status"] == "fail" for c in self.checks),
                "undecided": sum(c["status"] == "undecided" for c in self.checks),
                "kernel_claims": sum(c["kernel"] is not None for c in self.checks),
                "interpretations": len(self.interpretations),
                "conventions": len(self.conventions),
            },
            "trusted_base": {
                "kernel": "RequestProject/QBXCheck.lean: Claim.eval_sound, checkAll_sound",
                "model": "RequestProject/Q6Structure.lean",
                "front_end": "hypercube.codec.letters / braid_word (Python, not verified)",
            },
        }


def show(e):
    if isinstance(e, Num):
        return str(e.value)
    if isinstance(e, Str):
        return '"' + e.value + '"'
    if isinstance(e, Name):
        return e.name
    if isinstance(e, ListLit):
        return "[" + ", ".join(show(x) for x in e.items) + "]"
    if isinstance(e, Call):
        return f"{e.fn}(" + ", ".join(show(x) for x in e.args) + ")"
    return repr(e)


def jsonable(v):
    if hasattr(v, "to_json"):
        return v.to_json()
    if isinstance(v, (list, tuple)):
        return [jsonable(x) for x in v]
    return v


def compile_source(src, filename="<qbx>"):
    from .parser import parse
    return Compiler(parse(src), filename).run()
