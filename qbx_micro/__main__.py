"""Command line: python3 -m qbx_micro <command> ...

  braid N L1 L2 ...           six readings + integrity checks of a braid word
                              (letters: i = sigma_i, -i = inverse)
  laws "IDENTITY" [--cert DIR] law profile in R, C, H, O, S; optional certificates
  lawtable                    the law library against the Cayley-Dickson tower
  certs [PATH]                regenerate the Lean law certificates
  chern M [Q]                 Chern number of the (winding-Q) Qi-Wu-Zhang model at mass M
  grade [--strands N] OUT.jsonl.gz SUMMARY.json DECLS.jsonl.gz ...
                              grade theorem-graph exports (default N = 4)
  selftest                    quick checks against known values
"""

import json
import sys


def _braid(args):
    from . import braid as B
    n = int(args[0])
    word = [int(x) for x in args[1:]]
    r = B.reading(n, word, oscillator=n <= 6)
    r["jones_t"] = {str(k): v for k, v in B.jones_in_t(n, word).items()} if n <= 6 else None
    r["entropy_bound"] = B.entropy_bound(n, word)
    r["integrity"] = B.integrity(n, word)
    print(json.dumps(r, default=str, indent=1))


def _laws(args):
    from . import laws as L, cert as C
    ident = args[0]
    for name, status, wit in L.profile(ident):
        print("%-2s %-15s %s" % (name, status, "" if wit is None else wit))
    pattern, same = L.violated_laws(ident)
    print("fails in:", ", ".join(pattern) or "none of R, C, H, O, S")
    print("same failure pattern as:", ", ".join(same) or "no law in the library")
    if "--cert" in args:
        import os
        out = args[args.index("--cert") + 1]
        os.makedirs(out, exist_ok=True)
        for name, status, wit in L.profile(ident):
            if status == "fails":
                level = L.NAMES.index(name)
                for fmt, text in C.all_formats("fails_" + name, ident, level, wit).items():
                    ext = {"lean": "lean", "coq": "v", "isa": "thy"}[fmt]
                    with open("%s/fails_%s.%s" % (out, name, ext), "w") as fh:
                        fh.write(text)
                break
        print("certificates written to", out)


def _lawtable(args):
    from . import laws as L
    for name, row in L.law_table().items():
        print("%-22s %s" % (name, "  ".join("%s:%s" % x for x in row)))


def _certs(args):
    from . import cert as C
    path = args[0] if args else "QBX/Formal/Certificates/CayleyDickson.lean"
    with open(path, "w") as fh:
        fh.write(C.lean_law_file())
    print("wrote", path)


def _chern(args):
    from . import chern as C
    m = float(args[0])
    q = int(args[1]) if len(args) > 1 else 1
    print(json.dumps(C.chern(C.qwz_winding(m, q) if q != 1 else C.qwz(m)), indent=1))


def _grade(args):
    from . import grade as G
    n = G.STRANDS
    if args and args[0] == "--strands":
        n, args = int(args[1]), args[2:]
    out, summ, paths = args[0], args[1], args[2:]
    rows = G.grade_corpus(paths, n=n)
    for r in rows:
        r.pop("integrity_detail", None)
    G.write_rows(rows, out)
    s = G.summary(rows)
    s["strands"] = n
    with open(summ, "w") as fh:
        json.dump(s, fh, indent=1)
    print(json.dumps(s["channel_resolving_power"]))


def _selftest(args):
    from . import braid as B, laws as L, chern as C
    assert B.jones_in_t(2, [1, 1, 1]) == {1: 1, 3: 1, 4: -1}
    assert B.jones_in_t(3, [1, -2, 1, -2]) == {-2: 1, -1: -1, 0: 1, 1: -1, 2: 1}
    assert B.clifford_key(3, [1, 2, 1]) == B.clifford_key(3, [2, 1, 2])
    assert B.clifford(3, [1] * 4) == ({0: -1}, 0)
    assert all(B.integrity(4, [1, -2, 3, 2, -1, 3]).values())
    assert abs(B.entropy_bound(3, [1, -2]) - 0.9624236501192069) < 1e-9
    assert L.check("(a*b)*c = a*(b*c)", 2)[0] == "holds-complete"
    assert L.check("(a*b)*c = a*(b*c)", 3)[0] == "fails"
    assert L.check("(a*a)*b = a*(a*b)", 4, 512)[0] == "fails"
    assert C.chern(C.qwz(1.0), 24)["degree"] == -1 and C.chern(C.qwz(3.0), 24)["degree"] == 0
    print("selftest passed")


COMMANDS = {"braid": _braid, "laws": _laws, "lawtable": _lawtable, "certs": _certs,
            "chern": _chern, "grade": _grade, "selftest": _selftest}


def main(argv):
    if not argv or argv[0] not in COMMANDS:
        print(__doc__)
        return 1
    COMMANDS[argv[0]](argv[1:])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
