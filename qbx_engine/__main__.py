"""Command line for the harmonic torus engine.

  python -m qbx_engine selftest
  python -m qbx_engine run PATH_OR_TEXT [--store FILE] [--torus N M] [--full]
  python -m qbx_engine alphabet [hebrew|greek|latin]
  python -m qbx_engine braid [--spoken] TEXT1 TEXT2 [TEXT3 ...]
  python -m qbx_engine translit TARGET TEXT
  python -m qbx_engine cd-laws [MAXLEVEL]
  python -m qbx_engine lean-tables          (print the Lean alphabet tables)
  python -m qbx_engine serve [--port 8765] [--host 127.0.0.1]   (web UI with controls)
  python -m qbx_engine letter GLYPH [GLYPH ...]                 (letter detail cards)
  python -m qbx_engine program [--text TEXT] [--torus N M] PROGRAM  (command language)
  python -m qbx_engine play FRAMES [--text TEXT] [--torus N M]  (scheduled frames)
  python -m qbx_engine merkaba [CONTROL ...] [--svg FILE]       (merkaba controls figure)
  python -m qbx_engine combine "A1 A2" "B1 B2"                  (braids with braids)
  python -m qbx_engine outset TEXT --out DIR [--frames K] [--torus N M]   (output set)
  python -m qbx_engine checks                                   (all re-derived checks)

Run from `QBX/src` (or with `QBX/src` on PYTHONPATH).  No dependencies.
"""

import json
import sys

from . import alphabets, braidlines, multivector
from .engine import Engine, EigenStore


def _summary(rec):
    out = {"id": rec["id"], "kind": rec["kind"], "channels": {}}
    for name, ch in rec["channels"].items():
        out["channels"][name] = {
            "length": ch["length"], "bits": ch["bits"],
            "blades": len(ch["multivector"]),
            "colours": [(c["colour"], c["wavelength_nm"], c["energy"]) for c in ch["colours"]],
            "checks_ok": all(ch["checks"].values()),
        }
    if "braid" in rec:
        out["braid"] = {m: {"word": b["word"], "fold": b.get("fold"),
                            "integrity_ok": all(b.get("integrity", {}).values())}
                        for m, b in rec["braid"].items()}
    if "letters" in rec:
        out["letters"] = len(rec["letters"])
    return out


def selftest():
    from . import torus
    ok = True
    eng = Engine(torus=(8, 8))
    samples = ["בראשית ברא אלהים את השמים ואת הארץ",
               "ΕΝ ΑΡΧΗ ΗΝ Ο ΛΟΓΟΣ",
               "IN PRINCIPIO ERAT VERBUM",
               [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5],
               [0.5, -1.25, 2.0, 3.75],
               '{"a": [1, 2, 3], "b": {"c": 4.5, "d": "שלום"}}',
               "1,2,3\n4,5,6\n7,8,9\n",
               bytes(range(256))]
    for s in samples:
        rec = eng.process(s)
        for name, ch in rec["channels"].items():
            for k, v in ch["checks"].items():
                if not v:
                    ok = False
                    print("FAIL", rec["id"], name, k)
        for m, b in rec.get("braid", {}).items():
            for k, v in b.get("integrity", {}).items():
                if not v:
                    ok = False
                    print("FAIL braid", m, k)
        fc = eng.flow_check(s)
        for name, d in fc.items():
            for k, v in d.items():
                if not v:
                    ok = False
                    print("FAIL flow", name, k)
        st = EigenStore()
        st.append(rec)
        for name, ch in rec["channels"].items():
            from . import ingest as ing
            if st.signal(rec["id"], name) != multivector.EigenMultivector(
                    ing.ingest(s)["channels"][name]).signal:
                ok = False
                print("FAIL store roundtrip", name)
    for a in alphabets.ALPHABETS:
        if not all(alphabets.symmetry_closed(l.sym) for l in alphabets.letters(a)):
            ok = False
            print("FAIL symmetry closure", a)
    expect = {1: [], 2: ["commutative"], 3: ["commutative", "associative"],
              4: ["commutative", "associative", "norm-multiplicative"]}
    for n, lost in expect.items():
        if multivector.lost_properties(n) != lost:
            ok = False
            print("FAIL cd laws", n, multivector.lost_properties(n))
    from . import outsets
    from .controls import Session
    sess = Session("בראשית ברא אלהים", N=8, M=9)
    sess.run("flow 1 2; turnX; repeat 3 { read; diag }; spin; cross 1; invert")
    sess.advance(sess.master_clock().joint_period())
    for group, d in outsets.all_checks(sess).items():
        for k, v in d.items():
            if not v:
                ok = False
                print("FAIL", group, k)
    print("selftest", "OK" if ok else "FAILED")
    return 0 if ok else 1


def _opts(rest, flags):
    """Split `rest` into options (flag -> list of values) and positional arguments."""
    opts, pos, i = {}, [], 0
    while i < len(rest):
        if rest[i] in flags:
            n = flags[rest[i]]
            opts[rest[i]] = rest[i + 1:i + 1 + n]
            i += 1 + n
        else:
            pos.append(rest[i])
            i += 1
    return opts, pos


def _more(cmd, rest):
    from . import braidbraid, letters, merkaba, outsets
    from .controls import Session
    if cmd == "serve":
        from .server import serve
        o, _ = _opts(rest, {"--port": 1, "--host": 1})
        serve(o.get("--host", ["127.0.0.1"])[0], int(o.get("--port", ["8765"])[0]))
        return 0
    if cmd == "letter":
        for g in rest:
            print(json.dumps(letters.card(g), ensure_ascii=False, indent=1))
        return 0
    if cmd in ("program", "play"):
        o, pos = _opts(rest, {"--text": 1, "--torus": 2})
        N, M = map(int, o.get("--torus", ["16", "25"]))
        sess = Session(o.get("--text", ["בראשית ברא אלהים"])[0], N=N, M=M)
        st = sess.run(" ".join(pos)) if cmd == "program" else sess.advance(int(pos[0]) if pos else 1)
        st.pop("torus_grid"); st.pop("standing_grid")
        print(json.dumps(st, ensure_ascii=False, indent=1, default=str))
        return 0 if all(st["checks"].values()) else 1
    if cmd == "merkaba":
        o, pos = _opts(rest, {"--svg": 1})
        m = merkaba.Merkaba().run(pos)
        if "--svg" in o:
            with open(o["--svg"][0], "w", encoding="utf-8") as fh:
                fh.write(merkaba.svg(m))
        print(json.dumps({"state": m.as_dict(), "checks": merkaba.checks()}, indent=1))
        return 0
    if cmd == "combine":
        a, b = rest[0].split(), rest[1].split()
        a = a if len(a) > 1 else a + [a[0][::-1]]
        b = b if len(b) > 1 else b + [b[0][::-1]]
        print(json.dumps(braidbraid.interact(a, b), ensure_ascii=False, indent=1, default=str))
        return 0
    if cmd == "outset":
        o, pos = _opts(rest, {"--out": 1, "--frames": 1, "--torus": 2})
        N, M = map(int, o.get("--torus", ["16", "25"]))
        fr = int(o["--frames"][0]) if "--frames" in o else None
        src = pos[0] if pos else "QBX"
        r = outsets.outset(src, o.get("--out", ["outset"])[0], frames=fr, N=N, M=M)
        print(json.dumps(r, indent=1))
        return 0 if r["ok"] else 1
    if cmd == "checks":
        sess = Session("בראשית ברא אלהים", N=8, M=9)
        sess.advance(50)
        r = outsets.all_checks(sess)
        print(json.dumps(r, indent=1))
        return 0 if all(v for d in r.values() for v in d.values()) else 1
    return 2


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 0
    cmd, rest = argv[0], argv[1:]
    if cmd == "selftest":
        return selftest()
    if cmd == "run":
        store, N, M, full, src = None, 16, 16, False, None
        i = 0
        while i < len(rest):
            if rest[i] == "--store":
                store = rest[i + 1]; i += 2
            elif rest[i] == "--torus":
                N, M = int(rest[i + 1]), int(rest[i + 2]); i += 3
            elif rest[i] == "--full":
                full = True; i += 1
            else:
                src = rest[i]; i += 1
        if src is None or src == "-":
            src = sys.stdin.buffer.read()
        eng = Engine(torus=(N, M), store=EigenStore(store))
        rec = eng.process(src)
        eng.store.append(rec)
        print(json.dumps(rec if full else _summary(rec), ensure_ascii=False, indent=1))
        return 0
    if cmd == "alphabet":
        names = rest or list(alphabets.ALPHABETS)
        for a in names:
            for l in alphabets.letters(a):
                print(json.dumps(l.as_dict(), ensure_ascii=False))
        return 0
    if cmd == "braid":
        mode = "written"
        if rest and rest[0] == "--spoken":
            mode, rest = "spoken", rest[1:]
        print(json.dumps(braidlines.read(rest, mode), ensure_ascii=False, indent=1,
                         default=str))
        return 0
    if cmd == "translit":
        print(alphabets.transliterate(" ".join(rest[1:]), rest[0]))
        return 0
    if cmd == "cd-laws":
        top = int(rest[0]) if rest else 5
        for n in range(top + 1):
            print(2 ** n, "lost:", multivector.lost_properties(n))
        return 0
    if cmd == "lean-tables":
        from .gen_lean import lean_tables
        print(lean_tables())
        return 0
    if cmd in ("serve", "letter", "program", "play", "merkaba", "combine", "outset", "checks"):
        return _more(cmd, rest)
    print("unknown command", cmd)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
