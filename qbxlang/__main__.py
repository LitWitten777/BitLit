"""`python3 -m qbxlang` — the QBX verifier language.

    python3 -m qbxlang compile FILE.qbx [-o FILE.qbxir]   # parse + evaluate -> IR (JSON)
    python3 -m qbxlang run FILE.qbx                       # human-readable report
    python3 -m qbxlang keygen KEYFILE                     # Ed25519 key pair (KEYFILE, KEYFILE.pub)
    python3 -m qbxlang sign FILE.qbx [--key KEYFILE] [-o FILE.qbxcert]
    python3 -m qbxlang verify FILE.qbxcert FILE.qbx [--pub KEYFILE.pub]
    python3 -m qbxlang lean FILE.qbx [-o Cert.lean]       # kernel claims -> Lean (re-checked by Lean)
    python3 -m qbxlang layers                             # the one-line map of the structure
    python3 -m qbxlang selftest
"""
import argparse
import json
import sys

from . import cert, layers, lean_emit
from .compiler import QbxError, compile_source
from .parser import QbxSyntaxError


def load(path):
    with open(path, "rb") as f:
        raw = f.read()
    return raw, compile_source(raw.decode("utf-8"), path)


def report(ir):
    out = [f"program {ir['program']}"]
    for name, s in ir["sources"].items():
        out.append(f"  source {name}: {s['script']} text, {s['strands']} strands, {s['encoding']}")
    for c in ir["checks"]:
        mark = {"pass": "PASS", "fail": "FAIL", "undecided": "UNDECIDED"}[c["status"]]
        k = "kernel" if c["kernel"] else "computed"
        out.append(f"  [{mark:9}] [{c['layer']:<11}] [{k:8}] {c['label']}: {c['claim']}")
        if c["status"] != "pass":
            out.append(f"               lhs = {json.dumps(c['lhs'], ensure_ascii=False)}  "
                       f"rhs = {json.dumps(c['rhs'], ensure_ascii=False)}")
        if c["witness"]:
            w = c["witness"]
            out.append(f"               dome witness: from cell {w['cell']} the walks end at "
                       f"{w['ends'][0]} and {w['ends'][1]}")
    for cv in ir["conventions"]:
        out.append(f"  [CONVENTION] {cv['name']}: {cv['fields']}  ({cv['note']})")
    for it in ir["interpretations"]:
        sp = it["supporting_checks_pass"]
        sp = "cited checks pass" if sp else ("a cited check does not pass" if sp is False
                                            else "no cited check in this program")
        out.append(f"  [INTERPRETATION, not proved] {it['title']} — support {it['support']} ({sp})")
    s = ir["summary"]
    out.append(f"  {s['pass']} pass, {s['fail']} fail, {s['undecided']} undecided; "
               f"{s['kernel_claims']} claims go to the Lean kernel")
    out.append(f"  IR digest {cert.ir_digest(ir)}")
    return "\n".join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(prog="qbxlang", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("compile"); p.add_argument("file"); p.add_argument("-o")
    p = sub.add_parser("run"); p.add_argument("file")
    p = sub.add_parser("keygen"); p.add_argument("keyfile")
    p = sub.add_parser("sign"); p.add_argument("file"); p.add_argument("--key"); p.add_argument("-o")
    p = sub.add_parser("verify"); p.add_argument("certfile"); p.add_argument("file")
    p.add_argument("--pub")
    p = sub.add_parser("lean"); p.add_argument("file"); p.add_argument("-o")
    sub.add_parser("layers")
    sub.add_parser("selftest")
    a = ap.parse_args(argv)
    try:
        if a.cmd == "compile":
            _, ir = load(a.file)
            text = json.dumps(ir, indent=2, ensure_ascii=False)
            if a.o:
                open(a.o, "w", encoding="utf-8").write(text + "\n")
                print(f"wrote {a.o} ({cert.ir_digest(ir)})")
            else:
                print(text)
        elif a.cmd == "run":
            _, ir = load(a.file)
            print(report(ir))
            return 1 if ir["summary"]["fail"] else 0
        elif a.cmd == "keygen":
            print("public key:", cert.keygen(a.keyfile))
        elif a.cmd == "sign":
            raw, ir = load(a.file)
            c = cert.make(raw, ir, a.key)
            out = a.o or a.file.rsplit(".", 1)[0] + ".qbxcert"
            open(out, "w").write(c)
            print(f"wrote {out}")
        elif a.cmd == "verify":
            raw, ir = load(a.file)
            pub = open(a.pub).read().strip() if a.pub else None
            res = cert.verify(open(a.certfile).read(), raw, ir, pub)
            for name, ok, det in res:
                print(f"  [{'OK' if ok else 'FAIL'}] {name}: {det}")
            ok = all(r[1] for r in res)
            print("VERIFIED" if ok else "NOT VERIFIED")
            return 0 if ok else 1
        elif a.cmd == "lean":
            _, ir = load(a.file)
            text = lean_emit.emit(ir)
            if a.o:
                open(a.o, "w", encoding="utf-8").write(text)
                print(f"wrote {a.o}")
            else:
                print(text)
        elif a.cmd == "layers":
            print(layers.table())
        elif a.cmd == "selftest":
            from .selftest import main as st
            return st()
    except (QbxError, QbxSyntaxError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
