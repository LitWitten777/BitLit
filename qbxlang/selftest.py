"""End-to-end checks of qbxlang (standard library + `cryptography` for the signature tests)."""
import os
import tempfile

from . import cert, lean_emit
from .compiler import compile_source, walk, walk_r
from .parser import QbxSyntaxError, parse

HERE = os.path.dirname(__file__)


def main():
    fails = []

    def ok(cond, name):
        print(f"  [{'ok' if cond else 'FAIL'}] {name}")
        if not cond:
            fails.append(name)

    # parser
    try:
        parse("check 1 == ")
        ok(False, "syntax error is reported")
    except QbxSyntaxError:
        ok(True, "syntax error is reported")

    # examples
    for name, want_undecided in (("structure.qbx", 1), ("genesis_1_1.qbx", 0)):
        path = os.path.join(HERE, "examples", name)
        src = open(path, "rb").read()
        ir = compile_source(src.decode(), path)
        s = ir["summary"]
        ok(s["fail"] == 0 and s["undecided"] == want_undecided, f"{name}: {s['pass']} pass, "
           f"{s['fail']} fail, {s['undecided']} undecided")
        ok(cert.ir_digest(ir) == cert.ir_digest(compile_source(src.decode(), path)),
           f"{name}: IR digest is deterministic")
        lean = lean_emit.emit(ir)
        ok(lean.count("\n  .") == s["kernel_claims"], f"{name}: {s['kernel_claims']} claims emitted to Lean")

    # a false claim fails, and is never sent to the kernel
    ir = compile_source("def l = word(1,1,-2,-2)\ncheck writhe(l) == 1\n")
    ok(ir["checks"][0]["status"] == "fail" and ir["checks"][0]["kernel"] is None,
       "false claim fails and is not lowered")

    # walk vs walk_r agree up to reversal
    w = (1, -3, 2, 5, -4)
    ok(all(walk(w, x) == walk_r(tuple(reversed(w)), x) for x in range(64)), "walk / walkR agree")

    # certificates
    if cert.HAVE_CRYPTO:
        with tempfile.TemporaryDirectory() as d:
            key = os.path.join(d, "k")
            pub = open(cert.keygen(key)).read().strip()
            path = os.path.join(HERE, "examples", "structure.qbx")
            src = open(path, "rb").read()
            ir = compile_source(src.decode(), path)
            c = cert.make(src, ir, key)
            ok(all(r[1] for r in cert.verify(c, src, ir, pub)), "signed certificate verifies")
            src2 = src.replace(b"dist(0, 7) == 3", b"dist(0, 7) == 4")
            ir2 = compile_source(src2.decode(), path)
            ok(not all(r[1] for r in cert.verify(c, src2, ir2, pub)), "edited source is rejected")
            bad = c.replace("result: PASS", "result: FAIL")
            ok(not all(r[1] for r in cert.verify(bad, src, ir, pub)), "edited certificate is rejected")
    else:
        print("  [skip] signatures (no 'cryptography' package)")

    print(f"{len(fails)} failures")
    return 1 if fails else 0
