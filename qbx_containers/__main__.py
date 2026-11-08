"""``python -m qbx_containers check | show NAME | list``."""

from __future__ import annotations

import json
import sys

from qbx_containers.registry import load_registry


def main(argv: list) -> int:
    cmd = argv[1] if len(argv) > 1 else "check"
    reg = load_registry()
    if cmd == "list":
        for n, c in sorted(reg.containers.items()):
            print(f"{n:24s} {c.curvature:9s} {c.carrier:22s} v{c.version}")
        for n, c in sorted(reg.composites.items()):
            print(f"{n:24s} {reg.composite_curvature(c):9s} [{c.kind}]")
        return 0
    if cmd == "show":
        n = argv[2]
        if n in reg.containers:
            c = reg.containers[n]
            d = {k: v for k, v in c.__dict__.items() if k != "path"}
            d["measured_curvature"] = c.measured_curvature()
            print(json.dumps(d, indent=2))
        else:
            print(json.dumps(reg.composites[n].data, indent=2))
        return 0
    if cmd == "check":
        bad = 0
        for name, (errs, warns) in reg.check().items():
            status = "FAIL" if errs else "ok"
            print(f"[{status}] {name}")
            for e in errs:
                print(f"    error: {e}")
            for w in warns:
                print(f"    warning: {w}")
            bad += bool(errs)
        print(f"{len(reg.containers)} containers, {len(reg.composites)} composites, {bad} failing")
        return 1 if bad else 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
