#!/usr/bin/env python3
"""Inventory of `native_decide` uses (tactic occurrences, comments and docstrings stripped).

Usage:  python QBX/scripts/native_decide_inventory.py [--markdown] [ROOT ...]

Default roots: QBX, sovereign, refinery (relative to the repository root).  `.lake` is skipped.
A file using `native_decide` depends on `Lean.ofReduceBool` / `Lean.trustCompiler`; see
`CONTRIBUTING.md` ("Kernel-evaluation policy") for when that is acceptable.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
_BLOCK = re.compile(r"/-.*?-/", re.S)
_LINE = re.compile(r"--[^\n]*")


def strip_comments(src: str) -> str:
    # Nested block comments are rare here; a non-greedy pass is sufficient for counting.
    return _LINE.sub("", _BLOCK.sub("", src))


def count_uses(path: Path) -> int:
    return len(re.findall(r"\bnative_decide\b", strip_comments(path.read_text(encoding="utf-8"))))


def inventory(roots):
    rows = []
    for root in roots:
        base = REPO / root
        if not base.exists():
            continue
        for p in sorted(base.rglob("*.lean")):
            if ".lake" in p.parts:
                continue
            n = count_uses(p)
            if n:
                rows.append((str(p.relative_to(REPO)), n))
    return rows


def main(argv):
    md = "--markdown" in argv
    roots = [a for a in argv if not a.startswith("--")] or ["QBX", "sovereign", "refinery"]
    rows = inventory(roots)
    total = sum(n for _, n in rows)
    if md:
        print("| file | uses |\n|---|---|")
        for f, n in rows:
            print(f"| `{f}` | {n} |")
        print(f"\n{len(rows)} files, {total} uses.")
    else:
        for f, n in rows:
            print(f"{n:5d}  {f}")
        print(f"{len(rows)} files, {total} uses")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
