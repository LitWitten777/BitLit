"""Automated Lean staging: the immune system.

A surviving claim is rendered as a closed Lean theorem over ``Discovery.Kernel`` and compiled
by the local Lean toolchain (``lake env lean``).  It is *accepted* only if

* the file compiles with exit status 0 and no ``error`` message,
* the theorem text contains none of ``sorry``, ``admit``, ``axiom``, ``native_decide``,
  ``implemented_by`` (the renderer never emits them; this guards against renderer bugs), and
* ``#print axioms`` reports a subset of ``propext``, ``Classical.choice``, ``Quot.sound``
  (in practice the decided claims use no axiom at all).

Accepted theorems are *burned in*: appended to a Lean module under
``discovery/Discovery/Ledger/`` (so every later ``lake build Discovery`` re-checks them) and
recorded in ``discovery/ledger/burned.jsonl``.  Rejected claims are recorded in the journal with
the compiler output; a rejection after the arbiter's exhaustive check means the Python twin and
the Lean definition disagree, which is reported as a defect, never silently ignored.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
LEDGER_LEAN_DIR = REPO_ROOT / "discovery" / "Discovery" / "Ledger"
LEDGER_JSONL = REPO_ROOT / "discovery" / "ledger" / "burned.jsonl"

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = ("sorry", "admit", "axiom ", "native_decide", "implemented_by", "@[extern")

HEADER = """module

public import Discovery.Kernel

{doc}

@[expose] public section

namespace Discovery.Ledger

open Discovery

"""
FOOTER = "\nend Discovery.Ledger\n\nend\n"

# Scratch files are not modules (`#print axioms` is not allowed inside a module).
SCRATCH_HEADER = "import Discovery.Kernel\n\nnamespace Discovery.Ledger\n\nopen Discovery\n\n"
SCRATCH_FOOTER = "\nend Discovery.Ledger\n"


@dataclass
class StagedClaim:
    name: str
    statement: str
    proof: str
    doc: str
    kind: str                 # "theorem" (claim) or "refutation" (negation of a claim)
    domain: str
    key: str
    meta: dict = field(default_factory=dict)

    def lean(self) -> str:
        doc = self.doc.replace("-/", "- /")
        # larger instance-search budget: `Decidable` of a long bounded statement can exceed
        # the default `synthInstance.maxSize`
        return (f"set_option synthInstance.maxSize 4096 in\n"
                f"set_option synthInstance.maxHeartbeats 400000 in\n"
                f"/-- {doc} -/\ntheorem {self.name} :\n    {self.statement} :=\n  {self.proof}\n")


@dataclass
class StageResult:
    accepted: bool
    seconds: float
    axioms: list
    output: str


def claim_name(prefix: str, kind: str, statement: str) -> str:
    h = hashlib.sha256(statement.encode()).hexdigest()[:10]
    return f"{prefix}_{'refute' if kind == 'refutation' else 'holds'}_{h}"


def make_claim(domain, g, kind: str, counterexample=None, meta=None) -> StagedClaim:
    stmt = domain.lean_statement(g)
    if kind == "refutation":
        statement = f"¬ ({stmt})"
        proof = domain.lean_refutation(g, counterexample)
        doc = (f"Refuted: {domain.describe(g)}.  Counterexample: "
               f"{domain.describe_instance(g, counterexample)}.")
    else:
        statement = stmt
        proof = "by decide +kernel"
        doc = f"{domain.describe(g)}."
    return StagedClaim(claim_name(domain.lean_prefix, kind, statement), statement, proof, doc,
                       kind, domain.name, domain.key(g), dict(meta or {}))


_AXIOM_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
_NOAX_RE = re.compile(r"'([^']+)' does not depend on any axioms")


def parse_axioms(output: str, name: str):
    for m in _AXIOM_RE.finditer(output):
        if m.group(1).endswith(name):
            return [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in _NOAX_RE.finditer(output):
        if m.group(1).endswith(name):
            return []
    return None


def run_lean(src: str, timeout: float, lake: str = "lake"):
    """Elaborate ``src`` as a scratch file with ``lake env lean``; return (rc, output, secs)."""
    with tempfile.TemporaryDirectory(prefix="qbx_stage_") as d:
        path = Path(d) / "Staged.lean"
        path.write_text(src, encoding="utf-8")
        t0 = time.time()
        try:
            proc = subprocess.run([lake, "env", "lean", str(path)], cwd=REPO_ROOT,
                                  capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return None, f"timeout after {timeout}s", timeout
        return proc.returncode, proc.stdout + proc.stderr, time.time() - t0


def stage(claim: StagedClaim, timeout: float = 300.0, lake: str = "lake") -> StageResult:
    """Compile ``claim`` in a scratch file; decide acceptance."""
    text = claim.lean()
    if any(tok in text for tok in FORBIDDEN):
        return StageResult(False, 0.0, [], "forbidden token in rendered claim")
    src = (SCRATCH_HEADER + text + SCRATCH_FOOTER
           + f"\n#print axioms Discovery.Ledger.{claim.name}\n")
    rc, out, secs = run_lean(src, timeout, lake)
    if rc is None:
        return StageResult(False, secs, [], out)
    axioms = parse_axioms(out, claim.name)
    ok = (rc == 0 and "error" not in out and axioms is not None
          and set(axioms) <= STANDARD_AXIOMS)
    return StageResult(ok, secs, axioms or [], out.strip())


class Ledger:
    """The burned-in state: a Lean module per run plus a JSONL index of all runs."""

    def __init__(self, run_name: str, run_doc: str, lean_dir: Path = LEDGER_LEAN_DIR,
                 jsonl: Path = LEDGER_JSONL):
        self.lean_dir, self.jsonl = lean_dir, jsonl
        self.module = f"Discovery.Ledger.{run_name}"
        self.path = lean_dir / f"{run_name}.lean"
        self.run_doc = run_doc
        self.known = self.load_known(jsonl)
        self.burned: list = []

    @staticmethod
    def load_known(jsonl: Path) -> dict:
        known = {}
        if jsonl.exists():
            for line in jsonl.read_text(encoding="utf-8").splitlines():
                if line.strip():
                    rec = json.loads(line)
                    known[(rec["kind"], rec["key"])] = rec
        return known

    def is_known(self, kind: str, key: str) -> bool:
        return (kind, key) in self.known

    def burn(self, claim: StagedClaim, result: StageResult) -> None:
        self.lean_dir.mkdir(parents=True, exist_ok=True)
        self.jsonl.parent.mkdir(parents=True, exist_ok=True)
        body = self.path.read_text(encoding="utf-8")[: -len(FOOTER)] if self.path.exists() else \
            HEADER.format(doc=f"/-!\n{self.run_doc}\n-/")
        self.path.write_text(body + "\n" + claim.lean() + FOOTER, encoding="utf-8")
        rec = {"name": f"Discovery.Ledger.{claim.name}", "module": self.module,
               "kind": claim.kind, "domain": claim.domain, "key": claim.key,
               "statement": claim.statement, "doc": claim.doc, "axioms": result.axioms,
               "kernel_seconds": round(result.seconds, 2), **claim.meta}
        with open(self.jsonl, "a", encoding="utf-8") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        self.known[(claim.kind, claim.key)] = rec
        self.burned.append(rec)

    def rebuild(self, lake: str = "lake", timeout: float = 1800.0) -> tuple:
        """Re-check the whole run module with ``lake build`` (the permanent record)."""
        if not self.path.exists():
            return True, "nothing burned"
        proc = subprocess.run([lake, "build", self.module], cwd=REPO_ROOT, capture_output=True,
                              text=True, timeout=timeout)
        if proc.returncode != 0:
            return False, (proc.stdout + proc.stderr)[-4000:]
        return audit_module(self.module, [r["name"] for r in self.burned], lake=lake)


def audit_module(module: str, names: list, lake: str = "lake", timeout: float = 600.0) -> tuple:
    """Import a built ledger module and check ``#print axioms`` of every listed theorem."""
    src = f"import {module}\n\n" + "".join(f"#print axioms {n}\n" for n in names)
    rc, out, _ = run_lean(src, timeout, lake)
    if rc != 0:
        return False, out[-4000:]
    bad = []
    for n in names:
        ax = parse_axioms(out, n)
        if ax is None or not set(ax) <= STANDARD_AXIOMS:
            bad.append((n, ax))
    return (not bad), ("axiom audit OK: %d theorems" % len(names)) if not bad else repr(bad)
