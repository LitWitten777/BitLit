"""
Run a Bible braid through the QBX-IR pipeline.

:func:`run_braid` takes an :class:`~qbx_bible.encode.EncodedText` and computes

* **invariants** — permutation, writhe, closure components, linking number,
  and (for at most 10 strands and ``heavy_max`` crossings) the Alexander and
  Jones polynomials of the closure;
* **Garside left normal form** — the exact canonical form of the braid-group
  element (infimum, supremum, canonical length, normal-form word);
* **rewriting** — the R01/R02 reduction with its full provenance trace
  (:func:`qbx_ir.algebra.rewriting.normal_form_with_trace`);
* **ledger certificate** — the trace written as migration-019 rows with the
  in-memory reference checks of :mod:`qbx_ir.ledger`: every braid row and
  rewrite row must be well formed and the chain must be an accepted
  derivation from the verse braid to its reduced form;
* **checks** — each a test that could fail: the ledger certificate is accepted;
  the reduced word is equal to the input in Bₙ (Garside); the Garside normal
  form re-encodes to the same element; the braid is the product of its word
  braids; rewriting preserved permutation and writhe;
* **sofit test** (PLAN.md L2) — whether turning the sofit rule off changes the
  braid-group element;
* the QBX **fingerprint** and its hash, and the requested **views** (L0–L7).

:func:`write_outputs` saves the braid as a ``.qbx.json`` document (loadable
with :func:`qbx_ir.io.load`), the report as JSON, the views as text and,
optionally, an SVG diagram.
"""

from __future__ import annotations

import json
import os
import re
from typing import Any, Dict, List, Optional, Sequence

from qbx_ir import io as qbx_io
from qbx_ir.algebra.garside import left_normal_form
from qbx_ir.algebra.invariants import (
    closure_components,
    linking_number,
    permutation,
    writhe,
)
from qbx_ir.algebra.polynomial_invariants import (
    alexander_polynomial,
    format_jones,
    jones_polynomial,
)
from qbx_ir.algebra.rewriting import braid_hash, normal_form_with_trace
from qbx_ir.core.braid import Braid
from qbx_ir.fingerprint import fingerprint, fingerprint_hash
from qbx_ir.ledger import BraidRow, braid_problems, derivation_problems, record_rewrite, rewrite_problems

from qbx_bible.encode import EncodedText, Encoding, encode_text

ALL_VIEWS = ("L0", "L1", "L2", "L3", "L4", "L5", "L6", "L7")
#: Views that are skipped above this many strands (they build 2ⁿ- or fusion-space matrices).
HEAVY_VIEWS = {"L4": 8, "L5": 8}
#: Above this many crossings the polynomial invariants, fingerprint and L5/L6 are skipped.
HEAVY_MAX_CROSSINGS = 400


def ledger_certificate(braid: Braid, include_trace: bool = False) -> Dict[str, Any]:
    """The R01/R02 reduction of ``braid`` as checked migration-019 ledger rows.

    Every rewrite of :func:`normal_form_with_trace` is re-recorded with
    :func:`qbx_ir.ledger.record_rewrite` and checked with ``rewrite_problems``;
    the rows are chained forwards from the source braid and the chain must end
    at the reduced braid — the conditions of ``derivation_problems``, checked
    one row at a time so that long passages do not hold every row in memory.
    For short traces (≤ 2000 steps) ``derivation_problems`` itself is also run.
    """
    reduced, trace = normal_form_with_trace(braid)
    n = braid.strand_count
    source = BraidRow.of(n, braid.short_form())
    target = BraidRow.of(n, reduced.short_form())
    problems: List[Any] = []
    problems += [("source", p) for p in braid_problems(source)]
    problems += [("target", p) for p in braid_problems(target)]
    keep_rows = len(trace) <= 2000
    rows = []
    current = source
    rule_counts: Dict[str, int] = {}
    for k, t in enumerate(trace):
        rule_counts[t.rule_id] = rule_counts.get(t.rule_id, 0) + 1
        try:
            row = record_rewrite(current, t.rule_id, t.position)
        except ValueError as e:
            problems.append((f"step {k}", ("not_applicable", {"error": str(e)})))
            break
        problems += [(f"step {k}", p) for p in rewrite_problems(row)]
        if row.input.key != current.key:
            problems.append((f"step {k}", ("step_disconnected", {"step": k})))
        if keep_rows:
            rows.append(row)
        current = row.output
    if current.key != target.key:
        problems.append(("derivation", ("target_mismatch", {})))
    if keep_rows and not problems:
        problems += [("derivation", p) for p in
                     derivation_problems(source, target, rows, [True] * len(rows))]
    out: Dict[str, Any] = {
        "reduced": reduced,
        "source_hash": source.braid_hash,
        "target_hash": target.braid_hash,
        "steps": len(trace),
        "rule_counts": rule_counts,
        "problems": [[where, kind, detail] for where, (kind, detail) in problems],
        "accepted": not problems,
    }
    if include_trace:
        out["trace"] = [t.to_dict() for t in trace]
    return out


def run_braid(enc: EncodedText, encoding: Encoding,
              views: Sequence[str] = ALL_VIEWS,
              include_trace: bool = False,
              sofit_test: bool = True,
              heavy_max: int = HEAVY_MAX_CROSSINGS) -> Dict[str, Any]:
    """Run the pipeline on one encoded text and return a JSON-serialisable report.

    Braids with more than ``heavy_max`` crossings (whole chapters, say) skip
    the polynomial invariants, the fingerprint and the views L5/L6, whose cost
    grows quickly with length; everything else is always computed.
    """
    import numpy as np
    from qbx_ir.views import render

    B = enc.braid
    n = B.strand_count
    short = B.short_form()
    heavy = len(short) <= heavy_max
    skipped: List[str] = []

    nf = left_normal_form(B)
    nf_braid = nf.to_braid()
    cert = ledger_certificate(B, include_trace)
    reduced: Braid = cert.pop("reduced")
    trace = cert.pop("trace", None)

    invariants: Dict[str, Any] = {
        "permutation": list(permutation(B)),
        "writhe": writhe(B),
        "closure_components": len(closure_components(B)),
        "linking_number": linking_number(B),
    }
    if heavy and n <= 10:
        invariants["alexander"] = alexander_polynomial(B).format("t")
        invariants["jones"] = format_jones(jones_polynomial(B))
    elif n > 10:
        skipped.append("Alexander/Jones (more than 10 strands)")
    else:
        skipped.append(f"Alexander/Jones (more than {heavy_max} crossings)")

    word_product = [g for a, b in enc.spans for g in short[a:b]]
    checks = {
        "ledger_certificate_accepted": cert["accepted"],
        "reduced_word_equal_in_Bn": left_normal_form(reduced) == nf,
        "garside_form_equal_in_Bn": left_normal_form(nf_braid) == nf,
        "braid_is_product_of_word_braids": word_product == short,
        "rewriting_preserves_permutation": permutation(reduced) == permutation(B),
        "rewriting_preserves_writhe": writhe(reduced) == writhe(B),
    }

    report: Dict[str, Any] = {
        "ref": enc.label,
        "text": enc.text,
        "consonantal_text": " ".join(enc.words),
        "encoding": {"scheme": B.metadata.get("scheme"), "strand_count": n,
                     "sofit_rule": encoding.sofit_rule},
        "words": len(enc.words),
        "letters": enc.letters,
        "crossings": len(short),
        "word": short,
        "braid_hash": braid_hash(B),
        "invariants": invariants,
        "garside": {
            "infimum": nf.infimum,
            "supremum": nf.supremum,
            "canonical_length": nf.canonical_length,
            "normal_form": nf.to_short_form(),
            "trivial": nf.power == 0 and not nf.factors,
        },
        "rewriting": {
            "reduced_word": reduced.short_form(),
            "reduced_length": len(reduced),
            "steps": cert["steps"],
            "rule_counts": cert["rule_counts"],
        },
        "ledger": cert,
        "checks": checks,
        "all_checks_passed": all(checks.values()),
    }
    if trace is not None:
        report["rewriting"]["trace"] = trace

    if sofit_test:
        other = Encoding(encoding.strand_count, not encoding.sofit_rule)
        alt = encode_text(enc.text, enc.label, other).braid
        report["sofit_test"] = {
            "finals_in_text": sum(1 for g_on, g_off in zip(short, alt.short_form()) if g_on != g_off),
            "same_element_with_rule_toggled": left_normal_form(alt) == nf,
        }

    if heavy:
        fp = fingerprint(B)
        report["fingerprint"] = json.loads(json.dumps(fp, default=str))
        report["fingerprint_hash"] = fingerprint_hash(B)
    else:
        skipped.append(f"fingerprint (more than {heavy_max} crossings)")

    rendered: Dict[str, str] = {}
    for level in views:
        limit = HEAVY_VIEWS.get(level)
        if limit is not None and n > limit:
            rendered[level] = f"(skipped: {level} is limited to ≤ {limit} strands)"
            continue
        if level in ("L5", "L6") and not heavy:
            rendered[level] = f"(skipped: more than {heavy_max} crossings; raise --heavy-max)"
            continue
        with np.errstate(all="ignore"):
            rendered[level] = render(B, level)
    report["views"] = rendered
    report["skipped"] = skipped
    return report


def slug(label: str) -> str:
    """A filesystem-safe name for a reference such as ``"Genesis 1:1-5"``."""
    s = re.sub(r"[^A-Za-z0-9]+", "_", label).strip("_")
    return s or "braid"


def write_outputs(enc: EncodedText, report: Dict[str, Any], out_dir: str,
                  svg: bool = False) -> Dict[str, str]:
    """Write ``<slug>.qbx.json``, ``<slug>.report.json``, ``<slug>.views.txt`` (and ``.svg``)."""
    os.makedirs(out_dir, exist_ok=True)
    base = os.path.join(out_dir, slug(enc.label))
    paths = {"braid": base + ".qbx.json", "report": base + ".report.json",
             "views": base + ".views.txt"}
    doc = qbx_io.to_document(enc.braid, compute=["permutation", "writhe", "components"])
    with open(paths["braid"], "w", encoding="utf-8") as fh:
        json.dump(doc, fh, ensure_ascii=False, indent=2)
    with open(paths["report"], "w", encoding="utf-8") as fh:
        json.dump(report, fh, ensure_ascii=False, indent=2)
    with open(paths["views"], "w", encoding="utf-8") as fh:
        for level, text in report.get("views", {}).items():
            fh.write(f"==== {level} ====\n{text}\n\n")
    if svg:
        from qbx_ir.render import save_svg
        paths["svg"] = base + ".svg"
        save_svg(enc.braid, paths["svg"])
    return paths


def summary_lines(report: Dict[str, Any]) -> List[str]:
    """A short human-readable summary of a report."""
    inv = report["invariants"]
    g = report["garside"]
    rw = report["rewriting"]
    lines = [
        f"{report['ref']}",
        f"  text        : {_clip(report['consonantal_text'])}",
        f"  encoding    : {report['encoding']['scheme']}, n = {report['encoding']['strand_count']}, "
        f"sofit rule {'on' if report['encoding']['sofit_rule'] else 'off'}",
        f"  size        : {report['words']} words, {report['letters']} letters → {report['crossings']} crossings",
        f"  word        : {_short(report['word'])}",
        f"  permutation : {inv['permutation']}   writhe {inv['writhe']}   "
        f"closure components {inv['closure_components']}   linking {inv['linking_number']}",
    ]
    if "alexander" in inv:
        lines.append(f"  Alexander   : {inv['alexander']}")
    if "jones" in inv:
        lines.append(f"  Jones       : {inv['jones']}")
    lines += [
        f"  Garside     : inf {g['infimum']}, sup {g['supremum']}, canonical length {g['canonical_length']}",
        f"  rewriting   : {rw['steps']} steps {rw['rule_counts']} → length {rw['reduced_length']}",
        f"  ledger      : derivation {'ACCEPTED' if report['ledger']['accepted'] else 'REJECTED'} "
        f"({report['ledger']['source_hash'][:12]}… → {report['ledger']['target_hash'][:12]}…)",
    ]
    if "sofit_test" in report:
        s = report["sofit_test"]
        lines.append(f"  sofit test  : {s['finals_in_text']} final letters; element "
                     f"{'unchanged' if s['same_element_with_rule_toggled'] else 'changes'} with the rule toggled")
    if "fingerprint_hash" in report:
        lines.append(f"  fingerprint : {report['fingerprint_hash']}")
    if report.get("skipped"):
        lines.append(f"  skipped     : {'; '.join(report['skipped'])}")
    failed = [k for k, v in report["checks"].items() if not v]
    lines.append("  checks      : all passed" if not failed else f"  checks      : FAILED {failed}")
    return lines


def _clip(text: str, limit: int = 160) -> str:
    return text if len(text) <= limit else text[:limit] + f" … ({len(text)} characters)"


def _short(word: Sequence[int], limit: int = 24) -> str:
    def sym(g: int) -> str:
        return f"σ{abs(g)}" + ("⁻¹" if g < 0 else "")
    s = " ".join(sym(g) for g in word[:limit])
    return s + (f" … (+{len(word) - limit})" if len(word) > limit else "")
