"""
Command line: convert Bible text to braids and run them.

Examples (from the ``QBX`` directory)::

    python3 scripts/bible_braid.py                                  # Genesis 1:1
    python3 scripts/bible_braid.py --ref "Genesis 1:1-5"            # five verse braids
    python3 scripts/bible_braid.py --ref "Genesis 1:1-5" --passage  # + one passage braid
    python3 scripts/bible_braid.py --ref "Genesis 1" --passage-only --views L2,L6
    python3 scripts/bible_braid.py --text "בראשית ברא אלהים" --label "my words"
    python3 scripts/bible_braid.py --corpus path/to/Gen.xml --ref "Genesis 50:26"
    python3 scripts/bible_braid.py --ref "Genesis 1:1" --strands 23 --no-sofit

Outputs go to ``--out`` (default ``out/bible``): per braid a ``.qbx.json``
document, a ``.report.json`` with every computed quantity, a ``.views.txt``
with the requested views, and optionally an ``.svg``.  The exit status is 0
when every check of every braid passed and 1 otherwise.
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import List, Optional

from qbx_bible.corpus import DEFAULT_CORPUS, load_corpus, select
from qbx_bible.encode import DEFAULT_STRANDS, Encoding, concat, encode_text
from qbx_bible.pipeline import ALL_VIEWS, HEAVY_MAX_CROSSINGS, run_braid, summary_lines, write_outputs


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="bible_braid",
        description="Convert Bible text into QBX-IR braids and run them through the QBX pipeline.")
    src = p.add_argument_group("input")
    src.add_argument("--corpus", default=None,
                     help=f"TSV (<ref>\\t<text>) or OSIS XML corpus (default: {DEFAULT_CORPUS})")
    src.add_argument("--ref", action="append", default=None,
                     help='passage to convert, e.g. "Genesis 1:1", "Genesis 1:1-5", "Genesis 1", '
                          '"Gen.1.3" (repeatable; default "Genesis 1:1")')
    src.add_argument("--text", default=None, help="convert this text instead of a corpus passage")
    src.add_argument("--label", default="text", help="name of the braid made from --text")
    enc = p.add_argument_group("encoding")
    enc.add_argument("--strands", type=int, default=DEFAULT_STRANDS,
                     help=f"number of strands n (generators σ1…σ(n-1)); default {DEFAULT_STRANDS}")
    enc.add_argument("--no-sofit", action="store_true",
                     help="encode final letters like their base letters (default: final → inverse)")
    run = p.add_argument_group("run")
    run.add_argument("--passage", action="store_true",
                     help="also build one braid for each whole --ref passage (product of its verses)")
    run.add_argument("--passage-only", action="store_true",
                     help="build only the passage braid(s), not the individual verse braids")
    run.add_argument("--views", default=",".join(ALL_VIEWS),
                     help="comma-separated views to render (L0…L7, or 'none'); default all")
    run.add_argument("--trace", action="store_true", help="include the full rewrite trace in the report")
    run.add_argument("--heavy-max", type=int, default=HEAVY_MAX_CROSSINGS,
                     help="skip polynomial invariants, fingerprint and L5/L6 above this many crossings "
                          f"(default {HEAVY_MAX_CROSSINGS})")
    out = p.add_argument_group("output")
    out.add_argument("--out", default="out/bible", help="output directory (default out/bible)")
    out.add_argument("--no-write", action="store_true", help="do not write any files")
    out.add_argument("--svg", action="store_true", help="also write an SVG diagram per braid")
    out.add_argument("--json", action="store_true", help="print the full reports as JSON")
    out.add_argument("--show", default="", help="comma-separated views to print to the terminal, e.g. L0,L2")
    return p


def main(argv: Optional[List[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    encoding = Encoding(args.strands, sofit_rule=not args.no_sofit)
    views = [] if args.views.strip().lower() == "none" else \
        [v.strip().upper() for v in args.views.split(",") if v.strip()]
    for v in views:
        if v not in ALL_VIEWS:
            print(f"error: unknown view {v!r} (use L0…L7)", file=sys.stderr)
            return 2
    show = [v.strip().upper() for v in args.show.split(",") if v.strip()]

    jobs = []
    if args.text is not None:
        jobs.append(encode_text(args.text, args.label, encoding))
    else:
        try:
            verses = load_corpus(args.corpus)
            for spec in args.ref or ["Genesis 1:1"]:
                chosen = select(verses, spec)
                encoded = [encode_text(v.text, v.ref, encoding) for v in chosen]
                if not args.passage_only:
                    jobs.extend(encoded)
                if (args.passage or args.passage_only) and (len(encoded) > 1 or args.passage_only):
                    jobs.append(concat(encoded, spec, encoding))
        except (OSError, ValueError) as e:
            print(f"error: {e}", file=sys.stderr)
            return 2

    reports = []
    ok = True
    for enc in jobs:
        report = run_braid(enc, encoding, views=sorted(set(views) | set(show)),
                           include_trace=args.trace, heavy_max=args.heavy_max)
        reports.append(report)
        ok = ok and report["all_checks_passed"]
        if not args.json:
            print("\n".join(summary_lines(report)))
            for level in show:
                print(f"  ---- {level} ----")
                print(report["views"][level])
        if not args.no_write:
            paths = write_outputs(enc, report, args.out, svg=args.svg)
            if not args.json:
                print("  wrote       : " + ", ".join(paths.values()))
        if not args.json:
            print()
    if args.json:
        print(json.dumps(reports if len(reports) != 1 else reports[0], ensure_ascii=False, indent=2))
    elif len(reports) > 1:
        print(f"{len(reports)} braids, {'all checks passed' if ok else 'SOME CHECKS FAILED'}")
    return 0 if ok else 1


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
