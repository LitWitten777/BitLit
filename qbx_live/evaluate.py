"""
Single-node five-channel evaluator (local; no network).

Given two passages (texts in Hebrew, Greek or Latin script, or braid words in
short form), decide whether their braids are equal and report every channel:

* ``verdict`` — :func:`qbx_ir.algebra.multiprover.verdict`: ``PROVED`` iff the
  Garside normal forms agree (Lean ``verdict_eq_proved_iff``), with the channels
  that agree and disagree (``resonance_iff``: on ``REFUTED`` the fold channel
  always disagrees);
* ``routed`` — :func:`qbx_live.routing.route`: the same verdict reached by the
  cheapest refuter (three-fold-way plan);
* ``summaries`` — the wire-format content address (:func:`qbx_live.wire.digest`)
  of each passage's chunk reading ``(n, σ, w, B)``, computed by the certified
  chunk scheduler (Lean ``schedule_correct``);
* ``defect`` — the defect ``β₂⁻¹β₁`` as a short-form word (Lean ``heal``,
  ``defect_eq_one_iff``: it is trivial iff the claim holds).

Command line::

    python -m qbx_live.evaluate --text "בראשית ברא" --text "ברא בראשית"
    python -m qbx_live.evaluate --strands 3 --word "1 2 1" --word "2 1 2"

Output is one JSON object.
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import Any, Dict, List, Optional, Sequence

from qbx_bible.encode import Encoding, encode_text
from qbx_ir.algebra import multiprover as mp
from qbx_ir.core.braid import Braid
from qbx_live import routing, wire

#: Lean theorem behind each reported field.
LEAN = {
    "verdict": "QBX.Formal.MultiProver.verdict_eq_proved_iff",
    "channels": "QBX.Formal.MultiProver.resonance_iff",
    "routed": "QBX.Formal.MultiProver.Channel.agree_of_eval_eq",
    "summaries": "QBX.Formal.MultiProver.schedule_correct",
    "defect": "QBX.Formal.MultiProver.defect_eq_one_iff",
    "types": "QBX.Formal.MultiProver.ThreeFoldWay.channel_classification",
}


def braid_of_text(text: str, encoding: Encoding = Encoding()) -> Braid:
    return encode_text(text, "passage", encoding).braid


def braid_of_word(word: str, strands: int) -> Braid:
    gens = [int(x) for x in word.replace(",", " ").split()]
    return Braid.from_short_form(strands, gens)


def evaluate(b1: Braid, b2: Braid, chunk_size: int = 64) -> Dict[str, Any]:
    """Evaluate the claim ``b1 = b2`` on one node."""
    cert = mp.verdict(b1, b2)
    routed = routing.route(b1, b2)
    if routed.verdict != cert.verdict:      # cannot happen (see routing docstring)
        raise AssertionError("routing changed the verdict")
    s1 = mp.scheduled_reading(b1, chunk_size)
    s2 = mp.scheduled_reading(b2, chunk_size)
    return {
        "strands": b1.strand_count,
        "lengths": [len(b1.word), len(b2.word)],
        "verdict": cert.verdict,
        "agree": list(cert.agree),
        "disagree": list(cert.disagree),
        "partial_resonance": cert.partial_resonance,
        "routed": routed.to_dict(),
        "summaries": [wire.digest(s1), wire.digest(s2)],
        "defect": mp.defect(b1, b2).short_form(),
        "channel_types": {c: t for c, (t, _) in routing.CHANNEL_TYPES.items()},
        "lean": LEAN,
    }


def main(argv: Optional[Sequence[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Five-channel evaluation of a braid identity.")
    p.add_argument("--text", action="append", default=[], help="a passage (give two)")
    p.add_argument("--word", action="append", default=[], help="a short-form word (give two)")
    p.add_argument("--strands", type=int, default=None,
                   help="strand count (default: the text encoding's, 8)")
    p.add_argument("--chunk-size", type=int, default=64)
    args = p.parse_args(argv)
    items: List[Braid] = []
    enc = Encoding(args.strands) if args.strands else Encoding()
    items += [braid_of_text(t, enc) for t in args.text]
    items += [braid_of_word(w, enc.strand_count) for w in args.word]
    if len(items) != 2:
        p.error("give exactly two passages (--text / --word)")
    json.dump(evaluate(items[0], items[1], args.chunk_size), sys.stdout, ensure_ascii=False,
              indent=2)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
