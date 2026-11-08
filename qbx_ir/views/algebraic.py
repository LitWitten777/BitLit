"""
L2 — Algebraic view.

Renders the braid as a word in the braid group, with its Garside normal
form (the canonical representative of its group element).
"""

from __future__ import annotations

from qbx_ir.algebra.garside import left_normal_form
from qbx_ir.core.braid import Braid
from qbx_ir.views.base import View, register


def _render(braid: Braid) -> str:
    nf = left_normal_form(braid)
    if not braid.word:
        head = ["ε  (identity braid)"]
    else:
        long_form = " ".join(str(g) for g in braid.word)
        short = " ".join(f"+{g.index}" if g.sign == 1 else f"-{g.index}" for g in braid.word)
        head = [
            f"Braid word (n={braid.strand_count}):",
            f"  long form:  {long_form}",
            f"  short form: {short}",
            f"  length:     {len(braid.word)}",
        ]
    return "\n".join(head + [
        f"  Garside normal form: {nf}",
        f"  (inf, sup) = ({nf.infimum}, {nf.supremum})",
    ])


class AlgebraicView(View):
    level = "L2"
    name = "Algebraic"

    def render(self, braid: Braid) -> str:
        return _render(braid)


register(AlgebraicView())
