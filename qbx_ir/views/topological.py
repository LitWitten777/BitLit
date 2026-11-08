"""
L0 — Topological view.

Renders the braid as an ASCII diagram with strands and crossings, drawn
bottom (first generator) at the top of the text, matching the word order.
Positions are 1-indexed from left to right.
"""

from __future__ import annotations

from typing import List

from qbx_ir.core.braid import Braid
from qbx_ir.views.base import View, register


def _row(width: int, marks) -> str:
    r = [" "] * width
    for col, ch in marks:
        r[col] = ch
    return "".join(r).rstrip()


def _render(braid: Braid) -> str:
    n = braid.strand_count
    width = 4 * (n - 1) + 1
    verticals = [(4 * p, "│") for p in range(n)]
    lines: List[str] = []
    lines.append(_row(width, [(4 * p, str((p + 1) % 10)) for p in range(n)]))
    lines.append(_row(width, verticals))
    positions = list(range(1, n + 1))
    for g in braid.word:
        i = g.index
        c1, c2 = 4 * (i - 1), 4 * i
        others = [(4 * p, "│") for p in range(n) if p not in (i - 1, i)]
        # Positive crossing: the strand from the left passes over.
        center = "╲" if g.sign == 1 else "╱"
        lines.append(_row(width, others + [(c1 + 1, "╲"), (c2 - 1, "╱")]))
        lines.append(_row(width, others + [(c1 + 2, center)]))
        lines.append(_row(width, others + [(c1 + 1, "╱"), (c2 - 1, "╲")]))
        lines.append(_row(width, verticals))
        positions[i - 1], positions[i] = positions[i], positions[i - 1]
    lines.append(_row(width, [(4 * p, str(positions[p] % 10)) for p in range(n)]))
    legend = "(top row: initial strand labels; bottom row: which strand ends where; "
    legend += "centre ╲ = σ_i (left strand over), ╱ = σ_i⁻¹)"
    return "\n".join(lines + [legend])


class TopologicalView(View):
    level = "L0"
    name = "Topological"

    def render(self, braid: Braid) -> str:
        return _render(braid)


register(TopologicalView())
