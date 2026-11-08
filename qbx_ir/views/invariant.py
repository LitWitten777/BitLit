"""
L6 — Invariant view.

Renders invariants of the braid and of its closure.
"""

from __future__ import annotations

from qbx_ir.algebra.invariants import (
    closure_components,
    linking_matrix,
    linking_number,
    permutation,
    permutation_one_line,
    writhe,
)
from qbx_ir.algebra.polynomial_invariants import (
    MAX_STATE_SUM_CROSSINGS,
    alexander_polynomial,
    format_jones,
    jones_polynomial,
)
from qbx_ir.core.braid import Braid
from qbx_ir.views.base import View, register


def _cycle_notation(dest) -> str:
    """Cycle notation from one-line form dest[i] = image of i+1."""
    n = len(dest)
    seen = [False] * n
    cycles = []
    for start in range(n):
        if seen[start]:
            continue
        cycle = []
        cur = start
        while not seen[cur]:
            seen[cur] = True
            cycle.append(cur + 1)
            cur = dest[cur] - 1
        if len(cycle) > 1:
            cycles.append(cycle)
    if not cycles:
        return "()"
    return " ".join("(" + " ".join(str(x) for x in c) + ")" for c in cycles)


def _render(braid: Braid) -> str:
    comps = closure_components(braid)
    lines = [
        f"Invariants of {braid.name}:",
        f"  strand count:     {braid.strand_count}",
        f"  word length:      {len(braid.word)}",
        f"  writhe:           {writhe(braid)}",
        f"  permutation:      {permutation(braid)}  (strand at each final position)",
        f"  cycle notation:   {_cycle_notation(permutation_one_line(braid))}",
        f"  closure components: {len(comps)} {comps}",
        f"  linking number:   {linking_number(braid)}  pairwise {linking_matrix(braid)}",
    ]
    if braid.strand_count <= 10:
        lines.append(f"  Alexander Δ(t):   {alexander_polynomial(braid).format('t')}")
    if len(braid.word) <= MAX_STATE_SUM_CROSSINGS:
        lines.append(f"  Jones V(t):       {format_jones(jones_polynomial(braid))}")
    else:
        lines.append("  Jones V(t):       (skipped: too many crossings for the state sum)")
    return "\n".join(lines)


class InvariantView(View):
    level = "L6"
    name = "Invariant"

    def render(self, braid: Braid) -> str:
        return _render(braid)


register(InvariantView())
