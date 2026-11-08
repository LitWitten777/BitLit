"""
L1 — Graphical view.

Renders a string-diagram-inspired ASCII with labeled morphism boxes.
Where L0 shows the geometry, L1 shows the composition structure.
"""

from __future__ import annotations

from qbx_ir.core.braid import Braid
from qbx_ir.views.base import View, register


def _render(braid: Braid) -> str:
    n = braid.strand_count
    lines = [
        f"String diagram: {braid.name}",
        f"  Object: V^⊗{n}",
        f"  Morphism: V^⊗{n} → V^⊗{n}",
        "",
    ]
    if not braid.word:
        for i in range(n):
            lines.append(f"  [{i + 1}] " + "─" * 40 + " wire")
        return "\n".join(lines)
    for k, g in enumerate(braid.word):
        sign_label = "+" if g.sign == 1 else "−"
        lines.append(f"  ── step {k + 1}: c_({g.index},{g.index + 1}) [{sign_label}] ──")
        for i in range(1, n + 1):
            marker = "→" if i in (g.index, g.index + 1) else " "
            lines.append(f"       [{i}] {marker}")
        lines.append("")
    lines.append(f"  Total morphisms: {len(braid.word)}")
    return "\n".join(lines)


class GraphicalView(View):
    level = "L1"
    name = "Graphical"

    def render(self, braid: Braid) -> str:
        return _render(braid)


register(GraphicalView())
