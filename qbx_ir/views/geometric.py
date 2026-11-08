"""
L7 — Geometric view.

Renders the E8 embedding of the braid strands and the geometric cost
D(B) = Σ_crossings ‖x_left − x_right‖².
"""

from __future__ import annotations

from typing import List, Tuple

from qbx_ir.core.braid import Braid
from qbx_ir.views.base import View, register

# A few E8 roots (all of squared norm 2) used as default strand coordinates.
_DEFAULT_ROOTS: List[Tuple[float, ...]] = [
    (1.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0),
    (1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0),
    (1.0, 0.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0),
    (0.0, 1.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0),
    (0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5),
    (-0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5),
]


def default_e8_coord(i: int) -> Tuple[float, ...]:
    """Default E8 coordinate for strand i (cycles through a fixed root list)."""
    return _DEFAULT_ROOTS[(i - 1) % len(_DEFAULT_ROOTS)]


def geometric_cost(braid: Braid) -> float:
    coords = {s.id: (s.geometry if s.geometry is not None else default_e8_coord(s.id))
              for s in braid.strands}
    cost = 0.0
    for c in braid.crossings():
        a, b = coords[c.left_strand_id], coords[c.right_strand_id]
        cost += sum((x - y) ** 2 for x, y in zip(a, b))
    return cost


def _render(braid: Braid) -> str:
    lines = ["Geometric view (E8 embedding):", "  Strand coordinates (in E8):"]
    for s in braid.strands:
        c = s.geometry if s.geometry is not None else default_e8_coord(s.id)
        lines.append(f"    strand {s.id}: [" + ", ".join(f"{x:+.2f}" for x in c) + "]")
    lines.append("")
    lines.append("  Geometric cost D(B) = Σ ||x_i - x_j||²")
    lines.append(f"  D(B) = {geometric_cost(braid):.4f}")
    return "\n".join(lines)


class GeometricView(View):
    level = "L7"
    name = "Geometric"

    def render(self, braid: Braid) -> str:
        return _render(braid)


register(GeometricView())
