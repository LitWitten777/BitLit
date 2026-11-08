"""
L5 — Quantum view.

Renders the matrix representation ρ(B) for the U_q(sl_2) Ř-matrix.
"""

from __future__ import annotations

from qbx_ir.core.braid import Braid
from qbx_ir.quantum import SL2RMatrix, representation
from qbx_ir.views.base import View, register

Q_DEFAULT = 2.0
MAX_STRANDS = 8


def _format_complex(z: complex, width: int = 10) -> str:
    re, im = z.real, z.imag
    if abs(im) < 1e-9:
        return f"{re:.4f}".rjust(width)
    if abs(re) < 1e-9:
        return f"{im:+.4f}i".rjust(width)
    return f"{re:.3f}{im:+.3f}i".rjust(width)


def _render(braid: Braid) -> str:
    if braid.strand_count > MAX_STRANDS:
        return f"Quantum view unavailable: {braid.strand_count} strands exceeds {MAX_STRANDS}"
    R = SL2RMatrix(q=Q_DEFAULT)
    U = representation(braid, R)
    lines = [
        f"Quantum view (U_q(sl_2), q={Q_DEFAULT}, dim V = 2):",
        f"  Operator ρ(B): {U.shape[0]}×{U.shape[1]} matrix",
        f"  Tensor power: V^⊗{braid.strand_count}",
        "",
    ]
    max_rows = min(U.shape[0], 8)
    max_cols = min(U.shape[1], 8)
    for i in range(max_rows):
        lines.append("  [ " + " ".join(_format_complex(U[i, j]) for j in range(max_cols)) + " ]")
    if U.shape[0] > max_rows or U.shape[1] > max_cols:
        lines.append(f"  ... (truncated, full shape {U.shape})")
    return "\n".join(lines)


class QuantumView(View):
    level = "L5"
    name = "Quantum"

    def render(self, braid: Braid) -> str:
        return _render(braid)


register(QuantumView())
