"""
L4 — Anyonic view.

Renders the braid acting on the Fibonacci fusion space: fusion-chain basis,
F/R data and the resulting (unitary) braid matrix.
"""

from __future__ import annotations

import numpy as np

from qbx_ir.anyon import anyon_representation, fibonacci_model, fusion_space
from qbx_ir.core.braid import Braid
from qbx_ir.views.base import View, register

MAX_ANYONS_SHOWN = 7


def _render(braid: Braid) -> str:
    n = braid.strand_count
    model = fibonacci_model()
    lines = [
        "Anyonic view (Fibonacci anyons, τ × τ = 1 + τ):",
        "  R^{ττ}_1 = e^{-4πi/5},  R^{ττ}_τ = e^{3πi/5}",
        "  F^{τττ}_τ = [[φ⁻¹, φ^{-1/2}], [φ^{-1/2}, -φ⁻¹]]",
    ]
    if n > MAX_ANYONS_SHOWN:
        lines.append(f"  ({n} anyons: fusion space too large to display)")
        return "\n".join(lines)
    space = fusion_space(model, "τ", n)
    lines.append(f"  fusion space of {n} τ-anyons: dim = {space.dim} (Fibonacci number)")
    for k, chain in enumerate(space.basis):
        lines.append(f"    |{k}> = " + " → ".join(chain))
    U = anyon_representation(braid, model, "τ")
    unitary = float(np.abs(U.conj().T @ U - np.eye(space.dim)).max()) < 1e-9
    charges = {}
    for k, chain in enumerate(space.basis):
        charges.setdefault(chain[-1], []).append(k)
    lines.append(f"  ρ_Fib(B) unitary: {unitary}; preserves total charge sectors "
                 + ", ".join(f"{c}:{len(v)}" for c, v in charges.items()))
    if space.dim <= 8:
        for row in U:
            lines.append("    [ " + " ".join(f"{z.real:+.3f}{z.imag:+.3f}i" for z in row) + " ]")
    lines.append("  Crossings: " + ", ".join(
        f"σ_{g.index}{'' if g.sign == 1 else '⁻¹'} exchanges τ_{g.index},τ_{g.index + 1}"
        for g in braid.word) if braid.word else "  Crossings: none")
    return "\n".join(lines)


class AnyonicView(View):
    level = "L4"
    name = "Anyonic"

    def render(self, braid: Braid) -> str:
        return _render(braid)


register(AnyonicView())
