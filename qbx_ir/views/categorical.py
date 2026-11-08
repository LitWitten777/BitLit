"""
L3 — Categorical view.

Renders the braid as a morphism in a braided monoidal category.
"""

from __future__ import annotations

from qbx_ir.core.braid import Braid
from qbx_ir.views.base import View, register


def _braiding_symbol(i: int, j: int) -> str:
    return f"c_{{{i},{j}}}"


def _render(braid: Braid) -> str:
    n = braid.strand_count
    if not braid.word:
        morphism = f"id_{{V^⊗{n}}}"
    else:
        parts = []
        # Composition is written right-to-left: the first generator is rightmost.
        for g in reversed(braid.word):
            sym = _braiding_symbol(g.index, g.index + 1)
            if g.sign == -1:
                sym += "⁻¹"
            parts.append(sym)
        morphism = " ∘ ".join(parts)
    lines = [
        "Categorical view (braided monoidal category):",
        f"  domain:   V^⊗{n}",
        f"  codomain: V^⊗{n}",
        f"  morphism: {morphism}",
        "",
        "  Interpretation:",
        "    - Objects:  tensor powers V^⊗k",
        "    - Morphisms: braidings c_{i,i+1} = id^{⊗(i-1)} ⊗ c_{V,V} ⊗ id^{⊗(n-i-1)}",
        "    - Braiding satisfies the hexagon axioms (coherence).",
    ]
    return "\n".join(lines)


class CategoricalView(View):
    level = "L3"
    name = "Categorical"

    def render(self, braid: Braid) -> str:
        return _render(braid)


register(CategoricalView())
