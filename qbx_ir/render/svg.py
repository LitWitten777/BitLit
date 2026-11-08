"""
SVG renderer (QBX.md §36 Phase 3): a clean 2D braid diagram generated
directly from the IR.  Time flows upward (first generator at the bottom).
For σ_i the strand coming from position i passes *over* (drawn last, with a
white halo); for σ_i⁻¹ the strand from position i+1 passes over.
"""

from __future__ import annotations

from typing import List

from qbx_ir.core.braid import Braid

PALETTE = ["#1f77b4", "#d62728", "#2ca02c", "#9467bd", "#ff7f0e",
           "#17becf", "#8c564b", "#e377c2", "#7f7f7f", "#bcbd22"]


def braid_to_svg(braid: Braid, dx: float = 60.0, dy: float = 60.0,
                 margin: float = 30.0, stroke: float = 4.0) -> str:
    n = braid.strand_count
    m = len(braid.word)
    width = margin * 2 + dx * (n - 1)
    height = margin * 2 + dy * max(m, 1)

    def x(p: int) -> float:  # p: 0-indexed position
        return margin + dx * p

    def y(level: float) -> float:  # level 0 at the bottom
        return height - margin - dy * level

    positions = [s.id for s in braid.strands]
    colour = {s.id: PALETTE[k % len(PALETTE)] for k, s in enumerate(braid.strands)}
    under: List[str] = []
    over: List[str] = []

    def seg(x1, y1, x2, y2, c, halo=False) -> str:
        out = ""
        if halo:
            out += (f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                    f'stroke="white" stroke-width="{stroke * 3:.1f}" stroke-linecap="round"/>')
        out += (f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                f'stroke="{c}" stroke-width="{stroke:.1f}" stroke-linecap="round"/>')
        return out

    if m == 0:
        for p in range(n):
            under.append(seg(x(p), y(0), x(p), y(1), colour[positions[p]]))
    for k, g in enumerate(braid.word):
        i = g.index - 1
        for p in range(n):
            if p not in (i, i + 1):
                under.append(seg(x(p), y(k), x(p), y(k + 1), colour[positions[p]]))
        left, right = positions[i], positions[i + 1]
        up_right = (x(i), y(k), x(i + 1), y(k + 1), colour[left])  # left strand moves right
        up_left = (x(i + 1), y(k), x(i), y(k + 1), colour[right])
        if g.sign == 1:
            under.append(seg(*up_left))
            over.append(seg(*up_right, halo=True))
        else:
            under.append(seg(*up_right))
            over.append(seg(*up_left, halo=True))
        positions[i], positions[i + 1] = right, left

    labels: List[str] = []
    for p, s in enumerate(braid.strands):
        labels.append(f'<text x="{x(p):.1f}" y="{height - 8:.1f}" font-size="14" '
                      f'text-anchor="middle" font-family="monospace">{s.id}</text>')
    title = f"{braid.name}: " + (" ".join(str(g) for g in braid.word) or "ε")
    body = "".join(under) + "".join(over) + "".join(labels)
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{width:.0f}" '
            f'height="{height + 10:.0f}" viewBox="0 0 {width:.0f} {height + 10:.0f}">'
            f"<title>{_escape(title)}</title>"
            f'<rect width="100%" height="100%" fill="white"/>{body}</svg>')


def _escape(s: str) -> str:
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def save_svg(braid: Braid, path: str, **kwargs) -> str:
    svg = braid_to_svg(braid, **kwargs)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(svg)
    return path


