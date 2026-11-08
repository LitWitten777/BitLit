"""
The 8 views (L0–L7) of a Braid.

Each view is a pure function from Braid → str. All views are total:
every braid produces a valid render.

Usage:
    from qbx_ir.views import render_all, render
    views = render_all(B)       # all 8 views
    top = render(B, "L0")       # just the topological view
"""

from __future__ import annotations

from typing import Dict, List, Optional

from qbx_ir.core.braid import Braid
from qbx_ir.views.base import VIEW_REGISTRY, View, all_views, get_view

# Import all view modules to register them
from qbx_ir.views import topological  # noqa: F401,E402
from qbx_ir.views import graphical  # noqa: F401,E402
from qbx_ir.views import algebraic  # noqa: F401,E402
from qbx_ir.views import categorical  # noqa: F401,E402
from qbx_ir.views import anyonic  # noqa: F401,E402
from qbx_ir.views import quantum_view  # noqa: F401,E402
from qbx_ir.views import invariant  # noqa: F401,E402
from qbx_ir.views import geometric  # noqa: F401,E402


def render(braid: Braid, level: str) -> str:
    """Render a single view."""
    view = get_view(level)
    if view is None:
        raise ValueError(f"Unknown view level: {level}")
    return view.render(braid)


def render_all(
    braid: Braid,
    levels: Optional[List[str]] = None,
) -> Dict[str, str]:
    """Render multiple views. If levels is None, renders all."""
    if levels is None:
        levels = [v.level for v in all_views()]
    return {level: render(braid, level) for level in levels}


__all__ = [
    "View",
    "get_view",
    "all_views",
    "VIEW_REGISTRY",
    "render",
    "render_all",
]
