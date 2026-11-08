"""Base class and registry for views."""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Dict, List, Optional

from qbx_ir.core.braid import Braid


class View(ABC):
    """Abstract view of a braid.  Views are pure, total and read-only."""

    level: str
    name: str

    @abstractmethod
    def render(self, braid: Braid) -> str:
        """Render the braid as a string."""


VIEW_REGISTRY: Dict[str, View] = {}


def register(view: View) -> View:
    """Register a view by its level."""
    VIEW_REGISTRY[view.level] = view
    return view


def get_view(level: str) -> Optional[View]:
    return VIEW_REGISTRY.get(level)


def all_views() -> List[View]:
    return [VIEW_REGISTRY[k] for k in sorted(VIEW_REGISTRY.keys())]
