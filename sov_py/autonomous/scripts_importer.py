"""Helper to dynamically import harvester scripts from .agents/skills."""

import importlib.util
from pathlib import Path
from typing import Any


def get_harvester() -> Any:
    """Import and return the arxiv_harvester module."""
    script_path = Path("/home/roku/Jubilant_Computing_Machine/.agents/skills/research-to-lean4/scripts/arxiv_harvester.py")
    spec = importlib.util.spec_from_file_location("arxiv_harvester", str(script_path))
    if spec is None or spec.loader is None:
        raise ImportError(f"Cannot load harvester from {script_path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod
