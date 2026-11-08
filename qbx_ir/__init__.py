"""
QBX-IR — Quantum Braid Exchange Intermediate Representation.

The canonical IR for braids with 8 equivalent views.
"""

__version__ = "0.2.0"

from qbx_ir.core.primitive import Strand, Generator, Crossing
from qbx_ir.core.braid import Braid
from qbx_ir.core.equality import (
    EqualityKind,
    EqualityResult,
    check_equality,
)

__all__ = [
    "Strand",
    "Generator",
    "Crossing",
    "Braid",
    "EqualityKind",
    "EqualityResult",
    "check_equality",
]
