"""Quantum layer: R-matrices, representation ρ, verification."""

from qbx_ir.quantum.exact import (
    ExactMatrix,
    ExactSL2Representation,
    exact_sl2_matrix,
)
from qbx_ir.quantum.r_matrix import (
    PermutationRMatrix,
    RMatrix,
    SL2RMatrix,
    TwistedSwapRMatrix,
)
from qbx_ir.quantum.representation import (
    embed_r,
    jones_from_quantum_trace,
    quantum_trace,
    representation,
)
from qbx_ir.quantum.verify import (
    verify_braid_equality,
    verify_braid_relations,
    verify_yang_baxter,
)

__all__ = [
    "ExactMatrix",
    "ExactSL2Representation",
    "exact_sl2_matrix",
    "RMatrix",
    "SL2RMatrix",
    "TwistedSwapRMatrix",
    "PermutationRMatrix",
    "representation",
    "embed_r",
    "quantum_trace",
    "jones_from_quantum_trace",
    "verify_yang_baxter",
    "verify_braid_relations",
    "verify_braid_equality",
]
