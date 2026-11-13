"""
src/sedenion/kernel
=============================================================================
Sovereign Universal Memory Kernel v1.0 Package Interface.
=============================================================================
"""

from .storage import KernelStorage
from .plugin import KernelPlugin
from .symbol_graph import SymbolGraph
from .memory_kernel import UniversalMemoryKernel
from .crucible_plugin import CrucibleKernelPlugin
from .poincare_loader import (
    PoincareManifoldRecord,
    load_poincare_manifold_file,
    stream_poincare_manifold_file,
    ingest_poincare_manifold,
)

from .transitions import (
    StateTransition,
    ValidationRule,
    MerkleTree,
    MerkleStateBlock,
    DeterministicLedger,
    canonical_json_bytes,
    sha256_hex,
)

__all__ = [
    "KernelStorage",
    "KernelPlugin",
    "SymbolGraph",
    "UniversalMemoryKernel",
    "CrucibleKernelPlugin",
    "PoincareManifoldRecord",
    "load_poincare_manifold_file",
    "stream_poincare_manifold_file",
    "ingest_poincare_manifold",
    "StateTransition",
    "ValidationRule",
    "MerkleTree",
    "MerkleStateBlock",
    "DeterministicLedger",
    "canonical_json_bytes",
    "sha256_hex",
]
