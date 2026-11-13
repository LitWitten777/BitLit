"""
src/sedenion/runtime
====================
Geometric Cognitive Runtime and Geometric Native Language (GNL) based on
sedenion zero-divisor 2-frames, projective pencil grammar, Čech cohomology
hallucination suppression, and multiplierless integer kernels.
"""

from .geometric_lexer import GeometricFrame, GeometricLexer
from .pencil_grammar import PencilGrammarValidator, ExpanderGeodesicRouter
from .cohomology_gate import CohomologyGate, CohomologyReport
from .multiplierless_kernel import MultiplierlessKernel
from .adaptive_engine import AdaptiveHypernetworkEngine
from .geometric_runtime import GeometricCognitiveRuntime

__all__ = [
    "GeometricFrame",
    "GeometricLexer",
    "PencilGrammarValidator",
    "ExpanderGeodesicRouter",
    "CohomologyGate",
    "CohomologyReport",
    "MultiplierlessKernel",
    "AdaptiveHypernetworkEngine",
    "GeometricCognitiveRuntime",
]
