"""
src/sedenion/kernel/plugin.py
=============================================================================
Plugin architecture for the Sovereign Universal Memory Kernel.
Enables domain adapters, custom validation rules, and transformation pipelines.
=============================================================================
"""

from abc import ABC, abstractmethod
from typing import Any, Dict, List, Optional, Tuple, TYPE_CHECKING

if TYPE_CHECKING:
    from .memory_kernel import UniversalMemoryKernel


class KernelPlugin(ABC):
    """
    Abstract base class for Sovereign Kernel plugins.
    Allows modular extension of invariants, domain models, and transformations.
    """

    @property
    @abstractmethod
    def name(self) -> str:
        """Unique identifier for this plugin."""
        pass

    def on_attach(self, kernel: "UniversalMemoryKernel") -> None:
        """Lifecycle hook invoked when the plugin is registered to a kernel."""
        pass

    def validate_record(self, record: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """
        Validate a memory record before it is committed to storage.
        Returns (is_valid, error_message).
        """
        return True, None

    def validate_node(self, node: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """
        Validate a symbol graph node before insertion.
        Returns (is_valid, error_message).
        """
        return True, None

    def validate_edge(self, edge: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """
        Validate a symbol graph edge before insertion.
        Returns (is_valid, error_message).
        """
        return True, None

    def transform_record(self, record: Dict[str, Any]) -> Dict[str, Any]:
        """
        Optional deterministic transformation applied to record content/metadata.
        Default is the identity transformation.
        """
        return record
