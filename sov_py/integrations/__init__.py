"""
integrations — External research platform & physical hardware integrations.
"""

from .blockchain_ledger import BlockchainLedger, BlockHeader
from .esp32_coprocessor import ESP32Coprocessor, ESP32Telemetry
from .esp32_quantum_entropy import (
    FANO_LINES,
    FANO_STABILIZER_H,
    ESP32PhysicalEntropyHarvester,
    FanoCollapseResult,
    FanoQuantumStabilizerEngine,
)
from .veilbreak import VeilbreakClient, load_api_key_from_env_file

__all__ = [
    "BlockchainLedger",
    "BlockHeader",
    "VeilbreakClient",
    "load_api_key_from_env_file",
    "ESP32PhysicalEntropyHarvester",
    "FanoQuantumStabilizerEngine",
    "FanoCollapseResult",
    "FANO_LINES",
    "FANO_STABILIZER_H",
    "ESP32Coprocessor",
    "ESP32Telemetry",
]
