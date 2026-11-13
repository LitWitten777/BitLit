"""
src/sedenion/kernel/poincare_loader.py
=============================================================================
Poincare Manifold Dataset Ingestor and Loader for UniversalMemoryKernel.
Parses, validates, and indexes healed Poincare disk/ball and Hopf fibration
geometric records into the persistent memory kernel.
=============================================================================
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterator, List, Optional, Tuple
import numpy as np

from .memory_kernel import UniversalMemoryKernel


@dataclass(frozen=True)
class PoincareManifoldRecord:
    """Represents a validated geometric record from a Poincare healed manifold."""
    record_type: str
    timestamp: float
    record_hash: str
    poincare_disk: Tuple[float, float, float]
    hopf_quaternion_s3: Tuple[float, float, float, float]
    hopf_sphere_s2: Tuple[float, float, float]
    vector_8d: Tuple[float, float, float, float, float, float, float, float]
    curtis_nodal_ratio: float
    stability: str
    gap_cell: Tuple[int, int]

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> PoincareManifoldRecord:
        pd = tuple(float(x) for x in data["poincare_disk"])
        hq = tuple(float(x) for x in data["hopf_quaternion_s3"])
        hs = tuple(float(x) for x in data["hopf_sphere_s2"])
        v8 = tuple(float(x) for x in data["vector_8d"])
        gc = tuple(int(x) for x in data["gap_cell"])

        if len(pd) != 3:
            raise ValueError(f"Expected 3D Poincare disk tuple, got {len(pd)}")
        if len(hq) != 4:
            raise ValueError(f"Expected 4D quaternion, got {len(hq)}")
        if len(hs) != 3:
            raise ValueError(f"Expected 3D sphere coordinate, got {len(hs)}")
        if len(v8) != 8:
            raise ValueError(f"Expected 8D vector, got {len(v8)}")
        if len(gc) != 2:
            raise ValueError(f"Expected 2D gap cell, got {len(gc)}")

        return cls(
            record_type=str(data.get("type", "POINCARE_MANIFOLD_HEAL")),
            timestamp=float(data.get("timestamp", 0.0)),
            record_hash=str(data.get("hash", "")),
            poincare_disk=pd,  # type: ignore
            hopf_quaternion_s3=hq,  # type: ignore
            hopf_sphere_s2=hs,  # type: ignore
            vector_8d=v8,  # type: ignore
            curtis_nodal_ratio=float(data.get("curtis_nodal_ratio", 0.0)),
            stability=str(data.get("stability", "UNKNOWN")),
            gap_cell=gc,  # type: ignore
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "type": self.record_type,
            "timestamp": self.timestamp,
            "hash": self.record_hash,
            "poincare_disk": list(self.poincare_disk),
            "hopf_quaternion_s3": list(self.hopf_quaternion_s3),
            "hopf_sphere_s2": list(self.hopf_sphere_s2),
            "vector_8d": list(self.vector_8d),
            "curtis_nodal_ratio": self.curtis_nodal_ratio,
            "stability": self.stability,
            "gap_cell": list(self.gap_cell),
        }


def stream_poincare_manifold_file(file_path: str | Path) -> Iterator[PoincareManifoldRecord]:
    """Streams and yields PoincareManifoldRecords line by line from a JSONL file."""
    p = Path(file_path)
    if not p.exists():
        raise FileNotFoundError(f"Poincare manifold file not found: {p}")

    with p.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            data = json.loads(line)
            yield PoincareManifoldRecord.from_dict(data)


def load_poincare_manifold_file(
    file_path: str | Path,
    limit: Optional[int] = None,
) -> List[PoincareManifoldRecord]:
    """Loads a list of PoincareManifoldRecords up to an optional limit."""
    records: List[PoincareManifoldRecord] = []
    for rec in stream_poincare_manifold_file(file_path):
        records.append(rec)
        if limit is not None and len(records) >= limit:
            break
    return records


def ingest_poincare_manifold(
    kernel: UniversalMemoryKernel,
    file_path: str | Path,
    limit: Optional[int] = None,
    connect_grid_neighbors: bool = True,
) -> Dict[str, int]:
    """
    Ingests manifold records into the UniversalMemoryKernel:
    - Stores records addressed by SHA-256 CID.
    - Indexes 8D coordinates into the geometric spatial index.
    - Constructs relational grid edges between adjacent gap cells in SymbolGraph.
    """
    records = load_poincare_manifold_file(file_path, limit=limit)
    cell_to_id: Dict[Tuple[int, int], str] = {}
    stored_count = 0
    edges_count = 0

    for rec in records:
        node_id = f"poincare:{rec.gap_cell[0]}_{rec.gap_cell[1]}"
        cell_to_id[rec.gap_cell] = node_id

        # Store in kernel with content-addressing
        meta = {
            "type": rec.record_type,
            "stability": rec.stability,
            "curtis_nodal_ratio": rec.curtis_nodal_ratio,
            "probability": min(max(rec.curtis_nodal_ratio, 0.0), 1.0),
            "poincare_disk": list(rec.poincare_disk),
            "hopf_sphere_s2": list(rec.hopf_sphere_s2),
        }
        kernel.store(
            content=rec.to_dict(),
            key=node_id,
            coordinates=list(rec.vector_8d),
            metadata=meta,
        )
        kernel.register_symbol(
            node_id=node_id,
            label=f"GapCell_{rec.gap_cell[0]}_{rec.gap_cell[1]}",
            coordinates=list(rec.vector_8d),
            attributes=meta,
        )
        stored_count += 1

    if connect_grid_neighbors:
        # Link horizontal and vertical grid neighbors in SymbolGraph
        for cell, nid in cell_to_id.items():
            r, c = cell
            # Right neighbor
            right = (r, c + 1)
            if right in cell_to_id:
                kernel.link_symbols(nid, cell_to_id[right], relation="grid_east", weight=1.0)
                edges_count += 1
            # Down neighbor
            down = (r + 1, c)
            if down in cell_to_id:
                kernel.link_symbols(nid, cell_to_id[down], relation="grid_south", weight=1.0)
                edges_count += 1

    return {
        "records_loaded": len(records),
        "records_stored": stored_count,
        "grid_edges_linked": edges_count,
    }
