"""
multiplierless_kernel.py
========================
Phase 4: Multiplierless Kernel — Zero-GPU Edge Runtime Engine.

Executes graph convolutions, message passing, and state transitions over the
168-node Fano-coupled Ramanujan expander using strictly multiplierless bitwise
shifts, XORs, and integer additions (HYP-203).

Key Mechanics:
  - Pronic Coupling Invariant: Singular values {2, 3} (k=2 -> k(k+1) = 6).
  - Multiplierless Primitives:
      x * 2 = (x << 1)
      x * 3 = (x << 1) + x
      x * 4 = (x << 2)
      x * 8 = (x << 3)
      x * 12 = (x << 3) + (x << 2)
      x * 24 = (x << 4) + (x << 3)
  - Zero-GPU execution: Compatible with bare-metal microcontrollers (ARM Cortex-M,
    ESP32, RISC-V) and custom FPGA logic cells.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple
import numpy as np

from .geometric_lexer import GeometricLexer
from .pencil_grammar import ExpanderGeodesicRouter


@dataclass(frozen=True)
class KernelMetrics:
    num_nodes: int
    intra_edges: int
    inter_edges: int
    total_edges: int
    pronic_singular_values: Tuple[int, int]
    multiplierless: bool


class MultiplierlessKernel:
    """
    Multiplierless integer-shift convolution engine for the 168-vertex
    Fano-coupled Ramanujan expander.
    """

    def __init__(self, router: Optional[ExpanderGeodesicRouter] = None) -> None:
        self.router = router or ExpanderGeodesicRouter()
        self.lexer = self.router.lexer
        self.num_nodes = 168

        # Adjacency lookup tables: node_id -> list of neighbor node_ids
        self.intra_neighbors: List[List[int]] = [[] for _ in range(168)]
        self.inter_neighbors: List[List[int]] = [[] for _ in range(168)]
        self._build_neighbor_tables()

    def _build_neighbor_tables(self) -> None:
        """Extracts separate intra-sector and inter-sector neighbor lists from the graph."""
        G = self.router.graph
        for u in range(168):
            for v, data in G[u].items():
                edge_type = data.get("edge_type", "annihilation")
                if edge_type == "annihilation":
                    self.intra_neighbors[u].append(v)
                else:
                    self.inter_neighbors[u].append(v)

    @property
    def metrics(self) -> KernelMetrics:
        intra_count = sum(len(n) for n in self.intra_neighbors) // 2
        inter_count = sum(len(n) for n in self.inter_neighbors) // 2
        return KernelMetrics(
            num_nodes=self.num_nodes,
            intra_edges=intra_count,
            inter_edges=inter_count,
            total_edges=intra_count + inter_count,
            pronic_singular_values=(2, 3),
            multiplierless=True,
        )

    # -----------------------------------------------------------------------
    # Multiplierless Integer Shift Primitives
    # -----------------------------------------------------------------------

    @staticmethod
    def shift_mult_2(x: int) -> int:
        """Multiplication by 2 via 1-bit left shift: x * 2 = (x << 1)."""
        return x << 1

    @staticmethod
    def shift_mult_3(x: int) -> int:
        """Multiplication by 3 via 1-bit shift and add: x * 3 = (x << 1) + x."""
        return (x << 1) + x

    @staticmethod
    def shift_mult_4(x: int) -> int:
        """Multiplication by 4 via 2-bit left shift: x * 4 = (x << 2)."""
        return x << 2

    @staticmethod
    def shift_mult_8(x: int) -> int:
        """Multiplication by 8 via 3-bit left shift: x * 8 = (x << 3)."""
        return x << 3

    @staticmethod
    def shift_mult_12(x: int) -> int:
        """Multiplication by 12 via shift and add: x * 12 = (x << 3) + (x << 2)."""
        return (x << 3) + (x << 2)

    @staticmethod
    def shift_mult_24(x: int) -> int:
        """Multiplication by 24 via shift and add: x * 24 = (x << 4) + (x << 3)."""
        return (x << 4) + (x << 3)

    # -----------------------------------------------------------------------
    # Graph Convolution Step (Zero Floating-Point Multiplications)
    # -----------------------------------------------------------------------

    def convolve_step(self, state: Sequence[int]) -> List[int]:
        """
        Executes a single discrete graph convolution step:
          y_u = 3 * sum_{v in N_intra(u)} state[v] + 2 * sum_{w in N_inter(u)} state[w]
        using exclusively bitwise shifts and integer additions.
        """
        if len(state) != self.num_nodes:
            raise ValueError(f"State vector must have length {self.num_nodes}, got {len(state)}")

        output = [0] * self.num_nodes

        for u in range(self.num_nodes):
            # Sum intra-sector neighbors (integer adds only)
            intra_sum = 0
            for v in self.intra_neighbors[u]:
                intra_sum += state[v]

            # Sum inter-sector neighbors (integer adds only)
            inter_sum = 0
            for w in self.inter_neighbors[u]:
                inter_sum += state[w]

            # Multiplierless coupling: 3 * intra_sum + 2 * inter_sum
            term_intra = (intra_sum << 1) + intra_sum
            term_inter = inter_sum << 1

            output[u] = term_intra + term_inter

        return output

    def multi_hop_diffusion(self, initial_state: Sequence[int], hops: int = 3) -> List[int]:
        """
        Runs multi-hop graph diffusion for up to diameter bound hops (default D=3).
        """
        current = list(initial_state)
        for _ in range(hops):
            current = self.convolve_step(current)
        return current

    # -----------------------------------------------------------------------
    # C Header Code Generator
    # -----------------------------------------------------------------------

    def generate_c_header(self) -> str:
        """
        Generates a standalone, dependency-free C99 header file implementing
        the multiplierless graph convolution kernel for embedded/bare-metal systems.
        """
        lines = [
            "/*",
            " * multiplierless_kernel.h",
            " * =======================",
            " * Auto-generated Zero-GPU Edge Runtime Kernel for GNL.",
            " * Multiplierless graph convolution over the 168-node Ramanujan expander.",
            " * Invariant: Pronic singular values {2, 3}.",
            " */",
            "",
            "#ifndef MULTIPLIERLESS_KERNEL_H",
            "#define MULTIPLIERLESS_KERNEL_H",
            "",
            "#include <stdint.h>",
            "#include <stddef.h>",
            "",
            "#define GNL_NUM_NODES 168",
            "",
            "/* Shift primitives */",
            "#define SHIFT_MULT_2(x) ((x) << 1)",
            "#define SHIFT_MULT_3(x) (((x) << 1) + (x))",
            "#define SHIFT_MULT_4(x) ((x) << 2)",
            "#define SHIFT_MULT_8(x) ((x) << 3)",
            "#define SHIFT_MULT_12(x) (((x) << 3) + ((x) << 2))",
            "#define SHIFT_MULT_24(x) (((x) << 4) + ((x) << 3))",
            "",
        ]

        # Intra neighbors table
        lines.append("/* Intra-sector neighbor degree counts and adjacency list */")
        intra_flat: List[int] = []
        intra_offsets: List[int] = [0]
        for u in range(168):
            intra_flat.extend(self.intra_neighbors[u])
            intra_offsets.append(len(intra_flat))

        lines.append(f"static const uint16_t gnl_intra_offsets[169] = {{")
        for i in range(0, 169, 12):
            chunk = ", ".join(str(intra_offsets[j]) for j in range(i, min(i + 12, 169)))
            lines.append(f"    {chunk},")
        lines.append("};\n")

        lines.append(f"static const uint8_t gnl_intra_adj[{len(intra_flat)}] = {{")
        for i in range(0, len(intra_flat), 16):
            chunk = ", ".join(str(intra_flat[j]) for j in range(i, min(i + 16, len(intra_flat))))
            lines.append(f"    {chunk},")
        lines.append("};\n")

        # Inter neighbors table
        inter_flat: List[int] = []
        inter_offsets: List[int] = [0]
        for u in range(168):
            inter_flat.extend(self.inter_neighbors[u])
            inter_offsets.append(len(inter_flat))

        lines.append(f"static const uint16_t gnl_inter_offsets[169] = {{")
        for i in range(0, 169, 12):
            chunk = ", ".join(str(inter_offsets[j]) for j in range(i, min(i + 12, 169)))
            lines.append(f"    {chunk},")
        lines.append("};\n")

        lines.append(f"static const uint8_t gnl_inter_adj[{len(inter_flat)}] = {{")
        for i in range(0, len(inter_flat), 16):
            chunk = ", ".join(str(inter_flat[j]) for j in range(i, min(i + 16, len(inter_flat))))
            lines.append(f"    {chunk},")
        lines.append("};\n")

        # C execution function
        lines.extend([
            "/*",
            " * Convolves 168-element state vector in-place or into output buffer.",
            " * Pure integer operations: NO floating point, NO hardware multipliers.",
            " */",
            "static inline void gnl_convolve_step(const int32_t in_state[GNL_NUM_NODES], int32_t out_state[GNL_NUM_NODES]) {",
            "    for (int u = 0; u < GNL_NUM_NODES; ++u) {",
            "        int32_t intra_sum = 0;",
            "        uint16_t intra_start = gnl_intra_offsets[u];",
            "        uint16_t intra_end = gnl_intra_offsets[u + 1];",
            "        for (uint16_t idx = intra_start; idx < intra_end; ++idx) {",
            "            intra_sum += in_state[gnl_intra_adj[idx]];",
            "        }",
            "",
            "        int32_t inter_sum = 0;",
            "        uint16_t inter_start = gnl_inter_offsets[u];",
            "        uint16_t inter_end = gnl_inter_offsets[u + 1];",
            "        for (uint16_t idx = inter_start; idx < inter_end; ++idx) {",
            "            inter_sum += in_state[gnl_inter_adj[idx]];",
            "        }",
            "",
            "        /* 3 * intra_sum + 2 * inter_sum using shifts only */",
            "        out_state[u] = SHIFT_MULT_3(intra_sum) + SHIFT_MULT_2(inter_sum);",
            "    }",
            "}",
            "",
            "#endif /* MULTIPLIERLESS_KERNEL_H */",
            "",
        ])

        return "\n".join(lines)

    def export_c_header(self, destination: str | Path) -> Path:
        """Exports the C99 header to the specified destination path."""
        p = Path(destination)
        p.parent.mkdir(parents=True, exist_ok=True)
        content = self.generate_c_header()
        p.write_text(content, encoding="utf-8")
        return p
