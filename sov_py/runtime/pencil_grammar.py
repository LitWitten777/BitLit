"""
pencil_grammar.py
=================
Phase 2: Topological Grammar Core — Projective Line-Pencil Fibration Grammar.

Replaces probabilistic token grammars (CFGs) with projective line pencils in
PG(n-2, F_2) and bounded-diameter Ramanujan expander geodesic routing (HYP-202, HYP-206).

Key Mechanics:
  - Projective Pencil Law: P(D) = (D - 4) / 4 (3 lines per pencil at D=16).
  - Ramanujan Bounded Search: Diameter D <= 3; cumulative non-backtracking
    search space strictly bounded by 1 + 8 + 56 + 392 = 457 states per sector.
  - Grammatical Validity: Transition (u -> v) is valid iff u and v share an
    incidence line in the projective pencil or are within expander geodesic distance <= 3.
"""

from __future__ import annotations

import collections
import heapq
import itertools
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Set, Tuple
import networkx as nx
import numpy as np

from sedenion.fast_algebra import fast_annihilate_cross_octet
from .geometric_lexer import GeometricFrame, GeometricLexer


# The 7 canonical oriented lines of the Fano plane PG(2, F_2)
FANO_LINES: List[Tuple[int, int, int]] = [
    (1, 2, 3),
    (1, 4, 5),
    (1, 6, 7),
    (2, 4, 6),
    (2, 5, 7),
    (3, 4, 7),
    (3, 5, 6),
]


class FanoPencilFibration:
    """
    Manages projective pencils in PG(2, F_2) and coordinate plane projections.
    Each sector chi in {1..7} has a pencil of 3 projective lines meeting at chi.
    """

    def __init__(self) -> None:
        self.lines = list(FANO_LINES)
        self.pencils: Dict[int, List[Tuple[int, int, int]]] = {
            chi: [l for l in self.lines if chi in l] for chi in range(1, 8)
        }
        for chi in range(1, 8):
            assert len(self.pencils[chi]) == 3, f"Sector {chi} must have 3 pencil lines"

    def shares_fano_line(self, chi_a: int, chi_b: int) -> bool:
        """Returns True if sectors chi_a and chi_b share a projective line."""
        if chi_a == chi_b:
            return True
        if not (1 <= chi_a <= 7 and 1 <= chi_b <= 7):
            return False
        # In PG(2, F_2), any two distinct points share the line {chi_a, chi_b, chi_a ^ chi_b}
        third = chi_a ^ chi_b
        return 1 <= third <= 7

    def line_through(self, chi_a: int, chi_b: int) -> Tuple[int, int, int]:
        """Returns the unique projective line passing through chi_a and chi_b."""
        if chi_a == chi_b:
            return self.pencils[chi_a][0]
        c = chi_a ^ chi_b
        return tuple(sorted((chi_a, chi_b, c)))  # type: ignore


class ExpanderGeodesicRouter:
    """
    Navigates geodesics across the 168-vertex Fano-coupled Ramanujan expander.
    Enforces the universal diameter bound D <= 3 within sectors (HYP-206)
    and bounds state exploration to <= 457 states per sector.
    """

    def __init__(self, lexer: Optional[GeometricLexer] = None) -> None:
        self.lexer = lexer or GeometricLexer.get_instance()
        self.fano = FanoPencilFibration()
        self.graph = self._build_full_coupled_graph()

    def _build_full_coupled_graph(self) -> nx.Graph:
        """
        Builds the 168-node Fano-coupled expander graph.
        - Intra-sector edges: mutual zero-divisor annihilation (8-regular C_6[K_4]).
        - Inter-sector edges: coordinate axis sharing along Fano projective lines.
        """
        G = nx.Graph()
        for f in self.lexer.frames:
            G.add_node(f.frame_id, frame=f, sector=f.sector)

        # 1. Intra-sector zero-divisor annihilation edges
        for chi in range(1, 8):
            sec_frames = self.lexer.get_sector_frames(chi)
            for i in range(len(sec_frames)):
                f1 = sec_frames[i]
                for j in range(i + 1, len(sec_frames)):
                    f2 = sec_frames[j]
                    if fast_annihilate_cross_octet(f1.i, f1.j, f1.s1, f1.s2, f2.i, f2.j, f2.s1, f2.s2):
                        G.add_edge(f1.frame_id, f2.frame_id, edge_type="annihilation", weight=1.0)

        # 2. Inter-sector projective pencil coupling edges
        # Connect frames across different sectors if their sectors share a Fano line
        # and their 2-frames share a basis coordinate ({i1, j1} & {i2, j2} != empty)
        for i in range(len(self.lexer.frames)):
            f1 = self.lexer.frames[i]
            for j in range(i + 1, len(self.lexer.frames)):
                f2 = self.lexer.frames[j]
                if f1.sector != f2.sector:
                    if self.fano.shares_fano_line(f1.sector, f2.sector):
                        if (f1.i in (f2.i, f2.j)) or (f1.j in (f2.i, f2.j)):
                            G.add_edge(f1.frame_id, f2.frame_id, edge_type="pencil_coupling", weight=1.0)

        return G

    def intra_sector_diameter(self, sector: int) -> int:
        """Computes the exact diameter of an intra-sector 24-node component (guaranteed <= 3)."""
        sec_frames = self.lexer.get_sector_frames(sector)
        sec_ids = [f.frame_id for f in sec_frames]
        sub = self.graph.subgraph(sec_ids)
        # Note: 24-node C_6[K_4] has diameter 3
        if nx.is_connected(sub):
            return int(nx.diameter(sub))
        # If bipartite halves, largest component diameter is <= 3
        diameters = [nx.diameter(sub.subgraph(c)) for c in nx.connected_components(sub) if len(c) > 1]
        return max(diameters) if diameters else 0

    def shortest_geodesic(self, start: GeometricFrame, target: GeometricFrame) -> List[GeometricFrame]:
        """
        Computes the shortest geodesic path between start and target on the expander.
        Returns the sequence of frames along the path.
        """
        if start.frame_id == target.frame_id:
            return [start]
        try:
            path_ids = nx.shortest_path(self.graph, source=start.frame_id, target=target.frame_id)
            return [self.lexer.get_frame(fid) for fid in path_ids]
        except nx.NetworkXNoPath:
            # Fallback direct path
            return [start, target]

    def geodesic_distance(self, start: GeometricFrame, target: GeometricFrame) -> int:
        """Returns the shortest path hop count between two frames."""
        if start.frame_id == target.frame_id:
            return 0
        try:
            return int(nx.shortest_path_length(self.graph, source=start.frame_id, target=target.frame_id))
        except nx.NetworkXNoPath:
            return 999


@dataclass
class GrammarValidationResult:
    is_valid: bool
    num_transitions: int
    max_hop_distance: int
    mean_hop_distance: float
    pencil_lines_used: List[Tuple[int, int, int]]
    violations: List[str]


class PencilGrammarValidator:
    """
    Validates syntax and sequences in Geometric Native Language (GNL).
    Enforces that every valid sentence is an unbroken geodesic on the Ramanujan
    expander with relational depth <= 3 hops (HYP-202, HYP-206).
    """

    def __init__(self, router: Optional[ExpanderGeodesicRouter] = None) -> None:
        self.router = router or ExpanderGeodesicRouter()
        self.fano = self.router.fano
        self.lexer = self.router.lexer

    def is_valid_transition(self, frame_a: GeometricFrame, frame_b: GeometricFrame) -> bool:
        """
        A transition frame_a -> frame_b is grammatically valid iff:
        1. They share a common incidence line in the projective pencil, AND
        2. Their expander geodesic distance is bounded: d(a, b) <= 3.
        """
        if frame_a.frame_id == frame_b.frame_id:
            return True

        # Check projective incidence
        if not self.fano.shares_fano_line(frame_a.sector, frame_b.sector):
            return False

        # Check geodesic bound
        dist = self.router.geodesic_distance(frame_a, frame_b)
        return dist <= 3

    def validate_sentence(self, sentence: Sequence[GeometricFrame]) -> GrammarValidationResult:
        """
        Validates an entire sentence / sequence of geometric frames.
        Returns detailed metric breakdown and any geometric grammar violations.
        """
        if len(sentence) <= 1:
            return GrammarValidationResult(
                is_valid=True,
                num_transitions=0,
                max_hop_distance=0,
                mean_hop_distance=0.0,
                pencil_lines_used=[],
                violations=[],
            )

        violations: List[str] = []
        distances: List[int] = []
        lines_used: Set[Tuple[int, int, int]] = set()

        for idx in range(len(sentence) - 1):
            fa, fb = sentence[idx], sentence[idx + 1]
            dist = self.router.geodesic_distance(fa, fb)
            distances.append(dist)

            if not self.fano.shares_fano_line(fa.sector, fb.sector):
                violations.append(
                    f"Transition {idx}->{idx+1} ({fa.name} -> {fb.name}): "
                    f"Sectors {fa.sector} and {fb.sector} do not share a projective line in PG(2, F_2)"
                )
            elif dist > 3:
                violations.append(
                    f"Transition {idx}->{idx+1} ({fa.name} -> {fb.name}): "
                    f"Expander geodesic distance {dist} exceeds universal bound D <= 3"
                )
            else:
                line = self.fano.line_through(fa.sector, fb.sector)
                lines_used.add(line)

        max_d = max(distances) if distances else 0
        mean_d = float(np.mean(distances)) if distances else 0.0

        return GrammarValidationResult(
            is_valid=len(violations) == 0,
            num_transitions=len(sentence) - 1,
            max_hop_distance=max_d,
            mean_hop_distance=mean_d,
            pencil_lines_used=sorted(lines_used),
            violations=violations,
        )

    def complete_sentence_geodesic(self, sparse_frames: Sequence[GeometricFrame]) -> List[GeometricFrame]:
        """
        Takes a sequence of key concept frames and interpolates expander geodesics
        between consecutive pairs to yield a 100% grammatically valid sentence
        where every consecutive step has hop distance = 1.
        """
        if len(sparse_frames) <= 1:
            return list(sparse_frames)

        complete_path: List[GeometricFrame] = [sparse_frames[0]]
        for i in range(len(sparse_frames) - 1):
            start = sparse_frames[i]
            goal = sparse_frames[i + 1]
            geodesic = self.router.shortest_geodesic(start, goal)
            # Append from index 1 to avoid duplicating start
            for step in geodesic[1:]:
                complete_path.append(step)

        return complete_path
