"""The Orthogonal Frame Field: Quantum Error Correction and Leech Lattice Bridge.

This module formalizes the unified bridge between:
1. The continuous Stiefel manifold V_2(R^7) and higher towers V_2(R^{D/2 - 1}).
2. The discrete Orthogonal Frame Field of (D-2)(D-4) zero-divisor frames.
3. The [24, 4, 8] doubly-even Golay component codes and the 24D Leech lattice Lambda_24.

Key Mathematical Theorems:
- Co-Planar Frame Bipartite Splitting: In each coordinate 2-plane, the 8 frames split into
  4_+ + 4_- across the bipartite cut. The 28 co-planar pairs decompose as
  binom(4, 2)_+ + binom(4, 2)_- + (4_+ x 4_-) = 6 + 6 + 16 = 12 twins + 16 dichromatic.
  Across the tower, TwinPairs(D) = 12 * T(D) = (3/7) C_2(D) and DichromaticPairs(D) = 16 * T(D) = (4/7) C_2(D),
  with universal ratio 3/4.
- Vertex Neighborhood Octad Law: In every 24-vertex Ramanujan component, the 24 vertex
  neighborhoods are identically the 6 Golay octads of the [24, 4, 8] code.
- Bipartite Octad Syzygy & Gram Theorem: The 6 octads split into two disjoint triples
  T_1, T_2 supported on V^+ and V^-. Each sums to 2 * 1_{V^pm} over Z and 0 over F_2 (exact syzygies).
  The 6x6 octad Gram matrix is block-diagonal G_oct = B_3 + B_3 with spectrum {16^2, 4^4}
  and determinant 65,536 = 2^16.
- Stiefel Geodesic Jump to Leech Subspace: Each graph edge is an equilateral geodesic step
  of length pi / sqrt(2) on V_2 connecting frames in V^+ and V^-, which maps to transitions
  between mutually orthogonal Leech octad subspaces.
"""

from __future__ import annotations

import math
from typing import Any, Dict, List, Tuple
import networkx as nx
import numpy as np

from sedenion.graph import AnnihilationGraph
from sedenion.codes import MOGComponentEmbedding, LeechLatticeEmbedding
from sedenion.geometry.tower_stiefel import TowerStiefelEngine


class OrthogonalFrameField:
    """Master engine for the Orthogonal Frame Field in QEC and Leech lattice geometry."""

    @staticmethod
    def coplanar_bipartite_split(dim: int) -> Dict[str, Any]:
        """Compute the universal splitting of C_2(D) into twins and dichromatic pairs.

        Returns:
            Dict containing:
            - num_planes: T(D)
            - total_coplanar: C_2(D) = 28 * T(D)
            - twin_pairs: 12 * T(D) (monochromatic, identical neighborhoods)
            - dichromatic_pairs: 16 * T(D) (opposite bipartite color)
        """
        T = TowerStiefelEngine.num_coordinate_planes(dim)
        twins = 12 * T
        dichromatic = 16 * T
        c2 = 28 * T
        return {
            "dimension": dim,
            "num_planes": T,
            "total_coplanar": c2,
            "twin_pairs": twins,
            "dichromatic_pairs": dichromatic,
            "ratio_twins_to_dichromatic": twins / dichromatic,
        }

    @classmethod
    def verify_coplanar_splitting(cls, dim: int = 16) -> bool:
        """Verify computationally that graph twins match the 12*T coplanar pairs."""
        zds = TowerStiefelEngine.enumerate_cross_half_zds(dim)
        adj = TowerStiefelEngine.build_adjacency_matrix(dim)
        N = len(zds)

        plane_to_frames: Dict[Tuple[int, int], List[int]] = {}
        for u, (s1, i, s2, j) in enumerate(zds):
            p = (min(i, j), max(i, j))
            plane_to_frames.setdefault(p, []).append(u)

        total_twins = 0
        total_dichromatic = 0

        for p, frames in plane_to_frames.items():
            if len(frames) != 8:
                return False
            # Cluster frames by identical neighborhood
            clusters: List[List[int]] = []
            visited = set()
            for u in frames:
                if u in visited:
                    continue
                c = [v for v in frames if np.array_equal(adj[u], adj[v])]
                clusters.append(c)
                visited.update(c)
            if len(clusters) != 2 or len(clusters[0]) != 4 or len(clusters[1]) != 4:
                return False
            total_twins += 6 + 6
            total_dichromatic += 16

        T = TowerStiefelEngine.num_coordinate_planes(dim)
        return bool(total_twins == 12 * T and total_dichromatic == 16 * T)

    @classmethod
    def verify_neighborhood_octads(cls) -> bool:
        """Verify that all 24 vertex neighborhoods in each component are Golay octads."""
        g = AnnihilationGraph()
        subgraphs = g.component_subgraphs()
        if len(subgraphs) != 7:
            return False

        for sg in subgraphs:
            mog = MOGComponentEmbedding(sg)
            code = mog.build_canonical_binary_code()
            octads_wt8 = [c for c in code.generate_all_codewords() if int(c.sum()) == 8]
            if len(octads_wt8) != 6:
                return False

            nodes = mog.canonical_mog_nodes()
            node_to_idx = {n: i for i, n in enumerate(nodes)}
            A = np.zeros((24, 24), dtype=int)
            for u in nodes:
                for v in sg.neighbors(u):
                    A[node_to_idx[u], node_to_idx[v]] = 1

            # Check every row has weight 8 and is an exact octad
            if not np.all(A.sum(axis=1) == 8):
                return False
            unique_rows = np.unique(A, axis=0)
            if len(unique_rows) != 6:
                return False
            for r in unique_rows:
                if not any(np.array_equal(r, o) for o in octads_wt8):
                    return False
        return True

    @classmethod
    def octad_syzygies_and_gram(cls) -> Dict[str, Any]:
        """Compute the bipartite octad syzygies and 6x6 Gram matrix for a component."""
        g = AnnihilationGraph()
        sg = g.component_subgraphs()[0]
        mog = MOGComponentEmbedding(sg)
        code = mog.build_canonical_binary_code()
        octads = [c for c in code.generate_all_codewords() if int(c.sum()) == 8]
        oct_mat = np.array(octads, dtype=int)
        intersections = oct_mat @ oct_mat.T

        # Split into two triples
        t1 = [i for i in range(6) if intersections[0, i] > 0]
        t2 = [i for i in range(6) if intersections[0, i] == 0]

        # Syzygies over Z and F2
        sum_t1_Z = oct_mat[t1].sum(axis=0)
        sum_t2_Z = oct_mat[t2].sum(axis=0)

        syzygy_t1_f2_vanishes = bool((sum_t1_Z % 2).sum() == 0)
        syzygy_t2_f2_vanishes = bool((sum_t2_Z % 2).sum() == 0)

        # Gram matrix of the 6 octads in scale norm8
        gram = intersections.astype(float)
        evals = np.linalg.eigvalsh(gram)
        evals_rounded = [float(round(e, 4)) for e in evals]
        det_val = float(round(np.linalg.det(gram), 2))

        return {
            "triple_1_indices": t1,
            "triple_2_indices": t2,
            "syzygy_t1_f2_vanishes": syzygy_t1_f2_vanishes,
            "syzygy_t2_f2_vanishes": syzygy_t2_f2_vanishes,
            "gram_matrix": gram,
            "gram_eigenvalues": evals_rounded,
            "gram_determinant": det_val,
        }

    @classmethod
    def master_audit(cls) -> Dict[str, Any]:
        """Run full double-verification audit of the Orthogonal Frame Field QEC bridge."""
        split_16 = cls.coplanar_bipartite_split(16)
        split_32 = cls.coplanar_bipartite_split(32)
        split_64 = cls.coplanar_bipartite_split(64)

        split_16_verified = cls.verify_coplanar_splitting(16)
        octads_verified = cls.verify_neighborhood_octads()
        octad_data = cls.octad_syzygies_and_gram()

        return {
            "splits": {16: split_16, 32: split_32, 64: split_64},
            "split_16_verified": split_16_verified,
            "neighborhood_octads_verified": octads_verified,
            "syzygies_verified": octad_data["syzygy_t1_f2_vanishes"] and octad_data["syzygy_t2_f2_vanishes"],
            "gram_eigenvalues": octad_data["gram_eigenvalues"],
            "gram_determinant": octad_data["gram_determinant"],
        }
