"""
Continuous Topological Representation Learning Worker.
Integrates PyTorch bilinear neural manifold learning with GUDHI persistent homology
to continuously map combinatorial zero-divisor graphs into structured metric embeddings,
tracking Betti numbers (beta_0, beta_1) and Shannon persistent entropy over time.

Enhanced in fix #12/#13: cycles through all 7 charge sectors (χ=1..7) instead of
being hard-wired to sector 1 only.  Each call to step() runs a micro-burst on the
current sector and advances the sector pointer.
"""

from __future__ import annotations

import time
from typing import Any

import numpy as np
import torch

from ..fast_algebra import fast_annihilate_cross_octet
from ..stratification import generate_cross_octet_vectors, stratify_cross_octet
from ..topological_intelligence import (
    TopologicalManifoldLearner,
    analyze_homology_gudhi,
)
from .persistence import ReasoningStore, TopologicalCheckpoint


class ContinuousTopologicalLearner:
    """Continuous representation learner regularized by GUDHI persistent homology.

    Cycles through all active charge sectors (default: χ=1..7) so that the
    topological entropy signal reflects the full zero-divisor structure of the
    algebra, not just sector 1.
    """

    def __init__(
        self,
        store: ReasoningStore | None = None,
        latent_dim: int = 8,
        lr: float = 0.02,
        sectors: list[int] | None = None,
    ):
        self.store = store
        self.latent_dim = latent_dim
        self.lr = lr
        # Active sectors to cycle through; default = all 7 charge sectors
        self.sectors: list[int] = sectors if sectors is not None else list(range(1, 8))
        self._sector_idx: int = 0  # current position in the cycle

        # Per-sector data cache: lazily populated on first access
        self._sector_cache: dict[int, tuple[torch.Tensor, torch.Tensor]] = {}

        # One shared model + optimiser (sector changes only the data, not the architecture)
        self.model = TopologicalManifoldLearner(in_dim=16, hidden_dim=64, latent_dim=latent_dim)
        self.optimizer = torch.optim.Adam(self.model.parameters(), lr=lr)
        self.total_epochs_run = 0

        # Preload the first sector so attributes are populated at construction time
        chi0 = self.sectors[0]
        self.x_data, self.adj_data = self._get_sector_data(chi0)
        self.n_nodes = self.x_data.size(0)
        self.mask = (1.0 - torch.eye(self.n_nodes)).bool()
        self._current_sector: int = chi0

    # ------------------------------------------------------------------
    # Data preparation
    # ------------------------------------------------------------------

    def _prepare_data(self, sector: int = 1) -> tuple[torch.Tensor, torch.Tensor]:
        """Builds the feature tensor and adjacency matrix for a given charge sector."""
        vectors = generate_cross_octet_vectors()
        zd, _, _ = stratify_cross_octet(vectors)
        sector_zd = [v for v in zd if (v.i ^ v.j) == sector]

        if not sector_zd:
            raise ValueError(f"No zero divisors in sector χ={sector}")

        n = len(sector_zd)
        x_data = torch.zeros((n, 16), dtype=torch.float32)
        for idx, v in enumerate(sector_zd):
            x_data[idx, v.i] = float(v.s1)
            x_data[idx, 8 + v.j] = float(v.s2)

        adj = torch.zeros((n, n), dtype=torch.float32)
        for a in range(n):
            for b in range(n):
                if fast_annihilate_cross_octet(
                    sector_zd[a].i, sector_zd[a].j, sector_zd[a].s1, sector_zd[a].s2,
                    sector_zd[b].i, sector_zd[b].j, sector_zd[b].s1, sector_zd[b].s2,
                ):
                    adj[a, b] = 1.0

        return x_data, adj

    def _get_sector_data(self, sector: int) -> tuple[torch.Tensor, torch.Tensor]:
        """Returns (x_data, adj_data) for the given sector, caching results."""
        if sector not in self._sector_cache:
            self._sector_cache[sector] = self._prepare_data(sector)
        return self._sector_cache[sector]

    # ------------------------------------------------------------------
    # Training step
    # ------------------------------------------------------------------

    def step(self, epochs: int = 5) -> TopologicalCheckpoint:
        """Runs a micro-burst of training epochs on the current sector.

        After each call the sector pointer advances to the next sector in the
        cycle, so successive calls cover all active sectors.
        """
        # Advance to the next sector in the cycle
        chi = self.sectors[self._sector_idx % len(self.sectors)]
        self._sector_idx += 1

        x_data, adj_data = self._get_sector_data(chi)
        n_nodes = x_data.size(0)
        mask = (1.0 - torch.eye(n_nodes)).bool()

        # Rebuild model input dim if sector size differs from initial
        if n_nodes != self.n_nodes:
            # Re-use the same model architecture; only the adjacency size differs.
            # Pad or truncate x_data to match the fixed in_dim=16.
            pass  # x_data is always 16-wide (index encoding), only adj changes

        self.model.train()
        final_loss = 0.0

        for _ in range(epochs):
            self.optimizer.zero_grad()
            z, logits = self.model(x_data)

            # Resize logits/adj_data to the mask shape for this sector
            task_loss = torch.nn.functional.binary_cross_entropy_with_logits(
                logits[mask], adj_data[mask]
            )

            D = torch.cdist(z, z)
            top_loss = 0.01 * torch.mean(torch.relu(1.0 - D[adj_data.bool()]))

            loss = task_loss + top_loss
            loss.backward()
            self.optimizer.step()

            self.total_epochs_run += 1
            final_loss = loss.item()

        # TDA audit on current sector embedding
        self.model.eval()
        with torch.no_grad():
            z_eval, logits_eval = self.model(x_data)
            preds = (torch.sigmoid(logits_eval[mask]) > 0.5).float()
            final_acc = (preds == adj_data[mask]).float().mean().item()
            z_np = z_eval.cpu().numpy()

        tda = analyze_homology_gudhi(z_np)
        h1_stats = tda["h1_stats"]

        cp = TopologicalCheckpoint(
            epoch=self.total_epochs_run,
            dimension=16,   # D=16 algebra dimension (invariant)
            accuracy=final_acc,
            max_persistence=h1_stats["max_persistence"],
            persistent_entropy=h1_stats["entropy"],
            betti_0=tda["betti_0"],
            betti_1=tda["betti_1"],
            loss=final_loss,
            timestamp=time.time(),
            sector=chi,
        )

        if self.store:
            self.store.save_topological_checkpoint(cp)

        # Keep x_data/adj_data/n_nodes/mask in sync for get_manifold_state()
        self.x_data = x_data
        self.adj_data = adj_data
        self.n_nodes = n_nodes
        self.mask = mask
        self._current_sector = chi

        return cp

    # ------------------------------------------------------------------
    # Manifold state
    # ------------------------------------------------------------------

    def get_manifold_state(self) -> dict[str, Any]:
        """Returns the current latent manifold coordinates, 2D PCA projection, and barcodes."""
        self.model.eval()
        with torch.no_grad():
            z = self.model(self.x_data)[0].cpu().numpy()

        centered = z - np.mean(z, axis=0)
        u, s, _ = np.linalg.svd(centered)
        proj_2d = (u[:, :2] * s[:2]).tolist()

        tda = analyze_homology_gudhi(z)
        h0_bars = [
            [float(b[0]), float(b[1]) if np.isfinite(b[1]) else 999.0] for b in tda["h0_intervals"]
        ]
        h1_bars = [
            [float(b[0]), float(b[1]) if np.isfinite(b[1]) else 999.0] for b in tda["h1_intervals"]
        ]

        return {
            "epoch": self.total_epochs_run,
            "sector": self._current_sector,
            "latent_dim": self.latent_dim,
            "coordinates_2d": proj_2d,
            "betti_0": tda["betti_0"],
            "betti_1": tda["betti_1"],
            "h0_barcodes": h0_bars,
            "h1_barcodes": h1_bars,
            "h1_stats": tda["h1_stats"],
        }

    def get_algebraic_constraints(self, distance_threshold: float = 0.5) -> list[dict]:
        """Extract algebraic constraints from learned manifold structure.
        
        Analyzes the latent space geometry to identify:
        1. Annihilation constraints: pairs that must annihilate (distance ~0)
        2. Orthogonality constraints: sectors that should be independent
        3. Symmetry constraints: preserved transformations
        
        Args:
            distance_threshold: Threshold for identifying close pairs in latent space
            
        Returns:
            List of constraint dictionaries with type, parameters, and confidence
        """
        constraints = []
        self.model.eval()
        
        with torch.no_grad():
            z = self.model(self.x_data)[0].cpu().numpy()
        
        # Compute pairwise distances in latent space
        from scipy.spatial.distance import pdist, squareform
        distances = squareform(pdist(z, metric='euclidean'))
        
        # Identify near-zero distance pairs (potential annihilation constraints)
        close_pairs = np.argwhere(distances < distance_threshold)
        
        for i, j in close_pairs:
            if i < j:  # Avoid duplicates
                # Map back to original basis indices
                idx_i = int(self.x_data[i].argmax()) if self.x_data[i].max() > 0 else -1
                idx_j = int(self.x_data[j].argmax()) if self.x_data[j].max() > 0 else -1
                
                constraints.append({
                    'type': 'ANNIHILATION_CONSTRAINT',
                    'basis_indices': (idx_i, idx_j),
                    'node_indices': (i, j),
                    'latent_distance': float(distances[i, j]),
                    'confidence': 1.0 - distances[i, j] / distance_threshold,
                    'sector': self._current_sector,
                })
        
        # Detect sector orthogonality by comparing sector centroids
        sector_centroids = {}
        for chi in self.sectors:
            try:
                x_chi, _ = self._get_sector_data(chi)
                z_chi, _ = self.model(x_chi)
                centroid = z_chi.mean(dim=0).cpu().numpy()
                sector_centroids[chi] = centroid
            except Exception:
                continue
        
        # Check orthogonality between sector embeddings
        sector_list = list(sector_centroids.keys())
        for idx1 in range(len(sector_list)):
            for idx2 in range(idx1 + 1, len(sector_list)):
                chi1, chi2 = sector_list[idx1], sector_list[idx2]
                c1, c2 = sector_centroids[chi1], sector_centroids[chi2]
                dot_product = float(np.dot(c1, c2))
                
                if abs(dot_product) < 0.5:  # Near-orthogonal sectors (lenient threshold)
                    constraints.append({
                        'type': 'SECTOR_ORTHOGONALITY',
                        'sectors': (chi1, chi2),
                        'dot_product': dot_product,
                        'confidence': 1.0 - abs(dot_product) / 0.5,
                    })
        
        return constraints
