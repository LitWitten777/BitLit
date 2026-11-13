"""
Topological Entropy Driven Intelligence (TED-Intelligence)
Integrates PyTorch neural representation learning with GUDHI Persistent Homology
to analyze and verify topological entropy, homological phase transitions,
and invariant preservation on the Sedenion Ramanujan Annihilation Graph C₆[K̄₄].
"""

import math
from typing import Any

import gudhi
import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F


def calculate_topological_entropy_theory() -> dict[str, float]:
    """
    Computes theoretical topological entropy bounds for the 8-regular Ramanujan graph
    C₆[K̄₄] and its quotient 6-cycle C₆.
    By Gelfand's formula: h_top = log2(λ_max).
    For regular graph: λ_max = degree d.
    """
    # 1. Full 8-regular Ramanujan graph (d = 8)
    d_full = 8.0
    h_top_full = math.log2(d_full)  # exactly 3.0 bits

    # 2. Quotient 6-cycle C6 (d = 2)
    d_c6 = 2.0
    h_top_c6 = math.log2(d_c6)  # exactly 1.0 bit

    # 3. Twin cluster K4 entropy
    cluster_size = 4.0
    h_cluster = math.log2(cluster_size)  # exactly 2.0 bits

    return {
        "h_top_full": h_top_full,
        "h_top_c6": h_top_c6,
        "h_cluster": h_cluster,
        "additive_identity_holds": (h_top_c6 + h_cluster == h_top_full),
    }


def compute_gudhi_persistent_entropy(intervals: list[tuple[float, float]]) -> dict[str, float]:
    """
    Computes Shannon persistent entropy and summary statistics
    from GUDHI persistence intervals in dimension d.
    S_top = - ∑ p_i log2(p_i), where p_i = L_i / ∑ L_j.
    """
    if len(intervals) == 0:
        return {"entropy": 0.0, "max_persistence": 0.0, "total_persistence": 0.0, "count": 0}

    finite_bars = []
    max_finite = max((d for b, d in intervals if np.isfinite(d)), default=1.0)
    for b, d in intervals:
        death = max_finite if not np.isfinite(d) else d
        length = death - b
        if length > 1e-5:
            finite_bars.append(length)

    if not finite_bars:
        return {"entropy": 0.0, "max_persistence": 0.0, "total_persistence": 0.0, "count": 0}

    total_len = sum(finite_bars)
    p = np.array(finite_bars) / total_len
    p = p[p > 0]
    entropy = float(max(0.0, -np.sum(p * np.log2(p))))
    max_pers = float(max(finite_bars))

    return {
        "entropy": entropy,
        "max_persistence": max_pers,
        "total_persistence": total_len,
        "count": len(finite_bars),
    }


def analyze_homology_gudhi(
    points_np: np.ndarray, max_edge_length: float | None = None
) -> dict[str, Any]:
    """
    Computes Rips complex, Betti numbers, and persistent entropy using GUDHI.
    If max_edge_length is None, it defaults to the maximum pairwise distance of the point cloud.
    """
    if max_edge_length is None:
        from scipy.spatial.distance import pdist

        dists = pdist(points_np)
        max_edge_length = float(np.max(dists)) if len(dists) > 0 else 1.0

    rips = gudhi.RipsComplex(points=points_np, max_edge_length=max_edge_length)
    st = rips.create_simplex_tree(max_dimension=2)
    st.persistence()

    h0_intervals = st.persistence_intervals_in_dimension(0)
    h1_intervals = st.persistence_intervals_in_dimension(1)

    h0_stats = compute_gudhi_persistent_entropy(h0_intervals)
    h1_stats = compute_gudhi_persistent_entropy(h1_intervals)

    # Significant H1 loops (persistence > 0.25 * max_persistence)
    max_p = h1_stats["max_persistence"]
    sig_h1 = (
        [bar for bar in h1_intervals if np.isfinite(bar[1]) and (bar[1] - bar[0]) > 0.25 * max_p]
        if max_p > 0
        else []
    )

    return {
        "betti_0": len([b for b in h0_intervals if not np.isfinite(b[1]) or (b[1] - b[0]) > 0.5]),
        "betti_1": len(sig_h1),
        "h0_intervals": h0_intervals,
        "h1_intervals": h1_intervals,
        "h0_stats": h0_stats,
        "h1_stats": h1_stats,
        "simplex_tree": st,
    }


class TopologicalManifoldLearner(nn.Module):
    """
    Neural manifold learner that maps 16D sedenion vectors to a normalized latent space
    and predicts algebraic annihilation.
    """

    def __init__(self, in_dim: int = 16, hidden_dim: int = 64, latent_dim: int = 8):
        super().__init__()
        self.enc = nn.Sequential(
            nn.Linear(in_dim, hidden_dim),
            nn.LayerNorm(hidden_dim),
            nn.GELU(),
            nn.Linear(hidden_dim, 32),
            nn.LayerNorm(32),
            nn.GELU(),
            nn.Linear(32, latent_dim),
        )
        self.head = nn.Bilinear(latent_dim, latent_dim, 1)

    def forward(self, x: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        z = self.enc(x)
        n = x.size(0)
        z1 = z.unsqueeze(1).expand(n, n, -1)
        z2 = z.unsqueeze(0).expand(n, n, -1)
        logits = self.head(z1, z2).squeeze(-1)
        return z, logits


def train_topological_learner(
    x_data: torch.Tensor,
    adj_data: torch.Tensor,
    epochs: int = 80,
    lr: float = 0.02,
    topological_regularization: bool = True,
    seed: int = 42,
) -> dict[str, Any]:
    """
    Trains TopologicalManifoldLearner with or without GUDHI persistent entropy guidance.
    """
    torch.manual_seed(seed)
    np.random.seed(seed)

    model = TopologicalManifoldLearner(in_dim=16, hidden_dim=64, latent_dim=8)
    optimizer = torch.optim.Adam(model.parameters(), lr=lr)
    n = x_data.size(0)
    mask = (1.0 - torch.eye(n)).bool()

    history: dict[str, list[float]] = {
        "loss": [],
        "accuracy": [],
        "h1_max_persistence": [],
        "h1_entropy": [],
    }

    for epoch in range(epochs):
        optimizer.zero_grad()
        z, logits = model(x_data)
        task_loss = F.binary_cross_entropy_with_logits(logits[mask], adj_data[mask])

        # Topological guidance: promote persistent 1-cycles while keeping scale bounded
        if topological_regularization and epoch < 60:
            # We add a mild contraction within twin clusters and dilation across adjacent clusters
            # derived from the Rips persistence pairs
            D = torch.cdist(z, z)
            D_np = D.detach().cpu().numpy()
            max_d = float(np.max(D_np))
            if max_d > 1e-4:
                rips = gudhi.RipsComplex(distance_matrix=D_np, max_edge_length=max_d * 0.9)
                st = rips.create_simplex_tree(max_dimension=2)
                st.persistence()
                pairs = st.persistence_pairs()

                h1_pers = []
                for sb, sd in pairs:
                    if len(sb) == 2 and len(sd) == 3:
                        b_val = D[sb[0], sb[1]]
                        d_val = torch.max(
                            torch.stack([D[sd[0], sd[1]], D[sd[0], sd[2]], D[sd[1], sd[2]]])
                        )
                        pers = d_val - b_val
                        h1_pers.append(pers)

                if h1_pers:
                    h1_tensor = torch.stack(h1_pers)
                    max_p = torch.max(h1_tensor)
                    # Reward primary cycle persistence normalized by max distance
                    top_loss = -0.1 * (max_p / (max_d + 1e-6))
                else:
                    top_loss = torch.tensor(0.0)
            else:
                top_loss = torch.tensor(0.0)
        else:
            top_loss = torch.tensor(0.0)

        total_loss = task_loss + top_loss
        total_loss.backward()
        optimizer.step()

        with torch.no_grad():
            preds = (torch.sigmoid(logits[mask]) > 0.5).float()
            acc = (preds == adj_data[mask]).float().mean().item()
            z_np = z.detach().cpu().numpy()
            tda = analyze_homology_gudhi(z_np)

        history["loss"].append(total_loss.item())
        history["accuracy"].append(acc)
        history["h1_max_persistence"].append(tda["h1_stats"]["max_persistence"])
        history["h1_entropy"].append(tda["h1_stats"]["entropy"])

    final_z = model(x_data)[0].detach().cpu().numpy()
    final_tda = analyze_homology_gudhi(final_z)

    return {
        "model": model,
        "embeddings": final_z,
        "final_accuracy": history["accuracy"][-1],
        "final_tda": final_tda,
        "history": history,
    }
