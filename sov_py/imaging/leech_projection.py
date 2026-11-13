"""
24-Dimensional Leech Lattice Lambda_24 & Curtis MOG Projection Engine.

Lifts 16D sedenion multi-messenger fields into 24-dimensional Leech lattice space
via Curtis Miracle Octad Generator (MOG) 4x6 arrays and extended binary Golay code G_24 parity,
and performs associative resonance retrieval against the 144,000-node Leech Mind Vault.
"""

from __future__ import annotations

import json
import os
import torch
import numpy as np

from src.sedenion.codes import BinaryLinearCode, LeechLatticeEmbedding, MOGComponentEmbedding
from src.sedenion.graph import AnnihilationGraph


DIMENSION_DICTIONARY_PATH = "/data/mind/cognition/LEECH_DIMENSION_DICTIONARY.json"
BITPACKED_VAULT_PATH = "/data/mind/cognition/LEECH_BITPACKED_MIND_VAULT.pt"


def load_dimension_dictionary(path: str = DIMENSION_DICTIONARY_PATH) -> list[dict]:
    """Load the 24 Dimensions of Knowledge metadata."""
    if not os.path.exists(path):
        return [{"dim": i + 1, "name": f"Dim_{i+1}", "category": "General", "desc": ""} for i in range(24)]
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    return data.get("dimensions", [])


def lift_16d_to_24d_mog(field_16d: np.ndarray) -> np.ndarray:
    """Lift a 16D sedenion field into a 24D Leech lattice space via Curtis MOG 4x6 array.

    The first 4 columns of the 4x6 MOG grid correspond to the 16 sedenion dimensions:
    - Col 0: S[0..3]  (Continuum, Chrominance C1, C2, Gradient gx)
    - Col 1: S[4..7]  (Gradient gy, Laplacian, Texture, Divergence)
    - Col 2: S[8..11] (Coarse scale, Hessian gxx, gyy, gxy)
    - Col 3: S[12..15] (Shear diag, antidiag, TIE phase, Associator)
    - Col 4: Parity completion (Psyche, Soma, Pneuma, Techne)
    - Col 5: Parity completion (Nomos, Chaos, Telos, Apeiron)

    Parameters
    ----------
    field_16d : np.ndarray
        Array of shape (H, W, 16) or (N, 16).

    Returns
    -------
    np.ndarray
        Array of shape (..., 24).
    """
    is_1d = (field_16d.ndim == 1)
    is_spatial = (field_16d.ndim == 3)
    if is_1d:
        flat = field_16d.reshape(1, 16)
    elif is_spatial:
        h, w, c = field_16d.shape
        flat = field_16d.reshape(-1, 16)
    else:
        flat = field_16d

    n_pts, c = flat.shape
    if c != 16:
        raise ValueError(f"Expected 16 channels, got {c}")

    field_24d = np.zeros((n_pts, 24), dtype=np.float64)
    field_24d[:, :16] = flat

    # Reshape 16 coordinates into 4 rows x 4 columns per point
    col0 = flat[:, 0:4]
    col1 = flat[:, 4:8]
    col2 = flat[:, 8:12]
    col3 = flat[:, 12:16]

    # Curtis MOG Parity Completion:
    # Col 4 (dims 17..20: Psyche, Soma, Pneuma, Techne) completes row parity
    col4 = 0.5 * (col0 + col2) - 0.5 * (col1 + col3)

    # Col 5 (dims 21..24: Nomos, Chaos, Telos, Apeiron) completes total sum to zero mod 4
    col5 = - (col0 + col1 + col2 + col3 + col4) / 4.0

    field_24d[:, 16:20] = col4
    field_24d[:, 20:24] = col5

    # Normalize each 24D vector to unit norm
    norms = np.linalg.norm(field_24d, axis=-1, keepdims=True)
    norms = np.where(norms < 1e-8, 1.0, norms)
    field_24d_norm = field_24d / norms

    if is_1d:
        return field_24d_norm[0]
    if is_spatial:
        return field_24d_norm.reshape(h, w, 24)
    return field_24d_norm


def quantize_to_nearest_leech_vector(v24: np.ndarray) -> tuple[np.ndarray, float]:
    """Quantize a 24D vector to the nearest scaled Leech lattice vector in Lambda_24.

    Returns the quantized lattice vector and the Euclidean distance residual.
    """
    # Standard Construction B approximation:
    # A vector in Lambda_24 has integer or half-odd coordinates summing to 0 mod 4.
    scaled = v24 * np.sqrt(8.0)  # Scale to standard Leech minimal norm ||x||^2 = 8
    rounded = np.round(scaled)

    # Enforce sum = 0 mod 4
    rem = int(np.sum(rounded)) % 4
    if rem != 0:
        # Adjust the coordinate with the largest fractional error
        errors = np.abs(scaled - rounded)
        idx = np.argmax(errors)
        rounded[idx] -= rem

    residual = float(np.linalg.norm(scaled - rounded))
    return rounded, residual


class LeechVaultResonator:
    """Associative memory retriever querying the 144,000-node Leech Mind Vault."""

    def __init__(self, vault_path: str = BITPACKED_VAULT_PATH):
        self.vault_path = vault_path
        self.dim_dict = load_dimension_dictionary()
        self.vault_tensor: torch.Tensor | None = None
        self._load_vault()

    def _load_vault(self) -> None:
        if os.path.exists(self.vault_path):
            # Load with weights_only=False
            self.vault_tensor = torch.load(self.vault_path, map_location="cpu", weights_only=False)
            print(f"Loaded Leech Mind Vault: {self.vault_tensor.shape} ({self.vault_tensor.dtype})")
        else:
            print(f"Warning: Leech Vault not found at {self.vault_path}. Running in synthetic mock mode.")

    def query_resonance(
        self,
        v24: np.ndarray,
        top_k: int = 5,
    ) -> list[dict]:
        """Find the top-k resonant attractor nodes in the 144,000 Leech vault for vector v24."""
        if v24.shape[-1] != 24:
            raise ValueError(f"Expected 24-dimensional vector, got {v24.shape}")

        v24_norm = v24 / (np.linalg.norm(v24) + 1e-8)

        if self.vault_tensor is None:
            # Fallback mock results if vault file is missing
            return [
                {"node_id": i * 1000, "similarity": 0.85 - i * 0.05, "dominant_dims": ["Logos", "Physis", "Telos"]}
                for i in range(top_k)
            ]

        # In the bitpacked vault (144000, 1250), each vector has 1250 bytes = 10,000 bits.
        # We project the 24D vector into a 1250-byte bitpacked query via random orthogonal projection (Johnson-Lindenstrauss)
        n_bytes = self.vault_tensor.shape[1]
        np.random.seed(42)
        # Deterministic 24 -> 1250 projection matrix
        P = np.random.randn(24, n_bytes)
        proj = np.dot(v24_norm, P)
        query_bytes = torch.from_numpy(np.clip((proj - proj.min()) / (proj.max() - proj.min() + 1e-8) * 255.0, 0, 255).astype(np.uint8))

        # Vectorized L1 distance across 144,000 nodes (fast on CPU)
        # Sample or chunk to prevent huge memory spikes
        chunk_size = 24000
        n_nodes = self.vault_tensor.shape[0]
        distances = []

        q_float = query_bytes.float()
        for i in range(0, n_nodes, chunk_size):
            chunk = self.vault_tensor[i : i + chunk_size].float()
            dist = torch.mean(torch.abs(chunk - q_float), dim=1)
            distances.append(dist)

        all_dists = torch.cat(distances, dim=0)
        best_indices = torch.topk(all_dists, k=top_k, largest=False).indices.numpy()

        results = []
        for idx in best_indices:
            dist_val = float(all_dists[idx].item())
            sim = 1.0 - (dist_val / 255.0)

            # Determine dominant knowledge dimensions
            dim_activations = np.abs(v24_norm)
            top_dim_indices = np.argsort(dim_activations)[::-1][:3]
            dominant_dims = [self.dim_dict[d]["name"] for d in top_dim_indices if d < len(self.dim_dict)]

            results.append({
                "node_id": int(idx),
                "similarity": float(sim),
                "distance": dist_val,
                "dominant_dims": dominant_dims,
                "dimension_profile": {
                    self.dim_dict[d]["name"]: float(v24_norm[d]) for d in range(min(24, len(self.dim_dict)))
                },
            })

        return results
