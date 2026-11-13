"""
src/sedenion/hyperbolic_mds.py
=============================================================================
Hyperbolic Multidimensional Scaling (MDS) in Poincaré Ball B^3
Resolving Claim 4 (Refinement Audit):
  Quantifies stress distortion of Sephirot tree embeddings in B^3.
  Tests whether handcrafted radial coordinates (0.20 -> 0.90) minimize
  geodesic path stress, or whether they are purely conventional assignments [A].
=============================================================================
"""

import numpy as np
from typing import Dict, List, Tuple


TREE_EDGES = [
    (0, 1), (0, 2), (0, 5),
    (1, 2), (1, 3), (1, 5),
    (2, 4), (2, 5),
    (3, 4), (3, 5), (3, 6),
    (4, 5), (4, 7),
    (5, 6), (5, 7), (5, 8),
    (6, 7), (6, 8), (6, 9),
    (7, 8), (7, 9),
    (8, 9)
]

NODE_NAMES = [
    "Kether", "Chokmah", "Binah", "Chesed", "Geburah",
    "Tiphareth", "Netzach", "Hod", "Yesod", "Malkuth"
]


def poincare_dist(u: np.ndarray, v: np.ndarray, eps: float = 1e-10) -> float:
    """
    Riemannian geodesic distance in the Poincaré ball B^n:
      d_B(u, v) = arcosh(1 + 2 * ||u - v||^2 / ((1 - ||u||^2)(1 - ||v||^2)))
    """
    u_sq = np.sum(u**2)
    v_sq = np.sum(v**2)
    
    # Clip to strictly inside open unit ball
    u_sq = min(u_sq, 1.0 - eps)
    v_sq = min(v_sq, 1.0 - eps)
    
    diff_sq = np.sum((u - v)**2)
    alpha = 1.0 - u_sq
    beta = 1.0 - v_sq
    
    arg = 1.0 + 2.0 * diff_sq / max(alpha * beta, eps)
    # Ensure arg >= 1.0 for arcosh
    arg = max(arg, 1.0)
    return float(np.arccosh(arg))


def get_handcrafted_coordinates() -> np.ndarray:
    """
    The handcrafted Sephirotic coordinates with monotonic radial expansion (0.20 -> 0.90)
    across the four traditional worlds:
      Atziluth: Kether (0.20)
      Beriah: Chokmah, Binah (0.40)
      Yetzirah: Chesed, Geburah, Tiphareth (0.60), Netzach, Hod, Yesod (0.75)
      Assiah: Malkuth (0.90)
    """
    coords = np.zeros((10, 3), dtype=np.float64)
    # 0: Kether
    coords[0] = [0.0, 0.0, 0.20]
    # 1: Chokmah
    coords[1] = [0.35, 0.0, 0.19]
    # 2: Binah
    coords[2] = [-0.35, 0.0, 0.19]
    # 3: Chesed
    coords[3] = [0.42, 0.0, -0.42]
    # 4: Geburah
    coords[4] = [-0.42, 0.0, -0.42]
    # 5: Tiphareth
    coords[5] = [0.0, 0.0, -0.60]
    # 6: Netzach
    coords[6] = [0.45, 0.0, -0.60]
    # 7: Hod
    coords[7] = [-0.45, 0.0, -0.60]
    # 8: Yesod
    coords[8] = [0.0, 0.0, -0.75]
    # 9: Malkuth
    coords[9] = [0.0, 0.0, -0.90]
    return coords


def compute_stress(coords: np.ndarray, target_dist: float = 1.0) -> Tuple[float, List[float]]:
    """
    Compute total stress majorization loss:
      L(X) = sum_{(i,j) in E} (d_B(x_i, x_j) - target_dist)^2
    """
    residuals = []
    total_stress = 0.0
    for i, j in TREE_EDGES:
        d = poincare_dist(coords[i], coords[j])
        res = (d - target_dist) ** 2
        residuals.append(res)
        total_stress += res
    return float(total_stress), residuals


def optimize_poincare_mds(
    init_coords: np.ndarray | None = None,
    target_dist: float = 1.0,
    lr: float = 0.01,
    steps: int = 500,
    seed: int = 42
) -> Dict[str, any]:
    """
    Gradient descent optimization on Poincaré ball B^3 to find coordinates
    that minimize edge distance stress L*(X).
    Ensures coordinates remain inside the unit ball via projection retraction.
    """
    rng = np.random.default_rng(seed)
    if init_coords is None:
        coords = rng.uniform(-0.3, 0.3, size=(10, 3)).astype(np.float64)
    else:
        coords = np.copy(init_coords).astype(np.float64)

    initial_stress, _ = compute_stress(coords, target_dist)
    
    eps = 1e-6
    max_norm = 0.95

    for _ in range(steps):
        grad = np.zeros_like(coords)
        for i, j in TREE_EDGES:
            d = poincare_dist(coords[i], coords[j])
            diff = d - target_dist
            
            # Finite difference gradient per coordinate
            for node, sign in [(i, 1.0), (j, -1.0)]:
                for k in range(3):
                    orig = coords[node, k]
                    coords[node, k] = orig + eps
                    d_plus = poincare_dist(coords[i], coords[j])
                    coords[node, k] = orig
                    grad[node, k] += 2.0 * diff * (d_plus - d) / eps

        # Update step with clipping
        coords -= lr * np.clip(grad, -2.0, 2.0)
        
        # Retraction onto open ball ||x|| <= max_norm
        norms = np.linalg.norm(coords, axis=1, keepdims=True)
        scale = np.where(norms > max_norm, max_norm / (norms + 1e-12), 1.0)
        coords *= scale

    final_stress, final_res = compute_stress(coords, target_dist)
    
    # Calculate radius monotonicity for optimized vs initial
    init_radii = [float(np.linalg.norm(r)) for r in (init_coords if init_coords is not None else coords)]
    opt_radii = [float(np.linalg.norm(r)) for r in coords]

    return {
        "initial_stress": float(initial_stress),
        "optimized_stress": float(final_stress),
        "target_distance": target_dist,
        "stress_reduction_ratio": float((initial_stress - final_stress) / max(initial_stress, 1e-12)),
        "optimized_coords": coords.tolist(),
        "init_radii": init_radii,
        "optimized_radii": opt_radii,
        "is_opt_strictly_monotone": all(opt_radii[i] <= opt_radii[i+1] for i in range(len(opt_radii)-1)),
        "distortion_L_star": float(np.sqrt(final_stress) / len(TREE_EDGES))
    }
