"""
Braid group representations on anyon fusion spaces.

For n anyons of a single type ``a`` the fusion-chain basis is the set of
sequences  x_0 = 1, x_1 = a, x_k ∈ x_{k-1} ⊗ a  (k = 2..n);
x_n is the total topological charge.  The generator σ_i exchanges anyons
i and i+1 and acts on the label x_i (neighbours x_{i-1}, x_{i+1}) by

    B = F · diag(R^{aa}_c) · F⁻¹,      F = F^{x_{i-1} a a}_{x_{i+1}}.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

import numpy as np

from qbx_ir.anyon.model import AnyonModel, Label
from qbx_ir.core.braid import Braid


@dataclass(frozen=True)
class FusionSpace:
    model_name: str
    anyon: Label
    n: int
    basis: Tuple[Tuple[Label, ...], ...]

    @property
    def dim(self) -> int:
        return len(self.basis)


def fusion_space(model: AnyonModel, anyon: Label, n: int,
                 total_charge: Optional[Label] = None) -> FusionSpace:
    """Fusion-chain basis (x_0, …, x_n) for n anyons of type ``anyon``."""
    if n < 1:
        raise ValueError("need at least one anyon")
    chains: List[Tuple[Label, ...]] = [(model.vacuum, anyon)]
    for _ in range(2, n + 1):
        chains = [c + (x,) for c in chains for x in model.labels
                  if model.admissible(c[-1], anyon, x)]
    if total_charge is not None:
        chains = [c for c in chains if c[-1] == total_charge]
    return FusionSpace(model.name, anyon, n, tuple(chains))


def generator_matrix(model: AnyonModel, space: FusionSpace, i: int, sign: int = 1) -> np.ndarray:
    """Matrix of σ_i^{sign} on the fusion space."""
    a = space.anyon
    index: Dict[Tuple[Label, ...], int] = {c: k for k, c in enumerate(space.basis)}
    M = np.zeros((space.dim, space.dim), dtype=np.complex128)
    for col, chain in enumerate(space.basis):
        left, right = chain[i - 1], chain[i + 1]
        es = model.intermediates_left(left, a, a, right)
        cs = model.intermediates_right(left, a, a, right)
        F = model.f_matrix(left, a, a, right)
        D = np.diag([model.r_symbol(a, a, c) for c in cs])
        B = F @ D @ np.linalg.inv(F)  # B[e, e'] : coefficient of |e'> in σ|e>
        if sign == -1:
            B = np.linalg.inv(B)
        e = chain[i]
        e_idx = es.index(e)
        for e2_idx, e2 in enumerate(es):
            target = chain[:i] + (e2,) + chain[i + 1:]
            M[index[target], col] += B[e_idx, e2_idx]
    return M


def anyon_representation(braid: Braid, model: AnyonModel, anyon: Optional[Label] = None,
                         total_charge: Optional[Label] = None) -> np.ndarray:
    """ρ(B) on the fusion space of ``braid.strand_count`` anyons."""
    if anyon is None:
        anyon = model.labels[1]
    space = fusion_space(model, anyon, braid.strand_count, total_charge)
    U = np.eye(space.dim, dtype=np.complex128)
    for g in braid.word:
        U = generator_matrix(model, space, g.index, g.sign) @ U
    return U
