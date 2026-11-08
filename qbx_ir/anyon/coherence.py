"""Pentagon / hexagon residuals, gauge invariants and gauge matching for
multiplicity-free anyon data given as arrays.

A model is described by

* ``F[a, b, c, d, e, f] = [F^{abc}_d]_{ef}`` (zero on non-admissible
  vertices), a complex array of shape ``(L,)*6``;
* ``R[a, b, c] = R^{ab}_c`` (zero if ``c ∉ a ⊗ b``), shape ``(L,)*3``;
* ``N[a, b, c] ∈ {0, 1}`` the fusion multiplicities; label ``0`` is the vacuum.

The equations are those of ``tests/qbx_ir/test_anyon_coherence.py`` (and of
``QBX/Formal/AnyonCoherence.lean``).
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass

import numpy as np

__all__ = ["AnyonData", "pentagon_residual", "hexagon_residual",
           "unitarity_residual", "topological_spins", "fs_indicators",
           "gauge_transform", "find_gauge", "from_anyon_model", "restrict"]


@dataclass
class AnyonData:
    names: tuple[str, ...]
    N: np.ndarray
    F: np.ndarray
    R: np.ndarray
    d: np.ndarray          # quantum dimensions

    @property
    def L(self) -> int:
        return len(self.names)


def pentagon_residual(m: AnyonData) -> float:
    """``max |F(f,c,d,e,g,l) F(a,b,l,e,f,k) − Σ_h F(a,b,c,g,f,h) F(a,h,d,e,g,k) F(b,c,d,k,h,l)|``."""
    F = m.F
    worst = 0.0
    for a in range(m.L):
        lhs = np.einsum("fcdegl,blefk->bcdefgkl", F, F[a])
        rhs = np.einsum("bcgfh,hdegk,bcdkhl->bcdefgkl", F[a], F[a], F)
        worst = max(worst, float(np.abs(lhs - rhs).max()))
    return worst


def hexagon_residual(m: AnyonData, reverse: bool = False) -> float:
    """``max |R(c,a,e) F(a,c,b,d,e,g) R(c,b,g) − Σ_f F(c,a,b,d,e,f) R(c,f,d) F(a,b,c,d,f,g)|``;
    with ``reverse`` the reversed inverse ``(R^{ba}_c)^{-1}`` replaces ``R``."""
    R = m.R
    if reverse:
        Rt = np.transpose(R, (1, 0, 2))
        R = np.where(Rt != 0, 1 / np.where(Rt != 0, Rt, 1), 0)
    F = m.F
    lhs = np.einsum("cae,acbdeg,cbg->abcdeg", R, F, R)
    rhs = np.einsum("cabdef,cfd,abcdfg->abcdeg", F, R, F)
    return float(np.abs(lhs - rhs).max())


def unitarity_residual(m: AnyonData) -> float:
    worst = 0.0
    for a, b, c, d in itertools.product(range(m.L), repeat=4):
        left = [e for e in range(m.L) if m.N[a, b, e] and m.N[e, c, d]]
        right = [f for f in range(m.L) if m.N[b, c, f] and m.N[a, f, d]]
        if not left:
            continue
        M = m.F[a, b, c, d][np.ix_(left, right)]
        worst = max(worst, float(np.abs(M.conj().T @ M - np.eye(len(left))).max()))
    return worst


def topological_spins(m: AnyonData) -> np.ndarray:
    """``θ_a = Σ_c (d_c / d_a) R^{aa}_c`` — gauge invariant (``a`` self-dual
    or not: only ``R^{aa}`` enters)."""
    return np.array([sum(m.d[c] / m.d[a] * m.R[a, a, c] for c in range(m.L))
                     for a in range(m.L)])


def fs_indicators(m: AnyonData) -> np.ndarray:
    """Frobenius–Schur indicator ``κ_a = d_a [F^{a a a}_a]_{0 0}`` for
    self-dual ``a`` (vacuum gauge fixed); ``nan`` if ``a`` is not self-dual."""
    out = []
    for a in range(m.L):
        if not m.N[a, a, 0]:
            out.append(np.nan)
        else:
            out.append(m.d[a] * m.F[a, a, a, a, 0, 0])
    return np.array(out)


def gauge_transform(m: AnyonData, u: dict) -> AnyonData:
    """Apply the gauge ``u[(a, b, c)]`` (vertex ``a ⊗ b → c``; missing keys
    and vertices with a vacuum leg count as 1):
    ``F → u^{ab}_e u^{ec}_d / (u^{bc}_f u^{af}_d) F``, ``R → u^{ba}_c / u^{ab}_c R``."""
    L = m.L
    U = np.ones((L, L, L), dtype=complex)
    for (a, b, c), v in u.items():
        if 0 not in (a, b):
            U[a, b, c] = v
    F = np.empty_like(m.F)
    for a, b, c, d, e, f in itertools.product(range(L), repeat=6):
        F[a, b, c, d, e, f] = (m.F[a, b, c, d, e, f] * U[a, b, e] * U[e, c, d]
                               / (U[b, c, f] * U[a, f, d]))
    R = m.R * np.transpose(U, (1, 0, 2)) / U
    return AnyonData(m.names, m.N, F, R, m.d)


def find_gauge(src: AnyonData, dst: AnyonData,
               phases=(1, -1, 1j, -1j), tol: float = 1e-9):
    """Search gauges with values in ``phases`` on every non-vacuum vertex that
    turn ``src`` into ``dst`` (same labels and fusion). Returns the gauge (a
    dict) or ``None``. A ``None`` is evidence, not proof, of inequivalence;
    use the gauge invariants for that."""
    if not np.array_equal(src.N, dst.N):
        return None
    verts = [(a, b, c) for a, b, c in itertools.product(range(src.L), repeat=3)
             if src.N[a, b, c] and 0 not in (a, b)]
    for vals in itertools.product(phases, repeat=len(verts)):
        u = dict(zip(verts, vals))
        g = gauge_transform(src, u)
        if (np.abs(g.F - dst.F).max() < tol and np.abs(g.R - dst.R).max() < tol):
            return u
    return None


def restrict(m: AnyonData, keep: list[int]) -> AnyonData:
    """The data on a fusion-closed subset of labels (``keep[0]`` the vacuum)."""
    ix = np.ix_(*([keep] * 3))
    N = m.N[ix]
    F = m.F[np.ix_(*([keep] * 6))]
    R = m.R[ix]
    return AnyonData(tuple(m.names[i] for i in keep), N, F, R, m.d[keep])


def from_anyon_model(model) -> AnyonData:
    """Adapter for ``qbx_ir.anyon.AnyonModel`` (vacuum moved to index 0)."""
    labels = [model.vacuum] + [x for x in model.labels if x != model.vacuum]
    L = len(labels)
    N = np.zeros((L, L, L), dtype=int)
    for (i, a), (j, b), (k, c) in itertools.product(enumerate(labels), repeat=3):
        N[i, j, k] = 1 if model.admissible(a, b, c) else 0
    F = np.zeros((L,) * 6, dtype=complex)
    for idx in itertools.product(range(L), repeat=4):
        a, b, c, d = (labels[i] for i in idx)
        left = model.intermediates_left(a, b, c, d)
        right = model.intermediates_right(a, b, c, d)
        if not left:
            continue
        M = model.f_matrix(a, b, c, d)
        for e in left:
            for f in right:
                F[idx + (labels.index(e), labels.index(f))] = M[left.index(e), right.index(f)]
    R = np.zeros((L,) * 3, dtype=complex)
    for (i, a), (j, b), (k, c) in itertools.product(enumerate(labels), repeat=3):
        if model.admissible(a, b, c):
            R[i, j, k] = complex(model.r_symbol(a, b, c))
    d = np.array([model.quantum_dims[x] for x in labels])
    return AnyonData(tuple(labels), N, F, R, d)
