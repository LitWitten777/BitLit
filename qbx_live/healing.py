"""
Harmonic healing, Fano UV completion and gap filling — runtime mirror of
``QBX/Formal/Sovereign`` (Lean).

Correspondence with the Lean development
----------------------------------------

=====================================  ==============================================
Python                                 Lean (namespace ``QBX.Formal``)
=====================================  ==============================================
:func:`spectral_energy`                ``Healing.specEnergy`` (``Harmonic/Energy``)
:func:`arc_bound`                      the universal arc ``|θ| < 2π/n``
                                       (``MultiProver.resonance_universal_n``)
zero energy on the arc ⇔ Burau = 1     ``Healing.specEnergy_arc_iff``
… ⇔ braid = 1 for three strands        ``Healing.specEnergy_arc_iff_trivial_three``
one angle is not enough (σ₁², θ=0)     ``Healing.specEnergy_sigmaOneSq_zero``
:func:`phase_flow`                     ``Healing.phaseFlow_energy_le`` / ``_antitone``
:func:`heat_step`                      ``Healing.heatStep_sum`` / ``heatStep_mem_Icc``
:func:`fano_third`, :func:`fano_close` ``UV.completion_unique``, ``UV.closure_full_iff``
:func:`octonion_product`               ``UV.completion_octonion`` (``SovKernel.CD.sign``)
:func:`hamming_syndrome`, decoding     ``UV.single_error_syndrome``, ``UV.decode_corrects``
:func:`fano_checksum`, Fano candidate  ``GapFilling.fano_erasure``, ``fanoCandidate_correct``
anchor candidate unique                ``GapFilling.gap_unique``, ``anchor_gap_unique``
conflict ⇒ inconsistent input          ``GapFilling.conflict_detects``
=====================================  ==============================================

What is exact and what is numerical
-----------------------------------

* Garside normal forms, Burau matrices over ℤ[t, t⁻¹], permutations, writhe,
  linking numbers, Fano/Hamming computations are **exact**.
* Spectral energies are computed in floating point from exact matrices; they
  are used to *rank* candidates, never to certify.  Certification is always by
  the exact anchors (Garside NF, or the Burau matrix).
* The geometric layer (:class:`ClassicalGeometry`, :class:`GNPGeometry`) is a
  numerical smoothing/visualisation aid.  ``geo_neural_op`` (Geometric Neural
  Operators) is **optional**: if a model callable is supplied,
  :class:`GNPGeometry` uses it; otherwise a classical estimator (local PCA
  curvature, k-NN graph Laplacian) is used.  The GNP package is not a
  dependency, and its API is not assumed beyond "a callable mapping an
  ``(N, 3)`` point array to per-point values".
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Sequence, Tuple

import numpy as np

from qbx_ir.algebra.garside import braid_group_equal, left_normal_form
from qbx_ir.algebra.invariants import (
    closure_components,
    linking_matrix,
    permutation,
    writhe,
)
from qbx_ir.algebra.multiprover import anchor_reading, burau_at
from qbx_ir.core.braid import Braid

# ===========================================================================
# 1. Spectral (harmonic) energy
# ===========================================================================


def arc_bound(n: int) -> float:
    """Half-width ``2π/n`` of the universal arc on which every Burau eigenvalue
    is unimodular and Squier's form is definite."""
    return 2 * math.pi / n if n > 0 else 0.0


def burau_eigenvalues(braid: Braid, theta: float) -> np.ndarray:
    """Eigenvalues of ρ̄(β)(e^{iθ})."""
    if braid.strand_count < 2:
        return np.zeros(0, dtype=complex)
    return np.linalg.eigvals(burau_at(braid, theta))


def spectral_energy(braid: Braid, theta: float) -> float:
    """``E_θ(β) = Σ |λᵢ − 1|²`` over the Burau eigenvalues at ``t = e^{iθ}``."""
    lam = burau_eigenvalues(braid, theta)
    return float(np.sum(np.abs(lam - 1) ** 2))


def arc_angles(n: int, points: int = 33, margin: float = 0.98) -> np.ndarray:
    """A symmetric grid inside the open universal arc."""
    b = arc_bound(n) * margin
    return np.linspace(-b, b, points)


def arc_energy(braid: Braid, points: int = 33) -> float:
    """Average spectral energy over the universal arc — the discrete version of
    the design note's ``∫ E dt``.  Zero (exactly) iff the Burau matrix is the
    identity at the grid points; for three strands a zero over the whole arc
    means the braid is trivial (``specEnergy_arc_iff_trivial_three``)."""
    if braid.strand_count < 2:
        return 0.0
    return float(np.mean([spectral_energy(braid, th)
                          for th in arc_angles(braid.strand_count, points)]))


def energy_profile(braid: Braid, thetas: Sequence[float]) -> np.ndarray:
    return np.array([spectral_energy(braid, th) for th in thetas])


def is_burau_trivial(braid: Braid) -> bool:
    """Exact: is the reduced Burau matrix over ℤ[t, t⁻¹] the identity?"""
    return anchor_reading(braid) == anchor_reading(Braid.identity(braid.strand_count))


# ===========================================================================
# 2. Healing flows
# ===========================================================================


def eigen_phases(braid: Braid, theta: float) -> np.ndarray:
    """Phases ``φ`` of the (unimodular, on the arc) Burau eigenvalues ``e^{iφ}``."""
    return np.angle(burau_eigenvalues(braid, theta))


def phase_flow(phases: Sequence[float], kappa: float = 0.25, steps: int = 24) -> np.ndarray:
    """The healing flow ``φ ↦ (1 − κ) φ`` (Euler step of ``∂ₜφ = −φ``).

    Returns an array of shape ``(steps + 1, len(phases))``.  Lean:
    ``phaseFlow_energy_le`` (energy ≤ (1−κ)^{2k} φ₀²) and
    ``phaseFlow_energy_antitone`` (monotone for |φ₀| ≤ π)."""
    phases = np.asarray(phases, dtype=float)
    factors = (1 - kappa) ** np.arange(steps + 1)
    return factors[:, None] * phases[None, :]


def phase_energy(phases: np.ndarray) -> np.ndarray:
    """``Σ |e^{iφ} − 1|² = Σ (2 − 2 cos φ)`` along the last axis."""
    return np.sum(2 - 2 * np.cos(phases), axis=-1)


def heat_step(x: np.ndarray, alpha: float = 0.25) -> np.ndarray:
    """One explicit heat step on a cyclic signal (preserves the sum; maximum
    principle for 0 ≤ α ≤ 1/2)."""
    x = np.asarray(x, dtype=float)
    return x + alpha * (np.roll(x, 1) - 2 * x + np.roll(x, -1))


def heat_flow(x: Sequence[float], alpha: float = 0.25, steps: int = 20) -> np.ndarray:
    out = [np.asarray(x, dtype=float)]
    for _ in range(steps):
        out.append(heat_step(out[-1], alpha))
    return np.array(out)


# ===========================================================================
# 3. Fano plane, octonions, Hamming code
# ===========================================================================

FANO_POINTS: Tuple[int, ...] = (1, 2, 3, 4, 5, 6, 7)
FANO_LINES: Tuple[Tuple[int, int, int], ...] = (
    (1, 2, 3), (1, 4, 5), (1, 6, 7), (2, 4, 6), (2, 5, 7), (3, 4, 7), (3, 5, 6),
)


def fano_third(i: int, j: int) -> int:
    """The third point on the line through distinct points ``i, j``: ``i xor j``."""
    if i == j or not (1 <= i <= 7 and 1 <= j <= 7):
        raise ValueError("need two distinct Fano points 1..7")
    return i ^ j


def cd_sign(n: int, i: int, j: int) -> int:
    """Sign of ``e_i e_j = ± e_{i xor j}`` at Cayley–Dickson level ``n`` —
    a direct port of ``SovKernel.CD.sign`` (level 3 = octonions)."""
    if n == 0:
        return 1
    h = 2 ** (n - 1)
    if i < h:
        if j < h:
            return cd_sign(n - 1, i, j)
        return cd_sign(n - 1, j - h, i)
    if j < h:
        return (1 if j == 0 else -1) * cd_sign(n - 1, i - h, j)
    return -(1 if j - h == 0 else -1) * cd_sign(n - 1, j - h, i - h)


def octonion_product(i: int, j: int) -> Tuple[int, int]:
    """``e_i e_j = s · e_k``; returns ``(s, k)`` with ``k = i xor j``."""
    return cd_sign(3, i, j), i ^ j


def fano_close(points: Sequence[int]) -> Tuple[int, ...]:
    """Fano closure (nonzero part of the 𝔽₂-span) of a set of points."""
    s = {p for p in points if p != 0}
    while True:
        new = s | {a ^ b for a in s for b in s if a != b}
        if new == s:
            return tuple(sorted(s))
        s = new


def is_collinear(a: int, b: int, c: int) -> bool:
    return any({a, b, c} <= set(line) for line in FANO_LINES)


def fano_support(braid: Braid) -> Tuple[int, ...]:
    """Generator support ``{i : σᵢ^{±1} occurs}``; on eight strands these are the
    Fano points."""
    return tuple(sorted({abs(g) for g in braid.short_form()}))


def uv_span(braid: Braid) -> Tuple[int, ...]:
    return fano_close([p for p in fano_support(braid) if 1 <= p <= 7])


def uv_complete(braid: Braid) -> bool:
    return len(uv_span(braid)) == 7


def uv_completion(braid: Braid) -> List[int]:
    """The generators that UV-heal the word: closure minus support."""
    sup = set(fano_support(braid))
    return [p for p in uv_span(braid) if p not in sup]


def hamming_syndrome(bits: Sequence[int]) -> int:
    """Syndrome of a 7-bit word: XOR of the positions ``j+1`` of the set bits."""
    s = 0
    for j, b in enumerate(bits):
        if b:
            s ^= j + 1
    return s


def hamming_decode(bits: Sequence[int]) -> List[int]:
    """Correct a single bit error (the syndrome names the position)."""
    out = list(bits)
    s = hamming_syndrome(out)
    if s:
        out[s - 1] ^= 1
    return out


def hamming_codewords() -> List[Tuple[int, ...]]:
    words = []
    for c in range(128):
        bits = [(c >> j) & 1 for j in range(7)]
        if hamming_syndrome(bits) == 0:
            words.append(tuple(bits))
    return words


def fano_checksum(short: Sequence[int]) -> int:
    """XOR of the Fano points of the letters (eight strands)."""
    s = 0
    for g in short:
        s ^= abs(g)
    return s


def balance(short: Sequence[int]) -> List[int]:
    """Append (at most) one generator so the Fano checksum becomes zero."""
    c = fano_checksum(short)
    return list(short) + ([c] if c else [])


# ===========================================================================
# 4. Gap filling with anchors
# ===========================================================================

GAP = None  # marker for an unknown letter in a short-form word


@dataclass
class AnchorReport:
    name: str
    kind: str  # "exact", "necessary", "evidence"
    passed: bool
    detail: str = ""


@dataclass
class HealResult:
    status: str  # "healed", "ambiguous", "inconsistent"
    word: Optional[List[int]]
    candidates: List[List[int]]
    harmonic_choice: Optional[List[int]]
    fano_choice: Optional[List[int]]
    anchors: List[AnchorReport] = field(default_factory=list)
    energies: Dict[Tuple[int, ...], float] = field(default_factory=dict)
    notes: List[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return self.status == "healed"


def letters(n: int) -> List[int]:
    return [s * i for i in range(1, n) for s in (1, -1)]


def _fill(partial: Sequence[Optional[int]], choice: Sequence[int]) -> List[int]:
    it = iter(choice)
    return [next(it) if g is GAP else g for g in partial]


def defect_energy(word: Sequence[int], target: Braid, points: int = 17) -> float:
    """Arc energy of the defect ``target⁻¹ · word`` (zero iff Burau-trivial on
    the arc grid)."""
    b = Braid.from_short_form(target.strand_count, list(word))
    return arc_energy(target.inverse() * b, points)


def fano_gap_candidate(partial: Sequence[Optional[int]], writhe_target: int) -> Optional[int]:
    """Lean ``fanoCandidate``: generator from the checksum of the known letters,
    sign from the writhe anchor.  Only for a single gap on eight strands."""
    known = [g for g in partial if g is not GAP]
    p = fano_checksum(known)
    if not 1 <= p <= 7:
        return None
    w = sum(1 if g > 0 else -1 for g in known)
    return p if writhe_target - w == 1 else -p


def verify_anchors(word: Sequence[int], target: Braid) -> List[AnchorReport]:
    """Check the anchor table of the design on a candidate ``word``."""
    n = target.strand_count
    b = Braid.from_short_form(n, list(word))
    rep: List[AnchorReport] = [
        AnchorReport("garside_nf", "exact", left_normal_form(b) == left_normal_form(target),
                     "complete invariant of B_n (GarsideUniqueness)"),
        AnchorReport("burau", "exact", anchor_reading(b) == anchor_reading(target),
                     "reduced Burau over Z[t,t^-1] (faithful for n <= 3)"),
        AnchorReport("permutation", "necessary", permutation(b) == permutation(target)),
        AnchorReport("writhe", "necessary", writhe(b) == writhe(target)),
        AnchorReport("linking_spectrum", "necessary",
                     sorted(linking_matrix(b).values()) == sorted(linking_matrix(target).values())),
    ]
    e = arc_energy(target.inverse() * b, 17)
    rep.append(AnchorReport("harmonic_energy", "evidence", e < 1e-9, f"defect arc energy {e:.3g}"))
    if n == 8:
        rep.append(AnchorReport("fano_span", "necessary", uv_span(b) == uv_span(target),
                                f"span {uv_span(b)}"))
    return rep


def fill_gaps(
    partial: Sequence[Optional[int]],
    target: Braid,
    *,
    use_fano: bool = False,
    max_gaps: int = 3,
) -> HealResult:
    """Fill the gaps (``GAP``) of a short-form word so that it represents
    ``target``.

    * **harmonic candidate**: the filling minimising the defect arc energy;
    * **Fano candidate** (single gap, eight strands, ``use_fano``): from the
      checksum of the transmitted word (assumed balanced) and the writhe of
      the target;
    * **anchor**: the filling must pass the exact anchor (Garside NF).

    Status ``healed`` if exactly one filling passes and (when used) the Fano
    candidate agrees; ``ambiguous`` if several fillings pass (the number of
    solutions is reported — for one gap this cannot happen: ``gap_unique``);
    ``inconsistent`` if the candidates conflict (``conflict_detects``) or no
    filling passes."""
    n = target.strand_count
    k = sum(1 for g in partial if g is GAP)
    if k > max_gaps:
        raise ValueError(f"{k} gaps exceed max_gaps={max_gaps}")
    energies: Dict[Tuple[int, ...], float] = {}
    passing: List[List[int]] = []
    for choice in itertools.product(letters(n), repeat=k):
        w = _fill(partial, choice)
        energies[choice] = defect_energy(w, target)
        if braid_group_equal(Braid.from_short_form(n, w), target):
            passing.append(w)
    best = min(energies, key=energies.get) if energies else ()
    harmonic = _fill(partial, best)
    fano = None
    notes: List[str] = []
    if use_fano:
        if n != 8 or k != 1:
            notes.append("Fano candidate needs exactly one gap on eight strands")
        else:
            g = fano_gap_candidate(partial, writhe(target))
            fano = _fill(partial, [g]) if g is not None else None
    if not passing:
        return HealResult("inconsistent", None, [], harmonic, fano, [], energies,
                          notes + ["no filling satisfies the exact anchor"])
    if len(passing) > 1:
        return HealResult("ambiguous", None, passing, harmonic, fano, [], energies,
                          notes + [f"{len(passing)} fillings satisfy the anchor"])
    word = passing[0]
    if harmonic != word:
        notes.append("harmonic ranking tie/miss; the exact anchor decided")
    if use_fano and fano != word:
        return HealResult("inconsistent", word, passing, harmonic, fano,
                          verify_anchors(word, target), energies,
                          notes + ["Fano candidate conflicts with the anchor: the transmitted "
                                   "word was not checksum-balanced"])
    return HealResult("healed", word, passing, harmonic, fano, verify_anchors(word, target),
                      energies, notes)


def heal_claim(b1: Braid, b2: Braid) -> Tuple[Braid, float]:
    """Heal the claim ``b1 = b2``: return the defect ``b2⁻¹ b1`` and its arc
    energy (zero iff the claim is Burau-true on the arc grid)."""
    d = b2.inverse() * b1
    return d, arc_energy(d)


# ===========================================================================
# 5. Geometric layer (point clouds; optional GNP)
# ===========================================================================


def strand_paths(braid: Braid, samples: int = 24, radius: float = 1.0,
                 height: float = 1.0) -> List[np.ndarray]:
    """Polyline of each strand in ℝ³ (closure drawn in a solid torus, axis z).

    Strand positions are radial offsets; a crossing σᵢ^{±1} exchanges the
    strands at positions ``i, i+1`` with a smooth half-turn and a z-bump whose
    sign records over/under."""
    n = braid.strand_count
    word = braid.short_form()
    L = max(len(word), 1)
    pos = list(range(n))  # pos[strand] = position (0-based)
    paths: List[List[np.ndarray]] = [[] for _ in range(n)]

    def place(p: float, t: float, bump: float) -> np.ndarray:
        ang = 2 * math.pi * t
        r = radius + 0.7 * (p - (n - 1) / 2) / max(n - 1, 1)
        return np.array([r * math.cos(ang), r * math.sin(ang), height * bump])

    for step in range(L):
        g = word[step] if word else 0
        i = abs(g) - 1 if g else -1
        for s in range(samples):
            u = s / samples
            t = (step + u) / L
            for strand in range(n):
                p = pos[strand]
                if g and p in (i, i + 1):
                    other = i + 1 if p == i else i
                    q = p + (other - p) * (0.5 - 0.5 * math.cos(math.pi * u))
                    over = (p == i) == (g > 0)
                    bump = 0.25 * math.sin(math.pi * u) * (1 if over else -1)
                    paths[strand].append(place(q, t, bump))
                else:
                    paths[strand].append(place(p, t, 0.0))
        if g:
            a, b = pos.index(i), pos.index(i + 1)
            pos[a], pos[b] = pos[b], pos[a]
    return [np.array(p) for p in paths]


def strand_point_cloud(braid: Braid, samples: int = 24) -> List[np.ndarray]:
    """Closed polylines of the closure components (strand paths concatenated
    along the permutation cycles)."""
    paths = strand_paths(braid, samples)
    return [np.concatenate([paths[s - 1] for s in comp]) for comp in closure_components(braid)]


def discrete_curvature(curve: np.ndarray) -> np.ndarray:
    """Turning-angle curvature of a closed polyline (per vertex)."""
    prev = np.roll(curve, 1, axis=0)
    nxt = np.roll(curve, -1, axis=0)
    a = curve - prev
    b = nxt - curve
    na = np.linalg.norm(a, axis=1) + 1e-12
    nb = np.linalg.norm(b, axis=1) + 1e-12
    cos = np.clip(np.sum(a * b, axis=1) / (na * nb), -1, 1)
    return np.arccos(cos) / (0.5 * (na + nb))


def curve_shortening(curve: np.ndarray, steps: int = 50, dt: float = 0.2) -> List[np.ndarray]:
    """Discrete curve-shortening (Laplacian) flow on a closed polyline — the
    curvature-driven shape evolution of the design note."""
    out = [np.asarray(curve, dtype=float)]
    for _ in range(steps):
        c = out[-1]
        out.append(c + dt * (np.roll(c, 1, axis=0) - 2 * c + np.roll(c, -1, axis=0)))
    return out


class ClassicalGeometry:
    """Classical point-cloud geometry: local-PCA curvature and a k-NN graph
    Laplacian (heat smoothing).  Always available."""

    name = "classical"

    def __init__(self, k: int = 8):
        self.k = k

    def _knn(self, pts: np.ndarray) -> np.ndarray:
        d = np.linalg.norm(pts[:, None, :] - pts[None, :, :], axis=2)
        return np.argsort(d, axis=1)[:, 1:self.k + 1]

    def curvature(self, pts: np.ndarray) -> np.ndarray:
        """Surface-variation proxy ``λ_min / Σλ`` of the local covariance."""
        nb = self._knn(pts)
        out = np.empty(len(pts))
        for i, idx in enumerate(nb):
            q = pts[np.r_[i, idx]]
            ev = np.linalg.eigvalsh(np.cov((q - q.mean(0)).T))
            out[i] = ev[0] / max(ev.sum(), 1e-12)
        return out

    def laplacian(self, pts: np.ndarray) -> np.ndarray:
        nb = self._knn(pts)
        m = len(pts)
        W = np.zeros((m, m))
        for i, idx in enumerate(nb):
            W[i, idx] = 1.0
        W = np.maximum(W, W.T)
        return np.diag(W.sum(1)) - W

    def heat_smooth(self, pts: np.ndarray, values: np.ndarray, t: float = 0.1,
                    steps: int = 10) -> np.ndarray:
        L = self.laplacian(pts)
        L = L / max(np.abs(L).max(), 1e-12)
        v = np.asarray(values, dtype=float)
        for _ in range(steps):
            v = v - t * (L @ v)
        return v


class GNPGeometry(ClassicalGeometry):
    """Adapter for a Geometric Neural Operator (``geo_neural_op``) model.

    Pass ``curvature_model``: a callable ``(N, 3) array -> (N,) array``
    (e.g. a pretrained GNP curvature estimator wrapped by the user).  Methods
    without a model fall back to :class:`ClassicalGeometry`."""

    name = "gnp"

    def __init__(self, curvature_model: Optional[Callable[[np.ndarray], np.ndarray]] = None,
                 k: int = 8):
        super().__init__(k)
        self.curvature_model = curvature_model

    def curvature(self, pts: np.ndarray) -> np.ndarray:
        if self.curvature_model is None:
            return super().curvature(pts)
        return np.asarray(self.curvature_model(np.asarray(pts, dtype=float)), dtype=float)


def gnp_available() -> bool:
    """Is the optional ``geo_neural_op`` package importable?"""
    try:  # pragma: no cover - depends on the environment
        import geo_neural_op  # noqa: F401
        return True
    except Exception:
        return False


def geometry_backend(curvature_model: Optional[Callable] = None) -> ClassicalGeometry:
    """GNP adapter if a model is given, otherwise the classical estimator."""
    if curvature_model is not None:
        return GNPGeometry(curvature_model)
    return ClassicalGeometry()


# ===========================================================================
# 6. Invariant summary (feeds the visual/audible output)
# ===========================================================================


def cycle_type(perm: Sequence[int]) -> Tuple[int, ...]:
    """Cycle type of a permutation in one-line form on ``1..n`` (or ``0..n-1``)."""
    p = list(perm)
    if p and min(p) == 1:
        p = [x - 1 for x in p]
    seen = [False] * len(p)
    out = []
    for i in range(len(p)):
        if not seen[i]:
            c, j = 0, i
            while not seen[j]:
                seen[j] = True
                j = p[j]
                c += 1
            out.append(c)
    return tuple(sorted(out, reverse=True))


def resonance_count(braid: Braid, points: int = 181) -> int:
    """Number of boundary crossings of the resonance set as θ sweeps
    ``[0, 2π)`` (entries/exits of 'some eigenvalue on the unit circle')."""
    if braid.strand_count < 2:
        return 0
    th = np.linspace(0, 2 * math.pi, points, endpoint=False)
    on = [bool(np.any(np.abs(np.abs(burau_eigenvalues(braid, t)) - 1) < 1e-6)) for t in th]
    return sum(1 for a, b in zip(on, on[1:] + on[:1]) if a != b)


def invariant_summary(braid: Braid) -> Dict[str, object]:
    perm = permutation(braid)
    return {
        "strands": braid.strand_count,
        "word": braid.short_form(),
        "permutation": tuple(perm),
        "cycle_type": cycle_type(perm),
        "writhe": writhe(braid),
        "linking": sorted(linking_matrix(braid).values()),
        "components": len(closure_components(braid)),
        "eigenvalues_arc": burau_eigenvalues(braid, 0.5 * arc_bound(braid.strand_count)),
        "arc_energy": arc_energy(braid),
        "resonance_count": resonance_count(braid),
        "fano_span": uv_span(braid),
        "burau_trivial": is_burau_trivial(braid),
    }
