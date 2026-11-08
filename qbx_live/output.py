"""
Visual and audible output for braid invariants (``qbx_live``).

Mapping (design note §5)
------------------------

==================  ======================================  ==========================================
invariant           visual                                  audible
==================  ======================================  ==========================================
permutation         vertex/path on the permutohedron        chord quality from the cycle type
writhe              strand colours (red +, blue −)          pitch shift (one semitone per unit)
linking spectrum    linkage diagram (thickness = |lk|)      added intervals (|lk| semitones)
Burau eigenvalues   trajectories in ℂ over the θ-sweep      drone partials (|λ| → amplitude, arg → pan)
resonance count     crossings of the unit circle            number of chorus voices
harmonic energy     heat map E_θ(prefix)                    dissonance (beating detune + tritone)
Fano span           Fano plane with covered points          timbre (number of harmonics)
==================  ======================================  ==========================================

All functions take a :class:`qbx_ir.core.braid.Braid`; plots return the
matplotlib axes / figure, audio functions return float arrays in ``[-1, 1]``
of shape ``(samples, 2)`` (stereo).
"""

from __future__ import annotations

import io
import itertools
import math
import wave
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np

from qbx_ir.algebra.invariants import closure_components, linking_matrix, permutation, writhe
from qbx_ir.core.braid import Braid
from qbx_live import healing as H

SAMPLE_RATE = 22050

# ===========================================================================
# Visual
# ===========================================================================


def _plt():
    import matplotlib.pyplot as plt

    return plt


def plot_braid(braid: Braid, ax=None, title: Optional[str] = None):
    """Braid diagram, bottom to top; crossing colour = sign (red +, blue −)."""
    plt = _plt()
    if ax is None:
        _, ax = plt.subplots(figsize=(3, 4))
    n = braid.strand_count
    word = braid.short_form()
    pos = list(range(n))
    for step, g in enumerate(word):
        i = abs(g) - 1
        for strand in range(n):
            p = pos[strand]
            if p in (i, i + 1):
                continue
            ax.plot([p, p], [step, step + 1], color="0.35", lw=2)
        colour = "#d62728" if g > 0 else "#1f77b4"
        # positive crossing: the strand moving right (i -> i+1) passes over
        over = (i, i + 1) if g > 0 else (i + 1, i)
        under = (over[1], over[0])
        ax.plot([over[0], over[1]], [step, step + 1], color=colour, lw=3, solid_capstyle="round")
        for s0, s1 in ((0.0, 0.38), (0.62, 1.0)):
            ax.plot([under[0] + s0 * (under[1] - under[0]), under[0] + s1 * (under[1] - under[0])],
                    [step + s0, step + s1], color=colour, lw=3, solid_capstyle="round")
        a, b = pos.index(i), pos.index(i + 1)
        pos[a], pos[b] = pos[b], pos[a]
    if not word:
        for p in range(n):
            ax.plot([p, p], [0, 1], color="0.35", lw=2)
    ax.set_xlim(-0.5, n - 0.5)
    ax.set_ylim(0, max(len(word), 1))
    ax.set_xticks(range(n))
    ax.set_xticklabels([str(k + 1) for k in range(n)])
    ax.set_yticks([])
    ax.set_title(title or f"β = {word}  (writhe {writhe(braid)})", fontsize=9)
    return ax


def _perm_after(n: int, prefix: Sequence[int]) -> Tuple[int, ...]:
    return tuple(permutation(Braid.from_short_form(n, list(prefix))))


def _project(perms: List[Tuple[int, ...]]) -> np.ndarray:
    """Project permutation vectors onto the plane orthogonal to (1,…,1)."""
    inv = []
    for p in perms:  # vertex coordinates: positions of the values 1..n
        q = [0] * len(p)
        for i, v in enumerate(p):
            q[v - 1] = i + 1
        inv.append(q)
    X = np.array(inv, dtype=float)
    X = X - X.mean(axis=1, keepdims=True)
    n = X.shape[1]
    # orthonormal basis of the sum-zero plane: two fixed directions
    u = np.cos(2 * np.pi * np.arange(n) / n)
    v = np.sin(2 * np.pi * np.arange(n) / n)
    return np.stack([X @ u, X @ v], axis=1)


def plot_permutohedron(braid: Braid, ax=None):
    """The permutohedron Pₙ (n ≤ 5, Cayley graph of adjacent transpositions)
    with the path of prefix permutations; the final vertex is highlighted."""
    plt = _plt()
    if ax is None:
        _, ax = plt.subplots(figsize=(4, 4))
    n = braid.strand_count
    word = braid.short_form()
    path = [_perm_after(n, word[:k]) for k in range(len(word) + 1)]
    if n <= 5:
        perms = list(itertools.permutations(range(1, n + 1)))
    else:  # too many vertices: draw the path and its neighbours only
        perms = sorted(set(path) | {tuple(p[:i] + (p[i + 1], p[i]) + p[i + 2:])
                                    for p in path for i in range(n - 1)})
    idx = {p: k for k, p in enumerate(perms)}
    P = _project(perms)
    for p in perms:
        for i in range(n - 1):
            q = list(p)
            q[i], q[i + 1] = q[i + 1], q[i]
            q = tuple(q)
            if q in idx and idx[q] > idx[p]:
                ax.plot(*P[[idx[p], idx[q]]].T, color="0.85", lw=1, zorder=1)
    ax.scatter(*P.T, s=12, color="0.6", zorder=2)
    pts = P[[idx[p] for p in path]]
    ax.plot(*pts.T, color="#2ca02c", lw=2.5, zorder=3)
    ax.scatter(*pts[:1].T, s=60, color="black", zorder=4, label="identity")
    ax.scatter(*pts[-1:].T, s=140, color="#ff7f0e", edgecolor="black", zorder=5,
               label=f"π = {path[-1]}")
    ax.set_aspect("equal")
    ax.axis("off")
    ax.legend(loc="lower center", fontsize=7, frameon=False)
    ax.set_title(f"permutohedron P{n}: fold path" + ("" if n <= 5 else " (local)"), fontsize=9)
    return ax


def plot_eigen_trajectories(braid: Braid, ax=None, points: int = 361):
    """Burau eigenvalues of ρ̄(β)(e^{iθ}) over θ ∈ [0, 2π), coloured by θ; the
    universal arc |θ| < 2π/n is drawn bold (eigenvalues stay on the circle)."""
    plt = _plt()
    if ax is None:
        _, ax = plt.subplots(figsize=(4, 4))
    th = np.linspace(-np.pi, np.pi, points)
    ev = np.array([np.sort_complex(H.burau_eigenvalues(braid, t)) for t in th])
    circ = np.exp(1j * np.linspace(0, 2 * np.pi, 400))
    ax.plot(circ.real, circ.imag, color="0.7", lw=1)
    arc = np.abs(th) < H.arc_bound(braid.strand_count)
    for j in range(ev.shape[1]):
        ax.scatter(ev[:, j].real, ev[:, j].imag, c=th, cmap="twilight", s=4)
        ax.scatter(ev[arc, j].real, ev[arc, j].imag, color="black", s=6)
    ax.scatter([1], [0], marker="*", s=120, color="#ff7f0e", zorder=5, label="λ = 1 (healed)")
    ax.set_aspect("equal")
    lim = max(1.2, float(np.max(np.abs(ev))) * 1.05) if ev.size else 1.2
    lim = min(lim, 4)
    ax.set_xlim(-lim, lim)
    ax.set_ylim(-lim, lim)
    ax.legend(fontsize=7, loc="upper left", frameon=False)
    ax.set_title("Burau eigenvalues (black: universal arc)", fontsize=9)
    return ax


def plot_energy_landscape(braid: Braid, ax=None, points: int = 121):
    """Heat map of the spectral energy ``E_θ(β₁⋯β_k)`` over prefixes k and θ."""
    plt = _plt()
    if ax is None:
        _, ax = plt.subplots(figsize=(5, 3))
    n = braid.strand_count
    word = braid.short_form()
    th = np.linspace(-np.pi, np.pi, points)
    Z = np.array([[H.spectral_energy(Braid.from_short_form(n, word[:k]), t) for t in th]
                  for k in range(len(word) + 1)])
    im = ax.imshow(np.log1p(Z), aspect="auto", origin="lower", cmap="magma",
                   extent=[th[0], th[-1], -0.5, len(word) + 0.5])
    b = H.arc_bound(n)
    ax.axvline(-b, color="cyan", lw=1, ls="--")
    ax.axvline(b, color="cyan", lw=1, ls="--")
    ax.set_xlabel("θ")
    ax.set_ylabel("prefix length")
    ax.set_title("harmonic energy log(1+E_θ) (dashed: universal arc)", fontsize=9)
    plt.colorbar(im, ax=ax, fraction=0.046)
    return ax


_FANO_XY = {
    1: (0.0, 1.0), 2: (-0.866, -0.5), 3: (-0.433, 0.25), 4: (0.866, -0.5),
    5: (0.433, 0.25), 6: (0.0, -0.5), 7: (0.0, 0.0),
}


def plot_fano(span: Sequence[int] = (), ax=None, support: Sequence[int] = (), title: str = ""):
    """The Fano plane; points of the UV span are filled (support in orange,
    healed points in green); lines inside the span are drawn bold."""
    plt = _plt()
    from matplotlib.patches import Circle

    if ax is None:
        _, ax = plt.subplots(figsize=(3.2, 3.2))
    span, support = set(span), set(support)
    for line in H.FANO_LINES:
        bold = set(line) <= span
        if set(line) == {3, 5, 6}:  # the inscribed circle
            ax.add_patch(Circle((0, 0), 0.5, fill=False, lw=3 if bold else 1,
                                color="#2ca02c" if bold else "0.6"))
            continue
        xy = np.array([_FANO_XY[p] for p in line])
        order = np.argsort(xy[:, 0] + 1e-3 * xy[:, 1])
        ax.plot(*xy[order].T, lw=3 if bold else 1, color="#2ca02c" if bold else "0.6")
    for p, (x, y) in _FANO_XY.items():
        colour = "#ff7f0e" if p in support else ("#2ca02c" if p in span else "white")
        ax.scatter([x], [y], s=380, color=colour, edgecolor="black", zorder=3)
        ax.text(x, y, f"e{p}", ha="center", va="center", fontsize=8, zorder=4)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title(title or f"Fano span {sorted(span)}", fontsize=9)
    return ax


def plot_linkage(braid: Braid, ax=None):
    """Closure components on a circle; edge thickness = |linking number|,
    colour = sign."""
    plt = _plt()
    if ax is None:
        _, ax = plt.subplots(figsize=(3.2, 3.2))
    comps = closure_components(braid)
    m = len(comps)
    ang = 2 * np.pi * np.arange(m) / max(m, 1)
    xy = np.stack([np.cos(ang), np.sin(ang)], 1)
    lk = linking_matrix(braid)
    for (a, b), v in lk.items():
        if v:
            ax.plot(*xy[[a, b]].T, lw=1.5 + 2.5 * abs(v),
                    color="#d62728" if v > 0 else "#1f77b4", alpha=0.8)
            mid = xy[[a, b]].mean(0)
            ax.text(*mid, str(v), fontsize=8, ha="center",
                    bbox=dict(boxstyle="round", fc="white", ec="0.7"))
    for k, c in enumerate(comps):
        ax.scatter(*xy[k], s=500, color="#9467bd", edgecolor="black", zorder=3)
        ax.text(*xy[k], "".join(map(str, c)), ha="center", va="center", color="white",
                fontsize=8, zorder=4)
    ax.set_xlim(-1.6, 1.6)
    ax.set_ylim(-1.6, 1.6)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.set_title(f"linkage: {m} component(s)", fontsize=9)
    return ax


def plot_healing_flow(braid: Braid, ax=None, kappa: float = 0.25, steps: int = 24):
    """Eigenvalue healing: the phases at mid-arc flow to 0 (λ → 1); inset-free
    two-panel plot of eigenvalue paths and energy decay."""
    plt = _plt()
    if ax is None:
        _, ax = plt.subplots(1, 2, figsize=(7, 3))
    th = 0.5 * H.arc_bound(braid.strand_count)
    flow = H.phase_flow(H.eigen_phases(braid, th), kappa, steps)
    circ = np.exp(1j * np.linspace(0, 2 * np.pi, 400))
    ax[0].plot(circ.real, circ.imag, color="0.8")
    for j in range(flow.shape[1]):
        z = np.exp(1j * flow[:, j])
        ax[0].plot(z.real, z.imag, "o-", ms=3)
    ax[0].scatter([1], [0], marker="*", s=150, color="#ff7f0e", zorder=5)
    ax[0].set_aspect("equal")
    ax[0].set_title(f"eigenvalue healing at θ = π/{braid.strand_count}", fontsize=9)
    e = H.phase_energy(flow)
    bound = ((1 - kappa) ** 2) ** np.arange(steps + 1) * np.sum(flow[0] ** 2)
    ax[1].semilogy(e + 1e-16, "o-", label="energy Σ|λ−1|²")
    ax[1].semilogy(bound + 1e-16, "--", label="proved bound (1−κ)^{2k} Σφ₀²")
    ax[1].set_xlabel("healing step k")
    ax[1].legend(fontsize=7)
    ax[1].set_title("geometric convergence", fontsize=9)
    return ax


def plot_point_cloud(braid: Braid, ax=None, backend: Optional[H.ClassicalGeometry] = None,
                     samples: int = 16):
    """3-D closure point cloud coloured by estimated curvature."""
    plt = _plt()
    if ax is None:
        fig = plt.figure(figsize=(4, 4))
        ax = fig.add_subplot(111, projection="3d")
    backend = backend or H.ClassicalGeometry()
    for comp in H.strand_point_cloud(braid, samples):
        k = H.discrete_curvature(comp)
        ax.plot(*comp.T, color="0.6", lw=0.8)
        ax.scatter(*comp.T, c=k, cmap="viridis", s=6)
    ax.set_title(f"closure point cloud ({backend.name} geometry)", fontsize=9)
    ax.set_axis_off()
    return ax


def dashboard(braid: Braid, title: str = ""):
    """All panels for one braid in a single figure."""
    plt = _plt()
    fig = plt.figure(figsize=(14, 7.5))
    gs = fig.add_gridspec(2, 4)
    plot_braid(braid, fig.add_subplot(gs[0, 0]))
    plot_permutohedron(braid, fig.add_subplot(gs[0, 1]))
    plot_eigen_trajectories(braid, fig.add_subplot(gs[0, 2]))
    plot_linkage(braid, fig.add_subplot(gs[0, 3]))
    plot_energy_landscape(braid, fig.add_subplot(gs[1, :2]))
    sup = [p for p in H.fano_support(braid) if p <= 7]
    plot_fano(H.uv_span(braid), fig.add_subplot(gs[1, 2]), support=sup)
    plot_point_cloud(braid, fig.add_subplot(gs[1, 3], projection="3d"))
    fig.suptitle(title or f"β = {braid.short_form()} on {braid.strand_count} strands")
    fig.tight_layout()
    return fig


# ===========================================================================
# Audible
# ===========================================================================

#: Chord (semitone offsets) by cycle type of the permutation.
def chord_for_cycle_type(ct: Tuple[int, ...]) -> Tuple[int, ...]:
    nontriv = [c for c in ct if c > 1]
    if not nontriv:
        return (0, 4, 7)          # identity: major
    if nontriv == [2]:
        return (0, 3, 7)          # one transposition: minor
    if max(nontriv) >= 3 and len(nontriv) == 1:
        return (0, 3, 6)          # one long cycle: diminished
    return (0, 4, 8)              # several cycles: augmented


def _tone(freq: float, t: np.ndarray, harmonics: int = 3) -> np.ndarray:
    out = np.zeros_like(t)
    for h in range(1, harmonics + 1):
        out += np.sin(2 * np.pi * freq * h * t) / h
    return out / sum(1 / h for h in range(1, harmonics + 1))


def _envelope(t: np.ndarray, attack: float = 0.05, release: float = 0.3) -> np.ndarray:
    d = t[-1] if len(t) else 1
    env = np.minimum(1, t / attack) * np.minimum(1, np.maximum(0, (d - t)) / release)
    return env


def _pan(mono: np.ndarray, pan: float) -> np.ndarray:
    pan = float(np.clip(pan, -1, 1))
    left = math.cos((pan + 1) * math.pi / 4)
    right = math.sin((pan + 1) * math.pi / 4)
    return np.stack([mono * left, mono * right], 1)


def sonify(braid: Braid, duration: float = 3.0, sr: int = SAMPLE_RATE,
           energy_override: Optional[float] = None, summary: Optional[Dict] = None) -> np.ndarray:
    """Render the invariants of a braid as a stereo sound (see module table)."""
    s = summary or H.invariant_summary(braid)
    t = np.arange(int(duration * sr)) / sr
    base = 220.0 * 2 ** (np.clip(s["writhe"], -12, 12) / 12)
    harmonics = 1 + len(s["fano_span"])
    energy = s["arc_energy"] if energy_override is None else energy_override
    detune = 0.04 * energy / (1 + energy)
    out = np.zeros((len(t), 2))
    # chord (permutation) with chorus voices (resonance count)
    voices = 1 + min(int(s["resonance_count"]), 4)
    for semis in chord_for_cycle_type(s["cycle_type"]):
        f = base * 2 ** (semis / 12)
        for v in range(voices):
            dv = (v - (voices - 1) / 2) * 0.003
            mono = _tone(f * (1 + dv), t, harmonics) + _tone(f * (1 + detune), t, harmonics)
            out += _pan(0.5 * mono, (v - (voices - 1) / 2) / max(voices, 1))
    # linking intervals
    for lk in s["linking"]:
        if lk:
            f = base * 2 ** ((abs(lk) % 12 + (12 if lk > 0 else -12) * (abs(lk) // 12)) / 12)
            out += _pan(0.4 * _tone(f, t, harmonics), 0.0)
    # eigenvalue drone
    for j, lam in enumerate(np.atleast_1d(s["eigenvalues_arc"])):
        amp = 0.35 * min(abs(lam), 2.0)
        f = base / 2 * (j + 1)
        out += _pan(amp * np.sin(2 * np.pi * f * t), float(np.angle(lam)) / math.pi)
    # dissonance: tritone in proportion to the energy
    if energy > 1e-9:
        out += _pan(0.6 * energy / (1 + energy) * _tone(base * 2 ** (6 / 12), t, 2), 0.0)
    out *= _envelope(t)[:, None]
    peak = np.max(np.abs(out)) or 1.0
    return (0.9 * out / peak).astype(np.float32)


def sonify_healing(braid: Braid, steps: int = 12, kappa: float = 0.3,
                   step_duration: float = 0.45, sr: int = SAMPLE_RATE) -> np.ndarray:
    """Audible healing: along the phase flow the energy decays, the detuning
    (beating) and the tritone fade, and the sound resolves."""
    s = H.invariant_summary(braid)
    th = 0.5 * H.arc_bound(braid.strand_count)
    flow = H.phase_flow(H.eigen_phases(braid, th), kappa, steps)
    energies = H.phase_energy(flow)
    frames = []
    for k in range(steps + 1):
        s2 = dict(s)
        s2["eigenvalues_arc"] = np.exp(1j * flow[k])
        frames.append(sonify(braid, step_duration, sr, energy_override=float(energies[k]),
                             summary=s2))
    out = np.concatenate(frames)
    return out


def to_wav_bytes(audio: np.ndarray, sr: int = SAMPLE_RATE) -> bytes:
    """16-bit PCM WAV bytes of a stereo (or mono) float array."""
    a = np.asarray(audio)
    if a.ndim == 1:
        a = a[:, None]
    pcm = (np.clip(a, -1, 1) * 32767).astype("<i2")
    buf = io.BytesIO()
    with wave.open(buf, "wb") as w:
        w.setnchannels(pcm.shape[1])
        w.setsampwidth(2)
        w.setframerate(sr)
        w.writeframes(pcm.tobytes())
    return buf.getvalue()


def write_wav(path: str, audio: np.ndarray, sr: int = SAMPLE_RATE) -> None:
    with open(path, "wb") as f:
        f.write(to_wav_bytes(audio, sr))


def spectrogram(audio: np.ndarray, ax=None, sr: int = SAMPLE_RATE, title: str = ""):
    plt = _plt()
    if ax is None:
        _, ax = plt.subplots(figsize=(6, 2.5))
    mono = np.asarray(audio).mean(axis=1) if np.ndim(audio) == 2 else audio
    ax.specgram(mono, NFFT=1024, Fs=sr, noverlap=768, cmap="inferno")
    ax.set_ylim(0, 2500)
    ax.set_xlabel("time (s)")
    ax.set_ylabel("Hz")
    ax.set_title(title or "spectrogram", fontsize=9)
    return ax
