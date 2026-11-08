"""The project's AI personas as pluggable policies inside the running manifold.

The refinery personas (`refinery/personas/*.md`) and the QBX agent roles (`QBX/agents/roles/`)
are prompts for language models.  Here each persona becomes a small, deterministic policy with
the same job description, so the manifold can run without a model and every decision is
reproducible.  A persona sees the tick report and may act on the manifold.

| persona (source)                         | job in the runtime                                           |
|------------------------------------------|--------------------------------------------------------------|
| Harmonic Analyst (harmonic_analyst.md)   | finds the dominant bands and resonance between blocks        |
| Adversarial Critic (adversarial_critic.md) | injects faults (bit flips, replica corruption, noise) on purpose |
| Pipeline Auditor (pipeline_auditor.md)   | checks the proved invariants every tick; triggers healing    |
| Structural Engineer (structural_engineer.md) | tunes the denoise threshold (self-improvement)           |
| Cross-Domain Architect (cross_domain_architect.md) | decides when to CD-double blocks (resonance -> compression) |
"""
import random


class Persona:
    name = "persona"

    def act(self, m, report):
        return None


class HarmonicAnalyst(Persona):
    name = "harmonic_analyst"

    def act(self, m, report):
        be = report.get("band_energy") or {}
        tot = sum(be.values()) or 1.0
        top = sorted(be.items(), key=lambda kv: -kv[1])[:3]
        return {"dominant_bands": [(b, round(e / tot, 3)) for b, e in top],
                "resonance": report.get("resonance")}


class AdversarialCritic(Persona):
    """Attacks the system so that healing is exercised.  `rate` = expected flips per block."""
    name = "adversarial_critic"

    def __init__(self, rate=0.5, replica_attack=0.05, seed=7):
        self.rate, self.replica_attack = rate, replica_attack
        self.rnd = random.Random(seed)

    def corrupt_cells(self, cells):
        flips = 0
        for i in range(len(cells)):
            if self.rnd.random() < self.rate / max(1, len(cells)) * 3:
                cells[i] ^= 1 << self.rnd.randrange(6)
                flips += 1
        return flips

    def act(self, m, report):
        if self.rnd.random() < self.replica_attack:
            k = self.rnd.randrange(3)
            m.corrupt_replica(k, self.rnd.randrange(1 << 20))
            return {"attacked_replica": k}
        return None


class PipelineAuditor(Persona):
    name = "pipeline_auditor"

    def act(self, m, report):
        problems = []
        if report.get("join_error", 0) > 1e-6:
            problems.append("split/join not lossless")
        if report.get("energy_error", 0) > 1e-6:
            problems.append("band energies do not add up")
        if m.gov.speed > m.gov.vmax:
            problems.append("speed above vmax")
        if not m.replicas_agree():
            problems.append("control replicas disagree")
        if problems:
            m.self_heal(problems)
        return {"problems": problems}


class StructuralEngineer(Persona):
    """Self-improvement: tune the denoise threshold multiplier by paired probing.
    It runs the current multiplier c as c + d for `window` ticks, then c - d for `window` ticks,
    and moves c by `step` toward the probe with the higher mean quality (SNR against the clean
    reference when the source has one).  Paired probing averages out block-to-block noise, so c
    drifts toward the best multiplier instead of oscillating."""
    name = "structural_engineer"

    def __init__(self, step=0.1, probe=0.25, window=3):
        self.step, self.probe, self.window = step, probe, window
        self.c, self.phase, self.scores, self.history = 1.0, 0, {+1: [], -1: []}, []

    def act(self, m, report):
        q = report.get("quality")
        if q is None:
            return None
        side = +1 if self.phase < self.window else -1
        self.scores[side].append(q)
        self.phase += 1
        if self.phase == 2 * self.window:
            up = sum(self.scores[+1]) / len(self.scores[+1])
            dn = sum(self.scores[-1]) / len(self.scores[-1])
            self.c = min(3.0, max(0.0, self.c + (self.step if up > dn else -self.step)))
            self.history.append((round(self.c, 2), round(max(up, dn), 2)))
            self.phase, self.scores = 0, {+1: [], -1: []}
        side = +1 if self.phase < self.window else -1
        m.threshold_mult = max(0.0, self.c + side * self.probe)
        return {"centre": round(self.c, 2), "probing": round(m.threshold_mult, 2), "quality": round(q, 2)}


class CrossDomainArchitect(Persona):
    name = "cross_domain_architect"

    def __init__(self, on=0.95):
        self.on = on

    def act(self, m, report):
        r = report.get("resonance")
        m.double_blocks = r is not None and r >= self.on
        return {"double_blocks": m.double_blocks}


def default_team(seed=7, attack_rate=0.5):
    return [AdversarialCritic(rate=attack_rate, seed=seed), HarmonicAnalyst(), PipelineAuditor(),
            StructuralEngineer(), CrossDomainArchitect()]
