"""Adversarial falsification arbiter.

Every candidate claim goes through the stages below, cheapest first.  The first stage that
breaks it ends the trial; only survivors of every stage are handed to the Lean stager.

1. **trivial**     — the canonical form is empty (e.g. all sign factors cancel).
2. **fuzz**        — ``fuzz_samples`` random instances drawn from the entropy-driven DRBG.
3. **boundary**    — edge instances supplied by the domain (0, 1, top index, half-way points,
                     small primes, the bound itself, ...).
4. **exhaustive**  — the whole finite instance space.  The Python verdict is therefore exact,
                     and the Lean kernel re-decides it independently with its own definitions.
5. **vacuity**     — the premise must hold on at least ``domain.min_support`` instances.
6. **counter-hypothesis** — the claim is placed on its monotone ladder of strengthenings; the
                     arbiter returns the strongest true rung and the first false rung together
                     with an explicit counterexample to it.
7. **generalization** — hypotheses are dropped greedily while the claim stays true, and the
                     first false rung above the result is recomputed.
8. **null screen** — the strongest true rung must reach ``domain.min_surprise`` bits of surprise
                     under the domain's null model (where it has one).
9. **irreducibility** — claims that merely multiply together simpler laws are discarded.

The returned ``Verdict`` records how many instances each stage examined.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Optional


@dataclass
class Verdict:
    status: str   # trivial | falsified | vacuous | unsurprising | composite | survived
    genome: Any
    stage: str = ""
    counterexample: Any = None
    strongest: Any = None             # strongest true rung of the ladder
    breaker: Any = None               # first false rung of the ladder
    breaker_counterexample: Any = None
    surprise_bits: Optional[float] = None
    support: int = 0
    checked: dict = field(default_factory=dict)

    @property
    def survived(self) -> bool:
        return self.status == "survived"


def find_counterexample(domain, g, rng, fuzz_samples: int, checked: dict):
    """Run stages 2–4 on ``g``; return ``(stage, counterexample, support)``."""
    for _ in range(fuzz_samples):
        x = domain.random_instance(g, rng)
        checked["fuzz"] = checked.get("fuzz", 0) + 1
        if domain.premise(g, x) and not domain.conclusion(g, x):
            return "fuzz", x, None
    for x in domain.boundary_instances(g):
        checked["boundary"] = checked.get("boundary", 0) + 1
        if domain.premise(g, x) and not domain.conclusion(g, x):
            return "boundary", x, None
    support = 0
    for x in domain.instances(g):
        checked["exhaustive"] = checked.get("exhaustive", 0) + 1
        if domain.premise(g, x):
            support += 1
            if not domain.conclusion(g, x):
                return "exhaustive", x, support
    return None, None, support


def quick_score(domain, g, rng, samples: int = 48) -> float:
    """Fraction of sampled instances (with true premise) on which the claim holds; the smooth
    fitness signal of the annealer.  Returns 0.0 for trivial claims."""
    c = domain.canonical(g)
    if c is None:
        return 0.0
    ok = tot = 0
    for _ in range(samples):
        x = domain.random_instance(c, rng)
        if domain.premise(c, x):
            tot += 1
            ok += domain.conclusion(c, x)
    return ok / tot if tot else 0.0


def adjudicate(domain, g, rng, fuzz_samples: int = 64) -> Verdict:
    c = domain.canonical(g)
    if c is None:
        return Verdict("trivial", g, stage="trivial")
    checked: dict = {}
    stage, ce, support = find_counterexample(domain, c, rng, fuzz_samples, checked)
    verdict = Verdict("falsified" if ce is not None else "survived", c, stage=stage or "",
                      counterexample=ce, checked=checked, support=support or 0)
    if ce is None and not domain.support_ok(c, verdict.support):
        verdict.status, verdict.stage = "vacuous", "vacuity"

    # counter-hypothesis: climb the monotone ladder of strengthenings
    rungs = [domain.canonical(r) for r in domain.ladder(c)]
    strongest = None
    for r in rungs:
        if r is None:
            continue
        sub: dict = {}
        st, rce, sup = find_counterexample(domain, r, rng, fuzz_samples // 4, sub)
        for k, v in sub.items():
            checked["ladder_" + k] = checked.get("ladder_" + k, 0) + v
        if rce is None:
            if domain.support_ok(r, sup or 0):
                strongest = r
            continue
        verdict.breaker, verdict.breaker_counterexample = r, rce
        break
    # generalization: drop hypotheses while the claim stays true at the same rung
    if strongest is not None:
        improved = True
        while improved:
            improved = False
            for h in domain.generalizations(strongest):
                h = domain.canonical(h)
                if h is None:
                    continue
                sub = {}
                st, hce, sup = find_counterexample(domain, h, rng, fuzz_samples // 4, sub)
                for k, v in sub.items():
                    checked["generalize_" + k] = checked.get("generalize_" + k, 0) + v
                if hce is None and domain.support_ok(h, sup or 0):
                    strongest, improved = h, True
                    break
        # the first false rung above the (possibly generalized) strongest claim
        nxt = domain.next_rung(strongest)
        if nxt is not None:
            nxt = domain.canonical(nxt)
            sub = {}
            st, nce, _ = find_counterexample(domain, nxt, rng, fuzz_samples // 4, sub)
            if nce is not None:
                verdict.breaker, verdict.breaker_counterexample = nxt, nce
            else:  # cannot happen for a monotone ladder; recorded for the journal
                verdict.breaker, verdict.breaker_counterexample = None, None
                checked["ladder_anomaly"] = 1
        else:
            verdict.breaker, verdict.breaker_counterexample = None, None
    verdict.strongest = strongest

    if verdict.status == "survived" or (verdict.status == "falsified" and strongest is not None):
        # a falsified claim whose weaker rung is true is a *boundary* discovery:
        # promote the strongest true rung instead.
        if strongest is None:
            verdict.status, verdict.stage = "vacuous", "vacuity"
            return verdict
        bits = domain.surprise_bits(strongest)
        verdict.surprise_bits = bits
        if bits is not None and bits < domain.min_surprise:
            verdict.status, verdict.stage = "unsurprising", "null-screen"
            return verdict
        if domain.is_composite(strongest):
            verdict.status, verdict.stage = "composite", "irreducibility"
            return verdict
        verdict.status = "survived"
    return verdict
