"""The closed discovery loop: mutate → falsify → stage → burn.

Exploration is a population of Metropolis–Hastings / simulated-annealing chains over the genome
space of each domain.  All randomness comes from the entropy pool's DRBG.

Energy of a genome (lower is better)::

    E(g) = -(4·q(g) + 3·[novel] + interest(g) - λ·complexity(g))

where ``q(g)`` is the fraction of sampled instances on which the claim holds (``arbiter.
quick_score``), ``[novel]`` says that the canonical claim was neither adjudicated in this run nor burned
before, and
``complexity`` is the domain's description length and ``interest`` a domain bonus (CD level,
length of a prime run, number of primes in a residue class).  A proposal ``g'`` is accepted with
probability ``min(1, exp(-(E(g') - E(g)) / T))``; the temperature follows the geometric schedule
``T_k = T₀ · ρᵏ``.  Each chain is a path-dependent random walk: where it goes next depends on
where it has been, not on an exhaustive sweep.

Whenever a chain visits a claim with ``q(g) = 1`` that has not been adjudicated yet, the
arbiter runs the full falsification protocol.  Survivors (strongest true rung) and their
counter-hypotheses (first false rung + explicit counterexample) are staged in Lean; what the
kernel accepts is burned into the ledger.
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass, field
from pathlib import Path

from . import arbiter, stager

JOURNAL_DIR = stager.REPO_ROOT / "discovery" / "ledger" / "journal"


@dataclass
class Chain:
    domain: object
    genome: object
    energy: float
    accepted: int = 0
    proposed: int = 0
    stale: int = 0              # generations since this chain last led to a new adjudication


@dataclass
class RunConfig:
    generations: int = 200
    chains_per_domain: int = 3
    t0: float = 2.0
    rho: float = 0.985
    lam: float = 0.15
    fuzz_samples: int = 64
    max_burn: int = 40
    restart_after: int = 40       # restart a chain that found nothing new for this many gens
    stage_timeout: float = 300.0
    dry_run: bool = False         # adjudicate but do not call Lean
    lake: str = "lake"


@dataclass
class RunStats:
    proposals: int = 0
    adjudicated: int = 0
    verdicts: dict = field(default_factory=dict)
    staged: int = 0
    accepted: int = 0
    rejected: int = 0
    duplicates: int = 0
    restarts: int = 0


class DiscoveryLoop:
    def __init__(self, domains: list, entropy_seed, config: RunConfig, run_name: str,
                 ledger: stager.Ledger | None = None):
        self.domains = domains
        self.seed = entropy_seed
        self.rng = entropy_seed.rng()
        self.cfg = config
        self.run_name = run_name
        self.ledger = ledger
        self.seen: set = set()
        self.rejected: set = set()
        self.stats = RunStats()
        JOURNAL_DIR.mkdir(parents=True, exist_ok=True)
        self.journal_path = JOURNAL_DIR / f"{run_name}.jsonl"
        self._journal = open(self.journal_path, "a", encoding="utf-8")
        self.log("run_start", config=self.cfg.__dict__, entropy=entropy_seed.summary(),
                 domains=[d.name for d in domains])

    # ------------------------------------------------------------------ journal
    def log(self, event: str, **details) -> None:
        rec = {"t": round(time.time(), 3), "event": event, **details}
        self._journal.write(json.dumps(rec, ensure_ascii=False, default=str) + "\n")
        self._journal.flush()

    # ------------------------------------------------------------------ energy
    def energy(self, domain, g) -> float:
        q = arbiter.quick_score(domain, g, self.rng)
        key = domain.key(g)
        novel = key not in self.seen and (self.ledger is None
                                          or not self.ledger.is_known("theorem", key))
        return -(4.0 * q + 3.0 * novel + domain.interest(g) - self.cfg.lam * domain.complexity(g))

    # ------------------------------------------------------------------ main loop
    def run(self) -> RunStats:
        chains = []
        for d in self.domains:
            for _ in range(self.cfg.chains_per_domain):
                g = d.random_genome(self.rng)
                chains.append(Chain(d, g, self.energy(d, g)))
        T = self.cfg.t0
        for gen in range(self.cfg.generations):
            for ch in chains:
                d = ch.domain
                ch.stale += 1
                if ch.stale > self.cfg.restart_after:
                    ch.genome = d.random_genome(self.rng)
                    ch.stale = 0
                    self.stats.restarts += 1
                # the energy landscape moves (novelty is spent as claims are adjudicated)
                ch.energy = self.energy(d, ch.genome)
                prop = d.mutate(ch.genome, self.rng)
                self.stats.proposals += 1
                ch.proposed += 1
                e = self.energy(d, prop)
                if e <= ch.energy or self.rng.random() < math.exp(-(e - ch.energy) / max(T, 1e-9)):
                    ch.genome, ch.energy = prop, e
                    ch.accepted += 1
                if arbiter.quick_score(d, ch.genome, self.rng) == 1.0:
                    if self.consider(d, ch.genome, gen):
                        ch.stale = 0
                if self.ledger is not None and len(self.ledger.burned) >= self.cfg.max_burn:
                    self.log("max_burn_reached", generation=gen)
                    return self.finish()
            T *= self.cfg.rho
        return self.finish()

    def consider(self, d, g, gen: int) -> bool:
        """Adjudicate ``g`` if it is new; return whether it was new."""
        key = d.key(g)
        if key in self.seen or key == "trivial":
            return False
        self.seen.add(key)
        self.stats.adjudicated += 1
        v = arbiter.adjudicate(d, g, self.rng, self.cfg.fuzz_samples)
        self.stats.verdicts[v.status] = self.stats.verdicts.get(v.status, 0) + 1
        self.log("verdict", domain=d.name, claim=d.describe(v.genome), status=v.status,
                 stage=v.stage, checked=v.checked, surprise_bits=v.surprise_bits,
                 strongest=d.describe(v.strongest) if v.strongest is not None else None,
                 breaker=d.describe(v.breaker) if v.breaker is not None else None,
                 breaker_counterexample=(d.describe_instance(v.breaker, v.breaker_counterexample)
                                         if v.breaker is not None else None))
        if not v.survived:
            return True
        meta = {"run": self.run_name, "generation": gen, "seed_hex": self.seed.hex,
                "arbiter_checked": v.checked, "surprise_bits": v.surprise_bits}
        claims = [stager.make_claim(d, v.strongest, "theorem", meta=meta)]
        if v.breaker is not None:
            claims.append(stager.make_claim(d, v.breaker, "refutation", v.breaker_counterexample,
                                            meta=meta))
        for c in claims:
            self.promote(c)
        return True

    def promote(self, claim: stager.StagedClaim) -> None:
        if (self.ledger is not None and self.ledger.is_known(claim.kind, claim.key)) \
                or (claim.kind, claim.key) in self.rejected:
            self.stats.duplicates += 1
            return
        if self.cfg.dry_run:
            self.log("dry_run_claim", name=claim.name, statement=claim.statement)
            return
        self.stats.staged += 1
        res = stager.stage(claim, timeout=self.cfg.stage_timeout, lake=self.cfg.lake)
        self.log("staged", name=claim.name, kind=claim.kind, statement=claim.statement,
                 accepted=res.accepted, seconds=round(res.seconds, 2), axioms=res.axioms,
                 output=None if res.accepted else res.output[-2000:])
        if res.accepted:
            self.stats.accepted += 1
            if self.ledger is not None:
                self.ledger.burn(claim, res)
        else:
            # every claim reaching Lean already survived the exhaustive check, so a rejection
            # is a defect of the pipeline (Python twin ≠ Lean definition, or a rendering /
            # elaboration problem); it is journalled as such and the claim is not retried
            self.stats.rejected += 1
            self.rejected.add((claim.kind, claim.key))
            reason = ("kernel_disagrees" if "is false" in res.output else
                      "timeout" if res.output.startswith("timeout") else "elaboration")
            self.log("defect", name=claim.name, reason=reason)

    def finish(self) -> RunStats:
        self.log("run_end", stats=self.stats.__dict__)
        self._journal.close()
        return self.stats
