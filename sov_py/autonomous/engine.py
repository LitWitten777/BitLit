"""
Autonomous Reasoning Engine (Core Lifecycle & Scheduler).
Coordinates:
1. Hypothesis formulation & dynamic probe generation.
2. Dual truth verification (Z3 SMT + exact integer arithmetic).
3. Continuous topological manifold representation learning (PyTorch + GUDHI).
4. Durable SQLite checkpointing and audit logging.
"""

from __future__ import annotations

import asyncio
import json
import time
import traceback
from typing import Any

from pathlib import Path
import numpy as np

from .arxiv_crawler import ArxivResearchCrawler
from .epistemic_sentry import EpistemicSentry
from .hypothesis_generator import CandidateHypothesis, HypothesisGenerator
from .orchestration import (
    CrossDomainHarmonizer,
    StrategicEpistemicDirector,
    VerificationDispatcher,
)
from .persistence import HypothesisRecord, ReasoningStore
from .prover_loop import SovereignAutonomousProver
from .self_patch_sandbox import SelfPatchSandboxEngine
from .topological_learner import ContinuousTopologicalLearner
from .type_bridge import UniversalTypeBridge
from .verifier import DualTruthVerifier
from ..ipc.shm_ring_buffer import SovereignPacket, SovereignRingBuffer


class AutonomousReasoningEngine:
    """Production-grade asynchronous reasoning daemon with state persistence."""

    def __init__(
        self,
        db_path: str = "data/reasoning_store.db",
        tick_interval_sec: float = 1.0,
        enable_local_llm: bool = False,
        cognitive_bridge: Any | None = None,
        quantum_engine: Any | None = None,
        workspace_root: Path | str | None = None,
        enable_arxiv_crawler: bool = False,
        crawl_cadence_ticks: int = 50,
    ):
        self.db_path = db_path
        self.tick_interval_sec = tick_interval_sec
        self.workspace_root = Path(workspace_root or "/home/roku/Jubilant_Computing_Machine")
        self.enable_arxiv_crawler = enable_arxiv_crawler
        self.crawl_cadence_ticks = crawl_cadence_ticks
        self.store = ReasoningStore(db_path)

        # Autonomous closed-loop subsystems
        self.crawler = ArxivResearchCrawler(store=self.store)
        self.patch_sandbox = SelfPatchSandboxEngine(workspace_root=self.workspace_root)
        self.prover = SovereignAutonomousProver(workspace_root=self.workspace_root)

        # Geometric Epistemic Steering & Multi-Tiered Orchestrator Hierarchy
        self.director = StrategicEpistemicDirector(store=self.store)
        self.harmonizer = CrossDomainHarmonizer()
        self.dispatcher = VerificationDispatcher()
        self.type_bridge = UniversalTypeBridge()

        if enable_local_llm and cognitive_bridge is None:
            from .local_llm import LocalCognitiveBridge

            self.cognitive_bridge = LocalCognitiveBridge()
        else:
            self.cognitive_bridge = cognitive_bridge

        if quantum_engine is None:
            try:
                from ..integrations.esp32_quantum_entropy import FanoQuantumStabilizerEngine
                self.quantum_engine = FanoQuantumStabilizerEngine()
            except Exception:
                self.quantum_engine = None
        else:
            self.quantum_engine = quantum_engine

        self.generator = HypothesisGenerator(
            cognitive_bridge=self.cognitive_bridge,
            quantum_engine=self.quantum_engine,
            store=self.store,
        )
        self.verifier = DualTruthVerifier(self.store)
        self.learner = ContinuousTopologicalLearner(self.store)
        from ..runtime.geometric_runtime import GeometricCognitiveRuntime
        self.gnl = GeometricCognitiveRuntime()

        self.is_running = False
        self.is_paused = False
        self.ticks_executed = 0
        self.start_time = 0.0
        self._task: asyncio.Task[Any] | None = None
        self.tower_system = None

        try:
            shm_path = Path("/dev/shm/sov_state_ring")
            self.shm_ring = SovereignRingBuffer(capacity=1024, backing_file=shm_path)
        except Exception:
            self.shm_ring = SovereignRingBuffer(capacity=1024)

        self._initialize_canonical_knowledge()

    def _initialize_canonical_knowledge(self) -> None:
        """Seeds initial mathematical conjectures into the durable store if not already present."""
        existing = {h.id for h in self.store.list_hypotheses()}
        initial_hyps = (
            self.generator.generate_algebraic_conjectures([2, 4, 8, 16])
            + self.generator.generate_graph_conjectures([16], [1, 2, 3])
            + self.generator.generate_code_conjectures([1, 2])
            + self.generator.generate_scaling_law_conjectures()
            + self.generator.generate_smt_probes()
            + self.generator.generate_lean4_probes()
        )
        initial_hyps = self.generator.canonicalizer.prune_isomorphic_candidates(initial_hyps)
        for hyp in initial_hyps:
            if hyp.id not in existing:
                details = {
                    "conjecture_type": hyp.conjecture_type,
                    "predicate": hyp.predicate,
                    **hyp.parameters,
                }
                rec = HypothesisRecord(
                    id=hyp.id,
                    statement=hyp.statement,
                    category=hyp.category,
                    status="OPEN",
                    details=details,
                    created_at=time.time(),
                    updated_at=time.time(),
                )
                self.store.save_hypothesis(rec)

    def tick(self) -> dict[str, Any]:
        """Executes a single discrete reasoning cycle."""
        self.ticks_executed += 1
        cycle_start = time.time()
        actions_taken = []

        # 1. Check for open hypotheses in store
        open_hyps = self.store.list_hypotheses(status="OPEN")
        target_hyp: CandidateHypothesis | None = None

        if open_hyps:
            # Batch convert candidates for strategic epistemic prioritization
            candidates = []
            for rec in open_hyps[:15]:
                details = rec.details or {}
                c_type = details.get("conjecture_type", "ALGEBRAIC_IDENTITY")
                pred = details.get("predicate", "associativity")
                params = {k: v for k, v in details.items() if k not in ["conjecture_type", "predicate"]}
                candidates.append(
                    CandidateHypothesis(
                        id=rec.id,
                        statement=rec.statement,
                        category=rec.category,
                        conjecture_type=c_type,
                        predicate=pred,
                        parameters=params,
                    )
                )

            # Strategic Epistemic Director selects the maximal-entropy / void target
            prioritized = self.director.prioritize_candidates(candidates, top_k=1)
            target_hyp = prioritized[0].hypothesis if prioritized else candidates[0]
            if prioritized:
                top_tgt = prioritized[0]
                actions_taken.append(
                    f"Strategic Director steered: {target_hyp.id} [Φ={top_tgt.score:.2f}, S_bloch={top_tgt.entropy_bits:.2f}b, d_void={top_tgt.void_distance:.2f}]"
                )
            else:
                actions_taken.append(f"Verifying open hypothesis: {target_hyp.id} [{target_hyp.conjecture_type}::{target_hyp.predicate}]")
        else:
            # Generate next dynamic probe
            target_hyp = self.generator.generate_next_hypothesis()
            details = {
                "conjecture_type": target_hyp.conjecture_type,
                "predicate": target_hyp.predicate,
                **target_hyp.parameters,
            }
            # Register it in store and director
            self.store.save_hypothesis(
                HypothesisRecord(
                    id=target_hyp.id,
                    statement=target_hyp.statement,
                    category=target_hyp.category,
                    status="OPEN",
                    details=details,
                    created_at=time.time(),
                    updated_at=time.time(),
                )
            )
            self.director.register_hypothesis(target_hyp, status="OPEN")
            actions_taken.append(
                f"Generated & verifying dynamic probe: {target_hyp.id} [{target_hyp.conjecture_type}::{target_hyp.predicate}]"
            )

        # Tactical Dispatch recommendation
        dispatch_dec = self.dispatcher.route_hypothesis(target_hyp)
        actions_taken.append(f"Dispatcher recommendation: {dispatch_dec.target_engine.value} ({dispatch_dec.rationale})")

        # 2. Execute verification
        verif_res = self.verifier.verify_hypothesis(target_hyp)
        self.director.record_verification_result(target_hyp.id, verif_res.status)
        actions_taken.append(
            f"Hypothesis {target_hyp.id} -> {verif_res.status} ({verif_res.duration_ms:.1f}ms via {verif_res.engine})"
        )
        if self.generator.last_quantum_collapse is not None:
            q = self.generator.last_quantum_collapse
            actions_taken.append(
                f"Fano quantum collapse: sector={q.collapse_sector} (syndrome={q.syndrome_int}, ΔS={q.entropy_delta:.3f}b, src={q.source_info.get('source', 'UNKNOWN')})"
            )

        # Record teleological feedback for cognitive bridge & update database
        if verif_res.status in ("FALSIFIED", "REFUTED"):
            summary_str = (
                json.dumps(verif_res.counterexample)
                if isinstance(verif_res.counterexample, (dict, list))
                else (str(verif_res.counterexample) if verif_res.counterexample is not None else None)
            )
            self.store.update_hypothesis_status(
                target_hyp.id,
                status="FALSIFIED",
                proof_summary=summary_str,
            )
            err_detail = verif_res.counterexample or f"{target_hyp.predicate} failed on {target_hyp.parameters}"
            self.generator.record_negative_feedback(f"Falsified {target_hyp.id} [{target_hyp.predicate}]: {err_detail}")
        elif verif_res.status == "PROVED":
            self.store.update_hypothesis_status(
                target_hyp.id,
                status="CONFIRMED",
                proof_summary=verif_res.logs[:200] if verif_res.logs else None,
            )
            self.generator.record_confirmed_invariant(f"Proved {target_hyp.id}: {target_hyp.statement}")
            try:
                from .audit_exporter import export_audit_bundle
                export_audit_bundle(db_path=self.store.db_path)
            except Exception:
                pass
            try:
                from ..integrations.obsidian_sync import ObsidianVaultSync
                v_sync = ObsidianVaultSync()
                v_sync.sync_theorems(db_path=self.store.db_path)
                if self.generator.last_quantum_collapse is not None:
                    v_sync.sync_quantum_telemetry([self.generator.last_quantum_collapse])
            except Exception:
                pass


        # 3. Step topological representation learning
        topo_cp = self.learner.step(epochs=2)
        actions_taken.append(
            f"Topological learner epoch {topo_cp.epoch}: acc={topo_cp.accuracy * 100:.1f}%, H1_max_pers={topo_cp.max_persistence:.3f}"
        )

        # NEW: Extract algebraic constraints and feed to hypothesis generator
        constraints = self.learner.get_algebraic_constraints()
        self.generator.update_manifold_constraints(constraints)
        
        # Log high-confidence constraints
        high_conf = [c for c in constraints if c.get('confidence', 0) > 0.9]
        if high_conf:
            actions_taken.append(f"Extracted {len(high_conf)} high-confidence algebraic constraints")
            for constraint in high_conf[:3]:  # Log top 3
                if constraint['type'] == 'ANNIHILATION_CONSTRAINT':
                    actions_taken.append(
                        f"  - Annihilation pair (nodes {constraint['node_indices']}, "
                        f"distance {constraint['latent_distance']:.4f}, confidence {constraint['confidence']:.2f})"
                    )
                elif constraint['type'] == 'SECTOR_ORTHOGONALITY':
                    actions_taken.append(
                        f"  - Sector orthogonality χ{constraint['sectors']} "
                        f"(dot product {constraint['dot_product']:.4f})"
                    )

        # 4. GUDHI persistent Shannon entropy feedback steering conjecture generation
        self.generator.update_topological_feedback(
            entropy=topo_cp.persistent_entropy,
            max_persistence=topo_cp.max_persistence,
            betti_0=topo_cp.betti_0,
            betti_1=topo_cp.betti_1,
        )
        actions_taken.append(
            f"Topological feedback steered: S_top={topo_cp.persistent_entropy:.4f} bits, mode={self.generator.manifold_stability_mode}"
        )
        
        # PHASE 1 IMPROVEMENT: Wire topological constraints to LLM automatically
        # Build topological constraints dict for cognitive bridge
        topological_constraints = {
            'proven_invariants': list(self.generator.proven_invariants)[:20],  # Limit to top 20
            'betti_constraints': {
                'betti_0': topo_cp.betti_0,
                'betti_1': topo_cp.betti_1,
            },
            'forbidden_proposals': [],  # Will be populated from negative feedback
        }
        
        # Add high-confidence annihilation constraints as proven invariants
        for constraint in high_conf[:10]:
            if constraint['type'] == 'ANNIHILATION_CONSTRAINT':
                basis = constraint.get('basis_indices', ())
                if basis and len(basis) >= 2:
                    topological_constraints['proven_invariants'].append(
                        f'annihilation_pair_{basis[0]}_{basis[1]}'
                    )
        
        # Build forbidden proposals from negative feedback
        for fb in self.generator.negative_feedback_history[-5:]:
            if 'falsified' in fb.lower():
                # Extract predicate from feedback
                topological_constraints['forbidden_proposals'].append(fb)
        
        # Pass constraints to cognitive bridge for next generation cycle
        if self.cognitive_bridge and hasattr(self.cognitive_bridge, 'set_topological_constraints'):
            self.cognitive_bridge.set_topological_constraints(topological_constraints)

        # 5. GNL Topological Routing & Cohomology Certification
        gnl_summary = {}
        try:
            gnl_frames = self.gnl.ingest(target_hyp.statement)
            if gnl_frames:
                sample_frames = gnl_frames[:min(len(gnl_frames), 6)]
                gnl_traj = self.gnl.run_trajectory(sample_frames)
                gnl_summary = {
                    "vocab_size": len(self.gnl.lexer.frames),
                    "encoded_frames": len(gnl_frames),
                    "is_certified": bool(gnl_traj.is_certified),
                    "h1_norm": float(gnl_traj.cohomology_report.h1_norm),
                    "negentropy": float(gnl_traj.final_negentropy),
                    "active_register_density": sum(1 for x in self.gnl.state_register if x > 0),
                }
                actions_taken.append(
                    f"GNL certified: H1_norm={gnl_summary['h1_norm']:.4e}, negentropy={gnl_summary['negentropy']:.3f}, frames={len(gnl_frames)}"
                )
        except Exception as e:
            gnl_summary = {"error": str(e)}

        # 6. Autonomous Research Harvesting (arXiv preprint ingestion)
        if self.enable_arxiv_crawler and (self.ticks_executed % self.crawl_cadence_ticks == 0):
            try:
                num_crawled = self.crawler.crawl_and_ingest(max_results=3)
                if num_crawled > 0:
                    actions_taken.append(
                        f"Autonomous arXiv crawl: ingested {num_crawled} preprint candidate theorems"
                    )
            except Exception as e:
                actions_taken.append(f"Autonomous arXiv crawl deferred: {e}")

        elapsed_ms = (time.time() - cycle_start) * 1000.0

        tick_summary = {
            "tick": self.ticks_executed,
            "duration_ms": elapsed_ms,
            "actions": actions_taken,
            "hypothesis": {
                "id": target_hyp.id,
                "statement": target_hyp.statement,
                "category": target_hyp.category,
                "conjecture_type": target_hyp.conjecture_type,
                "predicate": target_hyp.predicate,
                "parameters": target_hyp.parameters,
            },
            "verification": {
                "hypothesis_id": verif_res.hypothesis_id,
                "status": verif_res.status,
                "engine": verif_res.engine,
                "duration_ms": verif_res.duration_ms,
                "proof_summary": verif_res.logs[:120],
            },
            "topology": {
                "epoch": topo_cp.epoch,
                "sector": topo_cp.sector,   # charge sector χ stepped this tick
                "accuracy": topo_cp.accuracy,
                "max_persistence": topo_cp.max_persistence,
                "entropy": topo_cp.persistent_entropy,
                "betti_0": topo_cp.betti_0,
                "betti_1": topo_cp.betti_1,
                "stability_mode": self.generator.manifold_stability_mode,
            },
            "gnl": gnl_summary,
        }

        # Emit 58-byte binary packet to shared memory ring buffer
        if hasattr(self, "shm_ring") and self.shm_ring:
            try:
                state_vec = np.zeros(16, dtype=np.float32)
                packet = SovereignPacket(
                    seq=self.ticks_executed,
                    state_16=state_vec,
                    lamb_norm=float(verif_res.duration_ms),
                    s_diagram=float(topo_cp.persistent_entropy if topo_cp else 0.0),
                    zd_mask=1 if verif_res.status == "PROVED" else 0,
                    flags=0x01 if verif_res.status == "PROVED" else (0x02 if verif_res.status in ("FALSIFIED", "REFUTED") else 0x00),
                )
                self.shm_ring.push(packet)
            except Exception:
                pass

        self.store.log_system_event(
            "INFO", "Engine", f"Tick {self.ticks_executed} completed", tick_summary
        )
        return tick_summary

    async def _run_loop(self) -> None:
        """Internal asynchronous daemon loop."""
        self.is_running = True
        self.start_time = time.time()
        self.store.log_system_event("INFO", "Engine", "Autonomous Reasoning Daemon started")

        try:
            while self.is_running:
                if not self.is_paused:
                    try:
                        self.tick()
                    except Exception as e:
                        self.store.log_system_event(
                            "ERROR", "Engine", f"Tick error: {e}", {"trace": traceback.format_exc()}
                        )
                await asyncio.sleep(self.tick_interval_sec)
        except asyncio.CancelledError:
            pass
        finally:
            self.is_running = False
            self.store.log_system_event("INFO", "Engine", "Autonomous Reasoning Daemon stopped")

    def start_background(self) -> None:
        """Starts the reasoning daemon as a non-blocking background task."""
        if not self.is_running:
            loop = asyncio.get_event_loop()
            self._task = loop.create_task(self._run_loop())

    def stop(self) -> None:
        """Gracefully stops the reasoning daemon."""
        self.is_running = False
        if self._task and not self._task.done():
            self._task.cancel()
        if self.cognitive_bridge is not None:
            if hasattr(self.cognitive_bridge, "stop"):
                self.cognitive_bridge.stop()
            elif hasattr(self.cognitive_bridge, "close"):
                self.cognitive_bridge.close()


    def run_forever(self, print_progress: bool = True) -> None:
        """Synchronously runs the reasoning daemon in a blocking loop until interrupted."""
        self.is_running = True
        self.start_time = time.time()
        self.store.log_system_event("INFO", "Engine", "Autonomous Reasoning Daemon started (run_forever)")
        try:
            while self.is_running:
                if not self.is_paused:
                    try:
                        res = self.tick()
                        if print_progress:
                            verif = res.get("verification", {})
                            topo = res.get("topology", {})
                            print(
                                f"[Tick {res['tick']:03d} | {res['duration_ms']:.1f}ms] "
                                f"Hyp: {verif.get('hypothesis_id', 'N/A')} => {verif.get('status', 'N/A')} "
                                f"({verif.get('engine', 'N/A')}) | "
                                f"Topology: Ep {topo.get('epoch', 0)} Acc {topo.get('accuracy', 0)*100:.1f}% "
                                f"S_top {topo.get('entropy', 0):.3f} bits"
                            )
                    except Exception as e:
                        self.store.log_system_event(
                            "ERROR", "Engine", f"Tick error: {e}", {"trace": traceback.format_exc()}
                        )
                time.sleep(self.tick_interval_sec)
        except KeyboardInterrupt:
            self.stop()
        finally:
            self.is_running = False
            self.store.log_system_event("INFO", "Engine", "Autonomous Reasoning Daemon stopped")


    def get_status(self) -> dict[str, Any]:
        """Returns comprehensive real-time engine telemetry."""
        uptime = time.time() - self.start_time if self.is_running else 0.0
        stats = self.store.get_summary_stats()
        manifold = self.learner.get_manifold_state()

        return {
            "is_running": self.is_running,
            "is_paused": self.is_paused,
            "uptime_seconds": uptime,
            "ticks_executed": self.ticks_executed,
            "stats": stats,
            "manifold": {
                "epoch": manifold["epoch"],
                "betti_0": manifold["betti_0"],
                "betti_1": manifold["betti_1"],
                "h1_stats": manifold["h1_stats"],
            },
        }

    def evaluate_tower_organism(
        self,
        prop_id: str,
        linguistic_phrase: str = "",
        vector_params: Any | None = None,
        operator: str = "==",
        dimension: int = 16,
        functor_epochs: int = 120,
        enable_topological_learner: bool = False,
    ) -> Any:
        """Evaluates a proposition across the 5-pillar Tower Organism System."""
        if self.tower_system is None:
            from .tower_organism_system import TowerOrganismSystem
            self.tower_system = TowerOrganismSystem(topological_learner=self.learner)
        return self.tower_system.process_unified_proposition(
            prop_id=prop_id,
            linguistic_phrase=linguistic_phrase,
            vector_params=vector_params,
            operator=operator,
            dimension=dimension,
            functor_epochs=functor_epochs,
            verify_lean=False,
            enable_topological_learner=enable_topological_learner,
        )

    def crawl_recent_research(
        self,
        query: str | None = None,
        categories: list[str] | None = None,
        max_results: int = 5,
    ) -> int:
        """Explicitly triggers arXiv research crawling and ingests candidate conjectures into store."""
        return self.crawler.crawl_and_ingest(query=query, categories=categories, max_results=max_results)

    def apply_self_patch(
        self,
        files_patch: dict[str, str],
        test_commands: list[list[str]] | None = None,
    ) -> Any:
        """Atomically tests and applies code evolution through Epistemic Sentry and isolated rollback sandbox."""
        receipt = self.patch_sandbox.apply_patch(files_patch=files_patch, test_commands=test_commands)
        self.store.log_system_event(
            "INFO" if receipt.success else "WARNING",
            "AutonomousReasoningEngine",
            f"Self-patch execution: success={receipt.success}, rolled_back={receipt.rolled_back}",
            {
                "modified": receipt.modified_files,
                "sentry_passed": receipt.sentry_passed,
                "tests_passed": receipt.tests_passed,
                "diagnostics": receipt.diagnostics[:300],
            },
        )
        return receipt

    def run_formal_prover_cycle(
        self,
        candidate_name: str,
        solver_setup_fn: Any,
        eval_fn: Any,
        lean_generator: Any,
    ) -> Any:
        """Executes the complete SovereignAutonomousProver loop (Inhale -> Exhale -> Pause -> Escalate)."""
        receipt = self.prover.run_proof_loop(
            candidate_name=candidate_name,
            solver_setup_fn=solver_setup_fn,
            eval_fn=eval_fn,
            lean_generator=lean_generator,
        )
        self.store.log_system_event(
            "INFO" if receipt.status.name in ("CERTIFIED", "CERTIFIED_ARISTOTLE") else "WARNING",
            "AutonomousReasoningEngine",
            f"Prover cycle completed for {candidate_name}: {receipt.status.name}",
            {
                "status": receipt.status.name,
                "total_time_ms": receipt.total_time_ms,
                "escalate_attempted": receipt.escalate.attempted if receipt.escalate else False,
            },
        )
        return receipt

    def find_epistemic_voids(self, grid_res: int = 12) -> list[Any]:
        """Returns candidate epistemic gap voids on the Poincaré disk."""
        return self.director.manifold.find_hyperbolic_voids(grid_res=grid_res)

    def find_cross_domain_analogies(self, domain: str) -> list[Any]:
        """Discovers cross-domain functorial analogies involving the given domain."""
        return self.harmonizer.find_analogies(domain)

    def lookup_type_mapping(self, concept_name: str) -> Any:
        """Looks up cross-language type mappings across Python, Z3, and Lean 4."""
        return self.type_bridge.get_mapping(concept_name)


