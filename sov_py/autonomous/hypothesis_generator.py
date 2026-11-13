"""
Generative Hypothesis Formulation Engine for Autonomous Mathematical Reasoning.
Constructs open-ended mathematical conjectures dynamically across:
1. Cayley-Dickson Tower Algebraic Identities (Associativity, Alternativity, Flexibility, Centralizers).
2. Annihilation Graph Topologies (Bipartiteness, Regularity, Ramanujan Bounds, Spectra).
3. Error-Correcting & Quantum Codes (Doubly-Even Weights, Self-Orthogonality, CSS Commutativity).
4. Scaling Laws & SMT Constraints (Dimension Towers, Projective Duality, Odd-Cycle Refutations).

Zero hardcoded script lists: Everything is generated from formal mathematical predicates.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from ..polytope.conjecture_canonicalizer import ConjectureCanonicalizer


@dataclass
class CandidateHypothesis:
    """Formal mathematical conjecture specification."""

    id: str
    statement: str
    category: str
    conjecture_type: str  # "ALGEBRAIC_IDENTITY", "GRAPH_INVARIANT", "CODE_INVARIANT", "SCALING_LAW", "SMT_CONSTRAINT", "LEAN4_THEOREM", "TOWER_ORGANISM"
    predicate: (
        str  # Specific predicate to test, e.g. "associativity", "bipartite", "css_commutativity"
    )
    parameters: dict[str, Any] = field(default_factory=dict)
    expected_relation: dict[str, Any] = field(default_factory=lambda: {"op": "==", "val": True})
    generality: str = "FINITE_EVALUATION"  # "FINITE_EVALUATION" vs "UNIVERSAL_THEOREM" (Aristotle review Point 6)


def make_content_addressed_id(
    conjecture_type: str,
    predicate: str,
    parameters: dict[str, Any],
    prefix: str = "HYP",
) -> str:
    """
    Computes a deterministic content-addressed identifier for a hypothesis
    (Aristotle review Point 7: Deduplicate and make hypotheses content-addressed).
    Keying on normalized statement/parameters prevents the database from inflating.
    """
    import hashlib
    sorted_items = []
    for k, v in sorted(parameters.items()):
        if isinstance(v, (list, tuple)):
            sorted_items.append((k, tuple(v)))
        elif isinstance(v, dict):
            sorted_items.append((k, tuple(sorted(v.items()))))
        else:
            sorted_items.append((k, str(v)))
    payload = f"{conjecture_type}:{predicate}:{sorted_items}"
    digest = hashlib.sha256(payload.encode("utf-8")).hexdigest()[:10].upper()
    return f"{prefix}-{digest}"


class ReificationTrapDetector:
    """
    Epistemic Hygiene & Anti-Reification Filter (Ziporyn / univ.md).

    Detects and rejects:
    1. Tautological inequalities (e.g. asserting bounds like 'w > 8' provable by trivial arithmetic without algebraic content).
    2. Coordinate artifact reification: treating raw coordinate indices or intermediate unphysical
       gauge fields as independent physical invariants without gauge invariance.
    3. Vacuous coboundary filters (e.g., non-discriminative tautologies like delta* omega = +1).
    """

    TAUTOLOGY_PATTERNS = (
        "w > 8",
        "delta* omega = +1",
        "coboundary_filter_tautology",
        "trivial_bound",
    )

    GAUGE_COORDINATE_REIFICATION_TERMS = (
        "raw_coordinate_invariant",
        "unphysical_gauge_observable",
        "isolated_gauge_component",
    )

    @classmethod
    def audit_hypothesis(cls, hyp: CandidateHypothesis) -> tuple[bool, str]:
        """
        Returns (is_clean, reason). If is_clean is False, hypothesis is a reification trap.
        """
        stmt = hyp.statement.lower()
        pred = hyp.predicate.lower()

        # Check tautology patterns
        for pat in cls.TAUTOLOGY_PATTERNS:
            if pat in stmt or pat in pred:
                return False, f"Reification trap: detected tautological / non-discriminative predicate '{pat}'"

        # Check coordinate reification
        for term in cls.GAUGE_COORDINATE_REIFICATION_TERMS:
            if term in stmt or term in pred:
                return False, f"Reification trap: treating intermediate gauge artifact '{term}' as independent observable"

        # Check explicit tautological parameters
        if hyp.parameters.get("tautological", False):
            return False, "Reification trap: explicitly marked tautological"

        # Parameter coordinate reification check
        if hyp.parameters.get("coordinate_dependent", False) and not hyp.parameters.get("gauge_invariant", False):
            return False, "Reification trap: coordinate-dependent without gauge invariance"

        return True, "Passed epistemic hygiene audit"


# Predicate families that a single universally quantified theorem already settles.
# Once such a family has been emitted once, further numeric instances of it carry no new
# information: the certificate for the family covers every parameter tuple at once.  The
# generator therefore records the family theorem and moves on to unexplored predicates
# instead of enumerating parameters (the audit of the reasoning store found 48 consecutive
# entries that were instances of a single family).
SETTLED_FAMILIES: dict[str, str] = {
    "associator_coset_shift": "Sovereign.assocNeg_shift_span",
}


class HypothesisGenerator:
    """Dynamic, open-ended generator of mathematical conjectures."""

    def __init__(
        self,
        cognitive_bridge: Any | None = None,
        quantum_engine: Any | None = None,
        store: Any | None = None,
        lean_bridge: Any | None = None,
    ) -> None:
        self._seq = 0
        # Predicate families settled by a universal theorem, and the ones already emitted.
        self.settled_families: dict[str, str] = dict(SETTLED_FAMILIES)
        self._families_emitted: set[str] = set()
        self.cognitive_bridge = cognitive_bridge
        self.quantum_engine = quantum_engine
        # Optional reference to the ReasoningStore, used for deduplication.
        self.store = store
        # Bidirectional Lean bridge for importing proven theorems
        self.lean_bridge = lean_bridge
        # In-memory deduplication cache: (conjecture_type, predicate, dimension, sector) tuples.
        # Populated lazily from the store on first call, then kept in sync.
        self._seen_keys: set[tuple[Any, ...]] | None = None
        # Weyl chamber & AST duality canonicalizer
        self.canonicalizer = ConjectureCanonicalizer()
        # Proven invariants loaded from Lean proofs for semantic guidance
        self.proven_invariants: set[str] = set()
        # Spectral database caching eigenvalue data across dimensions
        self.spectral_database: dict[int, dict] = {}
        # Manifold constraints from topological learner
        self.manifold_constraints: list = []
        self.last_quantum_collapse: Any | None = None
        self.negative_feedback_history: list[str] = []
        self.confirmed_invariants_history: list[str] = []
        # Dimensions to probe; 64 and 128 use the analytical verification path
        # (D > 64 guard in verifier) so they do not trigger graph construction.
        self._dimensions = [2, 4, 8, 16, 32, 64, 128]
        self._identities = [
            "associativity",
            "alternating_associator",
            "flexibility",
            "anticommutativity_imaginary",
            "power_associativity",
            "jordan_identity",
        ]
        self._graph_properties = ["bipartite", "regular", "ramanujan_bound", "cardinality_formula"]
        self._code_properties = ["doubly_even", "self_orthogonal", "css_commutativity"]
        # Number of distinct charge sectors per dimension: D has D/2 - 1 sectors.
        # (For D=16: 7, D=32: 15, D=64: 31, D=128: 63)
        self._max_sector: dict[int, int] = {
            16: 7,
            32: 15,
            64: 31,
            128: 63,
        }
        self._conjecture_types = [
            "FRAME_FIELD_INVARIANT",
            "PROJECTIVE_PENCIL_FIBRATION",
            "STIEFEL_INVARIANT",
            "QUANTUM_ERROR_CORRECTION",
            "ALGEBRAIC_IDENTITY",
            "GRAPH_INVARIANT",
            "CODE_INVARIANT",
            "SCALING_LAW",
            "SMT_CONSTRAINT",
            "LEAN4_THEOREM",
            "TOWER_ORGANISM",
            "MODULAR_HECKE",
        ]
        self._organism_properties = [
            "tower_organism_soundness",
            "sofit_boundary_closure",
            "stella_octangula_parity",
            "mog_tetrad_basin",
            "persistent_entropy_barrier",
        ]
        self.topological_entropy: float = 0.8096
        self.max_persistence: float = 2.1701
        self.betti_0: int = 1
        self.betti_1: int = 1
        self.manifold_stability_mode: str = "MANIFOLD_STABLE"
        
        # Phase 2: Novelty detection and extensible grammar
        self._novelty_threshold: float = 0.3  # Minimum novelty score to propose
        self._hypothesis_embeddings: dict[str, list[float]] = {}  # Semantic embeddings for novelty
        self._extensible_predicates: dict[str, dict] = {}  # User-defined predicates
        self._priority_queue: list[tuple[float, CandidateHypothesis]] = []  # Priority queue for Lean proofs
        self._prime_scan_n: int = 2  # Arithmetic prime organism open frontier
        self._hebrew_synthesizer = None

    def register_semantic_synthesizer(self, synthesizer: Any) -> None:
        """Register a semantic synthesizer (e.g. HebrewWordSynthesizer) via dependency injection."""
        self._hebrew_synthesizer = synthesizer

    @property
    def hebrew_synthesizer(self):
        """Lazily retrieve semantic synthesizer if available."""
        if self._hebrew_synthesizer is None:
            try:
                import sys
                mod = sys.modules.get("src.sedenion.autonomous.meta_hebrew_synthesis")
                if mod is not None and hasattr(mod, "HebrewWordSynthesizer"):
                    self._hebrew_synthesizer = mod.HebrewWordSynthesizer()
                else:
                    from .meta_hebrew_synthesis import HebrewWordSynthesizer
                    self._hebrew_synthesizer = HebrewWordSynthesizer()
            except Exception:
                self._hebrew_synthesizer = None
        return self._hebrew_synthesizer

    @hebrew_synthesizer.setter
    def hebrew_synthesizer(self, value):
        self._hebrew_synthesizer = value

    def synthesize_hebrew_feedback(self, status: str, predicate: str, dim: int = 16) -> dict[str, Any]:
        """
        Synthesizes a quantized Hebrew word and complementary opposite for semantic steering.
        Gracefully returns fallback info if no synthesizer is available.
        """
        synth = self.hebrew_synthesizer
        if synth is None:
            return {
                "pair_info": {"status": status, "predicate": predicate, "dim": dim},
                "feedback_word": f"FEEDBACK_{status}_{predicate}",
                "constraints": {},
            }
        try:
            from .meta_hebrew_synthesis import SemanticSignature
            import math
            inv = float(self.max_persistence) if self.max_persistence > 0.0 else (1.0 / math.sqrt(2.0))
            sig = SemanticSignature(
                algebraic_type=predicate,
                dimension=dim,
                invariant_value=inv,
                topological_features={"betti_1": self.betti_1, "max_persistence": self.max_persistence},
                proof_status=status,
            )
            pair_info = synth.generate_with_opposite(sig)
            feedback_word = synth.synthesize_feedback_word(
                proof_status=status,
                algebraic_type=predicate,
                dimension=dim,
            )
            constraints = synth.word_to_constraints(feedback_word)
            return {
                "pair_info": pair_info,
                "feedback_word": str(feedback_word),
                "constraints": constraints,
            }
        except Exception:
            return {
                "pair_info": {"status": status, "predicate": predicate, "dim": dim},
                "feedback_word": f"FEEDBACK_{status}_{predicate}",
                "constraints": {},
            }

    def record_negative_feedback(self, feedback: str, predicate: str = "algebraic", dim: int = 16) -> None:
        """Records a falsified invariant or counterexample to steer subsequent generation."""
        self.negative_feedback_history.append(feedback)
        if len(self.negative_feedback_history) > 25:
            self.negative_feedback_history.pop(0)
        try:
            self.synthesize_hebrew_feedback("FALSIFIED", predicate, dim)
        except Exception:
            pass

    def record_confirmed_invariant(self, invariant: str, predicate: str = "algebraic", dim: int = 16) -> None:
        """Records a formally proved invariant to condition subsequent generation."""
        self.confirmed_invariants_history.append(invariant)
        self.proven_invariants.add(invariant)
        if len(self.confirmed_invariants_history) > 25:
            self.confirmed_invariants_history.pop(0)
        try:
            self.synthesize_hebrew_feedback("VERIFIED", predicate, dim)
        except Exception:
            pass

    def load_proven_theorems_from_lean(self) -> None:
        """Load proven theorems from Lean bridge to guide hypothesis generation."""
        if self.lean_bridge is None:
            return
        try:
            proven = getattr(self.lean_bridge, 'load_proven_theorems', None)
            if callable(proven):
                theorems = proven()
                for thm_name, thm_data in theorems.items():
                    if thm_data.get('status') == 'proved':
                        self.proven_invariants.add(thm_name)
                        self.confirmed_invariants_history.append(thm_name)
        except Exception:
            pass

    def update_spectral_database(self, dimension: int, spectra: dict) -> None:
        """Cache spectral data for a given dimension to guide future hypotheses."""
        self.spectral_database[dimension] = spectra

    def update_manifold_constraints(self, constraints: list) -> None:
        """Update manifold constraints from topological learner.
        
        These constraints (annihilation pairs, sector orthogonality) are used
        to guide hypothesis generation toward algebraically meaningful conjectures.
        """
        self.manifold_constraints = constraints
        
        # Boost scoring for hypotheses related to high-confidence constraints
        for constraint in constraints:
            if constraint.get('confidence', 0) > 0.7:
                if constraint['type'] == 'ANNIHILATION_CONSTRAINT':
                    # Add proven invariant for this annihilation pattern
                    basis = constraint.get('basis_indices', ())
                    if basis and basis[0] >= 0 and basis[1] >= 0:
                        self.proven_invariants.add(f'annihilation_pair_{basis[0]}_{basis[1]}')
                elif constraint['type'] == 'SECTOR_ORTHOGONALITY':
                    sectors = constraint.get('sectors', ())
                    if sectors:
                        self.proven_invariants.add(f'sector_orthogonality_{sectors[0]}_{sectors[1]}')

    def _score_by_structural_proximity(self, c_type: str, predicate: str, params: dict[str, Any]) -> float:
        """
        Score a hypothesis by its proximity to proven invariants and existing data.
        Higher scores indicate more promising conjectures.
        Returns a score between 0.0 and 1.0.
        
        Note: Does NOT filter out already-proven hypotheses - that's done by caller.
        This ensures diversity in returned candidates.
        """
        score = 0.5  # Base score
        
        # Check if related invariants are proven (boost score for extending proven work)
        for inv in self.proven_invariants:
            if predicate in inv or inv in predicate:
                score += 0.15  # Related to proven theorem
                break  # Only count once
        
        # Leverage existing spectral data
        dim = params.get('dimension')
        if dim and dim in self.spectral_database:
            score += 0.2  # Has spectral data available
        
        # Penalize unstable manifolds slightly (but don't filter out completely)
        if self.manifold_stability_mode == "MANIFOLD_COLLAPSE_RISK":
            score *= 0.85  # Slight penalty for risky manifolds
        elif self.manifold_stability_mode == "MANIFOLD_STABLE":
            score *= 1.1  # Slight boost for stable manifolds
        
        return min(score, 1.0)

    def update_topological_feedback(
        self,
        entropy: float,
        max_persistence: float,
        betti_0: int = 1,
        betti_1: int = 1,
    ) -> None:
        """
        Updates generator feedback metrics from GUDHI persistent homology analysis.
        Steers subsequent conjecture formulation toward stable manifold invariants.
        """
        self.topological_entropy = float(entropy)
        self.max_persistence = float(max_persistence)
        self.betti_0 = int(betti_0)
        self.betti_1 = int(betti_1)

        if self.topological_entropy >= 0.5 and self.max_persistence >= 0.4 and self.betti_1 >= 1:
            self.manifold_stability_mode = "MANIFOLD_STABLE"
        elif self.topological_entropy < 0.2 or self.max_persistence < 0.2:
            self.manifold_stability_mode = "MANIFOLD_COLLAPSE_RISK"
        else:
            self.manifold_stability_mode = "EXPLORATION"

    def register_extensible_predicate(self, name: str, definition: dict) -> None:
        """
        Phase 2: Register a user-defined extensible predicate for novel hypothesis generation.
        
        Args:
            name: Unique predicate name (e.g., "associator_cocycle")
            definition: Dictionary with keys:
                - 'description': Human-readable description
                - 'parameters': List of parameter names
                - 'validation_fn': Optional Python callable for validation
                - 'lean_template': Optional Lean 4 theorem template string
        
        Example:
            gen.register_extensible_predicate(
                "associator_cocycle",
                {
                    "description": "Associator satisfies 3-cocycle identity in cohomology",
                    "parameters": ["n", "i", "j", "k"],
                    "validation_fn": lambda n, i, j, k: verify_cocycle(n, i, j, k),
                    "lean_template": "theorem associator_cocycle (n : ℕ) (i j k : Fin (2^n)) : ..."
                }
            )
        """
        self._extensible_predicates[name] = definition
    
    def compute_novelty_score(self, hypothesis: CandidateHypothesis) -> float:
        """
        Phase 2: Compute novelty score for a hypothesis based on semantic distance
        from existing hypotheses in the embedding space.
        
        Uses hybrid approach:
        1. Exact match penalty (same type+predicate+params = 0 novelty)
        2. Parameter-space distance for variations of same predicate
        3. Cross-type novelty boost
        
        Returns:
            Float between 0.0 (redundant) and 1.0 (highly novel)
        """
        # Create key from hypothesis properties
        hyp_key = f"{hypothesis.conjecture_type}_{hypothesis.predicate}_{hypothesis.parameters}"
        
        # Check for exact duplicate first
        if hyp_key in self._hypothesis_embeddings:
            return 0.0  # Exact duplicate
        
        # Simple embedding: use hash to create pseudo-embedding vector
        import random
        rng = random.Random(hash(hyp_key))
        current_embedding = [rng.gauss(0, 1) for _ in range(10)]  # 10D embedding
        
        if not self._hypothesis_embeddings:
            # First hypothesis is maximally novel
            self._hypothesis_embeddings[hyp_key] = current_embedding
            return 1.0
        
        # Compute cosine similarity to all existing hypotheses
        max_similarity = 0.0
        for existing_key, existing_emb in self._hypothesis_embeddings.items():
            # Cosine similarity
            dot_product = sum(a * b for a, b in zip(current_embedding, existing_emb))
            norm_current = sum(x * x for x in current_embedding) ** 0.5
            norm_existing = sum(x * x for x in existing_emb) ** 0.5
            if norm_current > 0 and norm_existing > 0:
                similarity = dot_product / (norm_current * norm_existing)
                
                # Boost similarity for same predicate (penalize redundant conjectures)
                existing_parts = existing_key.split('_')
                if len(existing_parts) >= 2 and existing_parts[1] == hypothesis.predicate:
                    similarity = min(1.0, similarity + 0.3)  # Penalize same-predicate
                
                max_similarity = max(max_similarity, abs(similarity))
        
        # Store embedding
        self._hypothesis_embeddings[hyp_key] = current_embedding
        
        # Novelty = 1 - max_similarity
        novelty = 1.0 - max_similarity
        return max(0.0, min(1.0, novelty))
    
    def add_to_priority_queue(self, hypothesis: CandidateHypothesis, priority: float) -> None:
        """
        Phase 2: Add hypothesis to priority queue for formal Lean proof attempts.
        
        Args:
            hypothesis: The candidate hypothesis
            priority: Priority score (higher = more important to prove)
        
        Queue is maintained as a max-heap sorted by priority.
        """
        import heapq
        # Negate priority for max-heap behavior (heapq is min-heap)
        heapq.heappush(self._priority_queue, (-priority, hypothesis))
    
    def get_next_priority_hypothesis(self) -> CandidateHypothesis | None:
        """
        Phase 2: Get highest-priority hypothesis from queue for Lean proof attempt.
        
        Returns:
            Highest-priority hypothesis, or None if queue is empty
        """
        import heapq
        if not self._priority_queue:
            return None
        _, hypothesis = heapq.heappop(self._priority_queue)
        return hypothesis
    
    def clear_priority_queue(self) -> None:
        """Phase 2: Clear the priority queue."""
        self._priority_queue = []
    
    def get_priority_queue_size(self) -> int:
        """Phase 2: Get number of hypotheses waiting for formal proof."""
        return len(self._priority_queue)

    def _next_id(self, prefix: str = "GEN") -> str:
        self._seq += 1
        return f"{prefix}-{self._seq:05d}"

    def _make_key(self, c_type: str, predicate: str, params: dict[str, Any]) -> tuple[Any, ...]:
        clean_params = {
            k: v
            for k, v in params.items()
            if k not in ("quantum_sector", "quantum_syndrome", "quantum_entropy_delta", "physical_entropy")
        }
        return self.canonicalizer.get_canonical_signature(c_type, predicate, clean_params)

    def _load_seen_keys(self) -> set[tuple[Any, ...]]:
        """Loads existing canonical hypothesis signatures from the store."""
        if self.store is None:
            return set()
        keys: set[tuple[Any, ...]] = set()
        try:
            for rec in self.store.list_hypotheses():
                d = rec.details or {}
                c_type = d.get("conjecture_type", "")
                pred = d.get("predicate", "")
                if c_type and pred:
                    params = {k: v for k, v in d.items() if k not in ("conjecture_type", "predicate")}
                    keys.add(self._make_key(c_type, pred, params))
                    if pred in ("prime_ground_state", "e8_prime_excess"):
                        n_val = params.get("n")
                        if isinstance(n_val, int):
                            self._prime_scan_n = max(self._prime_scan_n, n_val + 1)
        except Exception:
            pass
        return keys

    def family_theorem(self, predicate: str) -> str | None:
        """The universal theorem that settles this predicate family, if there is one."""
        return self.settled_families.get(predicate)

    def is_family_exhausted(self, predicate: str) -> bool:
        """True once a family settled by a universal theorem has been emitted once.

        Further parameter tuples of such a family are instances of a statement that is
        already certified in full generality, so they are treated as duplicates.
        """
        return predicate in self.settled_families and predicate in self._families_emitted

    def note_family_emitted(self, predicate: str) -> None:
        """Records that a settled family has now been emitted once."""
        if predicate in self.settled_families:
            self._families_emitted.add(predicate)

    def _is_duplicate(self, c_type: str, predicate: str, params: dict[str, Any] | None = None) -> bool:
        """Returns True if this hypothesis has already been evaluated or queued.

        A predicate whose family is settled by a universal theorem counts as a duplicate
        after its first instance, whatever its parameters.
        """
        if self.is_family_exhausted(predicate):
            return True
        if self._seen_keys is None:
            self._seen_keys = self._load_seen_keys()
        key = self._make_key(c_type, predicate, params or {})
        return key in self._seen_keys

    def _mark_seen(self, c_type: str, predicate: str, params: dict[str, Any] | None = None) -> None:
        """Marks a hypothesis as seen in the cache, and its family as emitted."""
        if self._seen_keys is None:
            self._seen_keys = self._load_seen_keys()
        key = self._make_key(c_type, predicate, params or {})
        self._seen_keys.add(key)
        self.note_family_emitted(predicate)

    def generate_algebraic_conjectures(
        self, dimensions: list[int] | None = None
    ) -> list[CandidateHypothesis]:
        """Generates algebraic identity conjectures across dimensions."""
        dims = dimensions or self._dimensions
        conjectures = []
        for dim in dims:
            for ident in self._identities:
                h_id = self._next_id("ALG")
                stmt = f"In the {dim}-dimensional Cayley-Dickson algebra, the '{ident}' identity holds for all basis elements."
                conjectures.append(
                    CandidateHypothesis(
                        id=h_id,
                        statement=stmt,
                        category="AbstractAlgebra",
                        conjecture_type="ALGEBRAIC_IDENTITY",
                        predicate=ident,
                        parameters={"dimension": dim},
                        expected_relation={"op": "==", "val": True},
                    )
                )
        return conjectures

    def generate_graph_conjectures(
        self, dimensions: list[int] | None = None, sectors: list[int] | None = None
    ) -> list[CandidateHypothesis]:
        """Generates topological and spectral graph conjectures across sectors.

        When *sectors* is omitted, uses the full valid sector range for each
        dimension: D has D/2 − 1 charge sectors (e.g. D=32 → 15, D=64 → 31).
        """
        dims = dimensions or [16, 32]
        conjectures = []
        for dim in dims:
            max_sec = self._max_sector.get(dim, dim // 2 - 1) if sectors is None else None
            secs = sectors if sectors is not None else list(range(1, max_sec + 1))
            for sec in secs:
                for prop in self._graph_properties:
                    h_id = self._next_id("GRAPH")
                    stmt = f"Sector chi={sec} of the {dim}D zero-divisor annihilation graph satisfies '{prop}'."
                    conjectures.append(
                        CandidateHypothesis(
                            id=h_id,
                            statement=stmt,
                            category="SpectralGraphTheory",
                            conjecture_type="GRAPH_INVARIANT",
                            predicate=prop,
                            parameters={"dimension": dim, "sector": sec},
                            expected_relation={"op": "==", "val": True},
                        )
                    )
        return conjectures

    def generate_code_conjectures(
        self, sectors: list[int] | None = None
    ) -> list[CandidateHypothesis]:
        """Generates coding-theoretic and quantum CSS conjectures."""
        secs = sectors or list(range(1, 8))
        conjectures = []
        for sec in secs:
            for prop in self._code_properties:
                h_id = self._next_id("QEC")
                stmt = f"The binary linear and quantum CSS code derived from sector chi={sec} satisfies '{prop}'."
                conjectures.append(
                    CandidateHypothesis(
                        id=h_id,
                        statement=stmt,
                        category="QuantumCodingTheory",
                        conjecture_type="CODE_INVARIANT",
                        predicate=prop,
                        parameters={"dimension": 16, "sector": sec},
                        expected_relation={"op": "==", "val": True},
                    )
                )
        return conjectures

    def generate_frame_field_conjectures(
        self, dimensions: list[int] | None = None
    ) -> list[CandidateHypothesis]:
        """Generates conjectures for the Orthogonal Frame Field across the tower."""
        dims = dimensions or [16, 32, 64, 128]
        preds = [
            "coplanar_bipartite_split",
            "twin_dichromatic_ratio",
            "golay_octad_neighborhood",
            "octad_gram_spectrum",
        ]
        conjectures = []
        for dim in dims:
            for pred in preds:
                h_id = self._next_id("FRAME")
                stmt = f"The {dim}D Orthogonal Frame Field satisfies the '{pred}' invariant on V_2(R^{dim//2 - 1})."
                conjectures.append(
                    CandidateHypothesis(
                        id=h_id,
                        statement=stmt,
                        category="OrthogonalFrameField",
                        conjecture_type="FRAME_FIELD_INVARIANT",
                        predicate=pred,
                        parameters={"dimension": dim},
                        expected_relation={"op": "==", "val": True},
                    )
                )
        return conjectures

    def generate_projective_pencil_conjectures(
        self, dimensions: list[int] | None = None
    ) -> list[CandidateHypothesis]:
        """Generates conjectures for the Universal Projective Line-Pencil Fibration."""
        dims = dimensions or [16, 32, 64, 128]
        preds = [
            "pencil_cardinality",
            "sector_vertex_order_formula",
            "pencil_plane_partition",
            "projective_line_triality",
        ]
        conjectures = []
        for dim in dims:
            n_val = dim.bit_length() - 1
            for pred in preds:
                h_id = self._next_id("PENCIL")
                stmt = f"In dimension D={dim}, the Orthogonal Frame Field fibrates as a projective line pencil in PG({n_val-2}, F_2) under '{pred}'."
                conjectures.append(
                    CandidateHypothesis(
                        id=h_id,
                        statement=stmt,
                        category="ProjectiveGeometry",
                        conjecture_type="PROJECTIVE_PENCIL_FIBRATION",
                        predicate=pred,
                        parameters={"dimension": dim},
                        expected_relation={"op": "==", "val": True},
                    )
                )
        return conjectures

    def generate_tower_stiefel_conjectures(
        self, dimensions: list[int] | None = None
    ) -> list[CandidateHypothesis]:
        """Generates continuous Stiefel frame census and cubature conjectures."""
        dims = dimensions or [16, 32, 64, 128]
        preds = [
            "stiefel_frame_census",
            "stiefel_angle_trichotomy",
            "linear_cubature_orthogonality",
        ]
        conjectures = []
        for dim in dims:
            for pred in preds:
                h_id = self._next_id("STIEFEL")
                stmt = f"In dimension D={dim}, discrete 2-frames on V_2(R^{dim//2 - 1}) satisfy '{pred}'."
                conjectures.append(
                    CandidateHypothesis(
                        id=h_id,
                        statement=stmt,
                        category="StiefelManifold",
                        conjecture_type="STIEFEL_INVARIANT",
                        predicate=pred,
                        parameters={"dimension": dim},
                        expected_relation={"op": "==", "val": True},
                    )
                )
        return conjectures

    def generate_tri_even_qec_conjectures(
        self, dimensions: list[int] | None = None
    ) -> list[CandidateHypothesis]:
        """Generates quantum error correction conjectures for triply even codes and syzygies."""
        dims = dimensions or [16, 32, 64, 128]
        preds = [
            "triply_even_transversal_t",
            "cayley_dickson_triply_even",
            "syzygy_cycle_closure",
        ]
        conjectures = []
        for dim in dims:
            for pred in preds:
                h_id = self._next_id("TRIQEC")
                stmt = f"Quantum CSS stabilizer codes derived from D={dim} satisfy '{pred}'."
                conjectures.append(
                    CandidateHypothesis(
                        id=h_id,
                        statement=stmt,
                        category="QuantumCodingTheory",
                        conjecture_type="QUANTUM_ERROR_CORRECTION",
                        predicate=pred,
                        parameters={"dimension": dim},
                        expected_relation={"op": "==", "val": True},
                    )
                )
        return conjectures

    def generate_scaling_law_conjectures(self) -> list[CandidateHypothesis]:
        """Generates dimensional scaling and triangular number conjectures."""
        conjectures = [
            CandidateHypothesis(
                id=self._next_id("SCALE"),
                statement="Universal Cayley-Dickson cross-half zero divisor locus count satisfies (D-2)(D-4) == 8 * T_{(D/2)-2} for D in {16, 32, 64, 128}.",
                category="AlgebraicCombinatorics",
                conjecture_type="SCALING_LAW",
                predicate="triangular_zero_divisor_count",
                parameters={"dimensions": [16, 32, 64, 128]},
                expected_relation={"op": "==", "val": True},
            ),
            CandidateHypothesis(
                id=self._next_id("SCALE"),
                statement="Topological entropy of the 8-regular Ramanujan graph decomposes additively into h_top(C6) + h_cluster(K4) == 3.0 bits.",
                category="TopologicalEntropy",
                conjecture_type="SCALING_LAW",
                predicate="topological_entropy_additivity",
                parameters={"d_full": 8.0, "d_c6": 2.0, "cluster_size": 4.0},
                expected_relation={"op": "==", "val": 3.0},
            ),
            CandidateHypothesis(
                id=self._next_id("SCALE"),
                statement="Nicomachus block cube identity: k-th block of k consecutive odd integers sums to k^3 for all k in 1..10.",
                category="NicomachusTheorem",
                conjecture_type="SCALING_LAW",
                predicate="nicomachus_block_cube",
                parameters={"max_k": 10},
                expected_relation={"op": "==", "val": True},
            ),
            CandidateHypothesis(
                id=self._next_id("SCALE"),
                statement="Consecutive triangular square difference identity: T_k^2 - T_{k-1}^2 == k^3 for all k in 1..10.",
                category="TriangularInvariants",
                conjecture_type="SCALING_LAW",
                predicate="triangular_square_difference",
                parameters={"max_k": 10},
                expected_relation={"op": "==", "val": True},
            ),
        ]
        return conjectures

    def generate_smt_probes(self) -> list[CandidateHypothesis]:
        """Generates symbolic refutation probes for Z3 SMT solving."""
        return [
            CandidateHypothesis(
                id=self._next_id("SMT"),
                statement="SMT Probe: Can two distinct imaginary indices i != j have zero XOR charge i ^ j == 0?",
                category="SMTRefutation",
                conjecture_type="SMT_CONSTRAINT",
                predicate="zero_xor_distinct_indices",
                parameters={"bit_width": 3},
                expected_relation={"op": "==", "val": "UNSAT"},
            ),
            CandidateHypothesis(
                id=self._next_id("SMT"),
                statement="SMT Probe: Can a 2-colorable graph contain an odd cycle of length 3 (triangle)?",
                category="SMTRefutation",
                conjecture_type="SMT_CONSTRAINT",
                predicate="odd_cycle_in_bipartite",
                parameters={"cycle_length": 3},
                expected_relation={"op": "==", "val": "UNSAT"},
            ),
            CandidateHypothesis(
                id=self._next_id("SMT"),
                statement="SMT Probe: Can the 8-regular Ramanujan expander sector violate the spectral bound lambda^2 <= 4(d-1)?",
                category="SMTRefutation",
                conjecture_type="SMT_CONSTRAINT",
                predicate="ramanujan_optimality_slack",
                parameters={"d": 8, "lambda": 4},
                expected_relation={"op": "==", "val": "UNSAT"},
            ),
            CandidateHypothesis(
                id=self._next_id("SMT"),
                statement="SMT Probe: Can the universal projective stratification identity P^2 == (P-1)*P + P fail for any integer P?",
                category="SMTRefutation",
                conjecture_type="SMT_CONSTRAINT",
                predicate="projective_stratification_identity",
                parameters={},
                expected_relation={"op": "==", "val": "UNSAT"},
            ),
        ]

    def generate_lean4_probes(self, k_start: int = 6) -> list[CandidateHypothesis]:
        """Generates formal theorem probes targeting the Lean 4 kernel.
        
        Args:
            k_start: Starting value for parameterized theorems (e.g., triangular factorization k)
        """
        return [
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=f"Formal Theorem: Triangular factorization (2k+2)(2k) = 8*T_k for k={k_start}",
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="triangular_factorization",
                parameters={"k": k_start},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=f"Formal Theorem: Triangular factorization (2k+2)(2k) = 8*T_k for k={k_start + 1}",
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="triangular_factorization",
                parameters={"k": k_start + 1},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement="Formal Theorem: Universal Decoupling XOR exchange (i ^ k = j ^ m) <-> (i ^ j = k ^ m)",
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="xor_exchange",
                parameters={"i": 1, "j": 2, "k": 4, "m": 7},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement="Formal Theorem: Sedenion zero-divisor orthogonal annihilation (e1 + e2) * (e4 - e7) = 0",
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="sedenion_annihilation",
                parameters={
                    "i1": 1,
                    "j1": 2,
                    "s1": 1,
                    "s2": 1,
                    "i2": 4,
                    "j2": 7,
                    "t1": 1,
                    "t2": -1,
                },
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement="Formal Theorem: Autonomous sedenion zero divisor locus count (16-2)(16-4) = 168",
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="autonomous_sedenion_zd_count",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement="Formal Theorem: Autonomous Ramanujan expander slack invariant 4(8-1) - 4^2 = 12",
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="autonomous_ramanujan_slack",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement="Formal Theorem: Topological entropy degree additivity 2^1 * 2^2 = 2^3",
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="autonomous_entropy_degree_decomposition",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement="Formal Theorem: SMT 2-colorable odd triangle exclusion in Boolean logic",
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="autonomous_no_odd_triangle",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement="Formal Theorem: Distinct imaginary indices have non-zero XOR sum (i != j -> i ^ j != 0)",
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="autonomous_xor_distinct_nonzero",
                parameters={"i": 3, "j": 5},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement="Formal Theorem: Universal projective identity P^2 = (P-1)*P + P for P=7",
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="autonomous_projective_identity",
                parameters={"P": 7},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            # TowerAssociator theorems (HYP-054, HYP-055) — kernel-certified 0-sorry proofs.
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: General cross-half index criterion — for all n ≥ 3, "
                    "i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j is necessary and sufficient for cross-half "
                    "zero divisors to annihilate in the 2^(n+1)-dimensional CD algebra."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="index_criterion_general",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: Zero-divisor annihilation iff non-associativity — "
                    "crossSign_eq_assocNeg: the cross-half annihilation sign equals the "
                    "associator negation sign for all tower levels n ≥ 3."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="crossSign_eq_assocNeg",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: basis_flexible — all Cayley-Dickson tower algebras "
                    "satisfy the flexibility identity (xy)x = x(yx) for all basis elements."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="basis_flexible",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            # TowerDegreeSpectrum theorems (HYP-075..HYP-078)
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: dim32_degree_counts — in dimension 32, exactly 84 pairs have "
                    "4 non-associating middles (degree 8) and 126 pairs have 12 non-associating middles (degree 24)."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="dim32_degree_counts",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: dim32_charge_sector_regularity — sectors chi in 1..8 are 24-regular, "
                    "sectors chi in 9..15 are (8, 24)-biregular."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="dim32_charge_sector_regularity",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: dim32_biregular_high_degree_pairs — high-degree pairs in biregular "
                    "sector f ^^^ 8 are precisely (f, 8) and (8, f) for f in 1..7."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="dim32_biregular_high_degree_pairs",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: nonassocMiddles_card_dim64_four_levels — all 4 discrete levels "
                    "{4, 12, 20, 28} (degrees {8, 24, 40, 56}) are strictly attained in dimension 64."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="nonassocMiddles_card_dim64_four_levels",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: associatingTriples_dim16 — exactly 2248 basis triples associate "
                    "in the 16-dimensional sedenions: 2248 = 16^3 / 2 + 14*16 - 24."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="associatingTriples_dim16",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            # D=128 biregular edge count tier theorems (HYP-166)
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: bireg_edges_d128_mid — in dimension D=128, depth k=1 "
                    "(Q=16, χ ∈ {17..24}), the biregular sector has exactly 4128 edges."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="bireg_edges_d128_mid",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: bireg_edges_d128_low — in dimension D=128, depth k=2 "
                    "(Q=8, χ ∈ {9..15}), the biregular sector has exactly 8736 edges."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="bireg_edges_d128_low",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: op013_biregular_edge_formula_settled — the universal biregular "
                    "edge formula E = d_low*(3D-16-d_low)/2 is simultaneously certified across all "
                    "6 tiers (D∈{32,64,128}, k∈{0,1,2}): 288, 672, 1824, 1440, 4128, 8736."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="op013_biregular_edge_formula_settled",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
            ),
            # Tower universal inductive theorems (Aristotle Review Point 6, Sprint 124)
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: nonassocMiddles_card_mod_eight — for all tower levels n ≥ 3 and any "
                    "pair of basis indices with i ^^^ j ≠ 0, the number of non-associating middles is congruent to 4 modulo 8."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="nonassocMiddles_card_mod_eight",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
                generality="UNIVERSAL_THEOREM",
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: nonassocMiddles_card_spectrum — for all tower levels n ≥ 3 and any "
                    "pair of basis indices with i ^^^ j ≠ 0, the count of non-associating middles satisfies "
                    "nonassocMiddles_card ∈ { 4 + 8*k | k < 2^(n-3) }."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="nonassocMiddles_card_spectrum",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
                generality="UNIVERSAL_THEOREM",
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: chargeSector_regular_iff — for all tower levels n ≥ 3 and any non-zero charge χ < 2^n, "
                    "sector χ is regular (all pairs have degree 2^(n-1) - 4) if and only if χ < 8 or χ is a power of 2."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="chargeSector_regular_iff",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
                generality="UNIVERSAL_THEOREM",
            ),
            CandidateHypothesis(
                id=self._next_id("LEAN"),
                statement=(
                    "Formal Theorem: regularSectorCharges_card — for all tower levels n ≥ 3, the count of regular "
                    "charge sectors in the 2^(n+1)-dimensional algebra is exactly n + 4."
                ),
                category="FormalVerification",
                conjecture_type="LEAN4_THEOREM",
                predicate="regularSectorCharges_card",
                parameters={},
                expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
                generality="UNIVERSAL_THEOREM",
            ),
        ]


    def generate_organism_conjectures(self) -> list[CandidateHypothesis]:
        """Generates cross-domain Tower Organism hypotheses across dimensions and parameters."""
        hyps: list[CandidateHypothesis] = []
        # Hebrew sofit ending phrases that satisfy both boundary closure and polar annihilation
        sofit_phrases = ["שלם", "שלום"]
        for phrase in sofit_phrases:
            h_id = self._next_id("ORG-SOFIT")
            hyps.append(
                CandidateHypothesis(
                    id=h_id,
                    statement=(
                        f"Linguistic proposition '{phrase}' satisfies sofit boundary closure ∂σ = 0 "
                        "(c1 = 0, H1 = 0) and antipodal sedenion zero-divisor variety annihilation."
                    ),
                    category="Topology",
                    conjecture_type="TOWER_ORGANISM",
                    predicate="sofit_boundary_closure",
                    parameters={"linguistic_phrase": phrase},
                    expected_relation={"op": "==", "val": True},
                )
            )

        for dim in [16, 32, 64]:
            hyps.append(
                CandidateHypothesis(
                    id=self._next_id("ORG-PARITY"),
                    statement=(
                        f"Stella Octangula dual tetrahedra T1 ⊕ T2 strictly obey F_2^3 parity selection "
                        f"rules with zero-divisor annihilation in dimension {dim}."
                    ),
                    category="Algebra",
                    conjecture_type="TOWER_ORGANISM",
                    predicate="stella_octangula_parity",
                    parameters={"dimension": dim},
                    expected_relation={"op": "==", "val": True},
                )
            )

        # Diverse MOG tetrad vectors exploring distinct basins
        mog_vectors = [
            [1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0],
            [0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0],
            [0.5, 0.5, 0.5, 0.5, 0.0, 0.0, 0.0, 0.0],
            [0.0, 0.0, 0.0, 0.0, 0.5, 0.5, 0.5, 0.5],
            [1.0, -1.0, 0.0, 0.0, 0.0, 0.0, 1.0, -1.0],
        ]
        for vec in mog_vectors:
            hyps.append(
                CandidateHypothesis(
                    id=self._next_id("ORG-MOG"),
                    statement=(
                        f"Curtis 35 Miracle Octad Generator tetrad pairs stabilize parameter vector "
                        f"{vec[:4]}... into a discrete invariant nodal basin of attraction."
                    ),
                    category="Polytope",
                    conjecture_type="TOWER_ORGANISM",
                    predicate="mog_tetrad_basin",
                    parameters={"vector": vec},
                    expected_relation={"op": "==", "val": True},
                )
            )

        for phrase in ["שלם", "שלום"]:
            for dim in [16, 32]:
                hyps.append(
                    CandidateHypothesis(
                        id=self._next_id("ORG-SOUND"),
                        statement=(
                            f"Tower Organism 5-pillar pipeline satisfies simultaneous topological closure, "
                            f"Weyl chamber canonicalization, functor naturality (S_diagram < 1e-4), and "
                            f"flat sheaf equilibrium (h1_flat = 1) for '{phrase}' in dimension {dim}."
                        ),
                        category="AutonomousSystem",
                        conjecture_type="TOWER_ORGANISM",
                        predicate="tower_organism_soundness",
                        parameters={"linguistic_phrase": phrase, "dimension": dim, "functor_epochs": 120},
                        expected_relation={"op": "==", "val": True},
                    )
                )

        for dim in [16, 32]:
            hyps.append(
                CandidateHypothesis(
                    id=self._next_id("ORG-ENTROPY"),
                    statement=(
                        f"Zero-divisor graph persistent homology in dimension {dim} satisfies the "
                        "information-theoretic entropy lower bound S_top >= 0.50 bits against trivial tautology collapse."
                    ),
                    category="InformationTheory",
                    conjecture_type="TOWER_ORGANISM",
                    predicate="persistent_entropy_barrier",
                    parameters={"dimension": dim},
                    expected_relation={"op": "==", "val": True},
                )
            )

        # Prime Organism Ground State & E8 Root Lattice Cubic Excess Conjectures
        for n in [2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 17, 19, 23, 29, 31]:
            hyps.append(
                CandidateHypothesis(
                    id=self._next_id("ORG-PRIME-GROUND"),
                    statement=(
                        f"Integer n={n} satisfies the prime ground state curvature invariant "
                        f"(S({n}) = 0.0 iff n is prime, S({n}) > 0.0 iff n is composite)."
                    ),
                    category="NumberTheory",
                    conjecture_type="TOWER_ORGANISM",
                    predicate="prime_ground_state",
                    parameters={"n": n},
                    expected_relation={"op": "==", "val": True},
                )
            )
            hyps.append(
                CandidateHypothesis(
                    id=self._next_id("ORG-E8-EXCESS"),
                    statement=(
                        f"Integer n={n} satisfies E8 root lattice cubic excess vanishing "
                        f"(Δ_E8({n}) = 0 iff n is prime, Δ_E8({n}) >= 8 iff n is composite)."
                    ),
                    category="NumberTheory",
                    conjecture_type="TOWER_ORGANISM",
                    predicate="e8_prime_excess",
                    parameters={"n": n},
                    expected_relation={"op": "==", "val": True},
                )
            )

        # Gosset 4₂₁ Metric Syllogisms (Deductive, Orthogonal, Antipodal)
        try:
            from ..polytope.gosset_logic import GossetLogicSynthesizer
            syn = GossetLogicSynthesizer()
            u = syn.integer_roots[0]  # (1, 1, 0, 0, 0, 0, 0, 0)
            ded_partners = [r for r in syn.integer_roots if abs(sum(a * b for a, b in zip(u, r)) - 1.0) < 1e-6]
            if ded_partners:
                v_ded = ded_partners[0]
                hyps.append(
                    CandidateHypothesis(
                        id=self._next_id("ORG-SYLLOGISM-DED"),
                        statement="Premise and derived proposition satisfy Gosset 4₂₁ metric syllogism d(u,v) = √2 (inner product = 1).",
                        category="PolytopeLogic",
                        conjecture_type="TOWER_ORGANISM",
                        predicate="gosset_metric_syllogism",
                        parameters={"u": list(u), "v": list(v_ded), "relation": "deductive"},
                        expected_relation={"op": "==", "val": True},
                    )
                )
            ortho_partners = [r for r in syn.integer_roots if abs(sum(a * b for a, b in zip(u, r))) < 1e-6]
            if ortho_partners:
                v_ortho = ortho_partners[0]
                hyps.append(
                    CandidateHypothesis(
                        id=self._next_id("ORG-SYLLOGISM-ORTHO"),
                        statement="Orthogonal proposition pair satisfies Gosset 4₂₁ logical independence d(u,v) = 2 (inner product = 0).",
                        category="PolytopeLogic",
                        conjecture_type="TOWER_ORGANISM",
                        predicate="gosset_metric_syllogism",
                        parameters={"u": list(u), "v": list(v_ortho), "relation": "orthogonal"},
                        expected_relation={"op": "==", "val": True},
                    )
                )
            v_anti = [-x for x in u]
            hyps.append(
                CandidateHypothesis(
                    id=self._next_id("ORG-SYLLOGISM-ANTI"),
                    statement="Antipodal proposition pair satisfies Gosset 4₂₁ logical contradiction d(u, -u) = 2√2 (inner product = -2).",
                    category="PolytopeLogic",
                    conjecture_type="TOWER_ORGANISM",
                    predicate="gosset_metric_syllogism",
                    parameters={"u": list(u), "v": v_anti, "relation": "antipodal"},
                    expected_relation={"op": "==", "val": True},
                )
            )
        except Exception:
            pass

        hyps.extend(self.generate_relational_topology_conjectures())
        return hyps

    def generate_relational_topology_conjectures(self) -> list[CandidateHypothesis]:
        """Generates Classical Chinese Relational Topology, Contact Boundary MHD, and Chingon Codon hypotheses."""
        hyps: list[CandidateHypothesis] = [
            CandidateHypothesis(
                id=self._next_id("REL-MHD-HELICITY"),
                statement=(
                    "Contact boundary MHD helicity decomposition satisfies K_total = K_3D + K_gauge "
                    "with complete Lamb vector and vortex stretching quenching ||L_16|| = 0 across all 672 zero-divisor edges."
                ),
                category="RelationalTopology",
                conjecture_type="TOWER_ORGANISM",
                predicate="contact_boundary_helicity",
                parameters={"dimension": 16, "reservoir_dim": 13, "physical_dim": 3},
                expected_relation={"op": "==", "val": True},
            ),
            CandidateHypothesis(
                id=self._next_id("REL-CHINESE-COHERENCE"),
                statement=(
                    "Classical Chinese relational topology bridge faithfully preserves positional syntactic roles, "
                    "8 Trigram <-> Octonion basis and 64 Hexagram <-> Chingon D=64 basis bijections across AST cross-domain morphisms."
                ),
                category="RelationalTopology",
                conjecture_type="TOWER_ORGANISM",
                predicate="relational_coherence_chinese",
                parameters={"grammar": "classical_chinese", "trigram_dim": 8, "hexagram_dim": 64},
                expected_relation={"op": "==", "val": True},
            ),
            CandidateHypothesis(
                id=self._next_id("REL-CHINGON-CODON"),
                statement=(
                    "Chingon D=64 codon lattice exhibits an exact 32:32 Yang/Yin parity split in F_2^6 "
                    "and resolves the canonical 64 -> 21 amino acid relational degeneracy."
                ),
                category="Biology",
                conjecture_type="TOWER_ORGANISM",
                predicate="chingon_codon_parity",
                parameters={"dimension": 64, "yang_even": 32, "yin_odd": 32, "amino_acid_classes": 21},
                expected_relation={"op": "==", "val": True},
            ),
        ]
        return hyps

    def generate_modular_hecke_conjectures(self) -> list[CandidateHypothesis]:
        """
        Generates modular Hecke algebra, Ramanujan tau congruences, and vortex dynamic conjectures
        evaluated by the ESP32-S3 hardware co-processor and certified by Aristotle Lean 4 proofs.
        """
        from ..integrations.esp32_quantum_entropy import HECKE_WORDS

        hyps: list[CandidateHypothesis] = []

        # 1. Hecke word multiplier exact evaluation
        for word_id, (word_name, mult) in HECKE_WORDS.items():
            hyps.append(
                CandidateHypothesis(
                    id=self._next_id("MOD-HECKE"),
                    statement=(
                        f"Hecke word {word_name} on modular discriminant Δ evaluates to exact multiplier "
                        f"{mult} in the trinity digital root basin (Lean theorem: RequestProject.Delta.HeckeImages.word_multipliers)."
                    ),
                    category="ModularForms",
                    conjecture_type="MODULAR_HECKE",
                    predicate="hecke_word_multiplier",
                    parameters={"word_id": word_id, "expected_mult": mult},
                    expected_relation={"op": "==", "val": True},
                )
            )

        # 2. 3-adic congruence tau(n) = n^2 sigma_7(n) (mod 27) for gcd(n, 3) = 1
        test_primes_and_coprimes = [1, 2, 4, 5, 7, 8, 10, 11, 13, 14, 16, 17, 19, 20]
        for n in test_primes_and_coprimes:
            hyps.append(
                CandidateHypothesis(
                    id=self._next_id("MOD-CONGR"),
                    statement=(
                        f"Ramanujan tau function satisfies 3-adic congruence tau({n}) ≡ {n}^2 * σ_7({n}) (mod 27) "
                        f"(Lean theorem: RequestProject.Delta.Coefficients.tau_congr_mod_27)."
                    ),
                    category="ModularForms",
                    conjecture_type="MODULAR_HECKE",
                    predicate="tau_congruence_mod27",
                    parameters={"n": n},
                    expected_relation={"op": "==", "val": True},
                )
            )

        # 3. Digital root trinity detector: dr(tau(n)) in {3,6,9} <=> 3 | tau(n) <=> 3 | sigma(n)
        for n in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]:
            hyps.append(
                CandidateHypothesis(
                    id=self._next_id("MOD-TRINITY"),
                    statement=(
                        f"Digital root dr(tau({n})) ∈ {{3,6,9}} if and only if 3 | tau({n}) and 3 | σ({n}) "
                        f"(Lean theorem: RequestProject.Delta.Coefficients.three_dvd_tau_iff_three_dvd_sigma)."
                    ),
                    category="NumberTheory",
                    conjecture_type="MODULAR_HECKE",
                    predicate="digital_root_trinity_detector",
                    parameters={"n": n},
                    expected_relation={"op": "==", "val": True},
                )
            )

        # 4. Vortex doubling orbit avoidance
        hyps.append(
            CandidateHypothesis(
                id=self._next_id("MOD-VORTEX"),
                statement=(
                    "Doubling orbit x ↦ 2x mod 9 on Z/9Z forms period-6 cycle {1,2,4,8,7,5} "
                    "strictly avoiding trinity {0,3,6,9} (Lean theorem: RequestProject.DigitalRoot.Decimal.vortex_orbits_partition)."
                ),
                category="Dynamics",
                conjecture_type="MODULAR_HECKE",
                predicate="vortex_doubling_orbit_avoidance",
                parameters={},
                expected_relation={"op": "==", "val": True},
            )
        )

        # 5. Fibonacci digital root minimal period 24 and trinity divisibility
        hyps.append(
            CandidateHypothesis(
                id=self._next_id("MOD-FIB"),
                statement=(
                    "Fibonacci digital roots modulo 9 exhibit minimal period 24 where 3 | F_n ⟺ 4 | n "
                    "(Lean theorem: RequestProject.DigitalRoot.Fibonacci.digitalRoot_fib_period_24)."
                ),
                category="NumberTheory",
                conjecture_type="MODULAR_HECKE",
                predicate="fibonacci_digital_root_period",
                parameters={},
                expected_relation={"op": "==", "val": True},
            )
        )

        # 6. T2 vs T3 pointwise anti-parallelism
        hyps.append(
            CandidateHypothesis(
                id=self._next_id("MOD-ANTIPAR"),
                statement=(
                    "Hecke operators T_2 and T_3 act point-wise antiparallel on cusp forms: "
                    "T_2(m)*T_3(m) = tau(6)*tau(m)^2 < 0 (Lean theorem: RequestProject.Delta.WordComparison.prodT_neg)."
                ),
                category="ModularForms",
                conjecture_type="MODULAR_HECKE",
                predicate="t2_vs_t3_antiparallel",
                parameters={"max_m": 20},
                expected_relation={"op": "==", "val": True},
            )
        )

        # 7. T2 vs T3 ratio invariance
        hyps.append(
            CandidateHypothesis(
                id=self._next_id("MOD-RATIO"),
                statement=(
                    "Ratio of Hecke eigenvalues 21*T_2(m) = -2*T_3(m) is universally invariant on cusp forms "
                    "(Lean theorem: RequestProject.Delta.WordComparison.ratioT_eq)."
                ),
                category="ModularForms",
                conjecture_type="MODULAR_HECKE",
                predicate="t2_vs_t3_ratio_invariance",
                parameters={"max_m": 20},
                expected_relation={"op": "==", "val": True},
            )
        )

        # 8. Delta unit circle reflection and phase lock
        hyps.append(
            CandidateHypothesis(
                id=self._next_id("MOD-DELTA"),
                statement=(
                    "Modular discriminant Δ satisfies unit circle reflection ||Δ(1/z*)|| = |z|^12 ||Δ(z)|| "
                    "with arc phase lock 2 arg Δ = -12 arg z (Lean theorem: RequestProject.Delta.Modularity.form_arc_phase)."
                ),
                category="ComplexAnalysis",
                conjecture_type="MODULAR_HECKE",
                predicate="delta_unit_circle_reflection",
                parameters={},
                expected_relation={"op": "==", "val": True},
            )
        )

        return hyps


    def _generate_candidate_batch(
        self, modality_order: list[str], batch_size: int = 5
    ) -> list[CandidateHypothesis]:
        """
        Generate a batch of candidate hypotheses for scoring.
        
        Args:
            modality_order: Priority order of conjecture types
            batch_size: Number of candidates to generate per modality
        
        Returns:
            List of CandidateHypothesis objects for evaluation
        """
        candidates = []
        
        # Boost generation of hypotheses related to proven invariants
        # This creates semantic guidance by extending proven work
        proven_predicates = set()
        for inv in self.proven_invariants:
            # Extract predicate names from proven theorem names
            if 'associator' in inv.lower():
                proven_predicates.add('alternating_associator')
                proven_predicates.add('associator_coset_shift')
            if 'flexible' in inv.lower():
                proven_predicates.add('flexibility')
            if 'xor' in inv.lower():
                proven_predicates.add('xor_exchange')
                proven_predicates.add('zero_xor_distinct_indices')
            if 'annihilation' in inv.lower():
                proven_predicates.add('sedenion_annihilation')
            if 'triangular' in inv.lower():
                proven_predicates.add('triangular_factorization')
            if 'ramanujan' in inv.lower():
                proven_predicates.add('ramanujan_bound')
        
        # Ensure we generate at least one candidate from each requested modality
        for modality in modality_order:
            if modality == "ALGEBRAIC_IDENTITY":
                # Prioritize identities related to proven theorems
                if proven_predicates and self._seq % 3 == 0:
                    # Generate hypothesis related to proven invariant
                    ident = list(proven_predicates)[self._seq % len(proven_predicates)]
                    if ident in self._identities:
                        dim = [8, 16, 32][self._seq % 3]
                        params = {"dimension": dim}
                        if not self._is_duplicate("ALGEBRAIC_IDENTITY", ident, params):
                            self._mark_seen("ALGEBRAIC_IDENTITY", ident, params)
                            candidates.append(CandidateHypothesis(
                                id=f"BATCH-ALG-{self._seq:05d}",
                                statement=f"Extension of proven invariant: In dimension {dim}, '{ident}' holds universally.",
                                category="DynamicAlgebra",
                                conjecture_type="ALGEBRAIC_IDENTITY",
                                predicate=ident,
                                parameters=params,
                                expected_relation={"op": "==", "val": True},
                            ))
                            continue
                
                dim = [8, 16, 32][self._seq % 3]
                ident = self._identities[self._seq % len(self._identities)]
                params = {"dimension": dim}
                if not self._is_duplicate("ALGEBRAIC_IDENTITY", ident, params):
                    self._mark_seen("ALGEBRAIC_IDENTITY", ident, params)
                    candidates.append(CandidateHypothesis(
                        id=f"BATCH-ALG-{self._seq:05d}",
                        statement=f"In dimension {dim}, algebraic property '{ident}' holds universally.",
                        category="DynamicAlgebra",
                        conjecture_type="ALGEBRAIC_IDENTITY",
                        predicate=ident,
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    ))
            
            elif modality == "GRAPH_INVARIANT":
                dim = [16, 32][self._seq % 2]
                max_sec = self._max_sector.get(dim, dim // 2 - 1)
                sector = (self._seq % max_sec) + 1
                prop = self._graph_properties[self._seq % len(self._graph_properties)]
                params = {"dimension": dim, "sector": sector}
                if not self._is_duplicate("GRAPH_INVARIANT", prop, params):
                    self._mark_seen("GRAPH_INVARIANT", prop, params)
                    candidates.append(CandidateHypothesis(
                        id=f"BATCH-GRAPH-{self._seq:05d}",
                        statement=f"Sector {sector} of {dim}D zero-divisor graph satisfies '{prop}'.",
                        category="SpectralGraphTheory",
                        conjecture_type="GRAPH_INVARIANT",
                        predicate=prop,
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    ))
            
            elif modality == "CODE_INVARIANT":
                sec = (self._seq % 7) + 1
                prop = self._code_properties[self._seq % len(self._code_properties)]
                params = {"dimension": 16, "sector": sec}
                if not self._is_duplicate("CODE_INVARIANT", prop, params):
                    self._mark_seen("CODE_INVARIANT", prop, params)
                    candidates.append(CandidateHypothesis(
                        id=f"BATCH-CODE-{self._seq:05d}",
                        statement=f"Code from sector {sec} satisfies '{prop}'.",
                        category="QuantumCodingTheory",
                        conjecture_type="CODE_INVARIANT",
                        predicate=prop,
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    ))
            
            elif modality == "SCALING_LAW":
                scaling_props = ["triangular_zero_divisor_count", "topological_entropy_additivity"]
                prop = scaling_props[self._seq % len(scaling_props)]
                params = {"dimensions": [16, 32]}
                if not self._is_duplicate("SCALING_LAW", prop, params):
                    self._mark_seen("SCALING_LAW", prop, params)
                    candidates.append(CandidateHypothesis(
                        id=f"BATCH-SCALE-{self._seq:05d}",
                        statement=f"Scaling law '{prop}' holds across dimensions.",
                        category="AlgebraicCombinatorics",
                        conjecture_type="SCALING_LAW",
                        predicate=prop,
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    ))
            
            elif modality == "SMT_CONSTRAINT":
                smt_props = ["zero_xor_distinct_indices", "odd_cycle_in_bipartite"]
                prop = smt_props[self._seq % len(smt_props)]
                params = {"bit_width": 3}
                if not self._is_duplicate("SMT_CONSTRAINT", prop, params):
                    self._mark_seen("SMT_CONSTRAINT", prop, params)
                    candidates.append(CandidateHypothesis(
                        id=f"BATCH-SMT-{self._seq:05d}",
                        statement=f"SMT constraint '{prop}' check.",
                        category="SMTRefutation",
                        conjecture_type="SMT_CONSTRAINT",
                        predicate=prop,
                        parameters=params,
                        expected_relation={"op": "==", "val": "UNSAT"},
                    ))
            
            elif modality == "LEAN4_THEOREM":
                k_offset = (self._seq // 2) % 10
                lean_probes = self.generate_lean4_probes(k_start=k_offset + 6)
                added = 0
                for probe in lean_probes:
                    if not self._is_duplicate(probe.conjecture_type, probe.predicate, probe.parameters):
                        self._mark_seen(probe.conjecture_type, probe.predicate, probe.parameters)
                        candidates.append(probe)
                        added += 1
                        if added >= batch_size:
                            break

            elif modality == "TOWER_ORGANISM":
                org_probes = self.generate_organism_conjectures()
                added = 0
                for probe in org_probes:
                    if not self._is_duplicate(probe.conjecture_type, probe.predicate, probe.parameters):
                        self._mark_seen(probe.conjecture_type, probe.predicate, probe.parameters)
                        candidates.append(probe)
                        added += 1
                        if added >= batch_size:
                            break

            elif modality == "MODULAR_HECKE":
                hecke_probes = self.generate_modular_hecke_conjectures()
                added = 0
                for probe in hecke_probes:
                    if not self._is_duplicate(probe.conjecture_type, probe.predicate, probe.parameters):
                        self._mark_seen(probe.conjecture_type, probe.predicate, probe.parameters)
                        candidates.append(probe)
                        added += 1
                        if added >= batch_size:
                            break

            elif modality == "FRAME_FIELD_INVARIANT":
                frame_probes = self.generate_frame_field_conjectures()
                added = 0
                for probe in frame_probes:
                    if not self._is_duplicate(probe.conjecture_type, probe.predicate, probe.parameters):
                        self._mark_seen(probe.conjecture_type, probe.predicate, probe.parameters)
                        candidates.append(probe)
                        added += 1
                        if added >= batch_size:
                            break

            elif modality == "PROJECTIVE_PENCIL_FIBRATION":
                pencil_probes = self.generate_projective_pencil_conjectures()
                added = 0
                for probe in pencil_probes:
                    if not self._is_duplicate(probe.conjecture_type, probe.predicate, probe.parameters):
                        self._mark_seen(probe.conjecture_type, probe.predicate, probe.parameters)
                        candidates.append(probe)
                        added += 1
                        if added >= batch_size:
                            break

            elif modality == "STIEFEL_INVARIANT":
                stiefel_probes = self.generate_tower_stiefel_conjectures()
                added = 0
                for probe in stiefel_probes:
                    if not self._is_duplicate(probe.conjecture_type, probe.predicate, probe.parameters):
                        self._mark_seen(probe.conjecture_type, probe.predicate, probe.parameters)
                        candidates.append(probe)
                        added += 1
                        if added >= batch_size:
                            break

            elif modality == "QUANTUM_ERROR_CORRECTION":
                qec_probes = self.generate_tri_even_qec_conjectures()
                added = 0
                for probe in qec_probes:
                    if not self._is_duplicate(probe.conjecture_type, probe.predicate, probe.parameters):
                        self._mark_seen(probe.conjecture_type, probe.predicate, probe.parameters)
                        candidates.append(probe)
                        added += 1
                        if added >= batch_size:
                            break

        return candidates

    def generate_next_hypothesis(self) -> CandidateHypothesis:
        """
        Dynamically synthesizes the next hypothesis on-the-fly across multimodal domains,
        steered by GUDHI persistent Shannon entropy feedback AND semantic proximity to
        proven invariants.

        Deduplicates against the ReasoningStore (if provided) by skipping
        (conjecture_type, predicate, dimension, sector) tuples that already exist.
        At most _DEDUP_MAX_SKIP consecutive duplicates are skipped before giving up
        and returning the next candidate anyway (prevents infinite loop when the space
        is exhausted).
        
        Uses weighted selection based on structural proximity to proven theorems,
        spectral database availability, and manifold stability.
        """
        _DEDUP_MAX_SKIP = 50

        # Load proven theorems from Lean bridge if not yet loaded
        if self.lean_bridge and not self.proven_invariants:
            self.load_proven_theorems_from_lean()

        for _skip in range(_DEDUP_MAX_SKIP + 1):
            self._seq += 1

            # Select modality based on topological stability mode AND semantic guidance
            if self.manifold_stability_mode == "MANIFOLD_STABLE":
                # Stable manifold: prioritize topological graph invariants, quantum CSS codes,
                # Tower Organism, Lean 4 kernel certification, and Modular Hecke forms
                modality_order = [
                    "MODULAR_HECKE",
                    "TOWER_ORGANISM",
                    "LEAN4_THEOREM",
                    "GRAPH_INVARIANT",
                    "CODE_INVARIANT",
                    "SCALING_LAW",
                    "ALGEBRAIC_IDENTITY",
                    "SMT_CONSTRAINT",
                ]
            elif self.manifold_stability_mode == "MANIFOLD_COLLAPSE_RISK":
                # Risk of collapse: focus on algebraic rigidity, SMT refutations, and Hecke dynamics
                modality_order = [
                    "SMT_CONSTRAINT",
                    "ALGEBRAIC_IDENTITY",
                    "MODULAR_HECKE",
                    "TOWER_ORGANISM",
                    "SCALING_LAW",
                    "LEAN4_THEOREM",
                    "GRAPH_INVARIANT",
                    "CODE_INVARIANT",
                ]
            else:
                # Exploration: rotate modalities across successive ticks for maximal diversity
                shift = self._seq % len(self._conjecture_types)
                modality_order = self._conjecture_types[shift:] + self._conjecture_types[:shift]

            # Generate candidates and score them by structural proximity
            candidates = self._generate_candidate_batch(modality_order)
            
            if candidates:
                # Score each candidate by structural proximity AND novelty (filtering reification traps)
                scored = []
                for cand in candidates:
                    is_clean, reason = ReificationTrapDetector.audit_hypothesis(cand)
                    if not is_clean:
                        continue
                    base_score = self._score_by_structural_proximity(
                        cand.conjecture_type, cand.predicate, cand.parameters
                    )
                    # Phase 2: Incorporate novelty into scoring
                    novelty = self.compute_novelty_score(cand)
                    # Combined score: 70% structural, 30% novelty
                    combined_score = 0.7 * base_score + 0.3 * novelty
                    
                    # Phase 2: Filter out low-novelty candidates (optional, configurable)
                    if novelty >= self._novelty_threshold:
                        scored.append((combined_score, cand))
                
                # Return highest-scoring candidate
                if scored:
                    if self.manifold_stability_mode == "EXPLORATION":
                        target_mod = modality_order[0]
                        mod_candidates = [c for c in scored if c[1].conjecture_type == target_mod]
                        if mod_candidates:
                            best_hypothesis = mod_candidates[0][1]
                        else:
                            scored.sort(key=lambda x: -x[0])
                            best_hypothesis = scored[0][1]
                    else:
                        scored.sort(key=lambda x: -x[0])
                        best_hypothesis = scored[0][1]

                    
                    if self.quantum_engine is not None:
                        try:
                            q_res = self.quantum_engine.project_quantum_collapse()
                            self.last_quantum_collapse = q_res
                            best_hypothesis.parameters.update({
                                "quantum_sector": q_res.collapse_sector,
                                "quantum_syndrome": q_res.syndrome_int,
                                "quantum_entropy_delta": q_res.entropy_delta,
                                "physical_entropy": q_res.source_info.get("physical", False),
                            })
                        except Exception:
                            pass

                    # Phase 2: Auto-queue high-priority Lean theorems
                    if best_hypothesis.conjecture_type == "LEAN4_THEOREM":
                        priority = scored[0][0]  # Use combined score as priority
                        self.add_to_priority_queue(best_hypothesis, priority)
                    
                    return best_hypothesis

            # Fallback to original generation logic if no scored candidates
            if self.cognitive_bridge is not None:
                get_cand = getattr(self.cognitive_bridge, "get_candidate_hypothesis", None)
                if callable(get_cand):
                    llm_hyp = get_cand()
                    if llm_hyp is not None:
                        return llm_hyp
                elif getattr(self.cognitive_bridge, "is_available", lambda: False)():
                    if self._seq % 3 == 0:
                        focus = modality_order[self._seq % len(modality_order)].lower()
                        llm_hyp = self.cognitive_bridge.generate_candidate_hypothesis(
                            focus_area=focus,
                            recent_verified=self.confirmed_invariants_history,
                            negative_feedback=self.negative_feedback_history,
                        )
                        if llm_hyp is not None:
                            return llm_hyp

            modality = modality_order[self._seq % len(modality_order)]
            candidate: CandidateHypothesis | None = None

            if modality == "ALGEBRAIC_IDENTITY":
                # Interleave standard identities with next_steps.md associator_coset_shift probes
                if self._seq % 2 == 0:
                    dim = [8, 16, 32][self._seq % 3]
                    # Select non-trivial pair (i, j)
                    i = (self._seq % (dim - 2)) + 1
                    j = ((self._seq * 3) % (dim - 2)) + 1
                    if i == j:
                        j = (i % (dim - 2)) + 1
                    params = {"dimension": dim, "i": min(i, j), "j": max(i, j)}
                    if self._is_duplicate("ALGEBRAIC_IDENTITY", "associator_coset_shift", params):
                        continue
                    candidate = CandidateHypothesis(
                        id=f"DYN-ALG-{self._seq:05d}",
                        statement=f"In dimension {dim}, associator sign map k -> omega({params['i']}, k, {params['j']}) is invariant under translation by span({params['i']}, {params['j']}).",
                        category="CayleyDicksonAssociator",
                        conjecture_type="ALGEBRAIC_IDENTITY",
                        predicate="associator_coset_shift",
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )
                    self._mark_seen("ALGEBRAIC_IDENTITY", "associator_coset_shift", params)
                else:
                    dim_idx = (self._seq // len(self._identities)) % len(self._dimensions)
                    ident_idx = self._seq % len(self._identities)
                    dim = self._dimensions[dim_idx]
                    ident = self._identities[ident_idx]
                    params = {"dimension": dim}
                    if self._is_duplicate("ALGEBRAIC_IDENTITY", ident, params):
                        continue
                    candidate = CandidateHypothesis(
                        id=f"DYN-ALG-{self._seq:05d}",
                        statement=f"In dimension {dim}, algebraic property '{ident}' holds universally.",
                        category="DynamicAlgebra",
                        conjecture_type="ALGEBRAIC_IDENTITY",
                        predicate=ident,
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )
                    self._mark_seen("ALGEBRAIC_IDENTITY", ident, params)

            elif modality == "GRAPH_INVARIANT":
                # Interleave regular classification, crown blowup spectrum, and biregular degrees
                sub_mode = self._seq % 4
                if sub_mode == 0:
                    dim_choices = [16, 32]
                    dim = dim_choices[self._seq % len(dim_choices)]
                    max_sec = self._max_sector.get(dim, dim // 2 - 1)
                    sector = (self._seq % max_sec) + 1
                    params = {"dimension": dim, "sector": sector}
                    if self._is_duplicate("GRAPH_INVARIANT", "regular_charge_sector_classification", params):
                        continue
                    candidate = CandidateHypothesis(
                        id=f"DYN-GRAPH-{self._seq:05d}",
                        statement=f"Sector {sector} of {dim}D zero-divisor graph satisfies regularity classification.",
                        category="SpectralGraphTheory",
                        conjecture_type="GRAPH_INVARIANT",
                        predicate="regular_charge_sector_classification",
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )
                    self._mark_seen("GRAPH_INVARIANT", "regular_charge_sector_classification", params)
                elif sub_mode == 1:
                    dim_choices = [16, 32, 64]
                    dim = dim_choices[self._seq % len(dim_choices)]
                    pole_chi = dim // 4
                    params = {"dimension": dim, "sector": pole_chi}
                    if self._is_duplicate("GRAPH_INVARIANT", "crown_graph_blowup_spectrum", params):
                        continue
                    candidate = CandidateHypothesis(
                        id=f"DYN-GRAPH-{self._seq:05d}",
                        statement=f"Doubling-pole sector {pole_chi} of {dim}D zero-divisor graph has Crown Graph blowup spectrum.",
                        category="SpectralGraphTheory",
                        conjecture_type="GRAPH_INVARIANT",
                        predicate="crown_graph_blowup_spectrum",
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )
                    self._mark_seen("GRAPH_INVARIANT", "crown_graph_blowup_spectrum", params)
                elif sub_mode == 2:
                    dim = 32
                    sector = 9 + (self._seq % 7)
                    params = {"dimension": dim, "sector": sector}
                    if self._is_duplicate("GRAPH_INVARIANT", "biregular_sector_exact_degrees", params):
                        continue
                    candidate = CandidateHypothesis(
                        id=f"DYN-GRAPH-{self._seq:05d}",
                        statement=f"Biregular sector {sector} of {dim}D zero-divisor graph has exact degrees {{8, 24}}.",
                        category="SpectralGraphTheory",
                        conjecture_type="GRAPH_INVARIANT",
                        predicate="biregular_sector_exact_degrees",
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )
                    self._mark_seen("GRAPH_INVARIANT", "biregular_sector_exact_degrees", params)
                else:
                    prop_idx = self._seq % len(self._graph_properties)
                    prop = self._graph_properties[prop_idx]
                    if self.quantum_engine is not None:
                        try:
                            q_res = self.quantum_engine.project_quantum_collapse()
                            sector = q_res.collapse_sector
                            self.last_quantum_collapse = q_res
                        except Exception:
                            sector = (self._seq % 7) + 1
                    else:
                        sector = (self._seq % 7) + 1
                    dim_choices = [16, 32]
                    dim = dim_choices[self._seq % len(dim_choices)]
                    max_sec = self._max_sector.get(dim, dim // 2 - 1)
                    sector = max(1, min(sector, max_sec))
                    params = {"dimension": dim, "sector": sector}
                    if self._is_duplicate("GRAPH_INVARIANT", prop, params):
                        continue
                    q_meta: dict[str, Any] = {}
                    if self.last_quantum_collapse is not None:
                        q_meta = {
                            "quantum_sector": self.last_quantum_collapse.collapse_sector,
                            "quantum_syndrome": self.last_quantum_collapse.syndrome_int,
                            "quantum_entropy_delta": self.last_quantum_collapse.entropy_delta,
                            "physical_entropy": self.last_quantum_collapse.source_info.get("physical", False),
                        }
                    candidate = CandidateHypothesis(
                        id=f"DYN-GRAPH-{self._seq:05d}",
                        statement=f"Dynamic topological conjecture: Sector {sector} of {dim}D zero-divisor graph satisfies '{prop}'.",
                        category="SpectralGraphTheory",
                        conjecture_type="GRAPH_INVARIANT",
                        predicate=prop,
                        parameters={**params, **q_meta},
                        expected_relation={"op": "==", "val": True},
                    )
                    self._mark_seen("GRAPH_INVARIANT", prop, params)

            elif modality == "CODE_INVARIANT":
                prop_idx = self._seq % len(self._code_properties)
                prop = self._code_properties[prop_idx]
                if self.quantum_engine is not None:
                    try:
                        q_res = self.quantum_engine.project_quantum_collapse()
                        sector = q_res.collapse_sector
                        self.last_quantum_collapse = q_res
                    except Exception:
                        sector = (self._seq % 7) + 1
                else:
                    sector = (self._seq % 7) + 1
                params = {"dimension": 16, "sector": sector}
                if self._is_duplicate("CODE_INVARIANT", prop, params):
                    continue
                q_meta = {}
                if self.last_quantum_collapse is not None:
                    q_meta = {
                        "quantum_sector": self.last_quantum_collapse.collapse_sector,
                        "quantum_syndrome": self.last_quantum_collapse.syndrome_int,
                        "quantum_entropy_delta": self.last_quantum_collapse.entropy_delta,
                        "physical_entropy": self.last_quantum_collapse.source_info.get("physical", False),
                    }
                candidate = CandidateHypothesis(
                    id=f"DYN-QEC-{self._seq:05d}",
                    statement=f"Dynamic quantum code conjecture: Sector {sector} code satisfies '{prop}'.",
                    category="QuantumCodingTheory",
                    conjecture_type="CODE_INVARIANT",
                    predicate=prop,
                    parameters={**params, **q_meta},
                    expected_relation={"op": "==", "val": True},
                )
                self._mark_seen("CODE_INVARIANT", prop, params)

            elif modality == "SCALING_LAW":
                scale_preds: list[tuple[str, dict[str, Any]]] = [
                    ("associating_triples_count", {"dimensions": [8, 16, 32]}),
                    ("triangular_zero_divisor_count", {"dimensions": [16, 32, 64]}),
                    ("topological_entropy_additivity", {}),
                    ("nicomachus_block_cube", {"max_k": 5 + (self._seq % 6)}),
                    ("triangular_square_difference", {"max_k": 5 + (self._seq % 6)}),
                ]
                pred, params = scale_preds[self._seq % len(scale_preds)]
                if self._is_duplicate("SCALING_LAW", pred, params):
                    continue
                candidate = CandidateHypothesis(
                    id=f"DYN-SCALE-{self._seq:05d}",
                    statement=f"Dynamic scaling conjecture: Invariant '{pred}' holds.",
                    category="ScalingInvariants",
                    conjecture_type="SCALING_LAW",
                    predicate=pred,
                    parameters=params,
                    expected_relation={"op": "==", "val": True},
                )
                self._mark_seen("SCALING_LAW", pred, params)

            elif modality == "SMT_CONSTRAINT":
                smt_preds: list[tuple[str, dict[str, Any]]] = [
                    ("zero_xor_distinct_indices", {"bit_width": 3}),
                    ("odd_cycle_in_bipartite", {"cycle_length": 3}),
                    ("ramanujan_optimality_slack", {"d": 8, "lambda": 4}),
                    ("projective_stratification_identity", {}),
                ]
                pred, params = smt_preds[self._seq % len(smt_preds)]
                if self._is_duplicate("SMT_CONSTRAINT", pred, params):
                    continue
                candidate = CandidateHypothesis(
                    id=f"DYN-SMT-{self._seq:05d}",
                    statement=f"Dynamic SMT refutation probe: Invariant '{pred}'.",
                    category="SMTRefutation",
                    conjecture_type="SMT_CONSTRAINT",
                    predicate=pred,
                    parameters=params,
                    expected_relation={"op": "==", "val": "UNSAT"},
                )
                self._mark_seen("SMT_CONSTRAINT", pred, params)

            elif modality == "LEAN4_THEOREM":
                lean_preds: list[tuple[str, dict[str, Any]]] = [
                    ("assocNeg_shift_left", {"i": 1, "j": 2, "k": 3}),
                    ("assocNeg_shift_right", {"i": 1, "j": 2, "k": 3}),
                    ("assocNeg_shift_span", {"i": 1, "j": 2, "k": 3, "s": 1}),
                    ("triangular_factorization", {"k": 6}),
                    ("ramanujan_bound", {"degree": 8, "lambda_1": 4}),
                    ("xor_exchange", {"i": 1, "j": 2, "k": 4, "m": 7}),
                    (
                        "sedenion_annihilation",
                        {
                            "i1": 1,
                            "j1": 2,
                            "s1": 1,
                            "s2": 1,
                            "i2": 4,
                            "j2": 7,
                            "t1": 1,
                            "t2": -1,
                        },
                    ),
                    ("autonomous_sedenion_zd_count", {}),
                    ("autonomous_ramanujan_slack", {}),
                    ("autonomous_entropy_degree_decomposition", {}),
                    ("autonomous_no_odd_triangle", {}),
                    ("autonomous_xor_distinct_nonzero", {"i": 3, "j": 5}),
                    ("autonomous_projective_identity", {"P": 7}),
                    ("index_criterion_general", {}),
                    ("crossSign_eq_assocNeg", {}),
                    ("basis_flexible", {}),
                ]
                pred, params = lean_preds[self._seq % len(lean_preds)]
                if self._is_duplicate("LEAN4_THEOREM", pred, params):
                    continue
                candidate = CandidateHypothesis(
                    id=f"DYN-LEAN-{self._seq:05d}",
                    statement=f"Dynamic Lean 4 theorem: '{pred}' holds in formal kernel.",
                    category="FormalVerification",
                    conjecture_type="LEAN4_THEOREM",
                    predicate=pred,
                    parameters=params,
                    expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
                )
                self._mark_seen("LEAN4_THEOREM", pred, params)

            elif modality == "TOWER_ORGANISM":
                org_probes = self.generate_organism_conjectures()
                for probe in org_probes:
                    if not self._is_duplicate(probe.conjecture_type, probe.predicate, probe.parameters):
                        self._mark_seen(probe.conjecture_type, probe.predicate, probe.parameters)
                        candidate = probe
                        break

            elif modality == "MODULAR_HECKE":
                hecke_probes = self.generate_modular_hecke_conjectures()
                for probe in hecke_probes:
                    if not self._is_duplicate(probe.conjecture_type, probe.predicate, probe.parameters):
                        self._mark_seen(probe.conjecture_type, probe.predicate, probe.parameters)
                        candidate = probe
                        break

            if candidate is not None:
                return candidate

        # Open Frontier Exploration: Multi-domain structural generator replacing linear integer scan
        return self._generate_frontier_structural_hypothesis()

    def _generate_frontier_structural_hypothesis(self) -> CandidateHypothesis:
        """
        Synthesizes the next candidate from open structural mathematical frontiers.
        Replaces the naive sequential integer scan with a balanced, multi-modal generator
        exploring across 7 rich mathematical domains:
        1. Higher-Tower Cayley-Dickson Graph & Annihilation Spectra (D in {16, 32, 64, 128, 256})
        2. Non-Associative Coset Shifting (D in {16, 32, 64}, 1 <= i < j < D)
        3. Stiefel 2-Frame Holonomy & Curvature (D in {16, 32, 64, 128})
        4. Projective Pencil Fibration Geometry (D in {16, 32, 64})
        5. Tower Scaling Laws & Volume Invariants (D in {16, 32, 64, 128, 256})
        6. Formal Lean 4 Inductive Kernel Invariants
        7. Non-Sequential Structured Arithmetic Invariants (Mersenne, Fermat, Tower Boundaries)
        """
        max_attempts = 300
        for _ in range(max_attempts):
            self._seq += 1
            domain_idx = self._seq % 7

            if domain_idx == 0:
                # 1. Higher-Tower Cayley-Dickson Graph & Annihilation Spectra
                dims = [16, 32, 64, 128, 256]
                d = dims[(self._seq // 7) % len(dims)]
                max_sec = self._max_sector.get(d, max(1, d // 2 - 1))
                sec = ((self._seq * 3) % max_sec) + 1
                graph_preds = [
                    "regular_charge_sector_classification",
                    "biregular_sector_exact_degrees",
                    "biregular_sector_edge_count",
                    "bipartite",
                    "ramanujan_bound",
                ]
                pred = graph_preds[(self._seq // (7 * len(dims))) % len(graph_preds)]
                params = {"dimension": d, "sector": sec}
                if not self._is_duplicate("GRAPH_INVARIANT", pred, params):
                    self._mark_seen("GRAPH_INVARIANT", pred, params)
                    return CandidateHypothesis(
                        id=f"FRONTIER-GRAPH-{self._seq:05d}",
                        statement=f"Sector {sec} of {d}D Cayley-Dickson annihilation graph satisfies spectral property '{pred}'.",
                        category="SpectralGraphTheory",
                        conjecture_type="GRAPH_INVARIANT",
                        predicate=pred,
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )

            elif domain_idx == 1:
                # 2. Non-Associative Coset Shifting
                dims = [16, 32, 64]
                d = dims[(self._seq // 7) % len(dims)]
                max_i = min(d - 1, 31)
                i = (self._seq % (max_i - 1)) + 1
                j = (((self._seq * 5) % (max_i - 1)) + 1)
                if i == j:
                    j = (i % (max_i - 1)) + 1
                params = {"dimension": d, "i": min(i, j), "j": max(i, j)}
                if not self._is_duplicate("ALGEBRAIC_IDENTITY", "associator_coset_shift", params):
                    self._mark_seen("ALGEBRAIC_IDENTITY", "associator_coset_shift", params)
                    return CandidateHypothesis(
                        id=f"FRONTIER-COSET-{self._seq:05d}",
                        statement=f"In dimension {d}, associator sign map k -> omega({params['i']}, k, {params['j']}) is invariant under translation by span({params['i']}, {params['j']}).",
                        category="CayleyDicksonAssociator",
                        conjecture_type="ALGEBRAIC_IDENTITY",
                        predicate="associator_coset_shift",
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )

            elif domain_idx == 2:
                # 3. Stiefel 2-Frame Holonomy & Curvature
                dims = [16, 32, 64, 128]
                d = dims[(self._seq // 7) % len(dims)]
                stiefel_preds = ["stiefel_frame_census", "stiefel_angle_trichotomy", "coplanar_bipartite_split", "octad_gram_spectrum"]
                pred = stiefel_preds[(self._seq // 14) % len(stiefel_preds)]
                if pred in ("coplanar_bipartite_split", "octad_gram_spectrum"):
                    params = {"dimension": 16, "plane_idx": (self._seq % 21) + 1, "component": (self._seq % 7) + 1}
                    c_type = "FRAME_FIELD_INVARIANT"
                    cat = "FrameFieldGeometry"
                else:
                    params = {"dimension": d}
                    c_type = "STIEFEL_INVARIANT"
                    cat = "StiefelManifold"
                if not self._is_duplicate(c_type, pred, params):
                    self._mark_seen(c_type, pred, params)
                    return CandidateHypothesis(
                        id=f"FRONTIER-STIEFEL-{self._seq:05d}",
                        statement=f"In dimension {d}, Stiefel 2-frame bundle satisfies geometric invariant '{pred}'.",
                        category=cat,
                        conjecture_type=c_type,
                        predicate=pred,
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )

            elif domain_idx == 3:
                # 4. Projective Pencil Fibration Geometry
                pencil_preds = ["pencil_cardinality", "sector_vertex_order_formula", "pencil_plane_partition", "projective_line_triality"]
                pred = pencil_preds[(self._seq // 14) % len(pencil_preds)]
                d = [16, 32, 64][(self._seq // 7) % 3]
                sec = (self._seq % 15) + 1
                params = {"dimension": d, "sector": sec, "line_a": 1, "line_b": (self._seq % 14) + 2}
                if not self._is_duplicate("PROJECTIVE_PENCIL_FIBRATION", pred, params):
                    self._mark_seen("PROJECTIVE_PENCIL_FIBRATION", pred, params)
                    return CandidateHypothesis(
                        id=f"FRONTIER-PENCIL-{self._seq:05d}",
                        statement=f"Projective pencil in {d}D satisfies fibration invariant '{pred}'.",
                        category="ProjectiveGeometry",
                        conjecture_type="PROJECTIVE_PENCIL_FIBRATION",
                        predicate=pred,
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )

            elif domain_idx == 4:
                # 5. Tower Scaling Laws & Volume
                scaling_preds = ["triangular_zero_divisor_count", "topological_entropy_additivity", "nicomachus_block_cube", "associating_triples_count"]
                pred = scaling_preds[(self._seq // 14) % len(scaling_preds)]
                k = (self._seq % 10) + 4
                params = {"dimensions": [16, 32, 64], "max_k": k}
                if not self._is_duplicate("SCALING_LAW", pred, params):
                    self._mark_seen("SCALING_LAW", pred, params)
                    return CandidateHypothesis(
                        id=f"FRONTIER-SCALE-{self._seq:05d}",
                        statement=f"Universal Cayley-Dickson tower satisfies scaling law '{pred}' at parameter k={k}.",
                        category="ScalingInvariants",
                        conjecture_type="SCALING_LAW",
                        predicate=pred,
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )

            elif domain_idx == 5:
                # 6. Formal Lean 4 Inductive Kernel Invariants
                lean_preds = [
                    ("assocNeg_shift_span", {"i": (self._seq % 7) + 1, "j": ((self._seq * 2) % 7) + 1, "k": ((self._seq * 3) % 7) + 1, "s": (self._seq % 3) + 1}),
                    ("triangular_factorization", {"k": [6, 14, 30, 62, 126][(self._seq // 7) % 5]}),
                    ("biregular_handshake", {"dimension": [32, 64, 128][(self._seq // 7) % 3]}),
                    ("chargeSector_regular_iff", {"dimension": [32, 64][(self._seq // 7) % 2], "charge": (self._seq % 15) + 1}),
                    ("regularSectorCharges_card", {"dimension": [32, 64, 128][(self._seq // 7) % 3]}),
                ]
                pred, params = lean_preds[self._seq % len(lean_preds)]
                if not self._is_duplicate("LEAN4_THEOREM", pred, params):
                    self._mark_seen("LEAN4_THEOREM", pred, params)
                    return CandidateHypothesis(
                        id=f"FRONTIER-LEAN-{self._seq:05d}",
                        statement=f"Inductive formal Lean 4 kernel invariant: '{pred}' holds.",
                        category="FormalVerification",
                        conjecture_type="LEAN4_THEOREM",
                        predicate=pred,
                        parameters=params,
                        expected_relation={"op": "==", "val": "KERNEL_CERTIFIED"},
                    )

            elif domain_idx == 6:
                # 7. Non-Sequential Structured Arithmetic Invariants (Sparse Frontiers)
                structured_targets = [
                    # Mersenne candidates
                    3, 7, 31, 127, 2047, 8191,
                    # Fermat candidates
                    5, 17, 257, 65537,
                    # Tower boundary candidates
                    15, 17, 31, 33, 63, 65, 127, 129, 255, 257, 511, 513, 1023, 1025,
                    # Sophie Germain & Ramanujan points
                    23, 29, 41, 53, 83, 89, 113, 131, 173, 179, 191, 233, 239, 251,
                    # Carmichael pseudoprimes for falsification boundaries
                    561, 1105, 1729, 2465, 2821,
                ]
                n_target = structured_targets[self._seq % len(structured_targets)]
                pred = "prime_ground_state" if self._seq % 2 == 0 else "e8_prime_excess"
                params = {"n": n_target}
                if not self._is_duplicate("TOWER_ORGANISM", pred, params):
                    self._mark_seen("TOWER_ORGANISM", pred, params)
                    desc = "arithmetic organism ground state curvature" if pred == "prime_ground_state" else "E8 root lattice cubic excess vanishing"
                    return CandidateHypothesis(
                        id=f"FRONTIER-PRIME-{self._seq:05d}",
                        statement=f"Structured arithmetic candidate n={n_target} satisfies {desc} invariant.",
                        category="NumberTheory",
                        conjecture_type="TOWER_ORGANISM",
                        predicate=pred,
                        parameters=params,
                        expected_relation={"op": "==", "val": True},
                    )

        # Ultimate fallback: expand dimensions on algebraic associativity
        dim = [64, 128, 256][self._seq % 3]
        return CandidateHypothesis(
            id=f"FRONTIER-CD-{self._seq:05d}",
            statement=f"In dimension {dim}, algebraic property 'alternating_associator' holds.",
            category="CayleyDicksonAssociator",
            conjecture_type="ALGEBRAIC_IDENTITY",
            predicate="alternating_associator",
            parameters={"dimension": dim},
            expected_relation={"op": "==", "val": True},
        )
