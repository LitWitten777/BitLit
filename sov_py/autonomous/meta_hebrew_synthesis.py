"""
Quantized Hebrew Word Synthesis Engine for Autonomous Reasoning Feedback Loops.

Generates Hebrew words dynamically from:
1. Algebraic invariants (associator patterns, zero-divisor structures)
2. Topological features (Betti numbers, persistence diagrams)
3. Proof states (verified/falsified predicates)
4. Semantic feedback (negative feedback history, manifold stability mode)

Implements bidirectional mapping:
- Mathematical Structure → Hebrew Word (gematria encoding)
- Hebrew Word → Mathematical Constraints (semantic guidance)
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

import numpy as np

from ..grammar.hopf_braid_bridge import (
    HebrewLetter, HebrewWord,
    ArabicLetter, ArabicWord,
    SanskritLetter, SanskritWord,
)


@dataclass
class SemanticSignature:
    """Mathematical fingerprint for word generation."""
    
    algebraic_type: str  # "associator", "zero_divisor", "centralizer"
    dimension: int       # Cayley-Dickson dimension (2, 4, 8, 16, ...)
    invariant_value: float  # Numerical invariant (norm, eigenvalue, etc.)
    topological_features: Dict[str, Any] = field(default_factory=dict)
    proof_status: str = "OPEN"  # "OPEN", "VERIFIED", "FALSIFIED"
    
    def to_gematria_seed(self) -> int:
        """Convert mathematical signature to gematria seed value."""
        # Hash the signature to get deterministic seed
        sig_str = f"{self.algebraic_type}:{self.dimension}:{self.invariant_value:.6f}"
        hash_bytes = hashlib.sha256(sig_str.encode()).digest()
        seed = int.from_bytes(hash_bytes[:4], 'big')
        
        # Modulo by max gematria sum (22 letters × 400 max value = 8800)
        return seed % 8800
    
    def determine_word_length(self) -> int:
        """Determine optimal word length from topological features."""
        betti_1 = self.topological_features.get('betti_1', 1)
        persistence = self.topological_features.get('max_persistence', 0.5)
        
        # Higher Betti numbers → longer words (more semantic complexity)
        if betti_1 >= 3:
            return min(8, max(3, int(3 + persistence * 5)))
        elif betti_1 >= 2:
            return min(6, max(2, int(2 + persistence * 4)))
        else:
            return min(4, max(2, int(2 + persistence * 3)))


class HebrewWordSynthesizer:
    """
    Dynamic Hebrew word generator for autonomous reasoning feedback loops.
    
    Usage:
        synthesizer = HebrewWordSynthesizer()
        
        # Generate word from mathematical signature
        sig = SemanticSignature(
            algebraic_type="associator",
            dimension=32,
            invariant_value=0.707,
            topological_features={"betti_1": 2, "max_persistence": 0.6},
            proof_status="VERIFIED"
        )
        word = synthesizer.generate_word(sig, context="theorem_naming")
        
        # Get semantic guidance from word
        constraints = synthesizer.word_to_constraints(word)
    """
    
    def __init__(self):
        self.letter_weights: Dict[HebrewLetter, float] = self._initialize_letter_weights()
        self.semantic_categories: Dict[str, List[HebrewLetter]] = {
            "algebraic": [HebrewLetter.ALEPH, HebrewLetter.MEM, HebrewLetter.TAV, 
                         HebrewLetter.QOF, HebrewLetter.SHIN],
            "topological": [HebrewLetter.GIMEL, HebrewLetter.LAMED, HebrewLetter.AYIN,
                           HebrewLetter.PE, HebrewLetter.TSADI],
            "logical": [HebrewLetter.BET, HebrewLetter.DALET, HebrewLetter.YOD,
                       HebrewLetter.KAF, HebrewLetter.RESH],
            "physical": [HebrewLetter.HE, HebrewLetter.VAV, HebrewLetter.ZAYIN,
                        HebrewLetter.HET, HebrewLetter.TET],
            "unifying": [HebrewLetter.NUN, HebrewLetter.SAMEKH]
        }
        self.generated_words: List[HebrewWord] = []
        self.word_usage_count: Dict[str, int] = {}
    
    def _initialize_letter_weights(self) -> Dict[HebrewLetter, float]:
        """Initialize letter weights based on traditional significance."""
        weights = {}
        for letter in HebrewLetter:
            # Base weight inversely proportional to gematria value
            base_weight = 1.0 / np.sqrt(letter.value)
            
            # Boost for first/middle/last letters of alphabet
            if letter in [HebrewLetter.ALEPH, HebrewLetter.MEM, HebrewLetter.TAV]:
                base_weight *= 1.5  # Aleph-Mem-Tav (EMET = Truth)
            
            weights[letter] = base_weight
        
        return weights
    
    def _select_category(self, signature: SemanticSignature) -> str:
        """Select semantic category based on algebraic type."""
        type_to_category = {
            "associator": "algebraic",
            "zero_divisor": "algebraic",
            "centralizer": "algebraic",
            "power_associativity": "algebraic",
            "bipartite": "topological",
            "ramanujan_bound": "topological",
            "spectral_gap": "topological",
            "css_commutativity": "logical",
            "doubly_even": "logical",
            "enstrophy": "physical",
            "reynolds_number": "physical",
            "cascade_exponent": "physical",
        }
        
        return type_to_category.get(signature.algebraic_type, "algebraic")
    
    def _compute_letter_probabilities(
        self, 
        category: str, 
        target_sum: int,
        word_length: int
    ) -> List[Tuple[HebrewLetter, float]]:
        """Compute probability distribution over letters for given constraints."""
        candidates = self.semantic_categories.get(category, self.semantic_categories["algebraic"])
        
        # Weight by closeness to target average
        avg_target = target_sum / word_length if word_length > 0 else 100
        
        weighted_candidates = []
        for letter in candidates:
            # Combine base weight with target proximity
            base_w = self.letter_weights[letter]
            proximity = np.exp(-abs(letter.value - avg_target) / 100.0)
            combined_weight = base_w * proximity
            
            # Boost for proof status
            if letter == HebrewLetter.ALEPH and target_sum % 11 == 0:
                combined_weight *= 2.0  # Aleph for master numbers
            
            weighted_candidates.append((letter, combined_weight))
        
        # Normalize probabilities
        total = sum(w for _, w in weighted_candidates)
        normalized = [(letter, w / total) for letter, w in weighted_candidates]
        
        return normalized
    
    def generate_word(
        self,
        signature: SemanticSignature,
        context: str = "theorem_naming",
        transliteration_hint: Optional[str] = None,
        include_opposite: bool = True
    ) -> Tuple[HebrewWord, Optional[HebrewWord]]:
        """
        Generate Hebrew word from mathematical signature.
        
        Args:
            signature: Mathematical fingerprint
            context: Usage context ("theorem_naming", "semantic_bridge", "constraint_encoding")
            transliteration_hint: Optional hint for transliteration
            include_opposite: If True, also generate the opposite word (default: True)
        
        Returns:
            Tuple of (primary_word, opposite_word) if include_opposite else (word, None)
        """
        # Step 1: Determine target gematria sum
        seed_sum = signature.to_gematria_seed()
        
        # Adjust based on proof status
        if signature.proof_status == "VERIFIED":
            # Verified theorems get "master number" sums (11, 22, 33, or squares)
            master_numbers = [11, 22, 33, 121, 144, 441, 484]
            target_sum = min(master_numbers, key=lambda x: abs(x - seed_sum % 500))
        elif signature.proof_status == "FALSIFIED":
            # Falsified conjectures get prime sums
            primes = [17, 19, 23, 29, 31, 37, 41, 43, 47, 53]
            target_sum = min(primes, key=lambda x: abs(x - seed_sum % 60))
        else:
            target_sum = seed_sum % 500 + 50  # Open problems: moderate range
        
        # Step 2: Determine word length from topology
        word_length = signature.determine_word_length()
        
        # Step 3: Select semantic category
        category = self._select_category(signature)
        
        # Step 4: Greedy letter selection to match target sum
        letters = []
        remaining_sum = target_sum
        probs = self._compute_letter_probabilities(category, target_sum, word_length)
        
        for i in range(word_length - 1):
            if not probs:
                break
            
            # Select letter probabilistically
            rng = np.random.default_rng(seed=seed_sum + i)
            selected = rng.choice(len(probs), p=[p for _, p in probs])
            letter = probs[selected][0]
            
            # Ensure we don't overshoot
            if letter.value < remaining_sum - (word_length - i - 1):
                letters.append(letter)
                remaining_sum -= letter.value
        
        # Fill last letter to match target as closely as possible
        if letters and remaining_sum > 0:
            # Find closest matching letter
            best_letter = min(HebrewLetter, key=lambda l: abs(l.value - remaining_sum))
            letters.append(best_letter)
        elif not letters:
            # Fallback: use Aleph
            letters = [HebrewLetter.ALEPH] * min(3, word_length)
        
        # Step 5: Create primary HebrewWord
        transliteration = transliteration_hint or f"Q{signature.dimension}_{signature.algebraic_type[:4]}"
        meaning = f"{category.title()} invariant (D={signature.dimension}, {signature.proof_status})"
        
        primary_word = HebrewWord(
            letters=letters,
            transliteration=transliteration,
            meaning=meaning
        )
        
        # Step 6: Generate opposite word if requested
        opposite_word = None
        if include_opposite:
            opposite_word = self._generate_opposite_word(primary_word, signature)
        
        # Track usage
        self.generated_words.append(primary_word)
        key = "".join(l.name for l in letters)
        self.word_usage_count[key] = self.word_usage_count.get(key, 0) + 1
        
        return (primary_word, opposite_word)
    
    def _generate_opposite_word(self, word: HebrewWord, signature: SemanticSignature) -> HebrewWord:
        """
        Generate the opposite/complement word for semantic balance.
        
        Opposites are constructed by:
        1. Reversing letter order (temporal inversion)
        2. Using complementary gematria (9's complement mod 22)
        3. Inverting semantic polarity (verified↔falsified, stable↔unstable)
        """
        # Method 1: Reverse letter sequence
        reversed_letters = list(reversed(word.letters))
        
        # Method 2: Complement each letter (22-letter alphabet symmetry)
        # Map: Aleph(1)↔Tav(400), Bet(2)↔Shin(300), etc.
        complement_map = {
            HebrewLetter.ALEPH: HebrewLetter.TAV,
            HebrewLetter.BET: HebrewLetter.SHIN,
            HebrewLetter.GIMEL: HebrewLetter.RESH,
            HebrewLetter.DALET: HebrewLetter.QOF,
            HebrewLetter.HE: HebrewLetter.PE,
            HebrewLetter.VAV: HebrewLetter.AYIN,
            HebrewLetter.ZAYIN: HebrewLetter.SAMEKH,
            HebrewLetter.HET: HebrewLetter.NUN,
            HebrewLetter.TET: HebrewLetter.MEM,
            HebrewLetter.YOD: HebrewLetter.LAMED,
            HebrewLetter.KAF: HebrewLetter.KAF,  # Self-complementary (center)
            HebrewLetter.LAMED: HebrewLetter.YOD,
            HebrewLetter.MEM: HebrewLetter.TET,
            HebrewLetter.NUN: HebrewLetter.HET,
            HebrewLetter.SAMEKH: HebrewLetter.ZAYIN,
            HebrewLetter.AYIN: HebrewLetter.VAV,
            HebrewLetter.PE: HebrewLetter.HE,
            HebrewLetter.TSADI: HebrewLetter.TSADI,  # Self-complementary
            HebrewLetter.QOF: HebrewLetter.DALET,
            HebrewLetter.RESH: HebrewLetter.GIMEL,
            HebrewLetter.SHIN: HebrewLetter.BET,
            HebrewLetter.TAV: HebrewLetter.ALEPH,
        }
        
        complement_letters = [complement_map[l] for l in word.letters]
        
        # Method 3: Invert proof status for semantic opposition
        status_inversion = {
            "VERIFIED": "FALSIFIED",
            "FALSIFIED": "VERIFIED", 
            "OPEN": "OPEN"
        }
        inverted_status = status_inversion.get(signature.proof_status, "OPEN")
        
        # Create opposite signature with inverted status
        opposite_sig = SemanticSignature(
            algebraic_type=signature.algebraic_type,
            dimension=signature.dimension,
            invariant_value=-signature.invariant_value,  # Negate invariant
            topological_features=signature.topological_features,
            proof_status=inverted_status
        )
        
        # Generate opposite word with complement letters
        opp_transliteration = f"{word.transliteration}_OPP"
        opp_meaning = f"Opposite: {word.meaning} [{inverted_status}]"
        
        opposite_word = HebrewWord(
            letters=complement_letters,
            transliteration=opp_transliteration,
            meaning=opp_meaning
        )
        
        # Track opposite word usage
        self.generated_words.append(opposite_word)
        opp_key = "".join(l.name for l in complement_letters)
        self.word_usage_count[opp_key] = self.word_usage_count.get(opp_key, 0) + 1
        
        return opposite_word
    
    def word_to_constraints(self, word: HebrewWord) -> Dict[str, Any]:
        """
        Decode Hebrew word back to mathematical constraints.
        
        This enables bidirectional reasoning:
        - Word gematria → numerical bounds
        - Letter sequence → structural constraints
        - Reduced value → symmetry class
        """
        constraints = {
            "gematria_bound": word.gematria_value,
            "digital_root": word.reduced_value,
            "structural_dim": len(word.letters),
            "algebraic_type": word.algebraic_structure,
        }
        
        # Extract constraints from letter pattern
        letter_values = [l.value for l in word.letters]
        
        # Parity pattern → symmetry constraint
        parities = [v % 2 for v in letter_values]
        constraints["symmetry_pattern"] = "even" if all(p == 0 for p in parities) else "mixed"
        
        # Monotonicity → ordering constraint
        is_increasing = all(letter_values[i] <= letter_values[i+1] for i in range(len(letter_values)-1))
        constraints["ordering"] = "increasing" if is_increasing else "unordered"
        
        # Check for special patterns
        if word.reduced_value in [11, 22, 33]:
            constraints["special_class"] = "master_number"
            constraints["expected_stability"] = "high"
        elif word.gematria_value in [441, 913]:  # EMET, BERESHIT
            constraints["canonical_reference"] = True
        
        return constraints
    
    def generate_with_opposite(
        self,
        signature: SemanticSignature,
        context: str = "theorem_naming"
    ) -> Dict[str, Any]:
        """
        Convenience method to generate word pair with full metadata.
        
        Args:
            signature: Mathematical fingerprint
            context: Usage context
            
        Returns:
            Dictionary with primary/opposite words, gematria values, and semantic relations
        """
        primary_word, opposite_word = self.generate_word(
            signature, 
            context=context,
            include_opposite=True
        )
        
        # Determine semantic relation type
        if signature.proof_status == "VERIFIED":
            relation = "Status Inversion: Primary is proven, opposite shows falsification path"
        elif signature.proof_status == "FALSIFIED":
            relation = "Counterexample Duality: Primary shows failure mode, opposite shows success condition"
        else:
            relation = "Exploratory Pair: Both words represent complementary search directions"
        
        return {
            "primary_word": str(primary_word),
            "primary_gematria": primary_word.gematria_value,
            "primary_reduced": primary_word.reduced_value,
            "primary_letters": [l.name for l in primary_word.letters],
            "opposite_word": str(opposite_word),
            "opposite_gematria": opposite_word.gematria_value,
            "opposite_reduced": opposite_word.reduced_value,
            "opposite_letters": [l.name for l in opposite_word.letters],
            "primary_status": signature.proof_status,
            "opposite_status": "FALSIFIED" if signature.proof_status == "VERIFIED" else 
                               "VERIFIED" if signature.proof_status == "FALSIFIED" else "OPEN",
            "semantic_relation": relation,
            "complement_mapping": self._get_complement_map_preview(primary_word.letters)
        }
    
    def _get_complement_map_preview(self, letters: List[HebrewLetter]) -> Dict[str, str]:
        """Show letter-to-complement mapping for transparency."""
        complement_map = {
            HebrewLetter.ALEPH: HebrewLetter.TAV,
            HebrewLetter.BET: HebrewLetter.SHIN,
            HebrewLetter.GIMEL: HebrewLetter.RESH,
            HebrewLetter.DALET: HebrewLetter.QOF,
            HebrewLetter.HE: HebrewLetter.PE,
            HebrewLetter.VAV: HebrewLetter.AYIN,
            HebrewLetter.ZAYIN: HebrewLetter.SAMEKH,
            HebrewLetter.HET: HebrewLetter.NUN,
            HebrewLetter.TET: HebrewLetter.MEM,
            HebrewLetter.YOD: HebrewLetter.LAMED,
            HebrewLetter.KAF: HebrewLetter.KAF,
            HebrewLetter.LAMED: HebrewLetter.YOD,
            HebrewLetter.MEM: HebrewLetter.TET,
            HebrewLetter.NUN: HebrewLetter.HET,
            HebrewLetter.SAMEKH: HebrewLetter.ZAYIN,
            HebrewLetter.AYIN: HebrewLetter.VAV,
            HebrewLetter.PE: HebrewLetter.HE,
            HebrewLetter.TSADI: HebrewLetter.TSADI,
            HebrewLetter.QOF: HebrewLetter.DALET,
            HebrewLetter.RESH: HebrewLetter.GIMEL,
            HebrewLetter.SHIN: HebrewLetter.BET,
            HebrewLetter.TAV: HebrewLetter.ALEPH,
        }
        return {f"{l.name}({l.value})": f"{complement_map[l].name}({complement_map[l].value})" 
                for l in letters[:5]}  # First 5 letters max for readability
    
    def generate_feedback_word(
        self,
        negative_feedback: List[str],
        topological_entropy: float,
        manifold_mode: str
    ) -> Tuple[HebrewWord, HebrewWord]:
        """
        Generate word specifically for steering reasoning based on feedback.
        
        Used in autonomous loop to encode learned constraints semantically.
        
        Returns:
            Tuple of (feedback_word, opposite_word)
        """
        # Encode feedback into signature
        feedback_hash = sum(hash(fb) for fb in negative_feedback[-5:]) % 1000
        
        signature = SemanticSignature(
            algebraic_type="feedback_synthesis",
            dimension=int(topological_entropy * 100),
            invariant_value=topological_entropy,
            topological_features={
                "entropy": topological_entropy,
                "mode": manifold_mode,
                "feedback_count": len(negative_feedback)
            },
            proof_status="VERIFIED" if manifold_mode == "MANIFOLD_STABLE" else "OPEN"
        )
        
        # Generate word with feedback-aware context
        context_hint = f"FB{len(negative_feedback)}_E{int(topological_entropy*100)}"
        return self.generate_word(signature, context="feedback_steering", transliteration_hint=context_hint)
    
    def compute_lexicon_diversity(self) -> float:
        """Measure diversity of generated lexicon (0=redundant, 1=diverse)."""
        if not self.generated_words:
            return 0.0
        
        unique_patterns = len(self.word_usage_count)
        total_words = len(self.generated_words)
        
        # Simpson diversity index adaptation
        if total_words <= 1:
            return 1.0
        
        diversity = unique_patterns / total_words
        return min(1.0, diversity)


def integrate_with_reasoning_loop(target=None):
    """
    Example integration with autonomous reasoning engine.
    
    This function demonstrates how to plug Hebrew word synthesis
    into the feedback loop in hypothesis_generator.py without circular imports.
    `target` can be a HypothesisGenerator class, an instance, or None.
    """
    import sys

    # Create synthesizer
    synthesizer = HebrewWordSynthesizer()

    if target is None:
        # Check if already imported without forcing a circular import
        mod = sys.modules.get("src.sedenion.autonomous.hypothesis_generator")
        if mod is not None and hasattr(mod, "HypothesisGenerator"):
            target = getattr(mod, "HypothesisGenerator")

    if target is not None:
        # Monkey-patch into hypothesis generator class or instance
        original_generate = getattr(target, "generate_next_hypothesis")

        def enhanced_generate(self_or_inst=None):
            # Call original generation
            if self_or_inst is not None and isinstance(target, type):
                hypothesis = original_generate(self_or_inst)
                ctx = self_or_inst
            elif not isinstance(target, type):
                hypothesis = original_generate()
                ctx = target
            else:
                hypothesis = original_generate(self_or_inst)
                ctx = self_or_inst

            # Create signature from hypothesis
            sig = SemanticSignature(
                algebraic_type=hypothesis.conjecture_type,
                dimension=hypothesis.parameters.get('dimension', 16),
                invariant_value=0.5,  # Default, would compute from spectral data
                topological_features={
                    'betti_1': getattr(ctx, 'betti_1', 1),
                    'max_persistence': getattr(ctx, 'max_persistence', 0.5)
                },
                proof_status="OPEN"
            )

            # Generate semantic word for this hypothesis
            word = synthesizer.generate_word(sig, context="hypothesis_labeling")

            # Attach word to hypothesis for downstream use
            hypothesis.semantic_label = word

            return hypothesis

        setattr(target, "generate_next_hypothesis", enhanced_generate)


class ArabicWordSynthesizer:
    """
    Dynamic Arabic word generator for autonomous reasoning feedback loops.
    Uses Hisab al-Jummal valuation (1 to 1000) and C(8, 2) = 28 D8 lattice pairs.
    """

    def __init__(self):
        self.semantic_categories: Dict[str, List[ArabicLetter]] = {
            "algebraic": [ArabicLetter.ALIF, ArabicLetter.BA, ArabicLetter.JIM, ArabicLetter.DAL, ArabicLetter.KAF],
            "topological": [ArabicLetter.LAM, ArabicLetter.MIM, ArabicLetter.NUN, ArabicLetter.RA, ArabicLetter.WAW],
            "logical": [ArabicLetter.SIN, ArabicLetter.SHIN, ArabicLetter.SAD, ArabicLetter.DAD, ArabicLetter.QAF],
            "physical": [ArabicLetter.HA_FIVE, ArabicLetter.HHA, ArabicLetter.AYN, ArabicLetter.GHAYN, ArabicLetter.FA],
            "unifying": [ArabicLetter.YA, ArabicLetter.TA, ArabicLetter.ZAY],
        }

    def generate_word(self, signature: SemanticSignature, context: str = "theorem_naming") -> ArabicWord:
        """Generate quantized Arabic word from mathematical signature."""
        category = "algebraic"
        if signature.algebraic_type in ("bipartite", "ramanujan_bound", "spectral_gap"):
            category = "topological"
        elif signature.algebraic_type in ("css_commutativity", "doubly_even"):
            category = "logical"
        elif signature.algebraic_type in ("enstrophy", "reynolds_number", "cascade_exponent"):
            category = "physical"

        candidates = self.semantic_categories.get(category, self.semantic_categories["algebraic"])
        word_len = max(2, min(5, signature.determine_word_length()))
        seed = signature.to_gematria_seed()

        selected_letters: List[ArabicLetter] = []
        for i in range(word_len):
            idx = (seed + i * 7) % len(candidates)
            selected_letters.append(candidates[idx])

        transliteration = "".join(l.name.capitalize() for l in selected_letters)
        meaning = f"Arabic {category.capitalize()} Invariant ({signature.proof_status})"

        return ArabicWord(
            letters=selected_letters,
            transliteration=transliteration,
            meaning=meaning,
        )

    def word_to_constraints(self, word: ArabicWord) -> Dict[str, Any]:
        """Map Arabic word Jummal value to mathematical constraints."""
        val = word.jummal_value
        return {
            "suggested_dimension": 16 if val % 2 == 0 else 32,
            "spectral_gap_bound": (val % 100) / 100.0,
            "charge_parity": val % 7 + 1,
            "quaternion_vector": word.to_quaternion().tolist(),
        }


class SanskritWordSynthesizer:
    """
    Dynamic Sanskrit word generator for autonomous reasoning feedback loops.
    Uses Katapayadi decimal numbering and 49 Nicomachus aksharas.
    """

    def __init__(self):
        self.semantic_categories: Dict[str, List[SanskritLetter]] = {
            "algebraic": [SanskritLetter.KA, SanskritLetter.KHA, SanskritLetter.GA, SanskritLetter.GHA, SanskritLetter.NGA],
            "topological": [SanskritLetter.PA, SanskritLetter.PHA, SanskritLetter.BA, SanskritLetter.BHA, SanskritLetter.MA],
            "logical": [SanskritLetter.CA, SanskritLetter.CHA, SanskritLetter.JA, SanskritLetter.JHA, SanskritLetter.NYA],
            "physical": [SanskritLetter.TTA, SanskritLetter.TTHA, SanskritLetter.DDA, SanskritLetter.DDHA, SanskritLetter.NNA],
            "unifying": [SanskritLetter.YA, SanskritLetter.RA, SanskritLetter.LA, SanskritLetter.VA, SanskritLetter.HA],
        }

    def generate_word(self, signature: SemanticSignature, context: str = "theorem_naming") -> SanskritWord:
        """Generate quantized Sanskrit word from mathematical signature."""
        category = "algebraic"
        if signature.algebraic_type in ("bipartite", "ramanujan_bound", "spectral_gap"):
            category = "topological"
        elif signature.algebraic_type in ("css_commutativity", "doubly_even"):
            category = "logical"
        elif signature.algebraic_type in ("enstrophy", "reynolds_number", "cascade_exponent"):
            category = "physical"

        candidates = self.semantic_categories.get(category, self.semantic_categories["algebraic"])
        word_len = max(2, min(5, signature.determine_word_length()))
        seed = signature.to_gematria_seed()

        selected_letters: List[SanskritLetter] = []
        for i in range(word_len):
            idx = (seed + i * 5) % len(candidates)
            selected_letters.append(candidates[idx])

        transliteration = "".join(l.name.capitalize() for l in selected_letters)
        meaning = f"Sanskrit {category.capitalize()} Invariant ({signature.proof_status})"

        return SanskritWord(
            letters=selected_letters,
            transliteration=transliteration,
            meaning=meaning,
        )

    def word_to_constraints(self, word: SanskritWord) -> Dict[str, Any]:
        """Map Sanskrit word Katapayadi number to mathematical constraints."""
        num = word.katapayadi_number
        return {
            "suggested_dimension": 16 if num % 2 == 0 else 32,
            "spectral_gap_bound": (num % 100) / 100.0,
            "charge_parity": num % 7 + 1,
            "quaternion_vector": word.to_quaternion().tolist(),
        }


class MultilingualWordSynthesizer:
    """
    Unified multilingual semantic synthesizer coordinating Hebrew, Arabic, and Sanskrit.
    """

    def __init__(self):
        self.hebrew = HebrewWordSynthesizer()
        self.arabic = ArabicWordSynthesizer()
        self.sanskrit = SanskritWordSynthesizer()

    def synthesize(self, signature: SemanticSignature, language: str = "hebrew") -> Any:
        lang = language.lower()
        if lang == "arabic":
            return self.arabic.generate_word(signature)
        elif lang == "sanskrit":
            return self.sanskrit.generate_word(signature)
        else:
            res = self.hebrew.generate_word(signature)
            return res[0] if isinstance(res, tuple) else res


if __name__ == "__main__":
    # Demo usage
    synthesizer = HebrewWordSynthesizer()
    
    print("=== Hebrew Word Synthesis Demo (with Opposites) ===\n")
    
    # Example 1: Verified theorem with opposite
    sig1 = SemanticSignature(
        algebraic_type="associator",
        dimension=32,
        invariant_value=0.707,
        topological_features={"betti_1": 2, "max_persistence": 0.6},
        proof_status="VERIFIED"
    )
    word1, opp1 = synthesizer.generate_word(sig1, transliteration_hint="AssocVerif")
    print(f"Verified Theorem Word:")
    print(f"  Primary Letters: {[l.name for l in word1.letters]}")
    print(f"  Primary Gematria: {word1.gematria_value} (reduced: {word1.reduced_value})")
    print(f"  Meaning: {word1.meaning}")
    if opp1:
        print(f"  Opposite Letters: {[l.name for l in opp1.letters]}")
        print(f"  Opposite Gematria: {opp1.gematria_value} (reduced: {opp1.reduced_value})")
        print(f"  Opposite Meaning: {opp1.meaning}")
    
    constraints1 = synthesizer.word_to_constraints(word1)
    print(f"  Decoded Constraints: {constraints1}\n")
    
    # Example 2: Falsified conjecture with opposite
    sig2 = SemanticSignature(
        algebraic_type="ramanujan_bound",
        dimension=64,
        invariant_value=2.5,
        topological_features={"betti_1": 1, "max_persistence": 0.3},
        proof_status="FALSIFIED"
    )
    word2, opp2 = synthesizer.generate_word(sig2, transliteration_hint="RamFalsify")
    print(f"Falsified Conjecture Word:")
    print(f"  Primary Letters: {[l.name for l in word2.letters]}")
    print(f"  Primary Gematria: {word2.gematria_value} (reduced: {word2.reduced_value})")
    print(f"  Meaning: {word2.meaning}")
    if opp2:
        print(f"  Opposite Letters: {[l.name for l in opp2.letters]}")
        print(f"  Opposite Gematria: {opp2.gematria_value} (reduced: {opp2.reduced_value})")
        print(f"  Opposite Meaning: {opp2.meaning}\n")
    
    # Example 3: Feedback-driven word
    feedback = ["Associativity failed at D=64", "Spectral gap too small"]
    word3, opp3 = synthesizer.generate_feedback_word(
        negative_feedback=feedback,
        topological_entropy=0.65,
        manifold_mode="EXPLORATION"
    )
    print(f"Feedback Steering Word:")
    print(f"  Letters: {[l.name for l in word3.letters]}")
    print(f"  Gematria: {word3.gematria_value}")
    print(f"  Lexicon Diversity: {synthesizer.compute_lexicon_diversity():.3f}")
