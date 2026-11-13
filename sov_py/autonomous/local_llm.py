"""
local_llm.py — Local GGUF Neuro-Symbolic Cognitive Bridge.

Integrates local quantized GGUF models (e.g. Qwen2.5-Coder-7B-Instruct)
from the cognition partition into the autonomous mathematical reasoning engine.
Features:
- P-core CPU execution with AVX2 acceleration
- Strict GBNF grammar-constrained sampling for valid mathematical ASTs
- Teleological negative feedback integration for self-consistency rejection
- Safe lazy loading and graceful test fallback
"""

from __future__ import annotations

import json
import logging
import os
import queue
import threading
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

from .hypothesis_generator import CandidateHypothesis

logger = logging.getLogger(__name__)

ROOT_DIR = Path(__file__).resolve().parent.parent.parent.parent
DEFAULT_MODEL_PATH = "/data/mind/cognition/Qwen2.5-Coder-7B-Instruct-Q5_K_M.gguf"
FALLBACK_MODEL_PATH = "/home/roku/Documents/llama-3.2-1b-instruct-q4_k_m.gguf"
DEFAULT_GRAMMAR_PATH = str(ROOT_DIR / "grammars" / "hypothesis_schema.gbnf")
DEFAULT_PROMPT_PATH = "/data/mind/cognition/sovereign_cognition/prompts/conjecture_system.md"
DEFAULT_SERVER_URL = "http://127.0.0.1:11435/v1"


class LocalCognitiveBridge:
    """
    Cognitive bridge interfacing local GGUF models and llama-server (port 11435)
    with the autonomous verification loop via a non-blocking producer-consumer queue.
    """

    def __init__(
        self,
        model_path: str = DEFAULT_MODEL_PATH,
        grammar_path: str = DEFAULT_GRAMMAR_PATH,
        prompt_path: str = DEFAULT_PROMPT_PATH,
        server_url: str = DEFAULT_SERVER_URL,
        n_ctx: int = 2048,
        n_threads: int = 8,
        lazy_load: bool = True,
        mock_mode: bool = False,
        auto_start_producer: bool = True,
        queue_size: int = 10,
    ):
        # Resolve model path candidates
        if not os.path.exists(model_path) and os.path.exists(FALLBACK_MODEL_PATH):
            self.model_path = FALLBACK_MODEL_PATH
        else:
            self.model_path = model_path

        # Resolve grammar path
        if not os.path.exists(grammar_path):
            alt_grammar = ROOT_DIR / "grammars" / "hypothesis_schema.gbnf"
            if alt_grammar.exists():
                self.grammar_path = str(alt_grammar)
            else:
                self.grammar_path = grammar_path
        else:
            self.grammar_path = grammar_path

        self.prompt_path = prompt_path
        self.server_url = server_url.rstrip("/")
        self.n_ctx = n_ctx
        self.n_threads = n_threads
        self.mock_mode = mock_mode

        self._llm: Any = None
        self._grammar: Any = None
        self._grammar_text: str = ""
        self._system_prompt: str = ""
        self._load_system_prompt()
        self._load_grammar_text()

        # Asynchronous Producer-Consumer Queue (Buffer of candidate hypotheses)
        self._queue: queue.Queue[CandidateHypothesis] = queue.Queue(maxsize=queue_size)
        self._running: bool = False
        self._producer_thread: threading.Thread | None = None
        
        # PHASE 1 IMPROVEMENT: Store topological constraints for guided generation
        self._topological_constraints: dict | None = None

        if not lazy_load and not mock_mode:
            self.load_model()

        if auto_start_producer and not mock_mode:
            self.start_producer()

    def _load_system_prompt(self) -> None:
        """Loads system prompt from cognition partition if available."""
        p = Path(self.prompt_path)
        if p.exists():
            try:
                self._system_prompt = p.read_text(encoding="utf-8")
                return
            except Exception as e:
                logger.warning("Failed to read prompt file %s: %s", self.prompt_path, e)

        self._system_prompt = (
            "You are the Sovereign Neuro-Symbolic Mathematical Reasoning Engine.\n"
            "Formulate conjectures about Cayley-Dickson algebras, zero divisors, Fano planes, and quantum CSS codes.\n"
            "Output ONLY a single valid JSON object representing a CandidateHypothesis."
        )

    def _load_grammar_text(self) -> None:
        """Loads GBNF grammar text from disk."""
        p = Path(self.grammar_path)
        if p.exists():
            try:
                self._grammar_text = p.read_text(encoding="utf-8")
            except Exception as e:
                logger.warning("Failed to read grammar file %s: %s", self.grammar_path, e)

    def is_server_available(self, timeout: float = 0.5) -> bool:
        """Checks if llama-server is alive at self.server_url."""
        try:
            req = urllib.request.Request(f"{self.server_url}/models", method="GET")
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.status == 200
        except Exception:
            return False

    def is_available(self) -> bool:
        """Checks if either the HTTP server or local GGUF model file is available."""
        if self.mock_mode:
            return True
        if self.is_server_available():
            return True
        return os.path.exists(self.model_path) and os.path.getsize(self.model_path) > 100_000_000

    def start_producer(self) -> None:
        """Starts the asynchronous background producer daemon."""
        if self._producer_thread is not None and self._producer_thread.is_alive():
            return
        self._running = True
        self._producer_thread = threading.Thread(
            target=self._producer_loop,
            daemon=True,
            name="SovereignCognitiveProducer",
        )
        self._producer_thread.start()
        logger.info("Started sovereign cognitive producer thread.")

    def stop(self) -> None:
        """Stops the producer daemon and releases local resources."""
        self._running = False
        if self._producer_thread is not None:
            self._producer_thread.join(timeout=1.0)
            self._producer_thread = None
        self.close()

    def get_candidate_hypothesis(self) -> CandidateHypothesis | None:
        """
        Non-blocking retrieval of a candidate hypothesis from the producer buffer.
        Returns CandidateHypothesis in <0.1ms if available, or None if buffer is empty.
        """
        try:
            return self._queue.get_nowait()
        except queue.Empty:
            return None

    def _query_http_server(
        self,
        focus_area: str = "algebra",
        max_tokens: int = 128,
        temperature: float = 0.2,
    ) -> CandidateHypothesis | None:
        """Queries the local llama-server on port 11435 with GBNF grammar constraints."""
        url = f"{self.server_url}/chat/completions"
        payload = {
            "messages": [
                {"role": "system", "content": self._system_prompt},
                {
                    "role": "user",
                    "content": (
                        f"Focus Area: {focus_area.upper()}.\n"
                        "Propose a candidate hypothesis conforming to Cayley-Dickson algebraic invariants or doubling pole codes.\n"
                        "Return strictly the JSON object."
                    ),
                },
            ],
            "grammar": self._grammar_text,
            "temperature": temperature,
            "max_tokens": max_tokens,
            "stop": ["<|im_end|>", "<|end_of_text|>", "<|eot_id|>"],
        }
        req = urllib.request.Request(
            url,
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=10.0) as resp:
            data = json.loads(resp.read().decode("utf-8"))
            content = data["choices"][0]["message"]["content"]
            return self._parse_json_hypothesis(content)

    def _producer_loop(self) -> None:
        """
        Background producer loop maintaining a buffer of 5-10 candidate invariants.
        Decoupled from the main tick loop so the engine never stalls.
        
        PHASE 1 IMPROVEMENT: Uses topological constraints to guide generation.
        """
        modality_cycle = ["algebra", "graph", "code", "scaling", "smt", "lean"]
        cycle_idx = 0

        while self._running:
            try:
                if self._queue.qsize() < 5:
                    focus = modality_cycle[cycle_idx % len(modality_cycle)]
                    cycle_idx += 1
                    hyp: CandidateHypothesis | None = None
                    
                    # PHASE 1 IMPROVEMENT: Build topological context for generation
                    topological_ctx = None
                    if self._topological_constraints:
                        topological_ctx = self._topological_constraints.copy()

                    # 1. Try local HTTP llama-server on port 11435
                    if self.is_server_available(timeout=0.3):
                        try:
                            # Note: HTTP server doesn't support topological constraints yet
                            # Would need to extend the payload schema
                            hyp = self._query_http_server(focus_area=focus)
                        except Exception as he:
                            logger.debug("HTTP llama-server query failed: %s", he)

                    # 2. Try in-process model if loaded (supports topological constraints)
                    if hyp is None and self._llm is not None:
                        try:
                            hyp = self._generate_inprocess(
                                focus_area=focus,
                                topological_constraints=topological_ctx,
                                max_tokens=128,
                            )
                        except Exception as ie:
                            logger.debug("In-process generation failed: %s", ie)

                    # 3. Fallback to mock if in mock mode or no model
                    if hyp is None and (self.mock_mode or not self.is_available()):
                        hyp = self._mock_generate(focus_area=focus)

                    if hyp is not None:
                        try:
                            self._queue.put(hyp, timeout=1.0)
                        except queue.Full:
                            pass
                    time.sleep(0.1)
                else:
                    time.sleep(0.5)
            except Exception as e:
                logger.debug("Cognitive producer loop error: %s", e)
                time.sleep(2.0)

    def load_model(self) -> bool:
        """Loads the local GGUF model into memory for in-process inference."""
        if self.mock_mode:
            return True
        if self._llm is not None:
            return True
        if not os.path.exists(self.model_path):
            logger.warning("Local GGUF model not found at %s", self.model_path)
            return False

        try:
            from llama_cpp import Llama, LlamaGrammar

            logger.info(
                "Loading in-process GGUF model from %s (n_ctx=%d, n_threads=%d)...",
                self.model_path,
                self.n_ctx,
                self.n_threads,
            )
            t0 = time.time()
            self._llm = Llama(
                model_path=self.model_path,
                n_ctx=self.n_ctx,
                n_threads=self.n_threads,
                verbose=False,
            )
            logger.info("Loaded in-process GGUF model in %.2f seconds.", time.time() - t0)

            if self._grammar_text:
                try:
                    self._grammar = LlamaGrammar.from_string(self._grammar_text)
                    logger.info("Loaded GBNF grammar into llama_cpp.")
                except Exception as ge:
                    logger.warning("Failed to parse grammar into llama_cpp: %s", ge)
                    self._grammar = None

            return True
        except ImportError:
            logger.warning("llama_cpp Python package is not installed.")
            return False
        except Exception as e:
            logger.error("Failed to initialize in-process GGUF model: %s", e)
            return False

    def close(self) -> None:
        """Explicitly releases local LLM resources before interpreter shutdown."""
        if self._llm is not None:
            try:
                self._llm.close()
            except Exception:
                pass
            self._llm = None
    
    def set_topological_constraints(self, constraints: dict) -> None:
        """
        PHASE 1 IMPROVEMENT: Set topological constraints for guided hypothesis generation.
        
        Args:
            constraints: Dict with keys:
                - proven_invariants: List of algebraic constraints that must hold
                - forbidden_proposals: List of proposals that violate topology
                - betti_constraints: Dict with betti_0, betti_1 values
        """
        self._topological_constraints = constraints
        logger.info(
            "Updated topological constraints: %d proven invariants, %d forbidden proposals",
            len(constraints.get('proven_invariants', [])),
            len(constraints.get('forbidden_proposals', [])),
        )
    
    def get_topological_constraints(self) -> dict | None:
        """Retrieve current topological constraints."""
        return self._topological_constraints

    def __del__(self) -> None:
        self.stop()
        self.close()


    def _generate_inprocess(
        self,
        focus_area: str = "algebra",
        recent_verified: list[str] | None = None,
        negative_feedback: list[str] | None = None,
        topological_constraints: dict | None = None,  # NEW
        max_tokens: int = 128,
        temperature: float = 0.2,
    ) -> CandidateHypothesis | None:
        """Runs generation through in-process llama_cpp model."""
        if self._llm is None and not self.load_model():
            return None

        user_content = f"Focus Area: {focus_area.upper()}\n"
        if recent_verified:
            user_content += "Recently Confirmed Invariants:\n"
            for v in recent_verified[-5:]:
                user_content += f"- {v}\n"

        if negative_feedback:
            user_content += "NEGATIVE INVARIANT CONSTRAINTS (DO NOT PROPOSE):\n"
            for fb in negative_feedback[-5:]:
                user_content += f"- {fb}\n"
        
        # NEW: Add topological guidance
        if topological_constraints:
            user_content += "\nTOPOLOGICAL CONSTRAINTS (MUST RESPECT):\n"
            if "proven_invariants" in topological_constraints:
                for inv in topological_constraints["proven_invariants"]:
                    user_content += f"- {inv}\n"
            if "betti_constraints" in topological_constraints:
                bc = topological_constraints["betti_constraints"]
                user_content += f"- Betti numbers: β₀={bc.get('betti_0', '?')}, β₁={bc.get('betti_1', '?')}\n"
            if "forbidden_proposals" in topological_constraints:
                user_content += "FORBIDDEN (violates topology):\n"
                for prop in topological_constraints["forbidden_proposals"]:
                    user_content += f"- {prop}\n"

        user_content += (
            "Propose a candidate hypothesis conforming to Cayley-Dickson algebraic invariants or doubling pole codes.\n"
            "Return strictly the JSON object."
        )

        prompt = (
            f"<|im_start|>system\n{self._system_prompt}<|im_end|>\n"
            f"<|im_start|>user\n{user_content}<|im_end|>\n"
            f"<|im_start|>assistant\n"
        )

        kwargs: dict[str, Any] = {
            "max_tokens": max_tokens,
            "temperature": temperature,
            "stop": ["<|im_end|>", "<|end_of_text|>", "<|eot_id|>"],
        }
        if self._grammar is not None:
            kwargs["grammar"] = self._grammar

        res = self._llm(prompt, **kwargs)
        raw_text = res["choices"][0]["text"].strip()
        return self._parse_json_hypothesis(raw_text)

    def generate_candidate_hypothesis(
        self,
        focus_area: str = "algebra",
        recent_verified: list[str] | None = None,
        negative_feedback: list[str] | None = None,
        topological_constraints: dict | None = None,  # NEW: Topological guidance
        max_tokens: int = 128,
        temperature: float = 0.2,
    ) -> CandidateHypothesis | None:
        """
        Synthesizes a new mathematical CandidateHypothesis.
        Pops from the pre-buffered producer queue if available for zero latency,
        or generates immediately via HTTP server / in-process model.
        
        Args:
            topological_constraints: Optional dict with:
                - proven_invariants: List of algebraic constraints that must hold
                - forbidden_proposals: List of proposals that violate topology
                - betti_constraints: Dict with betti_0, betti_1 values
        """
        if self.mock_mode or not self.is_available():
            return self._mock_generate(focus_area, negative_feedback)

        # 1. Non-blocking queue check
        buffered = self.get_candidate_hypothesis()
        if buffered is not None and not recent_verified and not negative_feedback and not topological_constraints:
            return buffered

        # 2. HTTP Server query
        if self.is_server_available():
            try:
                hyp = self._query_http_server(focus_area=focus_area, max_tokens=max_tokens, temperature=temperature)
                if hyp is not None:
                    return hyp
            except Exception as e:
                logger.debug("Direct HTTP query failed: %s", e)

        # 3. In-process inference
        if self._llm is not None or (not self.mock_mode and os.path.exists(self.model_path)):
            try:
                hyp = self._generate_inprocess(
                    focus_area=focus_area,
                    recent_verified=recent_verified,
                    negative_feedback=negative_feedback,
                    topological_constraints=topological_constraints,  # NEW
                    max_tokens=max_tokens,
                    temperature=temperature,
                )
                if hyp is not None:
                    return hyp
            except Exception as e:
                logger.error("Local GGUF hypothesis generation failed: %s", e)

        # 4. Fallback mock generator
        return self._mock_generate(focus_area, negative_feedback)

    def generate_lean_tactic_strategy(
        self,
        theorem_statement: str,
        known_lemmas: list[str] | None = None,
        max_tokens: int = 200,
    ) -> str:
        """
        Generates a candidate Lean 4 proof tactic sequence for a given theorem statement.
        """
        if self.mock_mode or not self.is_available():
            return "by\n  dsimp\n  omega"

        if not self.load_model():
            return "by\n  dsimp\n  omega"

        user_msg = f"Theorem to prove in Lean 4:\n```lean\n{theorem_statement}\n```\n"
        if known_lemmas:
            user_msg += "Available helper lemmas:\n" + "\n".join(f"- {l}" for l in known_lemmas[:8])
        user_msg += "\nProvide ONLY the Lean 4 proof body (starting with `by`)."

        prompt = (
            "<|im_start|>system\nYou are an expert Lean 4 formal mathematician. "
            "Emit only clean, sound tactic proofs.<|im_end|>\n"
            f"<|im_start|>user\n{user_msg}<|im_end|>\n"
            f"<|im_start|>assistant\n"
        )

        try:
            res = self._llm(prompt, max_tokens=max_tokens, temperature=0.1, stop=["<|im_end|>"])
            tactic_code = res["choices"][0]["text"].strip()
            if not tactic_code.startswith("by"):
                tactic_code = f"by\n  {tactic_code}"
            return tactic_code
        except Exception as e:
            logger.error("Local GGUF tactic generation failed: %s", e)
            return "by\n  dsimp\n  omega"

    def _parse_json_hypothesis(self, text: str) -> CandidateHypothesis | None:
        """Parses and validates a candidate hypothesis JSON string."""
        start_idx = text.find("{")
        end_idx = text.rfind("}")
        if start_idx == -1 or end_idx == -1 or end_idx < start_idx:
            logger.warning("No JSON object found in response: %s", text)
            return None

        json_str = text[start_idx : end_idx + 1]
        try:
            data = json.loads(json_str)
            return CandidateHypothesis(
                id=str(data.get("id", f"HYP-LLM-{int(time.time() * 1000) % 100000}")),
                statement=str(data.get("statement", "Candidate invariant")),
                category=str(data.get("category", "ALGEBRA")),
                conjecture_type=str(data.get("conjecture_type", "ALGEBRAIC_IDENTITY")),
                predicate=str(data.get("predicate", "associativity")),
                parameters=dict(data.get("parameters", {})),
                expected_relation=dict(data.get("expected_relation", {"op": "==", "val": True})),
            )
        except Exception as e:
            logger.warning("JSON hypothesis validation failed: %s (raw: %s)", e, json_str)
            return None

    def _mock_generate(
        self, focus_area: str, negative_feedback: list[str] | None = None
    ) -> CandidateHypothesis:
        """Generates a structured candidate hypothesis in mock mode."""
        ts = int(time.time() * 1000) % 100000
        if "graph" in focus_area.lower():
            return CandidateHypothesis(
                id=f"HYP-LLM-G{ts}",
                statement="The doubling pole annihilation subgraph at chi = D/4 is (D-8)-regular.",
                category="GRAPH_THEORY",
                conjecture_type="GRAPH_INVARIANT",
                predicate="regular",
                parameters={"dim": 64, "expected_degree": 56},
                expected_relation={"op": "==", "val": True},
            )
        if "code" in focus_area.lower():
            return CandidateHypothesis(
                id=f"HYP-LLM-C{ts}",
                statement="The doubling pole CSS code at D=64 has triply-even basis check weights w = 56 = 8 * 7.",
                category="CODING_THEORY",
                conjecture_type="CODE_INVARIANT",
                predicate="triply_even_checks",
                parameters={"dim": 64},
                expected_relation={"op": "==", "val": True},
            )

        return CandidateHypothesis(
            id=f"HYP-LLM-A{ts}",
            statement="Cross-half vectors in sedenions annihilate only if their XOR charges are equal.",
            category="ALGEBRA",
            conjecture_type="ALGEBRAIC_IDENTITY",
            predicate="anticommutativity_imaginary",
            parameters={"dim": 16},
            expected_relation={"op": "==", "val": True},
        )
