"""
src/lab/competition.py
Language Discovery Lab — Grammar Competition Engine.

Runs candidate grammars against a corpus, scores them, and ranks results.
See specs/language_discovery_plan.md for architecture and protocol.

Author: Researcher
Version: 0.1.0
"""
from __future__ import annotations

import json
import logging
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

from ..hypergraph import make_provenance

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class Grammar:
    grammar_id: str
    grammar_version: str
    rules: list[str]
    parameters: dict[str, Any] = field(default_factory=dict)
    fitness: Optional[float] = None
    fitness_details: dict[str, float] = field(default_factory=dict)
    parent_id: Optional[str] = None

    def to_dict(self) -> dict:
        return {
            "grammar_id": self.grammar_id,
            "grammar_version": self.grammar_version,
            "rules": self.rules,
            "parameters": self.parameters,
            "fitness": self.fitness,
            "fitness_details": self.fitness_details,
            "parent_id": self.parent_id,
        }


@dataclass
class CorpusFile:
    path: str
    language: str
    weight: float = 1.0
    content: str = ""

    def load(self) -> None:
        self.content = Path(self.path).read_text(encoding="utf-8")


@dataclass
class CompetitionResult:
    round_number: int
    ranked_grammars: list[Grammar]      # sorted best → worst
    best_grammar: Grammar
    best_fitness: float
    ir_count: int
    provenance: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict:
        return {
            "round_number": self.round_number,
            "best_grammar_id": self.best_grammar.grammar_id,
            "best_fitness": round(self.best_fitness, 4),
            "ir_count": self.ir_count,
            "ranking": [
                {"grammar_id": g.grammar_id, "fitness": round(g.fitness or 0, 4)}
                for g in self.ranked_grammars
            ],
            "provenance": self.provenance,
        }


# ---------------------------------------------------------------------------
# Scoring objectives (mirrors language_discovery_plan.md §5)
# ---------------------------------------------------------------------------

SCORING_WEIGHTS = {
    "parse_success_rate": 0.40,
    "ir_completeness":    0.25,
    "graph_density":      0.15,
    "token_entropy":      0.10,
    "parse_time_ms":      0.10,   # lower is better → inverted below
}

REQUIRED_IR_FIELDS = {
    "ir_id", "ir_version", "object_type", "representation_level",
    "content", "provenance",
}


def _ir_completeness(ir: dict) -> float:
    present = sum(1 for f in REQUIRED_IR_FIELDS if f in ir)
    return present / len(REQUIRED_IR_FIELDS)


def _graph_density(ir: dict) -> float:
    graph = ir.get("content", {}).get("graph", {})
    nodes = len(graph.get("nodes", []))
    edges = len(graph.get("edges", []))
    if nodes == 0:
        return 0.0
    return min(edges / nodes, 1.0)


def _token_entropy(ir: dict) -> float:
    import math
    tokens = ir.get("content", {}).get("tokens", [])
    if not tokens:
        return 0.0
    pos_counts: dict[str, int] = {}
    for t in tokens:
        pos = t.get("pos", "UNKNOWN")
        pos_counts[pos] = pos_counts.get(pos, 0) + 1
    total = len(tokens)
    entropy = -sum(
        (c / total) * math.log2(c / total) for c in pos_counts.values() if c > 0
    )
    # Normalize: max entropy for n classes is log2(n)
    max_entropy = math.log2(len(pos_counts)) if len(pos_counts) > 1 else 1.0
    return entropy / max_entropy if max_entropy > 0 else 0.0


def score_grammar(
    irs: list[dict],
    parse_times_ms: list[float],
    corpus_size: int,
) -> tuple[float, dict[str, float]]:
    """
    Compute weighted fitness score for a grammar given its produced IRs.
    Returns (fitness, details_dict).
    """
    parse_success_rate = len(irs) / corpus_size if corpus_size > 0 else 0.0
    ir_completeness    = sum(_ir_completeness(ir) for ir in irs) / len(irs) if irs else 0.0
    graph_density      = sum(_graph_density(ir) for ir in irs)   / len(irs) if irs else 0.0
    token_entropy      = sum(_token_entropy(ir) for ir in irs)   / len(irs) if irs else 0.0
    avg_parse_ms       = sum(parse_times_ms) / len(parse_times_ms) if parse_times_ms else 500.0
    parse_time_score   = max(0.0, 1.0 - avg_parse_ms / 500.0)   # 500ms = worst

    details = {
        "parse_success_rate": round(parse_success_rate, 4),
        "ir_completeness":    round(ir_completeness, 4),
        "graph_density":      round(graph_density, 4),
        "token_entropy":      round(token_entropy, 4),
        "parse_time_ms":      round(avg_parse_ms, 2),
        "parse_time_score":   round(parse_time_score, 4),
    }

    fitness = (
        SCORING_WEIGHTS["parse_success_rate"] * parse_success_rate
        + SCORING_WEIGHTS["ir_completeness"]  * ir_completeness
        + SCORING_WEIGHTS["graph_density"]    * graph_density
        + SCORING_WEIGHTS["token_entropy"]    * token_entropy
        + SCORING_WEIGHTS["parse_time_ms"]    * parse_time_score
    )
    return round(fitness, 4), details


# ---------------------------------------------------------------------------
# Corpus encoder (stub — wired to sample_lang pipeline)
# ---------------------------------------------------------------------------

def encode_corpus(
    corpus_files: list[CorpusFile],
    grammar: Grammar,
    context_id: str = "ctx-lab-001",
) -> tuple[list[dict], list[float]]:
    """
    Encode all corpus files using the given grammar.
    Returns (irs, parse_times_ms).

    Stub implementation: generates minimal IR dicts from content without
    calling the full parser (full parser integration is Sprint 2).
    """
    import time

    irs: list[dict] = []
    times: list[float] = []

    for cf in corpus_files:
        t0 = time.monotonic()
        try:
            # Sprint 1 stub: produce a minimal valid IR from raw content
            ir = _stub_encode(cf, grammar, context_id)
            irs.append(ir)
        except Exception as exc:
            logger.warning("encode_corpus: failed on %s: %s", cf.path, exc)
        elapsed = (time.monotonic() - t0) * 1000
        times.append(elapsed)

    return irs, times


def _stub_encode(
    cf: CorpusFile,
    grammar: Grammar,
    context_id: str,
) -> dict:
    """Minimal IR from corpus file content. Replace with real parser in Sprint 2."""
    tokens = [
        {"index": i, "surface": w, "lemma": w, "pos": "IDENT", "span": [i * 2, i * 2 + len(w)]}
        for i, w in enumerate(cf.content.split()[:50])   # cap at 50 tokens
    ]
    return {
        "ir_id": str(uuid.uuid4()),
        "ir_version": "0.1.0",
        "object_type": "code_snippet",
        "representation_level": 1,
        "language_tag": cf.language,
        "content": {
            "surface_form": cf.content[:200],
            "payload": {"grammar_id": grammar.grammar_id, "stub": True},
            "tokens": tokens,
            "graph": {"nodes": [], "edges": []},
        },
        "provenance": make_provenance(
            source=f"lab_stub_{grammar.grammar_id}",
            derivation=f"Stub encoding of {cf.path} with grammar {grammar.grammar_id}",
            confidence=0.5,
            validation_status="unvalidated",
            evidence=[],
        ),
        "context_id": context_id,
        "metrics": {"token_count": len(tokens)},
    }


# ---------------------------------------------------------------------------
# Competition Engine
# ---------------------------------------------------------------------------

class GrammarCompetition:
    """
    Runs grammar competition rounds.

    Usage:
        from src.lab.mutation_ops import mutate_grammar

        corpus = load_corpus("corpus/")
        baseline = Grammar(grammar_id="baseline", grammar_version="0.1.0", rules=["program ::= stmt*"])
        comp = GrammarCompetition(corpus=corpus, n_candidates=5, n_rounds=3)
        results = comp.run(baseline)
    """

    def __init__(
        self,
        corpus: list[CorpusFile],
        n_candidates: int = 5,
        n_rounds: int = 3,
        context_id: str = "ctx-lab-001",
        output_dir: Optional[Path] = None,
    ) -> None:
        self.corpus = corpus
        self.n_candidates = n_candidates
        self.n_rounds = n_rounds
        self.context_id = context_id
        self.output_dir = output_dir
        self.history: list[CompetitionResult] = []

    def run(
        self,
        baseline: Grammar,
        mutate_fn: Optional[Any] = None,
    ) -> list[CompetitionResult]:
        """
        Run n_rounds of competition starting from baseline grammar.

        Parameters
        ----------
        baseline  : Initial grammar.
        mutate_fn : Callable(grammar, n) -> List[Grammar]. Defaults to mutation_ops.mutate_grammar.
        """
        if mutate_fn is None:
            from .mutation_ops import mutate_grammar
            mutate_fn = lambda g, n: [mutate_grammar(g) for _ in range(n)]

        candidates: list[Grammar] = [baseline] + mutate_fn(baseline, self.n_candidates - 1)

        for round_num in range(1, self.n_rounds + 1):
            logger.info("Competition round %d/%d (%d candidates)", round_num, self.n_rounds, len(candidates))
            result = self._run_round(round_num, candidates)
            self.history.append(result)

            if self.output_dir:
                self._save_round(result)

            # Next round: top-1 survives, rest are mutated
            best = result.best_grammar
            candidates = [best] + mutate_fn(best, self.n_candidates - 1)

        return self.history

    def _run_round(self, round_num: int, candidates: list[Grammar]) -> CompetitionResult:
        scored: list[Grammar] = []
        for grammar in candidates:
            irs, times = encode_corpus(self.corpus, grammar, self.context_id)
            fitness, details = score_grammar(irs, times, len(self.corpus))
            grammar.fitness = fitness
            grammar.fitness_details = details
            scored.append(grammar)

        scored.sort(key=lambda g: g.fitness or 0, reverse=True)
        best = scored[0]

        total_irs = sum(
            len(encode_corpus(self.corpus, g, self.context_id)[0]) for g in scored
        )

        return CompetitionResult(
            round_number=round_num,
            ranked_grammars=scored,
            best_grammar=best,
            best_fitness=best.fitness or 0.0,
            ir_count=total_irs,
            provenance=make_provenance(
                source="grammar_competition_v0.1",
                derivation=f"Round {round_num}: {len(scored)} grammars scored; best={best.grammar_id}",
                confidence=best.fitness or 0.0,
                validation_status="unvalidated",
                evidence=[g.grammar_id for g in scored],
            ),
        )

    def _save_round(self, result: CompetitionResult) -> None:
        if self.output_dir is None:
            return
        self.output_dir.mkdir(parents=True, exist_ok=True)
        path = self.output_dir / f"round_{result.round_number:02d}.json"
        path.write_text(json.dumps(result.to_dict(), indent=2), encoding="utf-8")


# ---------------------------------------------------------------------------
# Corpus loader
# ---------------------------------------------------------------------------

def load_corpus(directory: str) -> list[CorpusFile]:
    """Load all .sl files from a directory as corpus files."""
    files: list[CorpusFile] = []
    for p in sorted(Path(directory).glob("**/*.sl")):
        cf = CorpusFile(path=str(p), language="sample_lang")
        cf.load()
        files.append(cf)
    logger.info("Loaded %d corpus files from %s", len(files), directory)
    return files
