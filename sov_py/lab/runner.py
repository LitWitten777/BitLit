"""
src/lab/runner.py
Minimal runner script: encodes a small corpus to IR and scores candidate grammars.
Run from repo root:
    python -m src.lab.runner --corpus corpus/ --rounds 3 --candidates 5

Author: Researcher
Version: 0.1.0
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# Allow running from repo root without install
sys.path.insert(0, str(Path(__file__).parents[3]))

from .competition import (
    CorpusFile,
    Grammar,
    GrammarCompetition,
    load_corpus,
)
from .mutation_ops import mutate_n

# ---------------------------------------------------------------------------
# Built-in mini corpus (Sprint 1 — used when no --corpus dir is supplied)
# ---------------------------------------------------------------------------

BUILTIN_CORPUS = [
    CorpusFile(path="inline:ex1", language="sample_lang",
               content="let x = 1; let y = add(1, 2);"),
    CorpusFile(path="inline:ex2", language="sample_lang",
               content="let z = mul(2, 3);"),
    CorpusFile(path="inline:ex3", language="sample_lang",
               content="let result = add(mul(2, 3), 1);"),
]
for cf in BUILTIN_CORPUS:
    cf.content = cf.content  # already set inline


# ---------------------------------------------------------------------------
# Baseline grammar (sample_lang EBNF)
# ---------------------------------------------------------------------------

BASELINE_GRAMMAR = Grammar(
    grammar_id="sample_lang_baseline_v1",
    grammar_version="0.1.0",
    rules=[
        "program   ::= stmt*",
        "stmt      ::= let_stmt | expr_stmt",
        "let_stmt  ::= 'let' IDENT '=' expr ';'",
        "expr_stmt ::= expr ';'",
        "expr      ::= term (('+'|'-') term)*",
        "term      ::= factor (('*'|'/') factor)*",
        "factor    ::= IDENT '(' args ')' | IDENT | INT_LIT | '(' expr ')'",
        "args      ::= (expr (',' expr)*)?",
    ],
    parameters={"grammar_type": "LL1", "target_language": "sample_lang"},
)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Language Discovery Lab — Grammar Competition Runner"
    )
    parser.add_argument(
        "--corpus", default=None,
        help="Path to directory of .sl corpus files. Uses built-in mini corpus if omitted."
    )
    parser.add_argument(
        "--rounds", type=int, default=3,
        help="Number of competition rounds (default: 3)"
    )
    parser.add_argument(
        "--candidates", type=int, default=5,
        help="Number of grammar candidates per round (default: 5)"
    )
    parser.add_argument(
        "--output", default="output/discovery",
        help="Output directory for round results (default: output/discovery)"
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Emit JSON summary to stdout instead of human-readable output"
    )
    args = parser.parse_args()

    # Load corpus
    if args.corpus:
        corpus = load_corpus(args.corpus)
        if not corpus:
            print(f"No .sl files found in {args.corpus}; using built-in corpus.")
            corpus = BUILTIN_CORPUS
    else:
        print("No --corpus specified; using built-in mini corpus (3 files).")
        corpus = BUILTIN_CORPUS

    print(f"\nCorpus: {len(corpus)} file(s)")
    print(f"Rounds: {args.rounds}")
    print(f"Candidates/round: {args.candidates}")
    print(f"Output: {args.output}\n")

    # Run competition
    output_dir = Path(args.output)
    comp = GrammarCompetition(
        corpus=corpus,
        n_candidates=args.candidates,
        n_rounds=args.rounds,
        output_dir=output_dir,
    )
    history = comp.run(BASELINE_GRAMMAR, mutate_fn=lambda g, n: mutate_n(g, n))

    # Report results
    all_results = [r.to_dict() for r in history]

    if args.json:
        print(json.dumps(all_results, indent=2))
    else:
        print("=" * 60)
        print("COMPETITION RESULTS")
        print("=" * 60)
        for result in history:
            print(f"\nRound {result.round_number}:")
            print(f"  Best grammar : {result.best_grammar.grammar_id}")
            print(f"  Best fitness : {result.best_fitness:.4f}")
            print(f"  IR count     : {result.ir_count}")
            print(f"  Ranking:")
            for g in result.ranked_grammars:
                flag = " ← best" if g.grammar_id == result.best_grammar.grammar_id else ""
                print(f"    {g.grammar_id:50s}  {g.fitness:.4f}{flag}")
                if g.fitness_details:
                    for k, v in g.fitness_details.items():
                        print(f"      {k}: {v}")

        print("\n" + "=" * 60)
        final = history[-1]
        print(f"FINAL BEST: {final.best_grammar.grammar_id}")
        print(f"FITNESS:    {final.best_fitness:.4f}")
        print(f"ROUNDS:     {args.rounds}")
        print("=" * 60)

        # Save summary JSON
        output_dir.mkdir(parents=True, exist_ok=True)
        summary_path = output_dir / "summary.json"
        summary_path.write_text(json.dumps(all_results, indent=2), encoding="utf-8")
        print(f"\nSummary saved to: {summary_path}")


if __name__ == "__main__":
    main()
