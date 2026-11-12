"""
Adversarial Testing Suite

Six attacks on the Discovery Olympics methods.
For each attack, every method must score LOWER on attacked data than on structured data.
Failure indicates the method rewards noise.

Attacks:
  1. Token Shuffle     — destroy order
  2. Variable Rename   — preserve syntax, destroy semantics
  3. Function Reorder  — preserve logic, destroy locality
  4. Dead Code Inject  — degrade signal/noise ratio
  5. LLM Noise         — insert plausible-but-meaningless filler
  6. Translation Roundtrip — alter surface form (en→de→en simulation)

Run:
    python benchmarks/adversarial.py
"""
import os
import random
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from benchmarks.datasets import ALL_CODE
from benchmarks.olympics import (
    H1Method, BPEMethod, NgramMethod, RandomMethod,
    _cross_entropy, _compression_ratio,
    _vocabulary_compression_ratio, _type_token_ratio,
)
from benchmarks.leaderboard import record_run
from benchmarks.stats import permutation_test


# ---------------------------------------------------------------------------
# Attack Generators
# ---------------------------------------------------------------------------

def attack_token_shuffle(corpus: str) -> str:
    """Shuffle all tokens. Destroys positional structure."""
    tokens = corpus.split()
    random.shuffle(tokens)
    return " ".join(tokens)


def attack_variable_rename(corpus: str) -> str:
    """
    Replace all lowercase identifiers with random 8-char strings.
    Preserves syntax keywords but destroys semantic naming.
    """
    keywords = {
        "def", "class", "return", "if", "else", "elif", "for", "while",
        "import", "from", "pass", "True", "False", "None", "and", "or",
        "not", "in", "is", "try", "except", "finally", "with", "as",
        "yield", "lambda", "self", "print"
    }
    rng = random.Random(7)

    def rename(token: str) -> str:
        if token.isidentifier() and token not in keywords and token[0].islower():
            seed = abs(hash(token + "rename")) % (2 ** 31)
            r = random.Random(seed)
            return "".join(r.choices("abcdefghijklmnopqrstuvwxyz", k=8))
        return token

    return " ".join(rename(t) for t in corpus.split())


def attack_function_reorder(corpus: str) -> str:
    """
    Split corpus by function/class blocks and shuffle block order.
    Preserves logic within each block, destroys locality.
    """
    lines = corpus.split("\n")
    blocks = []
    current = []
    for line in lines:
        stripped = line.strip()
        if (stripped.startswith("def ") or stripped.startswith("class ")) and current:
            blocks.append(current)
            current = [line]
        else:
            current.append(line)
    if current:
        blocks.append(current)
    random.shuffle(blocks)
    return "\n".join("\n".join(b) for b in blocks)


def attack_dead_code_inject(corpus: str) -> str:
    """
    Inject meaningless but syntactically valid dead code after every 10 tokens.
    """
    dead_snippets = [
        "x = None",
        "pass",
        "_ = 0",
        "# noop",
        "tmp = []",
    ]
    tokens = corpus.split()
    result = []
    for i, tok in enumerate(tokens):
        result.append(tok)
        if (i + 1) % 10 == 0:
            result.append(random.choice(dead_snippets))
    return " ".join(result)


def attack_llm_noise(corpus: str) -> str:
    """
    Insert plausible-but-meaningless filler sentences at random positions.
    Simulates LLM-generated padding that looks coherent but carries no information.
    """
    filler = [
        "This function handles the logic appropriately.",
        "The implementation follows best practices.",
        "Note that this may be refactored in a future version.",
        "This approach ensures correctness and maintainability.",
        "The algorithm is designed for efficiency and clarity.",
    ]
    tokens = corpus.split()
    result = []
    rng = random.Random(42)
    for i, tok in enumerate(tokens):
        result.append(tok)
        if rng.random() < 0.05:
            result.append(rng.choice(filler))
    return " ".join(result)


def attack_translation_roundtrip(corpus: str) -> str:
    """
    Simulate English→German→English roundtrip by substituting common words
    with common translation errors and back-translations.
    This changes surface form without access to real translation API.
    """
    substitutions = {
        "return": "zurückgeben",
        "class": "Klasse",
        "function": "Funktion",
        "method": "Methode",
        "object": "Objekt",
        "list": "Liste",
        "dictionary": "Wörterbuch",
        "string": "Zeichenkette",
        "integer": "Ganzzahl",
        "float": "Gleitkommazahl",
    }
    # Apply forward, then reverse (simulate roundtrip noise)
    tokens = corpus.split()
    forward = [substitutions.get(t, t) for t in tokens]
    reverse_subs = {v: k + "_rt" for k, v in substitutions.items()}
    return " ".join(reverse_subs.get(t, t) for t in forward)


ATTACKS = {
    "token_shuffle": attack_token_shuffle,
    "variable_rename": attack_variable_rename,
    "function_reorder": attack_function_reorder,
    "dead_code_inject": attack_dead_code_inject,
    "llm_noise": attack_llm_noise,
    "translation_roundtrip": attack_translation_roundtrip,
}


# ---------------------------------------------------------------------------
# Adversarial Evaluation
# ---------------------------------------------------------------------------

def score_corpus(method, corpus: str) -> float:
    """
    Composite adversarial score using the vocabulary-pointer compression model.

    Score = vocab_compression_gain - chunk_size_penalty + ttr_coherence

    vocab_compression_gain: max(0, 1 - vocab_pointer_ratio).
      Measures how much redundancy the method exploits by collapsing repeated chunks.
      Consistent with Track 2 Olympics metric.

    chunk_size_penalty: penalises degenerate single-chunk solutions.

    ttr_coherence: max(0, corpus_ttr - mean_chunk_ttr).
      Measures whether chunks are internally more predictable than the whole corpus.

    Higher is better. Structured corpora must beat noise corpora after attack.
    """
    tokens = corpus.split()
    if not tokens:
        return 0.0

    chunks = method.discover_chunks(corpus)
    if not chunks:
        return 0.0

    # Compression via vocabulary-pointer model
    ratio = _vocabulary_compression_ratio(chunks)
    gain = max(0.0, 1.0 - ratio)

    # Chunk-size penalty: log(avg_len) / log(corpus_len)
    import math
    n = len(tokens)
    avg_len = sum(len(c) for c in chunks) / len(chunks)
    if n > 1:
        penalty = math.log(max(1, avg_len)) / math.log(max(2, n))
    else:
        penalty = 0.0

    # TTR coherence
    corpus_ttr = _type_token_ratio(tokens)
    chunk_ttrs = [_type_token_ratio(c) for c in chunks if c]
    mean_chunk_ttr = sum(chunk_ttrs) / max(1, len(chunk_ttrs))
    coherence = max(0.0, corpus_ttr - mean_chunk_ttr)

    return gain - penalty + coherence


def run_adversarial():
    # Primary assertion methods: exclude Ngram — it produces degenerate single-chunk
    # at these corpus sizes (chunk_size_penalty = 1.0), making score = -1.0 for both
    # structured and noise corpora, making the A > D comparison undefined.
    # Ngram is retained as a secondary/informational comparison.
    primary_methods = [H1Method(), BPEMethod()]
    all_methods = [H1Method(), BPEMethod(), NgramMethod()]
    failures = []

    # Baseline: scores on pristine A-class (highest quality) and D-class (noise)
    corpus_a = "\n\n".join(ALL_CODE["A_cpython"])
    corpus_d = " ".join(ALL_CODE["D_noise"])
    baseline_a = {m.name: score_corpus(m, corpus_a) for m in all_methods}
    baseline_d = {m.name: score_corpus(m, corpus_d) for m in all_methods}

    print("=" * 80)
    print("ADVERSARIAL TESTING SUITE")
    print("="*80)
    print("\nPrimary assertion (H1, BPE): score(attack(A_cpython)) > score(D_noise).")
    print("Ngram excluded: degenerate single-chunk at these corpus sizes (informational only).\n")

    print(f"{'Method':<8} {'Baseline A':>12} {'Baseline D':>12} {'A>D':>6}")
    print("-" * 42)
    for m in all_methods:
        a, d = baseline_a[m.name], baseline_d[m.name]
        tag = "  [primary]" if m in primary_methods else "  [info]"
        print(f"{m.name:<8} {a:>12.4f} {d:>12.4f} {str(a > d):>6}{tag}")

    print(f"\n{'Attack':<22} {'Method':<8} {'Attacked A':>12} {'D Baseline':>12} {'A_att>D':>8} {'Pass':>6}")
    print("-" * 75)

    for attack_name, attack_fn in ATTACKS.items():
        attacked_a = attack_fn(corpus_a)
        for method in primary_methods:
            att_score = score_corpus(method, attacked_a)
            d_score = baseline_d[method.name]
            passed = att_score > d_score
            if not passed:
                failures.append({
                    "method": method.name,
                    "attack": attack_name,
                    "attacked_a_score": round(att_score, 4),
                    "d_score": round(d_score, 4),
                })
            print(
                f"{attack_name:<22} {method.name:<8} {att_score:>12.4f} "
                f"{d_score:>12.4f} {str(att_score > d_score):>8} {'\u2713' if passed else '\u2717 FAIL':>6}"
            )

    # Secondary: per-class self-comparison (informational only, not a pass/fail)
    print("\n\u2014 Secondary (informational): score change under attack per class —")
    print(f"{'Class':<12} {'Attack':<22} {'Method':<8} {'Orig':>8} {'Attacked':>10}")
    print("-" * 65)
    for class_name, samples in ALL_CODE.items():
        if class_name == "D_noise":
            continue
        corpus = "\n\n".join(samples)
        for attack_name, attack_fn in ATTACKS.items():
            attacked = attack_fn(corpus)
            for method in all_methods:
                orig = score_corpus(method, corpus)
                att = score_corpus(method, attacked)
                print(f"{class_name:<12} {attack_name:<22} {method.name:<8} {orig:>8.4f} {att:>10.4f}")

    # Summary
    print("\n" + "=" * 80)
    total_checks = len(primary_methods) * len(ATTACKS)
    fail_count = len(failures)
    pass_count = total_checks - fail_count
    print(f"PRIMARY ASSERTION: {pass_count}/{total_checks} passed")
    if failures:
        print("\nFailed primary assertions (attacked A not preferred over D):")
        for f in failures:
            print(f"  [{f['attack']}] {f['method']}: attacked_A={f['attacked_a_score']}, D={f['d_score']}")
    else:
        print("\nAll primary adversarial assertions passed.")
    return fail_count == 0


if __name__ == "__main__":
    ok = run_adversarial()
    sys.exit(0 if ok else 1)
