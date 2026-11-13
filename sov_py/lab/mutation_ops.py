"""
src/lab/mutation_ops.py
Grammar Mutation Operations for the Language Discovery Lab.

Each operation takes a Grammar and returns a new Grammar (original is unchanged).
See specs/language_discovery_plan.md §6 for operation catalog.

Author: Researcher
Version: 0.1.0
"""
from __future__ import annotations

import random
import uuid
from typing import Optional

from .competition import Grammar


# ---------------------------------------------------------------------------
# Individual mutation operations
# ---------------------------------------------------------------------------

def _new_id() -> str:
    return str(uuid.uuid4())[:8]


def add_rule(grammar: Grammar, rule: Optional[str] = None) -> Grammar:
    """Add a new production rule (random placeholder if not provided)."""
    new_rule = rule or f"rule_{_new_id()} ::= IDENT"
    return Grammar(
        grammar_id=f"{grammar.grammar_id}_add_{_new_id()}",
        grammar_version=grammar.grammar_version,
        rules=grammar.rules + [new_rule],
        parameters=dict(grammar.parameters),
        parent_id=grammar.grammar_id,
    )


def drop_rule(grammar: Grammar) -> Grammar:
    """Remove a random rule (never drops the first rule — assumed to be start)."""
    if len(grammar.rules) <= 1:
        return Grammar(
            grammar_id=f"{grammar.grammar_id}_noop",
            grammar_version=grammar.grammar_version,
            rules=list(grammar.rules),
            parameters=dict(grammar.parameters),
            parent_id=grammar.grammar_id,
        )
    idx = random.randint(1, len(grammar.rules) - 1)
    new_rules = grammar.rules[:idx] + grammar.rules[idx + 1:]
    return Grammar(
        grammar_id=f"{grammar.grammar_id}_drop_{_new_id()}",
        grammar_version=grammar.grammar_version,
        rules=new_rules,
        parameters=dict(grammar.parameters),
        parent_id=grammar.grammar_id,
    )


def rename_terminal(grammar: Grammar, old: str = "IDENT", new: str = "NAME") -> Grammar:
    """Rename a terminal token class throughout all rules."""
    new_rules = [r.replace(old, new) for r in grammar.rules]
    return Grammar(
        grammar_id=f"{grammar.grammar_id}_rename_{_new_id()}",
        grammar_version=grammar.grammar_version,
        rules=new_rules,
        parameters=dict(grammar.parameters),
        parent_id=grammar.grammar_id,
    )


def relax_quantifier(grammar: Grammar) -> Grammar:
    """Replace a '+' or '?' quantifier with '*' in a random rule."""
    new_rules = list(grammar.rules)
    for i, rule in enumerate(new_rules):
        if "+" in rule or "?" in rule:
            rule = rule.replace("+", "*", 1)
            rule = rule.replace("?", "*", 1)
            new_rules[i] = rule
            break
    return Grammar(
        grammar_id=f"{grammar.grammar_id}_relax_{_new_id()}",
        grammar_version=grammar.grammar_version,
        rules=new_rules,
        parameters=dict(grammar.parameters),
        parent_id=grammar.grammar_id,
    )


def tighten_quantifier(grammar: Grammar) -> Grammar:
    """Replace a '*' quantifier with '+' in a random rule."""
    new_rules = list(grammar.rules)
    for i, rule in enumerate(new_rules):
        if "*" in rule:
            new_rules[i] = rule.replace("*", "+", 1)
            break
    return Grammar(
        grammar_id=f"{grammar.grammar_id}_tighten_{_new_id()}",
        grammar_version=grammar.grammar_version,
        rules=new_rules,
        parameters=dict(grammar.parameters),
        parent_id=grammar.grammar_id,
    )


def swap_alternatives(grammar: Grammar) -> Grammar:
    """Swap two alternatives in a rule that contains '|'."""
    new_rules = list(grammar.rules)
    for i, rule in enumerate(new_rules):
        if "|" in rule:
            lhs, rest = rule.split("::=", 1)
            parts = rest.split("|")
            if len(parts) >= 2:
                parts[0], parts[1] = parts[1], parts[0]
                new_rules[i] = lhs + "::=" + "|".join(parts)
                break
    return Grammar(
        grammar_id=f"{grammar.grammar_id}_swap_{_new_id()}",
        grammar_version=grammar.grammar_version,
        rules=new_rules,
        parameters=dict(grammar.parameters),
        parent_id=grammar.grammar_id,
    )


# ---------------------------------------------------------------------------
# Mutation dispatcher
# ---------------------------------------------------------------------------

MUTATION_OPS = [
    add_rule,
    drop_rule,
    relax_quantifier,
    tighten_quantifier,
    swap_alternatives,
]


def mutate_grammar(grammar: Grammar, rng: Optional[random.Random] = None) -> Grammar:
    """Apply a single random mutation operation to grammar."""
    rng = rng or random
    op = rng.choice(MUTATION_OPS)
    return op(grammar)


def mutate_n(grammar: Grammar, n: int) -> list[Grammar]:
    """Produce n distinct mutations of grammar."""
    return [mutate_grammar(grammar) for _ in range(n)]
