"""
Rewriting rules for braid words, with provenance.

The three fundamental relations (QBX.md §5, §21):

1. R01 Inverse cancellation:  σ_i^e σ_i^{-e} → ε
2. R02 Far commutation:       σ_i^a σ_j^b → σ_j^b σ_i^a   for |i - j| ≥ 2
3. R03 Yang–Baxter:           σ_i^e σ_{i+1}^e σ_i^e ⇄ σ_{i+1}^e σ_i^e σ_{i+1}^e

Every rule declares the semantics it preserves (QBX.md §22).  The claim
"rule preserves braid_group_element / permutation / writhe" is proved for
all n in the Lean library ``QBX/Formal`` (theorem names in ``lean_theorem``);
:func:`audit_transformation` re-checks the declaration at runtime.

Two engines are provided:

- :func:`normal_form` — a *terminating* reduction (R01 plus R02 oriented to
  sort indices).  It never loops, but it is not canonical for B_n.
- :func:`qbx_ir.algebra.garside.garside_normal_form` — the exact, canonical
  Garside normal form, used for WORD equality.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Tuple

from qbx_ir.core.braid import Braid
from qbx_ir.core.primitive import Generator


@dataclass(frozen=True)
class RewriteRule:
    name: str
    description: str
    preserved: Tuple[str, ...]
    changed: Tuple[str, ...]
    lean_theorem: str = ""


_PRESERVED = ("braid_group_element", "strand_count", "permutation", "writhe")

INVERSE_CANCELLATION = RewriteRule(
    name="R01",
    description="σ_i^e σ_i^{-e} → ε",
    preserved=_PRESERVED,
    changed=("word_length",),
    lean_theorem="QBX.Formal.Step.eval_eq",
)

FAR_COMMUTATION = RewriteRule(
    name="R02",
    description="σ_i^a σ_j^b → σ_j^b σ_i^a  for |i - j| ≥ 2",
    preserved=_PRESERVED,
    changed=("word_order",),
    lean_theorem="QBX.Formal.Step.eval_eq",
)

YANG_BAXTER = RewriteRule(
    name="R03",
    description="σ_i^e σ_{i+1}^e σ_i^e ⇄ σ_{i+1}^e σ_i^e σ_{i+1}^e",
    preserved=_PRESERVED,
    changed=("word_order", "crossing_positions"),
    lean_theorem="QBX.Formal.Step.eval_eq",
)

ALL_RULES: Tuple[RewriteRule, ...] = (INVERSE_CANCELLATION, FAR_COMMUTATION, YANG_BAXTER)


# ---------------------------------------------------------------------------
# Provenance
# ---------------------------------------------------------------------------

def braid_hash(braid: Braid) -> str:
    """SHA3-256 of the canonical JSON of (strand_count, word)."""
    payload = json.dumps(
        {"n": braid.strand_count, "word": braid.short_form()},
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha3_256(payload).hexdigest()


@dataclass(frozen=True)
class Transformation:
    """Provenance record of a single rewrite (QBX.md §22)."""

    input_hash: str
    rule_id: str
    position: int
    output_hash: str
    preserved_properties: Tuple[str, ...]
    changed_properties: Tuple[str, ...]
    input_word: Tuple[int, ...] = field(default=())
    output_word: Tuple[int, ...] = field(default=())

    def to_dict(self) -> Dict[str, object]:
        return {
            "input_hash": self.input_hash,
            "rule_id": self.rule_id,
            "position": self.position,
            "output_hash": self.output_hash,
            "preserved_properties": list(self.preserved_properties),
            "changed_properties": list(self.changed_properties),
            "input_word": list(self.input_word),
            "output_word": list(self.output_word),
        }


# ---------------------------------------------------------------------------
# Pattern matchers: (word, start) -> (end, replacement) or None
# ---------------------------------------------------------------------------

Match = Optional[Tuple[int, List[Generator]]]


def _match_r01(word: List[Generator], start: int) -> Match:
    if start + 1 >= len(word):
        return None
    a, b = word[start], word[start + 1]
    if a.index == b.index and a.sign == -b.sign:
        return start + 2, []
    return None


def _match_r02(word: List[Generator], start: int) -> Match:
    if start + 1 >= len(word):
        return None
    a, b = word[start], word[start + 1]
    if abs(a.index - b.index) >= 2:
        return start + 2, [b, a]
    return None


def _match_r02_sorting(word: List[Generator], start: int) -> Match:
    """R02 oriented so that the smaller index moves left (terminating)."""
    if start + 1 >= len(word):
        return None
    a, b = word[start], word[start + 1]
    if a.index >= b.index + 2:
        return start + 2, [b, a]
    return None


def _match_r03(word: List[Generator], start: int) -> Match:
    if start + 2 >= len(word):
        return None
    a, b, c = word[start], word[start + 1], word[start + 2]
    if not (a.sign == b.sign == c.sign and a.index == c.index):
        return None
    if abs(a.index - b.index) != 1:
        return None
    e = a.sign
    return start + 3, [Generator(b.index, e), Generator(a.index, e), Generator(b.index, e)]


_MATCHERS: Dict[str, Callable[[List[Generator], int], Match]] = {
    "R01": _match_r01,
    "R02": _match_r02,
    "R03": _match_r03,
}


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def find_matches(braid: Braid, rule: RewriteRule) -> List[int]:
    """All positions at which ``rule`` applies."""
    matcher = _MATCHERS[rule.name]
    word = list(braid.word)
    return [k for k in range(len(word)) if matcher(word, k) is not None]


def apply_rule(braid: Braid, rule: RewriteRule, position: int) -> Tuple[Braid, Transformation]:
    """Apply ``rule`` at ``position``; returns the new braid and its provenance."""
    matcher = _MATCHERS[rule.name]
    word = list(braid.word)
    m = matcher(word, position)
    if m is None:
        raise ValueError(f"Rule {rule.name} does not apply at position {position}")
    end, replacement = m
    out = braid.with_word(word[:position] + replacement + word[end:],
                          name=f"{braid.name}→{rule.name}")
    t = Transformation(
        input_hash=braid_hash(braid),
        rule_id=rule.name,
        position=position,
        output_hash=braid_hash(out),
        preserved_properties=rule.preserved,
        changed_properties=rule.changed,
        input_word=tuple(braid.short_form()),
        output_word=tuple(out.short_form()),
    )
    return out, t


def insert_cancelling_pair(braid: Braid, position: int, index: int, sign: int = 1) -> Braid:
    """Inverse of R01: insert σ_index^{sign} σ_index^{-sign} at ``position``."""
    word = list(braid.word)
    g = Generator(index, sign)
    return braid.with_word(word[:position] + [g, g.inverse()] + word[position:])


def _reduce_once(braid: Braid) -> Optional[Tuple[Braid, Transformation]]:
    word = list(braid.word)
    for k in range(len(word)):
        if _match_r01(word, k) is not None:
            return apply_rule(braid, INVERSE_CANCELLATION, k)
    for k in range(len(word)):
        m = _match_r02_sorting(word, k)
        if m is not None:
            return apply_rule(braid, FAR_COMMUTATION, k)
    return None


def rewrite_step(braid: Braid) -> Optional[Braid]:
    """
    One step of the terminating reduction: an R01 cancellation if any,
    otherwise one sorting R02 swap.  Returns None at a fixed point.
    """
    r = _reduce_once(braid)
    return None if r is None else r[0]


def normal_form_with_trace(
    braid: Braid, max_iterations: int = 100000
) -> Tuple[Braid, List[Transformation]]:
    """Reduce to a fixed point, recording every transformation."""
    trace: List[Transformation] = []
    current = braid
    for _ in range(max_iterations):
        r = _reduce_once(current)
        if r is None:
            return current, trace
        current, t = r
        trace.append(t)
    raise RuntimeError(f"Rewriting did not terminate in {max_iterations} iterations")


def normal_form(braid: Braid, max_iterations: int = 100000) -> Braid:
    """
    Apply R01 and sorting-R02 until a fixed point is reached.

    This always terminates: R01 shortens the word and sorting-R02 strictly
    decreases the number of out-of-order commuting pairs.  It is NOT a
    canonical form of the braid group (R03 is not oriented); for exact
    equality use :func:`qbx_ir.algebra.garside.garside_normal_form`.
    """
    return normal_form_with_trace(braid, max_iterations)[0]


def audit_transformation(before: Braid, after: Braid, rule: RewriteRule) -> Dict[str, bool]:
    """Re-check each declared preserved property on a concrete rewrite."""
    from qbx_ir.algebra.garside import braid_group_equal
    from qbx_ir.algebra.invariants import permutation, writhe

    checks = {
        "braid_group_element": lambda: braid_group_equal(before, after),
        "strand_count": lambda: before.strand_count == after.strand_count,
        "permutation": lambda: permutation(before) == permutation(after),
        "writhe": lambda: writhe(before) == writhe(after),
    }
    return {p: checks[p]() for p in rule.preserved if p in checks}


def yang_baxter_pair(n: int = 3, i: int = 1) -> Tuple[Braid, Braid]:
    """
    Return the Yang–Baxter pair (σ_i σ_{i+1} σ_i, σ_{i+1} σ_i σ_{i+1}).
    """
    if i + 1 >= n:
        raise ValueError(f"Cannot build YB pair for i={i}, n={n}")
    lhs = Braid.from_short_form(n, [i, i + 1, i])
    rhs = Braid.from_short_form(n, [i + 1, i, i + 1])
    return lhs, rhs
