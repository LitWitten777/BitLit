"""Domain: sign laws of the Cayley–Dickson basis.

In the Cayley–Dickson algebra of dimension ``2ⁿ`` the canonical basis multiplies as
``e_a e_b = σₙ(a, b) e_{a ⊕ b}`` with ``σₙ(a, b) = ±1`` (``Discovery.cdSign``; the bridge
theorem ``Discovery.cdMul_basis`` ties it to the actual product).  A *sign law* is a claim

    ∀ i j k < 2ⁿ,  E₁ ≠ 0 ∧ … ∧ E_s ≠ 0 → σₙ(A₁, B₁) · … · σₙ(A_r, B_r) = ±1

where every ``A``, ``B``, ``E`` is a non-empty xor of the variables ``i, j, k``.  Commutation,
associativity, alternativity, flexibility and Moufang-type laws of basis elements, and the
cocycle law of ``σ``, are all of this shape.

Genome: ``(level, factors, target, conds)``; an index expression is a bit mask over the
variables (bit 0 = ``i``, bit 1 = ``j``, bit 2 = ``k``).

Ladder: the same law at levels ``1, …, 5``.  Because ``σₙ₊₁`` restricted to indices ``< 2ⁿ``
is ``σₙ``, a law that fails at level ``n`` fails at every higher level, so the ladder is
monotone.  The first false rung is where the law breaks along the tower
ℝ ⊂ ℂ ⊂ ℍ ⊂ 𝕆 ⊂ 𝕊 ⊂ (32-dim).
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from functools import lru_cache

from .base import Domain

MAX_LEVEL = 5
VARS = ("i", "j", "k")
MASKS = tuple(range(1, 8))
MAX_FACTORS = 6


@lru_cache(maxsize=None)
def cd_sign(n: int, i: int, j: int) -> int:
    """Python twin of ``Discovery.cdSign`` (same recursion, line by line)."""
    if n == 0:
        return 1
    h = 1 << (n - 1)
    if i < h:
        return cd_sign(n - 1, i, j) if j < h else cd_sign(n - 1, j - h, i)
    if j < h:
        return cd_sign(n - 1, i - h, j) if j == 0 else -cd_sign(n - 1, i - h, j)
    inner = cd_sign(n - 1, j - h, i - h) if j - h == 0 else -cd_sign(n - 1, j - h, i - h)
    return -inner


def eval_mask(mask: int, vals: tuple) -> int:
    out = 0
    for b in range(3):
        if mask >> b & 1:
            out ^= vals[b]
    return out


def mask_lean(mask: int, names=VARS) -> str:
    parts = [names[b] for b in range(3) if mask >> b & 1]
    return parts[0] if len(parts) == 1 else "(" + " ^^^ ".join(parts) + ")"


def permute_mask(mask: int, perm: tuple) -> int:
    """``perm[b]`` is the new bit position of old variable ``b``."""
    out = 0
    for b in range(3):
        if mask >> b & 1:
            out |= 1 << perm[b]
    return out


def gf2_basis(masks: list) -> list:
    """A basis of the GF(2)-span of ``masks``, chosen deterministically: scan the masks in the
    given order (duplicates ignored) and keep each one independent of those kept so far."""
    chosen, span = [], {0}
    for m in dict.fromkeys(masks):
        if m not in span:
            chosen.append(m)
            span |= {s ^ m for s in span}
    return chosen


def gf2_coords(mask: int, basis: list) -> int:
    """Coordinates of ``mask`` in ``basis`` (bit t ↔ basis[t]); ``mask`` must lie in the span."""
    r = len(basis)
    for c in range(1, 1 << r):
        v = 0
        for t in range(r):
            if c >> t & 1:
                v ^= basis[t]
        if v == mask:
            return c
    raise ValueError("mask outside span")


@dataclass(frozen=True, order=True)
class SignLaw:
    level: int
    factors: tuple          # tuple of (mask_a, mask_b)
    target: int             # +1 or -1
    conds: tuple            # sorted tuple of masks m, each meaning "expr(m) ≠ 0"

    @property
    def var_mask(self) -> int:
        m = 0
        for a, b in self.factors:
            m |= a | b
        for c in self.conds:
            m |= c
        return m


class CDSignDomain(Domain):
    name = "cd_signs"
    lean_prefix = "cdsign"

    # -- genome space -----------------------------------------------------------------
    def random_genome(self, rng) -> SignLaw:
        r = rng.randint(1, 4)
        factors = tuple((rng.choice(MASKS), rng.choice(MASKS)) for _ in range(r))
        conds = tuple(sorted({rng.choice(MASKS) for _ in range(rng.randint(0, 3))}))
        return SignLaw(rng.randint(2, MAX_LEVEL), factors, rng.choice((1, -1)), conds)

    def mutate(self, g: SignLaw, rng) -> SignLaw:
        level, factors, target, conds = g.level, list(g.factors), g.target, set(g.conds)
        move = rng.randrange(6)
        if move == 0:
            level = min(MAX_LEVEL, max(1, level + rng.choice((-1, 1))))
        elif move == 1 and factors:
            idx = rng.randrange(len(factors))
            a, b = factors[idx]
            factors[idx] = (rng.choice(MASKS), b) if rng.random() < 0.5 else (a, rng.choice(MASKS))
        elif move == 2 and len(factors) < MAX_FACTORS:
            factors.append((rng.choice(MASKS), rng.choice(MASKS)))
        elif move == 3 and len(factors) > 1:
            factors.pop(rng.randrange(len(factors)))
        elif move == 4:
            target = -target
        else:
            m = rng.choice(MASKS)
            conds.symmetric_difference_update({m})
        return SignLaw(level, tuple(factors), target, tuple(sorted(conds)))

    def canonical(self, g: SignLaw):
        # σ(a, b)² = 1: cancel equal factors in pairs
        counts = {}
        for f in g.factors:
            counts[f] = counts.get(f, 0) + 1
        factors = tuple(sorted(f for f, c in counts.items() if c % 2 == 1))
        if not factors:
            return None
        used = 0
        for a, b in factors:
            used |= a | b
        conds = tuple(sorted({m for m in g.conds if m & ~used == 0}))
        # change of variables over GF(2): if the index expressions span a space of rank r
        # smaller than the number of variables, rewrite them in r fresh variables.  The map
        # x ↦ (b₁·x, …, b_r·x) onto the coordinates of a basis is surjective, so the claim is
        # equivalent.  This also compacts unused variables.
        # factor masks first (so the law itself is written in plain variables when possible)
        basis = gf2_basis(sorted({m for f in factors for m in f}) + sorted(conds))
        coords = lambda m: gf2_coords(m, basis)
        factors = tuple(sorted((coords(a), coords(b)) for a, b in factors))
        conds = tuple(sorted({coords(m) for m in conds}))
        # a hypothesis "0 ≠ 0" cannot occur (all masks are non-zero), and a duplicated factor
        # pair may appear after the change of variables: cancel again
        counts = {}
        for f in factors:
            counts[f] = counts.get(f, 0) + 1
        factors = tuple(sorted(f for f, c in counts.items() if c % 2 == 1))
        if not factors:
            return None
        return SignLaw(g.level, factors, g.target, conds)

    def key(self, g: SignLaw) -> str:
        c = self.canonical(g)
        if c is None:
            return "trivial"
        nv = bin(c.var_mask).count("1")
        best = None
        for p in itertools.permutations(range(nv)):
            perm = tuple(list(p) + list(range(nv, 3)))
            fs = tuple(sorted((permute_mask(a, perm), permute_mask(b, perm)) for a, b in c.factors))
            cs = tuple(sorted(permute_mask(m, perm) for m in c.conds))
            cand = (c.level, fs, c.target, cs)
            best = cand if best is None or cand < best else best
        return "cd:" + repr(best)

    def complexity(self, g: SignLaw) -> float:
        c = self.canonical(g) or g
        return len(c.factors) + 0.5 * len(c.conds) + 0.5 * bin(c.var_mask).count("1")

    # -- instance space ---------------------------------------------------------------
    def _nvars(self, g):
        return max(1, (g.var_mask.bit_length()))

    def instances(self, g: SignLaw):
        nv = self._nvars(g)
        size = 1 << g.level
        for vals in itertools.product(range(size), repeat=nv):
            yield tuple(vals) + (0,) * (3 - nv)

    def random_instance(self, g: SignLaw, rng):
        nv = self._nvars(g)
        size = 1 << g.level
        return tuple(rng.randrange(size) for _ in range(nv)) + (0,) * (3 - nv)

    def boundary_instances(self, g: SignLaw):
        nv = self._nvars(g)
        size = 1 << g.level
        edge = sorted({0, 1, size - 1, size >> 1, (size >> 1) - 1 if size > 1 else 0})
        for vals in itertools.product(edge, repeat=nv):
            yield tuple(vals) + (0,) * (3 - nv)

    def premise(self, g: SignLaw, x) -> bool:
        return all(eval_mask(m, x) != 0 for m in g.conds)

    def conclusion(self, g: SignLaw, x) -> bool:
        prod = 1
        for a, b in g.factors:
            prod *= cd_sign(g.level, eval_mask(a, x), eval_mask(b, x))
        return prod == g.target

    def support_ok(self, g: SignLaw, support: int) -> bool:
        # a law must constrain at least a quarter of its instance space (and 4 instances)
        nv = self._nvars(g)
        return support >= max(4, (1 << (g.level * nv)) // 4)

    def generalizations(self, g: SignLaw):
        return [SignLaw(g.level, g.factors, g.target, tuple(m for m in g.conds if m != d))
                for d in g.conds]

    def is_composite(self, g: SignLaw) -> bool:
        """A law is composite if some proper, non-empty sub-product of its factors is constant
        on the premise set: then the law is the product of two shorter true laws.  Checked at
        level ``min(level, 3)`` (a cheap heuristic: this screen only affects which claims are
        promoted, never their truth)."""
        lv = min(g.level, 3)
        h = SignLaw(lv, g.factors, g.target, g.conds)
        xs = [x for x in self.instances(h) if self.premise(h, x)]
        r = len(g.factors)
        if r < 2 or not xs:
            return False
        vals = [[cd_sign(lv, eval_mask(a, x), eval_mask(b, x)) for a, b in g.factors] for x in xs]
        for sub in range(1, (1 << r) - 1):
            if not sub & 1:      # each partition once: the subset containing factor 0
                continue
            prods = set()
            for v in vals:
                p = 1
                for t in range(r):
                    if sub >> t & 1:
                        p *= v[t]
                prods.add(p)
                if len(prods) > 1:
                    break
            if len(prods) == 1:
                return True
        return False

    def interest(self, g: SignLaw) -> float:
        return 0.5 * g.level

    def ladder(self, g: SignLaw):
        return [SignLaw(n, g.factors, g.target, g.conds) for n in range(1, MAX_LEVEL + 1)]

    # -- presentation -----------------------------------------------------------------
    def describe(self, g: SignLaw) -> str:
        nv = self._nvars(g)
        names = VARS[:nv]
        prod = " · ".join(f"σ({mask_lean(a)}, {mask_lean(b)})" for a, b in g.factors)
        conds = ", ".join(f"{mask_lean(m)} ≠ 0" for m in g.conds)
        alg = {1: "ℂ", 2: "ℍ", 3: "𝕆", 4: "𝕊", 5: "32-dim CD"}.get(g.level, f"level {g.level}")
        head = f"[{alg}, dim {1 << g.level}] ∀ {' '.join(names)}"
        return f"{head}{(' with ' + conds) if conds else ''}: {prod} = {g.target:+d}"

    def lean_statement(self, g: SignLaw) -> str:
        nv = self._nvars(g)
        size = 1 << g.level
        binders = ", ".join(f"∀ {v} < {size}" for v in VARS[:nv])
        # hypotheses as one conjunction (a long chain of implications defeats instance search
        # for `Decidable`)
        hyps = " ∧ ".join(f"{mask_lean(m)} ≠ 0" for m in g.conds)
        hyps = hyps + " → " if hyps else ""
        prod = " * ".join(f"cdSign {g.level} {mask_lean(a)} {mask_lean(b)}" for a, b in g.factors)
        rhs = "1" if g.target == 1 else "-1"
        return f"{binders}, {hyps}{prod} = {rhs}"

    def lean_refutation(self, g: SignLaw, x) -> str:
        nv = self._nvars(g)
        args = " ".join(f"{x[b]} (by decide)" for b in range(nv))
        hyp_args = " (by decide)" if g.conds else ""
        return f"fun h => absurd (h {args}{hyp_args}) (by decide +kernel)"

    def describe_instance(self, g: SignLaw, x) -> str:
        nv = self._nvars(g)
        return ", ".join(f"{VARS[b]} = {x[b]}" for b in range(nv))
