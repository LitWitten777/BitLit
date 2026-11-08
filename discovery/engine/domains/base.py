"""Interface of a conjecture domain.

A domain supplies a genome space (the mutation engine searches it), a finite instance space per
genome (the falsification arbiter searches it), and a renderer to closed Lean statements written
in the vocabulary of ``Discovery.Kernel`` (the Lean kernel decides them).

Conventions
-----------
* A genome is an immutable, hashable value.  ``canonical(g)`` returns its normal form, or
  ``None`` when the claim is trivial (e.g. an empty product of signs).
* ``instances(g)`` enumerates the *whole* finite instance space of the claim, so the arbiter can
  be exhaustive; ``random_instance`` and ``boundary_instances`` serve the cheaper fuzzing
  stages that run first.
* ``premise(g, x)`` is the hypothesis of the claim at instance ``x`` and ``conclusion(g, x)`` its
  conclusion; the claim is ``∀ x, premise → conclusion``.
* ``ladder(g)`` is a list of claims of increasing strength that contains ``g`` and is
  *monotone*: if a rung is false, every later rung is false.  The arbiter uses it to turn each
  survivor into a sharp pair "strongest true rung / first false rung" (the counter-hypothesis).
* ``lean_statement(g)`` is a closed Lean proposition; the kernel proves it with
  ``decide +kernel``.  ``lean_refutation(g, x)`` is a proof term of its negation from the
  counterexample ``x``.
"""

from __future__ import annotations

from typing import Iterable, Iterator, Optional


class Domain:
    name = "abstract"
    lean_prefix = "disc"
    #: null-hypothesis screen: a true claim is promoted only if ``surprise_bits`` reaches this
    min_surprise = 0.0
    #: vacuity screen: the premise must hold on at least this many instances
    min_support = 1

    # -- genome space -----------------------------------------------------------------
    def random_genome(self, rng):
        raise NotImplementedError

    def mutate(self, g, rng):
        raise NotImplementedError

    def canonical(self, g):
        return g

    def key(self, g) -> str:
        return repr(self.canonical(g))

    def complexity(self, g) -> float:
        return 1.0

    # -- instance space ---------------------------------------------------------------
    def instances(self, g) -> Iterator:
        raise NotImplementedError

    def random_instance(self, g, rng):
        raise NotImplementedError

    def boundary_instances(self, g) -> Iterable:
        return []

    def premise(self, g, x) -> bool:
        return True

    def conclusion(self, g, x) -> bool:
        raise NotImplementedError

    # -- counter-hypotheses and null models --------------------------------------------
    def ladder(self, g) -> list:
        return [g]

    def next_rung(self, g):
        """The rung just above ``g`` on its ladder (``None`` at the top)."""
        rungs = [self.canonical(r) for r in self.ladder(g)]
        c = self.canonical(g)
        for a, b in zip(rungs, rungs[1:]):
            if a == c:
                return b
        return None

    def surprise_bits(self, g) -> Optional[float]:
        """Null-model surprise of a true claim (``None``: no null model for this domain)."""
        return None

    def support_ok(self, g, support: int) -> bool:
        """Vacuity screen: is the premise met on enough instances?"""
        return support >= self.min_support

    def generalizations(self, g) -> list:
        """Strictly stronger variants of ``g`` (e.g. with one hypothesis dropped); the arbiter
        greedily replaces a survivor by a true generalization."""
        return []

    def is_composite(self, g) -> bool:
        """Irreducibility screen: is the true claim ``g`` merely a combination of simpler true
        claims?  (Default: never.)"""
        return False

    def interest(self, g) -> float:
        """Domain-specific bonus in the annealer's energy (default 0)."""
        return 0.0

    # -- presentation -----------------------------------------------------------------
    def describe(self, g) -> str:
        return repr(g)

    def lean_statement(self, g) -> str:
        raise NotImplementedError

    def lean_refutation(self, g, x) -> str:
        raise NotImplementedError

    def describe_instance(self, g, x) -> str:
        return repr(x)
