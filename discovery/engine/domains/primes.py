"""Domains about primes.

``QuadFormDomain`` — which primes in a residue class are represented by ``a x² + b y²``?

    ∀ p < N,  isPrimeB p = true → p % m = r → ∃ x < X, ∃ y < X, a·x·x + b·y·y = p

Fermat's two-square theorem (``a = b = 1``, ``p ≡ 1 mod 4``), ``x² + 2y²`` (``p ≡ 1, 3 mod 8``),
``x² + 3y²`` (``p ≡ 1 mod 3``) and ``x² + 7y²`` are of this shape, and so are their failures
(``x² + 5y²`` misses ``p ≡ 3, 7 mod 20``: genus theory).  Ladder: ``N = 100, 200, 400, 800``
(monotone: a counterexample below ``N`` is one below every larger bound).  Screens: the class
must be coprime to ``m`` and contain at least ``MIN_SUPPORT`` primes below ``N``; null model:
if representability by the form were independent of the residue class, each of the ``s``
primes of the class would be represented with probability ``d`` = the fraction of all primes
below ``N`` represented by the form, so the claim carries ``-s·log₂ d`` bits of surprise; at
least ``QUAD_MIN_SURPRISE_BITS`` are required.

``PrimePolyDomain`` — prime-producing quadratics ``n² + b n + c``:

    ∀ n < L,  isPrimeB (n * n + b * n + c) = true

For each ``(b, c)`` the ladder is ``L = 1, 2, …``; the arbiter finds the longest true run and the
first composite value (e.g. Euler's ``n² + n + 41``: ``L = 40``, broken at ``n = 40``).  Null
screen: the run must carry at least ``MIN_SURPRISE_BITS`` of surprise against the heuristic
"a random integer near v is prime with probability 1/ln v".
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from functools import lru_cache

from .base import Domain

MIN_SUPPORT = 4
MIN_SURPRISE_BITS = 20.0
QUAD_MIN_SURPRISE_BITS = 12.0


@lru_cache(maxsize=None)
def is_prime(n: int) -> bool:
    """Python twin of ``Discovery.isPrimeB`` (trial division)."""
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


# ---------------------------------------------------------------------------
# a x² + b y²  on a residue class of primes
# ---------------------------------------------------------------------------

BOUNDS = (100, 200, 400, 800)


@dataclass(frozen=True, order=True)
class QuadClaim:
    a: int
    b: int
    m: int
    r: int
    N: int

    @property
    def X(self) -> int:
        return math.isqrt(self.N // min(self.a, self.b)) + 1


class QuadFormDomain(Domain):
    name = "quad_forms"
    lean_prefix = "quadform"
    min_support = MIN_SUPPORT
    min_surprise = QUAD_MIN_SURPRISE_BITS

    def random_genome(self, rng) -> QuadClaim:
        m = rng.randint(3, 40)
        return QuadClaim(rng.randint(1, 8), rng.randint(1, 12), m, rng.randrange(m), rng.choice(BOUNDS))

    def mutate(self, g: QuadClaim, rng) -> QuadClaim:
        a, b, m, r, N = g.a, g.b, g.m, g.r, g.N
        move = rng.randrange(5)
        if move == 0:
            a = max(1, min(12, a + rng.choice((-1, 1))))
        elif move == 1:
            b = max(1, min(16, b + rng.choice((-2, -1, 1, 2))))
        elif move == 2:
            m = max(3, min(48, m + rng.choice((-4, -1, 1, 4))))
            r = r % m
        elif move == 3:
            r = (r + rng.randrange(1, m)) % m
        else:
            N = rng.choice(BOUNDS)
        return QuadClaim(a, b, m, r, N)

    def canonical(self, g: QuadClaim):
        a, b = sorted((g.a, g.b))
        if math.gcd(g.r % g.m, g.m) != 1:
            return None  # class with at most one prime: nothing to conjecture
        return QuadClaim(a, b, g.m, g.r % g.m, g.N)

    def key(self, g: QuadClaim) -> str:
        c = self.canonical(g)
        return "trivial" if c is None else "qf:" + repr((c.a, c.b, c.m, c.r, c.N))

    def complexity(self, g: QuadClaim) -> float:
        return math.log2(g.a * g.b * g.m + 1)

    def instances(self, g: QuadClaim):
        return iter(range(g.N))

    def random_instance(self, g: QuadClaim, rng):
        # sample primes of the class preferentially (the premise is otherwise rarely met)
        cands = [p for p in range(g.r, g.N, g.m) if is_prime(p)]
        return rng.choice(cands) if cands and rng.random() < 0.9 else rng.randrange(g.N)

    def boundary_instances(self, g: QuadClaim):
        return [p for p in (2, 3, 5, 7, g.m - 1, g.m + 1, g.N - 1) if 0 <= p < g.N]

    def premise(self, g: QuadClaim, p) -> bool:
        return is_prime(p) and p % g.m == g.r

    def conclusion(self, g: QuadClaim, p) -> bool:
        X = g.X
        return any(g.a * x * x + g.b * y * y == p for x in range(X) for y in range(X))

    def support(self, g: QuadClaim) -> int:
        return sum(1 for p in range(g.N) if self.premise(g, p))

    def generalizations(self, g: QuadClaim):
        """Coarser residue classes: ``p ≡ r (mod d)`` for every proper divisor ``d ≥ 2`` of
        ``m`` (a stronger claim)."""
        return [QuadClaim(g.a, g.b, d, g.r % d, g.N) for d in range(2, g.m) if g.m % d == 0]

    def represented(self, g: QuadClaim, p: int) -> bool:
        return self.conclusion(g, p)

    def surprise_bits(self, g: QuadClaim) -> float:
        primes = [p for p in range(g.N) if is_prime(p)]
        d = sum(1 for p in primes if self.represented(g, p)) / len(primes)
        if d >= 1.0:
            return 0.0
        if d <= 0.0:
            return float("inf")
        return -self.support(g) * math.log2(d)

    def interest(self, g: QuadClaim) -> float:
        return min(3.0, self.support(g) / 8.0)

    def ladder(self, g: QuadClaim):
        return [QuadClaim(g.a, g.b, g.m, g.r, N) for N in BOUNDS]

    def describe(self, g: QuadClaim) -> str:
        a = "" if g.a == 1 else str(g.a)
        b = "" if g.b == 1 else str(g.b)
        return f"every prime p < {g.N} with p ≡ {g.r} (mod {g.m}) is of the form {a}x² + {b}y²"

    def lean_statement(self, g: QuadClaim) -> str:
        X = g.X
        a = "" if g.a == 1 else f"{g.a} * "
        b = "" if g.b == 1 else f"{g.b} * "
        return (f"∀ p < {g.N}, isPrimeB p = true → p % {g.m} = {g.r} → "
                f"∃ x < {X}, ∃ y < {X}, {a}x * x + {b}y * y = p")

    def lean_refutation(self, g: QuadClaim, p) -> str:
        return f"fun h => absurd (h {p} (by decide) (by decide +kernel) (by decide)) (by decide +kernel)"

    def describe_instance(self, g: QuadClaim, p) -> str:
        return f"p = {p}"


# ---------------------------------------------------------------------------
# prime-producing quadratics
# ---------------------------------------------------------------------------

MAX_RUN = 64


@dataclass(frozen=True, order=True)
class PolyClaim:
    b: int
    c: int
    L: int


class PrimePolyDomain(Domain):
    name = "prime_poly"
    lean_prefix = "primepoly"
    min_surprise = MIN_SURPRISE_BITS

    def value(self, g, n) -> int:
        return n * n + g.b * n + g.c

    def run_length(self, b: int, c: int) -> int:
        n = 0
        while n < MAX_RUN and is_prime(n * n + b * n + c):
            n += 1
        return n

    def random_genome(self, rng) -> PolyClaim:
        return PolyClaim(rng.randint(0, 30), rng.randint(1, 500), rng.randint(1, 20))

    def mutate(self, g: PolyClaim, rng) -> PolyClaim:
        b, c, L = g.b, g.c, g.L
        move = rng.randrange(4)
        if move == 0:
            b = max(0, min(40, b + rng.choice((-2, -1, 1, 2))))
        elif move == 1:
            c = max(1, min(1000, c + rng.choice((-10, -2, -1, 1, 2, 10))))
        elif move == 2:
            c = max(1, min(1000, c + rng.randint(-100, 100)))
        else:
            L = max(1, min(MAX_RUN, L + rng.choice((-5, -1, 1, 5))))
        return PolyClaim(b, c, L)

    def canonical(self, g: PolyClaim):
        return g

    def key(self, g: PolyClaim) -> str:
        # the interesting object is the polynomial; the ladder fixes the run length
        return "pp:" + repr((g.b, g.c))

    def complexity(self, g: PolyClaim) -> float:
        return math.log2(g.b + 2) + math.log2(g.c + 1)

    def instances(self, g: PolyClaim):
        return iter(range(g.L))

    def random_instance(self, g: PolyClaim, rng):
        return rng.randrange(g.L)

    def boundary_instances(self, g: PolyClaim):
        return sorted({0, 1, g.L - 1, g.c % max(1, g.L)} & set(range(g.L)))

    def conclusion(self, g: PolyClaim, n) -> bool:
        return is_prime(self.value(g, n))

    def surprise_bits(self, g: PolyClaim) -> float:
        bits = 0.0
        for n in range(g.L):
            v = self.value(g, n)
            p = min(1.0, 1.0 / math.log(max(v, 3)))
            bits += -math.log2(p)
        return bits

    def interest(self, g: PolyClaim) -> float:
        return self.run_length(g.b, g.c) / 8.0

    def ladder(self, g: PolyClaim):
        top = min(MAX_RUN, self.run_length(g.b, g.c) + 1)
        return [PolyClaim(g.b, g.c, L) for L in range(1, max(top, g.L) + 1)]

    def describe(self, g: PolyClaim) -> str:
        return f"n² + {g.b}n + {g.c} is prime for every n < {g.L}"

    def lean_statement(self, g: PolyClaim) -> str:
        return f"∀ n < {g.L}, isPrimeB (n * n + {g.b} * n + {g.c}) = true"

    def lean_refutation(self, g: PolyClaim, n) -> str:
        return f"fun h => absurd (h {n} (by decide)) (by decide +kernel)"

    def describe_instance(self, g: PolyClaim, n) -> str:
        return f"n = {n}: {self.value(g, n)} is composite"
