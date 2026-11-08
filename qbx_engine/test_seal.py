"""Tests for ``qbx_engine.seal`` (runtime counterparts of seal-lane theorems S3–S6)."""

import itertools
import random
import unittest
from fractions import Fraction

from qbx_engine import seal
from qbx_engine.seal import Leaf


def random_tree(items, rng):
    if len(items) == 1:
        return Leaf(items[0])
    cut = rng.randrange(1, len(items))
    return (random_tree(items[:cut], rng), random_tree(items[cut:], rng))


class TestS3Merge(unittest.TestCase):
    def test_any_schedule_same_state(self):
        rng = random.Random(3)
        join = lambda a, b: a | b
        base = [frozenset({1}), frozenset({2, 3}), frozenset({3, 4}), frozenset()]
        expected = seal.merge(base, join)
        for _ in range(200):
            items = base + [rng.choice(base) for _ in range(rng.randrange(4))]  # duplicates
            rng.shuffle(items)
            self.assertEqual(seal.merge_tree(random_tree(items, rng), join), expected)

    def test_max_lattice(self):
        for perm in itertools.permutations([3, 9, 1, 9, 4]):
            self.assertEqual(seal.merge(perm, max), 9)


class TestS4Kleene(unittest.TestCase):
    # reachability on a 5-node graph as a monotone map on the lattice of subsets (32 elements)
    EDGES = {0: [1], 1: [2], 2: [0, 3], 3: [], 4: [3]}

    def F(self, s):
        return frozenset({0}) | frozenset(v for u in s for v in self.EDGES[u])

    def test_lfp_within_card(self):
        x, rounds = seal.kleene(self.F, frozenset(), max_rounds=32)
        self.assertEqual(x, frozenset({0, 1, 2, 3}))
        self.assertLessEqual(rounds, 32)

    def test_chaotic_fair_schedule(self):
        # componentwise version: x[v] = 1 iff v reachable
        def G(x):
            return tuple(int(v == 0 or any(x[u] and v in self.EDGES[u] for u in range(5)))
                         for v in range(5))
        rng = random.Random(4)
        for _ in range(50):
            sched = [rng.randrange(5) for _ in range(400)] + list(range(5)) * 10
            self.assertEqual(seal.chaotic(G, (0,) * 5, sched, len(sched)), (1, 1, 1, 1, 0))


class TestS5Coded(unittest.TestCase):
    def test_any_k_of_n(self):
        rng = random.Random(5)
        k, n = 3, 6
        coeffs = [[[Fraction(rng.randrange(-9, 10)) for _ in range(2)] for _ in range(2)]
                  for _ in range(k)]
        shares = [(Fraction(x), seal.coded_encode(coeffs, Fraction(x))) for x in range(1, n + 1)]
        for subset in itertools.combinations(shares, k):
            self.assertEqual(seal.coded_decode(list(subset), k), coeffs)

    def test_too_few(self):
        with self.assertRaises(ValueError):
            seal.coded_decode([(Fraction(1), [[Fraction(0)]])], 2)


class TestS6Chord(unittest.TestCase):
    def test_braid_relation(self):
        a = [(0, True), (1, True), (0, True)]
        b = [(1, True), (0, True), (1, True)]
        self.assertEqual(seal.final_chord(a, 3), seal.final_chord(b, 3))

    def test_far_commutation_and_cancellation(self):
        a = [(0, True), (2, False), (1, True), (1, False)]
        b = [(2, False), (0, True)]
        self.assertEqual(seal.final_chord(a, 4), seal.final_chord(b, 4))

    def test_distinguishes(self):
        self.assertNotEqual(seal.final_chord([(0, True)], 3), seal.final_chord([(0, False)], 3))

    def test_charpoly_identity(self):
        self.assertEqual(seal.charpoly([[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]),
                         (Fraction(1), Fraction(-2), Fraction(1)))


if __name__ == "__main__":
    unittest.main()
