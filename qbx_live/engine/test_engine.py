"""Tests for ``qbx_live.engine`` (run: ``python -m unittest qbx_live.engine.test_engine``)."""

import itertools
import random
import unittest

from qbx_live.engine import coded, fixed_point as fp


class TestMerge(unittest.TestCase):
    def test_any_delivery_order(self):
        rng = random.Random(1)
        join = lambda a, b: tuple(x | y for x, y in zip(a, b))
        states = [tuple(rng.randrange(2) == 1 for _ in range(6)) for _ in range(5)]
        self.assertTrue(fp.check_join(join, states))
        expected = fp.merge_deliveries(states, join)
        for _ in range(100):
            deliveries = states + [rng.choice(states) for _ in range(3)]
            rng.shuffle(deliveries)
            self.assertEqual(fp.merge_deliveries(deliveries, join), expected)

    def test_check_join_rejects_non_join(self):
        self.assertFalse(fp.check_join(lambda a, b: a + b, [1, 2]))


class TestFixedPoint(unittest.TestCase):
    def setUp(self):
        rng = random.Random(7)
        self.n = 30
        self.edges = [(rng.randrange(self.n), rng.randrange(self.n)) for _ in range(45)]
        self.F = fp.reachability_update(self.edges, [0, 5], self.n)
        self.bottom = (False,) * self.n

    def reachable(self):
        seen, stack = {0, 5}, [0, 5]
        while stack:
            u = stack.pop()
            for a, b in self.edges:
                if a == u and b not in seen:
                    seen.add(b)
                    stack.append(b)
        return tuple(v in seen for v in range(self.n))

    def test_sync_reaches_lfp_within_card(self):
        run = fp.run_sync(self.F, self.bottom, max_rounds=self.n + 1)
        self.assertEqual(run.point, self.reachable())
        self.assertLessEqual(run.rounds, self.n + 1)
        self.assertEqual(run.residuals[-1], 0)

    def test_async_same_point(self):
        sync = fp.run_sync(self.F, self.bottom, self.n + 1)
        for sched in (fp.round_robin(self.n), fp.random_fair(self.n, 3)):
            run = fp.run_async(self.F, self.bottom, sched, max_steps=self.n * (self.n + 2))
            self.assertEqual(run.point, sync.point)
            # every update switches one component False → True, so updates = |lfp|
            self.assertEqual(run.updates, sum(sync.point))


class TestCoded(unittest.TestCase):
    def setUp(self):
        words = [[(0, True), (1, True)], [(1, False)], [(0, True), (0, True), (2, False)]]
        self.blocks = coded.burau_blocks(words, 4)
        self.B = coded.burau_blocks([[(2, True), (1, False)]], 4)[0]
        self.exact = [coded.mat_mul(A, self.B) for A in self.blocks]

    def test_any_k_of_n(self):
        k, n = 3, 6
        for alive in itertools.combinations(range(n), k):
            delays = [1.0 + j if j in alive else None for j in range(n)]
            run = coded.coded_product(self.blocks, self.B, n, delays)
            self.assertEqual(run.products, self.exact)
            self.assertEqual(sorted(run.used_workers), list(alive))

    def test_k_minus_one_insufficient(self):
        delays = [1.0, 2.0, None, None, None, None]
        with self.assertRaises(ValueError):
            coded.coded_product(self.blocks, self.B, 6, delays)

    def test_straggler_latency(self):
        # Worker 0 (block 0 in the uncoded scheme) is a straggler; coding does not wait for it.
        delays = [100.0, 1.0, 1.5, 2.0, 2.5, 3.0]
        run = coded.coded_product(self.blocks, self.B, 6, delays)
        self.assertEqual(run.products, self.exact)
        self.assertEqual(run.finish_time, 2.0)
        self.assertEqual(run.uncoded_time, 100.0)

    def test_float_path_close(self):
        err = coded.float_error(self.blocks, self.B, [1, 2, 3])
        self.assertLess(err, 1e-9)


if __name__ == "__main__":
    unittest.main()
