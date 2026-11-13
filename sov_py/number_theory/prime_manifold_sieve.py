"""
src/sedenion/number_theory/prime_manifold_sieve.py
=============================================================================
High-Throughput Vectorized Arithmetic Manifold Scanner.

Evaluates prime ground-state invariants across N >= 2:
1. E8 Root Lattice Theta Divisor Excess:
   Delta_E8(n) = sigma_3(n) - (n^3 + 1) = 0  iff n in P
   (Delta_E8(n) >= 8                          iff n is composite)

2. Arithmetic Organism Ground-State Curvature:
   S(n) = I * (gamma(n)^2 + beta(n)^2) / delta = 0.0  iff n in P
   where:
     beta(n)  = sigma_0(n) - 2              (non-trivial factor defect)
     gamma(n) = sum_{d|n, 1<d<n} 1/d        (associator defect)

Target Throughput: > 100,000 candidate integers / sec.
=============================================================================
"""

from __future__ import annotations

import math
import time
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

import numpy as np


@dataclass(frozen=True)
class PrimeSieveResult:
    n: int
    is_prime: bool
    delta_e8: int
    curvature_s: float
    beta: int
    gamma: float


class PrimeManifoldSieve:
    """
    High-performance sieve verifying arithmetic ground-state invariants.
    """

    def __init__(self, default_limit: int = 100_000):
        self.default_limit = default_limit

    @staticmethod
    def compute_e8_excess(n: int) -> int:
        """
        Exact integer computation of E8 root lattice cubic excess:
        Delta_E8(n) = sigma_3(n) - (n^3 + 1).
        """
        if n < 2:
            return 0
        s3 = 0
        limit = int(math.isqrt(n))
        for d in range(1, limit + 1):
            if n % d == 0:
                s3 += d ** 3
                other = n // d
                if other != d:
                    s3 += other ** 3
        return s3 - (n ** 3 + 1)

    @staticmethod
    def compute_curvature_s(n: int, delta: float = 1.0) -> Tuple[float, int, float]:
        """
        Computes ground state curvature S(n), factor defect beta(n), and associator defect gamma(n).
        """
        if n < 2:
            return 0.0, 0, 0.0
        divisors = []
        limit = int(math.isqrt(n))
        for d in range(1, limit + 1):
            if n % d == 0:
                divisors.append(d)
                other = n // d
                if other != d:
                    divisors.append(other)
        
        # Proper non-trivial divisors: 1 < d < n
        proper = [d for d in divisors if 1 < d < n]
        beta = len(proper)  # sigma_0(n) - 2
        gamma = sum(1.0 / d for d in proper)
        
        # Topological inertia I = sum(d) / n
        inertia = sum(divisors) / float(n)
        s = (inertia * (gamma ** 2 + beta ** 2)) / float(delta)
        return s, beta, gamma

    def scan_range(self, start: int, count: int) -> List[PrimeSieveResult]:
        """
        Scans a contiguous block of integers [start, start + count) and returns
        exact ground-state invariant metrics.
        """
        results: List[PrimeSieveResult] = []
        for n in range(start, start + count):
            delta_e8 = self.compute_e8_excess(n)
            s, beta, gamma = self.compute_curvature_s(n)
            is_prime = (delta_e8 == 0) and (beta == 0)
            results.append(
                PrimeSieveResult(
                    n=n,
                    is_prime=is_prime,
                    delta_e8=delta_e8,
                    curvature_s=s,
                    beta=beta,
                    gamma=gamma,
                )
            )
        return results

    def batch_benchmark(self, limit: int = 100_000) -> Dict[str, float]:
        """
        Executes vectorized batch sieve over [2, limit) and measures throughput.
        """
        t0 = time.perf_counter()
        primes = []
        min_prime = np.zeros(limit, dtype=np.uint32)
        p_pow = np.zeros(limit, dtype=np.uint32)
        sigma3 = np.ones(limit, dtype=np.uint64)
        sigma0 = np.ones(limit, dtype=np.uint32)

        for i in range(2, limit):
            if min_prime[i] == 0:
                min_prime[i] = i
                p_pow[i] = i
                primes.append(i)
                sigma0[i] = 2
                sigma3[i] = 1 + np.uint64(i) ** 3
            for p in primes:
                ip = i * p
                if p > min_prime[i] or ip >= limit:
                    break
                min_prime[ip] = p
                if min_prime[i] == p:
                    pk = p_pow[i] * p
                    p_pow[ip] = pk
                    rem = ip // pk
                    s3_pk = sigma3[p_pow[i]] * (np.uint64(p) ** 3) + 1
                    sigma3[ip] = s3_pk * (sigma3[rem] if rem > 1 else 1)
                    sigma0[ip] = (sigma0[i] + 1) * (sigma0[rem] // (sigma0[p_pow[i]] if p_pow[i] < i else 1) if rem > 1 else 1)
                else:
                    p_pow[ip] = p
                    sigma3[ip] = (1 + np.uint64(p) ** 3) * sigma3[i]
                    sigma0[ip] = 2 * sigma0[i]

        elapsed = time.perf_counter() - t0
        rate = limit / elapsed
        
        # Verify invariants
        n_arr = np.arange(limit, dtype=np.uint64)
        delta_e8 = sigma3 - ((n_arr ** 3) + 1)
        primes_e8 = (delta_e8[2:] == 0)
        primes_sigma0 = (sigma0[2:] == 2)
        assert np.array_equal(primes_e8, primes_sigma0), "Delta_E8 prime characterization mismatch!"

        return {
            "limit": float(limit),
            "elapsed_sec": elapsed,
            "throughput_ints_per_sec": rate,
            "total_primes_found": float(len(primes)),
        }
