"""
Statistical validation utilities for the Discovery Olympics.

Provides bootstrap confidence intervals and permutation tests so that
method comparisons carry quantified uncertainty rather than point estimates.
"""
import math
import random
from typing import List, Tuple


def bootstrap_ci(
    scores: List[float],
    n_resamples: int = 1000,
    confidence: float = 0.95,
) -> Tuple[float, float, float]:
    """
    Return (mean, lower_ci, upper_ci) via bootstrap resampling.

    Args:
        scores: Observed metric values for one method on one dataset.
        n_resamples: Number of bootstrap iterations.
        confidence: Confidence level, e.g. 0.95 for 95% CI.

    Returns:
        Tuple of (mean, lower bound, upper bound).
    """
    if not scores:
        return (0.0, 0.0, 0.0)

    n = len(scores)
    boot_means = []
    for _ in range(n_resamples):
        sample = [random.choice(scores) for _ in range(n)]
        boot_means.append(sum(sample) / n)

    boot_means.sort()
    alpha = 1.0 - confidence
    lo_idx = int(math.floor(alpha / 2 * n_resamples))
    hi_idx = int(math.ceil((1.0 - alpha / 2) * n_resamples)) - 1
    hi_idx = min(hi_idx, n_resamples - 1)

    mean = sum(scores) / n
    return (round(mean, 4), round(boot_means[lo_idx], 4), round(boot_means[hi_idx], 4))


def permutation_test(
    scores_a: List[float],
    scores_b: List[float],
    n_permutations: int = 10_000,
) -> float:
    """
    Two-sided permutation test: p-value for the null hypothesis that
    scores_a and scores_b come from the same distribution.

    Returns: p-value in [0, 1].
    """
    if not scores_a or not scores_b:
        return 1.0

    combined = scores_a + scores_b
    n_a = len(scores_a)
    observed_diff = abs(
        sum(scores_a) / len(scores_a) - sum(scores_b) / len(scores_b)
    )

    count_ge = 0
    for _ in range(n_permutations):
        shuffled = combined[:]
        random.shuffle(shuffled)
        perm_a = shuffled[:n_a]
        perm_b = shuffled[n_a:]
        perm_diff = abs(
            sum(perm_a) / len(perm_a) - sum(perm_b) / len(perm_b)
        )
        if perm_diff >= observed_diff:
            count_ge += 1

    return round(count_ge / n_permutations, 4)


def compare_methods(
    name_a: str,
    scores_a: List[float],
    name_b: str,
    scores_b: List[float],
    n_boot: int = 1000,
    n_perm: int = 10_000,
) -> dict:
    """
    Full statistical comparison between two methods on one metric.

    Returns a dict with means, CIs, p-value, and significance flag.
    """
    mean_a, lo_a, hi_a = bootstrap_ci(scores_a, n_boot)
    mean_b, lo_b, hi_b = bootstrap_ci(scores_b, n_boot)
    p_value = permutation_test(scores_a, scores_b, n_perm)

    # CIs overlap check
    cis_overlap = not (hi_a < lo_b or hi_b < lo_a)

    return {
        name_a: {"mean": mean_a, "ci_95": [lo_a, hi_a]},
        name_b: {"mean": mean_b, "ci_95": [lo_b, hi_b]},
        "p_value": p_value,
        "significant": p_value < 0.05 and not cis_overlap,
        "winner": name_a if mean_a > mean_b else name_b,
    }
