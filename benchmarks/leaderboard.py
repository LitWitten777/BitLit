"""
Discovery Olympics Leaderboard

Persists every run to benchmarks/leaderboard/runs.jsonl.
Provides methods to append results, load history, and print rankings.
"""
import json
import os
from datetime import datetime, timezone
from typing import Dict, List

_HERE = os.path.dirname(os.path.abspath(__file__))
RUNS_PATH = os.path.join(_HERE, "leaderboard", "runs.jsonl")


def record_run(
    method: str,
    dataset: str,
    track: str,
    compression: float = 0.0,
    prediction: float = 0.0,
    reuse: float = 0.0,
    boundary_f1: float = 0.0,
    novelty: float = 0.0,
    ci_95: List[float] = None,
) -> Dict:
    """
    Append a single run result to the leaderboard JSONL file.
    Returns the recorded entry.
    """
    overall = (
        0.25 * compression
        + 0.25 * prediction
        + 0.20 * reuse
        + 0.20 * boundary_f1
        + 0.10 * novelty
    )
    entry = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "method": method,
        "dataset": dataset,
        "track": track,
        "compression": round(compression, 4),
        "prediction": round(prediction, 4),
        "reuse": round(reuse, 4),
        "boundary_f1": round(boundary_f1, 4),
        "novelty": round(novelty, 4),
        "overall": round(overall, 4),
        "ci_95": ci_95 if ci_95 else [0.0, 0.0],
    }
    os.makedirs(os.path.dirname(RUNS_PATH), exist_ok=True)
    with open(RUNS_PATH, "a") as f:
        f.write(json.dumps(entry) + "\n")
    return entry


def load_runs() -> List[Dict]:
    """Return all historical runs from the leaderboard file."""
    if not os.path.exists(RUNS_PATH):
        return []
    runs = []
    with open(RUNS_PATH) as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    runs.append(json.loads(line))
                except json.JSONDecodeError:
                    pass
    return runs


def print_leaderboard(track: str = None, dataset: str = None):
    """
    Print a ranked leaderboard table, optionally filtered by track and/or dataset.
    """
    runs = load_runs()
    if track:
        runs = [r for r in runs if r["track"] == track]
    if dataset:
        runs = [r for r in runs if r["dataset"] == dataset]

    if not runs:
        print("No runs recorded yet.")
        return

    # Aggregate: for each (method, dataset, track), keep best overall
    best: Dict[tuple, Dict] = {}
    for r in runs:
        key = (r["method"], r["dataset"], r["track"])
        if key not in best or r["overall"] > best[key]["overall"]:
            best[key] = r

    ranked = sorted(best.values(), key=lambda x: x["overall"], reverse=True)

    print(f"\n{'Rank':<5} {'Method':<12} {'Dataset':<20} {'Track':<15} "
          f"{'Compress':<10} {'Predict':<10} {'Reuse':<8} "
          f"{'BoundF1':<10} {'Novelty':<9} {'Overall':<10} {'CI95'}")
    print("-" * 120)
    for rank, r in enumerate(ranked, 1):
        ci = r.get("ci_95", [0.0, 0.0])
        print(
            f"{rank:<5} {r['method']:<12} {r['dataset']:<20} {r['track']:<15} "
            f"{r['compression']:<10.4f} {r['prediction']:<10.4f} {r['reuse']:<8.4f} "
            f"{r['boundary_f1']:<10.4f} {r['novelty']:<9.4f} {r['overall']:<10.4f} "
            f"[{ci[0]:.3f}, {ci[1]:.3f}]"
        )
