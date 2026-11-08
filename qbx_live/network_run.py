"""
Node step 8 — Genesis 1 end to end over the (simulated) network.

1. **Scatter.** A coordinator cuts the text into windows and the windows into
   balanced consecutive blocks, one per worker node; workers summarise their
   blocks through the DHT (:mod:`qbx_live.dht`), which fills the network cache
   (:mod:`qbx_live.distributed`).
2. **Gather.** The coordinator combines the block summaries in block order.
3. **Verify.** Every node of the address graph recomputes the summary from the
   network cache (all lookups, no recomputation of cached windows) and reports
   the content address of its result to its neighbours.
4. **Consensus.** The reports form a ledger (:mod:`qbx_live.consensus`); it must
   be flat and unanimous, and its common state must equal the coordinator's.

The run is accepted when the network result equals the single-node summary
``manifold.summarize(text)``.  ``tests/qbx_live/test_network.py`` also compares
the braid word with the per-verse words that ``QBX/Formal/BibleBraidGenesis1.lean``
checks in Lean.

Usage: ``python -m qbx_live.network_run [--bits 2 --cycles 3 4 --workers 8 --k 4]``.
"""

from __future__ import annotations

import argparse
import json
import time
from typing import Any, Dict, Optional, Sequence

from qbx_bible import Encoding, load_corpus
from qbx_bible import manifold as mf
from qbx_live import consensus as cs
from qbx_live import wire
from qbx_live import window_cache as wc
from qbx_live.dht import AddressSpace, Network
from qbx_live.distributed import distributed_summary


def genesis_text() -> str:
    return " ".join(v.text for v in load_corpus())


def run(text: str, space: AddressSpace, n_workers: int = 8, k: int = wc.DEFAULT_K,
        encoding: Encoding = Encoding(), keep_word: bool = True,
        verifiers: Optional[int] = None) -> Dict[str, Any]:
    """Run steps 1–4 and compare with the single-node summary."""
    t0 = time.perf_counter()
    net = Network(space)
    addrs = list(space.addresses())
    workers = [addrs[(i * len(addrs)) // n_workers] for i in range(n_workers)]
    coordinator = addrs[0]
    combined = distributed_summary(text, workers, encoding, k, keep_word, network=net)
    t1 = time.perf_counter()

    checked = addrs if verifiers is None else addrs[:verifiers]
    state = {}
    for a in checked:
        s = net.summarize_text(text, a, encoding=encoding, k=k, keep_word=keep_word)
        state[a] = cs.state_of_digest(wire.digest(s))
    # nodes not asked to verify adopt the coordinator's result (they report it unchanged)
    coord_state = cs.state_of_digest(wire.digest(combined))
    for a in addrs:
        state.setdefault(a, coord_state)
    claims = cs.honest_claims(space, state)
    verdict = cs.verdict(space, claims)
    t2 = time.perf_counter()

    direct = mf.summarize(text, encoding, keep_word)
    t3 = time.perf_counter()
    return {
        "nodes": space.size,
        "degree": space.degree,
        "diameter": space.diameter,
        "workers": n_workers,
        "windows": len(wc.windows_of(text, k)),
        "network_digest": wire.digest(combined),
        "single_node_digest": wire.digest(direct),
        "matches_single_node": combined == direct,
        "verifiers": len(checked),
        "ledger_flat": verdict["flat"],
        "ledger_unanimous": verdict["unanimous"],
        "consensus_state_is_coordinator": set(claims.values()) == {coord_state},
        "lookups": net.stats.gets,
        "max_hops": net.stats.max_hops,
        "misses": net.stats.misses,
        "seconds": {"distributed": round(t1 - t0, 3), "verify+consensus": round(t2 - t1, 3),
                    "single_node": round(t3 - t2, 3)},
        "lean": {
            "lookup": "Node.greedy_arrives, Node.addrDist_le_addrDiam",
            "scheduling": "Node.distributed_correct, MultiProver.schedule_correct",
            "consensus": "Node.addrGraph_single_liar_isFlat_iff, "
                         "Integration.addrGraph_perturb_detected",
        },
    }


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    ap.add_argument("--bits", type=int, default=2)
    ap.add_argument("--cycles", type=int, nargs="*", default=[3, 4])
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--k", type=int, default=wc.DEFAULT_K)
    ap.add_argument("--verifiers", type=int, default=None)
    args = ap.parse_args(argv)
    report = run(genesis_text(), AddressSpace(args.bits, tuple(args.cycles)), args.workers,
                 args.k, verifiers=args.verifiers)
    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 0 if report["matches_single_node"] and report["ledger_flat"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
