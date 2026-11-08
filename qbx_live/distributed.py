"""
Node step 6 — the distributed scheduler.

The text is cut into windows (as for the cache), the windows into ``N``
*consecutive* blocks of balanced size, one block per worker node.  Each worker
summarises its block (through the network cache if one is given) and sends the
block summary back in wire format, tagged with the block index.  The
coordinator checks that it received each index exactly once and combines the
summaries **in block order** with the balanced reduction tree.

Lean (``QBX/Formal/MultiProver/NodeNetwork.lean``):

* ``flatten_blocks``, ``distributed_correct`` — consecutive blocks combined in
  block order by any reduction schedule give the summary of the whole text;
* ``sum_balancedSizes``, ``balancedSizes_bounds`` — :func:`balanced_sizes` gives
  ``N`` sizes adding up to the number of windows, differing by at most one;
* ``roundRobin_wrong`` — dealing chunks round-robin and multiplying each node's
  chunks locally is wrong: the summary monoid is not commutative.
  :func:`round_robin_summary` implements that mistake so the tests can show it.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Tuple, TypeVar

from qbx_bible.encode import Encoding
from qbx_bible import manifold as mf
from qbx_live import wire
from qbx_live import window_cache as wc
from qbx_live.dht import Address, Network

T = TypeVar("T")


class ScheduleError(RuntimeError):
    """The coordinator received a block twice, or not at all."""


def balanced_sizes(n_nodes: int, m: int) -> List[int]:
    """Lean ``balancedSizes``: the first ``m % N`` nodes get ``m // N + 1`` items."""
    if n_nodes < 1:
        raise ValueError("need at least one node")
    q, r = divmod(m, n_nodes)
    return [q + (1 if i < r else 0) for i in range(n_nodes)]


def blocks(sizes: Sequence[int], items: Sequence[T]) -> List[List[T]]:
    """Lean ``blocks``: consecutive blocks of the given sizes; the last block takes the rest."""
    out, i = [], 0
    for s in sizes:
        out.append(list(items[i:i + s]))
        i += s
    out.append(list(items[i:]))
    return out


def _block_summary(windows: Sequence[str], encoding: Encoding, keep_word: bool,
                   network: Optional[Network], node: Optional[Address],
                   alphabet_id: str) -> mf.ChunkSummary:
    if network is not None and node is not None:
        parts = [network.summary(w, node, alphabet_id, encoding, keep_word) for w in windows]
    else:
        parts = [mf.summarize(w, encoding, keep_word) for w in windows]
    return mf.reduce_tree(parts, encoding) if parts else mf.identity(encoding, keep_word)


def worker_results(text: str, nodes: Sequence[Optional[Address]], encoding: Encoding = Encoding(),
                   k: int = wc.DEFAULT_K, keep_word: bool = True,
                   network: Optional[Network] = None,
                   alphabet_id: str = "hebrew-wlc") -> List[Tuple[int, bytes]]:
    """What the workers send back: ``(block index, CBOR summary)`` for each node's block."""
    ws = wc.windows_of(text, k)
    bl = blocks(balanced_sizes(len(nodes), len(ws)), ws)
    assert not bl[-1], "balanced sizes cover every window"
    return [(i, wire.to_cbor(_block_summary(bl[i], encoding, keep_word, network, node,
                                            alphabet_id)))
            for i, node in enumerate(nodes)]


def combine(results: Sequence[Tuple[int, bytes]], n_blocks: int,
            encoding: Encoding = Encoding(), keep_word: bool = True) -> mf.ChunkSummary:
    """The coordinator: check every block index arrived exactly once, decode, and
    combine in block order."""
    got: Dict[int, bytes] = {}
    for i, blob in results:
        if not 0 <= i < n_blocks:
            raise ScheduleError(f"unknown block {i}")
        if i in got:
            raise ScheduleError(f"block {i} received twice")
        got[i] = blob
    missing = [i for i in range(n_blocks) if i not in got]
    if missing:
        raise ScheduleError(f"blocks {missing} missing")
    parts = [wire.from_cbor(got[i]) for i in range(n_blocks)]
    return mf.reduce_tree(parts, encoding) if parts else mf.identity(encoding, keep_word)


def distributed_summary(text: str, nodes: Sequence[Optional[Address]],
                        encoding: Encoding = Encoding(), k: int = wc.DEFAULT_K,
                        keep_word: bool = True, network: Optional[Network] = None,
                        alphabet_id: str = "hebrew-wlc") -> mf.ChunkSummary:
    """Scatter the text over ``nodes``, gather the block summaries, combine in order.
    Equal to ``manifold.summarize(text)`` (Lean ``distributed_correct``)."""
    res = worker_results(text, nodes, encoding, k, keep_word, network, alphabet_id)
    return combine(res, len(nodes), encoding, keep_word)


def round_robin_summary(text: str, n_nodes: int, encoding: Encoding = Encoding(),
                        k: int = wc.DEFAULT_K, keep_word: bool = True) -> mf.ChunkSummary:
    """**Wrong on purpose** (Lean ``roundRobin_wrong``): window ``i`` goes to node
    ``i mod N``, each node multiplies its own windows, the node results are multiplied."""
    ws = wc.windows_of(text, k)
    per_node = [[w for i, w in enumerate(ws) if i % n_nodes == j] for j in range(n_nodes)]
    parts = [_block_summary(p, encoding, keep_word, None, None, "") for p in per_node]
    return mf.reduce_tree(parts, encoding)
