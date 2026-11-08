"""
Node step 7 — consensus as flatness.

Every node ``v`` reports a state to each neighbour ``w``: ``claim[(v, w)]``.  For
the network run the state is the node's summary of the text, as an element of
the additive group ``ℤ / P`` (``P = 2⁶¹ − 1``; the value is the content address
:func:`qbx_live.wire.digest` reduced mod ``P``).  The link ``v → w`` carries the
transport ``claim[(w, v)] − claim[(v, w)]`` (Lean ``Node.claimConn``, written
additively).  The ledger is *flat* when every closed walk has zero holonomy;
:func:`is_flat` checks this with a spanning tree (Lean
``Gauge.Connection.isFlat_iff_fundamental``).

Lean results this module relies on:

* ``Node.claimConn_isFlat_of_consistent`` — honest nodes give a flat ledger;
* ``Node.addrGraph_single_liar_isFlat_iff`` — on the address graph (all
  ``M_j ≥ 2``), if only one node deviates, the ledger is flat **iff** that node
  reports one state to all neighbours.  An *equivocating* node is always caught;
  a node that tells everybody the same wrong state is not (that is a gauge
  change) — it is caught by :func:`unanimous` instead, which compares the
  states themselves;
* ``Integration.addrGraph_perturb_detected`` / ``addrGraph_not_isBridge`` — with
  at least two non-trivial coordinates the address graph has no bridges, so every
  single-link fork is detected; ``Gauge.Connection.perturb_detected_iff_not_isBridge``
  — on a bridge (e.g. ``Q_1``) a fork is invisible.
"""

from __future__ import annotations

from collections import deque
from typing import Dict, List, Mapping, Optional, Set, Tuple

from qbx_live.dht import Address, AddressSpace

P = (1 << 61) - 1
Edge = Tuple[Address, Address]


def state_of_digest(digest_hex: str) -> int:
    """A summary's content address as an element of ``ℤ / P``."""
    return int(digest_hex, 16) % P


def directed_edges(space: AddressSpace) -> List[Edge]:
    return [(v, w) for v in space.addresses() for w in space.neighbors(v)]


def honest_claims(space: AddressSpace, state: Mapping[Address, int]) -> Dict[Edge, int]:
    """Every node reports its own state to every neighbour."""
    return {(v, w): state[v] % P for v, w in directed_edges(space)}


def transports(claims: Mapping[Edge, int]) -> Dict[Edge, int]:
    """Lean ``claimConn``: ``t(v → w) = claim(w, v) − claim(v, w)``."""
    return {(v, w): (claims[(w, v)] - c) % P for (v, w), c in claims.items()}


def is_flat(space: AddressSpace, t: Mapping[Edge, int]) -> bool:
    """Spanning-tree check: potentials along a BFS tree, then every link must agree."""
    pot: Dict[Address, int] = {}
    for root in space.addresses():
        if root in pot:
            continue
        pot[root] = 0
        queue = deque([root])
        while queue:
            v = queue.popleft()
            for w in space.neighbors(v):
                if w not in pot:
                    pot[w] = (pot[v] + t[(v, w)]) % P
                    queue.append(w)
    return all((pot[w] - pot[v]) % P == x for (v, w), x in t.items())


def perturb(t: Mapping[Edge, int], a: Address, b: Address, kappa: int) -> Dict[Edge, int]:
    """Lean ``Connection.perturb``: change the transport of one link by ``kappa``."""
    out = dict(t)
    out[(a, b)] = (t[(a, b)] + kappa) % P
    out[(b, a)] = (-out[(a, b)]) % P
    return out


def unanimous(claims: Mapping[Edge, int]) -> bool:
    """Every report carries the same state (on a connected graph: all transports zero
    and the ledger flat)."""
    return len(set(claims.values())) <= 1


def bridges(space: AddressSpace) -> Set[frozenset]:
    """The bridges of the address graph (iterative Tarjan low-link)."""
    index: Dict[Address, int] = {}
    low: Dict[Address, int] = {}
    out: Set[frozenset] = set()
    counter = 0
    for root in space.addresses():
        if root in index:
            continue
        index[root] = low[root] = counter
        counter += 1
        stack: List[Tuple[Address, Optional[Address], List[Address]]] = [
            (root, None, list(space.neighbors(root)))]
        while stack:
            v, parent, todo = stack[-1]
            if todo:
                w = todo.pop()
                if w == parent:
                    continue
                if w in index:
                    low[v] = min(low[v], index[w])
                else:
                    index[w] = low[w] = counter
                    counter += 1
                    stack.append((w, v, list(space.neighbors(w))))
            else:
                stack.pop()
                if parent is not None:
                    low[parent] = min(low[parent], low[v])
                    if low[v] > index[parent]:
                        out.add(frozenset((parent, v)))
    return out


def nontrivial_coords(space: AddressSpace) -> int:
    """Lean ``nontrivialCoords``: bits plus cycles with modulus ``≠ 1``."""
    return space.n + sum(1 for m in space.moduli if m != 1)


def verdict(space: AddressSpace, claims: Mapping[Edge, int]) -> Dict[str, object]:
    """Flatness and unanimity of a round of reports."""
    flat = is_flat(space, transports(claims))
    return {"flat": flat, "unanimous": unanimous(claims),
            "states": len(set(claims.values()))}
