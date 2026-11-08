"""
Node step 5 — a distributed hash table on the address graph ``Q_n □ T^k_M``.

Every address of the graph is one node (full occupancy; the node count is
``2^n · ∏ M_j``).  A window summary with cache key ``key`` (see
:func:`qbx_live.window_cache.window_key`) is *owned* by the address
:func:`key_address` decodes from the key, and replicated on the owner's
neighbours.  Every node keeps its share in its own
:class:`qbx_live.window_cache.WindowCache`.

Lookups are greedy: every hop is one move (a bit flip or a ``±1`` cycle step)
that lowers the distance to the owner by one.  Lean
(``QBX/Formal/MultiProver/NodeNetwork.lean``):

* ``greedy_arrives`` — any greedy lookup reaches the owner after exactly
  ``distance(origin, owner)`` hops (whatever greedy choice is made);
* ``addrDist_le_addrDiam`` / ``exists_addrDist_eq_addrDiam`` — that is at most
  ``n + Σ_j ⌊M_j / 2⌋`` hops, and this is attained;
* ``lookup_survives_link_failures`` — after fewer than ``degree`` link failures
  every address is still reachable (then :meth:`Network.path` falls back to a
  breadth-first search of the surviving graph);
* ``replica_survives`` / ``replicas_can_all_fail`` — the replica set has
  ``degree + 1`` members, so some replica survives any ``degree`` node failures,
  and ``degree + 1`` failures can remove all of them.

Not proved: that a surviving replica is reachable when *nodes* (not links)
fail; that needs the vertex connectivity of the address graph.  :meth:`Network.get`
searches the surviving graph and reports a miss if no replica is reachable.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
from typing import Dict, FrozenSet, Iterator, List, Optional, Sequence, Set, Tuple

from qbx_bible.encode import Encoding
from qbx_bible import manifold as mf
from qbx_live import window_cache as wc

Address = Tuple[Tuple[int, ...], Tuple[int, ...]]   # (bits, cycles)


class LookupFailed(RuntimeError):
    """No live replica of the key is reachable from the origin."""


@dataclass(frozen=True)
class AddressSpace:
    """The graph ``Q_n □ T^k_M`` (Lean: ``Gates.addrGraph n k M``)."""

    n: int
    moduli: Tuple[int, ...] = ()

    def __post_init__(self):
        if self.n < 0 or any(m < 2 for m in self.moduli):
            raise ValueError("need n ≥ 0 and every modulus ≥ 2")
        if self.n + len(self.moduli) == 0:
            raise ValueError("the space needs at least one coordinate")

    @property
    def size(self) -> int:
        s = 2 ** self.n
        for m in self.moduli:
            s *= m
        return s

    @property
    def degree(self) -> int:
        """``addrDegree n k M = n + Σ_j (M_j = 2 ? 1 : 2)``."""
        return self.n + sum(1 if m == 2 else 2 for m in self.moduli)

    @property
    def diameter(self) -> int:
        """``addrDiam n k M = n + Σ_j ⌊M_j / 2⌋`` (Lean: ``exists_addrDist_eq_addrDiam``)."""
        return self.n + sum(m // 2 for m in self.moduli)

    def addresses(self) -> Iterator[Address]:
        for i in range(self.size):
            yield self.decode(i)

    def decode(self, x: int) -> Address:
        """Mixed-radix decoding of ``x mod size``: the low ``n`` bits are the cube
        coordinates, the remaining digits (radices ``M_0, M_1, …``) the cycles."""
        x %= self.size
        bits = tuple((x >> i) & 1 for i in range(self.n))
        x >>= self.n
        cycles = []
        for m in self.moduli:
            cycles.append(x % m)
            x //= m
        return bits, tuple(cycles)

    def encode(self, a: Address) -> int:
        """Inverse of :meth:`decode` on ``range(size)``."""
        bits, cycles = a
        x = 0
        for m, c in zip(reversed(self.moduli), reversed(cycles)):
            x = x * m + c
        x <<= self.n
        return x | sum(b << i for i, b in enumerate(bits))

    def distance(self, a: Address, b: Address) -> int:
        """``addrDist``: Hamming distance on the bits plus cyclic distance on each cycle."""
        d = sum(x != y for x, y in zip(a[0], b[0]))
        for x, y, m in zip(a[1], b[1], self.moduli):
            r = (x - y) % m
            d += min(r, m - r)
        return d

    def neighbors(self, a: Address) -> List[Address]:
        """The single moves from ``a``, in the order of ``MixedRadixSpace.neighbors``
        (bits, then each cycle ``+1`` and, if ``M_j > 2``, ``−1``)."""
        bits, cycles = a
        out = []
        for i in range(self.n):
            b = list(bits)
            b[i] ^= 1
            out.append((tuple(b), cycles))
        for j, m in enumerate(self.moduli):
            for s in ((1,) if m == 2 else (1, -1)):
                c = list(cycles)
                c[j] = (c[j] + s) % m
                out.append((bits, tuple(c)))
        return out

    def greedy_next(self, a: Address, b: Address) -> Optional[Address]:
        """The first neighbour of ``a`` one step closer to ``b`` (``None`` at ``b``).
        Lean ``exists_isMove_addrDist``: such a neighbour always exists."""
        d = self.distance(a, b)
        if d == 0:
            return None
        for v in self.neighbors(a):
            if self.distance(v, b) == d - 1:
                return v
        raise AssertionError("no greedy step: the metric is inconsistent")

    def greedy_route(self, a: Address, b: Address) -> List[Address]:
        """The greedy lookup path ``[a, …, b]``; it has ``distance(a, b)`` hops."""
        path = [a]
        while (nxt := self.greedy_next(path[-1], b)) is not None:
            path.append(nxt)
        return path

    def replica_set(self, c: Address) -> List[Address]:
        """The address and its neighbours (Lean ``replicaSet``; ``degree + 1`` members)."""
        return [c] + self.neighbors(c)


def key_address(key_hex: str, space: AddressSpace) -> Address:
    """The owner of a cache key: the address decoded from the key's integer value."""
    return space.decode(int(key_hex, 16))


def _link(a: Address, b: Address) -> FrozenSet[Address]:
    return frozenset((a, b))


@dataclass
class NetStats:
    puts: int = 0
    gets: int = 0
    hops: int = 0
    max_hops: int = 0
    detours: int = 0     # lookups that could not follow the greedy path
    misses: int = 0


@dataclass
class Network:
    """An in-process simulation of the node network on ``space``."""

    space: AddressSpace
    replicate: bool = True
    failed_links: Set[FrozenSet[Address]] = field(default_factory=set)
    failed_nodes: Set[Address] = field(default_factory=set)
    stats: NetStats = field(default_factory=NetStats)

    def __post_init__(self):
        self.stores: Dict[Address, wc.WindowCache] = {}

    # -- topology -----------------------------------------------------------

    def store(self, a: Address) -> wc.WindowCache:
        if a not in self.stores:
            self.stores[a] = wc.WindowCache()
        return self.stores[a]

    def alive(self, a: Address) -> bool:
        return a not in self.failed_nodes

    def link_up(self, a: Address, b: Address) -> bool:
        return self.alive(a) and self.alive(b) and _link(a, b) not in self.failed_links

    def fail_link(self, a: Address, b: Address) -> None:
        if b not in self.space.neighbors(a):
            raise ValueError("not a link of the address graph")
        self.failed_links.add(_link(a, b))

    def fail_node(self, a: Address) -> None:
        self.failed_nodes.add(a)

    def path(self, a: Address, b: Address) -> Optional[List[Address]]:
        """The greedy path if all its links are up; otherwise a shortest path in the
        surviving graph (breadth-first search); ``None`` if ``b`` is unreachable."""
        if not (self.alive(a) and self.alive(b)):
            return None
        g = self.space.greedy_route(a, b)
        if all(self.link_up(x, y) for x, y in zip(g, g[1:])):
            return g
        self.stats.detours += 1
        prev: Dict[Address, Optional[Address]] = {a: None}
        queue = deque([a])
        while queue:
            x = queue.popleft()
            if x == b:
                out = [b]
                while prev[out[-1]] is not None:
                    out.append(prev[out[-1]])
                return out[::-1]
            for y in self.space.neighbors(x):
                if y not in prev and self.link_up(x, y):
                    prev[y] = x
                    queue.append(y)
        return None

    def _count(self, path: Sequence[Address]) -> None:
        h = len(path) - 1
        self.stats.hops += h
        self.stats.max_hops = max(self.stats.max_hops, h)

    # -- storage ------------------------------------------------------------

    def holders(self, key: str) -> List[Address]:
        owner = key_address(key, self.space)
        return self.space.replica_set(owner) if self.replicate else [owner]

    def put(self, key: str, window: str, summary, origin: Address) -> int:
        """Store a summary on every reachable live holder; returns the number stored."""
        self.stats.puts += 1
        stored = 0
        for h in self.holders(key):
            p = self.path(origin, h)
            if p is None:
                continue
            self._count(p)
            self.store(h).put(key, window, summary)
            stored += 1
        return stored

    def get(self, key: str, window: str, origin: Address):
        """The summary from the first reachable live holder that has it, or ``None``."""
        self.stats.gets += 1
        for h in self.holders(key):
            if h in self.stores:
                p = self.path(origin, h)
                if p is None:
                    continue
                s = self.stores[h].get(key, window)
                if s is not None:
                    self._count(p)
                    return s
        self.stats.misses += 1
        return None

    def summary(self, window: str, origin: Address, alphabet_id: str = "hebrew-wlc",
                encoding: Encoding = Encoding(), keep_word: bool = True):
        """One window's summary, looked up in the network or computed and stored."""
        key = wc.window_key(window, alphabet_id, encoding, keep_word)
        s = self.get(key, window, origin)
        if s is None:
            s = mf.summarize(window, encoding, keep_word)
            self.put(key, window, s, origin)
        return s

    def summarize_text(self, text: str, origin: Address, alphabet_id: str = "hebrew-wlc",
                       encoding: Encoding = Encoding(), k: int = wc.DEFAULT_K,
                       keep_word: bool = True) -> mf.ChunkSummary:
        """The summary of ``text`` assembled from network-cached windows (equal to
        ``manifold.summarize``; Lean ``TextManifold.mapReduce``)."""
        parts = [self.summary(w, origin, alphabet_id, encoding, keep_word)
                 for w in wc.windows_of(text, k)]
        if not parts:
            return mf.identity(encoding, keep_word)
        return mf.reduce_tree(parts, encoding)
