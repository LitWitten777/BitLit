"""
Sheaves on finite spaces and Čech cohomology (Phase 1, sprint 9).

A **finite site** is a finite topological space given by its open sets: each
open has a name and a set of points.  A **cover** of an open ``U`` is a named
family of opens ``{U_i}`` with ``⋃ U_i = U``.  A **presheaf** of sets on the
site is given by its sections ``F(U)`` (string labels) and its restriction maps
``res(U, V, s) ∈ F(V)`` for ``V ⊆ U``.

The checker reports, with the same reasons and details as migration 012:

  site (``FiniteSite.problems``)
    base_typing             the base is not an open, or its points are not the
                            union of all opens (base)
    topology_empty          no open with no points ()
    topology_intersection   U ∩ V is not an open (opens = [U, V], sorted)
    topology_union          U ∪ V is not an open (opens = [U, V], sorted)
    cover_typing            the covered set or a member is not an open, or a
                            member is not contained in the covered set
                            (cover, open)
    cover_not_covering      the members do not cover the covered set (cover)

  presheaf (``Presheaf.problems``), in stages: each stage runs only when the
  previous ones found nothing
    site_invalid            the site has problems (site) — nothing else then
    section_typing          a section over a set that is not an open
                            (open, section)
    restriction_typing      a restriction row whose sets are not opens, whose
                            target is not contained in its source, or whose
                            section / image is not a section (from, to, section)
    cohomology_typing       a cohomology record with a negative degree, a cover
                            of another site, or a descriptor without a
                            non-negative integer ``cardinality`` (degree 0) or
                            ``rank`` (degree ≥ 1) (degree, cover)
    cochain_typing          a Čech cochain record with a negative degree or a
                            cover of another site (degree, cover)
    --
    restriction_missing     V ⊆ U, s ∈ F(U) and no res(U, V, s) (from, to, section)
    restriction_identity    res(U, U, s) ≠ s (open, section)
    restriction_composition W ⊆ V ⊆ U pairwise distinct and
                            res(V, W, res(U, V, s)) ≠ res(U, W, s)
                            (from, via, to, section)
    --
    sheaf_empty_open        F(∅) does not have exactly one section (count)
    sheaf_locality          on a cover: the number of unordered pairs s ≠ t in
                            F(U) restricting equally to every member
                            (cover, count)
    sheaf_gluing            on a cover: the number of compatible families with
                            no gluing (cover, count)
    cohomology_h0_mismatch  a degree-0 record on a cover whose ``cardinality``
                            is not the number of compatible families
                            (cover, recorded, computed)

The sheaf condition is checked on the *registered* covers (plus the empty cover
of ∅, which is ``sheaf_empty_open``); ``is_sheaf`` checks it on every cover of
every open.  This module is the in-memory reference implementation of the
checker migration 012 runs in Postgres (same reasons, same STRICT / PERMISSIVE
modes).

``LinearPresheaf`` computes Čech cohomology over F₂ (presheaves of F₂-vector
spaces given by restriction matrices); the database stores those results as
typed descriptors only.

Formal backing (``Formal/Sheaf.lean``, registry H-034 – H-036):

* ``isSheaf_iff_locality_and_gluing``: locality and gluing over every cover are
  exactly Mathlib's ``IsSheaf``;
* ``uniqueBot``: a sheaf has exactly one section over ∅ (``sheaf_empty_open``);
* ``constBool_gluing_not_locality`` / ``constEmpty_locality_not_gluing``: neither
  half implies the other (``constant_presheaf`` with two values / none);
* ``card_compatible_eq``: for a sheaf, the number of compatible families on a
  cover (``H⁰``) is the number of sections over the covered set;
* ``presheafToTypes_locality_and_gluing``: the presheaf of all functions passes
  (oracle for ``functions_presheaf``).
"""

from __future__ import annotations

import itertools
import logging
from dataclasses import dataclass, field
from typing import Any, Dict, FrozenSet, Iterable, List, Optional, Sequence, Tuple

from qbx.core.enforced_functor import EnforcementMode
from qbx.core.exceptions import QBXError

logger = logging.getLogger(__name__)

Problem = Tuple[str, Dict[str, Any]]

SITE_REASONS = (
    "base_typing",
    "topology_empty",
    "topology_intersection",
    "topology_union",
    "cover_typing",
    "cover_not_covering",
)

PRESHEAF_REASONS = (
    "site_invalid",
    "section_typing",
    "restriction_typing",
    "cohomology_typing",
    "cochain_typing",
    "restriction_missing",
    "restriction_identity",
    "restriction_composition",
    "sheaf_empty_open",
    "sheaf_locality",
    "sheaf_gluing",
    "cohomology_h0_mismatch",
)


class SheafViolation(QBXError):
    """Raised (STRICT mode) when a site or presheaf check fails."""

    def __init__(self, subject: str, reason: str, details: dict):
        self.subject = subject
        self.reason = reason
        self.details = details
        super().__init__(f"{subject}: {reason} {details}")


def _nonneg_int(v: Any) -> bool:
    return isinstance(v, int) and not isinstance(v, bool) and v >= 0


# ---------------------------------------------------------------------------
# Sites
# ---------------------------------------------------------------------------
@dataclass
class Cover:
    """A named cover: ``members`` claimed to cover ``covered``."""

    covered: Optional[str]
    members: List[str] = field(default_factory=list)


@dataclass
class FiniteSite:
    """A finite topological space recorded by its opens (name → points)."""

    name: str
    base: Optional[str] = None
    opens: Dict[str, FrozenSet[str]] = field(default_factory=dict)
    covers: Dict[str, Cover] = field(default_factory=dict)

    def add_open(self, name: str, points: Iterable[str]) -> str:
        pts = frozenset(points)
        if name in self.opens:
            raise ValueError(f"open {name!r} already recorded")
        if pts in self.opens.values():
            raise ValueError(f"an open with points {sorted(pts)} is already recorded")
        self.opens[name] = pts
        return name

    def add_cover(self, name: str, covered: Optional[str], members: Sequence[str]) -> str:
        if name in self.covers:
            raise ValueError(f"cover {name!r} already recorded")
        self.covers[name] = Cover(covered, list(dict.fromkeys(members)))
        return name

    def open_of(self, points: FrozenSet[str]) -> Optional[str]:
        for n, p in self.opens.items():
            if p == points:
                return n
        return None

    @property
    def empty_open(self) -> Optional[str]:
        return self.open_of(frozenset())

    def subset(self, v: str, u: str) -> bool:
        return self.opens[v] <= self.opens[u]

    def inter(self, u: str, v: str) -> Optional[str]:
        return self.open_of(self.opens[u] & self.opens[v])

    def cover_problems(self, name: str) -> List[Problem]:
        cov = self.covers[name]
        out: List[Problem] = []
        if cov.covered not in self.opens:
            out.append(("cover_typing", {"cover": name, "open": cov.covered}))
            return out
        ok = True
        for m in cov.members:
            if m not in self.opens or not self.subset(m, cov.covered):
                out.append(("cover_typing", {"cover": name, "open": m}))
                ok = False
        if ok:
            union = frozenset().union(*(self.opens[m] for m in cov.members))
            if union != self.opens[cov.covered]:
                out.append(("cover_not_covering", {"cover": name}))
        return out

    def problems(self) -> List[Problem]:
        out: List[Problem] = []
        every = frozenset().union(*self.opens.values())
        if self.base not in self.opens or self.opens[self.base] != every:
            out.append(("base_typing", {"base": self.base}))
        if self.empty_open is None:
            out.append(("topology_empty", {}))
        values = set(self.opens.values())
        for u, v in itertools.combinations(sorted(self.opens), 2):
            if self.opens[u] & self.opens[v] not in values:
                out.append(("topology_intersection", {"opens": [u, v]}))
            if self.opens[u] | self.opens[v] not in values:
                out.append(("topology_union", {"opens": [u, v]}))
        for name in self.covers:
            out.extend(self.cover_problems(name))
        return out

    def is_valid(self) -> bool:
        return not self.problems()

    def all_covers(self, u: str) -> Iterable[List[str]]:
        """Every family of opens inside ``u`` whose union is ``u`` (as sets of opens)."""
        inside = sorted(v for v in self.opens if self.subset(v, u))
        for r in range(len(inside) + 1):
            for fam in itertools.combinations(inside, r):
                if frozenset().union(*(self.opens[v] for v in fam)) == self.opens[u]:
                    yield list(fam)


# ---------------------------------------------------------------------------
# Presheaves of sets
# ---------------------------------------------------------------------------
@dataclass
class CohomologyRecord:
    degree: int
    cover: Optional[str]
    descriptor: Dict[str, Any] = field(default_factory=dict)


@dataclass
class CochainRecord:
    degree: int
    cover: Optional[str]


@dataclass
class Presheaf:
    """A presheaf of sets on a finite site, by sections and restriction rows."""

    site: FiniteSite
    name: str = "F"
    sections: Dict[str, List[str]] = field(default_factory=dict)      # open -> labels
    restrictions: Dict[Tuple[str, str, str], str] = field(default_factory=dict)
    cohomology: List[CohomologyRecord] = field(default_factory=list)
    cochains: List[CochainRecord] = field(default_factory=list)

    # -- data ---------------------------------------------------------------
    def F(self, u: str) -> List[str]:
        return self.sections.get(u, [])

    def res(self, u: str, v: str, s: str) -> Optional[str]:
        return self.restrictions.get((u, v, s))

    # -- stages -------------------------------------------------------------
    def typing_problems(self) -> List[Problem]:
        S = self.site
        out: List[Problem] = []
        for u, secs in self.sections.items():
            if u not in S.opens:
                out.extend(("section_typing", {"open": u, "section": s}) for s in secs)
        for (u, v, s), t in self.restrictions.items():
            ok = (u in S.opens and v in S.opens and S.subset(v, u)
                  and s in self.F(u) and t in self.F(v))
            if not ok:
                out.append(("restriction_typing", {"from": u, "to": v, "section": s}))
        for rec in self.cohomology:
            key = "cardinality" if rec.degree == 0 else "rank"
            if (rec.degree < 0 or (rec.cover is not None and rec.cover not in S.covers)
                    or not _nonneg_int(rec.descriptor.get(key))):
                out.append(("cohomology_typing", {"degree": rec.degree, "cover": rec.cover}))
        for ch in self.cochains:
            if ch.degree < 0 or (ch.cover is not None and ch.cover not in S.covers):
                out.append(("cochain_typing", {"degree": ch.degree, "cover": ch.cover}))
        return out

    def functoriality_problems(self) -> List[Problem]:
        S = self.site
        out: List[Problem] = []
        for u in S.opens:
            for s in self.F(u):
                for v in S.opens:
                    if S.subset(v, u) and self.res(u, v, s) is None:
                        out.append(("restriction_missing", {"from": u, "to": v, "section": s}))
        for u in S.opens:
            for s in self.F(u):
                t = self.res(u, u, s)
                if t is not None and t != s:
                    out.append(("restriction_identity", {"open": u, "section": s}))
        for u, v, w in itertools.permutations(S.opens, 3):
            if not (S.subset(v, u) and S.subset(w, v)):
                continue
            for s in self.F(u):
                a = self.res(u, v, s)
                b = self.res(v, w, a) if a is not None else None
                c = self.res(u, w, s)
                if b is not None and c is not None and b != c:
                    out.append(("restriction_composition",
                                {"from": u, "via": v, "to": w, "section": s}))
        return out

    def compatible_families(self, covered: str, members: Sequence[str]) -> List[Tuple[str, ...]]:
        """The compatible families on ``members`` (one section per member) — Čech H⁰."""
        S = self.site
        fams: List[Tuple[str, ...]] = [()]
        for k, uk in enumerate(members):
            nxt = []
            for fam in fams:
                for s in self.F(uk):
                    if all(self.res(members[j], S.inter(members[j], uk), fam[j])
                           == self.res(uk, S.inter(members[j], uk), s) for j in range(k)):
                        nxt.append(fam + (s,))
            fams = nxt
        return fams

    def gluings(self, covered: str, members: Sequence[str], fam: Sequence[str]) -> List[str]:
        return [t for t in self.F(covered)
                if all(self.res(covered, m, t) == s for m, s in zip(members, fam))]

    def locality_failures(self, covered: str, members: Sequence[str]) -> int:
        secs = self.F(covered)
        return sum(1 for s, t in itertools.combinations(secs, 2)
                   if all(self.res(covered, m, s) == self.res(covered, m, t) for m in members))

    def gluing_failures(self, covered: str, members: Sequence[str]) -> int:
        return sum(1 for fam in self.compatible_families(covered, members)
                   if not self.gluings(covered, members, fam))

    def sheaf_problems(self) -> List[Problem]:
        S = self.site
        out: List[Problem] = []
        n = len(self.F(S.empty_open))
        if n != 1:
            out.append(("sheaf_empty_open", {"count": n}))
        for name, cov in S.covers.items():
            k = self.locality_failures(cov.covered, cov.members)
            if k:
                out.append(("sheaf_locality", {"cover": name, "count": k}))
            k = self.gluing_failures(cov.covered, cov.members)
            if k:
                out.append(("sheaf_gluing", {"cover": name, "count": k}))
        for rec in self.cohomology:
            if rec.degree == 0 and rec.cover is not None:
                cov = S.covers[rec.cover]
                computed = len(self.compatible_families(cov.covered, cov.members))
                if rec.descriptor["cardinality"] != computed:
                    out.append(("cohomology_h0_mismatch", {
                        "cover": rec.cover, "recorded": rec.descriptor["cardinality"],
                        "computed": computed}))
        return out

    def problems(self) -> List[Problem]:
        if self.site.problems():
            return [("site_invalid", {"site": self.site.name})]
        for stage in (self.typing_problems, self.functoriality_problems):
            out = stage()
            if out:
                return out
        return self.sheaf_problems()

    def is_valid(self) -> bool:
        return not self.problems()

    def is_presheaf(self) -> bool:
        return (self.site.is_valid() and not self.typing_problems()
                and not self.functoriality_problems())

    def is_sheaf(self) -> bool:
        """The sheaf condition on *every* cover of every open (exhaustive)."""
        if not self.is_presheaf():
            return False
        S = self.site
        for u in S.opens:
            for members in S.all_covers(u):
                if self.locality_failures(u, members) or self.gluing_failures(u, members):
                    return False
        return True


class SheafChecker:
    """Runs the checks, logging every problem and raising in STRICT mode."""

    def __init__(self, mode: Optional[EnforcementMode] = None):
        self.mode = mode or EnforcementMode.from_env()
        self.violations: List[Problem] = []

    def _report(self, subject: str, problems: List[Problem]) -> bool:
        for reason, details in problems:
            logger.warning("%s: %s %s", subject, reason, details)
            self.violations.append((reason, details))
        if problems and self.mode == EnforcementMode.STRICT:
            reason, details = problems[0]
            raise SheafViolation(subject, reason, details)
        return not problems

    def check_site(self, site: FiniteSite) -> bool:
        return self._report(site.name, site.problems())

    def check(self, presheaf: Presheaf) -> bool:
        return self._report(presheaf.name, presheaf.problems())


# ---------------------------------------------------------------------------
# Builders
# ---------------------------------------------------------------------------
def _pts_name(points: Iterable[str]) -> str:
    pts = sorted(points)
    return "U_" + ("".join(pts) if pts else "empty")


def finite_space(open_sets: Iterable[Iterable[str]], name: str = "S") -> FiniteSite:
    """A site whose opens are the given point sets, named ``U_<points>``
    (``U_empty`` for ∅); the base is the open with every point, if recorded."""
    site = FiniteSite(name)
    for pts in open_sets:
        pts = frozenset(pts)
        if site.open_of(pts) is None:
            site.add_open(_pts_name(pts), pts)
    site.base = site.open_of(frozenset().union(*site.opens.values()))
    return site


def generated_topology(points: Sequence[str], generators: Iterable[Iterable[str]],
                       name: str = "S") -> FiniteSite:
    """The topology on ``points`` generated by ``generators`` (closed under
    finite unions and intersections, with ∅ and the whole space)."""
    opens = {frozenset(), frozenset(points)} | {frozenset(g) for g in generators}
    changed = True
    while changed:
        changed = False
        for a, b in itertools.combinations(list(opens), 2):
            for c in (a | b, a & b):
                if c not in opens:
                    opens.add(c)
                    changed = True
    return finite_space(sorted(opens, key=lambda s: (len(s), sorted(s))), name)


def _func_label(f: Dict[str, str]) -> str:
    return ",".join(f"{p}={f[p]}" for p in sorted(f)) or "()"


def functions_presheaf(site: FiniteSite, values: Dict[str, Sequence[str]],
                       name: str = "Fun") -> Presheaf:
    """``F(U) = ∏_{p ∈ U} values[p]`` with restriction by projection — the
    presheaf of all dependent functions, a sheaf on every space
    (``presheafToTypes_locality_and_gluing``)."""
    F = Presheaf(site, name)
    funcs: Dict[str, List[Dict[str, str]]] = {}
    for u, pts in site.opens.items():
        pts_l = sorted(pts)
        funcs[u] = [dict(zip(pts_l, vs)) for vs in itertools.product(*(values[p] for p in pts_l))]
        F.sections[u] = [_func_label(f) for f in funcs[u]]
    for u in site.opens:
        for v in site.opens:
            if site.subset(v, u):
                for f in funcs[u]:
                    F.restrictions[(u, v, _func_label(f))] = _func_label(
                        {p: f[p] for p in site.opens[v]})
    return F


def constant_presheaf(site: FiniteSite, values: Sequence[str],
                      empty_values: Optional[Sequence[str]] = None,
                      name: str = "Const") -> Presheaf:
    """``F(U) = values`` with identity restrictions, except ``F(∅) =
    empty_values`` (default: ``values``) with every restriction to ∅ sending
    a section to the first of them (``empty_values`` must then be nonempty or
    ``values`` empty).  With ``empty_values = None``: two values give
    ``constBool``, none give ``constEmpty``."""
    F = Presheaf(site, name)
    e = site.empty_open
    for u in site.opens:
        F.sections[u] = list(empty_values if (u == e and empty_values is not None) else values)
    for u in site.opens:
        for v in site.opens:
            if not site.subset(v, u):
                continue
            for s in F.F(u):
                if v == e and empty_values is not None and u != e:
                    F.restrictions[(u, v, s)] = empty_values[0]
                else:
                    F.restrictions[(u, v, s)] = s
    return F


# ---------------------------------------------------------------------------
# Čech cohomology over F₂
# ---------------------------------------------------------------------------
Matrix = List[List[int]]


def rank_f2(rows: Matrix) -> int:
    """Rank over F₂ (Gaussian elimination on bit masks)."""
    basis: Dict[int, int] = {}
    for row in rows:
        x = 0
        for j, b in enumerate(row):
            if b & 1:
                x |= 1 << j
        while x:
            hi = x.bit_length() - 1
            if hi in basis:
                x ^= basis[hi]
            else:
                basis[hi] = x
                break
    return len(basis)


def matmul_f2(a: Matrix, b: Matrix, inner: int, cols: int) -> Matrix:
    """``a · b`` over F₂ for ``a`` (· × inner) and ``b`` (inner × cols)."""
    return [[sum(a[i][k] * b[k][j] for k in range(inner)) % 2 for j in range(cols)]
            for i in range(len(a))]


@dataclass
class LinearPresheaf:
    """A presheaf of F₂-vector spaces on a finite site: ``dims[U]`` and, for
    ``V ⊆ U``, a ``dims[V] × dims[U]`` matrix ``maps[(U, V)]``."""

    site: FiniteSite
    dims: Dict[str, int] = field(default_factory=dict)
    maps: Dict[Tuple[str, str], Matrix] = field(default_factory=dict)

    def mat(self, u: str, v: str) -> Matrix:
        return self.maps[(u, v)]

    def is_functorial(self) -> bool:
        S = self.site
        for u in S.opens:
            ident = [[int(i == j) for j in range(self.dims[u])] for i in range(self.dims[u])]
            if self.maps.get((u, u)) != ident:
                return False
        for u, v, w in itertools.product(S.opens, repeat=3):
            if S.subset(v, u) and S.subset(w, v):
                if matmul_f2(self.mat(v, w), self.mat(u, v), self.dims[v], self.dims[u]) != self.mat(u, w):
                    return False
        return True

    def _simplices(self, members: Sequence[str], n: int) -> List[Tuple[int, ...]]:
        return list(itertools.combinations(range(len(members)), n + 1))

    def _inter(self, members: Sequence[str], simplex: Tuple[int, ...]) -> str:
        pts = frozenset.intersection(*(self.site.opens[members[i]] for i in simplex))
        u = self.site.open_of(pts)
        if u is None:
            raise ValueError("intersection of cover members is not an open")
        return u

    def cochain_dim(self, members: Sequence[str], n: int) -> int:
        return sum(self.dims[self._inter(members, s)] for s in self._simplices(members, n))

    def differential(self, members: Sequence[str], n: int) -> Matrix:
        """``d : C^n → C^{n+1}`` (signs vanish over F₂)."""
        src = self._simplices(members, n)
        tgt = self._simplices(members, n + 1)
        src_off, off = {}, 0
        for s in src:
            src_off[s] = off
            off += self.dims[self._inter(members, s)]
        rows: Matrix = []
        for t in tgt:
            ut = self._inter(members, t)
            block = [[0] * off for _ in range(self.dims[ut])]
            for k in range(len(t)):
                face = t[:k] + t[k + 1:]
                uf = self._inter(members, face)
                m = self.mat(uf, ut)
                for i in range(self.dims[ut]):
                    for j in range(self.dims[uf]):
                        block[i][src_off[face] + j] ^= m[i][j] & 1
            rows.extend(block)
        return rows

    def cohomology(self, members: Sequence[str]) -> List[int]:
        """Dimensions of Čech ``H^n`` of the cover for ``n = 0 … len(members) - 1``."""
        dims = [self.cochain_dim(members, n) for n in range(len(members))]
        ranks = [rank_f2(self.differential(members, n)) if n + 1 < len(members) else 0
                 for n in range(len(members))]
        return [dims[n] - ranks[n] - (ranks[n - 1] if n else 0) for n in range(len(members))]


def constant_linear(site: FiniteSite, dim: int = 1) -> LinearPresheaf:
    """The presheaf ``U ↦ F₂^dim`` for nonempty ``U`` and ``0`` on ∅, identity
    restrictions — on a cover whose intersections are empty or connected its
    Čech cohomology is the simplicial cohomology of the nerve."""
    L = LinearPresheaf(site)
    e = site.empty_open
    for u in site.opens:
        L.dims[u] = 0 if u == e else dim
    for u in site.opens:
        for v in site.opens:
            if site.subset(v, u):
                L.maps[(u, v)] = [[int(i == j) for j in range(L.dims[u])] for i in range(L.dims[v])]
    return L
