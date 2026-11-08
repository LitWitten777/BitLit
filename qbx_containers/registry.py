"""Container descriptors, composites, and the registry checker.

Descriptor (``containers/descriptors/<name>.json``)::

    {
      "name": "braid_words",
      "version": "1.0.0",
      "curvature": "negative",
      "carrier": "free(4)",                  # see qbx_containers.carriers
      "development": "tree(4)",              # optional: the cover whose growth is the curvature
      "metric": {"formula": "...", "lean": "QBX.Formal.Foundations.treeDist"},
      "algebra": ["concat", "rewrite", ...],
      "boundary": {"kind": "leaves", "attaches": ["braid_invariants"]},
      "address": "path",                     # default from curvature
      "time": "causal",                      # default from curvature
      "hosting": {"preserve": ["metric", "algebra"], "substrates": ["cpu", "dht"]},
      "lean": {"correctness": "QBX.Formal.Foundations.tree_correct"},
      "code": ["src/qbx_ir/core/braid.py"],
      "notes": "..."
    }

Composite (``containers/composites/<name>.json``) is a ``pipeline``, ``product``, ``bundle`` or
``sum`` of named containers; see ``QBX/containers/README.md``.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from qbx_containers import carriers
from qbx_containers.curvature import (
    ADDRESS_KIND,
    CURVATURES,
    FORBIDDEN_OPS,
    TIME_KIND,
    classify_profile,
    compose_bundle,
    compose_product,
    compose_sum,
)

QBX_ROOT = Path(__file__).resolve().parents[2]
CONTAINER_DIR = QBX_ROOT / "containers"
_SEMVER = re.compile(r"^\d+\.\d+\.\d+$")
BOUNDARY_KINDS = ("none", "closed", "leaves", "edge", "port")
PROFILE_RADIUS = 40


class RegistryError(Exception):
    pass


@dataclass
class Container:
    name: str
    version: str
    curvature: str
    carrier: str
    metric: Dict[str, Any]
    algebra: List[str]
    boundary: Dict[str, Any]
    development: Optional[str] = None
    address: Optional[str] = None
    time: Optional[str] = None
    hosting: Dict[str, Any] = field(default_factory=dict)
    lean: Dict[str, str] = field(default_factory=dict)
    code: List[str] = field(default_factory=list)
    adaptive: Optional[Dict[str, Any]] = None
    override_reason: Optional[str] = None
    notes: str = ""
    path: Optional[Path] = None

    @classmethod
    def from_dict(cls, d: Dict[str, Any], path: Optional[Path] = None) -> "Container":
        missing = [k for k in ("name", "version", "curvature", "carrier", "metric", "algebra",
                               "boundary") if k not in d]
        if missing:
            raise RegistryError(f"{path or d.get('name')}: missing fields {missing}")
        known = set(cls.__dataclass_fields__) - {"path"}
        extra = set(d) - known
        if extra:
            raise RegistryError(f"{d['name']}: unknown fields {sorted(extra)}")
        return cls(**d, path=path)

    @property
    def effective_development(self) -> str:
        return self.development or carriers.development(self.carrier)

    @property
    def effective_address(self) -> str:
        return self.address or ADDRESS_KIND[self.curvature]

    @property
    def effective_time(self) -> str:
        return self.time or TIME_KIND[self.curvature]

    def measured_curvature(self) -> Optional[str]:
        prof = carriers.volume_profile(self.effective_development, PROFILE_RADIUS)
        if prof is None:
            return None
        if carriers.parse_carrier(self.effective_development)[0] == "finite":
            return "positive"
        return classify_profile(prof)


@dataclass
class Composite:
    name: str
    kind: str
    data: Dict[str, Any]
    path: Optional[Path] = None


def _lean_index(root: Path) -> set:
    """Short and qualified names of every theorem/def/abbrev/structure under QBX/Formal."""
    names: set = set()
    pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                     r"(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s:({\[]+)")
    for f in (root / "Formal").rglob("*.lean"):
        ns: List[str] = []
        for line in f.read_text(encoding="utf-8", errors="replace").splitlines():
            m = re.match(r"^namespace\s+(\S+)", line)
            if m:
                ns.append(m.group(1))
                continue
            m = re.match(r"^end\s+(\S+)", line)
            if m and ns and ns[-1] == m.group(1):
                ns.pop()
                continue
            m = pat.match(line)
            if m:
                short = m.group(1)
                names.add(short)
                if ns:
                    names.add(".".join(ns + [short]))
    return names


class Registry:
    def __init__(self, containers: Dict[str, Container], composites: Dict[str, Composite],
                 root: Path = QBX_ROOT):
        self.containers = containers
        self.composites = composites
        self.root = root
        self._lean: Optional[set] = None

    # ------------------------------------------------------------------ lookups
    def lean_names(self) -> set:
        if self._lean is None:
            self._lean = _lean_index(self.root)
        return self._lean

    def curvature_of(self, name: str) -> str:
        if name in self.containers:
            return self.containers[name].curvature
        if name in self.composites:
            return self.composite_curvature(self.composites[name])
        raise RegistryError(f"unknown container {name!r}")

    def composite_curvature(self, c: Composite) -> str:
        d = c.data
        if c.kind == "product":
            cs = [self.curvature_of(x) for x in d["factors"]]
            out = cs[0]
            for x in cs[1:]:
                out = compose_product(out, x)
            return out
        if c.kind == "bundle":
            return compose_bundle(self.curvature_of(d["base"]), self.curvature_of(d["fiber"]))
        if c.kind == "sum":
            return compose_sum(self.curvature_of(x) for x in d["summands"])
        if c.kind == "pipeline":
            # A pipeline is not one space; report the worst stage (its capacity requirement).
            return compose_sum(self.curvature_of(s["container"]) for s in d["stages"])
        raise RegistryError(f"{c.name}: unknown composite kind {c.kind!r}")

    # ------------------------------------------------------------------ checks
    def check_container(self, c: Container) -> Tuple[List[str], List[str]]:
        errors: List[str] = []
        warnings: List[str] = []
        if c.curvature not in CURVATURES:
            errors.append(f"curvature {c.curvature!r} not in {CURVATURES}")
            return errors, warnings
        if not _SEMVER.match(c.version):
            errors.append(f"version {c.version!r} is not MAJOR.MINOR.PATCH")
        for op in c.algebra:
            why = FORBIDDEN_OPS[c.curvature].get(op)
            if why:
                errors.append(f"algebra declares {op!r}, impossible for {c.curvature} curvature: {why}")
        kind = c.boundary.get("kind")
        if kind not in BOUNDARY_KINDS:
            errors.append(f"boundary.kind {kind!r} not in {BOUNDARY_KINDS}")
        for t in c.boundary.get("attaches", []):
            if t not in self.containers and t not in self.composites:
                errors.append(f"boundary attaches to unknown container {t!r}")
        overridden = (c.address and c.address != ADDRESS_KIND[c.curvature]) or \
                     (c.time and c.time != TIME_KIND[c.curvature])
        if overridden and not c.override_reason:
            errors.append("address/time differ from the curvature defaults "
                          f"({ADDRESS_KIND[c.curvature]}/{TIME_KIND[c.curvature]}) without override_reason")
        try:
            measured = c.measured_curvature()
        except ValueError as e:
            errors.append(f"carrier: {e}")
            measured = None
        if measured is None:
            warnings.append(f"carrier {c.effective_development!r} is not enumerable; curvature is declared only")
        elif measured != c.curvature:
            errors.append(f"declared {c.curvature} but the volume profile of "
                          f"{c.effective_development} reads {measured}")
        names = self.lean_names()
        refs = [v for v in c.lean.values()] + ([c.metric["lean"]] if "lean" in c.metric else [])
        for ref in refs:
            if ref not in names and ref.split(".")[-1] not in names:
                errors.append(f"Lean reference {ref!r} does not resolve under QBX/Formal")
        for p in c.code:
            if not (self.root / p).exists():
                errors.append(f"code path {p!r} does not exist")
        if c.adaptive is not None:
            to = c.adaptive.get("to")
            if to not in CURVATURES or "trigger" not in c.adaptive:
                errors.append("adaptive needs 'trigger' and a target curvature 'to'")
            elif to != c.curvature and not c.adaptive.get("new_container"):
                warnings.append("adaptive curvature change: per the versioning rule this yields a "
                                "new container; name it in adaptive.new_container")
        return errors, warnings

    def check_composite(self, c: Composite) -> Tuple[List[str], List[str]]:
        errors: List[str] = []
        warnings: List[str] = []
        d = c.data
        try:
            computed = self.composite_curvature(c)
        except (RegistryError, KeyError) as e:
            return [str(e)], warnings
        declared = d.get("curvature")
        if declared and declared != computed:
            errors.append(f"declared curvature {declared} but the composition rules give {computed}")
        if c.kind == "sum":
            algs = {tuple(sorted(self.containers[x].algebra)) for x in d["summands"]
                    if x in self.containers}
            if len(algs) > 1:
                errors.append("sum of containers with different algebras")
        if c.kind == "bundle" and "connection" not in d:
            errors.append("bundle needs a 'connection' (how fibers over neighbouring base points attach)")
        if c.kind == "pipeline":
            stages = d["stages"]
            for i, s in enumerate(stages):
                if s["container"] not in self.containers and s["container"] not in self.composites:
                    errors.append(f"stage {i}: unknown container {s['container']!r}")
            trans = d.get("transitions", [])
            if len(trans) != len(stages) - 1:
                errors.append(f"{len(stages)} stages need {len(stages) - 1} transitions, got {len(trans)}")
            if errors:
                return errors, warnings
            for i, t in enumerate(trans):
                a, b = stages[i]["container"], stages[i + 1]["container"]
                ca, cb = self.curvature_of(a), self.curvature_of(b)
                if ca != cb:
                    if not t.get("curvature_changing"):
                        errors.append(f"transition {a} -> {b} changes curvature {ca} -> {cb} "
                                      "but is not declared curvature_changing")
                    elif t.get("to") != cb:
                        errors.append(f"transition {a} -> {b}: declared destination {t.get('to')!r}, actual {cb}")
                elif t.get("curvature_changing"):
                    warnings.append(f"transition {a} -> {b} is declared curvature_changing but preserves {ca}")
                ka = self._boundary_kind(a)
                kb = self._boundary_kind(b)
                if (ka == "none") != (kb == "none") and "connection" not in t:
                    errors.append(f"transition {a} -> {b} joins a boundary-free container to a bounded "
                                  "one without a 'connection'")
                if "operation" not in t:
                    errors.append(f"transition {a} -> {b} has no 'operation'")
                elif "lean" in t:
                    names = self.lean_names()
                    if t["lean"] not in names and t["lean"].split(".")[-1] not in names:
                        errors.append(f"transition {a} -> {b}: Lean reference {t['lean']!r} does not resolve")
        return errors, warnings

    def _boundary_kind(self, name: str) -> str:
        if name in self.containers:
            return self.containers[name].boundary.get("kind", "none")
        return self.composites[name].data.get("boundary", {}).get("kind", "port")

    def check(self) -> Dict[str, Tuple[List[str], List[str]]]:
        out = {}
        for n, c in sorted(self.containers.items()):
            out[n] = self.check_container(c)
        for n, c in sorted(self.composites.items()):
            out[n] = self.check_composite(c)
        return out


def load_registry(root: Path = CONTAINER_DIR) -> Registry:
    containers: Dict[str, Container] = {}
    composites: Dict[str, Composite] = {}
    for f in sorted((root / "descriptors").glob("*.json")):
        c = Container.from_dict(json.loads(f.read_text(encoding="utf-8")), f)
        if c.name in containers:
            raise RegistryError(f"duplicate container {c.name}")
        containers[c.name] = c
    for f in sorted((root / "composites").glob("*.json")):
        d = json.loads(f.read_text(encoding="utf-8"))
        if d["name"] in containers or d["name"] in composites:
            raise RegistryError(f"duplicate name {d['name']}")
        composites[d["name"]] = Composite(d["name"], d["kind"], d, f)
    return Registry(containers, composites, root.parent)


def classify_revision(old: Container, new: Container) -> str:
    """Versioning rule (README, "Versioning"):

    * curvature change      -> ``new_container`` (a different geometric object: rename it);
    * metric change         -> ``major``;
    * algebra ops removed   -> ``major``; ops only added -> ``minor``;
    * anything else         -> ``patch``.
    """
    if old.curvature != new.curvature:
        return "new_container"
    if old.metric.get("formula") != new.metric.get("formula") or old.carrier != new.carrier:
        return "major"
    o, n = set(old.algebra), set(new.algebra)
    if o - n:
        return "major"
    if n - o:
        return "minor"
    return "patch"
