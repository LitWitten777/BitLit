"""
QBX file format (QBX.md §33) — load/save.

The canonical on-disk form is JSON (always available).  The human-readable
YAML form of §33 is supported when PyYAML is installed.

Document shape::

    qbx: "0.1"
    braid:
      strands: 3
      word: [{sigma: 1, power: 1}, {sigma: 2, power: -1}]
    objects: [{id: A, type: anyon}, ...]     # optional strand metadata
    fusion: {rules: []}
    quantum: {representation: "R", verify: true}
    geometry: {embedding: null}
    invariants: {compute: [permutation, writhe]}
"""

from __future__ import annotations

import json
from typing import Any, Dict, List

from qbx_ir.core.braid import Braid
from qbx_ir.core.primitive import Generator, Strand

QBX_FORMAT_VERSION = "0.1"


def to_document(braid: Braid, compute: List[str] = None) -> Dict[str, Any]:
    word = [{"sigma": g.index, "power": g.sign} for g in braid.word]
    return {
        "qbx": QBX_FORMAT_VERSION,
        "name": braid.name,
        "braid": {"strands": braid.strand_count, "word": word},
        "objects": [
            {"id": s.id, "type": s.particle_type, "state": s.state,
             "orientation": s.orientation,
             "geometry": list(s.geometry) if s.geometry else None}
            for s in braid.strands
        ],
        "fusion": {"rules": []},
        "quantum": {"representation": "R", "verify": True},
        "geometry": {"embedding": None},
        "invariants": {"compute": list(compute or ["permutation", "writhe"])},
        "metadata": braid.metadata,
    }


def _expand_word(entries) -> List[Generator]:
    out: List[Generator] = []
    for e in entries:
        if isinstance(e, int):
            out.append(Generator.from_short(e))
            continue
        sigma, power = int(e["sigma"]), int(e.get("power", 1))
        if power == 0:
            continue
        g = Generator(sigma, 1 if power > 0 else -1)
        out.extend([g] * abs(power))  # σ^k expands to k generators
    return out


def from_document(doc: Dict[str, Any]) -> Braid:
    if str(doc.get("qbx", QBX_FORMAT_VERSION)) != QBX_FORMAT_VERSION:
        raise ValueError(f"unsupported QBX version {doc.get('qbx')}")
    n = int(doc["braid"]["strands"])
    word = _expand_word(doc["braid"].get("word", []))
    objects = doc.get("objects") or []
    strands = []
    for k in range(n):
        o = objects[k] if k < len(objects) else {}
        geom = o.get("geometry")
        strands.append(Strand(
            id=k + 1,
            particle_type=str(o.get("type", "line")),
            state=o.get("state"),
            orientation=int(o.get("orientation", 1)),
            geometry=tuple(geom) if geom else None,
        ))
    return Braid(strand_count=n, word=tuple(word), strands=tuple(strands),
                 name=str(doc.get("name", "B")), metadata=dict(doc.get("metadata") or {}))


def dumps(braid: Braid, fmt: str = "json") -> str:
    doc = to_document(braid)
    if fmt == "json":
        return json.dumps(doc, indent=2, ensure_ascii=False, sort_keys=False)
    if fmt == "yaml":
        import yaml  # optional dependency

        return yaml.safe_dump(doc, allow_unicode=True, sort_keys=False)
    raise ValueError(f"unknown format {fmt}")


def loads(text: str, fmt: str = "json") -> Braid:
    if fmt == "json":
        return from_document(json.loads(text))
    if fmt == "yaml":
        import yaml  # optional dependency

        return from_document(yaml.safe_load(text))
    raise ValueError(f"unknown format {fmt}")


def save(braid: Braid, path: str) -> None:
    fmt = "yaml" if path.endswith((".yaml", ".yml")) else "json"
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(dumps(braid, fmt))


def load(path: str) -> Braid:
    fmt = "yaml" if path.endswith((".yaml", ".yml")) else "json"
    with open(path, encoding="utf-8") as fh:
        return loads(fh.read(), fmt)
