"""
The Braid class — the canonical QBX-IR object.

A Braid is defined by:

- strand_count: number of strands (≥ 1)
- word: tuple of Generator (σ_i^{sign})
- strands: initial strand metadata (one per bottom position)
- name: human label

The word is written from bottom to top of the diagram. The first generator
is applied at the bottom.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from qbx_ir.core.primitive import Crossing, Generator, Strand


def _default_strands(strand_count: int) -> Tuple[Strand, ...]:
    return tuple(Strand(id=i + 1) for i in range(strand_count))


@dataclass
class Braid:
    strand_count: int
    word: Tuple[Generator, ...]
    strands: Tuple[Strand, ...]
    name: str = "B"
    metadata: Dict[str, Any] = field(default_factory=dict)

    # ---- Construction ----------------------------------------------------

    def __post_init__(self):
        if self.strand_count < 1:
            raise ValueError(f"strand_count must be ≥ 1, got {self.strand_count}")
        self.word = tuple(self.word)
        self.strands = tuple(self.strands)
        if len(self.strands) != self.strand_count:
            raise ValueError(
                f"Expected {self.strand_count} strands, got {len(self.strands)}"
            )
        # Validate generator indices: σ_i needs positions i and i+1.
        for g in self.word:
            if g.index >= self.strand_count:
                raise ValueError(
                    f"Generator index {g.index} out of range "
                    f"for {self.strand_count}-strand braid"
                )

    @classmethod
    def from_short_form(
        cls,
        strand_count: int,
        short: Sequence[int],
        name: str = "B",
        strand_metadata: Optional[Iterable[Strand]] = None,
    ) -> "Braid":
        """
        Build a braid from the short form.

        Example: from_short_form(3, [1, 2, -1]) → σ_1 σ_2 σ_1⁻¹
        """
        word = tuple(Generator.from_short(x) for x in short)
        if strand_metadata is None:
            strands = _default_strands(strand_count)
        else:
            strands = tuple(strand_metadata)
        return cls(
            strand_count=strand_count,
            word=word,
            strands=strands,
            name=name,
        )

    @classmethod
    def identity(cls, strand_count: int, name: str = "Id") -> "Braid":
        """The trivial (identity) braid on n strands."""
        return cls(
            strand_count=strand_count,
            word=(),
            strands=_default_strands(strand_count),
            name=name,
        )

    @classmethod
    def generator(
        cls,
        strand_count: int,
        index: int,
        sign: int = 1,
        name: Optional[str] = None,
    ) -> "Braid":
        """A single-generator braid."""
        g = Generator(index, sign)
        return cls(
            strand_count=strand_count,
            word=(g,),
            strands=_default_strands(strand_count),
            name=name or str(g),
        )

    @classmethod
    def half_twist(cls, strand_count: int, name: str = "Δ") -> "Braid":
        """
        The Garside fundamental braid Δ_n (positive half twist):
        Δ_n = (σ_1 σ_2 … σ_{n-1})(σ_1 … σ_{n-2}) … (σ_1).
        """
        short: List[int] = []
        for top in range(strand_count - 1, 0, -1):
            short.extend(range(1, top + 1))
        return cls.from_short_form(strand_count, short, name=name)

    @classmethod
    def full_twist(cls, strand_count: int, name: str = "Δ²") -> "Braid":
        """The full twist Δ_n², a generator of the centre of B_n (n ≥ 3)."""
        d = cls.half_twist(strand_count)
        return d.compose(d).with_name(name)

    @classmethod
    def from_qbx_dict(cls, data: Dict[str, Any]) -> "Braid":
        """Inverse of :meth:`to_qbx_dict`."""
        n = int(data["topology"]["strands"])
        word = data["braid"]["word"]
        strands_data = data.get("strands")
        if strands_data:
            strands = tuple(
                Strand(
                    id=int(s["id"]),
                    particle_type=s.get("particle_type", "line"),
                    state=s.get("state"),
                    orientation=int(s.get("orientation", 1)),
                    geometry=tuple(s["geometry"]) if s.get("geometry") else None,
                )
                for s in strands_data
            )
        else:
            strands = _default_strands(n)
        return cls(
            strand_count=n,
            word=tuple(Generator.from_short(int(x)) for x in word),
            strands=strands,
            name=data.get("name", "B"),
            metadata=dict(data.get("metadata") or {}),
        )

    # ---- Word manipulation ------------------------------------------------

    def short_form(self) -> List[int]:
        """Return the word as a list of signed integers."""
        return [g.to_short() for g in self.word]

    def compose(self, other: "Braid") -> "Braid":
        """
        Compose two braids: self first, then other.

        Both braids must have the same strand_count.
        """
        if self.strand_count != other.strand_count:
            raise ValueError(
                f"Cannot compose braids with strand counts "
                f"{self.strand_count} and {other.strand_count}"
            )
        return Braid(
            strand_count=self.strand_count,
            word=self.word + other.word,
            strands=self.strands,  # use self's strand metadata
            name=f"{self.name}·{other.name}",
            metadata={**self.metadata, **other.metadata},
        )

    def __mul__(self, other: "Braid") -> "Braid":
        return self.compose(other)

    def power(self, k: int) -> "Braid":
        """B^k for any integer k (B^0 is the identity, B^{-k} = (B⁻¹)^k)."""
        base = self if k >= 0 else self.inverse()
        word: Tuple[Generator, ...] = ()
        for _ in range(abs(k)):
            word = word + base.word
        return Braid(
            strand_count=self.strand_count,
            word=word,
            strands=self.strands,
            name=f"({self.name})^{k}",
            metadata=dict(self.metadata),
        )

    def inverse(self) -> "Braid":
        """The braid inverse: reverse the word and invert each generator."""
        return Braid(
            strand_count=self.strand_count,
            word=tuple(g.inverse() for g in reversed(self.word)),
            strands=self.strands,
            name=f"{self.name}⁻¹",
            metadata=dict(self.metadata),
        )

    def mirror(self) -> "Braid":
        """The mirror image: every crossing sign is flipped."""
        return Braid(
            strand_count=self.strand_count,
            word=tuple(g.inverse() for g in self.word),
            strands=self.strands,
            name=f"{self.name}*",
            metadata=dict(self.metadata),
        )

    def reverse_strands(self) -> "Braid":
        """Reflect the braid horizontally (swap left-right)."""
        n = self.strand_count
        new_word = tuple(Generator(n - g.index, g.sign) for g in self.word)
        new_strands = tuple(
            Strand(id=k + 1, particle_type=s.particle_type, state=s.state,
                   orientation=s.orientation, geometry=s.geometry)
            for k, s in enumerate(reversed(self.strands))
        )
        return Braid(
            strand_count=n,
            word=new_word,
            strands=new_strands,
            name=f"{self.name}ᵣ",
            metadata=dict(self.metadata),
        )

    def tensor(self, other: "Braid") -> "Braid":
        """
        Juxtaposition B ⊗ B' (other placed to the right of self).
        The result has strand_count = n + n'.
        """
        n = self.strand_count
        shifted = tuple(Generator(g.index + n, g.sign) for g in other.word)
        strands = self.strands + tuple(
            Strand(id=s.id + n, particle_type=s.particle_type, state=s.state,
                   orientation=s.orientation, geometry=s.geometry)
            for s in other.strands
        )
        return Braid(
            strand_count=n + other.strand_count,
            word=self.word + shifted,
            strands=strands,
            name=f"{self.name}⊗{other.name}",
            metadata={**self.metadata, **other.metadata},
        )

    def stabilize(self, sign: int = 1) -> "Braid":
        """Markov stabilisation: add a strand and append σ_n^{±1}."""
        n = self.strand_count
        return Braid(
            strand_count=n + 1,
            word=self.word + (Generator(n, sign),),
            strands=self.strands + (Strand(id=n + 1),),
            name=f"{self.name}↑",
            metadata=dict(self.metadata),
        )

    def crossings(self) -> List[Crossing]:
        """
        Resolve each generator into a Crossing between actual strand IDs
        (strand IDs refer to initial bottom positions).
        """
        positions = [s.id for s in self.strands]
        result: List[Crossing] = []
        for g in self.word:
            i = g.index
            left, right = positions[i - 1], positions[i]
            result.append(Crossing(left_strand_id=left, right_strand_id=right, sign=g.sign))
            positions[i - 1], positions[i] = right, left
        return result

    # ---- Convenience ------------------------------------------------------

    def __len__(self) -> int:
        return len(self.word)

    def __str__(self) -> str:
        if not self.word:
            return f"{self.name} = ε"
        return f"{self.name} = " + " ".join(str(g) for g in self.word)

    def __repr__(self) -> str:
        return f"Braid(n={self.strand_count}, word={self.short_form()})"

    def is_identity(self) -> bool:
        """True iff the *word* is empty (syntactic check; see equality.py)."""
        return len(self.word) == 0

    def with_name(self, name: str) -> "Braid":
        return Braid(
            strand_count=self.strand_count,
            word=self.word,
            strands=self.strands,
            name=name,
            metadata=dict(self.metadata),
        )

    def with_word(self, word: Sequence[Generator], name: Optional[str] = None) -> "Braid":
        """Same strands/metadata, different word."""
        return Braid(
            strand_count=self.strand_count,
            word=tuple(word),
            strands=self.strands,
            name=self.name if name is None else name,
            metadata=dict(self.metadata),
        )

    def to_qbx_dict(self) -> Dict[str, Any]:
        """Canonical QBX-IR serialization (dict form)."""
        return {
            "topology": {
                "strands": self.strand_count,
                "orientation": "time-up",
            },
            "braid": {
                "word": self.short_form(),
            },
            "strands": [
                {
                    "id": s.id,
                    "particle_type": s.particle_type,
                    "state": s.state,
                    "orientation": s.orientation,
                    "geometry": list(s.geometry) if s.geometry else None,
                }
                for s in self.strands
            ],
            "metadata": self.metadata,
            "name": self.name,
        }
