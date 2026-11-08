# FA-020 (draft) — a hyperbolic factor in `Address` and `EdgeLabel`

**Status:** draft from Phase D workstream D5; not applied. Reserved range
FA-020 – FA-029. Needs the owner's approval and one seal.

## Motivation

The master plan's "capacity ↔ curvature" row calls for a negatively curved
factor `ℍ^j` next to the hypercube `Q_n` (positive curvature) and the torus
`T^k_m` (flat). D5 built that factor (`d5_curvature/hyperbolic.py`: `{p,q}`
tiling balls and regular-tree balls) and the product
`Q_n □ T^k_m □ ℍ^j` (`d5_curvature/product.py`), but the frozen contract
cannot name a vertex of it:

* `Address` has only `bits` and `cycles`;
* `EdgeLabel.__post_init__` rejects every kind except `"bit"` and `"cycle"`.

D5 therefore works with local types `HAddress` / `HEdgeLabel` and an adapter
(`to_contract`, `from_contract`). This draft proposes the minimal contract
change that makes the local types unnecessary.

## Proposed change (backwards compatible: one optional field, one new kind)

```python
@dataclass(frozen=True)
class Address:
    """An address in Q_n □ T^k_m □ ℍ^j.

    bits:   n entries, each 0 or 1.
    cycles: k entries, cycles[j] in [0, moduli[j]).
    hyper:  j entries (FA-020), hyper[i] a vertex id of the i-th hyperbolic
            factor; () when there is none (every existing space).
    """
    bits: tuple[int, ...]
    cycles: tuple[int, ...]
    hyper: tuple[int, ...] = ()

    def as_tuple(self) -> tuple:
        return self.bits + self.cycles + self.hyper


@dataclass(frozen=True)
class EdgeLabel:
    """kind:  "bit"   -> flip bit `index` (delta ignored)
              "cycle" -> advance cycle `index` by `delta` (+1 or -1)
              "hyp"   -> (FA-020) move in hyperbolic factor `index` to the
                         neighbour in slot `delta` (0 <= delta < degree)
    """
    kind: str
    index: int
    delta: int = 0

    def __post_init__(self):
        if self.kind not in ("bit", "cycle", "hyp"):
            raise ValueError(f"unknown edge kind: {self.kind!r}")
```

No change to `interfaces.py`: `AddressSpace` already speaks only in
`Address` / `EdgeLabel`.

### Backward compatibility

* `Address(bits, cycles)` (positional or keyword) still works and gives
  `hyper == ()`; equality and hashing of such addresses are unchanged
  (`()` on both sides), so existing dictionaries, sets and test vectors keep
  working.
* `as_tuple()` is unchanged when `hyper == ()`.
* Every `EdgeLabel` that is valid today is still valid.

### Effect on every consumer (audited with `grep "Address("` over `foundation/`)

| Consumer | Uses | Effect | Action needed |
|---|---|---|---|
| `ws1_geometry/mixed_radix.py` (`vertices`, `step`, `origin`, `hypercube_vertices`) | builds `Address(bits, cycles)` | none: `MixedRadixSpace` has no hyperbolic factor, so `hyper == ()` throughout | none; the hyperbolic space would be a new class (`ws1_geometry/hyperbolic.py`, see the manifest) |
| `ws3_consensus/flatness.py:149` (`address_of`) | builds `Address(fiber, cycles)` | none | none |
| `ws5_braid_ops/gate_action.py:62` (`Gate.__call__`) | rebuilds `Address(bits, cycles)` | would **drop** a non-empty `hyper` | gates are defined on `Q_n □ T^k_m` and already reject addresses of the wrong shape by length checks; add `if a.hyper: raise ValueError` (one line) so a hyperbolic address is refused rather than truncated |
| `ws9_protocol/network.py:54` (`dimension_of`) | `as_tuple()` | correct (hyper coordinates become dimensions `n+k …`) | none |
| `ws9_protocol/network.py:66,70` (`move`) | rebuilds `Address(...)` | would drop `hyper` | pass `a.hyper` through (two edits) or refuse as in ws5 |
| `ws1_geometry/routing.py`, `ws3_consensus`, `ws6_certificates`, `ws7_benchmarks` | consume addresses through `AddressSpace` | none | none |
| `tests/test_fnd_contracts.py`, `tests/test_prop_*.py` | construct `Address(b, c)` / labels | none | add one test: `EdgeLabel("hyp", 0, 1)` accepted, `Address(b, c) == Address(b, c, ())` |

### Version

Interface 1.1.0 → 1.2.0 (if FA-010 is approved in the same seal, both go
into 1.2.0); history row in `INTERFACE_FREEZE.md`; queue
`foundation/contracts/types.py` with `--amendment FA-020` after the final
edit; one `./seal.sh` run.

### Alternatives considered

* **Encode the hyperbolic vertex in `cycles`.** Rejected: `cycles[j]` is
  read modulo `moduli[j]` by every consumer, and a ball vertex has no cyclic
  structure, so the distance formula of `MixedRadixSpace` would be silently
  wrong.
* **Label `"hyp"` steps by the target vertex instead of a slot.** Possible,
  but slots keep labels small and generator-like (as for bits and cycles)
  and make `neighbors` order-deterministic.

### If rejected

Nothing breaks: D5 keeps its local `HAddress` / `HEdgeLabel` and adapter,
and the hyperbolic factor stays outside the contract.
