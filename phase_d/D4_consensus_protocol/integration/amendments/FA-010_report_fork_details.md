# FA-010 (draft) — `ConsensusReport`: edge connectivity and fork kinds

**Status:** draft from Phase D workstream D4; not applied. Reserved range
FA-010 – FA-019.

## Motivation

`docs/ATTACKS.md`, observations 1 and 3. Consumers of `ConsensusReport` can see
whether a ledger is flat and where its blind spots are, but not

* the guaranteed detection radius λ (F6a: every fork on fewer than λ pairs is
  detected), which tells them how far `flat` can be trusted when
  `blind_spots == []`; nor
* which entries of `forks` are equivocations (localized to one pair) and which
  are fundamental-cycle forks (localized to a loop).

## Proposed change (backwards compatible: new optional fields with defaults)

```python
@dataclass
class ConsensusReport:
    ...
    blind_spots: list = field(default_factory=list)
    # FA-010
    n_equivocations: int = 0              # the first n entries of `forks`
    edge_connectivity: int | None = None  # λ of the merged event graph
                                          # (min over components), if computed
```

`consensus_check` sets `n_equivocations = len(equivocations)` (free) and leaves
`edge_connectivity = None` unless called with `with_connectivity=True`
(Stoer–Wagner, O(V·E log V); `ws9_protocol.connectivity` (formerly `d4_protocol.connectivity`) is a pure-Python
implementation, cross-checked against max flow and brute force).

## Version

Interface 1.1.0 → 1.2.0; history row in `INTERFACE_FREEZE.md`; one seal.
