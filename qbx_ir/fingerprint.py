"""
The braid fingerprint (QBX.md §19):

    F(B) = (n, w, π, I_topo, I_quantum, I_geometric)

- n: strand count
- w: reduced word — the Garside normal form (canonical for the group element)
- π: induced permutation
- I_topo: writhe, closure components, linking, Alexander and Jones polynomials
- I_quantum: trace of the Fibonacci-anyon representation (n ≤ 8)
- I_geometric: E8 geometric cost

Two braids that are equal in B_n get the same fingerprint *except* for the
geometric entry, which depends on strand metadata; ``fingerprint_hash``
therefore hashes only the group-invariant part.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any, Dict

import numpy as np

from qbx_ir.algebra.garside import left_normal_form
from qbx_ir.algebra.invariants import closure_components, linking_number, permutation, writhe
from qbx_ir.algebra.polynomial_invariants import (
    MAX_STATE_SUM_CROSSINGS,
    alexander_polynomial,
    jones_polynomial,
)
from qbx_ir.core.braid import Braid


def _poly(p) -> Dict[str, str]:
    return {str(k): str(v) for k, v in p.items()}


def fingerprint(braid: Braid) -> Dict[str, Any]:
    from qbx_ir.anyon import anyon_representation, fibonacci_model
    from qbx_ir.views.geometric import geometric_cost

    nf = left_normal_form(braid)
    topo: Dict[str, Any] = {
        "writhe": writhe(braid),
        "components": len(closure_components(braid)),
        "linking_number": linking_number(braid),
    }
    if braid.strand_count <= 10:
        topo["alexander"] = _poly(alexander_polynomial(braid))
    if len(braid.word) <= MAX_STATE_SUM_CROSSINGS:
        topo["jones_half_t"] = _poly(jones_polynomial(braid))
    quantum: Dict[str, Any] = {}
    if braid.strand_count <= 8:
        tr = complex(np.trace(anyon_representation(braid, fibonacci_model(), "τ")))
        quantum["fibonacci_trace"] = [round(tr.real, 9) + 0.0, round(tr.imag, 9) + 0.0]
    return {
        "n": braid.strand_count,
        "w": nf.to_short_form(),
        "garside": {"inf": nf.infimum, "sup": nf.supremum},
        "pi": list(permutation(braid)),
        "I_topo": topo,
        "I_quantum": quantum,
        "I_geometric": {"e8_cost": geometric_cost(braid)},
    }


def fingerprint_hash(braid: Braid) -> str:
    """SHA3-256 of the canonical JSON of the group-invariant fingerprint part."""
    fp = fingerprint(braid)
    fp.pop("I_geometric")
    payload = json.dumps(fp, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha3_256(payload).hexdigest()
