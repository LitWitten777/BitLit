"""
The seeded modalities and the modality rows of migration 015.

Policies attach to artifacts through four modal operators (table
``modality``).  Each is evaluated on one of two Kripke frames of governance
contexts (see :mod:`qbx.governance.policy`):

=====  ============  =======  ==========
name   kind          frame    backing
=====  ============  =======  ==========
``□``  necessity     alethic  comonad
``◇``  possibility   alethic  monad
``!``  obligation    deontic  —
``?``  permission    deontic  —
=====  ============  =======  ==========

``Formal/Modality.lean``: on a reflexive and transitive frame ``□`` is a
comonad and ``◇`` a monad on the poset of propositions (``boxComonad``,
``diaMonad``), and these laws hold for every proposition only on such frames
(``box_subset_self_iff``, ``box_subset_box_box_iff``).  The deontic operators
satisfy only axiom D (``box_subset_dia_iff_serial``) — what is obligatory need
not hold — so they are not comonads/monads and take no backing.

:func:`modality_table_problems` is the reference for
``governance_modality_table_problems``, :func:`modality_problems` for
``governance_modality_problems``.
"""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Optional, Tuple

Problem = Tuple[str, Dict[str, Any]]

#: The seed: (name, kind, frame, backing structure or None).
SEED: Tuple[Tuple[str, str, str, Optional[str]], ...] = (
    ("□", "necessity", "alethic", "comonad"),
    ("◇", "possibility", "alethic", "monad"),
    ("!", "obligation", "deontic", None),
    ("?", "permission", "deontic", None),
)

KIND_OF: Dict[str, str] = {name: kind for name, kind, _, _ in SEED}
FRAME_OF_KIND: Dict[str, str] = {kind: frame for _, kind, frame, _ in SEED}
BACKING_OF_KIND: Dict[str, Optional[str]] = {kind: b for _, kind, _, b in SEED}
#: Universal modalities quantify over every accessible context.
UNIVERSAL = frozenset({"necessity", "obligation"})


def modality_table_problems(rows: Iterable[Tuple[str, Any]]) -> List[Problem]:
    """``governance_modality_table_problems``: compare the rows (name, kind)
    with the seed.  In seed order ``modality_missing`` {name} or
    ``modality_kind`` {name, expected, found}; then ``modality_unknown``
    {name} for every other row, in code point order."""
    found = {name: kind for name, kind in rows}
    out: List[Problem] = []
    for name, kind, _, _ in SEED:
        if name not in found:
            out.append(("modality_missing", {"name": name}))
        elif found[name] != kind:
            out.append(("modality_kind", {"name": name, "expected": kind, "found": found[name]}))
    for name in sorted(n for n in found if n not in KIND_OF):
        out.append(("modality_unknown", {"name": name}))
    return out


def modality_problems(kind: Optional[str], monad: Any, comonad: Any,
                      monad_violations: Optional[int] = None,
                      comonad_violations: Optional[int] = None) -> List[Problem]:
    """``governance_modality_problems``.

    ``modality_backing`` {error: monad | comonad} when that backing is set but
    the kind does not take it (only possibility takes a monad, only necessity
    a comonad).  In batch (the violation counts given):
    ``modality_backing_unlawful`` {structure, violations} when an allowed
    backing has recorded law violations (``monad_violation`` /
    ``comonad_violation``, migration 006).
    """
    out: List[Problem] = []
    allowed = BACKING_OF_KIND.get(kind) if kind is not None else None
    if monad is not None and allowed != "monad":
        out.append(("modality_backing", {"error": "monad"}))
    if comonad is not None and allowed != "comonad":
        out.append(("modality_backing", {"error": "comonad"}))
    if monad is not None and allowed == "monad" and monad_violations:
        out.append(("modality_backing_unlawful", {"structure": "monad",
                                                  "violations": monad_violations}))
    if comonad is not None and allowed == "comonad" and comonad_violations:
        out.append(("modality_backing_unlawful", {"structure": "comonad",
                                                  "violations": comonad_violations}))
    return out
