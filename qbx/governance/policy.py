"""
Policies, modality assignments, governance frames and policy checks
(migration 015).

**Contexts and frames.**  Policy checks are evaluated over governance contexts
(table ``governance_context``, e.g. ``dev``, ``staging``, ``production``) with
two accessibility relations (``governance_access``): the ``alethic`` frame for
``□``/``◇`` and the ``deontic`` frame for ``!``/``?``.  The alethic frame must
be reflexive and transitive and the deontic frame serial — exactly the
conditions under which ``□`` is a comonad, ``◇`` a monad, and what is
obligatory is permitted (``Formal/Modality.lean``: ``box_subset_self_iff``,
``box_subset_box_box_iff``, ``box_subset_dia_iff_serial``).

**Checks.**  A check (``policy_check_log``) of a policy at a context records
``outcomes``, a JSON object mapping context names to booleans.  At write time
the database stores ``accessible``, the contexts accessible from the check's
context in the policy's frame (code point order).  With ``p`` the contexts
whose outcome is ``true``, the check *holds* when every accessible context is
in ``p`` (``□``, ``!``) or some is (``◇``, ``?``); its result is ``pass`` when
it holds and otherwise ``warn`` for a ``soft`` policy and ``fail`` for a
``hard`` or ``block_and_alert`` one (``result_eq_pass_iff``).

Blank text means text of only the characters space, tab, LF, CR, FF, VT (the
empty text included).
"""

from __future__ import annotations

import re
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

from qbx.governance.modality import FRAME_OF_KIND, UNIVERSAL, Problem

SCOPES = ("read", "write", "execute")
ENFORCEMENT_LEVELS = ("soft", "hard", "block_and_alert")
RESULTS = ("pass", "fail", "warn")
FRAMES = ("alethic", "deontic")
_SEMVER = re.compile(r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)")
_BLANK = " \t\n\r\f\v"


def is_blank(s: Optional[str]) -> bool:
    return s is None or all(ch in _BLANK for ch in s)


# ---------------------------------------------------------------------------
# Frames
# ---------------------------------------------------------------------------
def context_problems(name: Optional[str]) -> List[Problem]:
    """``context_typing`` {error: name} for a blank context name."""
    return [("context_typing", {"error": "name"})] if is_blank(name) else []


def frame_problems(frame: str, contexts: Iterable[str],
                   access: Iterable[Tuple[str, str]]) -> List[Problem]:
    """``governance_frame_problems``.

    alethic: ``frame_reflexive`` {context} for each context without a loop, in
    code point order; then ``frame_transitive`` {from, via, to} for each
    missing pair (from, to) with from → via → to (via the least such context),
    in (from, to) order.  deontic: ``frame_serial`` {context} for each context
    with no successor.
    """
    ctx = sorted(set(contexts))
    rel: Set[Tuple[str, str]] = set(access)
    out: List[Problem] = []
    if frame == "alethic":
        for c in ctx:
            if (c, c) not in rel:
                out.append(("frame_reflexive", {"context": c}))
        succ: Dict[str, Set[str]] = {}
        for a, b in rel:
            succ.setdefault(a, set()).add(b)
        missing: Dict[Tuple[str, str], str] = {}
        for a, b in rel:
            for c in succ.get(b, ()):
                if (a, c) not in rel:
                    key = (a, c)
                    if key not in missing or b < missing[key]:
                        missing[key] = b
        for (a, c) in sorted(missing):
            out.append(("frame_transitive", {"from": a, "via": missing[(a, c)], "to": c}))
    elif frame == "deontic":
        has_succ = {a for a, _ in rel}
        for c in ctx:
            if c not in has_succ:
                out.append(("frame_serial", {"context": c}))
    return out


def accessible_from(context: Optional[str], access: Iterable[Tuple[str, str]]) -> List[str]:
    """The contexts accessible from ``context`` (code point order)."""
    return sorted({b for a, b in access if a == context})


# ---------------------------------------------------------------------------
# Policies and assignments
# ---------------------------------------------------------------------------
def policy_problems(name: Optional[str], version: Optional[str], body: Any,
                    modality: Any, scope: Optional[str],
                    enforcement: Optional[str]) -> List[Problem]:
    """``governance_policy_problems``: ``policy_typing`` with error, in order,
    name (blank), version (not ``MAJOR.MINOR.PATCH`` without leading zeros),
    body (not a JSON object), modality (none), scope (given but blank),
    enforcement (none)."""
    out: List[Problem] = []
    if is_blank(name):
        out.append(("policy_typing", {"error": "name"}))
    if version is None or not _SEMVER.fullmatch(version):
        out.append(("policy_typing", {"error": "version"}))
    if not isinstance(body, dict):
        out.append(("policy_typing", {"error": "body"}))
    if modality is None:
        out.append(("policy_typing", {"error": "modality"}))
    if scope is not None and is_blank(scope):
        out.append(("policy_typing", {"error": "scope"}))
    if enforcement is None:
        out.append(("policy_typing", {"error": "enforcement"}))
    return out


def assignment_problems(policy_modality: Optional[str], modality: Optional[str],
                        scope: Optional[str], morphism_exists: Optional[bool],
                        duplicates: Optional[int] = None) -> List[Problem]:
    """``governance_assignment_problems`` (modalities by name).

    ``assignment_modality`` {expected, found} when the assignment's modality is
    not its policy's; ``assignment_typing`` {error: scope} unless the scope is
    read / write / execute, {error: morphism} when the morphism does not exist
    (``morphism_exists`` is None when no morphism is given); in batch
    (``duplicates``, the size of the row's group of identical assignments)
    ``assignment_duplicate`` {count} when it exceeds 1.
    """
    out: List[Problem] = []
    if policy_modality != modality:
        out.append(("assignment_modality", {"expected": policy_modality, "found": modality}))
    if scope not in SCOPES:
        out.append(("assignment_typing", {"error": "scope"}))
    if morphism_exists is False:
        out.append(("assignment_typing", {"error": "morphism"}))
    if duplicates is not None and duplicates > 1:
        out.append(("assignment_duplicate", {"count": duplicates}))
    return out


# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------
def holds(kind: str, accessible: Sequence[str], outcomes: Dict[str, bool]) -> bool:
    """The modal formula of a check (every outcome present)."""
    values = [outcomes[c] for c in accessible]
    return all(values) if kind in UNIVERSAL else any(values)


def computed_result(kind: str, enforcement: Optional[str], accessible: Sequence[str],
                    outcomes: Dict[str, bool]) -> str:
    if holds(kind, accessible, outcomes):
        return "pass"
    return "warn" if enforcement == "soft" else "fail"


def outcomes_ok(outcomes: Any) -> bool:
    return isinstance(outcomes, dict) and all(isinstance(v, bool) for v in outcomes.values())


def check_problems(has_policy: bool, kind: Optional[str], enforcement: Optional[str],
                   context: Optional[str], outcomes: Any, recorded: str,
                   accessible: Optional[Sequence[str]]) -> List[Problem]:
    """``governance_check_problems`` for a ``policy_check_log`` row.

    ``check_typing`` {error: policy} (no policy) or {error: modality} (the
    policy has none), {error: context} (none), {error: outcomes} (not an
    object of booleans).  When typed: ``check_outcome_missing`` {context} for
    each accessible context without an outcome; when none is missing,
    ``check_result`` {recorded, computed} when the recorded result is not the
    computed one.  ``accessible`` is the row's stored snapshot (None = empty).
    """
    out: List[Problem] = []
    if not has_policy:
        out.append(("check_typing", {"error": "policy"}))
    elif kind is None:
        out.append(("check_typing", {"error": "modality"}))
    if context is None:
        out.append(("check_typing", {"error": "context"}))
    if not outcomes_ok(outcomes):
        out.append(("check_typing", {"error": "outcomes"}))
    if out:
        return out
    acc = list(accessible or [])
    missing = [c for c in acc if c not in outcomes]
    for c in missing:
        out.append(("check_outcome_missing", {"context": c}))
    if not missing:
        computed = computed_result(kind, enforcement, acc, outcomes)
        if recorded != computed:
            out.append(("check_result", {"recorded": recorded, "computed": computed}))
    return out


def frame_of(kind: str) -> str:
    return FRAME_OF_KIND[kind]
