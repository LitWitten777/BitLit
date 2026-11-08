"""
Approval workflows and approval tokens (migration 015).

A workflow (``approval_workflow``) is an ordered, non-empty list of steps, each
a JSON object with a non-blank ``role``, roles distinct, and ``timeout_days``
in 1–3650.  An approval token (``approval_token``) records that the role of
one step approved an artifact: it needs the artifact, ``approved_at`` and
``expires_at`` with ``approved_at < expires_at ≤ approved_at + timeout_days ×
24 h``.  Steps are approved in order: when a step is approved, every earlier
step must already have a token for the same artifact approved no later
(batch check ``token_order``).

An artifact is approved by a workflow at time ``t`` when every step has a
token without problems whose window ``[approved_at, expires_at)`` contains
``t`` (:func:`is_approved`, ``approval_status``).
"""

from __future__ import annotations

from datetime import datetime, timedelta
from typing import Any, List, Optional, Sequence, Tuple

from qbx.governance.modality import Problem
from qbx.governance.policy import is_blank

MAX_TIMEOUT_DAYS = 3650


def workflow_problems(name: Optional[str], steps: Any, timeout_days: Any) -> List[Problem]:
    """``governance_workflow_problems``: ``workflow_typing`` with error name
    (blank); steps (not a non-empty array) or, per step i, {error: step, index}
    (not an object with a non-blank string ``role``) or {error:
    duplicate_role, index} (the role of an earlier step); timeout (not in
    1–3650)."""
    out: List[Problem] = []
    if is_blank(name):
        out.append(("workflow_typing", {"error": "name"}))
    if not isinstance(steps, list) or not steps:
        out.append(("workflow_typing", {"error": "steps"}))
    else:
        seen = set()
        for i, s in enumerate(steps):
            role = s.get("role") if isinstance(s, dict) else None
            if not isinstance(role, str) or is_blank(role):
                out.append(("workflow_typing", {"error": "step", "index": i}))
            elif role in seen:
                out.append(("workflow_typing", {"error": "duplicate_role", "index": i}))
            else:
                seen.add(role)
    if timeout_days is None or not (1 <= timeout_days <= MAX_TIMEOUT_DAYS):
        out.append(("workflow_typing", {"error": "timeout"}))
    return out


def workflow_roles(name: Optional[str], steps: Any, timeout_days: Any) -> Optional[List[str]]:
    """The step roles in order, or None when the workflow has problems."""
    if workflow_problems(name, steps, timeout_days):
        return None
    return [s["role"] for s in steps]


def token_problems(roles: Optional[Sequence[str]], timeout_days: Any, artifact: Any,
                   role: Optional[str], approved_at: Optional[datetime],
                   expires_at: Optional[datetime],
                   others: Optional[Sequence[Tuple[str, Optional[datetime]]]] = None
                   ) -> List[Problem]:
    """``governance_token_problems``.

    ``token_typing`` {error: workflow} (the workflow has problems) or {error:
    role} (not a step role); {error: artifact}, {error: approved_at}, {error:
    expires_at} (missing); {error: window} (expires_at ≤ approved_at) or
    {error: timeout} (expires_at after approved_at + timeout).  In batch
    (``others``: (role, approved_at) of the tokens of the same workflow and
    artifact): ``token_order`` {role} for each earlier step with no token
    approved at or before this one.
    """
    out: List[Problem] = []
    if roles is None:
        out.append(("token_typing", {"error": "workflow"}))
    elif role not in roles:
        out.append(("token_typing", {"error": "role"}))
    if artifact is None:
        out.append(("token_typing", {"error": "artifact"}))
    if approved_at is None:
        out.append(("token_typing", {"error": "approved_at"}))
    if expires_at is None:
        out.append(("token_typing", {"error": "expires_at"}))
    if approved_at is not None and expires_at is not None:
        if expires_at <= approved_at:
            out.append(("token_typing", {"error": "window"}))
        elif roles is not None and expires_at - approved_at > timedelta(days=timeout_days):
            out.append(("token_typing", {"error": "timeout"}))
    if (others is not None and roles is not None and role in roles
            and approved_at is not None and artifact is not None):
        for r in list(roles)[:list(roles).index(role)]:
            if not any(o_role == r and o_at is not None and o_at <= approved_at
                       for o_role, o_at in others):
                out.append(("token_order", {"role": r}))
    return out


def is_approved(roles: Optional[Sequence[str]],
                good_tokens: Sequence[Tuple[str, datetime, datetime]], at: datetime) -> bool:
    """``approval_status``: every step role has a token without problems,
    given as (role, approved_at, expires_at), valid at ``at``."""
    if roles is None:
        return False
    return all(any(r == role and a <= at < e for r, a, e in good_tokens) for role in roles)
