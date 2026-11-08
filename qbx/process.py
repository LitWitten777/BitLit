"""``qbx.process`` — the one end-to-end entry point (Phase 3, decision RUN-001).

**QBX turns a text (or an event stream of generator letters) into a braid word, reduces it with
checked rewrite steps, reads its closure invariants, and returns them with a certificate and a
verdict.**

    text --(reading frame)--> logical letters --(encoding)--> braid word
         --(optional forward-backward pass)--> word --(R01/R02 ledger)--> certificate
         --(closure invariants)--> verdict

Every step is backed by a Lean statement (``QBX/Formal``), listed in ``Result.lean``:

* reading-frame normalisation never changes closure data of a line: ``Foundations.frame_change_invariants``;
* rewriting preserves the braid: ``QBX.Formal.Step.eval_eq`` / ``eval_eq_iff_eqvGen``;
* the forward-backward pass is pure, closes to ``n`` components, and its linking matrix is the
  crossing matrix of the single pass: ``Foundations.bipass_pure``, ``numComponents_bipass``,
  ``linkMatrix_bipass``;
* writhe and permutation are invariants: ``permHom_eval``, ``writheHom_eval``.

The verdict re-checks the Lean identities numerically on this input (``Result.checks``); a
failed check means the runtime disagrees with the formal pipeline and is a bug.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Union

from qbx.hebrew.gematria import SCHEMES, gematria_value_scheme

LAYOUTS = ("uniform", "boustrophedon", "reverse_boustrophedon")


@dataclass
class Options:
    strands: int = 8
    sofit_rule: bool = True
    layout: str = "uniform"           # surface layout of `lines` input (undone before encoding)
    bidirectional: bool = False       # read forward, then backward (g · rev g)
    gematria: str = "standard"        # gematria scheme name (qbx.hebrew.gematria.SCHEMES)
    certificate: bool = True          # build the R01/R02 ledger certificate
    certificate_max_letters: int = 4000


@dataclass
class Result:
    input_kind: str
    strands: int
    letters: int
    words: List[str]
    short_form: List[int]
    reduced_short_form: Optional[List[int]]
    writhe: int
    permutation: List[int]
    components: List[List[int]]
    pure: bool
    crossing_matrix: List[List[int]]
    linking_matrix: Optional[List[List[int]]]
    gematria: Dict[str, Any]
    certificate: Optional[Dict[str, Any]]
    checks: Dict[str, bool]
    verdict: str
    lean: Dict[str, str] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return dict(self.__dict__)


# ----------------------------------------------------------------------------- braid algebra
def _perm_of(short: Sequence[int], n: int) -> List[int]:
    """Position permutation: the strand starting at position a ends at position perm[a]."""
    pos = list(range(n))           # pos[label] = current position
    at = list(range(n))            # at[position] = label
    for s in short:
        i = abs(s) - 1
        a, b = at[i], at[i + 1]
        at[i], at[i + 1] = b, a
        pos[a], pos[b] = i + 1, i
    return pos


def _crossing_matrix(short: Sequence[int], n: int) -> List[List[int]]:
    """Signed crossing counts between strands, labelled by starting position (Lean's
    ``crossMatrix``: symmetric, zero diagonal, each crossing ``σᵢ^{±1}`` adds ``±1`` to the pair of
    strands it crosses)."""
    M = [[0] * n for _ in range(n)]
    at = list(range(n))
    for s in short:
        i = abs(s) - 1
        a, b = at[i], at[i + 1]
        e = 1 if s > 0 else -1
        M[a][b] += e
        M[b][a] += e
        at[i], at[i + 1] = b, a
    return M


def _components(perm: Sequence[int]) -> List[List[int]]:
    seen, out = set(), []
    for a in range(len(perm)):
        if a in seen:
            continue
        cyc, x = [], a
        while x not in seen:
            seen.add(x)
            cyc.append(x)
            x = perm[x]
        out.append(sorted(cyc))
    return out


def reverse_word(short: Sequence[int]) -> List[int]:
    """``rev``: the same letters in the opposite order (Lean ``revB``: σᵢ ↦ σᵢ, order reversed)."""
    return list(reversed(short))


def bipass_word(short: Sequence[int]) -> List[int]:
    """Forward then backward: ``g · rev g`` (Lean ``Foundations.bipass``)."""
    return list(short) + reverse_word(short)


def undo_layout(lines: Sequence[str], layout: str) -> List[str]:
    """Surface lines -> logical lines.  In boustrophedon the odd lines are written mirrored (we
    receive them as visually reversed strings); in reverse boustrophedon they are turned through
    180° (also reversed as strings).  Unicode text is otherwise already in logical order."""
    if layout not in LAYOUTS:
        raise ValueError(f"unknown layout {layout!r}; expected one of {LAYOUTS}")
    if layout == "uniform":
        return list(lines)
    return [ln[::-1] if k % 2 == 1 else ln for k, ln in enumerate(lines)]


# ----------------------------------------------------------------------------- entry point
def process(data: Union[str, Sequence[str], Sequence[int]], options: Optional[Options] = None,
            **kw: Any) -> Result:
    """Run the QBX pipeline end to end.

    ``data`` is a text (``str``), a list of surface lines (``list[str]``, see ``Options.layout``),
    or an event stream: a list of nonzero ints in short form (``±i`` = ``σᵢ^{±1}``).
    Keyword arguments override fields of ``options``.
    """
    from qbx_bible.encode import Encoding, encode_text
    from qbx_ir.core.braid import Braid

    opts = options or Options()
    for k, v in kw.items():
        if not hasattr(opts, k):
            raise TypeError(f"unknown option {k!r}")
        setattr(opts, k, v)
    if opts.gematria not in SCHEMES:
        raise ValueError(f"unknown gematria scheme {opts.gematria!r}; known: {sorted(SCHEMES)}")
    n = opts.strands

    words: List[str] = []
    if isinstance(data, str) or (data and all(isinstance(x, str) for x in data)):
        kind = "text" if isinstance(data, str) else "lines"
        text = data if isinstance(data, str) else "\n".join(undo_layout(list(data), opts.layout))
        enc = encode_text(text, "input", Encoding(strand_count=n, sofit_rule=opts.sofit_rule))
        short = enc.braid.short_form()
        words = list(enc.words)
    else:
        kind = "events"
        short = [int(x) for x in data]
        bad = [s for s in short if s == 0 or abs(s) > n - 1]
        if bad:
            raise ValueError(f"generator letters must satisfy 1 <= |s| <= {n - 1}; got {bad[:5]}")

    single = list(short)
    if opts.bidirectional:
        short = bipass_word(single)

    perm = _perm_of(short, n)
    comps = _components(perm)
    pure = all(perm[a] == a for a in range(n))
    cross = _crossing_matrix(short, n)
    link = [[x // 2 for x in row] for row in cross] if pure else None
    writhe = sum(1 if s > 0 else -1 for s in short)

    cert = None
    reduced = None
    if opts.certificate and len(short) <= opts.certificate_max_letters:
        from qbx_bible.pipeline import ledger_certificate
        c = ledger_certificate(Braid.from_short_form(n, short, name="input"))
        reduced = c["reduced"].short_form()
        cert = {k: v for k, v in c.items() if k != "reduced"}

    # --- re-check the Lean identities on this input -------------------------------------
    checks: Dict[str, bool] = {
        "crossing_matrix_symmetric_zero_diagonal":
            all(cross[a][b] == cross[b][a] for a in range(n) for b in range(n))
            and all(cross[a][a] == 0 for a in range(n)),
        "writhe_is_half_crossing_sum": 2 * writhe == sum(map(sum, cross)),
        "frame_change_preserves_components":   # rigid frame change rev (turnOver): same closure
            len(_components(_perm_of(reverse_word(short), n))) == len(comps),
    }
    if cert is not None:
        rperm = _perm_of(reduced, n)
        checks["rewrite_preserves_permutation"] = rperm == perm
        checks["rewrite_preserves_writhe"] = sum(1 if s > 0 else -1 for s in reduced) == writhe
        checks["certificate_accepted"] = bool(cert["accepted"])
    if opts.bidirectional:
        c1 = _crossing_matrix(single, n)
        checks["bipass_pure"] = pure
        checks["bipass_n_components"] = len(comps) == n
        checks["bipass_linking_is_single_crossing"] = link == c1
        checks["bipass_writhe_doubles"] = writhe == 2 * sum(1 if s > 0 else -1 for s in single)

    gem = {"scheme": opts.gematria,
           "words": [[w, gematria_value_scheme(w, opts.gematria)] for w in words],
           "total": sum(gematria_value_scheme(w, opts.gematria) for w in words)}

    if not all(checks.values()):
        verdict = "inconsistent: " + ", ".join(k for k, v in checks.items() if not v)
    elif len(comps) == 1:
        verdict = "knot (1 component)"
    else:
        verdict = f"link ({len(comps)} components{', pure' if pure else ''})"

    lean = {
        "frame": "QBX.Formal.Foundations.frame_change_invariants",
        "rewrite": "QBX.Formal.eval_eq_iff_eqvGen",
        "invariants": "QBX.Formal.permHom_eval, QBX.Formal.writheHom_eval",
        "linking": "QBX.Formal.Foundations.linking_matrix",
    }
    if opts.bidirectional:
        lean["bidirectional"] = "QBX.Formal.Foundations.linkMatrix_bipass, numComponents_bipass"

    return Result(kind, n, len(single), words, short, reduced, writhe, perm, comps, pure, cross,
                  link, gem, cert, checks, verdict, lean)
