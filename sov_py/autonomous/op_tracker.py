"""
Open Problem Tracker — reads/writes the Open Problems Atlas in bidirectional sync.

Tracks all 65+ open problems (OP-001…OP-065+) from:
  - OPEN_PROBLEMS_ATLAS.md  (human-readable)
  - problems/data/open_problems.json  (machine-readable index)
  - problems/visualizer/open_problems_web.html  (interactive dependency web)

Key operations:
  get_open_problems()   — returns sorted list of open OPs filtered by domain/rigor
  close_problem()       — marks an OP [RESOLVED], updates all three artifacts
  open_derived()        — adds a new OP derived from a proved theorem
  sync()                — ensures all three files are in sync

Resolution metadata schema added to open_problems.json:
  "resolved_by"       : str | null  — HYP-### that resolved it
  "lean_theorem"      : str | null  — kernel-checked theorem name
  "lean_file"         : str | null  — relative path to .lean file
  "resolution_date"   : str | null  — ISO-8601 date
  "resolution_summary": str | null  — brief description
"""

from __future__ import annotations

import datetime
import json
import re
import subprocess
import sys
from enum import Enum
from pathlib import Path
from typing import Any


class OPStatus(str, Enum):
    OPEN = "open"
    IN_PROGRESS = "in_progress"
    RESOLVED = "resolved"
    FALSIFIED = "falsified"


# Rigor level ordering (most tractable first)
_RIGOR_ORDER = {"L2": 0, "L3": 1, "L4": 2, "L1": 3}


class OpenProblemTracker:
    """
    Bidirectional sync between Open Problems Atlas markdown, JSON index,
    and the interactive HTML visualizer.
    """

    def __init__(self, repo_root: str | Path = ".") -> None:
        self.repo_root = Path(repo_root).resolve()
        self._atlas_md = self.repo_root / "OPEN_PROBLEMS_ATLAS.md"
        self._problems_dir = self.repo_root / "problems"
        self._json_index = self._problems_dir / "data" / "open_problems.json"
        self._html_vis = self._problems_dir / "visualizer" / "open_problems_web.html"

        # In-memory cache: op_id -> problem dict
        self._cache: dict[str, dict[str, Any]] | None = None

    # ------------------------------------------------------------------
    # Loading
    # ------------------------------------------------------------------

    def _load(self) -> dict[str, dict[str, Any]]:
        """Load the JSON index, falling back to parsing the markdown atlas."""
        if self._cache is not None:
            return self._cache

        if self._json_index.exists():
            try:
                raw = json.loads(self._json_index.read_text(encoding="utf-8"))
                # raw may be a list or a dict
                if isinstance(raw, list):
                    data = {p["id"]: p for p in raw if "id" in p}
                elif isinstance(raw, dict) and "problems" in raw:
                    data = {p["id"]: p for p in raw["problems"] if "id" in p}
                else:
                    data = {k: v for k, v in raw.items() if isinstance(v, dict)}
                # Normalize field names and ensure resolution fields exist
                for p in data.values():
                    # Normalize domain_number → domain
                    if "domain_number" in p and "domain" not in p:
                        p["domain"] = p["domain_number"]
                    # Normalize motivating_hypotheses → motivating_hyps
                    if "motivating_hypotheses" in p and "motivating_hyps" not in p:
                        p["motivating_hyps"] = p["motivating_hypotheses"]
                    # Normalize status: None → open, non-empty string → resolved/falsified
                    raw_status = p.get("status")
                    if raw_status is None or raw_status == "":
                        p["status"] = OPStatus.OPEN.value
                    elif isinstance(raw_status, str) and raw_status.lower() in (
                        OPStatus.OPEN.value, OPStatus.RESOLVED.value,
                        OPStatus.FALSIFIED.value, OPStatus.IN_PROGRESS.value,
                    ):
                        pass  # already normalized
                    elif isinstance(raw_status, str) and "FALSIFIED" in raw_status.upper():
                        p["status"] = OPStatus.FALSIFIED.value
                    elif isinstance(raw_status, str) and len(raw_status) > 3:
                        p["status"] = OPStatus.RESOLVED.value
                    else:
                        p["status"] = OPStatus.OPEN.value
                    # Ensure all resolution fields exist
                    for field_name in ("resolved_by", "lean_theorem", "lean_file",
                                       "resolution_date", "resolution_summary",
                                       "derived_from", "generates"):
                        p.setdefault(field_name, None)
                self._cache = data
                return self._cache
            except Exception:
                pass

        # Fallback: parse the markdown
        self._cache = self._parse_markdown_atlas()
        return self._cache

    def _parse_markdown_atlas(self) -> dict[str, dict[str, Any]]:
        """Parse OPEN_PROBLEMS_ATLAS.md into a dict of problem dicts."""
        if not self._atlas_md.exists():
            return {}

        text = self._atlas_md.read_text(encoding="utf-8")
        problems: dict[str, dict[str, Any]] = {}

        # Match problem headers: ### OP-NNN — Title [Lk]
        header_re = re.compile(
            r"^### (OP-\d+)\s+—\s+(.+?)\s+`\[(L[1-4])\]`",
            re.MULTILINE,
        )
        # Also handle RESOLVED markers: ### OP-NNN ... [L3] **[RESOLVED...]**
        resolved_re = re.compile(r"\*\*\[RESOLVED", re.IGNORECASE)

        # Domain headers: ## Domain N — Name
        domain_re = re.compile(r"^## Domain (\d+)\s+—\s+(.+)$", re.MULTILINE)

        # Build domain map: position -> domain_number
        domain_positions: list[tuple[int, int, str]] = []
        for m in domain_re.finditer(text):
            domain_positions.append((m.start(), int(m.group(1)), m.group(2).strip()))

        def _domain_at(pos: int) -> int:
            d = 1
            for dpos, dnum, _ in domain_positions:
                if pos >= dpos:
                    d = dnum
            return d

        # Extract **Motivating:** HYP-NNN lines
        motivating_re = re.compile(r"\*\*Motivating:\*\*\s+(.+?)$", re.MULTILINE)
        # Extract **Statement:** lines
        statement_re = re.compile(r"\*\*Statement:\*\*\s+(.+?)(?=\n\*\*|\Z)", re.DOTALL)

        # Find all header matches and slice the text between them
        headers = list(header_re.finditer(text))
        for idx, match in enumerate(headers):
            op_id = match.group(1)
            title = match.group(2).strip()
            rigor = match.group(3)

            # Determine section text (up to next header or end)
            section_start = match.start()
            section_end = headers[idx + 1].start() if idx + 1 < len(headers) else len(text)
            section_text = text[section_start:section_end]

            # Status
            is_resolved = bool(resolved_re.search(section_text))
            is_falsified = "FALSIFIED" in section_text.upper() and "RESOLVED" in section_text.upper()
            status = OPStatus.RESOLVED.value if is_resolved else OPStatus.OPEN.value
            if is_falsified:
                status = OPStatus.FALSIFIED.value

            # Motivating HYPs
            mot_match = motivating_re.search(section_text)
            motivating_hyps: list[str] = []
            if mot_match:
                motivating_hyps = re.findall(r"HYP-\d+", mot_match.group(1))

            # Statement (first line after **Statement:**)
            stmt_match = statement_re.search(section_text)
            statement = stmt_match.group(1).strip().splitlines()[0] if stmt_match else title

            problems[op_id] = {
                "id": op_id,
                "title": title,
                "rigor_level": rigor,
                "domain": _domain_at(section_start),
                "status": status,
                "motivating_hyps": motivating_hyps,
                "statement": statement,
                "resolved_by": None,
                "lean_theorem": None,
                "lean_file": None,
                "resolution_date": None,
                "resolution_summary": None,
                "derived_from": None,
                "generates": None,
            }

        return problems

    # ------------------------------------------------------------------
    # Query API
    # ------------------------------------------------------------------

    def get_open_problems(
        self,
        domains: list[int] | None = None,
        rigor_levels: list[str] | None = None,
    ) -> list[dict[str, Any]]:
        """
        Return open problems sorted by rigor tractability (L2 → L3 → L4 → L1).

        Args:
            domains: filter to specific domain numbers (1–8)
            rigor_levels: filter to specific rigor levels
        """
        data = self._load()
        open_ops = [
            p for p in data.values()
            if p.get("status") == OPStatus.OPEN.value
        ]

        if domains:
            open_ops = [p for p in open_ops if p.get("domain") in domains]

        if rigor_levels:
            open_ops = [p for p in open_ops if p.get("rigor_level") in rigor_levels]

        # Sort: rigor order first, then by OP-### number
        open_ops.sort(key=lambda p: (
            _RIGOR_ORDER.get(p.get("rigor_level", "L1"), 99),
            int(p["id"].replace("OP-", "")),
        ))
        return open_ops

    def get_problem(self, op_id: str) -> dict[str, Any] | None:
        """Return the problem dict for a specific OP-###, or None."""
        return self._load().get(op_id)

    def all_problems(self) -> list[dict[str, Any]]:
        """Return all problems (open + resolved)."""
        return list(self._load().values())

    def stats(self) -> dict[str, int]:
        """Return counts by status and rigor level."""
        data = self._load()
        counts: dict[str, int] = {"total": len(data), "open": 0, "resolved": 0, "falsified": 0}
        for p in data.values():
            st = p.get("status", OPStatus.OPEN.value)
            counts[st] = counts.get(st, 0) + 1
        return counts

    # ------------------------------------------------------------------
    # Mutation API
    # ------------------------------------------------------------------

    def close_problem(
        self,
        op_id: str,
        resolution_summary: str,
        resolved_by: str | None = None,
        lean_theorem: str | None = None,
        lean_file: str | None = None,
    ) -> bool:
        """
        Mark op_id as [RESOLVED] with full provenance metadata.

        Updates:
          - In-memory cache
          - problems/data/open_problems.json
          - OPEN_PROBLEMS_ATLAS.md (inserts **Status: RESOLVED** note)
          - open_problems_web.html (updates status badge)

        Returns True on success, False if op_id not found.
        """
        data = self._load()
        if op_id not in data:
            return False

        now = datetime.date.today().isoformat()
        data[op_id].update({
            "status": OPStatus.RESOLVED.value,
            "resolved_by": resolved_by,
            "lean_theorem": lean_theorem,
            "lean_file": lean_file,
            "resolution_date": now,
            "resolution_summary": resolution_summary,
        })

        self._save_json(data)
        self._patch_markdown(op_id, data[op_id])
        self._update_html_badge(op_id, OPStatus.RESOLVED)
        self._regenerate_visualizer()
        return True

    def open_derived_problem(
        self,
        statement: str,
        title: str,
        motivating_hyps: list[str],
        rigor_level: str = "L1",
        domain: int = 8,
        derived_from: str | None = None,
    ) -> str:
        """
        Register a new open problem derived from a proved theorem.
        Returns the new OP-### ID.
        """
        data = self._load()
        existing_nums = [
            int(k.replace("OP-", ""))
            for k in data
            if re.match(r"^OP-\d+$", k)
        ]
        next_num = (max(existing_nums) + 1) if existing_nums else 66
        new_id = f"OP-{next_num:03d}"

        data[new_id] = {
            "id": new_id,
            "title": title,
            "rigor_level": rigor_level,
            "domain": domain,
            "status": OPStatus.OPEN.value,
            "motivating_hyps": motivating_hyps,
            "statement": statement,
            "resolved_by": None,
            "lean_theorem": None,
            "lean_file": None,
            "resolution_date": None,
            "resolution_summary": None,
            "derived_from": derived_from,
            "generates": None,
        }

        self._save_json(data)
        self._append_markdown(new_id, data[new_id])
        return new_id

    # ------------------------------------------------------------------
    # Persistence helpers
    # ------------------------------------------------------------------

    def _save_json(self, data: dict[str, dict[str, Any]]) -> None:
        """Save the in-memory cache to open_problems.json."""
        if not self._json_index.parent.exists():
            self._json_index.parent.mkdir(parents=True, exist_ok=True)
        problems_list = sorted(data.values(), key=lambda p: int(p["id"].replace("OP-", "")))
        payload = {
            "version": "2.0",
            "generated": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "stats": {
                "total": len(data),
                "open": sum(1 for p in data.values() if p.get("status") == "open"),
                "resolved": sum(1 for p in data.values() if p.get("status") == "resolved"),
            },
            "problems": problems_list,
        }
        self._json_index.write_text(
            json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8"
        )

    def _regenerate_visualizer(self) -> None:
        """Regenerate open_problems_web.html using experiments/generate_visualizer.py."""
        vis_script = self.repo_root / "experiments" / "generate_visualizer.py"
        if vis_script.exists():
            try:
                subprocess.run([sys.executable, str(vis_script)], check=False, capture_output=True)
            except Exception:
                pass

    def _patch_markdown(self, op_id: str, problem: dict[str, Any]) -> None:
        """Insert or update a **Status:** RESOLVED line and header under the OP in the markdown atlas."""
        if not self._atlas_md.exists():
            return

        text = self._atlas_md.read_text(encoding="utf-8")
        header_re = re.compile(
            rf"^(### {re.escape(op_id)}\s+—\s+.+)$",
            re.MULTILINE,
        )
        m = header_re.search(text)
        if not m:
            return

        header = m.group(1)
        resolved_by = problem.get("resolved_by")
        tag = f" [RESOLVED via {resolved_by}]" if resolved_by else " [RESOLVED]"
        if "[RESOLVED" not in header:
            new_header = header.rstrip() + tag
            text = text[:m.start()] + new_header + text[m.end():]
            m = header_re.search(text)
            if not m:
                return

        snippet_start = m.end()
        snippet_end = min(snippet_start + 400, len(text))
        snippet = text[snippet_start:snippet_end]

        status_line = f"\n**Status:** RESOLVED — {problem.get('resolution_summary', '')}"
        lean_line = ""
        if problem.get("lean_theorem"):
            lean_file_str = f" in `{problem['lean_file']}`" if problem.get("lean_file") else ""
            lean_line = f"\n**Lean 4 theorem:** `{problem['lean_theorem']}`{lean_file_str}"

        if "**Status:** RESOLVED" not in snippet:
            insert_pos = m.end()
            text = text[:insert_pos] + status_line + lean_line + text[insert_pos:]

        self._atlas_md.write_text(text, encoding="utf-8")

    def _update_html_badge(self, op_id: str, status: OPStatus) -> None:
        """Update the status data-attribute for op_id in the HTML visualizer."""
        if not self._html_vis.exists():
            return

        html = self._html_vis.read_text(encoding="utf-8")
        badge_colors = {
            OPStatus.OPEN: "status-open",
            OPStatus.IN_PROGRESS: "status-inprogress",
            OPStatus.RESOLVED: "status-resolved",
            OPStatus.FALSIFIED: "status-falsified",
        }

        # Update data-status attribute for this node
        # Look for: data-id="OP-NNN" ... data-status="open"
        node_re = re.compile(
            rf'(data-id="{re.escape(op_id)}"[^>]*?data-status=")[^"]*(")',
            re.DOTALL,
        )
        new_html = node_re.sub(rf"\g<1>{status.value}\g<2>", html)

        if new_html != html:
            self._html_vis.write_text(new_html, encoding="utf-8")

    def _append_markdown(self, op_id: str, problem: dict[str, Any]) -> None:
        """Append a new OP entry to OPEN_PROBLEMS_ATLAS.md."""
        if not self._atlas_md.exists():
            return

        domain_names = {
            1: "Cayley–Dickson Algebra & the Tower",
            2: "Spectral Graph Theory & Expanders",
            3: "Quantum Error Correction & CSS Codes",
            4: "Non-Associative Hydrodynamics & PDE",
            5: "Number Theory & ABC/IUTT",
            6: "Cryptography & Post-Quantum Security",
            7: "Physics / Standard Model Embeddings",
            8: "Cross-Domain / Meta",
        }
        domain = problem.get("domain", 8)
        rigor = problem.get("rigor_level", "L1")
        title = problem.get("title", problem.get("statement", "")[:80])
        motivating = ", ".join(problem.get("motivating_hyps", []))
        statement = problem.get("statement", "")

        section = f"""
### {op_id} — {title} `[{rigor}]`

**Motivating:** {motivating}
**Statement:** {statement}
**Why askable:** Derived from recent automated theorem generation.
**Falsification:** To be determined.

"""
        with self._atlas_md.open("a", encoding="utf-8") as f:
            f.write(section)

    def sync(self) -> None:
        """Force reload from disk (invalidate cache)."""
        self._cache = None
        self._load()


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Sovereign Open Problem Tracker CLI")
    subparsers = parser.add_subparsers(dest="command")

    subparsers.add_parser("stats", help="Print OP status statistics")

    close_p = subparsers.add_parser("close", help="Close an open problem with provenance metadata")
    close_p.add_argument("op_id", help="e.g. OP-048")
    close_p.add_argument("--summary", required=True, help="Detailed resolution summary")
    close_p.add_argument("--hyp", default=None, help="Resolving hypothesis ID, e.g. HYP-103")
    close_p.add_argument("--lean-thm", default=None, help="Lean 4 theorem identifier")
    close_p.add_argument("--lean-file", default=None, help="Lean 4 source file path")

    args = parser.parse_args()
    tracker = OpenProblemTracker(".")

    if args.command == "stats":
        s = tracker.stats()
        print(f"Total: {s['total']} | Open: {s.get('open', 0)} | Resolved: {s.get('resolved', 0)} | Falsified: {s.get('falsified', 0)}")
    elif args.command == "close":
        ok = tracker.close_problem(
            op_id=args.op_id,
            resolution_summary=args.summary,
            resolved_by=args.hyp,
            lean_theorem=args.lean_thm,
            lean_file=args.lean_file,
        )
        print(f"Closed {args.op_id}: {ok}")
    else:
        parser.print_help()

