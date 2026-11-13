r"""lean4_tactic_oracle.py — Lean 4 Dataset Tactic Oracle
==========================================================
Searches the /data/mind/cognition/lean4/ corpora for tactics and proof patterns
relevant to the Sovereign formalization goals.

Three datasets:
- lean-github.parquet (218,866 rows): tactic-state pairs from GitHub Lean 4 repos
  Columns: url, commit, file_path, full_name, start, end, tactic, state_before, state_after
- lean_workbook.json (140,214 items): competition math problems with formal statements
  Fields: natural_language_statement, answer, tags, formal_statement, split, proof
- wkbk_1009.parquet (25,214 rows): proved workbook problems
  Columns: id, status, tactic, state_before, state_after, natural_language_statement, answer, formal_statement
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Optional
from collections import Counter

import pandas as pd

_LEAN4_DIR = Path("/data/mind/cognition/lean4")
_GITHUB_PARQUET = _LEAN4_DIR / "lean-github.parquet"
_WORKBOOK_JSON = _LEAN4_DIR / "lean_workbook.json"
_WKBK1009_PARQUET = _LEAN4_DIR / "wkbk_1009.parquet"


class TacticOracle:
    """Lean 4 tactic search oracle backed by three corpora."""

    def __init__(self, load_all: bool = True) -> None:
        self._github_df: Optional[pd.DataFrame] = None
        self._workbook: Optional[list] = None
        self._wkbk1009_df: Optional[pd.DataFrame] = None
        if load_all:
            self._load()

    def _load(self) -> None:
        self._github_df = pd.read_parquet(_GITHUB_PARQUET)
        with open(_WORKBOOK_JSON) as f:
            self._workbook = json.load(f)
        self._wkbk1009_df = pd.read_parquet(_WKBK1009_PARQUET)

    @property
    def github_df(self) -> pd.DataFrame:
        if self._github_df is None:
            self._github_df = pd.read_parquet(_GITHUB_PARQUET)
        return self._github_df

    @property
    def wkbk1009_df(self) -> pd.DataFrame:
        if self._wkbk1009_df is None:
            self._wkbk1009_df = pd.read_parquet(_WKBK1009_PARQUET)
        return self._wkbk1009_df

    @property
    def workbook(self) -> list:
        if self._workbook is None:
            with open(_WORKBOOK_JSON) as f:
                self._workbook = json.load(f)
        return self._workbook

    def search_by_goal(self, goal_pattern: str, max_results: int = 10,
                       case_insensitive: bool = True) -> pd.DataFrame:
        """Search GitHub tactic-state pairs by goal pattern in state_before."""
        flags = re.IGNORECASE if case_insensitive else 0
        mask = self.github_df["state_before"].str.contains(
            goal_pattern, regex=True, flags=flags, na=False)
        return self.github_df[mask][
            ["file_path", "full_name", "tactic", "state_before", "state_after"]
        ].head(max_results)

    def find_tactics_for_pattern(self, pattern: str, column: str = "state_before",
                                  max_results: int = 15) -> list[tuple[str, str]]:
        """Find (tactic, state_before) pairs where state matches pattern."""
        mask = self.github_df[column].str.contains(pattern, na=False, regex=False)
        subset = self.github_df[mask][["tactic", "state_before"]].head(max_results)
        return list(zip(subset["tactic"], subset["state_before"]))

    def search_workbook(self, keyword: str, max_results: int = 10,
                        proved_only: bool = False) -> list[dict]:
        """Search competition workbook by natural-language keyword."""
        kw_lower = keyword.lower()
        results = []
        for item in self.workbook:
            stmt = item.get("natural_language_statement", "").lower()
            if kw_lower in stmt:
                if proved_only and not item.get("proof"):
                    continue
                results.append({
                    "natural_language_statement": item["natural_language_statement"],
                    "formal_statement": item.get("formal_statement", ""),
                    "proof": item.get("proof", []),
                    "tags": item.get("tags", ""),
                })
            if len(results) >= max_results:
                break
        return results

    def search_wkbk1009(self, goal_pattern: str, max_results: int = 10,
                         proved_only: bool = True) -> pd.DataFrame:
        """Search proved workbook problems by goal/state pattern."""
        df = self.wkbk1009_df
        if proved_only:
            df = df[df["status"] == "proved"]
        mask = df["state_before"].str.contains(goal_pattern, na=False, regex=True)
        return df[mask][
            ["id", "tactic", "state_before", "state_after", "formal_statement"]
        ].head(max_results)

    def suggest_tactic(self, goal_str: str) -> list[str]:
        """Given a Lean 4 goal string, suggest relevant tactics from all corpora."""
        tactics: list[str] = []
        gh_result = self.search_by_goal(re.escape(goal_str[:60]), max_results=30)
        tactics.extend(gh_result["tactic"].tolist())
        wk_result = self.search_wkbk1009(re.escape(goal_str[:60]), max_results=20)
        if len(wk_result) > 0:
            tactics.extend(wk_result["tactic"].tolist())
        counter = Counter(tactics)
        return [t for t, _ in counter.most_common(10)]

    def sovereign_tactic_search(self, mathlib_type: str) -> list[str]:
        """Search for tactics handling a specific Mathlib type or concept.

        Common queries: "ZMod 2", "Nat.choose", "Finset", "omega", "norm_num"
        """
        results = self.find_tactics_for_pattern(mathlib_type, max_results=20)
        return list({t for t, _ in results})[:10]

    def report_dataset_stats(self) -> dict:
        """Return basic statistics about all three datasets."""
        return {
            "github_rows": len(self.github_df),
            "workbook_items": len(self.workbook),
            "wkbk1009_rows": len(self.wkbk1009_df),
            "proved_count": int((self.wkbk1009_df["status"] == "proved").sum()),
        }

    def workbook_tag_distribution(self) -> dict[str, int]:
        """Return tag frequency distribution from lean_workbook.json."""
        import ast
        tag_counts: Counter = Counter()
        for item in self.workbook:
            try:
                tags = ast.literal_eval(item.get("tags", "[]"))
                for t in tags:
                    tag_counts[t] += 1
            except Exception:
                pass
        return dict(tag_counts.most_common(30))
