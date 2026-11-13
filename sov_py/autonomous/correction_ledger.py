"""
PAF Operational Correction Ledger & Directive Synthesizer.
Adapted from persistent-agent-framework for the Sovereign Autonomous Research Harness.

Core Principle: Self-Correcting Behavior
1. Mistake occurs (e.g. proof failure, syntax error, hallucinated bijection, loss divergence)
2. Logged to ledger: (category, what, why, should_have)
3. Pattern counter detects recurring mistakes (threshold >= 2)
4. System automatically synthesizes an Operational Directive
5. Directives constrain future conjecture generation and reasoning passes
"""

from __future__ import annotations

import datetime
import json
import sqlite3
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional


@dataclass
class MistakeEntry:
    id: Optional[int]
    category: str
    what: str
    why: str
    should_have: str
    timestamp: str


@dataclass
class DirectiveEntry:
    id: Optional[int]
    category: str
    rule_text: str
    priority: int
    trigger_count: int
    created_at: str
    active: bool


class OperationalLedger:
    """
    Self-correcting mistake ledger and dynamic directive engine.
    """

    def __init__(self, db_path: str = ":memory:") -> None:
        self.db_path = db_path
        if db_path == ":memory:":
            self._conn = sqlite3.connect(":memory:")
        else:
            self._conn = sqlite3.connect(db_path)
        self._init_db()

    def _init_db(self) -> None:
        with self._conn:
            self._conn.execute("""
                CREATE TABLE IF NOT EXISTS operational_mistakes (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    category TEXT NOT NULL,
                    what TEXT NOT NULL,
                    why TEXT NOT NULL,
                    should_have TEXT NOT NULL,
                    timestamp TEXT NOT NULL
                )
            """)
            self._conn.execute("""
                CREATE TABLE IF NOT EXISTS operational_directives (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    category TEXT UNIQUE NOT NULL,
                    rule_text TEXT NOT NULL,
                    priority INTEGER NOT NULL DEFAULT 1,
                    trigger_count INTEGER NOT NULL DEFAULT 1,
                    created_at TEXT NOT NULL,
                    active INTEGER NOT NULL DEFAULT 1
                )
            """)

    def log_mistake(
        self,
        category: str,
        what: str,
        why: str,
        should_have: str,
    ) -> MistakeEntry:
        """Record an operational mistake or verification failure into the ledger."""
        now = datetime.datetime.now(datetime.timezone.utc).isoformat()
        with self._conn:
            cur = self._conn.execute(
                """
                INSERT INTO operational_mistakes (category, what, why, should_have, timestamp)
                VALUES (?, ?, ?, ?, ?)
                """,
                (category, what, why, should_have, now),
            )
            mistake_id = cur.lastrowid

        entry = MistakeEntry(
            id=mistake_id,
            category=category,
            what=what,
            why=why,
            should_have=should_have,
            timestamp=now,
        )

        # Check if this category has reached the recurrence threshold
        self.evaluate_directives(threshold=2)
        return entry

    def get_mistakes(self, category: Optional[str] = None) -> List[MistakeEntry]:
        """Retrieve recorded mistakes, optionally filtered by category."""
        query = "SELECT id, category, what, why, should_have, timestamp FROM operational_mistakes"
        params: List[Any] = []
        if category:
            query += " WHERE category = ?"
            params.append(category)
        query += " ORDER BY id ASC"

        cur = self._conn.execute(query, params)
        return [
            MistakeEntry(
                id=row[0],
                category=row[1],
                what=row[2],
                why=row[3],
                should_have=row[4],
                timestamp=row[5],
            )
            for row in cur.fetchall()
        ]

    def evaluate_directives(self, threshold: int = 2) -> List[DirectiveEntry]:
        """
        Evaluate category recurrence frequencies.
        If a category has >= threshold mistakes, synthesize or escalate an operational directive.
        """
        cur = self._conn.execute("""
            SELECT category, COUNT(*) as cnt
            FROM operational_mistakes
            GROUP BY category
            HAVING cnt >= ?
        """, (threshold,))
        recurring = cur.fetchall()

        synthesized: List[DirectiveEntry] = []
        now = datetime.datetime.now(datetime.timezone.utc).isoformat()

        for cat, count in recurring:
            # Generate rule based on latest mistake in category
            latest = self._conn.execute("""
                SELECT should_have FROM operational_mistakes
                WHERE category = ?
                ORDER BY id DESC LIMIT 1
            """, (cat,)).fetchone()
            rule_text = latest[0] if latest else f"Enforce strict invariant check for {cat}"

            priority = min(3, count - threshold + 1)

            with self._conn:
                self._conn.execute("""
                    INSERT INTO operational_directives (category, rule_text, priority, trigger_count, created_at, active)
                    VALUES (?, ?, ?, ?, ?, 1)
                    ON CONFLICT(category) DO UPDATE SET
                        rule_text = excluded.rule_text,
                        priority = excluded.priority,
                        trigger_count = excluded.trigger_count,
                        active = 1
                """, (cat, rule_text, priority, count, now))

            entry = DirectiveEntry(
                id=None,
                category=cat,
                rule_text=rule_text,
                priority=priority,
                trigger_count=count,
                created_at=now,
                active=True,
            )
            synthesized.append(entry)

        return synthesized

    def get_active_directives(self) -> List[DirectiveEntry]:
        """Retrieve all currently active operational directives sorted by priority."""
        cur = self._conn.execute("""
            SELECT id, category, rule_text, priority, trigger_count, created_at, active
            FROM operational_directives
            WHERE active = 1
            ORDER BY priority DESC, id ASC
        """)
        return [
            DirectiveEntry(
                id=row[0],
                category=row[1],
                rule_text=row[2],
                priority=row[3],
                trigger_count=row[4],
                created_at=row[5],
                active=bool(row[6]),
            )
            for row in cur.fetchall()
        ]

    def export_directives_markdown(self, target_path: Optional[str] = None) -> str:
        """Export active directives formatted as markdown for inclusion in agent prompts."""
        directives = self.get_active_directives()
        lines = [
            "# Operational Directives (Synthesized from Mistake Ledger)",
            "",
            "These behavioral constraints have been automatically generated from operational error patterns.",
            "",
        ]
        if not directives:
            lines.append("*No recurring failure patterns detected. All invariants nominal.*")
        else:
            for d in directives:
                lines.append(f"- **[PRIORITY {d.priority}] {d.category}** (triggered {d.trigger_count}x): {d.rule_text}")

        md_content = "\n".join(lines) + "\n"
        if target_path:
            p = Path(target_path)
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(md_content, encoding="utf-8")

        return md_content
