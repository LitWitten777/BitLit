"""
Durable State & Persistence Layer for the Autonomous Reasoning Engine.
Uses SQLite in WAL (Write-Ahead Logging) mode to safely record all mathematical
hypotheses, dual verification runs (SMT/exact), minimal counterexamples,
topological representation checkpoints, and system telemetry across restarts.
"""

from __future__ import annotations

import hashlib
import json
import sqlite3
import subprocess
import time
from collections.abc import Generator
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any


def get_git_commit_hash() -> str:
    try:
        res = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, timeout=5)
        if res.returncode == 0:
            return res.stdout.strip()
    except Exception:
        pass
    return "UNKNOWN_COMMIT"


def get_lean_version_string() -> str:
    try:
        res = subprocess.run(["lake", "--version"], capture_output=True, text=True, timeout=5)
        if res.returncode == 0:
            return res.stdout.strip()
    except Exception:
        pass
    return "Lean 4 / Lake"


def compute_canonical_proof_hash(
    hypothesis_id: str,
    statement: str,
    predicate: str,
    parameters: dict[str, Any],
    engine: str,
    lean_source: str | None,
    kernel_axioms: list[str] | None,
    parent_hash: str,
    timestamp: float,
) -> str:
    payload = {
        "hypothesis_id": hypothesis_id,
        "statement": statement,
        "predicate": predicate,
        "parameters": parameters,
        "engine": engine,
        "lean_source": (lean_source or "").strip(),
        "kernel_axioms": sorted(kernel_axioms or []),
        "parent_hash": parent_hash,
        "timestamp": round(timestamp, 3),
    }
    canonical_bytes = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(canonical_bytes).hexdigest()


@dataclass
class HypothesisRecord:
    id: str
    statement: str
    category: str
    status: str  # "OPEN", "CONFIRMED", "FALSIFIED", "ERROR"
    proof_summary: str | None = None
    details: dict[str, Any] | None = None
    proof_hash: str | None = None
    created_at: float = 0.0
    updated_at: float = 0.0


@dataclass
class VerificationRecord:
    hypothesis_id: str
    engine: str  # "Z3_SMT", "EXACT_ARITHMETIC", "LEAN4"
    status: str  # "PROVED", "REFUTED", "TIMEOUT", "ERROR"
    duration_ms: float
    counterexample: dict[str, Any] | None = None
    logs: str | None = None
    lean_source: str | None = None
    proof_hash: str | None = None
    axioms: list[str] | None = None
    timestamp: float = 0.0
    id: int | None = None


@dataclass
class TheoremProvenanceRecord:
    hypothesis_id: str
    proof_hash: str
    parent_hash: str
    engine: str
    kernel_axioms: list[str]
    toolchain_git_hash: str
    lean_version: str
    timestamp: float
    receipt: dict[str, Any]
    id: int | None = None



@dataclass
class TopologicalCheckpoint:
    epoch: int
    dimension: int
    accuracy: float
    max_persistence: float
    persistent_entropy: float
    betti_0: int
    betti_1: int
    loss: float
    timestamp: float = 0.0
    sector: int = 1       # charge sector χ stepped by the learner
    id: int | None = None


class ReasoningStore:
    """Thread-safe, durable SQLite database for autonomous reasoning persistence."""

    def __init__(self, db_path: str = "data/reasoning_store.db"):
        self.is_memory = str(db_path) == ":memory:"
        self.db_path = Path(db_path)
        self._shared_conn: sqlite3.Connection | None = None
        if self.is_memory:
            self._shared_conn = sqlite3.connect(":memory:", timeout=30.0, check_same_thread=False)
            self._shared_conn.row_factory = sqlite3.Row
            self._shared_conn.execute("PRAGMA foreign_keys=ON;")
        else:
            self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self._init_schema()

    @contextmanager
    def _connection(self) -> Generator[sqlite3.Connection, None, None]:
        if self._shared_conn is not None:
            with self._shared_conn:
                yield self._shared_conn
            return
        conn = sqlite3.connect(str(self.db_path), timeout=30.0)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL;")
        conn.execute("PRAGMA synchronous=NORMAL;")
        conn.execute("PRAGMA foreign_keys=ON;")
        try:
            with conn:
                yield conn
        finally:
            conn.close()

    def _get_connection(self) -> sqlite3.Connection:
        if self._shared_conn is not None:
            return self._shared_conn
        conn = sqlite3.connect(str(self.db_path), timeout=30.0)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA journal_mode=WAL;")
        conn.execute("PRAGMA synchronous=NORMAL;")
        conn.execute("PRAGMA foreign_keys=ON;")
        return conn

    def close(self) -> None:
        if self._shared_conn is not None:
            self._shared_conn.close()
            self._shared_conn = None

    def _init_schema(self) -> None:
        with self._connection() as conn:
            conn.executescript("""
            CREATE TABLE IF NOT EXISTS hypotheses (
                id TEXT PRIMARY KEY,
                statement TEXT NOT NULL,
                category TEXT NOT NULL,
                status TEXT NOT NULL,
                proof_summary TEXT,
                details_json TEXT,
                created_at REAL NOT NULL,
                updated_at REAL NOT NULL
            );

            CREATE TABLE IF NOT EXISTS verification_runs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                hypothesis_id TEXT NOT NULL,
                engine TEXT NOT NULL,
                status TEXT NOT NULL,
                duration_ms REAL NOT NULL,
                counterexample_json TEXT,
                logs TEXT,
                lean_source TEXT,
                timestamp REAL NOT NULL,
                FOREIGN KEY(hypothesis_id) REFERENCES hypotheses(id) ON DELETE CASCADE
            );

            CREATE TABLE IF NOT EXISTS topological_checkpoints (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                epoch INTEGER NOT NULL,
                dimension INTEGER NOT NULL,
                accuracy REAL NOT NULL,
                max_persistence REAL NOT NULL,
                persistent_entropy REAL NOT NULL,
                betti_0 INTEGER NOT NULL,
                betti_1 INTEGER NOT NULL,
                loss REAL NOT NULL,
                timestamp REAL NOT NULL
            );

            CREATE TABLE IF NOT EXISTS system_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                level TEXT NOT NULL,
                module TEXT NOT NULL,
                message TEXT NOT NULL,
                metadata_json TEXT,
                timestamp REAL NOT NULL
            );

            CREATE TABLE IF NOT EXISTS schema_versions (
                version INTEGER PRIMARY KEY,
                applied_at REAL NOT NULL,
                description TEXT NOT NULL
            );

            CREATE INDEX IF NOT EXISTS idx_hypotheses_status ON hypotheses(status);
            CREATE INDEX IF NOT EXISTS idx_verifications_hyp ON verification_runs(hypothesis_id);
            CREATE INDEX IF NOT EXISTS idx_topo_epoch ON topological_checkpoints(epoch);
            """)
            # v1: lean_source column (pre-dates versioning; marked applied if already present)
            self._run_migration(
                conn, 1,
                "Add lean_source to verification_runs",
                "ALTER TABLE verification_runs ADD COLUMN lean_source TEXT;",
            )
            # v2: cryptographic provenance ledger, proof_hash, and axioms_json
            self._run_migration(
                conn, 2,
                "Add cryptographic provenance table and proof_hash columns",
                """
                ALTER TABLE verification_runs ADD COLUMN proof_hash TEXT;
                ALTER TABLE verification_runs ADD COLUMN axioms_json TEXT;
                ALTER TABLE hypotheses ADD COLUMN proof_hash TEXT;
                CREATE TABLE IF NOT EXISTS theorem_provenance (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    hypothesis_id TEXT NOT NULL,
                    verification_run_id INTEGER,
                    proof_hash TEXT NOT NULL UNIQUE,
                    parent_hash TEXT NOT NULL,
                    kernel_axioms_json TEXT NOT NULL,
                    toolchain_git_hash TEXT NOT NULL,
                    lean_version TEXT NOT NULL,
                    timestamp REAL NOT NULL,
                    receipt_json TEXT NOT NULL,
                    FOREIGN KEY(hypothesis_id) REFERENCES hypotheses(id) ON DELETE CASCADE,
                    FOREIGN KEY(verification_run_id) REFERENCES verification_runs(id) ON DELETE SET NULL
                );
                CREATE INDEX IF NOT EXISTS idx_provenance_hyp ON theorem_provenance(hypothesis_id);
                CREATE INDEX IF NOT EXISTS idx_provenance_hash ON theorem_provenance(proof_hash);
                """,
            )

    def _run_migration(
        self, conn: sqlite3.Connection, version: int, description: str, sql: str
    ) -> None:
        """Applies a schema migration exactly once, keyed by integer version number.

        Idempotent: checks schema_versions before executing. Tolerates pre-existing
        columns / indexes from databases created before versioning was introduced.
        """
        applied = conn.execute(
            "SELECT 1 FROM schema_versions WHERE version = ?;", (version,)
        ).fetchone()
        if applied:
            return
        for stmt in sql.strip().split(";"):
            stmt_clean = stmt.strip()
            if not stmt_clean:
                continue
            try:
                conn.execute(stmt_clean)
            except sqlite3.OperationalError:
                # Column / index already exists from a pre-versioning database.
                pass
        conn.execute(
            "INSERT INTO schema_versions (version, applied_at, description) VALUES (?, ?, ?);",
            (version, time.time(), description),
        )


    def save_hypothesis(self, record: HypothesisRecord) -> None:
        now = time.time()
        created = record.created_at or now
        updated = record.updated_at or now
        details_str = json.dumps(record.details or {})

        with self._connection() as conn:
            existing = conn.execute(
                "SELECT id, status FROM hypotheses WHERE statement = ?;", (record.statement,)
            ).fetchone()
            if existing:
                target_id, existing_status = existing
                record.id = target_id
                if existing_status in ("CONFIRMED", "FALSIFIED"):
                    return
            else:
                target_id = record.id
            conn.execute(
                """
            INSERT INTO hypotheses (id, statement, category, status, proof_summary, details_json, created_at, updated_at)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(id) DO UPDATE SET
                statement=excluded.statement,
                category=excluded.category,
                status=excluded.status,
                proof_summary=excluded.proof_summary,
                details_json=excluded.details_json,
                updated_at=excluded.updated_at;
            """,
                (
                    target_id,
                    record.statement,
                    record.category,
                    record.status,
                    record.proof_summary,
                    details_str,
                    created,
                    updated,
                ),
            )

    def update_hypothesis_status(
        self, hyp_id: str, status: str, proof_summary: str | None = None
    ) -> None:
        now = time.time()
        if proof_summary is not None and not isinstance(proof_summary, str):
            try:
                proof_summary = json.dumps(proof_summary)
            except Exception:
                proof_summary = str(proof_summary)
        with self._connection() as conn:
            conn.execute(
                """
            UPDATE hypotheses
            SET status = ?, proof_summary = COALESCE(?, proof_summary), updated_at = ?
            WHERE id = ?;
            """,
                (status, proof_summary, now, hyp_id),
            )

    def get_hypothesis(self, hyp_id: str) -> HypothesisRecord | None:
        with self._connection() as conn:
            row = conn.execute("SELECT * FROM hypotheses WHERE id = ?;", (hyp_id,)).fetchone()
            if not row:
                return None
            return HypothesisRecord(
                id=row["id"],
                statement=row["statement"],
                category=row["category"],
                status=row["status"],
                proof_summary=row["proof_summary"],
                details=json.loads(row["details_json"]) if row["details_json"] else {},
                proof_hash=row["proof_hash"] if "proof_hash" in row.keys() else None,
                created_at=row["created_at"],
                updated_at=row["updated_at"],
            )

    def list_hypotheses(
        self, status: str | None = None, category: str | None = None
    ) -> list[HypothesisRecord]:
        query = "SELECT * FROM hypotheses WHERE 1=1"
        params: list[Any] = []
        if status:
            query += " AND status = ?"
            params.append(status)
        if category:
            query += " AND category = ?"
            params.append(category)
        query += " ORDER BY created_at ASC;"

        with self._connection() as conn:
            rows = conn.execute(query, params).fetchall()
            return [
                HypothesisRecord(
                    id=r["id"],
                    statement=r["statement"],
                    category=r["category"],
                    status=r["status"],
                    proof_summary=r["proof_summary"],
                    details=json.loads(r["details_json"]) if r["details_json"] else {},
                    proof_hash=r["proof_hash"] if "proof_hash" in r.keys() else None,
                    created_at=r["created_at"],
                    updated_at=r["updated_at"],
                )
                for r in rows
            ]

    def record_verification(self, rec: VerificationRecord) -> int:
        ts = rec.timestamp or time.time()
        ce_str = json.dumps(rec.counterexample) if rec.counterexample else None
        axioms_str = json.dumps(rec.axioms) if rec.axioms else None
        with self._connection() as conn:
            # Ensure parent hypothesis exists before recording to guarantee foreign key integrity
            h_row = conn.execute("SELECT id FROM hypotheses WHERE id = ?;", (rec.hypothesis_id,)).fetchone()
            if not h_row:
                conn.execute(
                    """
                    INSERT INTO hypotheses (id, statement, category, status, created_at, updated_at)
                    VALUES (?, ?, ?, ?, ?, ?)
                    ON CONFLICT(id) DO NOTHING;
                    """,
                    (rec.hypothesis_id, f"Hypothesis {rec.hypothesis_id}", "General", "OPEN", ts, ts),
                )
            cur = conn.execute(
                """
            INSERT INTO verification_runs (hypothesis_id, engine, status, duration_ms, counterexample_json, logs, lean_source, proof_hash, axioms_json, timestamp)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?);
            """,
                (rec.hypothesis_id, rec.engine, rec.status, rec.duration_ms, ce_str, rec.logs, rec.lean_source, rec.proof_hash, axioms_str, ts),
            )
            return cur.lastrowid or 0

    def list_verifications(self, hypothesis_id: str | None = None) -> list[VerificationRecord]:
        query = "SELECT * FROM verification_runs"
        params = []
        if hypothesis_id:
            query += " WHERE hypothesis_id = ?"
            params.append(hypothesis_id)
        query += " ORDER BY timestamp DESC LIMIT 100;"

        with self._connection() as conn:
            rows = conn.execute(query, params).fetchall()
            return [
                VerificationRecord(
                    id=r["id"],
                    hypothesis_id=r["hypothesis_id"],
                    engine=r["engine"],
                    status=r["status"],
                    duration_ms=r["duration_ms"],
                    counterexample=json.loads(r["counterexample_json"])
                    if r["counterexample_json"]
                    else None,
                    logs=r["logs"],
                    lean_source=r["lean_source"] if "lean_source" in r.keys() else None,
                    proof_hash=r["proof_hash"] if "proof_hash" in r.keys() else None,
                    axioms=json.loads(r["axioms_json"]) if "axioms_json" in r.keys() and r["axioms_json"] else None,
                    timestamp=r["timestamp"],
                )
                for r in rows
            ]

    def record_theorem_provenance(
        self,
        hypothesis_id: str,
        verification_run_id: int | None,
        proof_hash: str,
        parent_hash: str,
        kernel_axioms: list[str],
        toolchain_git_hash: str,
        lean_version: str,
        timestamp: float,
        receipt: dict[str, Any],
    ) -> int:
        with self._connection() as conn:
            cur = conn.execute(
                """
                INSERT INTO theorem_provenance (
                    hypothesis_id, verification_run_id, proof_hash, parent_hash,
                    kernel_axioms_json, toolchain_git_hash, lean_version, timestamp, receipt_json
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(proof_hash) DO NOTHING;
                """,
                (
                    hypothesis_id,
                    verification_run_id,
                    proof_hash,
                    parent_hash,
                    json.dumps(kernel_axioms),
                    toolchain_git_hash,
                    lean_version,
                    timestamp,
                    json.dumps(receipt),
                ),
            )
            # Also update hypothesis proof_hash
            conn.execute(
                "UPDATE hypotheses SET proof_hash = ? WHERE id = ?;",
                (proof_hash, hypothesis_id),
            )
            if verification_run_id:
                conn.execute(
                    "UPDATE verification_runs SET proof_hash = ?, axioms_json = ? WHERE id = ?;",
                    (proof_hash, json.dumps(kernel_axioms), verification_run_id),
                )
            return cur.lastrowid or 0

    def get_latest_provenance_hash(self) -> str:
        with self._connection() as conn:
            row = conn.execute(
                "SELECT proof_hash FROM theorem_provenance ORDER BY id DESC LIMIT 1;"
            ).fetchone()
            if row and row["proof_hash"]:
                return str(row["proof_hash"])
            return "0" * 64

    def get_provenance_chain(self, limit: int = 100) -> list[TheoremProvenanceRecord]:
        with self._connection() as conn:
            rows = conn.execute(
                "SELECT * FROM theorem_provenance ORDER BY id ASC LIMIT ?;", (limit,)
            ).fetchall()
            return [
                TheoremProvenanceRecord(
                    id=r["id"],
                    hypothesis_id=r["hypothesis_id"],
                    proof_hash=r["proof_hash"],
                    parent_hash=r["parent_hash"],
                    engine=json.loads(r["receipt_json"]).get("engine", "UNKNOWN") if r["receipt_json"] else "UNKNOWN",
                    kernel_axioms=json.loads(r["kernel_axioms_json"]) if r["kernel_axioms_json"] else [],
                    toolchain_git_hash=r["toolchain_git_hash"],
                    lean_version=r["lean_version"],
                    timestamp=r["timestamp"],
                    receipt=json.loads(r["receipt_json"]) if r["receipt_json"] else {},
                )
                for r in rows
            ]

    def verify_provenance_chain(self) -> dict[str, Any]:
        """
        Cryptographically audits the entire Merkle provenance chain of verified theorems.
        """
        records = self.get_provenance_chain(limit=10000)
        if not records:
            return {"is_valid": True, "count": 0, "merkle_root": "0" * 64, "errors": []}

        errors = []
        expected_parent = "0" * 64
        for idx, rec in enumerate(records):
            if rec.parent_hash != expected_parent:
                errors.append(
                    f"Record {rec.id} ({rec.hypothesis_id}) broken parent link: expected {expected_parent}, got {rec.parent_hash}"
                )
            rcpt = rec.receipt
            recomputed = compute_canonical_proof_hash(
                hypothesis_id=rec.hypothesis_id,
                statement=rcpt.get("statement", ""),
                predicate=rcpt.get("predicate", ""),
                parameters=rcpt.get("parameters", {}),
                engine=rcpt.get("engine", ""),
                lean_source=rcpt.get("lean_source"),
                kernel_axioms=rec.kernel_axioms,
                parent_hash=rec.parent_hash,
                timestamp=rec.timestamp,
            )
            if recomputed != rec.proof_hash:
                errors.append(
                    f"Record {rec.id} ({rec.hypothesis_id}) hash mismatch: expected {recomputed}, got {rec.proof_hash}"
                )
            expected_parent = rec.proof_hash

        return {
            "is_valid": len(errors) == 0,
            "count": len(records),
            "merkle_root": expected_parent,
            "errors": errors,
        }

    def backfill_provenance(self) -> int:
        """
        Backfills cryptographic hashes and Merkle chain for confirmed hypotheses lacking provenance.
        """
        with self._connection() as conn:
            rows = conn.execute("""
                SELECT h.id, h.statement, h.details_json, h.created_at,
                       v.id as v_id, v.engine, v.lean_source, v.logs, v.timestamp as v_ts
                FROM hypotheses h
                LEFT JOIN verification_runs v ON h.id = v.hypothesis_id AND v.status = 'PROVED'
                WHERE h.status = 'CONFIRMED'
                  AND h.id NOT IN (SELECT hypothesis_id FROM theorem_provenance)
                GROUP BY h.id
                ORDER BY h.created_at ASC;
            """).fetchall()

            git_hash = get_git_commit_hash()
            lean_ver = get_lean_version_string()
            count = 0
            for r in rows:
                hyp_id = r["id"]
                stmt = r["statement"]
                details = json.loads(r["details_json"]) if r["details_json"] else {}
                pred = details.get("predicate", "")
                params = {k: v for k, v in details.items() if k not in ("conjecture_type", "predicate")}
                engine = r["engine"] or "EXACT_ARITHMETIC"
                lean_src = r["lean_source"]
                ts = r["v_ts"] or r["created_at"] or time.time()
                v_id = r["v_id"]

                axioms: list[str] = []
                if r["logs"] and "Axioms:" in r["logs"]:
                    import re
                    m = re.search(r"Axioms:\s*(\[.*?\])", r["logs"])
                    if m:
                        try:
                            import ast
                            axioms = ast.literal_eval(m.group(1))
                        except Exception:
                            pass
                if not axioms and engine == "LEAN4_KERNEL":
                    axioms = ["propext", "Classical.choice", "Quot.sound"]

                parent_hash = self.get_latest_provenance_hash()
                p_hash = compute_canonical_proof_hash(
                    hypothesis_id=hyp_id,
                    statement=stmt,
                    predicate=pred,
                    parameters=params,
                    engine=engine,
                    lean_source=lean_src,
                    kernel_axioms=axioms,
                    parent_hash=parent_hash,
                    timestamp=ts,
                )
                receipt = {
                    "hypothesis_id": hyp_id,
                    "statement": stmt,
                    "predicate": pred,
                    "parameters": params,
                    "engine": engine,
                    "lean_source": lean_src,
                    "kernel_axioms": axioms,
                    "parent_hash": parent_hash,
                    "proof_hash": p_hash,
                    "timestamp": ts,
                    "git_commit": git_hash,
                    "lean_version": lean_ver,
                }
                self.record_theorem_provenance(
                    hypothesis_id=hyp_id,
                    verification_run_id=v_id,
                    proof_hash=p_hash,
                    parent_hash=parent_hash,
                    kernel_axioms=axioms,
                    toolchain_git_hash=git_hash,
                    lean_version=lean_ver,
                    timestamp=ts,
                    receipt=receipt,
                )
                count += 1
            return count

    def get_statistics(self) -> dict[str, Any]:
        """Return aggregate statistics on hypotheses, verifications, and checkpoints."""
        with self._connection() as conn:
            total_hyp = conn.execute("SELECT COUNT(*) FROM hypotheses;").fetchone()[0]
            status_counts = dict(conn.execute("SELECT status, COUNT(*) FROM hypotheses GROUP BY status;").fetchall())
            total_verif = conn.execute("SELECT COUNT(*) FROM verification_runs;").fetchone()[0]
            total_checkpoints = conn.execute("SELECT COUNT(*) FROM topological_checkpoints;").fetchone()[0]
            return {
                "total_hypotheses": total_hyp,
                "confirmed_count": status_counts.get("CONFIRMED", 0),
                "proved_count": status_counts.get("PROVED", 0),
                "open_count": status_counts.get("OPEN", 0),
                "falsified_count": status_counts.get("FALSIFIED", 0),
                "status_breakdown": status_counts,
                "total_verifications": total_verif,
                "total_checkpoints": total_checkpoints,
            }

    def save_topological_checkpoint(self, cp: TopologicalCheckpoint) -> int:
        ts = cp.timestamp or time.time()
        with self._connection() as conn:
            cur = conn.execute(
                """
            INSERT INTO topological_checkpoints (epoch, dimension, accuracy, max_persistence, persistent_entropy, betti_0, betti_1, loss, timestamp)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?);
            """,
                (
                    cp.epoch,
                    cp.dimension,
                    cp.accuracy,
                    cp.max_persistence,
                    cp.persistent_entropy,
                    cp.betti_0,
                    cp.betti_1,
                    cp.loss,
                    ts,
                ),
            )
            return cur.lastrowid or 0

    def get_latest_topological_checkpoints(self, limit: int = 50) -> list[TopologicalCheckpoint]:
        with self._connection() as conn:
            rows = conn.execute(
                """
            SELECT * FROM topological_checkpoints ORDER BY epoch DESC, timestamp DESC LIMIT ?;
            """,
                (limit,),
            ).fetchall()
            return [
                TopologicalCheckpoint(
                    id=r["id"],
                    epoch=r["epoch"],
                    dimension=r["dimension"],
                    accuracy=r["accuracy"],
                    max_persistence=r["max_persistence"],
                    persistent_entropy=r["persistent_entropy"],
                    betti_0=r["betti_0"],
                    betti_1=r["betti_1"],
                    loss=r["loss"],
                    timestamp=r["timestamp"],
                )
                for r in rows
            ]

    def log_system_event(
        self, level: str, module: str, message: str, metadata: dict[str, Any] | None = None
    ) -> None:
        ts = time.time()
        meta_str = json.dumps(metadata) if metadata else None
        with self._connection() as conn:
            conn.execute(
                """
            INSERT INTO system_logs (level, module, message, metadata_json, timestamp)
            VALUES (?, ?, ?, ?, ?);
            """,
                (level, module, message, meta_str, ts),
            )

    def get_summary_stats(self) -> dict[str, Any]:
        with self._connection() as conn:
            total_hyp = conn.execute("SELECT COUNT(*) FROM hypotheses;").fetchone()[0]
            confirmed = conn.execute(
                "SELECT COUNT(*) FROM hypotheses WHERE status = 'CONFIRMED';"
            ).fetchone()[0]
            falsified = conn.execute(
                "SELECT COUNT(*) FROM hypotheses WHERE status = 'FALSIFIED';"
            ).fetchone()[0]
            open_hyp = conn.execute(
                "SELECT COUNT(*) FROM hypotheses WHERE status = 'OPEN';"
            ).fetchone()[0]
            total_verif = conn.execute("SELECT COUNT(*) FROM verification_runs;").fetchone()[0]
            latest_cp = conn.execute(
                "SELECT * FROM topological_checkpoints ORDER BY id DESC LIMIT 1;"
            ).fetchone()

            return {
                "total_hypotheses": total_hyp,
                "confirmed_hypotheses": confirmed,
                "falsified_hypotheses": falsified,
                "open_hypotheses": open_hyp,
                "total_verifications": total_verif,
                "latest_checkpoint": dict(latest_cp) if latest_cp else None,
            }
