"""
src/sedenion/kernel/storage.py
=============================================================================
Durable SQLite WAL Storage Engine for Sovereign Memory Kernel.
Provides persistent key-value and graph storage with ACID guarantees.
=============================================================================
"""

import sqlite3
import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


class KernelStorage:
    """
    SQLite-backed durable storage layer with Write-Ahead Logging (WAL).
    """
    def __init__(self, db_path: str = ":memory:"):
        self.db_path = db_path
        self._conn = sqlite3.connect(db_path, check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._init_db()

    def _init_db(self) -> None:
        with self._conn:
            # Enable WAL mode if on disk
            if self.db_path != ":memory:":
                self._conn.execute("PRAGMA journal_mode=WAL;")
                self._conn.execute("PRAGMA synchronous=NORMAL;")

            # Memory records table
            self._conn.execute("""
                CREATE TABLE IF NOT EXISTS memory_records (
                    key TEXT PRIMARY KEY,
                    content TEXT NOT NULL,
                    coordinates TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                    metadata TEXT
                );
            """)

            # Symbol graph nodes
            self._conn.execute("""
                CREATE TABLE IF NOT EXISTS graph_nodes (
                    node_id TEXT PRIMARY KEY,
                    label TEXT NOT NULL,
                    coordinates TEXT,
                    attributes TEXT
                );
            """)

            # Symbol graph edges
            self._conn.execute("""
                CREATE TABLE IF NOT EXISTS graph_edges (
                    edge_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    source_id TEXT NOT NULL,
                    target_id TEXT NOT NULL,
                    relation TEXT NOT NULL,
                    weight REAL DEFAULT 1.0,
                    attributes TEXT,
                    FOREIGN KEY(source_id) REFERENCES graph_nodes(node_id),
                    FOREIGN KEY(target_id) REFERENCES graph_nodes(node_id)
                );
            """)

    def put_record(self, key: str, content: Any, coordinates: Optional[List[float]] = None, metadata: Optional[Dict[str, Any]] = None) -> None:
        coord_json = json.dumps(coordinates) if coordinates is not None else None
        meta_json = json.dumps(metadata or {})
        cont_str = json.dumps(content) if not isinstance(content, str) else content
        with self._conn:
            self._conn.execute(
                "INSERT OR REPLACE INTO memory_records (key, content, coordinates, metadata) VALUES (?, ?, ?, ?)",
                (key, cont_str, coord_json, meta_json)
            )

    def get_record(self, key: str) -> Optional[Dict[str, Any]]:
        cur = self._conn.execute("SELECT * FROM memory_records WHERE key = ?", (key,))
        row = cur.fetchone()
        if not row:
            return None
        raw_content = row["content"]
        try:
            parsed_content = json.loads(raw_content)
        except (ValueError, TypeError):
            parsed_content = raw_content

        return {
            "key": row["key"],
            "content": parsed_content,
            "coordinates": json.loads(row["coordinates"]) if row["coordinates"] else None,
            "created_at": row["created_at"],
            "metadata": json.loads(row["metadata"]) if row["metadata"] else {},
        }

    def list_records(self) -> List[Dict[str, Any]]:
        cur = self._conn.execute("SELECT * FROM memory_records")
        records = []
        for row in cur.fetchall():
            raw_content = row["content"]
            try:
                parsed_content = json.loads(raw_content)
            except (ValueError, TypeError):
                parsed_content = raw_content
            records.append({
                "key": row["key"],
                "content": parsed_content,
                "coordinates": json.loads(row["coordinates"]) if row["coordinates"] else None,
                "created_at": row["created_at"],
                "metadata": json.loads(row["metadata"]) if row["metadata"] else {},
            })
        return records

    def put_node(self, node_id: str, label: str, coordinates: Optional[List[float]] = None, attributes: Optional[Dict[str, Any]] = None) -> None:
        coord_json = json.dumps(coordinates) if coordinates is not None else None
        attr_json = json.dumps(attributes or {})
        with self._conn:
            self._conn.execute(
                "INSERT OR REPLACE INTO graph_nodes (node_id, label, coordinates, attributes) VALUES (?, ?, ?, ?)",
                (node_id, label, coord_json, attr_json)
            )

    def put_edge(self, source_id: str, target_id: str, relation: str, weight: float = 1.0, attributes: Optional[Dict[str, Any]] = None) -> None:
        attr_json = json.dumps(attributes or {})
        with self._conn:
            self._conn.execute(
                "INSERT INTO graph_edges (source_id, target_id, relation, weight, attributes) VALUES (?, ?, ?, ?, ?)",
                (source_id, target_id, relation, weight, attr_json)
            )

    def get_node(self, node_id: str) -> Optional[Dict[str, Any]]:
        cur = self._conn.execute("SELECT * FROM graph_nodes WHERE node_id = ?", (node_id,))
        row = cur.fetchone()
        if not row:
            return None
        return {
            "node_id": row["node_id"],
            "label": row["label"],
            "coordinates": json.loads(row["coordinates"]) if row["coordinates"] else None,
            "attributes": json.loads(row["attributes"]) if row["attributes"] else {}
        }

    def get_neighbors(self, node_id: str) -> List[Dict[str, Any]]:
        cur = self._conn.execute("""
            SELECT e.relation, e.weight, n.* FROM graph_edges e
            JOIN graph_nodes n ON e.target_id = n.node_id
            WHERE e.source_id = ?
        """, (node_id,))
        neighbors = []
        for row in cur.fetchall():
            neighbors.append({
                "relation": row["relation"],
                "weight": row["weight"],
                "node_id": row["node_id"],
                "label": row["label"],
                "coordinates": json.loads(row["coordinates"]) if row["coordinates"] else None,
                "attributes": json.loads(row["attributes"]) if row["attributes"] else {}
            })
        return neighbors

    def get_all_nodes(self, label: Optional[str] = None) -> List[Dict[str, Any]]:
        if label:
            cur = self._conn.execute("SELECT * FROM graph_nodes WHERE label = ?", (label,))
        else:
            cur = self._conn.execute("SELECT * FROM graph_nodes")
        nodes = []
        for row in cur.fetchall():
            nodes.append({
                "node_id": row["node_id"],
                "label": row["label"],
                "coordinates": json.loads(row["coordinates"]) if row["coordinates"] else None,
                "attributes": json.loads(row["attributes"]) if row["attributes"] else {}
            })
        return nodes

    def get_all_edges(self) -> List[Dict[str, Any]]:
        cur = self._conn.execute("SELECT * FROM graph_edges")
        edges = []
        for row in cur.fetchall():
            edges.append({
                "edge_id": row["edge_id"],
                "source_id": row["source_id"],
                "target_id": row["target_id"],
                "relation": row["relation"],
                "weight": row["weight"],
                "attributes": json.loads(row["attributes"]) if row["attributes"] else {}
            })
        return edges

    def close(self) -> None:
        self._conn.close()
