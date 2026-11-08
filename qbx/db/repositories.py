"""
Repositories for categories, functors, and path signatures.

These provide a thin, typed wrapper over the SQL schema. They are NOT the
enforcement mechanism — the DB triggers are. This layer is for ergonomics.
"""

from __future__ import annotations

import json
from typing import Any, Dict, List, Optional

from psycopg2.extensions import connection as PGConnection

from qbx.path.signature import PathSignature


class CategoryRepository:
    def __init__(self, conn: PGConnection):
        self.conn = conn

    def create_category(self, name: str, description: str = "") -> str:
        with self.conn.cursor() as cur:
            cur.execute(
                "INSERT INTO category (name, description) VALUES (%s, %s) RETURNING id",
                (name, description),
            )
            return cur.fetchone()[0]

    def create_object(self, category_id: str, name: str, universe_id: Optional[str] = None) -> str:
        with self.conn.cursor() as cur:
            cur.execute(
                """INSERT INTO object (category_id, name, universe_id)
                   VALUES (%s, %s, %s) RETURNING id""",
                (category_id, name, universe_id),
            )
            return cur.fetchone()[0]

    def create_morphism(
        self, category_id: str, source_id: str, target_id: str, name: str = ""
    ) -> str:
        with self.conn.cursor() as cur:
            cur.execute(
                """INSERT INTO morphism (category_id, source_id, target_id, name)
                   VALUES (%s, %s, %s, %s) RETURNING id""",
                (category_id, source_id, target_id, name),
            )
            return cur.fetchone()[0]

    def add_identity(self, category_id: str, object_id: str, morphism_id: str) -> None:
        with self.conn.cursor() as cur:
            cur.execute(
                """INSERT INTO identity_morphism (category_id, object_id, morphism_id)
                   VALUES (%s, %s, %s)""",
                (category_id, object_id, morphism_id),
            )

    def add_composition(self, category_id: str, f_id: str, g_id: str, h_id: str) -> None:
        with self.conn.cursor() as cur:
            cur.execute(
                """INSERT INTO composition (category_id, left_id, right_id, result_id)
                   VALUES (%s, %s, %s, %s)""",
                (category_id, g_id, f_id, h_id),
            )


class FunctorRepository:
    def __init__(self, conn: PGConnection):
        self.conn = conn

    def create_functor(
        self, name: str, source_category_id: str, target_category_id: str
    ) -> str:
        with self.conn.cursor() as cur:
            cur.execute(
                """INSERT INTO functor (name, source_category_id, target_category_id)
                   VALUES (%s, %s, %s) RETURNING id""",
                (name, source_category_id, target_category_id),
            )
            return cur.fetchone()[0]

    def map_object(self, functor_id: str, source_obj: str, target_obj: str) -> None:
        with self.conn.cursor() as cur:
            cur.execute(
                """INSERT INTO functor_object_map
                   (functor_id, source_object_id, target_object_id)
                   VALUES (%s, %s, %s)""",
                (functor_id, source_obj, target_obj),
            )

    def map_morphism(self, functor_id: str, source_m: str, target_m: str) -> None:
        with self.conn.cursor() as cur:
            cur.execute(
                """INSERT INTO functor_morphism_map
                   (functor_id, source_morphism_id, target_morphism_id)
                   VALUES (%s, %s, %s)""",
                (functor_id, source_m, target_m),
            )

    def get_violations(self, functor_id: str) -> List[Dict[str, Any]]:
        with self.conn.cursor() as cur:
            cur.execute(
                """SELECT law, details, detected_at
                   FROM functor_law_violation WHERE functor_id = %s
                   ORDER BY detected_at DESC""",
                (functor_id,),
            )
            return [
                {"law": r[0], "details": r[1], "detected_at": r[2]}
                for r in cur.fetchall()
            ]


class PathSignatureRepository:
    def __init__(self, conn: PGConnection):
        self.conn = conn

    def insert(self, sig: PathSignature) -> str:
        with self.conn.cursor() as cur:
            cur.execute(
                """INSERT INTO path_signature
                   (id, category_id, start_object_id, end_object_id,
                    morphism_chain, canonical_bytes, proof_hash, address_hash, metadata)
                   VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                   RETURNING id""",
                (
                    sig.path_id,
                    sig.category_id,
                    sig.start_object_id,
                    sig.end_object_id,
                    sig.morphism_chain,
                    sig.canonical_bytes,
                    sig.proof_hash,
                    sig.address_hash,
                    json.dumps(sig.metadata),
                ),
            )
            return cur.fetchone()[0]

    def get_by_address(self, address_hash: str) -> Optional[Dict[str, Any]]:
        with self.conn.cursor() as cur:
            cur.execute(
                """SELECT id, category_id, start_object_id, end_object_id,
                          morphism_chain, proof_hash, address_hash, metadata
                   FROM path_signature WHERE address_hash = %s""",
                (address_hash,),
            )
            row = cur.fetchone()
            if not row:
                return None
            return {
                "id": row[0],
                "category_id": row[1],
                "start_object_id": row[2],
                "end_object_id": row[3],
                "morphism_chain": row[4],
                "proof_hash": row[5],
                "address_hash": row[6],
                "metadata": row[7],
            }
