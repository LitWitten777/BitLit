"""
Minimal Neo4j client for the categorical schema.

Provides helpers for ingesting categories, objects, morphisms, functors,
natural transformations, and path signatures.

All Cypher statements use ``$param`` placeholders (restored here after a
Markdown/KaTeX rendering pass had eaten the ``$...$`` spans).
"""

from __future__ import annotations

import os
from typing import Any, Dict, List, Optional

from neo4j import GraphDatabase, Driver


class Neo4jClient:
    def __init__(
        self,
        uri: Optional[str] = None,
        user: Optional[str] = None,
        password: Optional[str] = None,
    ):
        self.uri = uri or os.getenv("NEO4J_URI", "bolt://localhost:7687")
        self.user = user or os.getenv("NEO4J_USER", "neo4j")
        self.password = password or os.getenv("NEO4J_PASS", "qbx-test-password")
        self._driver: Optional[Driver] = None

    def connect(self) -> Driver:
        if self._driver is None:
            self._driver = GraphDatabase.driver(
                self.uri, auth=(self.user, self.password)
            )
        return self._driver

    def close(self) -> None:
        if self._driver is not None:
            self._driver.close()
            self._driver = None

    # ---- Ingestion --------------------------------------------------------

    def upsert_category(self, category_id: str, name: str) -> None:
        with self.connect().session() as s:
            s.run(
                "MERGE (c:Category {id: $id}) SET c.name = $name",
                id=category_id, name=name,
            )

    def upsert_object(self, object_id: str, name: str, category_id: str) -> None:
        with self.connect().session() as s:
            s.run(
                """MERGE (o:Object {id: $oid}) SET o.name = $name
                   WITH o
                   MATCH (c:Category {id: $cid})
                   MERGE (c)-[:HAS_OBJECT]->(o)""",
                oid=object_id, name=name, cid=category_id,
            )

    def upsert_morphism(
        self,
        morphism_id: str,
        name: str,
        category_id: str,
        source_id: str,
        target_id: str,
    ) -> None:
        with self.connect().session() as s:
            s.run(
                """MERGE (m:Morphism {id: $mid}) SET m.name = $name
                   WITH m
                   MATCH (c:Category {id: $cid})
                   MERGE (c)-[:HAS_MORPHISM]->(m)
                   WITH m
                   MATCH (src:Object {id: $sid})
                   MATCH (tgt:Object {id: $tid})
                   MERGE (m)-[:FROM]->(src)
                   MERGE (m)-[:TO]->(tgt)""",
                mid=morphism_id, name=name, cid=category_id,
                sid=source_id, tid=target_id,
            )

    def upsert_functor(
        self, functor_id: str, name: str, source_category_id: str, target_category_id: str
    ) -> None:
        with self.connect().session() as s:
            s.run(
                """MERGE (f:Functor {id: $fid}) SET f.name = $name
                   WITH f
                   MATCH (src:Category {id: $sid})
                   MATCH (tgt:Category {id: $tid})
                   MERGE (f)-[:SOURCE_CATEGORY]->(src)
                   MERGE (f)-[:TARGET_CATEGORY]->(tgt)""",
                fid=functor_id, name=name,
                sid=source_category_id, tid=target_category_id,
            )

    def record_violation(
        self,
        violation_id: str,
        functor_id: str,
        law: str,
        details: Dict[str, Any],
        detected_at: str,
    ) -> None:
        with self.connect().session() as s:
            s.run(
                """MERGE (v:FunctorLawViolation {id: $vid})
                   SET v.law = $law, v.details = $details, v.detected_at = datetime($ts)
                   WITH v
                   MATCH (f:Functor {id: $fid})
                   MERGE (f)-[:HAS_VIOLATION]->(v)""",
                vid=violation_id, fid=functor_id, law=law,
                details=str(details), ts=detected_at,
            )

    def upsert_path_signature(
        self,
        path_id: str,
        address_hash: str,
        proof_hash: str,
        chain: List[str],
        start_obj: str,
        end_obj: str,
    ) -> None:
        with self.connect().session() as s:
            s.run(
                """MERGE (p:PathSignature {id: $pid})
                   SET p.address_hash = $ah, p.proof_hash = $ph,
                       p.chain = $chain
                   WITH p
                   MATCH (src:Object {id: $sid})
                   MATCH (tgt:Object {id: $tid})
                   MERGE (p)-[:STARTS_AT]->(src)
                   MERGE (p)-[:ENDS_AT]->(tgt)""",
                pid=path_id, ah=address_hash, ph=proof_hash,
                chain=chain, sid=start_obj, tid=end_obj,
            )

    def find_similar_paths(self, address_hash: str, k: int = 10) -> List[Dict[str, Any]]:
        """Placeholder for semantic routing (Phase 1+)."""
        with self.connect().session() as s:
            result = s.run(
                """MATCH (p:PathSignature {address_hash: $ah})
                   MATCH (p)-[:STARTS_AT|ENDS_AT*1..2]-(n)
                   RETURN DISTINCT n.id AS neighbor LIMIT $k""",
                ah=address_hash, k=k,
            )
            return [dict(r) for r in result]
