#!/usr/bin/env bash
# Run QBX Phase 0 SQL migrations in order.
set -euo pipefail

PG_DSN="${PG_DSN:-postgresql://postgres:postgres@localhost:5432/qbx}"

echo "Running QBX Phase 0 migrations against: $PG_DSN"
for f in migrations/001_init.sql migrations/002_enforced_functor.sql migrations/003_capability_and_proof.sql; do
  echo "  → $f"
  psql "$PG_DSN" -f "$f"
done

echo "Applying Neo4j constraints..."
if command -v cypher-shell >/dev/null 2>&1; then
  cypher-shell -a "${NEO4J_URI:-bolt://localhost:7687}" \
               -u "${NEO4J_USER:-neo4j}" \
               -p "${NEO4J_PASS:-qbx-test-password}" \
               -f neo4j/constraints.cql
else
  echo "  (cypher-shell not found; run neo4j/constraints.cql manually)"
fi

echo "Migrations complete."