#!/usr/bin/env bash
# Apply Neo4j constraints.
set -euo pipefail

NEO4J_URI="${NEO4J_URI:-bolt://localhost:7687}"
NEO4J_USER="${NEO4J_USER:-neo4j}"
NEO4J_PASS="${NEO4J_PASS:-qbx-test-password}"

if ! command -v cypher-shell >/dev/null 2>&1; then
  echo "cypher-shell not found; install Neo4j or run constraints.cql manually"
  exit 1
fi

echo "Applying Neo4j constraints..."
cypher-shell -a "$NEO4J_URI" -u "$NEO4J_USER" -p "$NEO4J_PASS" \
  -f neo4j/constraints.cql

echo "Constraints applied."