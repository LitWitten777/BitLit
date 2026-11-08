#!/usr/bin/env bash
# Run the SQL test suite.
set -euo pipefail

PG_DSN="${PG_DSN:-postgresql://postgres:postgres@localhost:5432/qbx}"

echo "Running SQL tests against: $PG_DSN"
psql "$PG_DSN" -f tests/test_triggers.sql