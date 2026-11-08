#!/usr/bin/env bash
# Run all Categorical Ledger migrations in order.
set -euo pipefail

PG_DSN="${PG_DSN:-postgresql://postgres:postgres@localhost:5432/qbx}"

echo "Running Categorical Ledger migrations against: $PG_DSN"
for f in \
  migrations/001_init.sql \
  migrations/002_enforced_functor.sql \
  migrations/003_capability_and_proof.sql \
  migrations/004_natural_transformations.sql \
  migrations/005_adjunctions.sql \
  migrations/006_monad_comonad.sql \
  migrations/007_limits_colimits.sql \
  migrations/008_enriched_categories.sql \
  migrations/009_two_categories.sql \
  migrations/010_fibrations.sql \
  migrations/011_topos_kernel.sql \
  migrations/012_sheaf_cohomology.sql \
  migrations/013_addressing_protocol.sql \
  migrations/014_hebrew_primacy.sql \
  migrations/015_governance_modalities.sql \
  migrations/016_empirical_grounding.sql \
  migrations/017_all_triggers.sql \
  migrations/018_capability_revocation.sql \
  migrations/019_braid_ledger.sql \
  migrations/020_braid_invariants.sql \
  migrations/021_braid_normal_forms.sql \
  migrations/022_braid_representations.sql \
; do
  echo "  → $f"
  psql "$PG_DSN" -v ON_ERROR_STOP=1 -f "$f"
done

echo "All migrations applied."