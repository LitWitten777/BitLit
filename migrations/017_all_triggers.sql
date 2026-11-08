-- ============================================================================
-- Categorical Ledger — Migration 017: Unified Trigger Layer
-- ============================================================================
-- This migration installs:
--   * a central `invariant_violation` table
--   * a helper `qbx_is_strict()` function
--   * a trigger helper `qbx_record_violation(...)`
--   * strict-mode toggling helpers
--
-- It also documents the enforcement mode convention used across all
-- triggers in migrations 002–016.
-- ============================================================================

-- ---------------------------------------------------------------------------
-- Central invariant violation log (used by non-categorical subsystems).
-- ---------------------------------------------------------------------------
CREATE TABLE IF NOT EXISTS invariant_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  module TEXT NOT NULL,
  object_id UUID,
  artifact_id UUID,
  violation_type TEXT NOT NULL,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_invariant_violation_module
  ON invariant_violation (module, detected_at DESC);

-- ---------------------------------------------------------------------------
-- Enforcement mode helper.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION qbx_is_strict() RETURNS BOOLEAN AS $$
BEGIN
  RETURN coalesce(current_setting('qbx.enforcement_mode', true), 'permissive') = 'strict';
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Toggle helpers (session-local).
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION qbx_set_strict() RETURNS VOID AS $$
BEGIN
  PERFORM set_config('qbx.enforcement_mode', 'strict', false);
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION qbx_set_permissive() RETURNS VOID AS $$
BEGIN
  PERFORM set_config('qbx.enforcement_mode', 'permissive', false);
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Central violation recorder.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION qbx_record_violation(
  p_module TEXT, p_type TEXT, p_details JSONB,
  p_object_id UUID DEFAULT NULL, p_artifact_id UUID DEFAULT NULL
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  INSERT INTO invariant_violation
    (module, object_id, artifact_id, violation_type, details)
  VALUES
    (p_module, p_object_id, p_artifact_id, p_type, p_details)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Summary view: all violations across subsystems.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE VIEW v_all_violations AS
  SELECT 'functor_identity'       AS module, id, functor_id AS subject, law AS violation_type, details, detected_at FROM functor_law_violation
  UNION ALL
  SELECT 'naturality'             AS module, id, transformation_id, law, details, detected_at FROM naturality_violation
  UNION ALL
  SELECT 'adjunction'             AS module, id, adjunction_id, law, details, detected_at FROM adjunction_violation
  UNION ALL
  SELECT 'monad'                  AS module, id, monad_id, law, details, detected_at FROM monad_violation
  UNION ALL
  SELECT 'comonad'                AS module, id, comonad_id, law, details, detected_at FROM comonad_violation
  UNION ALL
  SELECT 'limit'                  AS module, id, diagram_id, reason, details, detected_at FROM limit_violation
  UNION ALL
  SELECT 'colimit'                AS module, id, diagram_id, reason, details, detected_at FROM colimit_violation
  UNION ALL
  SELECT 'enriched'               AS module, id, enriched_category_id, reason, details, detected_at FROM enriched_violation
  UNION ALL
  SELECT 'two_category'           AS module, id, two_category_id, violation_type, details, detected_at FROM two_category_coherence_violation
  UNION ALL
  SELECT 'fibration'              AS module, id, fibration_id, reason, details, detected_at FROM fibration_violation
  UNION ALL
  SELECT 'topos'                  AS module, id, category_id, reason, details, detected_at FROM topos_violation
  UNION ALL
  SELECT 'sheaf_cohomology'       AS module, id, site_id, coalesce(reason, 'obstruction'), details, detected_at FROM sheaf_cohomology_obstruction
  UNION ALL
  SELECT 'addressing'             AS module, id, subject_id, reason, details, detected_at FROM address_violation
  UNION ALL
  SELECT 'hebrew'                 AS module, id, subject_id, reason, details, detected_at FROM hebrew_violation
  UNION ALL
  SELECT 'governance'             AS module, id, subject_id, reason, details, detected_at FROM governance_violation
  UNION ALL
  SELECT 'empirical'              AS module, id, subject_id, reason, details, detected_at FROM empirical_violation
  UNION ALL
  SELECT 'invariant'              AS module, id, object_id, violation_type, details, detected_at FROM invariant_violation;

-- ---------------------------------------------------------------------------
-- Summary function: count violations per module.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION violation_summary()
RETURNS TABLE(module TEXT, count BIGINT) AS $$
BEGIN
  RETURN QUERY
  SELECT v.module, COUNT(*)::BIGINT
    FROM v_all_violations v
   GROUP BY v.module
   ORDER BY COUNT(*) DESC;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Batch checkers: run all heavy checks in one call.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION run_all_batch_checks() RETURNS VOID AS $$
DECLARE
  m RECORD;
  c RECORD;
  adj RECORD;
  t RECORD;
BEGIN
  -- All functors (identity and composition laws; migration 002, amendment A-002)
  FOR t IN SELECT id FROM functor LOOP
    PERFORM check_functor_laws(t.id);
  END LOOP;

  -- All natural transformations (re-walk every naturality square; migration 004)
  FOR t IN SELECT id FROM natural_transformation LOOP
    PERFORM recheck_naturality(t.id);
  END LOOP;

  -- All monads
  FOR m IN SELECT id FROM monad LOOP
    PERFORM check_monad_laws(m.id);
  END LOOP;

  -- All comonads
  FOR c IN SELECT id FROM comonad LOOP
    PERFORM check_comonad_laws(c.id);
  END LOOP;

  -- All adjunctions
  FOR adj IN SELECT id FROM adjunction LOOP
    PERFORM check_adjunction_triangles(adj.id);
  END LOOP;

  -- All limits and colimits (universality among the recorded data; migration 007)
  FOR t IN SELECT id FROM "limit" LOOP
    PERFORM verify_limit_universality(t.id);
  END LOOP;
  FOR t IN SELECT id FROM colimit LOOP
    PERFORM verify_colimit_universality(t.id);
  END LOOP;

  -- All enriched categories (unit / composition laws, kernel laws; migration 008)
  FOR t IN SELECT id FROM enriched_category LOOP
    PERFORM check_enriched_category(t.id);
  END LOOP;

  -- All 2-categories (typing, unit, associativity, interchange; migration 009)
  FOR t IN SELECT id FROM two_category LOOP
    PERFORM check_two_category(t.id);
  END LOOP;

  -- All fibrations / opfibrations (lift typing, (co)cartesian property,
  -- existence of lifts; migration 010)
  FOR t IN SELECT id FROM fibration LOOP
    PERFORM check_fibration(t.id);
  END LOOP;

  -- All subobject classifiers (typing, terminal object, pullback squares,
  -- existence and uniqueness of characteristic morphisms; migration 011)
  FOR t IN SELECT id FROM subobject_classifier LOOP
    PERFORM check_subobject_classifier(t.id);
  END LOOP;

  -- All finite sites (topology, covers) and presheaves (typing, functoriality,
  -- the sheaf condition on the registered covers, H⁰ descriptors; migration 012)
  FOR t IN SELECT id FROM site LOOP
    PERFORM check_site(t.id);
  END LOOP;
  FOR t IN SELECT id FROM presheaf LOOP
    PERFORM check_sheaf_condition(t.id);
  END LOOP;

  -- All addressing rows (AddressV2 hash, CBOR and schema, trust hint, pointers;
  -- cache entries, gateways, DHT nodes, discovery log; migration 013)
  PERFORM check_addressing();

  -- All Hebrew rows (letter table against the seed, words, gematria functors
  -- and their naturality obligations, Torah sites as sheaves and their
  -- sections, language adjunctions; migration 014)
  PERFORM check_hebrew();

  -- All governance rows (modality table against the seed, modality backings,
  -- policies, assignments, policy checks recomputed, approval workflows and
  -- tokens with their order, audit records), both frames (alethic reflexive
  -- and transitive, deontic serial) and the audit hash chain; migration 015)
  PERFORM check_governance();

  -- All empirical rows (uncertainty types, measurement contracts, bundles
  -- with their validated flag, validations recomputed, dynamical models,
  -- simulation runs, agent models, mechanisms with their incentive claims;
  -- migration 016)
  PERFORM check_empirical();

  RAISE NOTICE 'run_all_batch_checks: complete';
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Documentation: enforcement mode convention.
-- ---------------------------------------------------------------------------
COMMENT ON FUNCTION qbx_is_strict() IS
  'Returns true if qbx.enforcement_mode = ''strict''. All *row-level*
   triggers should raise on violation when this returns true; otherwise
   they should log to the corresponding *_violation table and continue.';

COMMENT ON TABLE invariant_violation IS
  'Central log for violations from non-categorical subsystems
   (measurement, policy, provenance, etc.). Categorical subsystems have
   their own dedicated violation tables.';