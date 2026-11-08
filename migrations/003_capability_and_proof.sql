-- ============================================================================
-- QBX Phase 0 — Migration 003: Capability + proof enforcement
-- ============================================================================

-- ---------------------------------------------------------------------------
-- Capability enforcement: production writes require a valid token.
--
-- Amendment A-004 (approved under question Q-005, option 1): the original
-- body declared a variable `token` and queried `WHERE token = token`, which
-- PostgreSQL rejects as an ambiguous column reference, so every production
-- write was refused even with a valid token.  The check now delegates to
-- `capability_token_is_active` (migration 018), which also applies the Q-001
-- policy: the token must be stored, carry an expiry that has not passed, and
-- not be revoked.  PL/pgSQL resolves the call when the trigger runs; if 018 is
-- not installed the call fails and the write is refused (fail closed).
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION enforce_capability_token() RETURNS trigger AS $$
BEGIN
  -- Only enforce when metadata->>'zone' = 'production'
  IF NEW.metadata ? 'zone' AND NEW.metadata->>'zone' = 'production' THEN
    IF NOT (NEW.metadata ? 'capability_token')
       OR NOT capability_token_is_active(NEW.metadata->>'capability_token') THEN
      RAISE EXCEPTION 'Production write requires a valid capability token';
    END IF;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

-- Apply this trigger to the artifact table only if it exists (Phase 1+).
-- For Phase 0, we expose the function so downstream migrations can attach it.

-- ---------------------------------------------------------------------------
-- Helper function: compute path signature proof hash (server-side sanity check).
-- NOTE: In production, the hash is computed in Python and stored; this is a
-- diagnostic helper only.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION compute_proof_hash_placeholder(canonical_bytes BYTEA)
RETURNS TEXT AS $$
BEGIN
  -- Placeholder: real implementation should call a PQ-hash extension.
  -- For now, use built-in sha256 as a stand-in.
  RETURN encode(digest(canonical_bytes, 'sha256'), 'hex');
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Helper: count violations per functor (for monitoring).
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION count_functor_violations()
RETURNS TABLE(functor_id UUID, violation_count BIGINT) AS $$
BEGIN
  RETURN QUERY
  SELECT flv.functor_id, COUNT(*)::BIGINT
  FROM functor_law_violation flv
  GROUP BY flv.functor_id
  ORDER BY COUNT(*) DESC;
END;
$$ LANGUAGE plpgsql;