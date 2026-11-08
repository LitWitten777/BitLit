-- ============================================================================
-- QBX Phase 1 — Migration 018: Capability revocation list (decision Q-001)
-- ============================================================================
-- Q-001 chose signed capability blobs with a revocation list (option 2).
-- Tokens are signed and verified in Python (`qbx.core.capability`); the
-- database stores issued tokens (`capability_token`, migration 001) and the
-- revocation list (this migration), and answers "is this token active?".
--
-- Conventions for a signed token stored in `capability_token`:
--   token                 = the full `qbxcap1.<claims>.<signature>` string
--   metadata->>'token_id' = the token_id claim (the revocation key)
--   scopes, expires_at    = copied from the claims
--
-- The frozen trigger function `enforce_capability_token()` (migration 003)
-- delegates to `capability_token_is_active` below (amendment A-004, applied).
-- It checks a token without a scope; `enforce_signed_capability()` below also
-- checks the scope given as a trigger argument, and is the one to attach to
-- Phase 1 tables.
--
-- Reference: qbx.core.capability.CapabilityVerifier.  The database cannot
-- verify signatures; for a stored qbxcap1 token it agrees with the reference
-- on everything else (validity window not_before <= t < expires_at, scope,
-- revocation); tests/live_db/test_capability_db.py compares the two on random
-- tokens.
--
-- Phase 1 sprint 14 (acceptance review).  Running the earlier version on
-- PostgreSQL 16 showed:
--   * register_signed_capability stored whatever token_id, owner, scopes and
--     expiry the caller passed, without looking at the token: a token issued
--     for 'weyl:expand' with a 100-second lifetime could be registered with
--     scope '*' and an expiry a million seconds later, and was then active for
--     every scope; registered under another token_id, revoking its real
--     token_id did not revoke it;
--   * not_before was ignored: a token was active before it became valid.
-- register_signed_capability now decodes the claims (capability_claims) and
-- refuses a token that is not a well-formed qbxcap1 token or whose claims
-- differ from the arguments; it records not_before, and
-- capability_token_is_active checks it.
-- ============================================================================

CREATE TABLE IF NOT EXISTS capability_revocation (
  token_id TEXT PRIMARY KEY,
  reason TEXT,
  revoked_by TEXT,
  revoked_at TIMESTAMPTZ NOT NULL DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_capability_token_token_id
  ON capability_token ((metadata->>'token_id'));

-- ---------------------------------------------------------------------------
-- The claims object of a qbxcap1 token (base64url, unpadded, JSON), or NULL
-- when the token is not of the form qbxcap1.<claims>.<signature> with a JSON
-- object as claims.  Nothing is verified.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION capability_claims(p_token TEXT) RETURNS JSONB AS $$
DECLARE
  v_parts TEXT[];
  v_body TEXT;
  v_claims JSONB;
BEGIN
  v_parts := string_to_array(p_token, '.');
  IF v_parts IS NULL OR cardinality(v_parts) <> 3 OR v_parts[1] <> 'qbxcap1'
     OR v_parts[2] !~ '^[A-Za-z0-9_-]+$' THEN
    RETURN NULL;
  END IF;
  v_body := translate(v_parts[2], '-_', '+/');
  v_body := v_body || repeat('=', (4 - length(v_body) % 4) % 4);
  v_claims := convert_from(decode(v_body, 'base64'), 'UTF8')::jsonb;
  IF jsonb_typeof(v_claims) <> 'object' THEN
    RETURN NULL;
  END IF;
  RETURN v_claims;
EXCEPTION WHEN others THEN
  RETURN NULL;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- A token is active at time p_at for scope p_scope iff it is stored, it has
-- not expired (tokens with no expiry are not accepted: Q-001 requires one),
-- it has become valid (metadata.not_before <= p_at, in whole UNIX seconds, when
-- recorded), it grants the scope (or '*', or no scope was asked for), and its
-- token_id is not revoked.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION capability_token_is_active(
  p_token TEXT, p_scope TEXT DEFAULT NULL, p_at TIMESTAMPTZ DEFAULT now()
) RETURNS BOOLEAN AS $$
  SELECT EXISTS (
    SELECT 1 FROM capability_token ct
     WHERE ct.token = p_token
       AND ct.expires_at IS NOT NULL
       AND ct.expires_at > p_at
       AND (NOT (ct.metadata ? 'not_before')
            OR (jsonb_typeof(ct.metadata->'not_before') = 'number'
                AND (ct.metadata->>'not_before')::numeric <= floor(extract(epoch FROM p_at))))
       AND (p_scope IS NULL OR p_scope = ANY (ct.scopes) OR '*' = ANY (ct.scopes))
       AND NOT EXISTS (
         SELECT 1 FROM capability_revocation r
          WHERE r.token_id = ct.metadata->>'token_id'
       )
  );
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Record a signed token (signature already verified in Python).  The token_id,
-- owner (the subject claim), scopes (as a set) and expiry passed must be the
-- token's own claims; the token is refused otherwise, in every mode.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION register_signed_capability(
  p_token TEXT, p_token_id TEXT, p_owner TEXT, p_scopes TEXT[],
  p_expires_at TIMESTAMPTZ
) RETURNS UUID AS $$
DECLARE
  new_id UUID;
  c JSONB;
BEGIN
  IF p_token_id IS NULL OR p_token_id = '' THEN
    RAISE EXCEPTION 'A signed capability needs a token_id';
  END IF;
  IF p_expires_at IS NULL THEN
    RAISE EXCEPTION 'A signed capability needs an expiry';
  END IF;
  c := capability_claims(p_token);
  IF c IS NULL
     OR jsonb_typeof(c->'token_id') IS DISTINCT FROM 'string'
     OR jsonb_typeof(c->'subject') IS DISTINCT FROM 'string'
     OR jsonb_typeof(c->'scopes') IS DISTINCT FROM 'array'
     OR jsonb_typeof(c->'expires_at') IS DISTINCT FROM 'number'
     OR jsonb_typeof(c->'not_before') IS DISTINCT FROM 'number'
     OR EXISTS (SELECT 1 FROM jsonb_array_elements(c->'scopes') e
                 WHERE jsonb_typeof(e) <> 'string') THEN
    RAISE EXCEPTION 'register_signed_capability: not a well-formed qbxcap1 token';
  END IF;
  IF c->>'token_id' <> p_token_id
     OR c->>'subject' IS DISTINCT FROM p_owner
     OR (c->>'expires_at')::numeric <> extract(epoch FROM p_expires_at)
     OR ARRAY(SELECT DISTINCT e FROM jsonb_array_elements_text(c->'scopes') e ORDER BY e)
        <> ARRAY(SELECT DISTINCT s FROM unnest(coalesce(p_scopes, ARRAY[]::text[])) s ORDER BY s) THEN
    RAISE EXCEPTION 'register_signed_capability: the arguments differ from the token''s claims';
  END IF;
  INSERT INTO capability_token (token, owner, scopes, expires_at, metadata)
  VALUES (p_token, p_owner, coalesce(p_scopes, ARRAY[]::text[]), p_expires_at,
          jsonb_build_object('token_id', p_token_id, 'format', 'qbxcap1',
                             'not_before', c->'not_before'))
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION revoke_capability(
  p_token_id TEXT, p_reason TEXT DEFAULT NULL, p_by TEXT DEFAULT NULL
) RETURNS VOID AS $$
BEGIN
  INSERT INTO capability_revocation (token_id, reason, revoked_by)
  VALUES (p_token_id, p_reason, p_by)
  ON CONFLICT (token_id) DO NOTHING;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Trigger function for tables with a `metadata` JSONB column: rows with
-- metadata.zone = 'production' must carry an active token whose scope
-- includes the scope given as the first trigger argument (default 'ledger:write').
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION enforce_signed_capability() RETURNS trigger AS $$
DECLARE
  v_scope TEXT := coalesce(TG_ARGV[0], 'ledger:write');
BEGIN
  IF NEW.metadata ? 'zone' AND NEW.metadata->>'zone' = 'production' THEN
    IF NOT (NEW.metadata ? 'capability_token')
       OR NOT capability_token_is_active(NEW.metadata->>'capability_token', v_scope) THEN
      RAISE EXCEPTION 'Production write requires an active capability token with scope %', v_scope;
    END IF;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;
