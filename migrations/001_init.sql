-- ============================================================================
-- QBX Phase 0 — Migration 001: Core categorical schema
-- ============================================================================

CREATE EXTENSION IF NOT EXISTS pgcrypto;
CREATE EXTENSION IF NOT EXISTS vector;

---

-- Universe registry

---

CREATE TABLE IF NOT EXISTS universe_registry (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
name TEXT NOT NULL UNIQUE,
level INT NOT NULL,
description TEXT,
metadata JSONB DEFAULT '{}'::jsonb,
created_at TIMESTAMPTZ DEFAULT now()
);

---

-- Category / Object / Morphism

---

CREATE TABLE IF NOT EXISTS category (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
name TEXT NOT NULL UNIQUE,
description TEXT,
metadata JSONB DEFAULT '{}'::jsonb,
created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS object (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
name TEXT NOT NULL,
universe_id UUID REFERENCES universe_registry(id),
data JSONB DEFAULT '{}'::jsonb,
UNIQUE (category_id, name)
);

CREATE TABLE IF NOT EXISTS morphism (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
source_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
target_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
name TEXT,
law_type TEXT DEFAULT 'general',
data JSONB DEFAULT '{}'::jsonb,
resource_bounds JSONB DEFAULT '{}'::jsonb,
created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_morphism_cat_src_tgt
ON morphism (category_id, source_id, target_id);

CREATE TABLE IF NOT EXISTS identity_morphism (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
UNIQUE (category_id, object_id)
);

CREATE TABLE IF NOT EXISTS composition (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
left_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
right_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
result_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
proof_hash TEXT,
witness JSONB DEFAULT '{}'::jsonb,
-- Amendment A-003: one result per composable pair; f ∘ f is allowed
-- (the former CHECK (left_id <> right_id) forbade it).
CONSTRAINT composition_pair_unique UNIQUE (left_id, right_id)
);

CREATE INDEX IF NOT EXISTS idx_composition_cat ON composition (category_id);

-- Amendment A-003: composition rows must be well typed.
-- Convention: composition(left_id = g, right_id = f, result_id = h) records
-- h = g ∘ f (f applied first), so it requires
--   target(f) = source(g),  source(h) = source(f),  target(h) = target(g),
-- and all three morphisms in category_id.  This is a structural constraint
-- (like a CHECK), so it raises in every enforcement mode.
CREATE OR REPLACE FUNCTION composition_check_typing() RETURNS trigger AS $$
DECLARE
g RECORD;
f RECORD;
h RECORD;
BEGIN
SELECT category_id, source_id, target_id INTO g FROM morphism WHERE id = NEW.left_id;
SELECT category_id, source_id, target_id INTO f FROM morphism WHERE id = NEW.right_id;
SELECT category_id, source_id, target_id INTO h FROM morphism WHERE id = NEW.result_id;
IF g.category_id <> NEW.category_id OR f.category_id <> NEW.category_id
OR h.category_id <> NEW.category_id THEN
RAISE EXCEPTION 'composition %: morphisms are not all in category %',
NEW.id, NEW.category_id;
END IF;
IF f.target_id <> g.source_id THEN
RAISE EXCEPTION 'composition %: target(right) <> source(left), not composable', NEW.id;
END IF;
IF h.source_id <> f.source_id OR h.target_id <> g.target_id THEN
RAISE EXCEPTION 'composition %: result must go from source(right) to target(left)', NEW.id;
END IF;
RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_composition_typing ON composition;
CREATE TRIGGER trg_composition_typing
BEFORE INSERT OR UPDATE ON composition
FOR EACH ROW EXECUTE FUNCTION composition_check_typing();

---

-- Functors

---

CREATE TABLE IF NOT EXISTS functor (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
name TEXT NOT NULL UNIQUE,
source_category_id UUID NOT NULL REFERENCES category(id),
target_category_id UUID NOT NULL REFERENCES category(id),
metadata JSONB DEFAULT '{}'::jsonb,
created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS functor_object_map (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
functor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
source_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
target_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
UNIQUE (functor_id, source_object_id)
);

CREATE TABLE IF NOT EXISTS functor_morphism_map (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
functor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
source_morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
target_morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
UNIQUE (functor_id, source_morphism_id)
);

---

-- Diagnostics

---

CREATE TABLE IF NOT EXISTS functor_law_violation (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
functor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
law TEXT NOT NULL,
source_morphism_id UUID,
target_morphism_id UUID,
details JSONB DEFAULT '{}'::jsonb,
detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_functor_law_violation_functor
ON functor_law_violation (functor_id, detected_at DESC);

---

-- Path signatures

---

CREATE TABLE IF NOT EXISTS path_signature (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
start_object_id UUID NOT NULL REFERENCES object(id),
end_object_id UUID NOT NULL REFERENCES object(id),
morphism_chain UUID[] NOT NULL,
canonical_bytes BYTEA NOT NULL,
proof_hash TEXT NOT NULL,
hash_algo TEXT NOT NULL DEFAULT 'SHA3-256',
address_hash TEXT NOT NULL,
metadata JSONB DEFAULT '{}'::jsonb,
created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_path_signature_address ON path_signature (address_hash);
CREATE INDEX IF NOT EXISTS idx_path_signature_proof ON path_signature (proof_hash);

---

-- Proof artifacts (Phase 0 stub)

---

CREATE TABLE IF NOT EXISTS proof_artifact (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
artifact_type TEXT NOT NULL,
payload_uri TEXT,
payload_hash TEXT NOT NULL,
hash_algo TEXT NOT NULL DEFAULT 'SHA3-256',
signature BYTEA,
signer_key_id TEXT,
metadata JSONB DEFAULT '{}'::jsonb,
created_at TIMESTAMPTZ DEFAULT now()
);

---

-- Capability tokens (Phase 0 stub)

---

CREATE TABLE IF NOT EXISTS capability_token (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
token TEXT NOT NULL UNIQUE,
owner TEXT,
scopes TEXT[] DEFAULT ARRAY[]::text[],
expires_at TIMESTAMPTZ,
signature BYTEA,
created_at TIMESTAMPTZ DEFAULT now(),
metadata JSONB DEFAULT '{}'::jsonb
);

-- Amendment A-001: a partial index may not use now() (not IMMUTABLE), so the
-- expiry test belongs in the query; (token, expires_at) serves it.
CREATE INDEX IF NOT EXISTS idx_capability_token_active
ON capability_token (token, expires_at);

---

-- Embeddings (pgvector, for Phase 1+)

---

CREATE TABLE IF NOT EXISTS embedding (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
artifact_id UUID,
vector vector(1536),
model_name TEXT NOT NULL,
created_at TIMESTAMPTZ DEFAULT now(),
metadata JSONB DEFAULT '{}'::jsonb
);

-- NOTE: ivfflat index should be created after bulk load, not here.