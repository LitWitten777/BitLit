-- ============================================================================
-- QBX Phase 0 — Migration 002: Functor law enforcement
-- ============================================================================

---

-- Helper view: identity morphisms

---

CREATE OR REPLACE VIEW v_identity_morphisms AS
SELECT im.category_id, im.object_id, im.morphism_id
FROM identity_morphism im;

-- ---------------------------------------------------------------------------
-- Amendment A-002 (approved): enforcement mode, unit laws, complete
-- incremental checking.  Violations are always logged to
-- functor_law_violation; the triggers raise only when
-- qbx.enforcement_mode = 'strict' (same test as qbx_is_strict() in 017).
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION functor_is_strict() RETURNS BOOLEAN AS $$
SELECT coalesce(current_setting('qbx.enforcement_mode', true), 'permissive') = 'strict';
$$ LANGUAGE sql STABLE;

-- qbx_compose(first, second) = second ∘ first (first applied first), applying
-- the unit laws id ∘ m = m = m ∘ id; otherwise looked up in `composition`
-- (unique per pair, amendment A-003).  NULL if the composite is not recorded.
CREATE OR REPLACE FUNCTION qbx_compose(p_first UUID, p_second UUID)
RETURNS UUID AS $$
DECLARE
res UUID;
BEGIN
IF EXISTS (SELECT 1 FROM identity_morphism WHERE morphism_id = p_first) THEN
RETURN p_second;
END IF;
IF EXISTS (SELECT 1 FROM identity_morphism WHERE morphism_id = p_second) THEN
RETURN p_first;
END IF;
SELECT result_id INTO res
FROM composition
WHERE left_id = p_second
AND right_id = p_first;
RETURN res;
END;
$$ LANGUAGE plpgsql STABLE;

---

-- Identity law: F(id_X) = id_{F(X)}

---

-- Checks one morphism-map row; logs and returns FALSE on a violation.
CREATE OR REPLACE FUNCTION functor_check_identity_row(
p_functor_id UUID, p_source_morphism UUID, p_target_morphism UUID)
RETURNS BOOLEAN AS $$
DECLARE
src_identity RECORD;
mapped_object UUID;
BEGIN
SELECT * INTO src_identity
FROM v_identity_morphisms
WHERE morphism_id = p_source_morphism
LIMIT 1;

IF NOT FOUND THEN
RETURN TRUE;  -- not an identity, nothing to check
END IF;

SELECT target_object_id INTO mapped_object
FROM functor_object_map
WHERE functor_id = p_functor_id
AND source_object_id = src_identity.object_id;

IF NOT FOUND THEN
INSERT INTO functor_law_violation
(functor_id, law, source_morphism_id, target_morphism_id, details)
VALUES
(p_functor_id, 'identity_missing_object_map',
p_source_morphism, p_target_morphism,
jsonb_build_object('object_id', src_identity.object_id));
RETURN FALSE;
END IF;

IF NOT EXISTS (
SELECT 1 FROM v_identity_morphisms
WHERE morphism_id = p_target_morphism
AND object_id = mapped_object) THEN
INSERT INTO functor_law_violation
(functor_id, law, source_morphism_id, target_morphism_id, details)
VALUES
(p_functor_id, 'identity',
p_source_morphism, p_target_morphism,
jsonb_build_object(
'source_object_id', src_identity.object_id,
'mapped_object_id', mapped_object
));
RETURN FALSE;
END IF;

RETURN TRUE;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION functor_check_identity_law() RETURNS trigger AS $$
BEGIN
IF NOT functor_check_identity_row(NEW.functor_id, NEW.source_morphism_id,
NEW.target_morphism_id)
AND functor_is_strict() THEN
RAISE EXCEPTION 'Functor identity law violated for functor %', NEW.functor_id;
END IF;
RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_functor_identity_law ON functor_morphism_map;
CREATE TRIGGER trg_functor_identity_law
AFTER INSERT OR UPDATE ON functor_morphism_map
FOR EACH ROW EXECUTE FUNCTION functor_check_identity_law();

-- ---------------------------------------------------------------------------
-- Composition law: F(g ∘ f) = F(g) ∘ F(f)
-- ---------------------------------------------------------------------------
-- Checks one recorded composition h = g ∘ f under functor F once F(f), F(g)
-- and F(h) are all mapped; returns TRUE when the law holds or cannot be
-- checked yet, and logs and returns FALSE on a violation.
CREATE OR REPLACE FUNCTION functor_check_composition_row(
p_functor_id UUID, p_composition_id UUID)
RETURNS BOOLEAN AS $$
DECLARE
comp RECORD;
mapped_left UUID;
mapped_right UUID;
mapped_result UUID;
expected UUID;
BEGIN
SELECT * INTO comp FROM composition WHERE id = p_composition_id;
IF NOT FOUND THEN
RETURN TRUE;
END IF;

SELECT target_morphism_id INTO mapped_left FROM functor_morphism_map
WHERE functor_id = p_functor_id AND source_morphism_id = comp.left_id;
SELECT target_morphism_id INTO mapped_right FROM functor_morphism_map
WHERE functor_id = p_functor_id AND source_morphism_id = comp.right_id;
SELECT target_morphism_id INTO mapped_result FROM functor_morphism_map
WHERE functor_id = p_functor_id AND source_morphism_id = comp.result_id;

IF mapped_left IS NULL OR mapped_right IS NULL OR mapped_result IS NULL THEN
RETURN TRUE;  -- checked when the last of the three maps is inserted
END IF;

-- F(g) ∘ F(f): F(f) first
expected := qbx_compose(mapped_right, mapped_left);

IF expected IS NULL OR expected <> mapped_result THEN
INSERT INTO functor_law_violation
(functor_id, law, source_morphism_id, target_morphism_id, details)
VALUES
(p_functor_id,
CASE WHEN expected IS NULL THEN 'composition_composite_missing'
ELSE 'composition' END,
comp.result_id, mapped_result,
jsonb_build_object(
'composition_id', comp.id,
'left_id', comp.left_id,
'right_id', comp.right_id,
'mapped_left', mapped_left,
'mapped_right', mapped_right,
'expected', expected
));
RETURN FALSE;
END IF;

RETURN TRUE;
END;
$$ LANGUAGE plpgsql;

-- Row trigger: re-check every recorded composition in which the newly mapped
-- morphism is the result OR a factor, over all factorizations (no LIMIT 1),
-- so the outcome does not depend on the order in which maps are inserted.
CREATE OR REPLACE FUNCTION functor_check_composition_law() RETURNS trigger AS $$
DECLARE
c RECORD;
ok BOOLEAN := TRUE;
BEGIN
FOR c IN
SELECT id FROM composition
WHERE NEW.source_morphism_id IN (left_id, right_id, result_id)
LOOP
IF NOT functor_check_composition_row(NEW.functor_id, c.id) THEN
ok := FALSE;
END IF;
END LOOP;

IF NOT ok AND functor_is_strict() THEN
RAISE EXCEPTION 'Functor composition law violated for functor %', NEW.functor_id;
END IF;

RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_functor_composition_law ON functor_morphism_map;
CREATE TRIGGER trg_functor_composition_law
AFTER INSERT OR UPDATE ON functor_morphism_map
FOR EACH ROW EXECUTE FUNCTION functor_check_composition_law();

-- Batch re-check of one functor (e.g. after compositions were recorded later
-- than the maps).  Logs every violation, never raises; returns their number.
CREATE OR REPLACE FUNCTION check_functor_laws(p_functor_id UUID)
RETURNS INT AS $$
DECLARE
r RECORD;
n INT := 0;
BEGIN
FOR r IN
SELECT source_morphism_id, target_morphism_id
FROM functor_morphism_map WHERE functor_id = p_functor_id
LOOP
IF NOT functor_check_identity_row(p_functor_id, r.source_morphism_id,
r.target_morphism_id) THEN
n := n + 1;
END IF;
END LOOP;

FOR r IN
SELECT c.id FROM composition c
JOIN functor f ON f.id = p_functor_id AND c.category_id = f.source_category_id
LOOP
IF NOT functor_check_composition_row(p_functor_id, r.id) THEN
n := n + 1;
END IF;
END LOOP;

RETURN n;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Path signature integrity trigger
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION path_signature_check_integrity() RETURNS trigger AS $$
BEGIN
  IF NEW.proof_hash IS NULL OR length(NEW.proof_hash) = 0 THEN
    RAISE EXCEPTION 'path_signature.proof_hash cannot be empty';
  END IF;
  IF NEW.canonical_bytes IS NULL OR length(NEW.canonical_bytes) = 0 THEN
    RAISE EXCEPTION 'path_signature.canonical_bytes cannot be empty';
  END IF;
  IF NEW.address_hash IS NULL OR length(NEW.address_hash) = 0 THEN
    RAISE EXCEPTION 'path_signature.address_hash cannot be empty';
  END IF;
  IF array_length(NEW.morphism_chain, 1) IS NULL
     OR array_length(NEW.morphism_chain, 1) = 0 THEN
    RAISE EXCEPTION 'path_signature.morphism_chain cannot be empty';
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_path_signature_integrity ON path_signature;
CREATE TRIGGER trg_path_signature_integrity
BEFORE INSERT OR UPDATE ON path_signature
FOR EACH ROW EXECUTE FUNCTION path_signature_check_integrity();