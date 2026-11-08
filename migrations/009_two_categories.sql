-- ============================================================================
-- Categorical Ledger — Migration 009: 2-Categories
-- ============================================================================
-- A (strict) 2-category is recorded over a base category, whose objects and
-- morphisms are its objects and 1-morphisms (composition table, identities).
-- On top of these it records:
--   * 2-cells  α : f ⇒ f'  between parallel 1-morphisms f, f' : A → B
--     (two_morphism);
--   * identity 2-cells 1_f : f ⇒ f (two_identity, at most one per f);
--   * vertical composites β ∘ᵥ α for α : f ⇒ f', β : f' ⇒ f''
--     (two_morphism_vertical_comp: upper = β, lower = α, lower applied first);
--   * horizontal composites β ⋆ α for α : f ⇒ f' (f, f' : A → B) and
--     β : g ⇒ g' (g, g' : B → C), a 2-cell g ∘ f ⇒ g' ∘ f'
--     (two_morphism_horizontal_comp: left = β, right = α, the same
--     left-after-right convention as the composition table of 001).
--
-- Checks.  Every check logs to two_category_coherence_violation (column
-- violation_type) and raises only when qbx.enforcement_mode = 'strict'.
--   typing (write time and batch)
--     cell_typing        a 2-cell joins 1-morphisms that are not parallel, or
--                        not in the base category
--     identity_typing    an identity 2-cell of f is not a 2-cell f ⇒ f of this
--                        2-category (or f is not in the base category)
--     vertical_typing    β ∘ᵥ α: cells from another 2-category, target(α) ≠
--                        source(β), or the result is not source(α) ⇒ target(β)
--     horizontal_typing  β ⋆ α: cells from another 2-category, the 1-morphisms
--                        do not compose, g ∘ f / g' ∘ f' are not recorded in the
--                        composition table (details.missing_composite), or the
--                        result is not g ∘ f ⇒ g' ∘ f'
--   laws read off one row and the identity table (write time and batch)
--     vertical_unit          1_f' ∘ᵥ α = α  and  α ∘ᵥ 1_f = α
--     horizontal_unit        1_(1_B) ⋆ α = α  and  β ⋆ 1_(1_B) = β
--     identity_preservation  1_g ⋆ 1_f = 1_(g ∘ f)   (when 1_(g ∘ f) is recorded)
--   laws over several rows (batch: check_two_category, run_all_batch_checks)
--     vertical_associativity    (γ ∘ᵥ β) ∘ᵥ α = γ ∘ᵥ (β ∘ᵥ α)
--     horizontal_associativity  (γ ⋆ β) ⋆ α = γ ⋆ (β ⋆ α)
--     interchange               (β' ∘ᵥ β) ⋆ (α' ∘ᵥ α) = (β' ⋆ α') ∘ᵥ (β ⋆ α)
-- A law is checked wherever every composite it mentions is recorded; a
-- missing composite is not a violation (the ledger cannot know it), so a pass
-- means "consistent with a strict 2-category on the recorded data".  2-cells
-- are compared by id.
--
-- Formal backing (Formal/TwoCategory.lean): identity preservation and
-- interchange are exactly functoriality of horizontal composition
-- Hom(B, C) × Hom(A, B) ⥤ Hom(A, C) (exists_bifunctor_iff); neither implies the
-- other (interchange_not_implied, identity_preservation_not_implied); on the
-- 2-cells of an identity 1-morphism the laws force vertical = horizontal and
-- commutativity (eckmannHilton_two_cells), which the live tests use as an
-- oracle.
--
-- Phase 1 sprint 6 rewrite.  Running the original on PostgreSQL 16 showed:
--   * a 2-cell between non-parallel 1-morphisms (f : A → B, k : B → A) was
--     accepted;
--   * compose_two_horizontal never checked that the cells compose and typed
--     the result source(left) ⇒ target(right) — 1-morphisms of the factors,
--     not the composites g ∘ f ⇒ g' ∘ f' — so composing two 2-cells
--     f ⇒ g, g ⇒ f : A → B "horizontally" produced a 2-cell f ⇒ f;
--   * compose_two_vertical's IF NOT FOUND only looked at the second lookup: a
--     missing upper cell surfaced as a NOT NULL error from the insert;
--   * cells from another 2-category, or a p_two_cat that differs from the
--     cells', were accepted;
--   * every call created a fresh result cell, so a composite could not be
--     identified with an existing cell, every unit law with a recorded
--     identity failed, and composing the same pair twice raised a unique
--     violation;
--   * there were no identity 2-cells at all;
--   * check_interchange_law was an empty loop: it checked nothing, logged
--     nothing, and was not part of run_all_batch_checks.
-- ============================================================================

CREATE TABLE IF NOT EXISTS two_category (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  base_category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS two_morphism (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  two_category_id UUID NOT NULL REFERENCES two_category(id) ON DELETE CASCADE,
  source_morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
  target_morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
  name TEXT,
  data JSONB DEFAULT '{}'::jsonb,
  UNIQUE (two_category_id, source_morphism_id, target_morphism_id, name)
);

CREATE INDEX IF NOT EXISTS idx_two_morphism_cat ON two_morphism (two_category_id);

-- Identity 2-cells: 1_f for a 1-morphism f (at most one per f).
CREATE TABLE IF NOT EXISTS two_identity (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  two_category_id UUID NOT NULL REFERENCES two_category(id) ON DELETE CASCADE,
  morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
  two_morphism_id UUID NOT NULL REFERENCES two_morphism(id) ON DELETE CASCADE,
  UNIQUE (two_category_id, morphism_id)
);

CREATE INDEX IF NOT EXISTS idx_two_identity_cell ON two_identity (two_morphism_id);

CREATE TABLE IF NOT EXISTS two_morphism_vertical_comp (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  two_category_id UUID NOT NULL REFERENCES two_category(id) ON DELETE CASCADE,
  upper_id UUID NOT NULL REFERENCES two_morphism(id) ON DELETE CASCADE,
  lower_id UUID NOT NULL REFERENCES two_morphism(id) ON DELETE CASCADE,
  result_id UUID NOT NULL REFERENCES two_morphism(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  UNIQUE (two_category_id, upper_id, lower_id)
);

CREATE TABLE IF NOT EXISTS two_morphism_horizontal_comp (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  two_category_id UUID NOT NULL REFERENCES two_category(id) ON DELETE CASCADE,
  left_id UUID NOT NULL REFERENCES two_morphism(id) ON DELETE CASCADE,
  right_id UUID NOT NULL REFERENCES two_morphism(id) ON DELETE CASCADE,
  result_id UUID NOT NULL REFERENCES two_morphism(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  UNIQUE (two_category_id, left_id, right_id)
);

CREATE TABLE IF NOT EXISTS two_category_coherence_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  two_category_id UUID NOT NULL REFERENCES two_category(id) ON DELETE CASCADE,
  violation_type TEXT,    -- see the header for the list of reasons
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_two_category_violation_cat
  ON two_category_coherence_violation (two_category_id, detected_at DESC);

-- ---------------------------------------------------------------------------
-- Lookups
-- ---------------------------------------------------------------------------
-- The identity 2-cell recorded for 1-morphism p_mor (NULL if none).
CREATE OR REPLACE FUNCTION two_identity_of(p_tc UUID, p_mor UUID) RETURNS UUID AS $$
  SELECT ti.two_morphism_id FROM two_identity ti
   WHERE ti.two_category_id = p_tc AND ti.morphism_id = p_mor;
$$ LANGUAGE sql STABLE;

-- Is p_cell a recorded identity 2-cell (of any 1-morphism)?
CREATE OR REPLACE FUNCTION two_is_identity(p_tc UUID, p_cell UUID) RETURNS BOOLEAN AS $$
  SELECT EXISTS (SELECT 1 FROM two_identity ti
                  WHERE ti.two_category_id = p_tc AND ti.two_morphism_id = p_cell);
$$ LANGUAGE sql STABLE;

-- Is p_cell a recorded identity 2-cell of an identity 1-morphism (1_(1_A))?
CREATE OR REPLACE FUNCTION two_is_unit_cell(p_tc UUID, p_cell UUID) RETURNS BOOLEAN AS $$
  SELECT EXISTS (SELECT 1 FROM two_identity ti
                   JOIN identity_morphism im ON im.morphism_id = ti.morphism_id
                  WHERE ti.two_category_id = p_tc AND ti.two_morphism_id = p_cell);
$$ LANGUAGE sql STABLE;

-- The recorded composite g ∘ f in the base category (NULL if none).
CREATE OR REPLACE FUNCTION two_base_composite(p_g UUID, p_f UUID) RETURNS UUID AS $$
  SELECT c.result_id FROM composition c WHERE c.left_id = p_g AND c.right_id = p_f;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Problems of single rows (pure)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION two_cell_problems(p_cell UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  v_base UUID;
  s RECORD;
  t RECORD;
BEGIN
  SELECT tm.* INTO c FROM two_morphism tm WHERE tm.id = p_cell;
  IF c.id IS NULL THEN
    RETURN;
  END IF;
  SELECT tc.base_category_id INTO v_base FROM two_category tc WHERE tc.id = c.two_category_id;
  SELECT m.* INTO s FROM morphism m WHERE m.id = c.source_morphism_id;
  SELECT m.* INTO t FROM morphism m WHERE m.id = c.target_morphism_id;
  IF s.category_id IS DISTINCT FROM v_base OR t.category_id IS DISTINCT FROM v_base
     OR s.source_id IS DISTINCT FROM t.source_id OR s.target_id IS DISTINCT FROM t.target_id THEN
    reason := 'cell_typing';
    details := jsonb_build_object('cell', c.id, 'source', c.source_morphism_id,
                                  'target', c.target_morphism_id);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION two_identity_problems(p_tc UUID, p_mor UUID, p_cell UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  v_base UUID;
  v_mor_cat UUID;
BEGIN
  SELECT tm.* INTO c FROM two_morphism tm WHERE tm.id = p_cell;
  SELECT tc.base_category_id INTO v_base FROM two_category tc WHERE tc.id = p_tc;
  SELECT m.category_id INTO v_mor_cat FROM morphism m WHERE m.id = p_mor;
  IF c.id IS NULL OR c.two_category_id IS DISTINCT FROM p_tc
     OR v_mor_cat IS DISTINCT FROM v_base
     OR c.source_morphism_id IS DISTINCT FROM p_mor
     OR c.target_morphism_id IS DISTINCT FROM p_mor THEN
    reason := 'identity_typing';
    details := jsonb_build_object('morphism', p_mor, 'cell', p_cell);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- β ∘ᵥ α = result, with upper = β, lower = α.
CREATE OR REPLACE FUNCTION two_vertical_problems(
  p_tc UUID, p_upper UUID, p_lower UUID, p_result UUID
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  u RECORD;
  l RECORD;
  r RECORD;
  v_details JSONB;
BEGIN
  v_details := jsonb_build_object('upper', p_upper, 'lower', p_lower, 'result', p_result);
  SELECT tm.* INTO u FROM two_morphism tm WHERE tm.id = p_upper;
  SELECT tm.* INTO l FROM two_morphism tm WHERE tm.id = p_lower;
  SELECT tm.* INTO r FROM two_morphism tm WHERE tm.id = p_result;
  IF u.id IS NULL OR l.id IS NULL OR r.id IS NULL
     OR u.two_category_id IS DISTINCT FROM p_tc OR l.two_category_id IS DISTINCT FROM p_tc
     OR r.two_category_id IS DISTINCT FROM p_tc
     OR l.target_morphism_id IS DISTINCT FROM u.source_morphism_id
     OR r.source_morphism_id IS DISTINCT FROM l.source_morphism_id
     OR r.target_morphism_id IS DISTINCT FROM u.target_morphism_id THEN
    reason := 'vertical_typing'; details := v_details; RETURN NEXT;
  END IF;
  -- unit laws: 1_f' ∘ᵥ α = α, β ∘ᵥ 1_f = β
  IF two_is_identity(p_tc, p_upper) AND p_result IS DISTINCT FROM p_lower THEN
    reason := 'vertical_unit';
    details := v_details || jsonb_build_object('expected', p_lower); RETURN NEXT;
  END IF;
  IF two_is_identity(p_tc, p_lower) AND p_result IS DISTINCT FROM p_upper THEN
    reason := 'vertical_unit';
    details := v_details || jsonb_build_object('expected', p_upper); RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- β ⋆ α = result, with left = β : g ⇒ g' (B → C), right = α : f ⇒ f' (A → B).
CREATE OR REPLACE FUNCTION two_horizontal_problems(
  p_tc UUID, p_left UUID, p_right UUID, p_result UUID
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  b RECORD;
  a RECORD;
  r RECORD;
  v_f_tgt UUID;
  v_g_src UUID;
  v_src UUID;
  v_tgt UUID;
  v_details JSONB;
  v_id_left UUID;
  v_id_right UUID;
  v_expected UUID;
BEGIN
  v_details := jsonb_build_object('left', p_left, 'right', p_right, 'result', p_result);
  SELECT tm.* INTO b FROM two_morphism tm WHERE tm.id = p_left;
  SELECT tm.* INTO a FROM two_morphism tm WHERE tm.id = p_right;
  SELECT tm.* INTO r FROM two_morphism tm WHERE tm.id = p_result;
  SELECT m.target_id INTO v_f_tgt FROM morphism m WHERE m.id = a.source_morphism_id;
  SELECT m.source_id INTO v_g_src FROM morphism m WHERE m.id = b.source_morphism_id;
  v_src := two_base_composite(b.source_morphism_id, a.source_morphism_id);
  v_tgt := two_base_composite(b.target_morphism_id, a.target_morphism_id);
  IF b.id IS NULL OR a.id IS NULL OR r.id IS NULL
     OR b.two_category_id IS DISTINCT FROM p_tc OR a.two_category_id IS DISTINCT FROM p_tc
     OR r.two_category_id IS DISTINCT FROM p_tc
     OR v_f_tgt IS DISTINCT FROM v_g_src
     OR v_src IS NULL OR v_tgt IS NULL
     OR r.source_morphism_id IS DISTINCT FROM v_src
     OR r.target_morphism_id IS DISTINCT FROM v_tgt THEN
    reason := 'horizontal_typing';
    details := v_details || jsonb_build_object(
      'missing_composite', (v_f_tgt IS NOT DISTINCT FROM v_g_src AND v_f_tgt IS NOT NULL)
                           AND (v_src IS NULL OR v_tgt IS NULL));
    RETURN NEXT;
  END IF;
  -- unit laws: 1_(1_B) ⋆ α = α, β ⋆ 1_(1_B) = β
  IF two_is_unit_cell(p_tc, p_left) AND p_result IS DISTINCT FROM p_right THEN
    reason := 'horizontal_unit';
    details := v_details || jsonb_build_object('expected', p_right); RETURN NEXT;
  END IF;
  IF two_is_unit_cell(p_tc, p_right) AND p_result IS DISTINCT FROM p_left THEN
    reason := 'horizontal_unit';
    details := v_details || jsonb_build_object('expected', p_left); RETURN NEXT;
  END IF;
  -- identity preservation: 1_g ⋆ 1_f = 1_(g ∘ f)
  v_id_left := two_identity_of(p_tc, b.source_morphism_id);
  v_id_right := two_identity_of(p_tc, a.source_morphism_id);
  IF v_id_left IS NOT NULL AND v_id_left = p_left
     AND v_id_right IS NOT NULL AND v_id_right = p_right THEN
    v_expected := two_identity_of(p_tc, v_src);
    IF v_expected IS NOT NULL AND v_expected IS DISTINCT FROM p_result THEN
      reason := 'identity_preservation';
      details := v_details || jsonb_build_object('expected', v_expected); RETURN NEXT;
    END IF;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- All problems of a 2-category (pure)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION two_category_problems(p_tc UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
  pr RECORD;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM two_category tc WHERE tc.id = p_tc) THEN
    reason := 'missing_two_category';
    details := jsonb_build_object('two_category', p_tc);
    RETURN NEXT;
    RETURN;
  END IF;

  FOR r IN SELECT tm.id FROM two_morphism tm WHERE tm.two_category_id = p_tc ORDER BY tm.id LOOP
    FOR pr IN SELECT * FROM two_cell_problems(r.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
    END LOOP;
  END LOOP;

  FOR r IN SELECT ti.* FROM two_identity ti WHERE ti.two_category_id = p_tc ORDER BY ti.id LOOP
    FOR pr IN SELECT * FROM two_identity_problems(p_tc, r.morphism_id, r.two_morphism_id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
    END LOOP;
  END LOOP;

  FOR r IN SELECT v.* FROM two_morphism_vertical_comp v WHERE v.two_category_id = p_tc ORDER BY v.id LOOP
    FOR pr IN SELECT * FROM two_vertical_problems(p_tc, r.upper_id, r.lower_id, r.result_id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
    END LOOP;
  END LOOP;

  FOR r IN SELECT h.* FROM two_morphism_horizontal_comp h WHERE h.two_category_id = p_tc ORDER BY h.id LOOP
    FOR pr IN SELECT * FROM two_horizontal_problems(p_tc, r.left_id, r.right_id, r.result_id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
    END LOOP;
  END LOOP;

  -- (γ ∘ᵥ β) ∘ᵥ α = γ ∘ᵥ (β ∘ᵥ α)
  FOR r IN
    SELECT v1.upper_id AS c, v1.lower_id AS b, v2.lower_id AS a,
           v2.result_id AS left_assoc, v4.result_id AS right_assoc
      FROM two_morphism_vertical_comp v1
      JOIN two_morphism_vertical_comp v2
        ON v2.two_category_id = p_tc AND v2.upper_id = v1.result_id
      JOIN two_morphism_vertical_comp v3
        ON v3.two_category_id = p_tc AND v3.upper_id = v1.lower_id AND v3.lower_id = v2.lower_id
      JOIN two_morphism_vertical_comp v4
        ON v4.two_category_id = p_tc AND v4.upper_id = v1.upper_id AND v4.lower_id = v3.result_id
     WHERE v1.two_category_id = p_tc AND v2.result_id <> v4.result_id
     ORDER BY v1.id, v2.id
  LOOP
    reason := 'vertical_associativity';
    details := jsonb_build_object('c', r.c, 'b', r.b, 'a', r.a,
                                  'left_assoc', r.left_assoc, 'right_assoc', r.right_assoc);
    RETURN NEXT;
  END LOOP;

  -- (γ ⋆ β) ⋆ α = γ ⋆ (β ⋆ α)
  FOR r IN
    SELECT h1.left_id AS c, h1.right_id AS b, h2.right_id AS a,
           h2.result_id AS left_assoc, h4.result_id AS right_assoc
      FROM two_morphism_horizontal_comp h1
      JOIN two_morphism_horizontal_comp h2
        ON h2.two_category_id = p_tc AND h2.left_id = h1.result_id
      JOIN two_morphism_horizontal_comp h3
        ON h3.two_category_id = p_tc AND h3.left_id = h1.right_id AND h3.right_id = h2.right_id
      JOIN two_morphism_horizontal_comp h4
        ON h4.two_category_id = p_tc AND h4.left_id = h1.left_id AND h4.right_id = h3.result_id
     WHERE h1.two_category_id = p_tc AND h2.result_id <> h4.result_id
     ORDER BY h1.id, h2.id
  LOOP
    reason := 'horizontal_associativity';
    details := jsonb_build_object('c', r.c, 'b', r.b, 'a', r.a,
                                  'left_assoc', r.left_assoc, 'right_assoc', r.right_assoc);
    RETURN NEXT;
  END LOOP;

  -- (β' ∘ᵥ β) ⋆ (α' ∘ᵥ α) = (β' ⋆ α') ∘ᵥ (β ⋆ α)
  FOR r IN
    SELECT vb.upper_id AS beta2, vb.lower_id AS beta1,
           va.upper_id AS alpha2, va.lower_id AS alpha1,
           hx.result_id AS horizontal_of_vertical, vy.result_id AS vertical_of_horizontal
      FROM two_morphism_vertical_comp vb
      JOIN two_morphism_vertical_comp va ON va.two_category_id = p_tc
      JOIN two_morphism_horizontal_comp hx
        ON hx.two_category_id = p_tc AND hx.left_id = vb.result_id AND hx.right_id = va.result_id
      JOIN two_morphism_horizontal_comp hp
        ON hp.two_category_id = p_tc AND hp.left_id = vb.upper_id AND hp.right_id = va.upper_id
      JOIN two_morphism_horizontal_comp hq
        ON hq.two_category_id = p_tc AND hq.left_id = vb.lower_id AND hq.right_id = va.lower_id
      JOIN two_morphism_vertical_comp vy
        ON vy.two_category_id = p_tc AND vy.upper_id = hp.result_id AND vy.lower_id = hq.result_id
     WHERE vb.two_category_id = p_tc AND hx.result_id <> vy.result_id
     ORDER BY vb.id, va.id
  LOOP
    reason := 'interchange';
    details := jsonb_build_object('beta2', r.beta2, 'beta1', r.beta1,
                                  'alpha2', r.alpha2, 'alpha1', r.alpha1,
                                  'horizontal_of_vertical', r.horizontal_of_vertical,
                                  'vertical_of_horizontal', r.vertical_of_horizontal);
    RETURN NEXT;
  END LOOP;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Logging helper and checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION two_category_record(p_tc UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  IF EXISTS (SELECT 1 FROM two_category tc WHERE tc.id = p_tc) THEN
    INSERT INTO two_category_coherence_violation (two_category_id, violation_type, details)
    VALUES (p_tc, p_reason, coalesce(p_details, '{}'::jsonb));
  END IF;
END;
$$ LANGUAGE plpgsql;

-- Batch tier: every row and every law.  Logs every problem, raises in strict
-- mode, returns TRUE iff there were none.
CREATE OR REPLACE FUNCTION check_two_category(p_tc UUID) RETURNS BOOLEAN AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM two_category_problems(p_tc) LOOP
    PERFORM two_category_record(p_tc, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION '2-category % violates its laws (% problem(s))', p_tc, n_problems;
  END IF;
  RETURN n_problems = 0;
END;
$$ LANGUAGE plpgsql;

-- The interchange law alone (the original entry point, formerly a no-op).
DROP FUNCTION IF EXISTS check_interchange_law(UUID);
CREATE OR REPLACE FUNCTION check_interchange_law(p_tc UUID) RETURNS BOOLEAN AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM two_category_problems(p_tc) p WHERE p.reason = 'interchange' LOOP
    PERFORM two_category_record(p_tc, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION '2-category % violates the interchange law (% instance(s))', p_tc, n_problems;
  END IF;
  RETURN n_problems = 0;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_two_morphism() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM two_cell_problems(NEW.id) LOOP
    PERFORM two_category_record(NEW.two_category_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION '2-cell % is not valid (% problem(s))', NEW.id, n_problems;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_two_morphism ON two_morphism;
CREATE TRIGGER trg_check_two_morphism
AFTER INSERT OR UPDATE ON two_morphism
FOR EACH ROW EXECUTE FUNCTION trg_check_two_morphism();

CREATE OR REPLACE FUNCTION trg_check_two_identity() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM two_identity_problems(NEW.two_category_id, NEW.morphism_id,
                                                NEW.two_morphism_id) LOOP
    PERFORM two_category_record(NEW.two_category_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Identity 2-cell % is not valid (% problem(s))', NEW.id, n_problems;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_two_identity ON two_identity;
CREATE TRIGGER trg_check_two_identity
AFTER INSERT OR UPDATE ON two_identity
FOR EACH ROW EXECUTE FUNCTION trg_check_two_identity();

CREATE OR REPLACE FUNCTION trg_check_two_vertical() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM two_vertical_problems(NEW.two_category_id, NEW.upper_id,
                                                NEW.lower_id, NEW.result_id) LOOP
    PERFORM two_category_record(NEW.two_category_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Vertical composite % is not valid (% problem(s))', NEW.id, n_problems;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_two_vertical ON two_morphism_vertical_comp;
CREATE TRIGGER trg_check_two_vertical
AFTER INSERT OR UPDATE ON two_morphism_vertical_comp
FOR EACH ROW EXECUTE FUNCTION trg_check_two_vertical();

CREATE OR REPLACE FUNCTION trg_check_two_horizontal() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM two_horizontal_problems(NEW.two_category_id, NEW.left_id,
                                                  NEW.right_id, NEW.result_id) LOOP
    PERFORM two_category_record(NEW.two_category_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Horizontal composite % is not valid (% problem(s))', NEW.id, n_problems;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_two_horizontal ON two_morphism_horizontal_comp;
CREATE TRIGGER trg_check_two_horizontal
AFTER INSERT OR UPDATE ON two_morphism_horizontal_comp
FOR EACH ROW EXECUTE FUNCTION trg_check_two_horizontal();

-- ---------------------------------------------------------------------------
-- Writers.  They refuse (raise in every mode) input they cannot build a
-- well-typed row from; rows inserted directly are checked by the triggers.
-- ---------------------------------------------------------------------------
-- The identity 2-cell 1_f, created (as a 2-cell f ⇒ f) if not yet recorded.
CREATE OR REPLACE FUNCTION two_identity_cell(p_tc UUID, p_mor UUID) RETURNS UUID AS $$
DECLARE
  v_cell UUID;
  v_name TEXT;
BEGIN
  v_cell := two_identity_of(p_tc, p_mor);
  IF v_cell IS NOT NULL THEN
    RETURN v_cell;
  END IF;
  SELECT m.name INTO v_name FROM morphism m WHERE m.id = p_mor;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'two_identity_cell: 1-morphism % not found', p_mor;
  END IF;
  INSERT INTO two_morphism (two_category_id, source_morphism_id, target_morphism_id, name)
  VALUES (p_tc, p_mor, p_mor, 'id2(' || coalesce(v_name, p_mor::text) || ')')
  RETURNING id INTO v_cell;
  INSERT INTO two_identity (two_category_id, morphism_id, two_morphism_id)
  VALUES (p_tc, p_mor, v_cell);
  RETURN v_cell;
END;
$$ LANGUAGE plpgsql;

-- β ∘ᵥ α (upper = β, lower = α).  Returns the recorded result if the pair is
-- already composed.  Otherwise records p_result if given; with p_result NULL
-- it uses the unit law when one factor is an identity 2-cell and else creates
-- a fresh 2-cell source(α) ⇒ target(β).
DROP FUNCTION IF EXISTS compose_two_vertical(UUID, UUID, UUID);
CREATE OR REPLACE FUNCTION compose_two_vertical(
  p_two_cat UUID, p_upper UUID, p_lower UUID, p_result UUID DEFAULT NULL
) RETURNS UUID AS $$
DECLARE
  upper_rec RECORD;
  lower_rec RECORD;
  v_result UUID;
BEGIN
  SELECT v.result_id INTO v_result FROM two_morphism_vertical_comp v
   WHERE v.two_category_id = p_two_cat AND v.upper_id = p_upper AND v.lower_id = p_lower;
  IF v_result IS NOT NULL THEN
    IF p_result IS NOT NULL AND p_result <> v_result THEN
      RAISE EXCEPTION 'compose_two_vertical: % ∘ᵥ % is already recorded as %', p_upper, p_lower, v_result;
    END IF;
    RETURN v_result;
  END IF;
  SELECT tm.* INTO upper_rec FROM two_morphism tm WHERE tm.id = p_upper;
  SELECT tm.* INTO lower_rec FROM two_morphism tm WHERE tm.id = p_lower;
  IF upper_rec.id IS NULL OR lower_rec.id IS NULL THEN
    RAISE EXCEPTION 'compose_two_vertical: 2-cell(s) not found (upper %, lower %)', p_upper, p_lower;
  END IF;
  IF upper_rec.two_category_id <> p_two_cat OR lower_rec.two_category_id <> p_two_cat THEN
    RAISE EXCEPTION 'compose_two_vertical: 2-cells are not in 2-category %', p_two_cat;
  END IF;
  IF lower_rec.target_morphism_id <> upper_rec.source_morphism_id THEN
    RAISE EXCEPTION 'compose_two_vertical: target(lower) <> source(upper)';
  END IF;

  v_result := p_result;
  IF v_result IS NULL AND two_is_identity(p_two_cat, p_upper) THEN
    v_result := p_lower;
  ELSIF v_result IS NULL AND two_is_identity(p_two_cat, p_lower) THEN
    v_result := p_upper;
  ELSIF v_result IS NULL THEN
    INSERT INTO two_morphism
      (two_category_id, source_morphism_id, target_morphism_id, name, data)
    VALUES
      (p_two_cat, lower_rec.source_morphism_id, upper_rec.target_morphism_id,
       '(' || coalesce(upper_rec.name, '?') || ' ∘v ' || coalesce(lower_rec.name, '?') || ')',
       jsonb_build_object('vertical_of', jsonb_build_array(p_upper, p_lower)))
    RETURNING id INTO v_result;
  END IF;

  INSERT INTO two_morphism_vertical_comp (two_category_id, upper_id, lower_id, result_id)
  VALUES (p_two_cat, p_upper, p_lower, v_result);
  RETURN v_result;
END;
$$ LANGUAGE plpgsql;

-- β ⋆ α (left = β : g ⇒ g', right = α : f ⇒ f').  The composites g ∘ f and
-- g' ∘ f' must be recorded in the composition table.  Returns the recorded
-- result if any; otherwise records p_result if given; with p_result NULL it
-- uses the unit law (a factor 1_(1_B)), identity preservation (1_g ⋆ 1_f =
-- 1_(g ∘ f), created if needed) or else a fresh 2-cell g ∘ f ⇒ g' ∘ f'.
DROP FUNCTION IF EXISTS compose_two_horizontal(UUID, UUID, UUID);
CREATE OR REPLACE FUNCTION compose_two_horizontal(
  p_two_cat UUID, p_left UUID, p_right UUID, p_result UUID DEFAULT NULL
) RETURNS UUID AS $$
DECLARE
  left_rec RECORD;
  right_rec RECORD;
  v_f_tgt UUID;
  v_g_src UUID;
  v_src UUID;
  v_tgt UUID;
  v_result UUID;
BEGIN
  SELECT h.result_id INTO v_result FROM two_morphism_horizontal_comp h
   WHERE h.two_category_id = p_two_cat AND h.left_id = p_left AND h.right_id = p_right;
  IF v_result IS NOT NULL THEN
    IF p_result IS NOT NULL AND p_result <> v_result THEN
      RAISE EXCEPTION 'compose_two_horizontal: % ⋆ % is already recorded as %', p_left, p_right, v_result;
    END IF;
    RETURN v_result;
  END IF;
  SELECT tm.* INTO left_rec FROM two_morphism tm WHERE tm.id = p_left;
  SELECT tm.* INTO right_rec FROM two_morphism tm WHERE tm.id = p_right;
  IF left_rec.id IS NULL OR right_rec.id IS NULL THEN
    RAISE EXCEPTION 'compose_two_horizontal: 2-cell(s) not found (left %, right %)', p_left, p_right;
  END IF;
  IF left_rec.two_category_id <> p_two_cat OR right_rec.two_category_id <> p_two_cat THEN
    RAISE EXCEPTION 'compose_two_horizontal: 2-cells are not in 2-category %', p_two_cat;
  END IF;
  SELECT m.target_id INTO v_f_tgt FROM morphism m WHERE m.id = right_rec.source_morphism_id;
  SELECT m.source_id INTO v_g_src FROM morphism m WHERE m.id = left_rec.source_morphism_id;
  IF v_f_tgt IS DISTINCT FROM v_g_src THEN
    RAISE EXCEPTION 'compose_two_horizontal: the 1-morphisms do not compose (target of right <> source of left)';
  END IF;
  v_src := two_base_composite(left_rec.source_morphism_id, right_rec.source_morphism_id);
  v_tgt := two_base_composite(left_rec.target_morphism_id, right_rec.target_morphism_id);
  IF v_src IS NULL OR v_tgt IS NULL THEN
    RAISE EXCEPTION 'compose_two_horizontal: composite 1-morphism not recorded in the composition table';
  END IF;

  v_result := p_result;
  IF v_result IS NULL AND two_is_unit_cell(p_two_cat, p_left) THEN
    v_result := p_right;
  ELSIF v_result IS NULL AND two_is_unit_cell(p_two_cat, p_right) THEN
    v_result := p_left;
  ELSIF v_result IS NULL
        AND two_identity_of(p_two_cat, left_rec.source_morphism_id) = p_left
        AND two_identity_of(p_two_cat, right_rec.source_morphism_id) = p_right THEN
    v_result := two_identity_cell(p_two_cat, v_src);
  ELSIF v_result IS NULL THEN
    INSERT INTO two_morphism
      (two_category_id, source_morphism_id, target_morphism_id, name, data)
    VALUES
      (p_two_cat, v_src, v_tgt,
       '(' || coalesce(left_rec.name, '?') || ' ⋆ ' || coalesce(right_rec.name, '?') || ')',
       jsonb_build_object('horizontal_of', jsonb_build_array(p_left, p_right)))
    RETURNING id INTO v_result;
  END IF;

  INSERT INTO two_morphism_horizontal_comp (two_category_id, left_id, right_id, result_id)
  VALUES (p_two_cat, p_left, p_right, v_result);
  RETURN v_result;
END;
$$ LANGUAGE plpgsql;
