-- ============================================================================
-- Categorical Ledger — Migration 004: Natural Transformations
-- ============================================================================
-- Enforces naturality squares:
--
--     F(X) --F(f)--> F(Y)
--      |              |
--     η_X            η_Y
--      |              |
--      v              v
--     G(X) --G(f)--> G(Y)
--
-- i.e.  η_Y ∘ F(f) = G(f) ∘ η_X   for every f: X → Y.
--
-- Reference.  The in-memory checker qbx.categorical.NaturalTransformation
-- (src/qbx/categorical/natural_transformation.py) is the reference; the
-- live-database tests (tests/live_db/test_naturality_db.py) compare the two on
-- random data.  Reasons carry the reference's names.
--
-- Recording.  natural_transformation (η : F ⇒ G) and
-- natural_transformation_component (η_X, at most one per object).
--
-- Checks.  Every check logs to naturality_violation (column law) and raises
-- only when qbx.enforcement_mode = 'strict'.
--   write time (transformation row)
--     transformation_typing   F and G do not have the same source and the same
--                             target category, or one of them does not exist
--                             (details: source_functor, target_functor)
--   write time (component row; natural_transformation_component trigger)
--     component_unknown_object  X is not an object of the source category
--                             (details: X, eta_x); no square is checked
--     component_typing        η_X is not a morphism F(X) → G(X) of the target
--                             category, or F(X) / G(X) is not mapped
--                             (details: X, eta_x, expected, actual)
--     the square of every morphism f of the source category (identities and
--     endomorphisms included) with one endpoint X whose other endpoint has a
--     component — see below.  Checking both directions makes incremental
--     enforcement complete (Formal/Naturality.lean: checkedBy_of_mem).
--   squares (write time, as above, and batch)
--     naturality_missing_data  η_X, η_Y, F(f) or G(f) is missing
--     naturality_composite_missing  η_Y ∘ F(f) or G(f) ∘ η_X is not recorded,
--                             or the two morphisms are not composable in the
--                             target category
--     naturality_square       the two composites differ
--                             (details: f, X, Y, eta_x, eta_y, Ff, Gf and, once
--                             computed, left = η_Y ∘ F(f), right = G(f) ∘ η_X)
--   batch only (natural_transformation_problems, check_natural_transformation,
--   recheck_naturality, run_all_batch_checks): transformation_typing (and then
--   nothing else), component_unknown_object for every stored component off the
--   source category, then per object of the source category
--   component_missing (details: X) or component_typing, then the square of
--   every morphism of the source category.  This is the reference's
--   verify_all_laws; each problem is logged once.
-- Composites are read with nt_compose_in: NULL unless both morphisms lie in the
-- target category and are composable, otherwise qbx_compose (unit laws for
-- recorded identities, the composition table otherwise).
--
-- Formal backing (Formal/Naturality.lean, H-010 – H-012): checking squares on
-- a generating set suffices; incremental enforcement in both directions is
-- complete; the pre-Phase-1 trigger (out of X only, endomorphisms skipped)
-- missed squares.
--
-- History.
--   Phase 1 sprint 1–2: the record/alias clash that made every insert fail
--   and the reversed composite lookup were fixed; squares are checked in both
--   directions; a missing composite is a violation (decision log).
--   Phase 1 sprint 14 (acceptance review) rewrite.  Comparing the previous
--   version with the reference on PostgreSQL 16 showed:
--     * a component η_X that is not a morphism F(X) → G(X) was accepted, even
--       in strict mode (e.g. η_X = f, a morphism of the source category);
--     * a component on an object of another category was accepted;
--     * η : F ⇒ G was accepted for functors with different source or target
--       categories;
--     * a square whose F(f) or G(f) is not mapped was skipped silently;
--     * identity squares were never checked, and nt_compose ignores
--       composability (η_Y ∘ F(f) with F(f) an identity of the wrong object
--       "composed" to η_Y);
--     * the batch check never reported missing components and logged every
--       square twice (once per component).
-- ============================================================================

---

-- Tables

---

CREATE TABLE IF NOT EXISTS natural_transformation (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
name TEXT NOT NULL,
source_functor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
target_functor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
metadata JSONB DEFAULT '{}'::jsonb,
created_at TIMESTAMPTZ DEFAULT now(),
UNIQUE (name, source_functor_id, target_functor_id)
);

CREATE TABLE IF NOT EXISTS natural_transformation_component (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
transformation_id UUID NOT NULL REFERENCES natural_transformation(id) ON DELETE CASCADE,
object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
metadata JSONB DEFAULT '{}'::jsonb,
UNIQUE (transformation_id, object_id)
);

CREATE INDEX IF NOT EXISTS idx_nt_component_transformation
ON natural_transformation_component (transformation_id);

---

-- Violation log

---

CREATE TABLE IF NOT EXISTS naturality_violation (
id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
transformation_id UUID NOT NULL REFERENCES natural_transformation(id) ON DELETE CASCADE,
object_x UUID,
object_y UUID,
morphism_f UUID,
eta_x UUID,
eta_y UUID,
f_mapped_by_F UUID,
f_mapped_by_G UUID,
left_composite UUID,
right_composite UUID,
law TEXT NOT NULL DEFAULT 'naturality_square',   -- read by v_all_violations (017)
details JSONB DEFAULT '{}'::jsonb,
detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_naturality_violation_transformation
ON naturality_violation (transformation_id, detected_at DESC);

---

-- Helper view: NT components joined with their transformation

---

CREATE OR REPLACE VIEW v_nt_components AS
SELECT
ntc.id              AS component_id,
ntc.transformation_id,
nt.source_functor_id,
nt.target_functor_id,
ntc.object_id,
ntc.morphism_id     AS eta_x
FROM natural_transformation_component ntc
JOIN natural_transformation nt ON nt.id = ntc.transformation_id;

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------
-- Composition convention (shared with qbx.db.repositories.add_composition and
-- migrations 002, 005, 006): composition(left_id = g, right_id = f, result_id = h)
-- records h = g ∘ f, i.e. the RIGHT morphism is applied first.
--
-- nt_compose(first, second) = second ∘ first, unit laws applied, no typing
-- check (used by migration 005; kept unchanged).
CREATE OR REPLACE FUNCTION nt_compose(p_first UUID, p_second UUID)
RETURNS UUID AS $$
SELECT qbx_compose(p_first, p_second);
$$ LANGUAGE sql STABLE;

-- second ∘ first in category p_cat: NULL unless both morphisms are morphisms
-- of p_cat with target(first) = source(second); otherwise qbx_compose.  This
-- is the reference's compose(cat, first, second).
CREATE OR REPLACE FUNCTION nt_compose_in(p_cat UUID, p_first UUID, p_second UUID)
RETURNS UUID AS $$
SELECT CASE WHEN a.category_id = p_cat AND b.category_id = p_cat
                 AND a.target_id = b.source_id
            THEN qbx_compose(p_first, p_second) END
  FROM morphism a, morphism b
 WHERE a.id = p_first AND b.id = p_second;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION nt_fobj(p_functor UUID, p_object UUID) RETURNS UUID AS $$
SELECT target_object_id FROM functor_object_map
 WHERE functor_id = p_functor AND source_object_id = p_object;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION nt_fmor(p_functor UUID, p_morphism UUID) RETURNS UUID AS $$
SELECT target_morphism_id FROM functor_morphism_map
 WHERE functor_id = p_functor AND source_morphism_id = p_morphism;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION nt_eta(p_transformation UUID, p_object UUID) RETURNS UUID AS $$
SELECT morphism_id FROM natural_transformation_component
 WHERE transformation_id = p_transformation AND object_id = p_object;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Typing
-- ---------------------------------------------------------------------------
-- F and G must exist and share their source and their target category.
CREATE OR REPLACE FUNCTION nt_transformation_typing_problems(p_t UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  t RECORD;
  f RECORD;
  g RECORD;
BEGIN
  SELECT nt.* INTO t FROM natural_transformation nt WHERE nt.id = p_t;
  IF t.id IS NULL THEN
    reason := 'missing_transformation';
    details := jsonb_build_object('transformation', p_t);
    RETURN NEXT; RETURN;
  END IF;
  SELECT fu.* INTO f FROM functor fu WHERE fu.id = t.source_functor_id;
  SELECT fu.* INTO g FROM functor fu WHERE fu.id = t.target_functor_id;
  IF f.id IS NULL OR g.id IS NULL
     OR f.source_category_id IS DISTINCT FROM g.source_category_id
     OR f.target_category_id IS DISTINCT FROM g.target_category_id THEN
    reason := 'transformation_typing';
    details := jsonb_build_object(
      'source_functor', t.source_functor_id, 'target_functor', t.target_functor_id,
      'source_categories', jsonb_build_array(f.source_category_id, g.source_category_id),
      'target_categories', jsonb_build_array(f.target_category_id, g.target_category_id));
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- η_X must sit on an object of the source category and be F(X) → G(X) in the
-- target category.  Assumes the transformation is well typed.
CREATE OR REPLACE FUNCTION nt_component_problems(p_t UUID, p_object UUID, p_eta UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  t RECORD;
  v_src_cat UUID;
  v_tgt_cat UUID;
  v_fx UUID;
  v_gx UUID;
  m RECORD;
  v_actual JSONB;
BEGIN
  SELECT nt.* INTO t FROM natural_transformation nt WHERE nt.id = p_t;
  SELECT fu.source_category_id, fu.target_category_id INTO v_src_cat, v_tgt_cat
    FROM functor fu WHERE fu.id = t.source_functor_id;
  IF NOT EXISTS (SELECT 1 FROM object o WHERE o.id = p_object AND o.category_id = v_src_cat) THEN
    reason := 'component_unknown_object';
    details := jsonb_build_object('X', p_object, 'eta_x', p_eta);
    RETURN NEXT; RETURN;
  END IF;
  v_fx := nt_fobj(t.source_functor_id, p_object);
  v_gx := nt_fobj(t.target_functor_id, p_object);
  SELECT mo.* INTO m FROM morphism mo WHERE mo.id = p_eta AND mo.category_id = v_tgt_cat;
  v_actual := CASE WHEN m.id IS NULL THEN 'null'::jsonb
                   ELSE jsonb_build_array(m.source_id, m.target_id) END;
  IF v_fx IS NULL OR v_gx IS NULL OR m.id IS NULL
     OR m.source_id <> v_fx OR m.target_id <> v_gx THEN
    reason := 'component_typing';
    details := jsonb_build_object('X', p_object, 'eta_x', p_eta,
                                  'expected', jsonb_build_array(v_fx, v_gx),
                                  'actual', v_actual);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- The naturality square of one morphism f of the source category
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION nt_square_problems(p_t UUID, p_f UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  t RECORD;
  f RECORD;
  v_tgt_cat UUID;
  v_eta_x UUID;
  v_eta_y UUID;
  v_ff UUID;
  v_gf UUID;
  v_left UUID;
  v_right UUID;
  v_d JSONB;
BEGIN
  SELECT nt.* INTO t FROM natural_transformation nt WHERE nt.id = p_t;
  SELECT fu.target_category_id INTO v_tgt_cat FROM functor fu WHERE fu.id = t.source_functor_id;
  SELECT mo.* INTO f FROM morphism mo WHERE mo.id = p_f;
  v_eta_x := nt_eta(p_t, f.source_id);
  v_eta_y := nt_eta(p_t, f.target_id);
  v_ff := nt_fmor(t.source_functor_id, p_f);
  v_gf := nt_fmor(t.target_functor_id, p_f);
  v_d := jsonb_build_object('f', p_f, 'X', f.source_id, 'Y', f.target_id,
                            'eta_x', v_eta_x, 'eta_y', v_eta_y, 'Ff', v_ff, 'Gf', v_gf);
  IF v_eta_x IS NULL OR v_eta_y IS NULL OR v_ff IS NULL OR v_gf IS NULL THEN
    reason := 'naturality_missing_data'; details := v_d; RETURN NEXT; RETURN;
  END IF;
  v_left := nt_compose_in(v_tgt_cat, v_ff, v_eta_y);     -- η_Y ∘ F(f)
  v_right := nt_compose_in(v_tgt_cat, v_eta_x, v_gf);    -- G(f) ∘ η_X
  v_d := v_d || jsonb_build_object('left', v_left, 'right', v_right);
  IF v_left IS NULL OR v_right IS NULL THEN
    reason := 'naturality_composite_missing'; details := v_d; RETURN NEXT;
  ELSIF v_left <> v_right THEN
    reason := 'naturality_square'; details := v_d; RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Every problem of a transformation (the reference's verify_all_laws)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION natural_transformation_problems(p_t UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  t RECORD;
  v_src_cat UUID;
  pr RECORD;
  r RECORD;
  v_eta UUID;
BEGIN
  FOR pr IN SELECT * FROM nt_transformation_typing_problems(p_t) LOOP
    reason := pr.reason; details := pr.details; RETURN NEXT;
    RETURN;                                     -- nothing else is meaningful
  END LOOP;
  SELECT nt.* INTO t FROM natural_transformation nt WHERE nt.id = p_t;
  SELECT fu.source_category_id INTO v_src_cat FROM functor fu WHERE fu.id = t.source_functor_id;

  -- components stored on objects outside the source category
  FOR r IN SELECT c.object_id, c.morphism_id FROM natural_transformation_component c
            JOIN object o ON o.id = c.object_id
           WHERE c.transformation_id = p_t AND o.category_id <> v_src_cat
           ORDER BY c.object_id LOOP
    reason := 'component_unknown_object';
    details := jsonb_build_object('X', r.object_id, 'eta_x', r.morphism_id);
    RETURN NEXT;
  END LOOP;

  -- typing: every object has a component η_X : F(X) → G(X)
  FOR r IN SELECT o.id FROM object o WHERE o.category_id = v_src_cat ORDER BY o.id LOOP
    v_eta := nt_eta(p_t, r.id);
    IF v_eta IS NULL THEN
      reason := 'component_missing';
      details := jsonb_build_object('X', r.id);
      RETURN NEXT;
    ELSE
      FOR pr IN SELECT * FROM nt_component_problems(p_t, r.id, v_eta) LOOP
        reason := pr.reason; details := pr.details; RETURN NEXT;
      END LOOP;
    END IF;
  END LOOP;

  -- naturality: the square of every morphism of the source category
  FOR r IN SELECT mo.id FROM morphism mo WHERE mo.category_id = v_src_cat ORDER BY mo.id LOOP
    FOR pr IN SELECT * FROM nt_square_problems(p_t, r.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
    END LOOP;
  END LOOP;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Logging
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION nt_record(p_t UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  INSERT INTO naturality_violation
    (transformation_id, object_x, object_y, morphism_f, eta_x, eta_y,
     f_mapped_by_F, f_mapped_by_G, left_composite, right_composite, law, details)
  VALUES
    (p_t, (p_details->>'X')::uuid, (p_details->>'Y')::uuid, (p_details->>'f')::uuid,
     (p_details->>'eta_x')::uuid, (p_details->>'eta_y')::uuid,
     (p_details->>'Ff')::uuid, (p_details->>'Gf')::uuid,
     (p_details->>'left')::uuid, (p_details->>'right')::uuid,
     p_reason, p_details);
END;
$$ LANGUAGE plpgsql;

-- All checks of one transformation; logs every problem once, raises in strict
-- mode, returns whether there was none.
CREATE OR REPLACE FUNCTION check_natural_transformation(p_t UUID) RETURNS BOOLEAN AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM natural_transformation WHERE id = p_t) THEN
    RAISE EXCEPTION 'check_natural_transformation: transformation % not found', p_t;
  END IF;
  FOR pr IN SELECT * FROM natural_transformation_problems(p_t) LOOP
    PERFORM nt_record(p_t, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Naturality law violated for NT % (% problem(s))', p_t, n_problems;
  END IF;
  RETURN n_problems = 0;
END;
$$ LANGUAGE plpgsql;

-- Batch re-check (kept for callers of the earlier version; run_all_batch_checks).
CREATE OR REPLACE FUNCTION recheck_naturality(p_transformation_id UUID)
RETURNS VOID AS $$
BEGIN
  PERFORM check_natural_transformation(p_transformation_id);
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
-- Checks a component and every square that became checkable: f in the source
-- category with an endpoint at X whose other endpoint has a component.
CREATE OR REPLACE FUNCTION check_naturality_for_component(p_component_id UUID)
RETURNS VOID AS $$
DECLARE
  c RECORD;
  t RECORD;
  v_src_cat UUID;
  pr RECORD;
  f RECORD;
  n_problems INT := 0;
  v_typed BOOLEAN := TRUE;
  v_first_f UUID;
BEGIN
  SELECT ntc.* INTO c FROM natural_transformation_component ntc WHERE ntc.id = p_component_id;
  IF c.id IS NULL THEN
    RETURN;
  END IF;
  SELECT nt.* INTO t FROM natural_transformation nt WHERE nt.id = c.transformation_id;

  FOR pr IN SELECT * FROM nt_transformation_typing_problems(c.transformation_id) LOOP
    PERFORM nt_record(c.transformation_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
    v_typed := FALSE;
  END LOOP;

  IF v_typed THEN
    SELECT fu.source_category_id INTO v_src_cat FROM functor fu WHERE fu.id = t.source_functor_id;
    FOR pr IN SELECT * FROM nt_component_problems(c.transformation_id, c.object_id, c.morphism_id) LOOP
      PERFORM nt_record(c.transformation_id, pr.reason, pr.details);
      n_problems := n_problems + 1;
      IF pr.reason = 'component_unknown_object' THEN
        v_typed := FALSE;
      END IF;
    END LOOP;
  END IF;

  IF v_typed THEN
    FOR f IN
      SELECT mo.id FROM morphism mo
       WHERE mo.category_id = v_src_cat
         AND ((mo.source_id = c.object_id
               AND EXISTS (SELECT 1 FROM natural_transformation_component x
                            WHERE x.transformation_id = c.transformation_id
                              AND x.object_id = mo.target_id))
           OR (mo.target_id = c.object_id
               AND EXISTS (SELECT 1 FROM natural_transformation_component x
                            WHERE x.transformation_id = c.transformation_id
                              AND x.object_id = mo.source_id)))
       ORDER BY mo.id
    LOOP
      FOR pr IN SELECT * FROM nt_square_problems(c.transformation_id, f.id) LOOP
        PERFORM nt_record(c.transformation_id, pr.reason, pr.details);
        n_problems := n_problems + 1;
        v_first_f := coalesce(v_first_f, f.id);
      END LOOP;
    END LOOP;
  END IF;

  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Naturality law violated for NT % on f=% (% problem(s))',
      c.transformation_id, v_first_f, n_problems;
  END IF;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION trg_check_naturality() RETURNS trigger AS $$
BEGIN
  PERFORM check_naturality_for_component(NEW.id);
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_naturality ON natural_transformation_component;
CREATE TRIGGER trg_check_naturality
AFTER INSERT OR UPDATE ON natural_transformation_component
FOR EACH ROW EXECUTE FUNCTION trg_check_naturality();

CREATE OR REPLACE FUNCTION trg_check_natural_transformation() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM nt_transformation_typing_problems(NEW.id) LOOP
    PERFORM nt_record(NEW.id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Natural transformation % is not well typed (F and G must share source and target)', NEW.id;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_natural_transformation ON natural_transformation;
CREATE TRIGGER trg_check_natural_transformation
AFTER INSERT OR UPDATE ON natural_transformation
FOR EACH ROW EXECUTE FUNCTION trg_check_natural_transformation();

-- ---------------------------------------------------------------------------
-- Writers.  Each refuses, in every mode, input it cannot build a well-typed
-- row from.  Rows inserted directly are checked by the triggers.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION register_natural_transformation(
  p_name TEXT,
  p_source_functor_id UUID,
  p_target_functor_id UUID
) RETURNS UUID AS $$
DECLARE
  f RECORD;
  g RECORD;
  new_id UUID;
BEGIN
  IF p_name IS NULL OR btrim(p_name) = '' THEN
    RAISE EXCEPTION 'register_natural_transformation: transformation_typing (blank name)';
  END IF;
  SELECT fu.* INTO f FROM functor fu WHERE fu.id = p_source_functor_id;
  SELECT fu.* INTO g FROM functor fu WHERE fu.id = p_target_functor_id;
  IF f.id IS NULL OR g.id IS NULL THEN
    RAISE EXCEPTION 'register_natural_transformation: transformation_typing (unknown functor)';
  END IF;
  IF f.source_category_id <> g.source_category_id OR f.target_category_id <> g.target_category_id THEN
    RAISE EXCEPTION 'register_natural_transformation: transformation_typing (F and G must share source and target)';
  END IF;
  INSERT INTO natural_transformation (name, source_functor_id, target_functor_id)
  VALUES (p_name, p_source_functor_id, p_target_functor_id)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Register η_X; refuses an unknown transformation, an ill-typed transformation
-- and an ill-typed component.  The trigger then checks the squares.
CREATE OR REPLACE FUNCTION register_nt_component(
  p_transformation_id UUID,
  p_object_id UUID,
  p_morphism_id UUID
) RETURNS UUID AS $$
DECLARE
  pr RECORD;
  new_id UUID;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM natural_transformation WHERE id = p_transformation_id) THEN
    RAISE EXCEPTION 'register_nt_component: transformation % not found', p_transformation_id;
  END IF;
  FOR pr IN SELECT * FROM nt_transformation_typing_problems(p_transformation_id) LOOP
    RAISE EXCEPTION 'register_nt_component: %', pr.reason;
  END LOOP;
  FOR pr IN SELECT * FROM nt_component_problems(p_transformation_id, p_object_id, p_morphism_id) LOOP
    RAISE EXCEPTION 'register_nt_component: % (%)', pr.reason, pr.details;
  END LOOP;
  INSERT INTO natural_transformation_component
    (transformation_id, object_id, morphism_id)
  VALUES
    (p_transformation_id, p_object_id, p_morphism_id)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;
