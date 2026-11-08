-- ============================================================================
-- Categorical Ledger — Migration 005: Adjunctions (F ⊣ G)
-- ============================================================================
-- Enforces the triangle identities:
--
--   Left:   ε_{F(X)} ∘ F(η_X) = id_{F(X)}      for every object X of C
--   Right:  G(ε_Y)   ∘ η_{G(Y)} = id_{G(Y)}    for every object Y of D
--
-- where:
--   F : C → D  is the left adjoint
--   G : D → C  is the right adjoint
--   η : Id_C ⇒ G∘F  is the unit
--   ε : F∘G ⇒ Id_D  is the counit
--
-- The unit and counit are rows of `natural_transformation` (migration 004), so
-- their naturality squares are enforced there.  Their source/target functors
-- are ordinary `functor` rows; this migration checks that they really are
-- Id_C, G∘F, F∘G and Id_D on every registered object and morphism.
--
-- Composition convention (shared with qbx.db.repositories.add_composition and
-- migrations 002 and 004): composition(left_id = g, right_id = f, result_id = h)
-- records h = g ∘ f — the RIGHT morphism is applied first.  Composites are
-- looked up with nt_compose_in(category, first, second) from migration 004:
-- NULL unless both morphisms lie in the category and are composable,
-- otherwise the recorded composite with the unit laws for identities.
--
-- Phase 1 sprint 14 (acceptance review).  Comparing this checker with the
-- reference qbx.categorical.Adjunction on random data (tests/live_db/
-- test_adjunction_db.py) showed two disagreements, both fixed:
--   * the triangles were composed with nt_compose, which ignores
--     composability: with ε_{F(X)} an identity of the wrong object,
--     ε_{F(X)} ∘ F(η_X) "composed" to F(η_X) and was reported as
--     triangle_left instead of triangle_left_composite_missing;
--   * component typing compared endpoints only, not that η_X is a morphism of
--     C (ε_Y of D).
--
-- Phase 1 sprint 2 rewrite.  The original checker
--   * looked up the right triangle in the wrong order (η_{G(Y)} ∘ G(ε_Y)
--     instead of G(ε_Y) ∘ η_{G(Y)}), so every genuine adjunction was flagged;
--   * did not use the unit laws, so a triangle whose composite involves an
--     identity morphism (not stored in `composition`) was flagged;
--   * silently skipped any object whose component or image was missing, and
--     passed when both the composite and the identity were missing
--     (NULL IS DISTINCT FROM NULL is false);
--   * never checked the categories, the unit/counit functors, or the typing
--     η_X : X → G(F(X)), ε_Y : F(G(Y)) → Y.
-- Neither triangle implies the other, even for natural η and ε
-- (Formal/Adjunction.lean: right_triangle_not_implies_left,
-- left_triangle_not_implies_right), so both are checked for every object.  When
-- every check passes, (η, ε) is a genuine adjunction
-- (Formal/Adjunction.lean: adjunctionOfChecks).
-- ============================================================================

-- ---------------------------------------------------------------------------
-- Tables
-- ---------------------------------------------------------------------------
CREATE TABLE IF NOT EXISTS adjunction (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  left_functor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
  right_functor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
  unit_nt_id UUID NOT NULL REFERENCES natural_transformation(id) ON DELETE CASCADE,
  counit_nt_id UUID NOT NULL REFERENCES natural_transformation(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_adjunction_left ON adjunction (left_functor_id);
CREATE INDEX IF NOT EXISTS idx_adjunction_right ON adjunction (right_functor_id);

-- Laws recorded (column `law`):
--   adjunction_typing          categories of F, G, unit or counit do not fit
--   unit_functor_mismatch      unit source is not Id_C / unit target is not G∘F
--   counit_functor_mismatch    counit source is not F∘G / counit target is not Id_D
--   unit_component_missing     no η_X for an object X of C
--   counit_component_missing   no ε_Y for an object Y of D
--   unit_component_typing      η_X is not a morphism X → G(F(X))
--   counit_component_typing    ε_Y is not a morphism F(G(Y)) → Y
--   triangle_left_missing      F(X), F(η_X), ε_{F(X)} or id_{F(X)} not registered
--   triangle_right_missing     G(Y), G(ε_Y), η_{G(Y)} or id_{G(Y)} not registered
--   triangle_left_composite_missing / triangle_right_composite_missing
--                              the composite is not recorded in `composition`
--   triangle_left / triangle_right
--                              the composite is recorded and is not the identity
CREATE TABLE IF NOT EXISTS adjunction_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  adjunction_id UUID NOT NULL REFERENCES adjunction(id) ON DELETE CASCADE,
  law TEXT NOT NULL,
  object_id UUID,
  left_side UUID,
  right_side UUID,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_adjunction_violation_adj
  ON adjunction_violation (adjunction_id, detected_at DESC);

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- Record a violation; in strict mode abort the transaction afterwards.
CREATE OR REPLACE FUNCTION adj_record_violation(
  p_adjunction_id UUID,
  p_law TEXT,
  p_object_id UUID,
  p_left UUID,
  p_right UUID,
  p_details JSONB
) RETURNS VOID AS $$
DECLARE
  is_strict BOOLEAN;
BEGIN
  is_strict := coalesce(current_setting('qbx.enforcement_mode', true), 'permissive') = 'strict';
  INSERT INTO adjunction_violation
    (adjunction_id, law, object_id, left_side, right_side, details)
  VALUES
    (p_adjunction_id, p_law, p_object_id, p_left, p_right, coalesce(p_details, '{}'::jsonb));
  IF is_strict THEN
    RAISE EXCEPTION 'Adjunction law % violated for adjunction % (object %)',
      p_law, p_adjunction_id, p_object_id;
  END IF;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION adj_fobj(p_functor UUID, p_object UUID)
RETURNS UUID AS $$
  SELECT target_object_id FROM functor_object_map
   WHERE functor_id = p_functor AND source_object_id = p_object;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION adj_fmor(p_functor UUID, p_morphism UUID)
RETURNS UUID AS $$
  SELECT target_morphism_id FROM functor_morphism_map
   WHERE functor_id = p_functor AND source_morphism_id = p_morphism;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION adj_component(p_transformation UUID, p_object UUID)
RETURNS UUID AS $$
  SELECT morphism_id FROM natural_transformation_component
   WHERE transformation_id = p_transformation AND object_id = p_object;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION adj_identity(p_object UUID)
RETURNS UUID AS $$
  SELECT morphism_id FROM identity_morphism WHERE object_id = p_object LIMIT 1;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Batch checker
--
-- 1. Typing:   F : C → D, G : D → C, unit functors C → C, counit functors D → D.
-- 2. Functors: unit source = Id_C and unit target = G∘F on every object and
--              morphism of C; counit source = F∘G and counit target = Id_D on
--              every object and morphism of D.  A missing image is a mismatch.
-- 3. Components: η_X : X → G(F(X)) for every X ∈ C, ε_Y : F(G(Y)) → Y for
--              every Y ∈ D.
-- 4. Triangles: ε_{F(X)} ∘ F(η_X) = id_{F(X)} for every X ∈ C and
--              G(ε_Y) ∘ η_{G(Y)} = id_{G(Y)} for every Y ∈ D.  Missing data
--              and unrecorded composites are violations, never silent passes.
-- Naturality of η and ε is enforced by migration 004 (and re-checked by
-- recheck_naturality in run_all_batch_checks).
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION check_adjunction_triangles(p_adjunction_id UUID)
RETURNS VOID AS $$
DECLARE
  adj RECORD;
  f_src UUID; f_tgt UUID;          -- F : C → D
  g_src UUID; g_tgt UUID;          -- G : D → C
  unit_src_f UUID; unit_tgt_f UUID;
  counit_src_f UUID; counit_tgt_f UUID;
  cat_c UUID; cat_d UUID;
  x_rec RECORD;
  m_rec RECORD;
  fx UUID; gy UUID; gfx UUID; fgy UUID;
  expected UUID; actual_a UUID; actual_b UUID;
  eta_x UUID; f_eta_x UUID; eps_fx UUID;
  eps_y UUID; g_eps_y UUID; eta_gy UUID;
  ident UUID; comp UUID;
  m_src UUID; m_tgt UUID;
BEGIN
  SELECT * INTO adj FROM adjunction WHERE id = p_adjunction_id;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'Adjunction % not found', p_adjunction_id;
  END IF;

  SELECT source_category_id, target_category_id INTO f_src, f_tgt
    FROM functor WHERE id = adj.left_functor_id;
  SELECT source_category_id, target_category_id INTO g_src, g_tgt
    FROM functor WHERE id = adj.right_functor_id;
  SELECT fs.source_category_id, fs.target_category_id INTO unit_src_f, unit_tgt_f
    FROM natural_transformation t JOIN functor fs ON fs.id = t.source_functor_id
   WHERE t.id = adj.unit_nt_id;
  SELECT fs.source_category_id, fs.target_category_id INTO counit_src_f, counit_tgt_f
    FROM natural_transformation t JOIN functor fs ON fs.id = t.source_functor_id
   WHERE t.id = adj.counit_nt_id;
  cat_c := f_src;
  cat_d := f_tgt;

  -- -------------------------------------------------------------------
  -- 1. Typing of the categories
  -- -------------------------------------------------------------------
  IF g_src IS DISTINCT FROM cat_d OR g_tgt IS DISTINCT FROM cat_c
     OR unit_src_f IS DISTINCT FROM cat_c OR unit_tgt_f IS DISTINCT FROM cat_c
     OR counit_src_f IS DISTINCT FROM cat_d OR counit_tgt_f IS DISTINCT FROM cat_d THEN
    PERFORM adj_record_violation(adj.id, 'adjunction_typing', NULL, NULL, NULL,
      jsonb_build_object('F', jsonb_build_array(f_src, f_tgt),
                         'G', jsonb_build_array(g_src, g_tgt),
                         'unit_functors', jsonb_build_array(unit_src_f, unit_tgt_f),
                         'counit_functors', jsonb_build_array(counit_src_f, counit_tgt_f)));
    RETURN;   -- nothing below is meaningful with mismatched categories
  END IF;

  -- -------------------------------------------------------------------
  -- 2. Unit / counit functors are Id_C, G∘F, F∘G, Id_D
  -- -------------------------------------------------------------------
  FOR x_rec IN SELECT o.id FROM object o WHERE o.category_id = cat_c ORDER BY o.id LOOP
    gfx := adj_fobj(adj.right_functor_id, adj_fobj(adj.left_functor_id, x_rec.id));
    actual_a := adj_fobj((SELECT source_functor_id FROM natural_transformation WHERE id = adj.unit_nt_id), x_rec.id);
    actual_b := adj_fobj((SELECT target_functor_id FROM natural_transformation WHERE id = adj.unit_nt_id), x_rec.id);
    IF actual_a IS NULL OR actual_a <> x_rec.id OR gfx IS NULL OR actual_b IS NULL OR actual_b <> gfx THEN
      PERFORM adj_record_violation(adj.id, 'unit_functor_mismatch', x_rec.id, actual_a, actual_b,
        jsonb_build_object('kind', 'object', 'expected_source', x_rec.id, 'expected_target', gfx));
    END IF;
  END LOOP;
  FOR m_rec IN SELECT m.id FROM morphism m WHERE m.category_id = cat_c ORDER BY m.id LOOP
    expected := adj_fmor(adj.right_functor_id, adj_fmor(adj.left_functor_id, m_rec.id));
    actual_a := adj_fmor((SELECT source_functor_id FROM natural_transformation WHERE id = adj.unit_nt_id), m_rec.id);
    actual_b := adj_fmor((SELECT target_functor_id FROM natural_transformation WHERE id = adj.unit_nt_id), m_rec.id);
    IF actual_a IS NULL OR actual_a <> m_rec.id OR expected IS NULL OR actual_b IS NULL OR actual_b <> expected THEN
      PERFORM adj_record_violation(adj.id, 'unit_functor_mismatch', NULL, actual_a, actual_b,
        jsonb_build_object('kind', 'morphism', 'morphism', m_rec.id,
                           'expected_source', m_rec.id, 'expected_target', expected));
    END IF;
  END LOOP;
  FOR x_rec IN SELECT o.id FROM object o WHERE o.category_id = cat_d ORDER BY o.id LOOP
    fgy := adj_fobj(adj.left_functor_id, adj_fobj(adj.right_functor_id, x_rec.id));
    actual_a := adj_fobj((SELECT source_functor_id FROM natural_transformation WHERE id = adj.counit_nt_id), x_rec.id);
    actual_b := adj_fobj((SELECT target_functor_id FROM natural_transformation WHERE id = adj.counit_nt_id), x_rec.id);
    IF fgy IS NULL OR actual_a IS NULL OR actual_a <> fgy OR actual_b IS NULL OR actual_b <> x_rec.id THEN
      PERFORM adj_record_violation(adj.id, 'counit_functor_mismatch', x_rec.id, actual_a, actual_b,
        jsonb_build_object('kind', 'object', 'expected_source', fgy, 'expected_target', x_rec.id));
    END IF;
  END LOOP;
  FOR m_rec IN SELECT m.id FROM morphism m WHERE m.category_id = cat_d ORDER BY m.id LOOP
    expected := adj_fmor(adj.left_functor_id, adj_fmor(adj.right_functor_id, m_rec.id));
    actual_a := adj_fmor((SELECT source_functor_id FROM natural_transformation WHERE id = adj.counit_nt_id), m_rec.id);
    actual_b := adj_fmor((SELECT target_functor_id FROM natural_transformation WHERE id = adj.counit_nt_id), m_rec.id);
    IF expected IS NULL OR actual_a IS NULL OR actual_a <> expected OR actual_b IS NULL OR actual_b <> m_rec.id THEN
      PERFORM adj_record_violation(adj.id, 'counit_functor_mismatch', NULL, actual_a, actual_b,
        jsonb_build_object('kind', 'morphism', 'morphism', m_rec.id,
                           'expected_source', expected, 'expected_target', m_rec.id));
    END IF;
  END LOOP;

  -- -------------------------------------------------------------------
  -- 3 + 4. Components and LEFT TRIANGLE: for X in C
  -- -------------------------------------------------------------------
  FOR x_rec IN SELECT o.id FROM object o WHERE o.category_id = cat_c ORDER BY o.id LOOP
    fx := adj_fobj(adj.left_functor_id, x_rec.id);
    gfx := adj_fobj(adj.right_functor_id, fx);
    eta_x := adj_component(adj.unit_nt_id, x_rec.id);
    IF eta_x IS NULL THEN
      PERFORM adj_record_violation(adj.id, 'unit_component_missing', x_rec.id, NULL, NULL, '{}'::jsonb);
    ELSE
      m_src := NULL; m_tgt := NULL;
      SELECT source_id, target_id INTO m_src, m_tgt FROM morphism
       WHERE id = eta_x AND category_id = cat_c;
      IF m_src IS DISTINCT FROM x_rec.id OR gfx IS NULL OR m_tgt IS DISTINCT FROM gfx THEN
        PERFORM adj_record_violation(adj.id, 'unit_component_typing', x_rec.id, eta_x, NULL,
          jsonb_build_object('actual', jsonb_build_array(m_src, m_tgt),
                             'expected', jsonb_build_array(x_rec.id, gfx)));
      END IF;
    END IF;

    f_eta_x := adj_fmor(adj.left_functor_id, eta_x);
    eps_fx := adj_component(adj.counit_nt_id, fx);
    ident := adj_identity(fx);
    IF fx IS NULL OR eta_x IS NULL OR f_eta_x IS NULL OR eps_fx IS NULL OR ident IS NULL THEN
      PERFORM adj_record_violation(adj.id, 'triangle_left_missing', x_rec.id, NULL, ident,
        jsonb_build_object('F(X)', fx, 'eta_X', eta_x, 'F(eta_X)', f_eta_x,
                           'eps_F(X)', eps_fx, 'id_F(X)', ident));
      CONTINUE;
    END IF;
    comp := nt_compose_in(cat_d, f_eta_x, eps_fx);   -- ε_{F(X)} ∘ F(η_X)
    IF comp IS NULL THEN
      PERFORM adj_record_violation(adj.id, 'triangle_left_composite_missing', x_rec.id, NULL, ident,
        jsonb_build_object('F(X)', fx, 'F(eta_X)', f_eta_x, 'eps_F(X)', eps_fx));
    ELSIF comp <> ident THEN
      PERFORM adj_record_violation(adj.id, 'triangle_left', x_rec.id, comp, ident,
        jsonb_build_object('reason', 'left_triangle_not_identity', 'F(X)', fx));
    END IF;
  END LOOP;

  -- -------------------------------------------------------------------
  -- 3 + 4. Components and RIGHT TRIANGLE: for Y in D
  -- -------------------------------------------------------------------
  FOR x_rec IN SELECT o.id FROM object o WHERE o.category_id = cat_d ORDER BY o.id LOOP
    gy := adj_fobj(adj.right_functor_id, x_rec.id);
    fgy := adj_fobj(adj.left_functor_id, gy);
    eps_y := adj_component(adj.counit_nt_id, x_rec.id);
    IF eps_y IS NULL THEN
      PERFORM adj_record_violation(adj.id, 'counit_component_missing', x_rec.id, NULL, NULL, '{}'::jsonb);
    ELSE
      m_src := NULL; m_tgt := NULL;
      SELECT source_id, target_id INTO m_src, m_tgt FROM morphism
       WHERE id = eps_y AND category_id = cat_d;
      IF fgy IS NULL OR m_src IS DISTINCT FROM fgy OR m_tgt IS DISTINCT FROM x_rec.id THEN
        PERFORM adj_record_violation(adj.id, 'counit_component_typing', x_rec.id, eps_y, NULL,
          jsonb_build_object('actual', jsonb_build_array(m_src, m_tgt),
                             'expected', jsonb_build_array(fgy, x_rec.id)));
      END IF;
    END IF;

    g_eps_y := adj_fmor(adj.right_functor_id, eps_y);
    eta_gy := adj_component(adj.unit_nt_id, gy);
    ident := adj_identity(gy);
    IF gy IS NULL OR eps_y IS NULL OR g_eps_y IS NULL OR eta_gy IS NULL OR ident IS NULL THEN
      PERFORM adj_record_violation(adj.id, 'triangle_right_missing', x_rec.id, NULL, ident,
        jsonb_build_object('G(Y)', gy, 'eps_Y', eps_y, 'G(eps_Y)', g_eps_y,
                           'eta_G(Y)', eta_gy, 'id_G(Y)', ident));
      CONTINUE;
    END IF;
    comp := nt_compose_in(cat_c, eta_gy, g_eps_y);   -- G(ε_Y) ∘ η_{G(Y)}
    IF comp IS NULL THEN
      PERFORM adj_record_violation(adj.id, 'triangle_right_composite_missing', x_rec.id, NULL, ident,
        jsonb_build_object('G(Y)', gy, 'eta_G(Y)', eta_gy, 'G(eps_Y)', g_eps_y));
    ELSIF comp <> ident THEN
      PERFORM adj_record_violation(adj.id, 'triangle_right', x_rec.id, comp, ident,
        jsonb_build_object('reason', 'right_triangle_not_identity', 'G(Y)', gy));
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier: every new or changed adjunction row is verified at once.
-- (Components registered later are covered by check_adjunction_triangles,
-- which run_all_batch_checks in migration 017 calls for every adjunction.)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_adjunction() RETURNS trigger AS $$
BEGIN
  PERFORM check_adjunction_triangles(NEW.id);
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_adjunction ON adjunction;
CREATE TRIGGER trg_check_adjunction
AFTER INSERT OR UPDATE ON adjunction
FOR EACH ROW EXECUTE FUNCTION trg_check_adjunction();

-- ---------------------------------------------------------------------------
-- Convenience: register an adjunction (verified by trg_check_adjunction)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION register_adjunction(
  p_name TEXT,
  p_left_functor UUID,
  p_right_functor UUID,
  p_unit_nt UUID,
  p_counit_nt UUID
) RETURNS UUID AS $$
DECLARE
  new_id UUID;
BEGIN
  INSERT INTO adjunction (name, left_functor_id, right_functor_id,
                          unit_nt_id, counit_nt_id)
  VALUES (p_name, p_left_functor, p_right_functor, p_unit_nt, p_counit_nt)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;
