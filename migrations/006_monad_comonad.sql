-- ============================================================================
-- Categorical Ledger — Migration 006: Monads and Comonads
-- ============================================================================
-- Monad (T, η, μ) on a category C, T : C → C, η : Id_C ⇒ T, μ : T∘T ⇒ T:
--   left_unit:      μ_X ∘ T(η_X)   = id_{T(X)}
--   right_unit:     μ_X ∘ η_{T(X)} = id_{T(X)}
--   associativity:  μ_X ∘ T(μ_X)   = μ_X ∘ μ_{T(X)}
--
-- Comonad (G, ε, δ) on C, G : C → C, ε : G ⇒ Id_C, δ : G ⇒ G∘G (dual):
--   left_counit:     ε_{G(X)} ∘ δ_X = id_{G(X)}
--   right_counit:    G(ε_X) ∘ δ_X   = id_{G(X)}
--   coassociativity: δ_{G(X)} ∘ δ_X = G(δ_X) ∘ δ_X
--
-- (Mathlib names the two unit laws the other way round: its `Monad.left_unit`
-- is η_{T(X)} ≫ μ_X = 𝟙, i.e. right_unit here; see Formal/Monad.lean.)
--
-- Composition convention (migrations 001–005): composition(left_id = g,
-- right_id = f, result_id = h) records h = g ∘ f (f applied first).  Composites
-- are looked up with nt_compose_in(category, first, second) from migration
-- 004: NULL unless both morphisms lie in the category and are composable,
-- otherwise qbx_compose (migration 002: the unit laws for identities, the
-- composition table otherwise).
--
-- Phase 1 sprint 14 (acceptance review).  Comparing these checkers with the
-- reference qbx.categorical.Monad / Comonad on random data
-- (tests/live_db/test_monad_db.py) showed that the laws were composed with
-- qbx_compose, which ignores composability: with an ill-typed component, a
-- composite whose factor is an identity of the wrong object "composed" to the
-- other factor, so left_unit / right_unit / associativity (and the comonad
-- laws) were reported as failing — or passing — where the reference reports
-- *_composite_missing.  Component typing now also requires the component to
-- be a morphism of the category.
--
-- Phase 1 sprint 3 rewrite.  The original checkers
--   * could not run at all: `SELECT eta_x INTO eta_x FROM v_monad_unit_components`
--     (and mu_x, eps_x, delta_x) is an ambiguous column reference in PL/pgSQL,
--     so check_monad_laws / check_comonad_laws — and run_all_batch_checks, as
--     soon as one monad or comonad existed — always raised;
--   * composed the right-hand side of associativity in the wrong order
--     (looked up μ_{T(X)} ∘ μ_X instead of μ_X ∘ μ_{T(X)});
--   * did not use the unit laws, so composites with an identity factor (never
--     stored in `composition`) were reported as violations;
--   * silently skipped objects with missing data, and passed when both sides
--     were missing (NULL IS DISTINCT FROM NULL is false);
--   * never checked that the endofunctor, η, μ (ε, δ) live over the category,
--     that η : Id ⇒ T, μ : T∘T ⇒ T (ε : G ⇒ Id, δ : G ⇒ G∘G), or the typing
--     of the components;
--   * ran only through register_monad / register_comonad (direct inserts were
--     never checked).
-- None of the three laws follows from the other two in general, so all are
-- checked for every object.  When every check passes (and η, μ are natural,
-- which migration 004 enforces) the data is a genuine monad
-- (Formal/Monad.lean: monadOfChecks; dually comonadOfChecks).
-- ============================================================================

CREATE TABLE IF NOT EXISTS monad (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
  endofunctor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
  unit_nt_id UUID REFERENCES natural_transformation(id) ON DELETE SET NULL,
  multiplication_nt_id UUID REFERENCES natural_transformation(id) ON DELETE SET NULL,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS comonad (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
  endofunctor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
  counit_nt_id UUID REFERENCES natural_transformation(id) ON DELETE SET NULL,
  comultiplication_nt_id UUID REFERENCES natural_transformation(id) ON DELETE SET NULL,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS monad_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  monad_id UUID NOT NULL REFERENCES monad(id) ON DELETE CASCADE,
  law TEXT NOT NULL,     -- 'left_unit' | 'right_unit' | 'associativity'
  object_id UUID,
  left_side UUID,
  right_side UUID,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS comonad_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  comonad_id UUID NOT NULL REFERENCES comonad(id) ON DELETE CASCADE,
  law TEXT NOT NULL,     -- 'left_counit' | 'right_counit' | 'coassociativity'
  object_id UUID,
  left_side UUID,
  right_side UUID,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

-- ---------------------------------------------------------------------------
-- Helper views
-- ---------------------------------------------------------------------------
CREATE OR REPLACE VIEW v_monad_unit_components AS
SELECT nt.id AS unit_nt_id,
       ntc.object_id,
       ntc.morphism_id AS eta_x
  FROM natural_transformation nt
  JOIN natural_transformation_component ntc ON ntc.transformation_id = nt.id
 WHERE nt.id IN (SELECT unit_nt_id FROM monad WHERE unit_nt_id IS NOT NULL);

CREATE OR REPLACE VIEW v_monad_mul_components AS
SELECT m.id AS monad_id,
       ntc.object_id,
       ntc.morphism_id AS mu_x
  FROM monad m
  JOIN natural_transformation nt ON nt.id = m.multiplication_nt_id
  JOIN natural_transformation_component ntc ON ntc.transformation_id = nt.id;

CREATE OR REPLACE VIEW v_comonad_counit_components AS
SELECT nt.id AS counit_nt_id,
       ntc.object_id,
       ntc.morphism_id AS eps_x
  FROM natural_transformation nt
  JOIN natural_transformation_component ntc ON ntc.transformation_id = nt.id
 WHERE nt.id IN (SELECT counit_nt_id FROM comonad WHERE counit_nt_id IS NOT NULL);

CREATE OR REPLACE VIEW v_comonad_comult_components AS
SELECT c.id AS comonad_id,
       ntc.object_id,
       ntc.morphism_id AS delta_x
  FROM comonad c
  JOIN natural_transformation nt ON nt.id = c.comultiplication_nt_id
  JOIN natural_transformation_component ntc ON ntc.transformation_id = nt.id;

-- Laws recorded in monad_violation.law:
--   monad_typing                       endofunctor / unit / multiplication not over C
--   unit_missing, multiplication_missing     the transformation row is not set
--   unit_functor_mismatch              unit source is not Id_C or target is not T
--   multiplication_functor_mismatch    multiplication source is not T∘T or target is not T
--   unit_component_missing, multiplication_component_missing
--   unit_component_typing              η_X is not a morphism X → T(X)
--   multiplication_component_typing    μ_X is not a morphism T(T(X)) → T(X)
--   left_unit_missing, right_unit_missing, associativity_missing
--                                      an image, component or identity is not registered
--   left_unit_composite_missing, right_unit_composite_missing,
--   associativity_composite_missing    a composite is not recorded in `composition`
--   left_unit, right_unit, associativity   the law fails
-- comonad_violation.law uses the dual names (comonad_typing, counit_…,
-- comultiplication_…, left_counit, right_counit, coassociativity).

-- ---------------------------------------------------------------------------
-- Helpers (adj_fobj / adj_fmor / adj_component / adj_identity: migration 005)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION monad_record_violation(
  p_monad_id UUID, p_law TEXT, p_object_id UUID,
  p_left UUID, p_right UUID, p_details JSONB
) RETURNS VOID AS $$
BEGIN
  INSERT INTO monad_violation (monad_id, law, object_id, left_side, right_side, details)
  VALUES (p_monad_id, p_law, p_object_id, p_left, p_right, coalesce(p_details, '{}'::jsonb));
  IF coalesce(current_setting('qbx.enforcement_mode', true), 'permissive') = 'strict' THEN
    RAISE EXCEPTION 'Monad law % violated for monad % (object %)', p_law, p_monad_id, p_object_id;
  END IF;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION comonad_record_violation(
  p_comonad_id UUID, p_law TEXT, p_object_id UUID,
  p_left UUID, p_right UUID, p_details JSONB
) RETURNS VOID AS $$
BEGIN
  INSERT INTO comonad_violation (comonad_id, law, object_id, left_side, right_side, details)
  VALUES (p_comonad_id, p_law, p_object_id, p_left, p_right, coalesce(p_details, '{}'::jsonb));
  IF coalesce(current_setting('qbx.enforcement_mode', true), 'permissive') = 'strict' THEN
    RAISE EXCEPTION 'Comonad law % violated for comonad % (object %)', p_law, p_comonad_id, p_object_id;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- Does functor p_actual agree with p_expected_src ↦ (apply p_f1 then p_f2) on
-- object / morphism p_x?  NULL p_f1 means the identity, NULL p_f2 means "only
-- p_f1".  Returns the expected image (NULL when it is not computable).
CREATE OR REPLACE FUNCTION mnd_expected_obj(p_f1 UUID, p_f2 UUID, p_x UUID)
RETURNS UUID AS $$
  SELECT CASE
    WHEN p_f1 IS NULL THEN p_x
    WHEN p_f2 IS NULL THEN adj_fobj(p_f1, p_x)
    ELSE adj_fobj(p_f2, adj_fobj(p_f1, p_x))
  END;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION mnd_expected_mor(p_f1 UUID, p_f2 UUID, p_m UUID)
RETURNS UUID AS $$
  SELECT CASE
    WHEN p_f1 IS NULL THEN p_m
    WHEN p_f2 IS NULL THEN adj_fmor(p_f1, p_m)
    ELSE adj_fmor(p_f2, adj_fmor(p_f1, p_m))
  END;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Monad batch checker
--
-- 1. Typing:   T : C → C; the source and target functors of η and μ are C → C.
-- 2. Functors: η : Id_C ⇒ T and μ : T∘T ⇒ T on every object and morphism of C.
-- 3. Components: η_X : X → T(X), μ_X : T(T(X)) → T(X) for every X.
-- 4. Laws: left_unit, right_unit, associativity for every X.  Missing data and
--    unrecorded composites are violations, never silent passes.
-- Naturality of η and μ is enforced by migration 004.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION check_monad_laws(p_monad_id UUID) RETURNS VOID AS $$
DECLARE
  mo RECORD;
  t_src UUID; t_tgt UUID;
  u_sf UUID; u_tf UUID; m_sf UUID; m_tf UUID;     -- functors of η and μ
  cats UUID[];
  rec RECORD;
  tx UUID; ttx UUID;
  v_eta UUID; v_mu UUID; v_t_eta UUID; v_eta_t UUID; v_t_mu UUID; v_mu_t UUID;
  ident UUID; lhs UUID; rhs UUID;
  a UUID; b UUID; ea UUID; eb UUID;
  m_src UUID; m_tgt UUID;
BEGIN
  SELECT * INTO mo FROM monad WHERE id = p_monad_id;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'Monad % not found', p_monad_id;
  END IF;
  IF mo.unit_nt_id IS NULL THEN
    PERFORM monad_record_violation(mo.id, 'unit_missing', NULL, NULL, NULL, '{}'::jsonb);
  END IF;
  IF mo.multiplication_nt_id IS NULL THEN
    PERFORM monad_record_violation(mo.id, 'multiplication_missing', NULL, NULL, NULL, '{}'::jsonb);
  END IF;
  IF mo.unit_nt_id IS NULL OR mo.multiplication_nt_id IS NULL THEN
    RETURN;
  END IF;

  SELECT source_category_id, target_category_id INTO t_src, t_tgt
    FROM functor WHERE id = mo.endofunctor_id;
  SELECT source_functor_id, target_functor_id INTO u_sf, u_tf
    FROM natural_transformation WHERE id = mo.unit_nt_id;
  SELECT source_functor_id, target_functor_id INTO m_sf, m_tf
    FROM natural_transformation WHERE id = mo.multiplication_nt_id;

  -- 1. Typing
  SELECT array_agg(c) INTO cats FROM (
    SELECT source_category_id AS c FROM functor WHERE id IN (u_sf, u_tf, m_sf, m_tf)
    UNION ALL
    SELECT target_category_id FROM functor WHERE id IN (u_sf, u_tf, m_sf, m_tf)) q;
  IF t_src IS DISTINCT FROM mo.category_id OR t_tgt IS DISTINCT FROM mo.category_id
     OR EXISTS (SELECT 1 FROM unnest(cats) c WHERE c IS DISTINCT FROM mo.category_id) THEN
    PERFORM monad_record_violation(mo.id, 'monad_typing', NULL, NULL, NULL,
      jsonb_build_object('category', mo.category_id,
                         'T', jsonb_build_array(t_src, t_tgt),
                         'functor_categories', to_jsonb(cats)));
    RETURN;
  END IF;

  -- 2. Functors: unit Id ⇒ T, multiplication T∘T ⇒ T
  FOR rec IN SELECT o.id FROM object o WHERE o.category_id = mo.category_id ORDER BY o.id LOOP
    a := adj_fobj(u_sf, rec.id); ea := rec.id;
    b := adj_fobj(u_tf, rec.id); eb := adj_fobj(mo.endofunctor_id, rec.id);
    IF a IS NULL OR a <> ea OR b IS NULL OR eb IS NULL OR b <> eb THEN
      PERFORM monad_record_violation(mo.id, 'unit_functor_mismatch', rec.id, a, b,
        jsonb_build_object('kind', 'object', 'expected_source', ea, 'expected_target', eb));
    END IF;
    a := adj_fobj(m_sf, rec.id); ea := mnd_expected_obj(mo.endofunctor_id, mo.endofunctor_id, rec.id);
    b := adj_fobj(m_tf, rec.id); eb := adj_fobj(mo.endofunctor_id, rec.id);
    IF a IS NULL OR ea IS NULL OR a <> ea OR b IS NULL OR eb IS NULL OR b <> eb THEN
      PERFORM monad_record_violation(mo.id, 'multiplication_functor_mismatch', rec.id, a, b,
        jsonb_build_object('kind', 'object', 'expected_source', ea, 'expected_target', eb));
    END IF;
  END LOOP;
  FOR rec IN SELECT m.id FROM morphism m WHERE m.category_id = mo.category_id ORDER BY m.id LOOP
    a := adj_fmor(u_sf, rec.id); ea := rec.id;
    b := adj_fmor(u_tf, rec.id); eb := adj_fmor(mo.endofunctor_id, rec.id);
    IF a IS NULL OR a <> ea OR b IS NULL OR eb IS NULL OR b <> eb THEN
      PERFORM monad_record_violation(mo.id, 'unit_functor_mismatch', NULL, a, b,
        jsonb_build_object('kind', 'morphism', 'morphism', rec.id,
                           'expected_source', ea, 'expected_target', eb));
    END IF;
    a := adj_fmor(m_sf, rec.id); ea := mnd_expected_mor(mo.endofunctor_id, mo.endofunctor_id, rec.id);
    b := adj_fmor(m_tf, rec.id); eb := adj_fmor(mo.endofunctor_id, rec.id);
    IF a IS NULL OR ea IS NULL OR a <> ea OR b IS NULL OR eb IS NULL OR b <> eb THEN
      PERFORM monad_record_violation(mo.id, 'multiplication_functor_mismatch', NULL, a, b,
        jsonb_build_object('kind', 'morphism', 'morphism', rec.id,
                           'expected_source', ea, 'expected_target', eb));
    END IF;
  END LOOP;

  -- 3 + 4. Components and laws, for every object X
  FOR rec IN SELECT o.id FROM object o WHERE o.category_id = mo.category_id ORDER BY o.id LOOP
    tx := adj_fobj(mo.endofunctor_id, rec.id);
    ttx := adj_fobj(mo.endofunctor_id, tx);
    v_eta := adj_component(mo.unit_nt_id, rec.id);
    v_mu := adj_component(mo.multiplication_nt_id, rec.id);

    IF v_eta IS NULL THEN
      PERFORM monad_record_violation(mo.id, 'unit_component_missing', rec.id, NULL, NULL, '{}'::jsonb);
    ELSE
      m_src := NULL; m_tgt := NULL;
      SELECT source_id, target_id INTO m_src, m_tgt FROM morphism
       WHERE id = v_eta AND category_id = mo.category_id;
      IF m_src IS DISTINCT FROM rec.id OR tx IS NULL OR m_tgt IS DISTINCT FROM tx THEN
        PERFORM monad_record_violation(mo.id, 'unit_component_typing', rec.id, v_eta, NULL,
          jsonb_build_object('actual', jsonb_build_array(m_src, m_tgt),
                             'expected', jsonb_build_array(rec.id, tx)));
      END IF;
    END IF;
    IF v_mu IS NULL THEN
      PERFORM monad_record_violation(mo.id, 'multiplication_component_missing', rec.id, NULL, NULL, '{}'::jsonb);
    ELSE
      m_src := NULL; m_tgt := NULL;
      SELECT source_id, target_id INTO m_src, m_tgt FROM morphism
       WHERE id = v_mu AND category_id = mo.category_id;
      IF ttx IS NULL OR m_src IS DISTINCT FROM ttx OR m_tgt IS DISTINCT FROM tx THEN
        PERFORM monad_record_violation(mo.id, 'multiplication_component_typing', rec.id, v_mu, NULL,
          jsonb_build_object('actual', jsonb_build_array(m_src, m_tgt),
                             'expected', jsonb_build_array(ttx, tx)));
      END IF;
    END IF;

    ident := adj_identity(tx);
    v_t_eta := adj_fmor(mo.endofunctor_id, v_eta);
    v_eta_t := adj_component(mo.unit_nt_id, tx);
    v_t_mu := adj_fmor(mo.endofunctor_id, v_mu);
    v_mu_t := adj_component(mo.multiplication_nt_id, tx);

    -- left_unit: μ_X ∘ T(η_X) = id_{T(X)}
    IF v_mu IS NULL OR v_t_eta IS NULL OR ident IS NULL THEN
      PERFORM monad_record_violation(mo.id, 'left_unit_missing', rec.id, NULL, ident,
        jsonb_build_object('mu_X', v_mu, 'T(eta_X)', v_t_eta, 'id_T(X)', ident));
    ELSE
      lhs := nt_compose_in(mo.category_id, v_t_eta, v_mu);
      IF lhs IS NULL THEN
        PERFORM monad_record_violation(mo.id, 'left_unit_composite_missing', rec.id, NULL, ident,
          jsonb_build_object('mu_X', v_mu, 'T(eta_X)', v_t_eta));
      ELSIF lhs <> ident THEN
        PERFORM monad_record_violation(mo.id, 'left_unit', rec.id, lhs, ident, '{}'::jsonb);
      END IF;
    END IF;

    -- right_unit: μ_X ∘ η_{T(X)} = id_{T(X)}
    IF v_mu IS NULL OR v_eta_t IS NULL OR ident IS NULL THEN
      PERFORM monad_record_violation(mo.id, 'right_unit_missing', rec.id, NULL, ident,
        jsonb_build_object('mu_X', v_mu, 'eta_T(X)', v_eta_t, 'id_T(X)', ident));
    ELSE
      lhs := nt_compose_in(mo.category_id, v_eta_t, v_mu);
      IF lhs IS NULL THEN
        PERFORM monad_record_violation(mo.id, 'right_unit_composite_missing', rec.id, NULL, ident,
          jsonb_build_object('mu_X', v_mu, 'eta_T(X)', v_eta_t));
      ELSIF lhs <> ident THEN
        PERFORM monad_record_violation(mo.id, 'right_unit', rec.id, lhs, ident, '{}'::jsonb);
      END IF;
    END IF;

    -- associativity: μ_X ∘ T(μ_X) = μ_X ∘ μ_{T(X)}
    IF v_mu IS NULL OR v_t_mu IS NULL OR v_mu_t IS NULL THEN
      PERFORM monad_record_violation(mo.id, 'associativity_missing', rec.id, NULL, NULL,
        jsonb_build_object('mu_X', v_mu, 'T(mu_X)', v_t_mu, 'mu_T(X)', v_mu_t));
    ELSE
      lhs := nt_compose_in(mo.category_id, v_t_mu, v_mu);
      rhs := nt_compose_in(mo.category_id, v_mu_t, v_mu);
      IF lhs IS NULL OR rhs IS NULL THEN
        PERFORM monad_record_violation(mo.id, 'associativity_composite_missing', rec.id, lhs, rhs,
          jsonb_build_object('mu_X', v_mu, 'T(mu_X)', v_t_mu, 'mu_T(X)', v_mu_t));
      ELSIF lhs <> rhs THEN
        PERFORM monad_record_violation(mo.id, 'associativity', rec.id, lhs, rhs, '{}'::jsonb);
      END IF;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Comonad batch checker (dual of check_monad_laws)
--   ε : G ⇒ Id_C, ε_X : G(X) → X;  δ : G ⇒ G∘G, δ_X : G(X) → G(G(X)).
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION check_comonad_laws(p_comonad_id UUID) RETURNS VOID AS $$
DECLARE
  co RECORD;
  g_src UUID; g_tgt UUID;
  e_sf UUID; e_tf UUID; d_sf UUID; d_tf UUID;
  cats UUID[];
  rec RECORD;
  gx UUID; ggx UUID;
  v_eps UUID; v_delta UUID; v_eps_g UUID; v_g_eps UUID; v_delta_g UUID; v_g_delta UUID;
  ident UUID; lhs UUID; rhs UUID;
  a UUID; b UUID; ea UUID; eb UUID;
  m_src UUID; m_tgt UUID;
BEGIN
  SELECT * INTO co FROM comonad WHERE id = p_comonad_id;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'Comonad % not found', p_comonad_id;
  END IF;
  IF co.counit_nt_id IS NULL THEN
    PERFORM comonad_record_violation(co.id, 'counit_missing', NULL, NULL, NULL, '{}'::jsonb);
  END IF;
  IF co.comultiplication_nt_id IS NULL THEN
    PERFORM comonad_record_violation(co.id, 'comultiplication_missing', NULL, NULL, NULL, '{}'::jsonb);
  END IF;
  IF co.counit_nt_id IS NULL OR co.comultiplication_nt_id IS NULL THEN
    RETURN;
  END IF;

  SELECT source_category_id, target_category_id INTO g_src, g_tgt
    FROM functor WHERE id = co.endofunctor_id;
  SELECT source_functor_id, target_functor_id INTO e_sf, e_tf
    FROM natural_transformation WHERE id = co.counit_nt_id;
  SELECT source_functor_id, target_functor_id INTO d_sf, d_tf
    FROM natural_transformation WHERE id = co.comultiplication_nt_id;

  SELECT array_agg(c) INTO cats FROM (
    SELECT source_category_id AS c FROM functor WHERE id IN (e_sf, e_tf, d_sf, d_tf)
    UNION ALL
    SELECT target_category_id FROM functor WHERE id IN (e_sf, e_tf, d_sf, d_tf)) q;
  IF g_src IS DISTINCT FROM co.category_id OR g_tgt IS DISTINCT FROM co.category_id
     OR EXISTS (SELECT 1 FROM unnest(cats) c WHERE c IS DISTINCT FROM co.category_id) THEN
    PERFORM comonad_record_violation(co.id, 'comonad_typing', NULL, NULL, NULL,
      jsonb_build_object('category', co.category_id,
                         'G', jsonb_build_array(g_src, g_tgt),
                         'functor_categories', to_jsonb(cats)));
    RETURN;
  END IF;

  -- Functors: counit G ⇒ Id, comultiplication G ⇒ G∘G
  FOR rec IN SELECT o.id FROM object o WHERE o.category_id = co.category_id ORDER BY o.id LOOP
    a := adj_fobj(e_sf, rec.id); ea := adj_fobj(co.endofunctor_id, rec.id);
    b := adj_fobj(e_tf, rec.id); eb := rec.id;
    IF a IS NULL OR ea IS NULL OR a <> ea OR b IS NULL OR b <> eb THEN
      PERFORM comonad_record_violation(co.id, 'counit_functor_mismatch', rec.id, a, b,
        jsonb_build_object('kind', 'object', 'expected_source', ea, 'expected_target', eb));
    END IF;
    a := adj_fobj(d_sf, rec.id); ea := adj_fobj(co.endofunctor_id, rec.id);
    b := adj_fobj(d_tf, rec.id); eb := mnd_expected_obj(co.endofunctor_id, co.endofunctor_id, rec.id);
    IF a IS NULL OR ea IS NULL OR a <> ea OR b IS NULL OR eb IS NULL OR b <> eb THEN
      PERFORM comonad_record_violation(co.id, 'comultiplication_functor_mismatch', rec.id, a, b,
        jsonb_build_object('kind', 'object', 'expected_source', ea, 'expected_target', eb));
    END IF;
  END LOOP;
  FOR rec IN SELECT m.id FROM morphism m WHERE m.category_id = co.category_id ORDER BY m.id LOOP
    a := adj_fmor(e_sf, rec.id); ea := adj_fmor(co.endofunctor_id, rec.id);
    b := adj_fmor(e_tf, rec.id); eb := rec.id;
    IF a IS NULL OR ea IS NULL OR a <> ea OR b IS NULL OR b <> eb THEN
      PERFORM comonad_record_violation(co.id, 'counit_functor_mismatch', NULL, a, b,
        jsonb_build_object('kind', 'morphism', 'morphism', rec.id,
                           'expected_source', ea, 'expected_target', eb));
    END IF;
    a := adj_fmor(d_sf, rec.id); ea := adj_fmor(co.endofunctor_id, rec.id);
    b := adj_fmor(d_tf, rec.id); eb := mnd_expected_mor(co.endofunctor_id, co.endofunctor_id, rec.id);
    IF a IS NULL OR ea IS NULL OR a <> ea OR b IS NULL OR eb IS NULL OR b <> eb THEN
      PERFORM comonad_record_violation(co.id, 'comultiplication_functor_mismatch', NULL, a, b,
        jsonb_build_object('kind', 'morphism', 'morphism', rec.id,
                           'expected_source', ea, 'expected_target', eb));
    END IF;
  END LOOP;

  FOR rec IN SELECT o.id FROM object o WHERE o.category_id = co.category_id ORDER BY o.id LOOP
    gx := adj_fobj(co.endofunctor_id, rec.id);
    ggx := adj_fobj(co.endofunctor_id, gx);
    v_eps := adj_component(co.counit_nt_id, rec.id);
    v_delta := adj_component(co.comultiplication_nt_id, rec.id);

    IF v_eps IS NULL THEN
      PERFORM comonad_record_violation(co.id, 'counit_component_missing', rec.id, NULL, NULL, '{}'::jsonb);
    ELSE
      m_src := NULL; m_tgt := NULL;
      SELECT source_id, target_id INTO m_src, m_tgt FROM morphism
       WHERE id = v_eps AND category_id = co.category_id;
      IF gx IS NULL OR m_src IS DISTINCT FROM gx OR m_tgt IS DISTINCT FROM rec.id THEN
        PERFORM comonad_record_violation(co.id, 'counit_component_typing', rec.id, v_eps, NULL,
          jsonb_build_object('actual', jsonb_build_array(m_src, m_tgt),
                             'expected', jsonb_build_array(gx, rec.id)));
      END IF;
    END IF;
    IF v_delta IS NULL THEN
      PERFORM comonad_record_violation(co.id, 'comultiplication_component_missing', rec.id, NULL, NULL, '{}'::jsonb);
    ELSE
      m_src := NULL; m_tgt := NULL;
      SELECT source_id, target_id INTO m_src, m_tgt FROM morphism
       WHERE id = v_delta AND category_id = co.category_id;
      IF gx IS NULL OR ggx IS NULL OR m_src IS DISTINCT FROM gx OR m_tgt IS DISTINCT FROM ggx THEN
        PERFORM comonad_record_violation(co.id, 'comultiplication_component_typing', rec.id, v_delta, NULL,
          jsonb_build_object('actual', jsonb_build_array(m_src, m_tgt),
                             'expected', jsonb_build_array(gx, ggx)));
      END IF;
    END IF;

    ident := adj_identity(gx);
    v_eps_g := adj_component(co.counit_nt_id, gx);
    v_g_eps := adj_fmor(co.endofunctor_id, v_eps);
    v_delta_g := adj_component(co.comultiplication_nt_id, gx);
    v_g_delta := adj_fmor(co.endofunctor_id, v_delta);

    -- left_counit: ε_{G(X)} ∘ δ_X = id_{G(X)}
    IF v_delta IS NULL OR v_eps_g IS NULL OR ident IS NULL THEN
      PERFORM comonad_record_violation(co.id, 'left_counit_missing', rec.id, NULL, ident,
        jsonb_build_object('delta_X', v_delta, 'eps_G(X)', v_eps_g, 'id_G(X)', ident));
    ELSE
      lhs := nt_compose_in(co.category_id, v_delta, v_eps_g);
      IF lhs IS NULL THEN
        PERFORM comonad_record_violation(co.id, 'left_counit_composite_missing', rec.id, NULL, ident,
          jsonb_build_object('delta_X', v_delta, 'eps_G(X)', v_eps_g));
      ELSIF lhs <> ident THEN
        PERFORM comonad_record_violation(co.id, 'left_counit', rec.id, lhs, ident, '{}'::jsonb);
      END IF;
    END IF;

    -- right_counit: G(ε_X) ∘ δ_X = id_{G(X)}
    IF v_delta IS NULL OR v_g_eps IS NULL OR ident IS NULL THEN
      PERFORM comonad_record_violation(co.id, 'right_counit_missing', rec.id, NULL, ident,
        jsonb_build_object('delta_X', v_delta, 'G(eps_X)', v_g_eps, 'id_G(X)', ident));
    ELSE
      lhs := nt_compose_in(co.category_id, v_delta, v_g_eps);
      IF lhs IS NULL THEN
        PERFORM comonad_record_violation(co.id, 'right_counit_composite_missing', rec.id, NULL, ident,
          jsonb_build_object('delta_X', v_delta, 'G(eps_X)', v_g_eps));
      ELSIF lhs <> ident THEN
        PERFORM comonad_record_violation(co.id, 'right_counit', rec.id, lhs, ident, '{}'::jsonb);
      END IF;
    END IF;

    -- coassociativity: δ_{G(X)} ∘ δ_X = G(δ_X) ∘ δ_X
    IF v_delta IS NULL OR v_delta_g IS NULL OR v_g_delta IS NULL THEN
      PERFORM comonad_record_violation(co.id, 'coassociativity_missing', rec.id, NULL, NULL,
        jsonb_build_object('delta_X', v_delta, 'delta_G(X)', v_delta_g, 'G(delta_X)', v_g_delta));
    ELSE
      lhs := nt_compose_in(co.category_id, v_delta, v_delta_g);
      rhs := nt_compose_in(co.category_id, v_delta, v_g_delta);
      IF lhs IS NULL OR rhs IS NULL THEN
        PERFORM comonad_record_violation(co.id, 'coassociativity_composite_missing', rec.id, lhs, rhs,
          jsonb_build_object('delta_X', v_delta, 'delta_G(X)', v_delta_g, 'G(delta_X)', v_g_delta));
      ELSIF lhs <> rhs THEN
        PERFORM comonad_record_violation(co.id, 'coassociativity', rec.id, lhs, rhs, '{}'::jsonb);
      END IF;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier: every new or changed monad / comonad row is verified.
-- (Components registered later are covered by run_all_batch_checks, 017.)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_monad() RETURNS trigger AS $$
BEGIN
  PERFORM check_monad_laws(NEW.id);
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_monad ON monad;
CREATE TRIGGER trg_check_monad
AFTER INSERT OR UPDATE ON monad
FOR EACH ROW EXECUTE FUNCTION trg_check_monad();

CREATE OR REPLACE FUNCTION trg_check_comonad() RETURNS trigger AS $$
BEGIN
  PERFORM check_comonad_laws(NEW.id);
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_comonad ON comonad;
CREATE TRIGGER trg_check_comonad
AFTER INSERT OR UPDATE ON comonad
FOR EACH ROW EXECUTE FUNCTION trg_check_comonad();

-- ---------------------------------------------------------------------------
-- Convenience wrappers (verified by the triggers above)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION register_monad(
  p_name TEXT, p_category UUID, p_endofunctor UUID,
  p_unit UUID, p_mult UUID
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  INSERT INTO monad (name, category_id, endofunctor_id, unit_nt_id, multiplication_nt_id)
  VALUES (p_name, p_category, p_endofunctor, p_unit, p_mult)
  RETURNING id INTO new_id;
  RETURN new_id;
END; $$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION register_comonad(
  p_name TEXT, p_category UUID, p_endofunctor UUID,
  p_counit UUID, p_comult UUID
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  INSERT INTO comonad (name, category_id, endofunctor_id, counit_nt_id, comultiplication_nt_id)
  VALUES (p_name, p_category, p_endofunctor, p_counit, p_comult)
  RETURNING id INTO new_id;
  RETURN new_id;
END; $$ LANGUAGE plpgsql;
