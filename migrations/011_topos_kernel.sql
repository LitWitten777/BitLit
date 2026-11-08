-- ============================================================================
-- Categorical Ledger — Migration 011: Topos Kernel (subobject classifier)
-- ============================================================================
-- Minimal topos structure: a subobject classifier Ω with a distinguished
-- element true : 1 → Ω, and for every monomorphism m : U → X a unique
-- characteristic morphism χ_m : X → Ω such that the following is a pullback:
--
--     U --!-> 1
--     |       |
--     m       true
--     |       |
--     v       v
--     X --χ-> Ω
--
-- Recording.  subobject_classifier (one per category): Ω and true; the
-- terminal object 1 is the source of true.  subobject: a morphism registered
-- as a monomorphism into subobject_of_object.  characteristic_morphism: the χ
-- registered for a subobject (at most one, never replaced).  truth_value: a
-- named global element 1 → Ω (morphism_id, optional).
--
-- Checks.  Every check logs to topos_violation (column reason, keyed by the
-- category) and raises only when qbx.enforcement_mode = 'strict'.
--   structure (write time and batch)
--     classifier_typing      Ω is not an object of the category, or true is
--                            missing, not in the category, or does not end at
--                            Ω (details: omega, truth)
--     subobject_typing       the morphism is not in the subobject's category or
--                            does not end at subobject_of_object (details:
--                            mono, object)
--     characteristic_typing  the category has no classifier, or χ is not a
--                            morphism X → Ω of the category, X the subobject's
--                            object (details: mono, chi)
--     truth_value_typing     the recorded morphism is not 1 → Ω in the category
--                            (details: name, morphism)
--   batch only (subobject_classifier_problems, check_subobject_classifier,
--   run_all_batch_checks); the universal checks run only when the classifier
--   is well typed and 1 passes the terminal check
--     terminal_existence     an object Z with no morphism Z → 1 (details: object)
--     terminal_uniqueness    an object Z with several (details: object, count)
--     not_mono               a registered subobject m : U → X with g ≠ h : Z → U
--                            and m ∘ g = m ∘ h (details: mono, count = the
--                            number of such unordered pairs)
--     pullback_not_commuting the square of a registered χ does not commute:
--                            χ ∘ m ≠ true ∘ !_U, or a composite is not recorded
--                            (details: mono, chi)
--     pullback_existence     f : Z → X with χ ∘ f = true ∘ !_Z but no g : Z → U
--                            with m ∘ g = f (details: mono, chi, f)
--     pullback_uniqueness    ... more than one such g (details: ..., count)
--   the classifier property, for every morphism m of the category that is a
--   monomorphism on the recorded data (registered or not)
--     unclassified_mono      no χ : X → Ω passes the pullback check
--                            (details: mono)
--     characteristic_not_unique  several do (details: mono, count)
-- Composites are read with qbx_compose (unit laws for recorded identities, the
-- composition table otherwise); the checks run against the recorded morphisms
-- and composites: a pass means "consistent with a subobject classifier on the
-- recorded data".
--
-- Formal backing (Formal/Topos.lean): the pullback check is exactly Mathlib's
-- IsPullback (isPullback_iff_pullbackCheck); "every mono has exactly one χ
-- passing it" is exactly Mathlib's Classifier (classifierCheck_of_classifier,
-- Classifier.ofCheck, hasClassifier_iff_exists_check); existence and
-- uniqueness are both needed (classifier_existence_not_sufficient,
-- classifier_uniqueness_not_sufficient); χ(id_X) = true ∘ !_X (chi_id_eq); a
-- nonempty partial order has a classifier iff it has one element
-- (partialOrder_hasClassifier_iff), which the live tests use as an oracle.
--
-- Phase 1 sprint 8 rewrite.  Running the original on PostgreSQL 16 showed:
--   * a classifier whose Ω and true do not fit (true : X → Ω' with Ω = X) and
--     a classifier with no true at all were accepted;
--   * register_subobject accepted a morphism that is not a monomorphism, a
--     morphism of another category, and a subobject_of_object that is not the
--     morphism's target;
--   * attach_characteristic accepted any morphism as χ (not X → Ω) and its
--     ON CONFLICT ... DO UPDATE silently replaced an attached χ;
--   * nothing checked the pullback square, the uniqueness of χ or that 1 is
--     terminal; there was no violation table and nothing in
--     run_all_batch_checks.
-- ============================================================================

CREATE TABLE IF NOT EXISTS subobject_classifier (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
  omega_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  true_morphism_id UUID REFERENCES morphism(id),  -- 1 → Ω
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now(),
  UNIQUE (category_id)
);

CREATE TABLE IF NOT EXISTS subobject (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
  mono_morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
  subobject_of_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_subobject_cat ON subobject (category_id, mono_morphism_id);

CREATE TABLE IF NOT EXISTS characteristic_morphism (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  subobject_id UUID NOT NULL REFERENCES subobject(id) ON DELETE CASCADE,
  morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  UNIQUE (subobject_id)
);

CREATE TABLE IF NOT EXISTS truth_value (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  classifier_id UUID NOT NULL REFERENCES subobject_classifier(id) ON DELETE CASCADE,
  name TEXT NOT NULL,
  data JSONB DEFAULT '{}'::jsonb,
  UNIQUE (classifier_id, name)
);

-- Upgrade path for a database holding the original 011 table: a truth value
-- may now name its global element 1 → Ω.
ALTER TABLE truth_value ADD COLUMN IF NOT EXISTS
  morphism_id UUID REFERENCES morphism(id) ON DELETE CASCADE;

CREATE TABLE IF NOT EXISTS topos_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
  reason TEXT,            -- see the header for the list of reasons
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_topos_violation_cat
  ON topos_violation (category_id, detected_at DESC);

-- ---------------------------------------------------------------------------
-- Structure problems (pure)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION topos_classifier_typing_problems(p_cls UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  o RECORD;
  t RECORD;
BEGIN
  SELECT sc.* INTO c FROM subobject_classifier sc WHERE sc.id = p_cls;
  IF c.id IS NULL THEN
    RETURN;
  END IF;
  SELECT ob.* INTO o FROM object ob WHERE ob.id = c.omega_object_id;
  SELECT mo.* INTO t FROM morphism mo WHERE mo.id = c.true_morphism_id;
  IF o.category_id IS DISTINCT FROM c.category_id
     OR t.id IS NULL
     OR t.category_id IS DISTINCT FROM c.category_id
     OR t.target_id IS DISTINCT FROM c.omega_object_id THEN
    reason := 'classifier_typing';
    details := jsonb_build_object('omega', c.omega_object_id, 'truth', c.true_morphism_id);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION topos_subobject_typing_problems(p_sub UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  s RECORD;
  m RECORD;
BEGIN
  SELECT so.* INTO s FROM subobject so WHERE so.id = p_sub;
  IF s.id IS NULL THEN
    RETURN;
  END IF;
  SELECT mo.* INTO m FROM morphism mo WHERE mo.id = s.mono_morphism_id;
  IF m.category_id IS DISTINCT FROM s.category_id
     OR m.target_id IS DISTINCT FROM s.subobject_of_object_id THEN
    reason := 'subobject_typing';
    details := jsonb_build_object('mono', s.mono_morphism_id, 'object', s.subobject_of_object_id);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION topos_characteristic_typing_problems(p_char UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  ch RECORD;
  s RECORD;
  c RECORD;
  x RECORD;
BEGIN
  SELECT cm.* INTO ch FROM characteristic_morphism cm WHERE cm.id = p_char;
  IF ch.id IS NULL THEN
    RETURN;
  END IF;
  SELECT so.* INTO s FROM subobject so WHERE so.id = ch.subobject_id;
  SELECT sc.* INTO c FROM subobject_classifier sc WHERE sc.category_id = s.category_id;
  SELECT mo.* INTO x FROM morphism mo WHERE mo.id = ch.morphism_id;
  IF c.id IS NULL
     OR x.category_id IS DISTINCT FROM s.category_id
     OR x.source_id IS DISTINCT FROM s.subobject_of_object_id
     OR x.target_id IS DISTINCT FROM c.omega_object_id THEN
    reason := 'characteristic_typing';
    details := jsonb_build_object('mono', s.mono_morphism_id, 'chi', ch.morphism_id);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION topos_truth_value_typing_problems(p_tv UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  tv RECORD;
  c RECORD;
  t RECORD;
  x RECORD;
BEGIN
  SELECT v.* INTO tv FROM truth_value v WHERE v.id = p_tv;
  IF tv.id IS NULL OR tv.morphism_id IS NULL THEN
    RETURN;
  END IF;
  SELECT sc.* INTO c FROM subobject_classifier sc WHERE sc.id = tv.classifier_id;
  SELECT mo.* INTO t FROM morphism mo WHERE mo.id = c.true_morphism_id;
  SELECT mo.* INTO x FROM morphism mo WHERE mo.id = tv.morphism_id;
  IF t.id IS NULL
     OR x.category_id IS DISTINCT FROM c.category_id
     OR x.source_id IS DISTINCT FROM t.source_id
     OR x.target_id IS DISTINCT FROM c.omega_object_id THEN
    reason := 'truth_value_typing';
    details := jsonb_build_object('name', tv.name, 'morphism', tv.morphism_id);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Universal checks (pure)
-- ---------------------------------------------------------------------------
-- The unique morphism Z → p_term of the category (NULL if none or several).
CREATE OR REPLACE FUNCTION topos_bang(p_cat UUID, p_obj UUID, p_term UUID) RETURNS UUID AS $$
  SELECT CASE WHEN count(*) = 1 THEN min(mo.id::text)::uuid END
    FROM morphism mo
   WHERE mo.category_id = p_cat AND mo.source_id = p_obj AND mo.target_id = p_term;
$$ LANGUAGE sql STABLE;

-- Number of unordered pairs g ≠ h : Z → source(m) with m ∘ g = m ∘ h (recorded).
CREATE OR REPLACE FUNCTION topos_mono_failures(p_mono UUID) RETURNS INT AS $$
DECLARE
  m RECORD;
  v_n INT;
BEGIN
  SELECT mo.* INTO m FROM morphism mo WHERE mo.id = p_mono;
  IF m.id IS NULL THEN
    RETURN 0;
  END IF;
  WITH c AS (
    SELECT g.id, g.source_id, qbx_compose(g.id, p_mono) AS r
      FROM morphism g
     WHERE g.category_id = m.category_id AND g.target_id = m.source_id
  )
  SELECT count(*) INTO v_n
    FROM c c1 JOIN c c2 ON c1.source_id = c2.source_id AND c1.id < c2.id
   WHERE c1.r IS NOT NULL AND c1.r = c2.r;
  RETURN v_n;
END;
$$ LANGUAGE plpgsql STABLE;

-- The pullback check of χ for m (classifier p_cls, assumed well typed with a
-- terminal source of true).  One row per failure.
CREATE OR REPLACE FUNCTION topos_pullback_problems(p_cls UUID, p_mono UUID, p_chi UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  t RECORD;
  m RECORD;
  f RECORD;
  v_a UUID;
  v_b UUID;
  v_n INT;
  v_details JSONB;
BEGIN
  SELECT sc.* INTO c FROM subobject_classifier sc WHERE sc.id = p_cls;
  SELECT mo.* INTO t FROM morphism mo WHERE mo.id = c.true_morphism_id;
  SELECT mo.* INTO m FROM morphism mo WHERE mo.id = p_mono;
  v_details := jsonb_build_object('mono', p_mono, 'chi', p_chi);

  v_a := qbx_compose(p_mono, p_chi);
  v_b := qbx_compose(topos_bang(c.category_id, m.source_id, t.source_id), t.id);
  IF v_a IS NULL OR v_b IS NULL OR v_a <> v_b THEN
    reason := 'pullback_not_commuting'; details := v_details; RETURN NEXT;
  END IF;

  FOR f IN SELECT mo.* FROM morphism mo
            WHERE mo.category_id = c.category_id AND mo.target_id = m.target_id
            ORDER BY mo.id LOOP
    v_a := qbx_compose(f.id, p_chi);
    v_b := qbx_compose(topos_bang(c.category_id, f.source_id, t.source_id), t.id);
    CONTINUE WHEN v_a IS NULL OR v_b IS NULL OR v_a <> v_b;
    SELECT count(*) INTO v_n FROM morphism g
     WHERE g.category_id = c.category_id
       AND g.source_id = f.source_id AND g.target_id = m.source_id
       AND qbx_compose(g.id, p_mono) = f.id;
    IF v_n = 0 THEN
      reason := 'pullback_existence';
      details := v_details || jsonb_build_object('f', f.id); RETURN NEXT;
    ELSIF v_n > 1 THEN
      reason := 'pullback_uniqueness';
      details := v_details || jsonb_build_object('f', f.id, 'count', v_n); RETURN NEXT;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql STABLE;

-- Does χ pass the pullback check for m?  (Stops at the first failure.)
CREATE OR REPLACE FUNCTION topos_pullback_ok(p_cls UUID, p_mono UUID, p_chi UUID)
RETURNS BOOLEAN AS $$
DECLARE
  c RECORD;
  t RECORD;
  m RECORD;
  f RECORD;
  v_a UUID;
  v_b UUID;
BEGIN
  SELECT sc.* INTO c FROM subobject_classifier sc WHERE sc.id = p_cls;
  SELECT mo.* INTO t FROM morphism mo WHERE mo.id = c.true_morphism_id;
  SELECT mo.* INTO m FROM morphism mo WHERE mo.id = p_mono;
  v_a := qbx_compose(p_mono, p_chi);
  v_b := qbx_compose(topos_bang(c.category_id, m.source_id, t.source_id), t.id);
  IF v_a IS NULL OR v_b IS NULL OR v_a <> v_b THEN
    RETURN FALSE;
  END IF;
  FOR f IN SELECT mo.* FROM morphism mo
            WHERE mo.category_id = c.category_id AND mo.target_id = m.target_id LOOP
    v_a := qbx_compose(f.id, p_chi);
    v_b := qbx_compose(topos_bang(c.category_id, f.source_id, t.source_id), t.id);
    CONTINUE WHEN v_a IS NULL OR v_b IS NULL OR v_a <> v_b;
    IF (SELECT count(*) FROM morphism g
         WHERE g.category_id = c.category_id
           AND g.source_id = f.source_id AND g.target_id = m.source_id
           AND qbx_compose(g.id, p_mono) = f.id) <> 1 THEN
      RETURN FALSE;
    END IF;
  END LOOP;
  RETURN TRUE;
END;
$$ LANGUAGE plpgsql STABLE;

-- Is the classifier well typed with a terminal source of true?
CREATE OR REPLACE FUNCTION topos_classifier_ready(p_cls UUID) RETURNS BOOLEAN AS $$
DECLARE
  c RECORD;
  t RECORD;
BEGIN
  IF EXISTS (SELECT 1 FROM topos_classifier_typing_problems(p_cls)) THEN
    RETURN FALSE;
  END IF;
  SELECT sc.* INTO c FROM subobject_classifier sc WHERE sc.id = p_cls;
  SELECT mo.* INTO t FROM morphism mo WHERE mo.id = c.true_morphism_id;
  RETURN NOT EXISTS (
    SELECT 1 FROM object ob
     WHERE ob.category_id = c.category_id
       AND (SELECT count(*) FROM morphism mo
             WHERE mo.category_id = c.category_id AND mo.source_id = ob.id
               AND mo.target_id = t.source_id) <> 1);
END;
$$ LANGUAGE plpgsql STABLE;

-- The characteristic morphisms X → Ω passing the pullback check for m.
CREATE OR REPLACE FUNCTION topos_characteristics(p_cls UUID, p_mono UUID)
RETURNS TABLE(chi UUID) AS $$
  SELECT x.id FROM subobject_classifier c
    JOIN morphism m ON m.id = p_mono
    JOIN morphism x ON x.category_id = c.category_id AND x.source_id = m.target_id
                   AND x.target_id = c.omega_object_id
   WHERE c.id = p_cls AND topos_pullback_ok(p_cls, p_mono, x.id)
   ORDER BY x.id;
$$ LANGUAGE sql STABLE;

-- The unique characteristic morphism of p_mono in p_cat (NULL when the
-- category has no usable classifier, or when there is none or several).
CREATE OR REPLACE FUNCTION classify_mono(p_cat UUID, p_mono UUID) RETURNS UUID AS $$
DECLARE
  c RECORD;
  v_ids UUID[];
BEGIN
  SELECT sc.* INTO c FROM subobject_classifier sc WHERE sc.category_id = p_cat;
  IF c.id IS NULL OR NOT topos_classifier_ready(c.id) THEN
    RETURN NULL;
  END IF;
  SELECT array_agg(chi) INTO v_ids FROM topos_characteristics(c.id, p_mono);
  IF coalesce(array_length(v_ids, 1), 0) = 1 THEN
    RETURN v_ids[1];
  END IF;
  RETURN NULL;
END;
$$ LANGUAGE plpgsql STABLE;

-- Every problem of a subobject classifier.
CREATE OR REPLACE FUNCTION subobject_classifier_problems(p_cls UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  t RECORD;
  ob RECORD;
  s RECORD;
  ch RECORD;
  tv RECORD;
  m RECORD;
  pr RECORD;
  v_n INT;
  v_ready BOOLEAN := TRUE;
  v_sub_ok BOOLEAN;
  v_chi_ok BOOLEAN;
BEGIN
  SELECT sc.* INTO c FROM subobject_classifier sc WHERE sc.id = p_cls;
  IF c.id IS NULL THEN
    reason := 'missing_classifier';
    details := jsonb_build_object('classifier', p_cls);
    RETURN NEXT;
    RETURN;
  END IF;

  FOR pr IN SELECT * FROM topos_classifier_typing_problems(p_cls) LOOP
    reason := pr.reason; details := pr.details; RETURN NEXT;
    RETURN;                                -- no terminal object to check against
  END LOOP;
  SELECT mo.* INTO t FROM morphism mo WHERE mo.id = c.true_morphism_id;

  -- 1 = source(true) is terminal
  FOR ob IN SELECT o.id FROM object o WHERE o.category_id = c.category_id ORDER BY o.id LOOP
    SELECT count(*) INTO v_n FROM morphism mo
     WHERE mo.category_id = c.category_id AND mo.source_id = ob.id AND mo.target_id = t.source_id;
    IF v_n = 0 THEN
      reason := 'terminal_existence';
      details := jsonb_build_object('object', ob.id); RETURN NEXT;
      v_ready := FALSE;
    ELSIF v_n > 1 THEN
      reason := 'terminal_uniqueness';
      details := jsonb_build_object('object', ob.id, 'count', v_n); RETURN NEXT;
      v_ready := FALSE;
    END IF;
  END LOOP;

  -- truth values
  FOR tv IN SELECT v.id FROM truth_value v WHERE v.classifier_id = p_cls ORDER BY v.name LOOP
    FOR pr IN SELECT * FROM topos_truth_value_typing_problems(tv.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
    END LOOP;
  END LOOP;

  -- registered subobjects and their characteristic morphisms
  FOR s IN SELECT so.* FROM subobject so WHERE so.category_id = c.category_id ORDER BY so.id LOOP
    v_sub_ok := TRUE;
    FOR pr IN SELECT * FROM topos_subobject_typing_problems(s.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
      v_sub_ok := FALSE;
    END LOOP;
    IF v_sub_ok THEN
      v_n := topos_mono_failures(s.mono_morphism_id);
      IF v_n > 0 THEN
        reason := 'not_mono';
        details := jsonb_build_object('mono', s.mono_morphism_id, 'count', v_n); RETURN NEXT;
      END IF;
    END IF;
    FOR ch IN SELECT cm.* FROM characteristic_morphism cm WHERE cm.subobject_id = s.id LOOP
      v_chi_ok := TRUE;
      FOR pr IN SELECT * FROM topos_characteristic_typing_problems(ch.id) LOOP
        reason := pr.reason; details := pr.details; RETURN NEXT;
        v_chi_ok := FALSE;
      END LOOP;
      IF v_sub_ok AND v_chi_ok AND v_ready THEN
        FOR pr IN SELECT * FROM topos_pullback_problems(p_cls, s.mono_morphism_id,
                                                        ch.morphism_id) LOOP
          reason := pr.reason; details := pr.details; RETURN NEXT;
        END LOOP;
      END IF;
    END LOOP;
  END LOOP;

  -- the classifier property: every recorded monomorphism has exactly one χ
  IF v_ready THEN
    FOR m IN SELECT mo.* FROM morphism mo WHERE mo.category_id = c.category_id ORDER BY mo.id LOOP
      CONTINUE WHEN topos_mono_failures(m.id) > 0;
      SELECT count(*) INTO v_n FROM topos_characteristics(p_cls, m.id);
      IF v_n = 0 THEN
        reason := 'unclassified_mono';
        details := jsonb_build_object('mono', m.id); RETURN NEXT;
      ELSIF v_n > 1 THEN
        reason := 'characteristic_not_unique';
        details := jsonb_build_object('mono', m.id, 'count', v_n); RETURN NEXT;
      END IF;
    END LOOP;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION topos_record(p_cat UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  INSERT INTO topos_violation (category_id, reason, details)
  VALUES (p_cat, p_reason, p_details);
END;
$$ LANGUAGE plpgsql;

-- All checks of one classifier; logs every problem, raises in strict mode.
CREATE OR REPLACE FUNCTION check_subobject_classifier(p_cls UUID) RETURNS BOOLEAN AS $$
DECLARE
  c RECORD;
  pr RECORD;
  n_problems INT := 0;
BEGIN
  SELECT sc.* INTO c FROM subobject_classifier sc WHERE sc.id = p_cls;
  IF c.id IS NULL THEN
    RAISE EXCEPTION 'check_subobject_classifier: classifier % not found', p_cls;
  END IF;
  FOR pr IN SELECT * FROM subobject_classifier_problems(p_cls) LOOP
    PERFORM topos_record(c.category_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Subobject classifier % violates its laws (% problem(s))', p_cls, n_problems;
  END IF;
  RETURN n_problems = 0;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_subobject_classifier() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM topos_classifier_typing_problems(NEW.id) LOOP
    PERFORM topos_record(NEW.category_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Subobject classifier % is not well typed', NEW.id;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_subobject_classifier ON subobject_classifier;
CREATE TRIGGER trg_check_subobject_classifier
AFTER INSERT OR UPDATE ON subobject_classifier
FOR EACH ROW EXECUTE FUNCTION trg_check_subobject_classifier();

CREATE OR REPLACE FUNCTION trg_check_subobject() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM topos_subobject_typing_problems(NEW.id) LOOP
    PERFORM topos_record(NEW.category_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Subobject % is not well typed', NEW.id;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_subobject ON subobject;
CREATE TRIGGER trg_check_subobject
AFTER INSERT OR UPDATE ON subobject
FOR EACH ROW EXECUTE FUNCTION trg_check_subobject();

CREATE OR REPLACE FUNCTION trg_check_characteristic() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
  v_cat UUID;
BEGIN
  SELECT so.category_id INTO v_cat FROM subobject so WHERE so.id = NEW.subobject_id;
  FOR pr IN SELECT * FROM topos_characteristic_typing_problems(NEW.id) LOOP
    PERFORM topos_record(v_cat, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Characteristic morphism % is not well typed', NEW.id;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_characteristic ON characteristic_morphism;
CREATE TRIGGER trg_check_characteristic
AFTER INSERT OR UPDATE ON characteristic_morphism
FOR EACH ROW EXECUTE FUNCTION trg_check_characteristic();

CREATE OR REPLACE FUNCTION trg_check_truth_value() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
  v_cat UUID;
BEGIN
  SELECT sc.category_id INTO v_cat FROM subobject_classifier sc WHERE sc.id = NEW.classifier_id;
  FOR pr IN SELECT * FROM topos_truth_value_typing_problems(NEW.id) LOOP
    PERFORM topos_record(v_cat, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Truth value % is not a global element 1 → Ω', NEW.name;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_truth_value ON truth_value;
CREATE TRIGGER trg_check_truth_value
AFTER INSERT OR UPDATE ON truth_value
FOR EACH ROW EXECUTE FUNCTION trg_check_truth_value();

-- ---------------------------------------------------------------------------
-- Writers.  Each refuses, in every mode, input it cannot build a valid row
-- from, and never replaces an existing row by a different one.  Rows inserted
-- directly are checked by the triggers.
-- ---------------------------------------------------------------------------
-- Register (Ω, true) as the classifier of p_cat.
CREATE OR REPLACE FUNCTION register_subobject_classifier(
  p_cat UUID, p_omega UUID, p_true UUID
) RETURNS UUID AS $$
DECLARE
  ex RECORD;
  o RECORD;
  t RECORD;
  new_id UUID;
BEGIN
  SELECT sc.* INTO ex FROM subobject_classifier sc WHERE sc.category_id = p_cat;
  IF ex.id IS NOT NULL THEN
    IF ex.omega_object_id = p_omega AND ex.true_morphism_id IS NOT DISTINCT FROM p_true THEN
      RETURN ex.id;
    END IF;
    RAISE EXCEPTION 'register_subobject_classifier: category % already has a classifier', p_cat;
  END IF;
  SELECT ob.* INTO o FROM object ob WHERE ob.id = p_omega;
  SELECT mo.* INTO t FROM morphism mo WHERE mo.id = p_true;
  IF o.id IS NULL OR o.category_id <> p_cat THEN
    RAISE EXCEPTION 'register_subobject_classifier: Ω is not an object of the category';
  END IF;
  IF t.id IS NULL OR t.category_id <> p_cat OR t.target_id <> p_omega THEN
    RAISE EXCEPTION 'register_subobject_classifier: true is not a morphism 1 → Ω of the category';
  END IF;
  INSERT INTO subobject_classifier (category_id, omega_object_id, true_morphism_id)
  VALUES (p_cat, p_omega, p_true)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Register p_mono as a subobject of p_sub_of_obj (NULL: its target).
-- Registering the same morphism again returns the existing row.  Whether it is
-- a monomorphism is checked in batch (not_mono): it depends on the recorded data.
CREATE OR REPLACE FUNCTION register_subobject(
  p_cat_id UUID, p_mono_morph UUID, p_sub_of_obj UUID
) RETURNS UUID AS $$
DECLARE
  m RECORD;
  ex UUID;
  new_id UUID;
BEGIN
  SELECT mo.* INTO m FROM morphism mo WHERE mo.id = p_mono_morph;
  IF m.id IS NULL THEN
    RAISE EXCEPTION 'register_subobject: morphism % not found', p_mono_morph;
  END IF;
  IF m.category_id <> p_cat_id THEN
    RAISE EXCEPTION 'register_subobject: the morphism is not in the category';
  END IF;
  IF p_sub_of_obj IS NOT NULL AND p_sub_of_obj <> m.target_id THEN
    RAISE EXCEPTION 'register_subobject: the object is not the target of the morphism';
  END IF;
  SELECT so.id INTO ex FROM subobject so
   WHERE so.category_id = p_cat_id AND so.mono_morphism_id = p_mono_morph
   ORDER BY so.created_at, so.id LIMIT 1;
  IF ex IS NOT NULL THEN
    RETURN ex;
  END IF;
  INSERT INTO subobject (category_id, mono_morphism_id, subobject_of_object_id)
  VALUES (p_cat_id, p_mono_morph, m.target_id)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Attach a characteristic morphism to a subobject.  Attaching the same χ again
-- is a no-op; attaching a different one is refused.  Whether χ makes the
-- square a pullback is checked in batch.
CREATE OR REPLACE FUNCTION attach_characteristic(
  p_sub_id UUID, p_char_morph UUID
) RETURNS VOID AS $$
DECLARE
  s RECORD;
  c RECORD;
  x RECORD;
  ex RECORD;
BEGIN
  SELECT so.* INTO s FROM subobject so WHERE so.id = p_sub_id;
  IF s.id IS NULL THEN
    RAISE EXCEPTION 'attach_characteristic: subobject % not found', p_sub_id;
  END IF;
  SELECT cm.* INTO ex FROM characteristic_morphism cm WHERE cm.subobject_id = p_sub_id;
  IF ex.id IS NOT NULL THEN
    IF ex.morphism_id = p_char_morph THEN
      RETURN;
    END IF;
    RAISE EXCEPTION 'attach_characteristic: subobject % already has a characteristic morphism',
      p_sub_id;
  END IF;
  SELECT sc.* INTO c FROM subobject_classifier sc WHERE sc.category_id = s.category_id;
  IF c.id IS NULL THEN
    RAISE EXCEPTION 'attach_characteristic: the category has no subobject classifier';
  END IF;
  SELECT mo.* INTO x FROM morphism mo WHERE mo.id = p_char_morph;
  IF x.id IS NULL OR x.category_id <> s.category_id
     OR x.source_id <> s.subobject_of_object_id OR x.target_id <> c.omega_object_id THEN
    RAISE EXCEPTION 'attach_characteristic: χ is not a morphism X → Ω of the category';
  END IF;
  INSERT INTO characteristic_morphism (subobject_id, morphism_id)
  VALUES (p_sub_id, p_char_morph);
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Subobject lattice helper: return the subobjects of X.
-- In a topos, subobjects of X form a Heyting algebra; we don't compute
-- meets/joins here, but we expose the raw subobject list.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION subobjects_of(p_object_id UUID)
RETURNS TABLE(subobject_id UUID, mono_morphism_id UUID) AS $$
BEGIN
  RETURN QUERY
  SELECT s.id, s.mono_morphism_id
    FROM subobject s
   WHERE s.subobject_of_object_id = p_object_id;
END;
$$ LANGUAGE plpgsql;
