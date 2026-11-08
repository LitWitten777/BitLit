-- ============================================================================
-- Categorical Ledger — Migration 010: Fibrations and Opfibrations
-- ============================================================================
-- A fibration is recorded as a functor p : E → B (projection_functor_id, an
-- ordinary functor of migration 001/002 with source E = total_category_id and
-- target B = base_category_id) together with registered lifts:
--   * kind = 'fibration':   a morphism φ : e' → e of E registered as a lift of
--     the base morphism u = p(φ) : b' → b *at its target* e;
--   * kind = 'opfibration': a morphism φ : e → e' of E registered as a lift of
--     u = p(φ) : b → b' *at its source* e.
-- One row per lift morphism (a lift of (u, e) is only unique up to a vertical
-- isomorphism, so several lifts of the same (u, e) may be registered).
--
-- Checks.  Every check logs to fibration_violation (column reason) and raises
-- only when qbx.enforcement_mode = 'strict'.
--   structure (write time and batch)
--     fibration_typing    the projection functor does not go from the total
--                         category to the base category
--     lift_typing         the lift morphism is not in E, the base morphism is
--                         not in B, or the recorded source / target objects are
--                         not those of the lift morphism
--     lift_not_over_base  p(φ) ≠ u (details.image is p(φ), NULL when the
--                         functor does not map φ)
--   universal property of every well-typed lift (batch: check_fibration,
--   verify_cartesian_property, run_all_batch_checks)
--     fibration, φ : a → b over u : x → y.  For every h : z → b in E whose
--     image p(h) is recorded and every w : p(z) → x in B with u ∘ w = p(h),
--     the morphisms k : z → a with p(k) = w and φ ∘ k = h are counted:
--       cartesian_existence      none (details: lift, base, h, w)
--       cartesian_uniqueness     more than one (details: ..., count)
--     opfibration, φ : a → b over u : x → y.  For every h : a → z with p(h)
--     recorded and every w : y → p(z) with w ∘ u = p(h), the k : b → z with
--     p(k) = w and k ∘ φ = h are counted:
--       cocartesian_existence, cocartesian_uniqueness
--   fibration property (batch)
--     missing_lift        a base morphism u and an object e of E over the
--                         target of u (opfibration: over the source of u) such
--                         that no morphism of E over u ending (starting) at e
--                         passes the (co)cartesian check above — registered or
--                         not (details: base, object)
-- Composites are read with qbx_compose (unit laws for recorded identities, the
-- composition table otherwise).  The universal property is checked against the
-- recorded morphisms and composites: a pass means "consistent with a fibration
-- on the recorded data"; a factorization whose composite is not recorded counts
-- as missing.
--
-- Formal backing (Formal/Fibration.lean): the check above is exactly Mathlib's
-- strongly cartesian morphism (isStronglyCartesian_iff_check) and its dual
-- (isStronglyCocartesian_iff_check); "every (u, e) has a lift passing the
-- check" is exactly Functor.IsFibered (isFibered_iff_cleavageCheck); the check
-- splits into existence and uniqueness and neither implies it
-- (cartesian_existence_not_sufficient, cartesian_uniqueness_not_sufficient);
-- over a one-object base the cartesian morphisms are exactly the isomorphisms
-- (isStronglyCartesian_star_iff_isIso), which the live tests use as an oracle.
--
-- Phase 1 sprint 7 rewrite.  Running the original on PostgreSQL 16 showed:
--   * a fibration whose projection functor goes B → E was accepted;
--   * register_cartesian_lift accepted a lift φ over a base morphism v with
--     p(φ) = u ≠ v, and recorded source / target objects that are not those of
--     φ;
--   * the unique key (fibration, base morphism, source object) made
--     register_cartesian_lift's ON CONFLICT ... DO UPDATE silently replace an
--     existing lift by another morphism (and forbade two lifts of the same u
--     with a common source but different targets);
--   * verify_cartesian_property only counted the morphisms into the lift's
--     source, so a non-cartesian lift passed as soon as an identity was
--     recorded;
--   * nothing checked that lifts exist, opfibrations were indistinguishable
--     from fibrations (no kind, no cocartesian check), and no fibration check
--     was part of run_all_batch_checks.
-- ============================================================================

CREATE TABLE IF NOT EXISTS fibration (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  total_category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
  base_category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
  projection_functor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
  kind TEXT NOT NULL DEFAULT 'fibration',
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now(),
  CONSTRAINT fibration_kind_check CHECK (kind IN ('fibration', 'opfibration'))
);

-- Upgrade path for a database holding the original 010 table.
ALTER TABLE fibration ADD COLUMN IF NOT EXISTS kind TEXT NOT NULL DEFAULT 'fibration';
DO $$
BEGIN
  IF NOT EXISTS (SELECT 1 FROM pg_constraint
                  WHERE conrelid = 'fibration'::regclass AND conname = 'fibration_kind_check') THEN
    ALTER TABLE fibration ADD CONSTRAINT fibration_kind_check
      CHECK (kind IN ('fibration', 'opfibration'));
  END IF;
END;
$$;

CREATE TABLE IF NOT EXISTS cartesian_lift (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  fibration_id UUID NOT NULL REFERENCES fibration(id) ON DELETE CASCADE,
  base_morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
  total_source_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  total_target_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  total_morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  CONSTRAINT cartesian_lift_morphism_unique UNIQUE (fibration_id, total_morphism_id)
);

-- Upgrade path: replace the original UNIQUE (fibration, base morphism, source).
DO $$
DECLARE
  c RECORD;
BEGIN
  FOR c IN SELECT conname FROM pg_constraint
            WHERE conrelid = 'cartesian_lift'::regclass AND contype = 'u'
              AND conname <> 'cartesian_lift_morphism_unique' LOOP
    EXECUTE format('ALTER TABLE cartesian_lift DROP CONSTRAINT %I', c.conname);
  END LOOP;
  IF NOT EXISTS (SELECT 1 FROM pg_constraint
                  WHERE conrelid = 'cartesian_lift'::regclass
                    AND conname = 'cartesian_lift_morphism_unique') THEN
    ALTER TABLE cartesian_lift ADD CONSTRAINT cartesian_lift_morphism_unique
      UNIQUE (fibration_id, total_morphism_id);
  END IF;
END;
$$;

CREATE INDEX IF NOT EXISTS idx_cartesian_lift_fib ON cartesian_lift (fibration_id);

CREATE TABLE IF NOT EXISTS fibration_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  fibration_id UUID NOT NULL REFERENCES fibration(id) ON DELETE CASCADE,
  reason TEXT,            -- see the header for the list of reasons
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_fibration_violation_fib
  ON fibration_violation (fibration_id, detected_at DESC);

-- ---------------------------------------------------------------------------
-- Lookups
-- ---------------------------------------------------------------------------
-- p(m) for the projection functor p (NULL if not mapped).
CREATE OR REPLACE FUNCTION fibration_map(p_functor UUID, p_mor UUID) RETURNS UUID AS $$
  SELECT fmm.target_morphism_id FROM functor_morphism_map fmm
   WHERE fmm.functor_id = p_functor AND fmm.source_morphism_id = p_mor;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION fibration_map_object(p_functor UUID, p_obj UUID) RETURNS UUID AS $$
  SELECT fom.target_object_id FROM functor_object_map fom
   WHERE fom.functor_id = p_functor AND fom.source_object_id = p_obj;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Problems (pure)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION fibration_typing_problems(p_fib UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  f RECORD;
  fu RECORD;
BEGIN
  SELECT fb.* INTO f FROM fibration fb WHERE fb.id = p_fib;
  IF f.id IS NULL THEN
    RETURN;
  END IF;
  SELECT fn.* INTO fu FROM functor fn WHERE fn.id = f.projection_functor_id;
  IF fu.source_category_id IS DISTINCT FROM f.total_category_id
     OR fu.target_category_id IS DISTINCT FROM f.base_category_id THEN
    reason := 'fibration_typing';
    details := jsonb_build_object('functor', f.projection_functor_id,
                                  'total', f.total_category_id, 'base', f.base_category_id);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION fibration_lift_problems(p_lift UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  l RECORD;
  f RECORD;
  m RECORD;
  b RECORD;
  v_image UUID;
BEGIN
  SELECT cl.* INTO l FROM cartesian_lift cl WHERE cl.id = p_lift;
  IF l.id IS NULL THEN
    RETURN;
  END IF;
  SELECT fb.* INTO f FROM fibration fb WHERE fb.id = l.fibration_id;
  SELECT mo.* INTO m FROM morphism mo WHERE mo.id = l.total_morphism_id;
  SELECT mo.* INTO b FROM morphism mo WHERE mo.id = l.base_morphism_id;
  IF m.category_id IS DISTINCT FROM f.total_category_id
     OR b.category_id IS DISTINCT FROM f.base_category_id
     OR l.total_source_object_id IS DISTINCT FROM m.source_id
     OR l.total_target_object_id IS DISTINCT FROM m.target_id THEN
    reason := 'lift_typing';
    details := jsonb_build_object('lift', l.total_morphism_id, 'base', l.base_morphism_id);
    RETURN NEXT;
  END IF;
  v_image := fibration_map(f.projection_functor_id, l.total_morphism_id);
  IF v_image IS DISTINCT FROM l.base_morphism_id THEN
    reason := 'lift_not_over_base';
    details := jsonb_build_object('lift', l.total_morphism_id, 'base', l.base_morphism_id,
                                  'image', v_image);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- The (co)cartesian check of a morphism p_phi of E over the base morphism p_u
-- (kind taken from the fibration).  Returns one row per failing (h, w).
CREATE OR REPLACE FUNCTION fibration_cartesian_problems(p_fib UUID, p_phi UUID, p_u UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  f RECORD;
  phi RECORD;
  u RECORD;
  h RECORD;
  w RECORD;
  v_ph UUID;
  v_n INT;
  v_details JSONB;
BEGIN
  SELECT fb.* INTO f FROM fibration fb WHERE fb.id = p_fib;
  SELECT mo.* INTO phi FROM morphism mo WHERE mo.id = p_phi;
  SELECT mo.* INTO u FROM morphism mo WHERE mo.id = p_u;
  IF f.id IS NULL OR phi.id IS NULL OR u.id IS NULL THEN
    RETURN;
  END IF;

  IF f.kind = 'fibration' THEN
    FOR h IN SELECT mo.* FROM morphism mo
              WHERE mo.category_id = f.total_category_id AND mo.target_id = phi.target_id
              ORDER BY mo.id LOOP
      v_ph := fibration_map(f.projection_functor_id, h.id);
      CONTINUE WHEN v_ph IS NULL;
      FOR w IN SELECT mo.* FROM morphism mo
                WHERE mo.category_id = u.category_id AND mo.target_id = u.source_id
                  AND qbx_compose(mo.id, p_u) = v_ph
                ORDER BY mo.id LOOP
        SELECT count(*) INTO v_n FROM morphism k
         WHERE k.category_id = f.total_category_id
           AND k.source_id = h.source_id AND k.target_id = phi.source_id
           AND fibration_map(f.projection_functor_id, k.id) = w.id
           AND qbx_compose(k.id, p_phi) = h.id;
        v_details := jsonb_build_object('lift', p_phi, 'base', p_u, 'h', h.id, 'w', w.id);
        IF v_n = 0 THEN
          reason := 'cartesian_existence'; details := v_details; RETURN NEXT;
        ELSIF v_n > 1 THEN
          reason := 'cartesian_uniqueness';
          details := v_details || jsonb_build_object('count', v_n); RETURN NEXT;
        END IF;
      END LOOP;
    END LOOP;
  ELSE
    FOR h IN SELECT mo.* FROM morphism mo
              WHERE mo.category_id = f.total_category_id AND mo.source_id = phi.source_id
              ORDER BY mo.id LOOP
      v_ph := fibration_map(f.projection_functor_id, h.id);
      CONTINUE WHEN v_ph IS NULL;
      FOR w IN SELECT mo.* FROM morphism mo
                WHERE mo.category_id = u.category_id AND mo.source_id = u.target_id
                  AND qbx_compose(p_u, mo.id) = v_ph
                ORDER BY mo.id LOOP
        SELECT count(*) INTO v_n FROM morphism k
         WHERE k.category_id = f.total_category_id
           AND k.source_id = phi.target_id AND k.target_id = h.target_id
           AND fibration_map(f.projection_functor_id, k.id) = w.id
           AND qbx_compose(p_phi, k.id) = h.id;
        v_details := jsonb_build_object('lift', p_phi, 'base', p_u, 'h', h.id, 'w', w.id);
        IF v_n = 0 THEN
          reason := 'cocartesian_existence'; details := v_details; RETURN NEXT;
        ELSIF v_n > 1 THEN
          reason := 'cocartesian_uniqueness';
          details := v_details || jsonb_build_object('count', v_n); RETURN NEXT;
        END IF;
      END LOOP;
    END LOOP;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- Does some morphism of E over p_u ending (fibration) / starting (opfibration)
-- at p_obj pass the (co)cartesian check?
CREATE OR REPLACE FUNCTION fibration_has_lift(p_fib UUID, p_u UUID, p_obj UUID)
RETURNS BOOLEAN AS $$
DECLARE
  f RECORD;
  c RECORD;
BEGIN
  SELECT fb.* INTO f FROM fibration fb WHERE fb.id = p_fib;
  FOR c IN SELECT mo.id FROM morphism mo
            WHERE mo.category_id = f.total_category_id
              AND ((f.kind = 'fibration' AND mo.target_id = p_obj)
                   OR (f.kind = 'opfibration' AND mo.source_id = p_obj))
              AND fibration_map(f.projection_functor_id, mo.id) = p_u
            ORDER BY mo.id LOOP
    IF NOT EXISTS (SELECT 1 FROM fibration_cartesian_problems(p_fib, c.id, p_u)) THEN
      RETURN TRUE;
    END IF;
  END LOOP;
  RETURN FALSE;
END;
$$ LANGUAGE plpgsql STABLE;

-- Every problem of a fibration.
CREATE OR REPLACE FUNCTION fibration_problems(p_fib UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  f RECORD;
  l RECORD;
  u RECORD;
  e RECORD;
  pr RECORD;
  v_bad BOOLEAN;
BEGIN
  SELECT fb.* INTO f FROM fibration fb WHERE fb.id = p_fib;
  IF f.id IS NULL THEN
    reason := 'missing_fibration';
    details := jsonb_build_object('fibration', p_fib);
    RETURN NEXT;
    RETURN;
  END IF;

  FOR pr IN SELECT * FROM fibration_typing_problems(p_fib) LOOP
    reason := pr.reason; details := pr.details; RETURN NEXT;
  END LOOP;

  -- registered lifts: structure, then the universal property of well-formed ones
  FOR l IN SELECT cl.* FROM cartesian_lift cl WHERE cl.fibration_id = p_fib ORDER BY cl.id LOOP
    v_bad := FALSE;
    FOR pr IN SELECT * FROM fibration_lift_problems(l.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
      v_bad := TRUE;
    END LOOP;
    CONTINUE WHEN v_bad;
    FOR pr IN SELECT * FROM fibration_cartesian_problems(p_fib, l.total_morphism_id,
                                                         l.base_morphism_id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
    END LOOP;
  END LOOP;

  -- the fibration property: every (u, e) has a lift passing the check
  FOR u IN SELECT mo.* FROM morphism mo WHERE mo.category_id = f.base_category_id ORDER BY mo.id LOOP
    FOR e IN SELECT ob.id FROM object ob
              WHERE ob.category_id = f.total_category_id
                AND fibration_map_object(f.projection_functor_id, ob.id)
                    = CASE WHEN f.kind = 'fibration' THEN u.target_id ELSE u.source_id END
              ORDER BY ob.id LOOP
      IF NOT fibration_has_lift(p_fib, u.id, e.id) THEN
        reason := 'missing_lift';
        details := jsonb_build_object('base', u.id, 'object', e.id);
        RETURN NEXT;
      END IF;
    END LOOP;
  END LOOP;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION fibration_record(p_fib UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  INSERT INTO fibration_violation (fibration_id, reason, details)
  VALUES (p_fib, p_reason, p_details);
END;
$$ LANGUAGE plpgsql;

-- All checks of one fibration; logs every problem, raises in strict mode.
CREATE OR REPLACE FUNCTION check_fibration(p_fib UUID) RETURNS BOOLEAN AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM fibration fb WHERE fb.id = p_fib) THEN
    RAISE EXCEPTION 'check_fibration: fibration % not found', p_fib;
  END IF;
  FOR pr IN SELECT * FROM fibration_problems(p_fib) LOOP
    PERFORM fibration_record(p_fib, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Fibration % violates its laws (% problem(s))', p_fib, n_problems;
  END IF;
  RETURN n_problems = 0;
END;
$$ LANGUAGE plpgsql;

-- One registered lift: structure and (co)cartesian property (the original
-- entry point, which only counted the morphisms into the lift's source).
CREATE OR REPLACE FUNCTION verify_cartesian_property(p_fib UUID, p_lift UUID)
RETURNS BOOLEAN AS $$
DECLARE
  l RECORD;
  pr RECORD;
  n_problems INT := 0;
BEGIN
  SELECT cl.* INTO l FROM cartesian_lift cl WHERE cl.id = p_lift;
  IF l.id IS NULL OR l.fibration_id <> p_fib THEN
    RAISE EXCEPTION 'verify_cartesian_property: % is not a lift of fibration %', p_lift, p_fib;
  END IF;
  FOR pr IN SELECT * FROM fibration_lift_problems(p_lift) LOOP
    PERFORM fibration_record(p_fib, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems = 0 THEN
    FOR pr IN SELECT * FROM fibration_cartesian_problems(p_fib, l.total_morphism_id,
                                                         l.base_morphism_id) LOOP
      PERFORM fibration_record(p_fib, pr.reason, pr.details);
      n_problems := n_problems + 1;
    END LOOP;
  END IF;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Lift % is not (co)cartesian (% problem(s))', p_lift, n_problems;
  END IF;
  RETURN n_problems = 0;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_fibration() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM fibration_typing_problems(NEW.id) LOOP
    PERFORM fibration_record(NEW.id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Fibration % is not well typed (% problem(s))', NEW.id, n_problems;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_fibration ON fibration;
CREATE TRIGGER trg_check_fibration
AFTER INSERT OR UPDATE ON fibration
FOR EACH ROW EXECUTE FUNCTION trg_check_fibration();

CREATE OR REPLACE FUNCTION trg_check_cartesian_lift() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM fibration_lift_problems(NEW.id) LOOP
    PERFORM fibration_record(NEW.fibration_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Lift % is not valid (% problem(s))', NEW.id, n_problems;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_cartesian_lift ON cartesian_lift;
CREATE TRIGGER trg_check_cartesian_lift
AFTER INSERT OR UPDATE ON cartesian_lift
FOR EACH ROW EXECUTE FUNCTION trg_check_cartesian_lift();

-- ---------------------------------------------------------------------------
-- Writer.  Registers p_morph as a lift of p_base.  p_src / p_tgt may be NULL
-- (they default to the endpoints of p_morph).  Refuses, in every mode, input
-- it cannot build a valid row from: unknown fibration or morphism, morphisms
-- outside E / B, endpoints that are not those of p_morph, or p(p_morph) ≠
-- p_base.  Registering the same morphism again returns the existing row; it
-- never replaces a lift.  Rows inserted directly are checked by the trigger.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION register_cartesian_lift(
  p_fib_id UUID, p_base_morph UUID,
  p_total_src UUID, p_total_tgt UUID, p_total_morph UUID
) RETURNS UUID AS $$
DECLARE
  f RECORD;
  m RECORD;
  b RECORD;
  ex RECORD;
  new_id UUID;
BEGIN
  SELECT fb.* INTO f FROM fibration fb WHERE fb.id = p_fib_id;
  IF f.id IS NULL THEN
    RAISE EXCEPTION 'register_cartesian_lift: fibration % not found', p_fib_id;
  END IF;
  SELECT mo.* INTO m FROM morphism mo WHERE mo.id = p_total_morph;
  SELECT mo.* INTO b FROM morphism mo WHERE mo.id = p_base_morph;
  IF m.id IS NULL OR b.id IS NULL THEN
    RAISE EXCEPTION 'register_cartesian_lift: morphism(s) not found (lift %, base %)',
      p_total_morph, p_base_morph;
  END IF;

  SELECT cl.* INTO ex FROM cartesian_lift cl
   WHERE cl.fibration_id = p_fib_id AND cl.total_morphism_id = p_total_morph;
  IF ex.id IS NOT NULL THEN
    IF ex.base_morphism_id <> p_base_morph THEN
      RAISE EXCEPTION 'register_cartesian_lift: % is already registered over another base morphism',
        p_total_morph;
    END IF;
    RETURN ex.id;
  END IF;

  IF m.category_id <> f.total_category_id THEN
    RAISE EXCEPTION 'register_cartesian_lift: the lift is not a morphism of the total category';
  END IF;
  IF b.category_id <> f.base_category_id THEN
    RAISE EXCEPTION 'register_cartesian_lift: the base morphism is not in the base category';
  END IF;
  IF (p_total_src IS NOT NULL AND p_total_src <> m.source_id)
     OR (p_total_tgt IS NOT NULL AND p_total_tgt <> m.target_id) THEN
    RAISE EXCEPTION 'register_cartesian_lift: source / target are not those of the lift morphism';
  END IF;
  IF fibration_map(f.projection_functor_id, p_total_morph) IS DISTINCT FROM p_base_morph THEN
    RAISE EXCEPTION 'register_cartesian_lift: the lift does not lie over the base morphism (p(lift) <> base)';
  END IF;

  INSERT INTO cartesian_lift
    (fibration_id, base_morphism_id, total_source_object_id,
     total_target_object_id, total_morphism_id, metadata)
  VALUES
    (p_fib_id, p_base_morph, m.source_id, m.target_id, p_total_morph,
     jsonb_build_object('registered_at', now()))
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;
