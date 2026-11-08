-- ============================================================================
-- Categorical Ledger — Migration 007: Limits and Colimits
-- ============================================================================
-- A diagram in category C is recorded as a graph: nodes (each labelled by an
-- object of C) and arrows (each labelled by a morphism of C between the node
-- objects).  Its shape is the free category on that graph, so a family of legs
-- is a cone as soon as the triangle of every recorded arrow commutes
-- (Formal/Limits.lean: coneOfEdges, coneOfGenerators).
--
-- Cone (L, π) over D, legs π_n : L → D(n):     π_tgt = a ∘ π_src  per arrow a
-- Cocone (L, ι) under D, legs ι_n : D(n) → L:  ι_src = ι_tgt ∘ a  per arrow a
--
-- A cone is a limit iff (Formal/Limits.lean: nonempty_isLimit_iff)
--   existence:  every cone (X, σ) has a mediator m : X → L, π_n ∘ m = σ_n, and
--   uniqueness: the legs are jointly monic — m, m' : X → L with
--               π_n ∘ m = π_n ∘ m' for every node n are equal;
-- dually a cocone is a colimit iff every cocone receives a mediator from it
-- and its legs are jointly epic.  Neither half implies the other
-- (existence_not_sufficient, jointlyMonic_not_sufficient), so both are checked.
--
-- What the ledger can check.  Uniqueness is checked exactly, over every
-- recorded morphism into (out of) the apex.  Existence is checked against the
-- cones (cocones) *recorded* over the same diagram — the ledger cannot
-- enumerate all cones.  A pass therefore means "universal among the recorded
-- data"; it is a proof of universality when every cone of interest is recorded.
--
-- Tiers: cone / cocone well-formedness and commutativity are checked at write
-- time (on insert or update of a "limit" / colimit row, and by finalize_*);
-- universality is batch (verify_*_universality, run_all_batch_checks in 017).
-- Every check logs to limit_violation / colimit_violation and raises only when
-- qbx.enforcement_mode = 'strict'.
--
-- Composition convention (migrations 001–006): composition(left_id = g,
-- right_id = f, result_id = h) records h = g ∘ f (f applied first); composites
-- are looked up with qbx_compose(first, second) (migration 002), which applies
-- the unit laws for identity morphisms.
--
-- Phase 1 sprint 4 rewrite.  Running the original on PostgreSQL 16 showed:
--   * composites were looked up in `composition` directly, without the unit
--     laws, so any triangle with an identity leg or arrow failed — e.g. the
--     limit of A →f B (apex A, legs id_A and f) was reported as non-commuting;
--   * only nodes touched by an arrow were inspected: a cone with no legs at
--     all over a diagram without arrows "commuted", and no leg was ever
--     type-checked (source = apex, target = node object, same category);
--   * missing legs returned FALSE without raising in strict mode, and the
--     first problem stopped the check, so later ones were never logged;
--   * a "limit" row could point at a cone over a different diagram;
--   * universality counted mediators only against recorded cones (including
--     cones that do not commute) and, lacking the unit laws, found no mediator
--     when the other cone had the same apex and legs (the mediator is the
--     identity); it never checked uniqueness beyond those cones;
--   * colimit universality was not implemented at all, and neither limits nor
--     colimits were part of run_all_batch_checks.
-- ============================================================================

-- ---------------------------------------------------------------------------
-- Diagrams
-- ---------------------------------------------------------------------------
CREATE TABLE IF NOT EXISTS diagram (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
  name TEXT NOT NULL,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now(),
  UNIQUE (category_id, name)
);

CREATE TABLE IF NOT EXISTS diagram_node (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  diagram_id UUID NOT NULL REFERENCES diagram(id) ON DELETE CASCADE,
  label TEXT,
  object_id UUID REFERENCES object(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb
);

CREATE TABLE IF NOT EXISTS diagram_arrow (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  diagram_id UUID NOT NULL REFERENCES diagram(id) ON DELETE CASCADE,
  label TEXT,
  source_node_id UUID NOT NULL REFERENCES diagram_node(id) ON DELETE CASCADE,
  target_node_id UUID NOT NULL REFERENCES diagram_node(id) ON DELETE CASCADE,
  morphism_id UUID REFERENCES morphism(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb
);

-- ---------------------------------------------------------------------------
-- Cones and cocones
-- ---------------------------------------------------------------------------
CREATE TABLE IF NOT EXISTS cone (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  diagram_id UUID NOT NULL REFERENCES diagram(id) ON DELETE CASCADE,
  apex_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb
);

CREATE TABLE IF NOT EXISTS cone_leg (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  cone_id UUID NOT NULL REFERENCES cone(id) ON DELETE CASCADE,
  node_id UUID NOT NULL REFERENCES diagram_node(id) ON DELETE CASCADE,
  leg_morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
  UNIQUE (cone_id, node_id)
);

CREATE TABLE IF NOT EXISTS cocone (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  diagram_id UUID NOT NULL REFERENCES diagram(id) ON DELETE CASCADE,
  apex_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb
);

CREATE TABLE IF NOT EXISTS cocone_leg (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  cocone_id UUID NOT NULL REFERENCES cocone(id) ON DELETE CASCADE,
  node_id UUID NOT NULL REFERENCES diagram_node(id) ON DELETE CASCADE,
  leg_morphism_id UUID NOT NULL REFERENCES morphism(id) ON DELETE CASCADE,
  UNIQUE (cocone_id, node_id)
);

-- ---------------------------------------------------------------------------
-- Limits and colimits
-- ---------------------------------------------------------------------------
CREATE TABLE IF NOT EXISTS "limit" (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  diagram_id UUID NOT NULL REFERENCES diagram(id) ON DELETE CASCADE,
  cone_id UUID NOT NULL REFERENCES cone(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS colimit (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  diagram_id UUID NOT NULL REFERENCES diagram(id) ON DELETE CASCADE,
  cocone_id UUID NOT NULL REFERENCES cocone(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

-- ---------------------------------------------------------------------------
-- Violation logs.  reason is one of
--   missing_cone, apex_category, node_without_object, node_category,
--   missing_leg, leg_typing, foreign_leg, arrow_without_morphism,
--   arrow_typing, missing_composite, non_commuting_triangle,
--   diagram_mismatch, invalid_cone, no_mediator, non_unique_mediator,
--   legs_not_jointly_monic (limits) / legs_not_jointly_epic (colimits)
-- ---------------------------------------------------------------------------
CREATE TABLE IF NOT EXISTS limit_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  diagram_id UUID,
  cone_id UUID,
  reason TEXT,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS colimit_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  diagram_id UUID,
  cocone_id UUID,
  reason TEXT,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

-- ---------------------------------------------------------------------------
-- Problems of a cone / cocone (pure: no logging, no raising).
-- p_is_cocone = FALSE: legs apex → node object, triangle π_tgt = a ∘ π_src.
-- p_is_cocone = TRUE:  legs node object → apex, triangle ι_src = ι_tgt ∘ a.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION lim_problems(p_id UUID, p_is_cocone BOOLEAN)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  v_diagram UUID;
  v_apex UUID;
  v_cat UUID;
  n RECORD;
  a RECORD;
  v_leg UUID;
  lm RECORD;
  bad_nodes UUID[] := ARRAY[]::uuid[];
  v_leg_src UUID;
  v_leg_tgt UUID;
  am RECORD;
  v_src_obj UUID;
  v_tgt_obj UUID;
  v_lhs UUID;
  v_rhs UUID;
BEGIN
  IF p_is_cocone THEN
    SELECT c.diagram_id, c.apex_object_id INTO v_diagram, v_apex FROM cocone c WHERE c.id = p_id;
  ELSE
    SELECT c.diagram_id, c.apex_object_id INTO v_diagram, v_apex FROM cone c WHERE c.id = p_id;
  END IF;
  IF v_diagram IS NULL THEN
    reason := 'missing_cone'; details := jsonb_build_object('id', p_id); RETURN NEXT;
    RETURN;
  END IF;
  SELECT d.category_id INTO v_cat FROM diagram d WHERE d.id = v_diagram;

  IF NOT EXISTS (SELECT 1 FROM object o WHERE o.id = v_apex AND o.category_id = v_cat) THEN
    reason := 'apex_category'; details := jsonb_build_object('apex', v_apex); RETURN NEXT;
  END IF;

  -- Legs: one per node, correctly typed.
  FOR n IN SELECT dn.id, dn.object_id FROM diagram_node dn WHERE dn.diagram_id = v_diagram LOOP
    IF n.object_id IS NULL THEN
      reason := 'node_without_object'; details := jsonb_build_object('node', n.id); RETURN NEXT;
      bad_nodes := bad_nodes || n.id;
      CONTINUE;
    END IF;
    IF NOT EXISTS (SELECT 1 FROM object o WHERE o.id = n.object_id AND o.category_id = v_cat) THEN
      reason := 'node_category'; details := jsonb_build_object('node', n.id); RETURN NEXT;
    END IF;
    IF p_is_cocone THEN
      SELECT l.leg_morphism_id INTO v_leg FROM cocone_leg l WHERE l.cocone_id = p_id AND l.node_id = n.id;
    ELSE
      SELECT l.leg_morphism_id INTO v_leg FROM cone_leg l WHERE l.cone_id = p_id AND l.node_id = n.id;
    END IF;
    IF v_leg IS NULL THEN
      reason := 'missing_leg'; details := jsonb_build_object('node', n.id); RETURN NEXT;
      bad_nodes := bad_nodes || n.id;
      CONTINUE;
    END IF;
    SELECT m.category_id, m.source_id, m.target_id INTO lm FROM morphism m WHERE m.id = v_leg;
    IF lm.category_id IS DISTINCT FROM v_cat
       OR (NOT p_is_cocone AND (lm.source_id <> v_apex OR lm.target_id <> n.object_id))
       OR (p_is_cocone AND (lm.source_id <> n.object_id OR lm.target_id <> v_apex)) THEN
      reason := 'leg_typing';
      details := jsonb_build_object('node', n.id, 'leg', v_leg,
                                    'leg_source', lm.source_id, 'leg_target', lm.target_id);
      RETURN NEXT;
      bad_nodes := bad_nodes || n.id;
    END IF;
  END LOOP;

  -- Legs attached to nodes of another diagram.
  IF p_is_cocone THEN
    FOR v_leg IN SELECT l.id FROM cocone_leg l JOIN diagram_node dn ON dn.id = l.node_id
                  WHERE l.cocone_id = p_id AND dn.diagram_id <> v_diagram LOOP
      reason := 'foreign_leg'; details := jsonb_build_object('leg_row', v_leg); RETURN NEXT;
    END LOOP;
  ELSE
    FOR v_leg IN SELECT l.id FROM cone_leg l JOIN diagram_node dn ON dn.id = l.node_id
                  WHERE l.cone_id = p_id AND dn.diagram_id <> v_diagram LOOP
      reason := 'foreign_leg'; details := jsonb_build_object('leg_row', v_leg); RETURN NEXT;
    END LOOP;
  END IF;

  -- Arrows: typed, and their triangles commute.
  FOR a IN SELECT da.* FROM diagram_arrow da WHERE da.diagram_id = v_diagram LOOP
    IF a.morphism_id IS NULL THEN
      reason := 'arrow_without_morphism'; details := jsonb_build_object('arrow', a.id); RETURN NEXT;
      CONTINUE;
    END IF;
    SELECT dn.object_id INTO v_src_obj FROM diagram_node dn
     WHERE dn.id = a.source_node_id AND dn.diagram_id = v_diagram;
    SELECT dn.object_id INTO v_tgt_obj FROM diagram_node dn
     WHERE dn.id = a.target_node_id AND dn.diagram_id = v_diagram;
    SELECT m.category_id, m.source_id, m.target_id INTO am FROM morphism m WHERE m.id = a.morphism_id;
    IF v_src_obj IS NULL OR v_tgt_obj IS NULL
       OR am.category_id IS DISTINCT FROM v_cat
       OR am.source_id <> v_src_obj OR am.target_id <> v_tgt_obj THEN
      reason := 'arrow_typing'; details := jsonb_build_object('arrow', a.id); RETURN NEXT;
      CONTINUE;
    END IF;
    IF a.source_node_id = ANY (bad_nodes) OR a.target_node_id = ANY (bad_nodes) THEN
      CONTINUE;  -- already reported (missing or mistyped leg)
    END IF;
    IF p_is_cocone THEN
      SELECT l.leg_morphism_id INTO v_leg_src FROM cocone_leg l WHERE l.cocone_id = p_id AND l.node_id = a.source_node_id;
      SELECT l.leg_morphism_id INTO v_leg_tgt FROM cocone_leg l WHERE l.cocone_id = p_id AND l.node_id = a.target_node_id;
      v_lhs := v_leg_src;                                   -- ι_src
      v_rhs := qbx_compose(a.morphism_id, v_leg_tgt);       -- ι_tgt ∘ a
    ELSE
      SELECT l.leg_morphism_id INTO v_leg_src FROM cone_leg l WHERE l.cone_id = p_id AND l.node_id = a.source_node_id;
      SELECT l.leg_morphism_id INTO v_leg_tgt FROM cone_leg l WHERE l.cone_id = p_id AND l.node_id = a.target_node_id;
      v_lhs := v_leg_tgt;                                   -- π_tgt
      v_rhs := qbx_compose(v_leg_src, a.morphism_id);       -- a ∘ π_src
    END IF;
    IF v_rhs IS NULL THEN
      reason := 'missing_composite';
      details := jsonb_build_object('arrow', a.id, 'leg_src', v_leg_src, 'leg_tgt', v_leg_tgt);
      RETURN NEXT;
    ELSIF v_rhs <> v_lhs THEN
      reason := 'non_commuting_triangle';
      details := jsonb_build_object('arrow', a.id, 'leg_src', v_leg_src, 'leg_tgt', v_leg_tgt,
                                    'composed', v_rhs);
      RETURN NEXT;
    END IF;
  END LOOP;
  RETURN;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION cone_problems(p_cone_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT * FROM lim_problems(p_cone_id, FALSE);
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION cocone_problems(p_cocone_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT * FROM lim_problems(p_cocone_id, TRUE);
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION cone_is_valid(p_cone_id UUID) RETURNS BOOLEAN AS $$
  SELECT NOT EXISTS (SELECT 1 FROM lim_problems(p_cone_id, FALSE));
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION cocone_is_valid(p_cocone_id UUID) RETURNS BOOLEAN AS $$
  SELECT NOT EXISTS (SELECT 1 FROM lim_problems(p_cocone_id, TRUE));
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Logging helpers
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION lim_record(
  p_is_cocone BOOLEAN, p_diagram UUID, p_cone UUID, p_reason TEXT, p_details JSONB
) RETURNS VOID AS $$
BEGIN
  IF p_is_cocone THEN
    INSERT INTO colimit_violation (diagram_id, cocone_id, reason, details)
    VALUES (p_diagram, p_cone, p_reason, coalesce(p_details, '{}'::jsonb));
  ELSE
    INSERT INTO limit_violation (diagram_id, cone_id, reason, details)
    VALUES (p_diagram, p_cone, p_reason, coalesce(p_details, '{}'::jsonb));
  END IF;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Cone / cocone check (write-time tier): log every problem; raise in strict.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION lim_check(p_id UUID, p_is_cocone BOOLEAN)
RETURNS BOOLEAN AS $$
DECLARE
  v_diagram UUID;
  pr RECORD;
  n_problems INT := 0;
BEGIN
  IF p_is_cocone THEN
    SELECT c.diagram_id INTO v_diagram FROM cocone c WHERE c.id = p_id;
  ELSE
    SELECT c.diagram_id INTO v_diagram FROM cone c WHERE c.id = p_id;
  END IF;
  FOR pr IN SELECT * FROM lim_problems(p_id, p_is_cocone) LOOP
    PERFORM lim_record(p_is_cocone, v_diagram, p_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION '% % is not valid (% problem(s))',
      CASE WHEN p_is_cocone THEN 'Cocone' ELSE 'Cone' END, p_id, n_problems;
  END IF;
  RETURN n_problems = 0;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION check_cone_commutes(p_cone_id UUID) RETURNS BOOLEAN AS $$
  SELECT lim_check(p_cone_id, FALSE);
$$ LANGUAGE sql;

CREATE OR REPLACE FUNCTION check_cocone_commutes(p_cocone_id UUID) RETURNS BOOLEAN AS $$
  SELECT lim_check(p_cocone_id, TRUE);
$$ LANGUAGE sql;

-- ---------------------------------------------------------------------------
-- Leg lookup and composite helpers for universality
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION lim_leg(p_id UUID, p_node UUID, p_is_cocone BOOLEAN)
RETURNS UUID AS $$
  SELECT CASE WHEN p_is_cocone
    THEN (SELECT l.leg_morphism_id FROM cocone_leg l WHERE l.cocone_id = p_id AND l.node_id = p_node)
    ELSE (SELECT l.leg_morphism_id FROM cone_leg l WHERE l.cone_id = p_id AND l.node_id = p_node)
  END;
$$ LANGUAGE sql STABLE;

-- Cone: π_n ∘ m (m first).  Cocone: m ∘ ι_n (ι_n first).
CREATE OR REPLACE FUNCTION lim_through(p_m UUID, p_leg UUID, p_is_cocone BOOLEAN)
RETURNS UUID AS $$
  SELECT CASE WHEN p_is_cocone THEN qbx_compose(p_leg, p_m) ELSE qbx_compose(p_m, p_leg) END;
$$ LANGUAGE sql STABLE;

-- Does p_m mediate from (to) the other cone (cocone) p_other to (from) p_id?
CREATE OR REPLACE FUNCTION lim_mediates(p_m UUID, p_id UUID, p_other UUID,
                                        p_diagram UUID, p_is_cocone BOOLEAN)
RETURNS BOOLEAN AS $$
  SELECT NOT EXISTS (
    SELECT 1 FROM diagram_node dn
     WHERE dn.diagram_id = p_diagram
       AND lim_through(p_m, lim_leg(p_id, dn.id, p_is_cocone), p_is_cocone)
           IS DISTINCT FROM lim_leg(p_other, dn.id, p_is_cocone)
  );
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Universality (batch tier)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION lim_verify_universality(p_id UUID, p_is_cocone BOOLEAN)
RETURNS BOOLEAN AS $$
DECLARE
  v_diagram UUID;     -- diagram recorded on the limit / colimit row
  v_cone UUID;
  v_cone_diagram UUID;
  v_apex UUID;
  v_cat UUID;
  o RECORD;
  pr RECORD;
  pair RECORD;
  v_mediators UUID[];
  v_problems JSONB;
  n_found INT := 0;
  n_nodes INT;
  n_sep INT;
  n_undef INT;
BEGIN
  IF p_is_cocone THEN
    SELECT c.diagram_id, c.cocone_id INTO v_diagram, v_cone FROM colimit c WHERE c.id = p_id;
    SELECT c.diagram_id, c.apex_object_id INTO v_cone_diagram, v_apex FROM cocone c WHERE c.id = v_cone;
  ELSE
    SELECT l.diagram_id, l.cone_id INTO v_diagram, v_cone FROM "limit" l WHERE l.id = p_id;
    SELECT c.diagram_id, c.apex_object_id INTO v_cone_diagram, v_apex FROM cone c WHERE c.id = v_cone;
  END IF;
  IF v_cone IS NULL THEN
    RETURN FALSE;
  END IF;

  IF v_diagram IS DISTINCT FROM v_cone_diagram THEN
    PERFORM lim_record(p_is_cocone, v_diagram, v_cone, 'diagram_mismatch',
      jsonb_build_object('id', p_id, 'cone_diagram', v_cone_diagram));
    n_found := n_found + 1;
  END IF;

  SELECT coalesce(jsonb_agg(jsonb_build_object('reason', x.reason, 'details', x.details)), '[]'::jsonb)
    INTO v_problems FROM lim_problems(v_cone, p_is_cocone) x;
  IF jsonb_array_length(v_problems) > 0 THEN
    PERFORM lim_record(p_is_cocone, v_cone_diagram, v_cone, 'invalid_cone',
      jsonb_build_object('id', p_id, 'problems', v_problems));
    n_found := n_found + 1;
  ELSE
    SELECT d.category_id INTO v_cat FROM diagram d WHERE d.id = v_cone_diagram;
    SELECT count(*) INTO n_nodes FROM diagram_node dn WHERE dn.diagram_id = v_cone_diagram;

    -- Existence (and uniqueness) of a mediator for every valid recorded cone.
    FOR o IN
      SELECT c.id, c.apex_object_id FROM cone c
       WHERE NOT p_is_cocone AND c.diagram_id = v_cone_diagram AND c.id <> v_cone
      UNION ALL
      SELECT c.id, c.apex_object_id FROM cocone c
       WHERE p_is_cocone AND c.diagram_id = v_cone_diagram AND c.id <> v_cone
    LOOP
      IF EXISTS (SELECT 1 FROM lim_problems(o.id, p_is_cocone)) THEN
        CONTINUE;  -- not a cone: nothing to mediate
      END IF;
      SELECT coalesce(array_agg(m.id ORDER BY m.id), ARRAY[]::uuid[]) INTO v_mediators
        FROM morphism m
       WHERE m.category_id = v_cat
         AND ((NOT p_is_cocone AND m.source_id = o.apex_object_id AND m.target_id = v_apex)
           OR (p_is_cocone AND m.source_id = v_apex AND m.target_id = o.apex_object_id))
         AND lim_mediates(m.id, v_cone, o.id, v_cone_diagram, p_is_cocone);
      IF cardinality(v_mediators) = 0 THEN
        PERFORM lim_record(p_is_cocone, v_cone_diagram, v_cone, 'no_mediator',
          jsonb_build_object('id', p_id, 'other', o.id));
        n_found := n_found + 1;
      ELSIF cardinality(v_mediators) > 1 THEN
        PERFORM lim_record(p_is_cocone, v_cone_diagram, v_cone, 'non_unique_mediator',
          jsonb_build_object('id', p_id, 'other', o.id, 'mediators', to_jsonb(v_mediators)));
        n_found := n_found + 1;
      END IF;
    END LOOP;

    -- Uniqueness: legs jointly monic (epic) over every recorded morphism.
    FOR pair IN
      SELECT m1.id AS m1, m2.id AS m2
        FROM morphism m1 JOIN morphism m2
          ON m1.category_id = m2.category_id AND m1.id < m2.id
         AND m1.source_id = m2.source_id AND m1.target_id = m2.target_id
       WHERE m1.category_id = v_cat
         AND ((NOT p_is_cocone AND m1.target_id = v_apex)
           OR (p_is_cocone AND m1.source_id = v_apex))
    LOOP
      SELECT count(*) FILTER (WHERE t.x IS NOT NULL AND t.y IS NOT NULL AND t.x <> t.y),
             count(*) FILTER (WHERE t.x IS NULL OR t.y IS NULL)
        INTO n_sep, n_undef
        FROM (SELECT lim_through(pair.m1, lim_leg(v_cone, dn.id, p_is_cocone), p_is_cocone) AS x,
                     lim_through(pair.m2, lim_leg(v_cone, dn.id, p_is_cocone), p_is_cocone) AS y
                FROM diagram_node dn WHERE dn.diagram_id = v_cone_diagram) t;
      IF n_sep = 0 AND n_undef = 0 THEN
        PERFORM lim_record(p_is_cocone, v_cone_diagram, v_cone,
          CASE WHEN p_is_cocone THEN 'legs_not_jointly_epic' ELSE 'legs_not_jointly_monic' END,
          jsonb_build_object('id', p_id, 'm1', pair.m1, 'm2', pair.m2));
        n_found := n_found + 1;
      ELSIF n_sep = 0 THEN
        PERFORM lim_record(p_is_cocone, v_cone_diagram, v_cone, 'missing_composite',
          jsonb_build_object('id', p_id, 'm1', pair.m1, 'm2', pair.m2,
                             'undecided_nodes', n_undef));
        n_found := n_found + 1;
      END IF;
    END LOOP;
  END IF;

  IF n_found > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION '% % is not universal (% problem(s))',
      CASE WHEN p_is_cocone THEN 'Colimit' ELSE 'Limit' END, p_id, n_found;
  END IF;
  RETURN n_found = 0;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION verify_limit_universality(p_limit_id UUID) RETURNS BOOLEAN AS $$
  SELECT lim_verify_universality(p_limit_id, FALSE);
$$ LANGUAGE sql;

CREATE OR REPLACE FUNCTION verify_colimit_universality(p_colimit_id UUID) RETURNS BOOLEAN AS $$
  SELECT lim_verify_universality(p_colimit_id, TRUE);
$$ LANGUAGE sql;

-- ---------------------------------------------------------------------------
-- Write-time tier: every new or changed limit / colimit row must point at a
-- valid cone (cocone) over its own diagram.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_limit() RETURNS trigger AS $$
DECLARE
  v_cone_diagram UUID;
BEGIN
  SELECT c.diagram_id INTO v_cone_diagram FROM cone c WHERE c.id = NEW.cone_id;
  IF v_cone_diagram IS DISTINCT FROM NEW.diagram_id THEN
    PERFORM lim_record(FALSE, NEW.diagram_id, NEW.cone_id, 'diagram_mismatch',
      jsonb_build_object('id', NEW.id, 'cone_diagram', v_cone_diagram));
    IF functor_is_strict() THEN
      RAISE EXCEPTION 'Limit % uses a cone over another diagram', NEW.id;
    END IF;
  END IF;
  PERFORM lim_check(NEW.cone_id, FALSE);
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_limit ON "limit";
CREATE TRIGGER trg_check_limit
AFTER INSERT OR UPDATE ON "limit"
FOR EACH ROW EXECUTE FUNCTION trg_check_limit();

CREATE OR REPLACE FUNCTION trg_check_colimit() RETURNS trigger AS $$
DECLARE
  v_cone_diagram UUID;
BEGIN
  SELECT c.diagram_id INTO v_cone_diagram FROM cocone c WHERE c.id = NEW.cocone_id;
  IF v_cone_diagram IS DISTINCT FROM NEW.diagram_id THEN
    PERFORM lim_record(TRUE, NEW.diagram_id, NEW.cocone_id, 'diagram_mismatch',
      jsonb_build_object('id', NEW.id, 'cone_diagram', v_cone_diagram));
    IF functor_is_strict() THEN
      RAISE EXCEPTION 'Colimit % uses a cocone over another diagram', NEW.id;
    END IF;
  END IF;
  PERFORM lim_check(NEW.cocone_id, TRUE);
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_colimit ON colimit;
CREATE TRIGGER trg_check_colimit
AFTER INSERT OR UPDATE ON colimit
FOR EACH ROW EXECUTE FUNCTION trg_check_colimit();

-- ---------------------------------------------------------------------------
-- Convenience: create a cone / cocone (legs are added afterwards), then
-- finalize it as a limit / colimit.  finalize_* refuses an invalid cone in
-- every mode (the problems are logged first).
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION attempt_construct_limit(
  p_diagram_id UUID, p_apex_object_id UUID
) RETURNS UUID AS $$
DECLARE
  c_id UUID;
BEGIN
  INSERT INTO cone (diagram_id, apex_object_id)
  VALUES (p_diagram_id, p_apex_object_id)
  RETURNING id INTO c_id;
  RETURN c_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION attempt_construct_colimit(
  p_diagram_id UUID, p_apex_object_id UUID
) RETURNS UUID AS $$
DECLARE
  c_id UUID;
BEGIN
  INSERT INTO cocone (diagram_id, apex_object_id)
  VALUES (p_diagram_id, p_apex_object_id)
  RETURNING id INTO c_id;
  RETURN c_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION finalize_limit(p_cone_id UUID) RETURNS UUID AS $$
DECLARE
  v_diagram UUID;
  l_id UUID;
BEGIN
  SELECT c.diagram_id INTO v_diagram FROM cone c WHERE c.id = p_cone_id;
  IF v_diagram IS NULL THEN
    RAISE EXCEPTION 'Cone % not found', p_cone_id;
  END IF;
  IF NOT check_cone_commutes(p_cone_id) THEN
    RAISE EXCEPTION 'Cannot finalize limit: cone % is not valid (see limit_violation)', p_cone_id;
  END IF;
  INSERT INTO "limit" (diagram_id, cone_id)
  VALUES (v_diagram, p_cone_id)
  RETURNING id INTO l_id;
  RETURN l_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION finalize_colimit(p_cocone_id UUID) RETURNS UUID AS $$
DECLARE
  v_diagram UUID;
  l_id UUID;
BEGIN
  SELECT c.diagram_id INTO v_diagram FROM cocone c WHERE c.id = p_cocone_id;
  IF v_diagram IS NULL THEN
    RAISE EXCEPTION 'Cocone % not found', p_cocone_id;
  END IF;
  IF NOT check_cocone_commutes(p_cocone_id) THEN
    RAISE EXCEPTION 'Cannot finalize colimit: cocone % is not valid (see colimit_violation)', p_cocone_id;
  END IF;
  INSERT INTO colimit (diagram_id, cocone_id)
  VALUES (v_diagram, p_cocone_id)
  RETURNING id INTO l_id;
  RETURN l_id;
END;
$$ LANGUAGE plpgsql;
