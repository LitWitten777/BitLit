-- ============================================================================
-- Categorical Ledger — Migration 015: Governance Modalities
-- ============================================================================
-- Policies attach to artifacts/morphisms through *modal operators* (□, ◇, !, ?)
-- evaluated over a finite Kripke model of governance contexts; approvals are
-- ordered workflows of role tokens; the audit log is an append-only hash
-- chain.  The Python reference is qbx.governance (modality, policy, approval,
-- audit): every *_problems function below reports the same problems, with the
-- same details, as the Python function it names.
--
-- Recording.
--   modality             the seeded four (governance_seed_modalities()): name,
--                        kind; the table must stay equal to the seed.
--                          □ necessity   alethic frame  backing: a comonad
--                          ◇ possibility alethic frame  backing: a monad
--                          ! obligation  deontic frame  no backing
--                          ? permission  deontic frame  no backing
--                        monad_id / comonad_id: optional backing (migration 006).
--   governance_context   a context (world), e.g. dev / staging / production.
--   governance_access    the accessibility relations: frame 'alethic' (must be
--                        reflexive and transitive) or 'deontic' (must be
--                        serial), from_context_id → to_context_id.
--   policy               name, scope (free text, e.g. 'personal_data'), body (a
--                        JSON object), version MAJOR.MINOR.PATCH,
--                        enforcement_level soft / hard / block_and_alert, and
--                        its modality.
--   policy_modality_assignment  attaches a policy (with its modality) to an
--                        artifact and/or morphism for scope read / write /
--                        execute.
--   policy_check_log     a check of a policy at a context: outcomes is a JSON
--                        object context name → boolean; accessible (set by a
--                        trigger at insert, overriding any given value) is the
--                        array of contexts accessible from the context in the
--                        policy's frame, in code point order; result is
--                        recomputed by the checks.  A check holds when every
--                        accessible context's outcome is true (□, !) or some
--                        is (◇, ?); its result is 'pass' when it holds, else
--                        'warn' for a soft policy and 'fail' otherwise.
--   approval_workflow    steps: a non-empty JSON array of objects with distinct
--                        non-blank "role"s, in approval order; timeout_days in
--                        1–3650.
--   approval_token       a role's approval of an artifact: approved_at <
--                        expires_at ≤ approved_at + timeout_days × 24 h; every
--                        earlier step must already be approved (no later) for
--                        the same artifact.  approval_status(workflow,
--                        artifact, at) is true when every step has a token
--                        without problems valid at `at` (approved_at ≤ at <
--                        expires_at).
--   audit_record         append-only.  On insert a trigger sets seq (1, 2, …),
--                        prev_hash (the previous record_hash, 64 zeros for the
--                        first) and record_hash = audit_record_hash(...): hex
--                        SHA-256 of the fields prev_hash, seq, actor, action,
--                        artifact_id, morphism_id, details (jsonb text),
--                        signature (hex), created_at (µs since the epoch), each
--                        written '-' when NULL, else '<UTF-8 bytes>:<text>'.
--   governance_violation the violation table (subject_table, subject_id,
--                        reason, details).
--
-- Checks.  Every check logs to governance_violation and raises only when
-- qbx.enforcement_mode = 'strict'.  Rows are checked when written (triggers)
-- and in batch (check_governance, part of run_all_batch_checks); the checks
-- marked "batch" need other rows and run only in batch.  Blank text is text of
-- only space, tab, LF, CR, FF, VT (the empty text included).
--   modality (statement trigger; governance_modality_table_problems)
--     modality_missing      a seeded modality has no row (details: name)
--     modality_kind         its kind differs (details: name, expected, found)
--     modality_unknown      a row for something else (details: name)
--   modality (governance_modality_problems)
--     modality_backing      error ∈ monad, comonad: a backing the kind does not
--                           take
--     modality_backing_unlawful  batch: the backing has recorded law
--                           violations (details: structure, violations)
--   governance_context      context_typing (error: name)
--   governance_access (batch; governance_frame_problems; subject: a context)
--     frame_reflexive       alethic: no loop (details: context)
--     frame_transitive      alethic: from → via → to without from → to
--                           (details: from, via (the least), to)
--     frame_serial          deontic: no successor (details: context)
--   policy                  policy_typing (error ∈ name, version, body,
--                           modality, scope, enforcement)
--   policy_modality_assignment
--     assignment_modality   not the policy's modality (details: expected,
--                           found — names)
--     assignment_typing     error ∈ scope, morphism
--     assignment_duplicate  batch: identical assignments (details: count)
--   policy_check_log
--     check_typing          error ∈ policy, modality, context, outcomes
--     check_outcome_missing an accessible context has no outcome (details:
--                           context)
--     check_result          the recorded result is not the computed one
--                           (details: recorded, computed)
--   approval_workflow       workflow_typing (error ∈ name, steps, step (index),
--                           duplicate_role (index), timeout)
--   approval_token
--     token_typing          error ∈ workflow, role, artifact, approved_at,
--                           expires_at, window, timeout
--     token_order           batch: an earlier step not yet approved (details:
--                           role)
--   audit_record            audit_typing (error ∈ actor, action, details)
--   audit_record (batch; governance_audit_chain_problems)
--     audit_chain           error ∈ gap (seq, expected), link (seq), hash (seq)
--   audit_record, policy_check_log (always, at the change)
--     log_mutation          an UPDATE, DELETE or TRUNCATE (details: table, op)
--
-- Writers (register_policy, assign_policy, register_governance_context,
-- register_governance_access, log_policy_check, register_approval_workflow,
-- record_approval, record_audit) refuse input with any problem.
--
-- Formal backing (Formal/Modality.lean): ◇ = ¬□¬ and ? = ¬!¬ (holds_dual);
-- □p ⊆ p for every p iff the frame is reflexive, □p ⊆ □□p iff transitive
-- (box_subset_self_iff, box_subset_box_box_iff; dually for ◇), so □ is a
-- comonad and ◇ a monad on the poset of propositions exactly on preorder
-- frames (boxComonad, diaMonad, diaClosure); !p ⊆ ?p for every p iff the
-- deontic frame is serial (box_subset_dia_iff_serial); the computed result is
-- 'pass' iff the formula holds (result_eq_pass_iff); on well-formed frames a
-- passed □ check implies the outcome at the context itself and passes at every
-- accessible context, and a passed ! check passes as a ? check
-- (necessity_pass_outcome, necessity_pass_stable,
-- obligation_pass_permission_pass); the newest record_hash commits to the
-- whole audit log when the step hash is collision-free (chainHash_injective).
--
-- Phase 1 sprint 12 rewrite.  Running the original on PostgreSQL 16 showed:
--   * register_policy with an unknown modality ('nope') created a policy with
--     no modality; a body 42 and version 'banana' were accepted;
--   * the seeded modalities could be changed (□ made a 'possibility') or
--     deleted; any monad/comonad could back any modality;
--   * an assignment could carry another modality than its policy's and the
--     scope 'fly'; identical assignments were accepted (NULLs defeat UNIQUE);
--   * a check could be logged with no policy, its result was never computed,
--     and checks could be rewritten (UPDATE policy_check_log SET result =
--     'fail');
--   * a workflow with steps '"x"' and timeout −3, and a token of an unknown
--     role expiring before its approval, were accepted;
--   * audit records could be rewritten and deleted without trace;
--   * nothing was logged, and nothing was part of run_all_batch_checks.
-- ============================================================================

CREATE TABLE IF NOT EXISTS modality (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  kind TEXT NOT NULL CHECK (kind IN ('necessity','possibility','obligation','permission')),
  description TEXT,
  monad_id UUID REFERENCES monad(id) ON DELETE SET NULL,
  comonad_id UUID REFERENCES comonad(id) ON DELETE SET NULL,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE OR REPLACE FUNCTION governance_seed_modalities()
RETURNS TABLE(name TEXT, kind TEXT, frame TEXT, structure TEXT, ordinal INT) AS $$
  SELECT * FROM (VALUES
    ('□', 'necessity',   'alethic', 'comonad', 1),
    ('◇', 'possibility', 'alethic', 'monad',   2),
    ('!', 'obligation',  'deontic', NULL,      3),
    ('?', 'permission',  'deontic', NULL,      4)
  ) AS s(name, kind, frame, structure, ordinal);
$$ LANGUAGE sql IMMUTABLE;

INSERT INTO modality (name, kind, description) VALUES
  ('□', 'necessity',  'Necessity (must hold in all accessible contexts)'),
  ('◇', 'possibility','Possibility (holds in some accessible context)'),
  ('!', 'obligation', 'Obligation (required in every deontically ideal context)'),
  ('?', 'permission', 'Permission (allowed in some deontically ideal context)')
ON CONFLICT (name) DO NOTHING;

CREATE TABLE IF NOT EXISTS governance_context (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  description TEXT,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS governance_access (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  frame TEXT NOT NULL CHECK (frame IN ('alethic','deontic')),
  from_context_id UUID NOT NULL REFERENCES governance_context(id) ON DELETE CASCADE,
  to_context_id UUID NOT NULL REFERENCES governance_context(id) ON DELETE CASCADE,
  created_at TIMESTAMPTZ DEFAULT now(),
  UNIQUE (frame, from_context_id, to_context_id)
);

CREATE INDEX IF NOT EXISTS idx_governance_access_to
  ON governance_access (frame, to_context_id);

CREATE TABLE IF NOT EXISTS policy (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL,
  scope TEXT,
  body JSONB NOT NULL,
  version TEXT NOT NULL DEFAULT '1.0.0',
  enforcement_level TEXT DEFAULT 'soft' CHECK (enforcement_level IN ('soft','hard','block_and_alert')),
  modality_id UUID REFERENCES modality(id) ON DELETE SET NULL,
  created_by TEXT,
  created_at TIMESTAMPTZ DEFAULT now(),
  active BOOLEAN DEFAULT TRUE,
  UNIQUE (name, version)
);

CREATE INDEX IF NOT EXISTS idx_policy_modality ON policy (modality_id);

CREATE TABLE IF NOT EXISTS policy_modality_assignment (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  policy_id UUID NOT NULL REFERENCES policy(id) ON DELETE CASCADE,
  modality_id UUID NOT NULL REFERENCES modality(id) ON DELETE CASCADE,
  artifact_id UUID,
  morphism_id UUID,
  scope TEXT,   -- 'read' | 'write' | 'execute'
  metadata JSONB DEFAULT '{}'::jsonb,
  UNIQUE (policy_id, modality_id, artifact_id, morphism_id, scope)
);
ALTER TABLE policy_modality_assignment ADD COLUMN IF NOT EXISTS
  created_at TIMESTAMPTZ DEFAULT now();

CREATE INDEX IF NOT EXISTS idx_policy_assignment_policy
  ON policy_modality_assignment (policy_id);

CREATE TABLE IF NOT EXISTS policy_check_log (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  artifact_id UUID,
  morphism_id UUID,
  policy_id UUID REFERENCES policy(id) ON DELETE SET NULL,
  result TEXT NOT NULL CHECK (result IN ('pass','fail','warn')),
  details JSONB DEFAULT '{}'::jsonb,
  checked_at TIMESTAMPTZ DEFAULT now()
);
ALTER TABLE policy_check_log ADD COLUMN IF NOT EXISTS
  context_id UUID REFERENCES governance_context(id) ON DELETE SET NULL;
ALTER TABLE policy_check_log ADD COLUMN IF NOT EXISTS outcomes JSONB;
ALTER TABLE policy_check_log ADD COLUMN IF NOT EXISTS accessible TEXT[];

CREATE INDEX IF NOT EXISTS idx_policy_check_log_artifact
  ON policy_check_log (artifact_id, checked_at DESC);
CREATE INDEX IF NOT EXISTS idx_policy_check_log_policy
  ON policy_check_log (policy_id);

CREATE TABLE IF NOT EXISTS approval_workflow (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  steps JSONB NOT NULL,       -- ordered list of step descriptors {"role": ...}
  timeout_days INT DEFAULT 7,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS approval_token (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  workflow_id UUID NOT NULL REFERENCES approval_workflow(id) ON DELETE CASCADE,
  artifact_id UUID,
  approver_role TEXT,
  approved_at TIMESTAMPTZ,
  expires_at TIMESTAMPTZ,
  signature BYTEA,
  metadata JSONB DEFAULT '{}'::jsonb
);
ALTER TABLE approval_token ADD COLUMN IF NOT EXISTS
  created_at TIMESTAMPTZ DEFAULT now();

CREATE INDEX IF NOT EXISTS idx_approval_token_lookup
  ON approval_token (workflow_id, artifact_id, approver_role, approved_at);

CREATE TABLE IF NOT EXISTS audit_record (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  actor TEXT NOT NULL,
  action TEXT NOT NULL,
  artifact_id UUID,
  morphism_id UUID,
  details JSONB DEFAULT '{}'::jsonb,
  signature BYTEA,
  created_at TIMESTAMPTZ DEFAULT now()
);
ALTER TABLE audit_record ADD COLUMN IF NOT EXISTS seq BIGINT;
ALTER TABLE audit_record ADD COLUMN IF NOT EXISTS prev_hash TEXT;
ALTER TABLE audit_record ADD COLUMN IF NOT EXISTS record_hash TEXT;

CREATE INDEX IF NOT EXISTS idx_audit_record_actor
  ON audit_record (actor, created_at DESC);
CREATE UNIQUE INDEX IF NOT EXISTS idx_audit_record_seq ON audit_record (seq);

CREATE TABLE IF NOT EXISTS governance_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  subject_table TEXT NOT NULL,
  subject_id UUID,
  reason TEXT NOT NULL,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_governance_violation_subject
  ON governance_violation (subject_table, subject_id, detected_at DESC);

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION gov_blank(p TEXT) RETURNS BOOLEAN AS $$
  -- space, tab, LF, CR, FF, VT (E'' strings have no \v escape)
  SELECT p IS NULL OR translate(p, ' ' || chr(9) || chr(10) || chr(13) || chr(12) || chr(11), '') = '';
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION gov_problem(p_reason TEXT, p_details JSONB)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT p_reason, p_details;
$$ LANGUAGE sql IMMUTABLE;

-- The frame a modality kind is evaluated on.
CREATE OR REPLACE FUNCTION governance_kind_frame(p_kind TEXT) RETURNS TEXT AS $$
  SELECT s.frame FROM governance_seed_modalities() s WHERE s.kind = p_kind;
$$ LANGUAGE sql IMMUTABLE;

-- The contexts accessible from p_context in p_frame, in code point order.
CREATE OR REPLACE FUNCTION governance_accessible(p_frame TEXT, p_context UUID) RETURNS TEXT[] AS $$
  SELECT coalesce(array_agg(c.name ORDER BY c.name COLLATE "C"), ARRAY[]::text[])
    FROM governance_access a JOIN governance_context c ON c.id = a.to_context_id
   WHERE a.frame = p_frame AND a.from_context_id = p_context;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Modalities (qbx.governance.modality)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION governance_modality_table_problems()
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  s RECORD;
  r RECORD;
BEGIN
  FOR s IN SELECT * FROM governance_seed_modalities() x ORDER BY x.ordinal LOOP
    SELECT m.* INTO r FROM modality m WHERE m.name = s.name;
    IF NOT FOUND THEN
      reason := 'modality_missing'; details := jsonb_build_object('name', s.name); RETURN NEXT;
    ELSIF r.kind IS DISTINCT FROM s.kind THEN
      reason := 'modality_kind';
      details := jsonb_build_object('name', s.name, 'expected', s.kind, 'found', r.kind);
      RETURN NEXT;
    END IF;
  END LOOP;
  FOR r IN SELECT m.name FROM modality m
            WHERE m.name NOT IN (SELECT x.name FROM governance_seed_modalities() x)
            ORDER BY m.name COLLATE "C" LOOP
    reason := 'modality_unknown'; details := jsonb_build_object('name', r.name); RETURN NEXT;
  END LOOP;
END;
$$ LANGUAGE plpgsql STABLE;

-- qbx.governance.modality.modality_problems (violation counts NULL: write time).
CREATE OR REPLACE FUNCTION governance_modality_values_problems(
  p_kind TEXT, p_has_monad BOOLEAN, p_has_comonad BOOLEAN,
  p_monad_violations BIGINT DEFAULT NULL, p_comonad_violations BIGINT DEFAULT NULL
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  allowed TEXT := (SELECT s.structure FROM governance_seed_modalities() s WHERE s.kind = p_kind);
BEGIN
  IF p_has_monad AND allowed IS DISTINCT FROM 'monad' THEN
    RETURN QUERY SELECT * FROM gov_problem('modality_backing', '{"error":"monad"}');
  END IF;
  IF p_has_comonad AND allowed IS DISTINCT FROM 'comonad' THEN
    RETURN QUERY SELECT * FROM gov_problem('modality_backing', '{"error":"comonad"}');
  END IF;
  IF p_has_monad AND allowed = 'monad' AND coalesce(p_monad_violations, 0) > 0 THEN
    RETURN QUERY SELECT * FROM gov_problem('modality_backing_unlawful',
      jsonb_build_object('structure', 'monad', 'violations', p_monad_violations));
  END IF;
  IF p_has_comonad AND allowed = 'comonad' AND coalesce(p_comonad_violations, 0) > 0 THEN
    RETURN QUERY SELECT * FROM gov_problem('modality_backing_unlawful',
      jsonb_build_object('structure', 'comonad', 'violations', p_comonad_violations));
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION governance_modality_problems(p_id UUID, p_batch BOOLEAN DEFAULT TRUE)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  m RECORD;
BEGIN
  SELECT * INTO m FROM modality WHERE id = p_id;
  IF NOT FOUND THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM governance_modality_values_problems(
    m.kind, m.monad_id IS NOT NULL, m.comonad_id IS NOT NULL,
    CASE WHEN p_batch THEN (SELECT count(*) FROM monad_violation v WHERE v.monad_id = m.monad_id) END,
    CASE WHEN p_batch THEN (SELECT count(*) FROM comonad_violation v WHERE v.comonad_id = m.comonad_id) END);
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Contexts and frames (qbx.governance.policy)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION governance_context_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT 'context_typing'::text, '{"error":"name"}'::jsonb
    FROM governance_context c WHERE c.id = p_id AND gov_blank(c.name);
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION governance_frame_problems(p_frame TEXT)
RETURNS TABLE(subject_id UUID, reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
BEGIN
  IF p_frame = 'alethic' THEN
    FOR c IN SELECT g.id, g.name FROM governance_context g ORDER BY g.name COLLATE "C" LOOP
      IF NOT EXISTS (SELECT 1 FROM governance_access a WHERE a.frame = 'alethic'
                        AND a.from_context_id = c.id AND a.to_context_id = c.id) THEN
        subject_id := c.id; reason := 'frame_reflexive';
        details := jsonb_build_object('context', c.name); RETURN NEXT;
      END IF;
    END LOOP;
    FOR c IN
      SELECT ca.id, ca.name AS fname, cc.name AS tname, min(cb.name COLLATE "C") AS via
        FROM governance_access x
        JOIN governance_access y ON y.frame = 'alethic' AND y.from_context_id = x.to_context_id
        JOIN governance_context ca ON ca.id = x.from_context_id
        JOIN governance_context cb ON cb.id = x.to_context_id
        JOIN governance_context cc ON cc.id = y.to_context_id
       WHERE x.frame = 'alethic'
         AND NOT EXISTS (SELECT 1 FROM governance_access z WHERE z.frame = 'alethic'
                            AND z.from_context_id = x.from_context_id
                            AND z.to_context_id = y.to_context_id)
       GROUP BY ca.id, ca.name, cc.name
       ORDER BY ca.name COLLATE "C", cc.name COLLATE "C"
    LOOP
      subject_id := c.id; reason := 'frame_transitive';
      details := jsonb_build_object('from', c.fname, 'via', c.via, 'to', c.tname); RETURN NEXT;
    END LOOP;
  ELSIF p_frame = 'deontic' THEN
    FOR c IN SELECT g.id, g.name FROM governance_context g ORDER BY g.name COLLATE "C" LOOP
      IF NOT EXISTS (SELECT 1 FROM governance_access a WHERE a.frame = 'deontic'
                        AND a.from_context_id = c.id) THEN
        subject_id := c.id; reason := 'frame_serial';
        details := jsonb_build_object('context', c.name); RETURN NEXT;
      END IF;
    END LOOP;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Policies and assignments
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION governance_policy_values_problems(
  p_name TEXT, p_version TEXT, p_body JSONB, p_has_modality BOOLEAN,
  p_scope TEXT, p_enforcement TEXT
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF gov_blank(p_name) THEN
    RETURN QUERY SELECT * FROM gov_problem('policy_typing', '{"error":"name"}');
  END IF;
  IF p_version IS NULL
     OR p_version !~ '^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$' THEN
    RETURN QUERY SELECT * FROM gov_problem('policy_typing', '{"error":"version"}');
  END IF;
  IF p_body IS NULL OR jsonb_typeof(p_body) <> 'object' THEN
    RETURN QUERY SELECT * FROM gov_problem('policy_typing', '{"error":"body"}');
  END IF;
  IF NOT coalesce(p_has_modality, FALSE) THEN
    RETURN QUERY SELECT * FROM gov_problem('policy_typing', '{"error":"modality"}');
  END IF;
  IF p_scope IS NOT NULL AND gov_blank(p_scope) THEN
    RETURN QUERY SELECT * FROM gov_problem('policy_typing', '{"error":"scope"}');
  END IF;
  IF p_enforcement IS NULL THEN
    RETURN QUERY SELECT * FROM gov_problem('policy_typing', '{"error":"enforcement"}');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION governance_policy_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM policy p,
    LATERAL governance_policy_values_problems(p.name, p.version, p.body,
                                              p.modality_id IS NOT NULL, p.scope,
                                              p.enforcement_level) pr
   WHERE p.id = p_id;
$$ LANGUAGE sql STABLE;

-- qbx.governance.policy.assignment_problems (p_morphism_exists NULL: none
-- given; p_duplicates NULL: write time).
CREATE OR REPLACE FUNCTION governance_assignment_values_problems(
  p_policy_modality TEXT, p_modality TEXT, p_scope TEXT,
  p_morphism_exists BOOLEAN, p_duplicates BIGINT DEFAULT NULL
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF p_policy_modality IS DISTINCT FROM p_modality THEN
    RETURN QUERY SELECT * FROM gov_problem('assignment_modality',
      jsonb_build_object('expected', p_policy_modality, 'found', p_modality));
  END IF;
  IF p_scope IS NULL OR p_scope NOT IN ('read', 'write', 'execute') THEN
    RETURN QUERY SELECT * FROM gov_problem('assignment_typing', '{"error":"scope"}');
  END IF;
  IF p_morphism_exists IS FALSE THEN
    RETURN QUERY SELECT * FROM gov_problem('assignment_typing', '{"error":"morphism"}');
  END IF;
  IF p_duplicates IS NOT NULL AND p_duplicates > 1 THEN
    RETURN QUERY SELECT * FROM gov_problem('assignment_duplicate',
      jsonb_build_object('count', p_duplicates));
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION governance_assignment_problems(p_id UUID, p_batch BOOLEAN DEFAULT TRUE)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  a RECORD;
BEGIN
  SELECT * INTO a FROM policy_modality_assignment WHERE id = p_id;
  IF NOT FOUND THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM governance_assignment_values_problems(
    (SELECT m.name FROM policy p JOIN modality m ON m.id = p.modality_id WHERE p.id = a.policy_id),
    (SELECT m.name FROM modality m WHERE m.id = a.modality_id),
    a.scope,
    CASE WHEN a.morphism_id IS NULL THEN NULL
         ELSE EXISTS (SELECT 1 FROM morphism mo WHERE mo.id = a.morphism_id) END,
    CASE WHEN p_batch THEN
      (SELECT count(*) FROM policy_modality_assignment b
        WHERE b.policy_id = a.policy_id AND b.modality_id = a.modality_id
          AND b.artifact_id IS NOT DISTINCT FROM a.artifact_id
          AND b.morphism_id IS NOT DISTINCT FROM a.morphism_id
          AND b.scope IS NOT DISTINCT FROM a.scope) END);
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Policy checks
-- ---------------------------------------------------------------------------
-- The result of a check whose accessible contexts all have an outcome: 'pass'
-- when it holds (every outcome true for necessity / obligation, some for
-- possibility / permission), else 'warn' (soft) or 'fail'.
CREATE OR REPLACE FUNCTION governance_check_result(
  p_kind TEXT, p_enforcement TEXT, p_outcomes JSONB, p_accessible TEXT[]
) RETURNS TEXT AS $$
DECLARE
  holds BOOLEAN;
BEGIN
  IF p_kind IN ('necessity', 'obligation') THEN
    SELECT coalesce(bool_and((p_outcomes -> x)::text = 'true'), TRUE) INTO holds
      FROM unnest(coalesce(p_accessible, ARRAY[]::text[])) x;
  ELSE
    SELECT coalesce(bool_or((p_outcomes -> x)::text = 'true'), FALSE) INTO holds
      FROM unnest(coalesce(p_accessible, ARRAY[]::text[])) x;
  END IF;
  RETURN CASE WHEN holds THEN 'pass' WHEN p_enforcement = 'soft' THEN 'warn' ELSE 'fail' END;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- qbx.governance.policy.check_problems.
CREATE OR REPLACE FUNCTION governance_check_values_problems(
  p_has_policy BOOLEAN, p_kind TEXT, p_enforcement TEXT, p_has_context BOOLEAN,
  p_outcomes JSONB, p_recorded TEXT, p_accessible TEXT[]
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  typed BOOLEAN := TRUE;
  c TEXT;
  missing BOOLEAN := FALSE;
  computed TEXT;
BEGIN
  IF NOT coalesce(p_has_policy, FALSE) THEN
    typed := FALSE;
    RETURN QUERY SELECT * FROM gov_problem('check_typing', '{"error":"policy"}');
  ELSIF p_kind IS NULL THEN
    typed := FALSE;
    RETURN QUERY SELECT * FROM gov_problem('check_typing', '{"error":"modality"}');
  END IF;
  IF NOT coalesce(p_has_context, FALSE) THEN
    typed := FALSE;
    RETURN QUERY SELECT * FROM gov_problem('check_typing', '{"error":"context"}');
  END IF;
  IF p_outcomes IS NULL OR jsonb_typeof(p_outcomes) <> 'object'
     OR EXISTS (SELECT 1 FROM jsonb_each(p_outcomes) e WHERE jsonb_typeof(e.value) <> 'boolean') THEN
    typed := FALSE;
    RETURN QUERY SELECT * FROM gov_problem('check_typing', '{"error":"outcomes"}');
  END IF;
  IF NOT typed THEN RETURN; END IF;
  FOREACH c IN ARRAY coalesce(p_accessible, ARRAY[]::text[]) LOOP
    IF NOT (p_outcomes ? c) THEN
      missing := TRUE;
      RETURN QUERY SELECT * FROM gov_problem('check_outcome_missing', jsonb_build_object('context', c));
    END IF;
  END LOOP;
  IF missing THEN RETURN; END IF;
  computed := governance_check_result(p_kind, p_enforcement, p_outcomes, p_accessible);
  IF p_recorded IS DISTINCT FROM computed THEN
    RETURN QUERY SELECT * FROM gov_problem('check_result',
      jsonb_build_object('recorded', p_recorded, 'computed', computed));
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION governance_check_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM policy_check_log l
    LEFT JOIN policy p ON p.id = l.policy_id
    LEFT JOIN modality m ON m.id = p.modality_id,
    LATERAL governance_check_values_problems(p.id IS NOT NULL, m.kind, p.enforcement_level,
                                             l.context_id IS NOT NULL, l.outcomes, l.result,
                                             l.accessible) pr
   WHERE l.id = p_id;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Approval workflows and tokens (qbx.governance.approval)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION governance_workflow_values_problems(
  p_name TEXT, p_steps JSONB, p_timeout INT
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  i INT;
  s JSONB;
  seen TEXT[] := ARRAY[]::text[];
BEGIN
  IF gov_blank(p_name) THEN
    RETURN QUERY SELECT * FROM gov_problem('workflow_typing', '{"error":"name"}');
  END IF;
  IF p_steps IS NULL OR jsonb_typeof(p_steps) <> 'array' OR jsonb_array_length(p_steps) = 0 THEN
    RETURN QUERY SELECT * FROM gov_problem('workflow_typing', '{"error":"steps"}');
  ELSE
    FOR i IN 0 .. jsonb_array_length(p_steps) - 1 LOOP
      s := p_steps -> i;
      IF jsonb_typeof(s) <> 'object' OR jsonb_typeof(s -> 'role') IS DISTINCT FROM 'string'
         OR gov_blank(s ->> 'role') THEN
        RETURN QUERY SELECT * FROM gov_problem('workflow_typing',
          jsonb_build_object('error', 'step', 'index', i));
      ELSIF (s ->> 'role') = ANY (seen) THEN
        RETURN QUERY SELECT * FROM gov_problem('workflow_typing',
          jsonb_build_object('error', 'duplicate_role', 'index', i));
      ELSE
        seen := seen || (s ->> 'role');
      END IF;
    END LOOP;
  END IF;
  IF p_timeout IS NULL OR p_timeout < 1 OR p_timeout > 3650 THEN
    RETURN QUERY SELECT * FROM gov_problem('workflow_typing', '{"error":"timeout"}');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION governance_workflow_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM approval_workflow w,
    LATERAL governance_workflow_values_problems(w.name, w.steps, w.timeout_days) pr
   WHERE w.id = p_id;
$$ LANGUAGE sql STABLE;

-- The step roles in order; NULL when the workflow has problems.
CREATE OR REPLACE FUNCTION governance_workflow_roles(p_id UUID) RETURNS TEXT[] AS $$
  SELECT CASE WHEN EXISTS (SELECT 1 FROM governance_workflow_problems(w.id)) THEN NULL
              ELSE ARRAY(SELECT e.value ->> 'role'
                           FROM jsonb_array_elements(w.steps) WITH ORDINALITY e(value, n)
                          ORDER BY e.n) END
    FROM approval_workflow w WHERE w.id = p_id;
$$ LANGUAGE sql STABLE;

-- qbx.governance.approval.token_problems without the order check.
CREATE OR REPLACE FUNCTION governance_token_values_problems(
  p_roles TEXT[], p_timeout INT, p_has_artifact BOOLEAN, p_role TEXT,
  p_approved_at TIMESTAMPTZ, p_expires_at TIMESTAMPTZ
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF p_roles IS NULL THEN
    RETURN QUERY SELECT * FROM gov_problem('token_typing', '{"error":"workflow"}');
  ELSIF p_role IS NULL OR NOT (p_role = ANY (p_roles)) THEN
    RETURN QUERY SELECT * FROM gov_problem('token_typing', '{"error":"role"}');
  END IF;
  IF NOT coalesce(p_has_artifact, FALSE) THEN
    RETURN QUERY SELECT * FROM gov_problem('token_typing', '{"error":"artifact"}');
  END IF;
  IF p_approved_at IS NULL THEN
    RETURN QUERY SELECT * FROM gov_problem('token_typing', '{"error":"approved_at"}');
  END IF;
  IF p_expires_at IS NULL THEN
    RETURN QUERY SELECT * FROM gov_problem('token_typing', '{"error":"expires_at"}');
  END IF;
  IF p_approved_at IS NOT NULL AND p_expires_at IS NOT NULL THEN
    IF p_expires_at <= p_approved_at THEN
      RETURN QUERY SELECT * FROM gov_problem('token_typing', '{"error":"window"}');
    ELSIF p_roles IS NOT NULL
          AND p_expires_at - p_approved_at > interval '24 hours' * p_timeout THEN
      RETURN QUERY SELECT * FROM gov_problem('token_typing', '{"error":"timeout"}');
    END IF;
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION governance_token_problems(p_id UUID, p_batch BOOLEAN DEFAULT TRUE)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  t RECORD;
  roles TEXT[];
  timeout INT;
  idx INT;
  r TEXT;
BEGIN
  SELECT * INTO t FROM approval_token WHERE id = p_id;
  IF NOT FOUND THEN RETURN; END IF;
  roles := governance_workflow_roles(t.workflow_id);
  timeout := (SELECT w.timeout_days FROM approval_workflow w WHERE w.id = t.workflow_id);
  RETURN QUERY SELECT * FROM governance_token_values_problems(
    roles, timeout, t.artifact_id IS NOT NULL, t.approver_role, t.approved_at, t.expires_at);
  IF p_batch AND roles IS NOT NULL AND t.approver_role = ANY (roles)
     AND t.approved_at IS NOT NULL AND t.artifact_id IS NOT NULL THEN
    idx := array_position(roles, t.approver_role);
    FOR i IN 1 .. idx - 1 LOOP
      r := roles[i];
      IF NOT EXISTS (SELECT 1 FROM approval_token o
                      WHERE o.workflow_id = t.workflow_id AND o.artifact_id = t.artifact_id
                        AND o.approver_role = r AND o.approved_at <= t.approved_at) THEN
        RETURN QUERY SELECT * FROM gov_problem('token_order', jsonb_build_object('role', r));
      END IF;
    END LOOP;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- Is the artifact approved by the workflow at p_at?  Every step needs a token
-- without problems (order included) whose window contains p_at.
CREATE OR REPLACE FUNCTION approval_status(
  p_workflow UUID, p_artifact UUID, p_at TIMESTAMPTZ DEFAULT now()
) RETURNS BOOLEAN AS $$
DECLARE
  roles TEXT[] := governance_workflow_roles(p_workflow);
  r TEXT;
BEGIN
  IF roles IS NULL THEN RETURN FALSE; END IF;
  FOREACH r IN ARRAY roles LOOP
    IF NOT EXISTS (
      SELECT 1 FROM approval_token o
       WHERE o.workflow_id = p_workflow AND o.artifact_id = p_artifact
         AND o.approver_role = r AND o.approved_at <= p_at AND p_at < o.expires_at
         AND NOT EXISTS (SELECT 1 FROM governance_token_problems(o.id, TRUE))) THEN
      RETURN FALSE;
    END IF;
  END LOOP;
  RETURN TRUE;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- The audit hash chain (qbx.governance.audit)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION audit_field(p TEXT) RETURNS TEXT AS $$
  SELECT CASE WHEN p IS NULL THEN '-' ELSE octet_length(p)::text || ':' || p END;
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION audit_record_hash(
  p_prev TEXT, p_seq BIGINT, p_actor TEXT, p_action TEXT, p_artifact UUID,
  p_morphism UUID, p_details JSONB, p_signature BYTEA, p_created TIMESTAMPTZ
) RETURNS TEXT AS $$
  SELECT encode(digest(convert_to(
           audit_field(p_prev) || audit_field(p_seq::text) || audit_field(p_actor)
           || audit_field(p_action) || audit_field(p_artifact::text)
           || audit_field(p_morphism::text) || audit_field(p_details::text)
           || audit_field(encode(p_signature, 'hex'))
           || audit_field(((extract(epoch FROM p_created) * 1000000)::bigint)::text),
           'UTF8'), 'sha256'), 'hex');
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION governance_audit_values_problems(
  p_actor TEXT, p_action TEXT, p_details JSONB
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF gov_blank(p_actor) THEN
    RETURN QUERY SELECT * FROM gov_problem('audit_typing', '{"error":"actor"}');
  END IF;
  IF gov_blank(p_action) THEN
    RETURN QUERY SELECT * FROM gov_problem('audit_typing', '{"error":"action"}');
  END IF;
  IF p_details IS NULL OR jsonb_typeof(p_details) <> 'object' THEN
    RETURN QUERY SELECT * FROM gov_problem('audit_typing', '{"error":"details"}');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION governance_audit_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM audit_record a,
    LATERAL governance_audit_values_problems(a.actor, a.action, a.details) pr
   WHERE a.id = p_id;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION governance_audit_chain_problems()
RETURNS TABLE(subject_id UUID, reason TEXT, details JSONB) AS $$
DECLARE
  a RECORD;
  expected_prev TEXT := repeat('0', 64);
  expected_seq BIGINT := 1;
BEGIN
  FOR a IN SELECT * FROM audit_record ORDER BY seq NULLS LAST, id LOOP
    subject_id := a.id; reason := 'audit_chain';
    IF a.seq IS DISTINCT FROM expected_seq THEN
      details := jsonb_build_object('error', 'gap', 'seq', a.seq, 'expected', expected_seq);
      RETURN NEXT;
    END IF;
    IF a.prev_hash IS DISTINCT FROM expected_prev THEN
      details := jsonb_build_object('error', 'link', 'seq', a.seq); RETURN NEXT;
    END IF;
    IF a.record_hash IS DISTINCT FROM audit_record_hash(a.prev_hash, a.seq, a.actor, a.action,
         a.artifact_id, a.morphism_id, a.details, a.signature, a.created_at) THEN
      details := jsonb_build_object('error', 'hash', 'seq', a.seq); RETURN NEXT;
    END IF;
    expected_prev := a.record_hash;
    expected_seq := coalesce(a.seq, 0) + 1;
  END LOOP;
END;
$$ LANGUAGE plpgsql STABLE;

-- Upgrade: chain existing records (created_at, id order) that have no seq.
DO $$
DECLARE
  a RECORD;
  last_seq BIGINT;
  last_hash TEXT;
BEGIN
  SELECT r.seq, r.record_hash INTO last_seq, last_hash
    FROM audit_record r WHERE r.seq IS NOT NULL ORDER BY r.seq DESC LIMIT 1;
  last_seq := coalesce(last_seq, 0);
  last_hash := coalesce(last_hash, repeat('0', 64));
  FOR a IN SELECT * FROM audit_record WHERE seq IS NULL ORDER BY created_at, id LOOP
    last_seq := last_seq + 1;
    UPDATE audit_record
       SET seq = last_seq, prev_hash = last_hash,
           record_hash = audit_record_hash(last_hash, last_seq, a.actor, a.action, a.artifact_id,
                                           a.morphism_id, a.details, a.signature, a.created_at)
     WHERE id = a.id
    RETURNING record_hash INTO last_hash;
  END LOOP;
END $$;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION governance_record(p_table TEXT, p_id UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  INSERT INTO governance_violation (subject_table, subject_id, reason, details)
  VALUES (p_table, p_id, p_reason, coalesce(p_details, '{}'::jsonb));
END;
$$ LANGUAGE plpgsql;

-- The problems of one row, or of the modality table (p_table 'modality_table').
CREATE OR REPLACE FUNCTION governance_problems_of(p_table TEXT, p_id UUID, p_batch BOOLEAN)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  CASE p_table
    WHEN 'modality_table' THEN RETURN QUERY SELECT * FROM governance_modality_table_problems();
    WHEN 'modality' THEN RETURN QUERY SELECT * FROM governance_modality_problems(p_id, p_batch);
    WHEN 'governance_context' THEN RETURN QUERY SELECT * FROM governance_context_problems(p_id);
    WHEN 'policy' THEN RETURN QUERY SELECT * FROM governance_policy_problems(p_id);
    WHEN 'policy_modality_assignment' THEN
      RETURN QUERY SELECT * FROM governance_assignment_problems(p_id, p_batch);
    WHEN 'policy_check_log' THEN RETURN QUERY SELECT * FROM governance_check_problems(p_id);
    WHEN 'approval_workflow' THEN RETURN QUERY SELECT * FROM governance_workflow_problems(p_id);
    WHEN 'approval_token' THEN RETURN QUERY SELECT * FROM governance_token_problems(p_id, p_batch);
    WHEN 'audit_record' THEN RETURN QUERY SELECT * FROM governance_audit_problems(p_id);
  END CASE;
END;
$$ LANGUAGE plpgsql;

-- Check one row: log every problem; returns their number.
CREATE OR REPLACE FUNCTION governance_check_row(p_table TEXT, p_id UUID, p_batch BOOLEAN DEFAULT TRUE)
RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM governance_problems_of(p_table, p_id, p_batch) LOOP
    PERFORM governance_record(CASE WHEN p_table = 'modality_table' THEN 'modality' ELSE p_table END,
                              p_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION governance_check_raise(p_n INT, p_what TEXT) RETURNS VOID AS $$
BEGIN
  IF p_n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION '% (% problem(s))', p_what, p_n;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- Both frames: log every problem; returns their number.
CREATE OR REPLACE FUNCTION check_governance_frames() RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM governance_frame_problems('alethic')
            UNION ALL SELECT * FROM governance_frame_problems('deontic') LOOP
    PERFORM governance_record('governance_context', pr.subject_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  PERFORM governance_check_raise(n, 'The governance frames are not well formed');
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- The audit hash chain: log every problem; returns their number.
CREATE OR REPLACE FUNCTION check_audit_chain() RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM governance_audit_chain_problems() LOOP
    PERFORM governance_record('audit_record', pr.subject_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  PERFORM governance_check_raise(n, 'The audit hash chain is broken');
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- Everything: the modality table, every row of every governance table, the
-- frames and the audit chain.  Returns the number of problems found.
CREATE OR REPLACE FUNCTION check_governance() RETURNS INT AS $$
DECLARE
  t RECORD;
  n INT;
  pr RECORD;
BEGIN
  n := governance_check_row('modality_table', NULL);
  FOR t IN SELECT 'governance_context' AS tb, id FROM governance_context
           UNION ALL SELECT 'modality', id FROM modality
           UNION ALL SELECT 'policy', id FROM policy
           UNION ALL SELECT 'policy_modality_assignment', id FROM policy_modality_assignment
           UNION ALL SELECT 'policy_check_log', id FROM policy_check_log
           UNION ALL SELECT 'approval_workflow', id FROM approval_workflow
           UNION ALL SELECT 'approval_token', id FROM approval_token
           UNION ALL SELECT 'audit_record', id FROM audit_record LOOP
    n := n + governance_check_row(t.tb, t.id);
  END LOOP;
  FOR pr IN SELECT * FROM governance_frame_problems('alethic')
            UNION ALL SELECT * FROM governance_frame_problems('deontic') LOOP
    PERFORM governance_record('governance_context', pr.subject_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  FOR pr IN SELECT * FROM governance_audit_chain_problems() LOOP
    PERFORM governance_record('audit_record', pr.subject_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  PERFORM governance_check_raise(n, 'Governance tables have problems');
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
-- Generic row check (write-time checks only): log, and raise in strict mode.
CREATE OR REPLACE FUNCTION trg_check_governance_row() RETURNS trigger AS $$
DECLARE
  n INT;
BEGIN
  n := governance_check_row(TG_TABLE_NAME, NEW.id, FALSE);
  PERFORM governance_check_raise(n, format('%s row %s is not well formed', TG_TABLE_NAME, NEW.id));
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_governance_row ON modality;
CREATE TRIGGER trg_check_governance_row AFTER INSERT OR UPDATE ON modality
FOR EACH ROW EXECUTE FUNCTION trg_check_governance_row();
DROP TRIGGER IF EXISTS trg_check_governance_row ON governance_context;
CREATE TRIGGER trg_check_governance_row AFTER INSERT OR UPDATE ON governance_context
FOR EACH ROW EXECUTE FUNCTION trg_check_governance_row();
DROP TRIGGER IF EXISTS trg_check_governance_row ON policy;
CREATE TRIGGER trg_check_governance_row AFTER INSERT OR UPDATE ON policy
FOR EACH ROW EXECUTE FUNCTION trg_check_governance_row();
DROP TRIGGER IF EXISTS trg_check_governance_row ON policy_modality_assignment;
CREATE TRIGGER trg_check_governance_row AFTER INSERT OR UPDATE ON policy_modality_assignment
FOR EACH ROW EXECUTE FUNCTION trg_check_governance_row();
DROP TRIGGER IF EXISTS trg_check_governance_row ON approval_workflow;
CREATE TRIGGER trg_check_governance_row AFTER INSERT OR UPDATE ON approval_workflow
FOR EACH ROW EXECUTE FUNCTION trg_check_governance_row();
DROP TRIGGER IF EXISTS trg_check_governance_row ON approval_token;
CREATE TRIGGER trg_check_governance_row AFTER INSERT OR UPDATE ON approval_token
FOR EACH ROW EXECUTE FUNCTION trg_check_governance_row();
-- The two logs are append-only: only inserts are checked here.
DROP TRIGGER IF EXISTS trg_check_governance_row ON policy_check_log;
CREATE TRIGGER trg_check_governance_row AFTER INSERT ON policy_check_log
FOR EACH ROW EXECUTE FUNCTION trg_check_governance_row();
DROP TRIGGER IF EXISTS trg_check_governance_row ON audit_record;
CREATE TRIGGER trg_check_governance_row AFTER INSERT ON audit_record
FOR EACH ROW EXECUTE FUNCTION trg_check_governance_row();

-- Any change to the modality table is compared with the seed.
CREATE OR REPLACE FUNCTION trg_check_governance_modalities() RETURNS trigger AS $$
DECLARE
  n INT;
BEGIN
  n := governance_check_row('modality_table', NULL);
  PERFORM governance_check_raise(n, 'The modality table differs from the seed');
  RETURN NULL;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_governance_modalities ON modality;
CREATE TRIGGER trg_check_governance_modalities
AFTER INSERT OR UPDATE OR DELETE OR TRUNCATE ON modality
FOR EACH STATEMENT EXECUTE FUNCTION trg_check_governance_modalities();

-- A check stores the contexts it was evaluated against.
CREATE OR REPLACE FUNCTION trg_policy_check_snapshot() RETURNS trigger AS $$
DECLARE
  k TEXT;
BEGIN
  SELECT m.kind INTO k FROM policy p JOIN modality m ON m.id = p.modality_id
   WHERE p.id = NEW.policy_id;
  IF k IS NULL OR NEW.context_id IS NULL THEN
    NEW.accessible := NULL;
  ELSE
    NEW.accessible := governance_accessible(governance_kind_frame(k), NEW.context_id);
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_policy_check_snapshot ON policy_check_log;
CREATE TRIGGER trg_policy_check_snapshot BEFORE INSERT ON policy_check_log
FOR EACH ROW EXECUTE FUNCTION trg_policy_check_snapshot();

-- An audit record is numbered, linked and hashed when inserted.
CREATE OR REPLACE FUNCTION trg_audit_chain() RETURNS trigger AS $$
DECLARE
  last_seq BIGINT;
  last_hash TEXT;
BEGIN
  PERFORM pg_advisory_xact_lock(hashtext('qbx.audit_record'));
  SELECT r.seq, r.record_hash INTO last_seq, last_hash
    FROM audit_record r WHERE r.seq IS NOT NULL ORDER BY r.seq DESC LIMIT 1;
  NEW.seq := coalesce(last_seq, 0) + 1;
  NEW.prev_hash := coalesce(last_hash, repeat('0', 64));
  NEW.created_at := coalesce(NEW.created_at, now());
  NEW.record_hash := audit_record_hash(NEW.prev_hash, NEW.seq, NEW.actor, NEW.action,
                                       NEW.artifact_id, NEW.morphism_id, NEW.details,
                                       NEW.signature, NEW.created_at);
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_audit_chain ON audit_record;
CREATE TRIGGER trg_audit_chain BEFORE INSERT ON audit_record
FOR EACH ROW EXECUTE FUNCTION trg_audit_chain();

-- The logs are append-only: an UPDATE, DELETE or TRUNCATE is logged (and
-- refused in strict mode).  A foreign-key SET NULL (deleting a policy or a
-- context that checks refer to) is an UPDATE and is logged too.
CREATE OR REPLACE FUNCTION trg_governance_append_only() RETURNS trigger AS $$
BEGIN
  PERFORM governance_record(TG_TABLE_NAME, CASE WHEN TG_LEVEL = 'ROW' THEN OLD.id END,
                            'log_mutation', jsonb_build_object('table', TG_TABLE_NAME, 'op', TG_OP));
  IF functor_is_strict() THEN
    RAISE EXCEPTION '% on % refused: the log is append-only', TG_OP, TG_TABLE_NAME;
  END IF;
  IF TG_OP = 'DELETE' THEN RETURN OLD; END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_governance_append_only ON audit_record;
CREATE TRIGGER trg_governance_append_only BEFORE UPDATE OR DELETE ON audit_record
FOR EACH ROW EXECUTE FUNCTION trg_governance_append_only();
DROP TRIGGER IF EXISTS trg_governance_append_only_truncate ON audit_record;
CREATE TRIGGER trg_governance_append_only_truncate BEFORE TRUNCATE ON audit_record
FOR EACH STATEMENT EXECUTE FUNCTION trg_governance_append_only();
DROP TRIGGER IF EXISTS trg_governance_append_only ON policy_check_log;
CREATE TRIGGER trg_governance_append_only BEFORE UPDATE OR DELETE ON policy_check_log
FOR EACH ROW EXECUTE FUNCTION trg_governance_append_only();
DROP TRIGGER IF EXISTS trg_governance_append_only_truncate ON policy_check_log;
CREATE TRIGGER trg_governance_append_only_truncate BEFORE TRUNCATE ON policy_check_log
FOR EACH STATEMENT EXECUTE FUNCTION trg_governance_append_only();

-- ---------------------------------------------------------------------------
-- Writers.  Each refuses input with a problem.  Rows inserted directly are
-- checked by the triggers and in batch.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION governance_refuse(p_what TEXT, p_problems JSONB) RETURNS VOID AS $$
BEGIN
  IF p_problems IS NOT NULL AND jsonb_array_length(p_problems) > 0 THEN
    RAISE EXCEPTION '%: % (%)', p_what, p_problems -> 0 ->> 'reason', p_problems -> 0 -> 'details';
  END IF;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION governance_problems_json(p_table TEXT, p_id UUID, p_batch BOOLEAN)
RETURNS JSONB AS $$
  SELECT coalesce(jsonb_agg(jsonb_build_object('reason', pr.reason, 'details', pr.details)), '[]')
    FROM governance_problems_of(p_table, p_id, p_batch) pr;
$$ LANGUAGE sql;

-- Register a policy under one of the seeded modalities (by name).  The
-- original 5-argument signature is replaced (a version argument is added).
DROP FUNCTION IF EXISTS register_policy(TEXT, TEXT, JSONB, TEXT, TEXT);
CREATE OR REPLACE FUNCTION register_policy(
  p_name TEXT, p_scope TEXT, p_body JSONB,
  p_modality TEXT, p_enforcement TEXT DEFAULT 'soft', p_version TEXT DEFAULT '1.0.0'
) RETURNS UUID AS $$
DECLARE
  new_id UUID;
  m_id UUID;
BEGIN
  SELECT id INTO m_id FROM modality WHERE name = p_modality;
  IF m_id IS NULL THEN
    RAISE EXCEPTION 'register_policy: unknown modality %', p_modality;
  END IF;
  PERFORM governance_refuse('register_policy', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM governance_policy_values_problems(p_name, p_version, p_body, TRUE, p_scope,
                                             p_enforcement)));
  INSERT INTO policy (name, scope, body, modality_id, enforcement_level, version)
  VALUES (p_name, p_scope, p_body, m_id, p_enforcement, p_version)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Attach a policy (with its modality) to an artifact and/or morphism.
CREATE OR REPLACE FUNCTION assign_policy(
  p_policy UUID, p_scope TEXT, p_artifact UUID DEFAULT NULL, p_morphism UUID DEFAULT NULL
) RETURNS UUID AS $$
DECLARE
  m_id UUID;
  new_id UUID;
BEGIN
  SELECT modality_id INTO m_id FROM policy WHERE id = p_policy;
  IF m_id IS NULL THEN
    RAISE EXCEPTION 'assign_policy: policy % not found or without modality', p_policy;
  END IF;
  INSERT INTO policy_modality_assignment (policy_id, modality_id, artifact_id, morphism_id, scope)
  VALUES (p_policy, m_id, p_artifact, p_morphism, p_scope)
  RETURNING id INTO new_id;
  PERFORM governance_refuse('assign_policy',
                            governance_problems_json('policy_modality_assignment', new_id, TRUE));
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION register_governance_context(p_name TEXT, p_description TEXT DEFAULT NULL)
RETURNS UUID AS $$
DECLARE
  new_id UUID;
BEGIN
  IF gov_blank(p_name) THEN
    RAISE EXCEPTION 'register_governance_context: context_typing ({"error": "name"})';
  END IF;
  INSERT INTO governance_context (name, description) VALUES (p_name, p_description)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Add from → to to a frame (contexts by name); existing pairs are kept.
CREATE OR REPLACE FUNCTION register_governance_access(p_frame TEXT, p_from TEXT, p_to TEXT)
RETURNS UUID AS $$
DECLARE
  f UUID := (SELECT id FROM governance_context WHERE name = p_from);
  t UUID := (SELECT id FROM governance_context WHERE name = p_to);
  new_id UUID;
BEGIN
  IF p_frame IS NULL OR p_frame NOT IN ('alethic', 'deontic') THEN
    RAISE EXCEPTION 'register_governance_access: unknown frame %', p_frame;
  END IF;
  IF f IS NULL OR t IS NULL THEN
    RAISE EXCEPTION 'register_governance_access: unknown context % or %', p_from, p_to;
  END IF;
  INSERT INTO governance_access (frame, from_context_id, to_context_id) VALUES (p_frame, f, t)
  ON CONFLICT (frame, from_context_id, to_context_id) DO NOTHING
  RETURNING id INTO new_id;
  IF new_id IS NULL THEN
    SELECT id INTO new_id FROM governance_access
     WHERE frame = p_frame AND from_context_id = f AND to_context_id = t;
  END IF;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Log a check of a policy at a context (by name) with its outcomes; the
-- result is computed.  The original signature (artifact, policy, result,
-- details) took the result on trust and is replaced.
DROP FUNCTION IF EXISTS log_policy_check(UUID, UUID, TEXT, JSONB);
CREATE OR REPLACE FUNCTION log_policy_check(
  p_artifact_id UUID, p_policy_id UUID, p_context TEXT, p_outcomes JSONB,
  p_details JSONB DEFAULT '{}'::jsonb, p_morphism_id UUID DEFAULT NULL
) RETURNS UUID AS $$
DECLARE
  ctx UUID := (SELECT id FROM governance_context WHERE name = p_context);
  k TEXT;
  lvl TEXT;
  acc TEXT[];
  computed TEXT;
  new_id UUID;
BEGIN
  SELECT m.kind, p.enforcement_level INTO k, lvl
    FROM policy p LEFT JOIN modality m ON m.id = p.modality_id WHERE p.id = p_policy_id;
  IF ctx IS NULL THEN
    RAISE EXCEPTION 'log_policy_check: unknown context %', p_context;
  END IF;
  acc := CASE WHEN k IS NULL THEN NULL ELSE governance_accessible(governance_kind_frame(k), ctx) END;
  IF k IS NOT NULL AND jsonb_typeof(p_outcomes) = 'object' THEN
    computed := governance_check_result(k, lvl, p_outcomes, acc);
  END IF;
  PERFORM governance_refuse('log_policy_check', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM governance_check_values_problems(
        EXISTS (SELECT 1 FROM policy p WHERE p.id = p_policy_id), k, lvl, TRUE, p_outcomes,
        coalesce(computed, 'pass'), acc)));
  INSERT INTO policy_check_log (artifact_id, morphism_id, policy_id, context_id, outcomes,
                                result, details)
  VALUES (p_artifact_id, p_morphism_id, p_policy_id, ctx, p_outcomes, computed,
          coalesce(p_details, '{}'::jsonb))
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION register_approval_workflow(
  p_name TEXT, p_steps JSONB, p_timeout_days INT DEFAULT 7
) RETURNS UUID AS $$
DECLARE
  new_id UUID;
BEGIN
  PERFORM governance_refuse('register_approval_workflow', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM governance_workflow_values_problems(p_name, p_steps, p_timeout_days)));
  INSERT INTO approval_workflow (name, steps, timeout_days)
  VALUES (p_name, p_steps, p_timeout_days)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Record a role's approval of an artifact (expiry defaults to the workflow's
-- timeout).  Refuses every problem, the order check included.
CREATE OR REPLACE FUNCTION record_approval(
  p_workflow UUID, p_artifact UUID, p_role TEXT,
  p_approved_at TIMESTAMPTZ DEFAULT now(), p_expires_at TIMESTAMPTZ DEFAULT NULL,
  p_signature BYTEA DEFAULT NULL
) RETURNS UUID AS $$
DECLARE
  timeout INT := (SELECT timeout_days FROM approval_workflow WHERE id = p_workflow);
  new_id UUID;
BEGIN
  IF timeout IS NULL AND NOT EXISTS (SELECT 1 FROM approval_workflow WHERE id = p_workflow) THEN
    RAISE EXCEPTION 'record_approval: workflow % not found', p_workflow;
  END IF;
  INSERT INTO approval_token (workflow_id, artifact_id, approver_role, approved_at, expires_at,
                              signature)
  VALUES (p_workflow, p_artifact, p_role, p_approved_at,
          coalesce(p_expires_at, p_approved_at + interval '24 hours' * timeout), p_signature)
  RETURNING id INTO new_id;
  PERFORM governance_refuse('record_approval', governance_problems_json('approval_token', new_id, TRUE));
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Append an audit record (numbered, linked and hashed by the trigger).
CREATE OR REPLACE FUNCTION record_audit(
  p_actor TEXT, p_action TEXT, p_artifact_id UUID,
  p_morphism_id UUID, p_details JSONB
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  PERFORM governance_refuse('record_audit', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM governance_audit_values_problems(p_actor, p_action, p_details)));
  INSERT INTO audit_record (actor, action, artifact_id, morphism_id, details)
  VALUES (p_actor, p_action, p_artifact_id, p_morphism_id, p_details)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;
