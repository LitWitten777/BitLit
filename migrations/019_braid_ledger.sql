-- ============================================================================
-- Categorical Ledger — Migration 019: Braid Ledger (Phase 2 sprint 1)
-- ============================================================================
-- Persists QBX-IR braids and their rewrite history, and enforces the rewrite
-- system R01–R03 at the database boundary (docs/architecture.md, "Interaction
-- with QBX-IR").
--
--   braid_word        a braid (strand_count, word) with its hash.  Words are
--                     short forms (+i = σ_i, -i = σ_i⁻¹, 1-indexed); the hash
--                     is qbx_ir.algebra.rewriting.braid_hash: SHA3-256 of the
--                     canonical JSON {"n":<strand_count>,"word":[...]}.  Rows
--                     are content addressed: (strand_count, word) is unique.
--   braid_rewrite     the provenance record of one rewrite
--                     (qbx_ir.algebra.rewriting.Transformation): input braid,
--                     rule, 0-based position, output braid, both hashes and
--                     the rule's declaration (preserved / changed properties).
--                     Append-only.
--   braid_derivation  a chain of rewrite records, each used forwards
--                     (input → output) or backwards (output → input), from a
--                     source to a target braid: a certificate that the two
--                     braids are equal in B_n.  Append-only.
--
-- Reference implementation: qbx_ir.ledger (same problems, same order, same
-- details).  Lean: QBX/Formal/BraidLedger.lean — a rewrite record passes the
-- check iff it is one QBX rewrite step; an accepted derivation exists between
-- two words iff they are equal in B_n (registry H-048, H-049).
--
-- Problems are logged to invariant_violation (migration 017) with module
-- 'braid_ledger', object_id the row and details.table its table, so they
-- appear in v_all_violations without changing the frozen migration 017.
-- run_phase2_batch_checks() runs run_all_batch_checks() and check_braid_ledger().
--
-- Write-time tier: every insert is checked (logged; raised in strict mode).
-- Writers (register_braid, record_braid_rewrite, record_braid_derivation)
-- refuse input with a problem.
-- ============================================================================

CREATE TABLE IF NOT EXISTS braid_word (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  strand_count INT NOT NULL,
  word INT[] NOT NULL DEFAULT '{}' CHECK (array_ndims(word) IS NULL OR array_ndims(word) = 1),
  braid_hash TEXT NOT NULL,
  name TEXT,
  created_at TIMESTAMPTZ DEFAULT now(),
  UNIQUE (strand_count, word)
);

CREATE INDEX IF NOT EXISTS idx_braid_word_hash ON braid_word (braid_hash);

CREATE TABLE IF NOT EXISTS braid_rewrite (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  seq BIGSERIAL,
  input_braid_id UUID NOT NULL REFERENCES braid_word(id) ON DELETE CASCADE,
  rule_id TEXT NOT NULL,
  position INT,
  output_braid_id UUID NOT NULL REFERENCES braid_word(id) ON DELETE CASCADE,
  input_hash TEXT NOT NULL,
  output_hash TEXT NOT NULL,
  preserved TEXT[] NOT NULL DEFAULT '{}',
  changed TEXT[] NOT NULL DEFAULT '{}',
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_braid_rewrite_input ON braid_rewrite (input_braid_id);
CREATE INDEX IF NOT EXISTS idx_braid_rewrite_output ON braid_rewrite (output_braid_id);

CREATE TABLE IF NOT EXISTS braid_derivation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  seq BIGSERIAL,
  name TEXT,
  source_braid_id UUID NOT NULL REFERENCES braid_word(id) ON DELETE CASCADE,
  target_braid_id UUID NOT NULL REFERENCES braid_word(id) ON DELETE CASCADE,
  steps UUID[] NOT NULL DEFAULT '{}',
  directions BOOLEAN[] NOT NULL DEFAULT '{}',
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_braid_derivation_source ON braid_derivation (source_braid_id);
CREATE INDEX IF NOT EXISTS idx_braid_derivation_target ON braid_derivation (target_braid_id);

-- ---------------------------------------------------------------------------
-- Words, hashes and the rules
-- ---------------------------------------------------------------------------

-- qbx_ir.algebra.rewriting.braid_hash.
CREATE OR REPLACE FUNCTION braid_word_hash(p_n INT, p_word INT[]) RETURNS TEXT AS $$
  SELECT encode(addr_sha3(convert_to(
           '{"n":' || p_n || ',"word":[' || array_to_string(p_word, ',') || ']}', 'UTF8'), 256), 'hex')
$$ LANGUAGE sql IMMUTABLE STRICT;

-- The declaration of a rule (RewriteRule.preserved / .changed); NULL if unknown.
CREATE OR REPLACE FUNCTION braid_rule_preserved(p_rule TEXT) RETURNS TEXT[] AS $$
  SELECT CASE WHEN p_rule IN ('R01', 'R02', 'R03')
              THEN ARRAY['braid_group_element', 'strand_count', 'permutation', 'writhe'] END
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION braid_rule_changed(p_rule TEXT) RETURNS TEXT[] AS $$
  SELECT CASE p_rule
           WHEN 'R01' THEN ARRAY['word_length']
           WHEN 'R02' THEN ARRAY['word_order']
           WHEN 'R03' THEN ARRAY['word_order', 'crossing_positions']
         END
$$ LANGUAGE sql IMMUTABLE;

-- qbx_ir.ledger.apply_short: the word after applying the rule at the 0-based
-- position, or NULL when the rule does not apply there.
CREATE OR REPLACE FUNCTION braid_apply_rule(p_word INT[], p_rule TEXT, p_pos INT) RETURNS INT[] AS $$
DECLARE
  len INT := coalesce(cardinality(p_word), 0);
  a INT; b INT; c INT;
BEGIN
  IF p_rule IS NULL OR p_rule NOT IN ('R01', 'R02', 'R03') OR p_pos IS NULL OR p_pos < 0 THEN
    RETURN NULL;
  END IF;
  IF p_rule IN ('R01', 'R02') THEN
    IF p_pos + 1 >= len THEN RETURN NULL; END IF;
    a := p_word[p_pos + 1]; b := p_word[p_pos + 2];
    IF p_rule = 'R01' THEN
      IF abs(a) = abs(b) AND sign(a) = -sign(b) THEN
        RETURN p_word[1:p_pos] || p_word[p_pos + 3:len];
      END IF;
      RETURN NULL;
    END IF;
    IF abs(abs(a) - abs(b)) >= 2 THEN
      RETURN p_word[1:p_pos] || ARRAY[b, a] || p_word[p_pos + 3:len];
    END IF;
    RETURN NULL;
  END IF;
  IF p_pos + 2 >= len THEN RETURN NULL; END IF;
  a := p_word[p_pos + 1]; b := p_word[p_pos + 2]; c := p_word[p_pos + 3];
  IF NOT (sign(a) = sign(b) AND sign(b) = sign(c) AND abs(a) = abs(c)) THEN RETURN NULL; END IF;
  IF abs(abs(a) - abs(b)) <> 1 THEN RETURN NULL; END IF;
  RETURN p_word[1:p_pos] || ARRAY[b, a, b] || p_word[p_pos + 4:len];
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Problems (qbx_ir.ledger)
-- ---------------------------------------------------------------------------

-- qbx_ir.ledger.braid_problems on values.
CREATE OR REPLACE FUNCTION braid_values_problems(p_n INT, p_word INT[], p_hash TEXT)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  k INT;
  g INT;
  bad BOOLEAN := FALSE;
  expected TEXT;
BEGIN
  IF p_n IS NULL OR p_n < 1 THEN
    reason := 'strand_count'; details := jsonb_build_object('strand_count', p_n);
    RETURN NEXT; RETURN;
  END IF;
  FOR k IN 1..coalesce(cardinality(p_word), 0) LOOP
    g := p_word[k];
    IF g IS NULL OR g = 0 OR abs(g) >= p_n THEN
      bad := TRUE;
      reason := 'letter'; details := jsonb_build_object('position', k - 1, 'letter', g);
      RETURN NEXT;
    END IF;
  END LOOP;
  IF NOT bad THEN
    expected := braid_word_hash(p_n, p_word);
    IF p_hash IS DISTINCT FROM expected THEN
      reason := 'hash'; details := jsonb_build_object('recorded', p_hash, 'expected', expected);
      RETURN NEXT;
    END IF;
  END IF;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM braid_word b, LATERAL braid_values_problems(b.strand_count, b.word, b.braid_hash) pr
   WHERE b.id = p_id
$$ LANGUAGE sql;

CREATE OR REPLACE FUNCTION braid_is_well_formed(p_id UUID) RETURNS BOOLEAN AS $$
  SELECT EXISTS (SELECT 1 FROM braid_word WHERE id = p_id)
         AND NOT EXISTS (SELECT 1 FROM braid_problems(p_id))
$$ LANGUAGE sql;

-- qbx_ir.ledger.rewrite_problems.
CREATE OR REPLACE FUNCTION braid_rewrite_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
  bi RECORD;
  bo RECORD;
  in_ok BOOLEAN;
  out_ok BOOLEAN;
  expected INT[];
BEGIN
  SELECT * INTO r FROM braid_rewrite WHERE id = p_id;
  IF NOT FOUND THEN RETURN; END IF;
  SELECT * INTO bi FROM braid_word WHERE id = r.input_braid_id;
  SELECT * INTO bo FROM braid_word WHERE id = r.output_braid_id;
  in_ok := braid_is_well_formed(r.input_braid_id);
  out_ok := braid_is_well_formed(r.output_braid_id);
  IF NOT in_ok THEN
    reason := 'input_not_well_formed'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
  IF NOT out_ok THEN
    reason := 'output_not_well_formed'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
  IF bi.strand_count IS DISTINCT FROM bo.strand_count THEN
    reason := 'strand_count_mismatch';
    details := jsonb_build_object('input', bi.strand_count, 'output', bo.strand_count);
    RETURN NEXT;
  END IF;
  IF r.rule_id NOT IN ('R01', 'R02', 'R03') THEN
    reason := 'rule_unknown'; details := jsonb_build_object('rule', r.rule_id); RETURN NEXT;
  ELSE
    IF in_ok THEN
      expected := braid_apply_rule(bi.word, r.rule_id, r.position);
      IF expected IS NULL THEN
        reason := 'not_applicable';
        details := jsonb_build_object('rule', r.rule_id, 'position', r.position);
        RETURN NEXT;
      ELSIF bo.word IS DISTINCT FROM expected THEN
        reason := 'output_mismatch';
        details := jsonb_build_object('expected', to_jsonb(expected), 'recorded', to_jsonb(bo.word));
        RETURN NEXT;
      END IF;
    END IF;
    IF r.preserved IS DISTINCT FROM braid_rule_preserved(r.rule_id)
       OR r.changed IS DISTINCT FROM braid_rule_changed(r.rule_id) THEN
      reason := 'declaration_mismatch';
      details := jsonb_build_object('preserved', to_jsonb(r.preserved), 'changed', to_jsonb(r.changed),
                                    'expected_preserved', to_jsonb(braid_rule_preserved(r.rule_id)),
                                    'expected_changed', to_jsonb(braid_rule_changed(r.rule_id)));
      RETURN NEXT;
    END IF;
  END IF;
  IF in_ok AND r.input_hash IS DISTINCT FROM bi.braid_hash THEN
    reason := 'input_hash_mismatch';
    details := jsonb_build_object('recorded', r.input_hash, 'expected', bi.braid_hash);
    RETURN NEXT;
  END IF;
  IF out_ok AND r.output_hash IS DISTINCT FROM bo.braid_hash THEN
    reason := 'output_hash_mismatch';
    details := jsonb_build_object('recorded', r.output_hash, 'expected', bo.braid_hash);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_rewrite_is_valid(p_id UUID) RETURNS BOOLEAN AS $$
  SELECT EXISTS (SELECT 1 FROM braid_rewrite WHERE id = p_id)
         AND NOT EXISTS (SELECT 1 FROM braid_rewrite_problems(p_id))
$$ LANGUAGE sql;

-- qbx_ir.ledger.derivation_problems on values (p_target NULL: only follow
-- the chain; the end is returned by braid_chain_end).
CREATE OR REPLACE FUNCTION braid_chain_problems(
  p_source UUID, p_target UUID, p_steps UUID[], p_directions BOOLEAN[]
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  ns INT := coalesce(cardinality(p_steps), 0);
  nd INT := coalesce(cardinality(p_directions), 0);
  k INT;
  st RECORD;
  cur UUID := p_source;
  s_start UUID;
BEGIN
  IF ns <> nd OR array_position(p_directions, NULL) IS NOT NULL THEN
    reason := 'steps_shape'; details := jsonb_build_object('steps', ns, 'directions', nd);
    RETURN NEXT; RETURN;
  END IF;
  FOR k IN 1..ns LOOP
    SELECT * INTO st FROM braid_rewrite WHERE id = p_steps[k];
    IF NOT FOUND THEN
      reason := 'step_unknown'; details := jsonb_build_object('step', k - 1); RETURN NEXT; RETURN;
    END IF;
    IF NOT braid_rewrite_is_valid(st.id) THEN
      reason := 'step_invalid'; details := jsonb_build_object('step', k - 1); RETURN NEXT;
    END IF;
    s_start := CASE WHEN p_directions[k] THEN st.input_braid_id ELSE st.output_braid_id END;
    IF s_start IS DISTINCT FROM cur THEN
      reason := 'step_disconnected'; details := jsonb_build_object('step', k - 1); RETURN NEXT; RETURN;
    END IF;
    cur := CASE WHEN p_directions[k] THEN st.output_braid_id ELSE st.input_braid_id END;
  END LOOP;
  IF p_target IS NOT NULL AND cur IS DISTINCT FROM p_target THEN
    reason := 'target_mismatch'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- The braid a chain ends at, ignoring validity (NULL if a step is unknown or
-- the chain is malformed or disconnected).
CREATE OR REPLACE FUNCTION braid_chain_end(p_source UUID, p_steps UUID[], p_directions BOOLEAN[])
RETURNS UUID AS $$
DECLARE
  k INT;
  st RECORD;
  cur UUID := p_source;
BEGIN
  IF coalesce(cardinality(p_steps), 0) <> coalesce(cardinality(p_directions), 0)
     OR array_position(p_directions, NULL) IS NOT NULL THEN
    RETURN NULL;
  END IF;
  FOR k IN 1..coalesce(cardinality(p_steps), 0) LOOP
    SELECT * INTO st FROM braid_rewrite WHERE id = p_steps[k];
    IF NOT FOUND THEN RETURN NULL; END IF;
    IF (CASE WHEN p_directions[k] THEN st.input_braid_id ELSE st.output_braid_id END)
       IS DISTINCT FROM cur THEN
      RETURN NULL;
    END IF;
    cur := CASE WHEN p_directions[k] THEN st.output_braid_id ELSE st.input_braid_id END;
  END LOOP;
  RETURN cur;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_derivation_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM braid_derivation d,
         LATERAL braid_chain_problems(d.source_braid_id, d.target_braid_id, d.steps, d.directions) pr
   WHERE d.id = p_id
$$ LANGUAGE sql;

-- True iff a recorded derivation between the two braids (either way round)
-- currently has no problem: a certificate that they are equal in B_n
-- (Lean: chainEnd_eval_eq).  Equal braids always admit one (Lean:
-- eval_eq_iff_exists_chain), but only recorded derivations are consulted.
CREATE OR REPLACE FUNCTION braid_equality_certified(p_a UUID, p_b UUID) RETURNS BOOLEAN AS $$
  SELECT p_a = p_b OR EXISTS (
    SELECT 1 FROM braid_derivation d
     WHERE ((d.source_braid_id = p_a AND d.target_braid_id = p_b)
            OR (d.source_braid_id = p_b AND d.target_braid_id = p_a))
       AND NOT EXISTS (SELECT 1 FROM braid_derivation_problems(d.id)))
$$ LANGUAGE sql;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION braid_ledger_problems_of(p_table TEXT, p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  CASE p_table
    WHEN 'braid_word' THEN RETURN QUERY SELECT * FROM braid_problems(p_id);
    WHEN 'braid_rewrite' THEN RETURN QUERY SELECT * FROM braid_rewrite_problems(p_id);
    WHEN 'braid_derivation' THEN RETURN QUERY SELECT * FROM braid_derivation_problems(p_id);
  END CASE;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_ledger_record(p_table TEXT, p_id UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  PERFORM qbx_record_violation('braid_ledger', p_reason,
                               coalesce(p_details, '{}'::jsonb) || jsonb_build_object('table', p_table),
                               p_id);
END;
$$ LANGUAGE plpgsql;

-- Check one row: log every problem; returns their number.
CREATE OR REPLACE FUNCTION braid_ledger_check_row(p_table TEXT, p_id UUID) RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM braid_ledger_problems_of(p_table, p_id) LOOP
    PERFORM braid_ledger_record(p_table, p_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_ledger_check_raise(p_n INT, p_what TEXT) RETURNS VOID AS $$
BEGIN
  IF p_n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION '% (% problem(s))', p_what, p_n;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- Every row of the three tables.  Returns the number of problems found.
CREATE OR REPLACE FUNCTION check_braid_ledger() RETURNS INT AS $$
DECLARE
  t RECORD;
  n INT := 0;
BEGIN
  FOR t IN SELECT 'braid_word' AS tb, id, created_at AS o1, 0::bigint AS o2 FROM braid_word
           UNION ALL SELECT 'braid_rewrite', id, created_at, seq FROM braid_rewrite
           UNION ALL SELECT 'braid_derivation', id, created_at, seq FROM braid_derivation
           ORDER BY 1, 3, 4 LOOP
    n := n + braid_ledger_check_row(t.tb, t.id);
  END LOOP;
  PERFORM braid_ledger_check_raise(n, 'Braid ledger has problems');
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- Phase 1 batch checks (frozen migration 017) followed by the Phase 2 ones.
CREATE OR REPLACE FUNCTION run_phase2_batch_checks() RETURNS VOID AS $$
BEGIN
  PERFORM run_all_batch_checks();
  PERFORM check_braid_ledger();
  RAISE NOTICE 'run_phase2_batch_checks: complete';
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_braid_ledger_row() RETURNS trigger AS $$
DECLARE
  n INT;
BEGIN
  n := braid_ledger_check_row(TG_TABLE_NAME, NEW.id);
  PERFORM braid_ledger_check_raise(n, format('%s row %s is not well formed', TG_TABLE_NAME, NEW.id));
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_braid_ledger_row ON braid_word;
CREATE TRIGGER trg_check_braid_ledger_row AFTER INSERT ON braid_word
FOR EACH ROW EXECUTE FUNCTION trg_check_braid_ledger_row();
DROP TRIGGER IF EXISTS trg_check_braid_ledger_row ON braid_rewrite;
CREATE TRIGGER trg_check_braid_ledger_row AFTER INSERT ON braid_rewrite
FOR EACH ROW EXECUTE FUNCTION trg_check_braid_ledger_row();
DROP TRIGGER IF EXISTS trg_check_braid_ledger_row ON braid_derivation;
CREATE TRIGGER trg_check_braid_ledger_row AFTER INSERT ON braid_derivation
FOR EACH ROW EXECUTE FUNCTION trg_check_braid_ledger_row();

-- The ledger is append-only: braids are content addressed and rewrites and
-- derivations are provenance.  An UPDATE, DELETE or TRUNCATE is logged (and
-- refused in strict mode).
CREATE OR REPLACE FUNCTION trg_braid_ledger_append_only() RETURNS trigger AS $$
BEGIN
  PERFORM braid_ledger_record(TG_TABLE_NAME, CASE WHEN TG_LEVEL = 'ROW' THEN OLD.id END,
                              'log_mutation', jsonb_build_object('op', TG_OP));
  IF functor_is_strict() THEN
    RAISE EXCEPTION '% on % refused: the braid ledger is append-only', TG_OP, TG_TABLE_NAME;
  END IF;
  IF TG_OP = 'DELETE' THEN RETURN OLD; END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_braid_ledger_append_only ON braid_word;
CREATE TRIGGER trg_braid_ledger_append_only BEFORE UPDATE OR DELETE ON braid_word
FOR EACH ROW EXECUTE FUNCTION trg_braid_ledger_append_only();
DROP TRIGGER IF EXISTS trg_braid_ledger_append_only ON braid_rewrite;
CREATE TRIGGER trg_braid_ledger_append_only BEFORE UPDATE OR DELETE ON braid_rewrite
FOR EACH ROW EXECUTE FUNCTION trg_braid_ledger_append_only();
DROP TRIGGER IF EXISTS trg_braid_ledger_append_only ON braid_derivation;
CREATE TRIGGER trg_braid_ledger_append_only BEFORE UPDATE OR DELETE ON braid_derivation
FOR EACH ROW EXECUTE FUNCTION trg_braid_ledger_append_only();
DROP TRIGGER IF EXISTS trg_braid_ledger_append_only_truncate ON braid_word;
CREATE TRIGGER trg_braid_ledger_append_only_truncate BEFORE TRUNCATE ON braid_word
FOR EACH STATEMENT EXECUTE FUNCTION trg_braid_ledger_append_only();
DROP TRIGGER IF EXISTS trg_braid_ledger_append_only_truncate ON braid_rewrite;
CREATE TRIGGER trg_braid_ledger_append_only_truncate BEFORE TRUNCATE ON braid_rewrite
FOR EACH STATEMENT EXECUTE FUNCTION trg_braid_ledger_append_only();
DROP TRIGGER IF EXISTS trg_braid_ledger_append_only_truncate ON braid_derivation;
CREATE TRIGGER trg_braid_ledger_append_only_truncate BEFORE TRUNCATE ON braid_derivation
FOR EACH STATEMENT EXECUTE FUNCTION trg_braid_ledger_append_only();

-- ---------------------------------------------------------------------------
-- Writers.  Each refuses input with a problem.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION braid_ledger_refuse(p_what TEXT, p_problems JSONB) RETURNS VOID AS $$
BEGIN
  IF p_problems IS NOT NULL AND jsonb_array_length(p_problems) > 0 THEN
    RAISE EXCEPTION '%: % (%)', p_what, p_problems -> 0 ->> 'reason', p_problems -> 0 -> 'details';
  END IF;
END;
$$ LANGUAGE plpgsql;

-- Register a braid (returns the existing row for the same strand count and word).
CREATE OR REPLACE FUNCTION register_braid(p_n INT, p_word INT[], p_name TEXT DEFAULT NULL)
RETURNS UUID AS $$
DECLARE
  h TEXT;
  b_id UUID;
BEGIN
  IF p_word IS NULL OR (array_ndims(p_word) IS NOT NULL AND array_ndims(p_word) <> 1) THEN
    RAISE EXCEPTION 'register_braid: the word must be a one-dimensional array';
  END IF;
  IF p_n IS NOT NULL AND p_n >= 1 AND array_position(p_word, NULL) IS NULL THEN
    h := braid_word_hash(p_n, p_word);
  END IF;
  PERFORM braid_ledger_refuse('register_braid',
    (SELECT coalesce(jsonb_agg(jsonb_build_object('reason', pr.reason, 'details', pr.details)), '[]')
       FROM braid_values_problems(p_n, p_word, h) pr));
  SELECT id INTO b_id FROM braid_word WHERE strand_count = p_n AND word = p_word;
  IF b_id IS NULL THEN
    INSERT INTO braid_word (strand_count, word, braid_hash, name)
    VALUES (p_n, p_word, h, p_name) RETURNING id INTO b_id;
  END IF;
  RETURN b_id;
END;
$$ LANGUAGE plpgsql;

-- Apply a rule to a registered braid and record the rewrite; returns its id.
-- The output braid is registered as needed.
CREATE OR REPLACE FUNCTION record_braid_rewrite(p_input UUID, p_rule TEXT, p_position INT)
RETURNS UUID AS $$
DECLARE
  bi RECORD;
  out_word INT[];
  out_id UUID;
  new_id UUID;
BEGIN
  SELECT * INTO bi FROM braid_word WHERE id = p_input;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'record_braid_rewrite: unknown braid %', p_input;
  END IF;
  IF NOT braid_is_well_formed(p_input) THEN
    RAISE EXCEPTION 'record_braid_rewrite: braid % is not well formed', p_input;
  END IF;
  IF p_rule IS NULL OR p_rule NOT IN ('R01', 'R02', 'R03') THEN
    RAISE EXCEPTION 'record_braid_rewrite: rule_unknown (%)', p_rule;
  END IF;
  out_word := braid_apply_rule(bi.word, p_rule, p_position);
  IF out_word IS NULL THEN
    RAISE EXCEPTION 'record_braid_rewrite: not_applicable (rule %, position %)', p_rule, p_position;
  END IF;
  out_id := register_braid(bi.strand_count, out_word);
  INSERT INTO braid_rewrite (input_braid_id, rule_id, position, output_braid_id,
                             input_hash, output_hash, preserved, changed)
  VALUES (p_input, p_rule, p_position, out_id, bi.braid_hash,
          (SELECT braid_hash FROM braid_word WHERE id = out_id),
          braid_rule_preserved(p_rule), braid_rule_changed(p_rule))
  RETURNING id INTO new_id;
  PERFORM braid_ledger_refuse('record_braid_rewrite',
    (SELECT coalesce(jsonb_agg(jsonb_build_object('reason', pr.reason, 'details', pr.details)), '[]')
       FROM braid_rewrite_problems(new_id) pr));
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Record a derivation from p_source along the given rewrite records
-- (p_directions[k] TRUE: forwards, FALSE: backwards); the target is where the
-- chain ends.  Refused unless every step is valid and the steps connect.
CREATE OR REPLACE FUNCTION record_braid_derivation(
  p_source UUID, p_steps UUID[], p_directions BOOLEAN[], p_name TEXT DEFAULT NULL
) RETURNS UUID AS $$
DECLARE
  tgt UUID;
  new_id UUID;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM braid_word WHERE id = p_source) THEN
    RAISE EXCEPTION 'record_braid_derivation: unknown braid %', p_source;
  END IF;
  PERFORM braid_ledger_refuse('record_braid_derivation',
    (SELECT coalesce(jsonb_agg(jsonb_build_object('reason', pr.reason, 'details', pr.details)), '[]')
       FROM braid_chain_problems(p_source, NULL, p_steps, p_directions) pr));
  tgt := braid_chain_end(p_source, p_steps, p_directions);
  INSERT INTO braid_derivation (name, source_braid_id, target_braid_id, steps, directions)
  VALUES (p_name, p_source, tgt, coalesce(p_steps, '{}'), coalesce(p_directions, '{}'))
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;
