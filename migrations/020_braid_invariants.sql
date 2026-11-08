-- ============================================================================
-- Categorical Ledger — Migration 020: Braid Invariant Certificates
-- (Phase 2 sprint 2)
-- ============================================================================
-- Stores, for a braid of the braid ledger (migration 019), an invariant
-- certificate recomputed by the database from the word:
--
--   braid_invariant   one certificate per braid:
--                       permutation  qbx_ir.algebra.invariants.permutation
--                                    (permutation[p] = the strand that ends at
--                                    position p, 1-indexed);
--                       writhe       the exponent sum;
--                       components   components[s] = 0-based index of the
--                                    closure component of strand s (components
--                                    are the cycles of the permutation,
--                                    numbered by smallest strand, as in
--                                    closure_components);
--                       linking      lk(C_a, C_b) for a < b in lexicographic
--                                    order (linking_matrix);
--                       braid_hash   the hash of the certified braid.
--                     Append-only.
--
-- Uses of the certificates:
--   * transport: along every accepted rewrite and derivation whose two ends
--     have valid certificates, the certificates must agree (batch tier);
--   * braid_invariant_differences / braid_inequality_certified: two braids
--     with the same strand count whose valid certificates differ are
--     different elements of B_n.
--
-- Reference implementation: qbx_ir.invariant_ledger (same problems, same
-- order, same details).  Lean: QBX/Formal/BraidInvariantCert.lean — every
-- field is computed by a crossing loop that depends only on the braid group
-- element (cert_eq_of_eval_eq, linkTotal_eq_of_eval_eq), so a valid
-- certificate never changes along an accepted rewrite or derivation, and
-- different certificates prove different braids (eval_ne_of_cert_ne); the
-- stored linking numbers are exact halves (linkTotal_even); registry H-052,
-- H-053.
--
-- Problems are logged to invariant_violation (migration 017) with module
-- 'braid_invariants', object_id the row and details.table its table.
-- run_phase2_batch_checks() (redefined here) runs run_all_batch_checks(),
-- check_braid_ledger() and check_braid_invariants().
--
-- Write-time tier: every inserted certificate is checked (logged; raised in
-- strict mode).  The writer certify_braid_invariants refuses a braid that is
-- not well formed.
-- ============================================================================

CREATE TABLE IF NOT EXISTS braid_invariant (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  seq BIGSERIAL,
  braid_id UUID NOT NULL UNIQUE REFERENCES braid_word(id) ON DELETE CASCADE,
  braid_hash TEXT NOT NULL,
  permutation INT[] NOT NULL DEFAULT '{}',
  writhe INT NOT NULL,
  components INT[] NOT NULL DEFAULT '{}',
  linking INT[] NOT NULL DEFAULT '{}',
  created_at TIMESTAMPTZ DEFAULT now()
);

-- ---------------------------------------------------------------------------
-- Recomputation (qbx_ir.invariant_ledger.invariant_values)
-- ---------------------------------------------------------------------------

-- The certificate fields of a well-formed braid (strand count >= 1, every
-- letter in ±1..±(n-1)); one row.  The crossing loop follows Braid.crossings:
-- pos[p] is the strand at position p; letter ±i crosses pos[i] and pos[i+1].
CREATE OR REPLACE FUNCTION braid_invariant_values(p_n INT, p_word INT[])
RETURNS TABLE(permutation INT[], writhe INT, components INT[], linking INT[]) AS $$
DECLARE
  len INT := coalesce(cardinality(p_word), 0);
  pos INT[];
  dest INT[];
  label INT[];
  totals INT[];
  k INT;
  g INT;
  i INT;
  t INT;
  s INT;
  cur INT;
  cnt INT := 0;
  a INT;
  b INT;
  w INT := 0;
BEGIN
  pos := ARRAY(SELECT generate_series(1, p_n));
  FOR k IN 1..len LOOP
    g := p_word[k];
    i := abs(g);
    w := w + sign(g)::int;
    t := pos[i]; pos[i] := pos[i + 1]; pos[i + 1] := t;
  END LOOP;
  permutation := pos;
  writhe := w;
  -- dest[s] = the final position of strand s.
  dest := array_fill(0, ARRAY[p_n]);
  FOR k IN 1..p_n LOOP
    dest[pos[k]] := k;
  END LOOP;
  -- Cycles of the permutation, numbered by smallest strand.
  label := array_fill(NULL::int, ARRAY[p_n]);
  FOR s IN 1..p_n LOOP
    IF label[s] IS NULL THEN
      cur := s;
      WHILE label[cur] IS NULL LOOP
        label[cur] := cnt;
        cur := dest[cur];
      END LOOP;
      cnt := cnt + 1;
    END IF;
  END LOOP;
  components := label;
  -- Signed crossings between different components, per pair a < b.
  totals := CASE WHEN cnt > 1 THEN array_fill(0, ARRAY[cnt * (cnt - 1) / 2]) ELSE '{}'::int[] END;
  pos := ARRAY(SELECT generate_series(1, p_n));
  FOR k IN 1..len LOOP
    g := p_word[k];
    i := abs(g);
    a := least(label[pos[i]], label[pos[i + 1]]);
    b := greatest(label[pos[i]], label[pos[i + 1]]);
    IF a <> b THEN
      t := a * cnt - a * (a + 1) / 2 + (b - a - 1) + 1;
      totals[t] := totals[t] + sign(g)::int;
    END IF;
    t := pos[i]; pos[i] := pos[i + 1]; pos[i + 1] := t;
  END LOOP;
  linking := ARRAY(SELECT floor(x::numeric / 2)::int FROM unnest(totals) WITH ORDINALITY AS u(x, o)
                   ORDER BY o);
  RETURN NEXT;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Problems (qbx_ir.invariant_ledger)
-- ---------------------------------------------------------------------------

-- qbx_ir.invariant_ledger.certificate_problems.
CREATE OR REPLACE FUNCTION braid_invariant_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  b RECORD;
  v RECORD;
BEGIN
  SELECT * INTO c FROM braid_invariant WHERE id = p_id;
  IF NOT FOUND THEN RETURN; END IF;
  IF NOT braid_is_well_formed(c.braid_id) THEN
    reason := 'braid_not_well_formed'; details := '{}'::jsonb; RETURN NEXT; RETURN;
  END IF;
  SELECT * INTO b FROM braid_word WHERE id = c.braid_id;
  IF c.braid_hash IS DISTINCT FROM b.braid_hash THEN
    reason := 'braid_hash_mismatch';
    details := jsonb_build_object('recorded', c.braid_hash, 'expected', b.braid_hash);
    RETURN NEXT;
  END IF;
  SELECT * INTO v FROM braid_invariant_values(b.strand_count, b.word);
  IF c.permutation IS DISTINCT FROM v.permutation THEN
    reason := 'permutation_mismatch';
    details := jsonb_build_object('recorded', to_jsonb(c.permutation), 'expected', to_jsonb(v.permutation));
    RETURN NEXT;
  END IF;
  IF c.writhe IS DISTINCT FROM v.writhe THEN
    reason := 'writhe_mismatch';
    details := jsonb_build_object('recorded', c.writhe, 'expected', v.writhe);
    RETURN NEXT;
  END IF;
  IF c.components IS DISTINCT FROM v.components THEN
    reason := 'components_mismatch';
    details := jsonb_build_object('recorded', to_jsonb(c.components), 'expected', to_jsonb(v.components));
    RETURN NEXT;
  END IF;
  IF c.linking IS DISTINCT FROM v.linking THEN
    reason := 'linking_mismatch';
    details := jsonb_build_object('recorded', to_jsonb(c.linking), 'expected', to_jsonb(v.linking));
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- The certificate of a braid, if it has one without problems.
CREATE OR REPLACE FUNCTION braid_valid_certificate(p_braid UUID) RETURNS UUID AS $$
  SELECT c.id FROM braid_invariant c
   WHERE c.braid_id = p_braid
     AND NOT EXISTS (SELECT 1 FROM braid_invariant_problems(c.id))
$$ LANGUAGE sql;

-- qbx_ir.invariant_ledger.differences: the invariants on which the valid
-- certificates of two braids with the same strand count differ (NULL when a
-- valid certificate is missing or the strand counts differ).
CREATE OR REPLACE FUNCTION braid_invariant_differences(p_a UUID, p_b UUID) RETURNS TEXT[] AS $$
DECLARE
  ca RECORD;
  cb RECORD;
  diffs TEXT[] := '{}';
BEGIN
  SELECT * INTO ca FROM braid_invariant WHERE id = braid_valid_certificate(p_a);
  IF NOT FOUND THEN RETURN NULL; END IF;
  SELECT * INTO cb FROM braid_invariant WHERE id = braid_valid_certificate(p_b);
  IF NOT FOUND THEN RETURN NULL; END IF;
  IF (SELECT strand_count FROM braid_word WHERE id = p_a)
     IS DISTINCT FROM (SELECT strand_count FROM braid_word WHERE id = p_b) THEN
    RETURN NULL;
  END IF;
  IF ca.permutation IS DISTINCT FROM cb.permutation THEN diffs := diffs || 'permutation'::text; END IF;
  IF ca.writhe IS DISTINCT FROM cb.writhe THEN diffs := diffs || 'writhe'::text; END IF;
  IF ca.components IS DISTINCT FROM cb.components THEN diffs := diffs || 'components'::text; END IF;
  IF ca.linking IS DISTINCT FROM cb.linking THEN diffs := diffs || 'linking'::text; END IF;
  RETURN diffs;
END;
$$ LANGUAGE plpgsql;

-- True iff the two braids have valid certificates that differ: a certificate
-- that they are different elements of B_n (Lean: eval_ne_of_cert_ne).
-- FALSE means "not certified", not "equal".
CREATE OR REPLACE FUNCTION braid_inequality_certified(p_a UUID, p_b UUID) RETURNS BOOLEAN AS $$
  SELECT coalesce(cardinality(braid_invariant_differences(p_a, p_b)) > 0, FALSE)
$$ LANGUAGE sql;

-- qbx_ir.invariant_ledger.transport_problems for a rewrite record.
CREATE OR REPLACE FUNCTION braid_rewrite_transport_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
  inv TEXT;
BEGIN
  SELECT * INTO r FROM braid_rewrite WHERE id = p_id;
  IF NOT FOUND OR NOT braid_rewrite_is_valid(p_id) THEN RETURN; END IF;
  FOREACH inv IN ARRAY coalesce(braid_invariant_differences(r.input_braid_id, r.output_braid_id), '{}')
  LOOP
    reason := 'invariant_not_preserved'; details := jsonb_build_object('invariant', inv);
    RETURN NEXT;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- qbx_ir.invariant_ledger.transport_problems for a derivation.
CREATE OR REPLACE FUNCTION braid_derivation_transport_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  d RECORD;
  inv TEXT;
BEGIN
  SELECT * INTO d FROM braid_derivation WHERE id = p_id;
  IF NOT FOUND OR EXISTS (SELECT 1 FROM braid_derivation_problems(p_id)) THEN RETURN; END IF;
  FOREACH inv IN ARRAY coalesce(braid_invariant_differences(d.source_braid_id, d.target_braid_id), '{}')
  LOOP
    reason := 'invariant_not_preserved'; details := jsonb_build_object('invariant', inv);
    RETURN NEXT;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION braid_invariants_problems_of(p_table TEXT, p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  CASE p_table
    WHEN 'braid_invariant' THEN RETURN QUERY SELECT * FROM braid_invariant_problems(p_id);
    WHEN 'braid_rewrite' THEN RETURN QUERY SELECT * FROM braid_rewrite_transport_problems(p_id);
    WHEN 'braid_derivation' THEN RETURN QUERY SELECT * FROM braid_derivation_transport_problems(p_id);
  END CASE;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_invariants_record(p_table TEXT, p_id UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  PERFORM qbx_record_violation('braid_invariants', p_reason,
                               coalesce(p_details, '{}'::jsonb) || jsonb_build_object('table', p_table),
                               p_id);
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_invariants_check_row(p_table TEXT, p_id UUID) RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM braid_invariants_problems_of(p_table, p_id) LOOP
    PERFORM braid_invariants_record(p_table, p_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- Every certificate, then the transport check on every rewrite and
-- derivation.  Returns the number of problems found.
CREATE OR REPLACE FUNCTION check_braid_invariants() RETURNS INT AS $$
DECLARE
  t RECORD;
  n INT := 0;
BEGIN
  FOR t IN SELECT 1 AS o0, 'braid_invariant' AS tb, id, created_at AS o1, seq AS o2 FROM braid_invariant
           UNION ALL SELECT 2, 'braid_rewrite', id, created_at, seq FROM braid_rewrite
           UNION ALL SELECT 3, 'braid_derivation', id, created_at, seq FROM braid_derivation
           ORDER BY 1, 4, 5 LOOP
    n := n + braid_invariants_check_row(t.tb, t.id);
  END LOOP;
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Braid invariant certificates have problems (% problem(s))', n;
  END IF;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- Phase 1 batch checks (frozen migration 017) followed by the Phase 2 ones
-- (replaces the definition of migration 019).
CREATE OR REPLACE FUNCTION run_phase2_batch_checks() RETURNS VOID AS $$
BEGIN
  PERFORM run_all_batch_checks();
  PERFORM check_braid_ledger();
  PERFORM check_braid_invariants();
  RAISE NOTICE 'run_phase2_batch_checks: complete';
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_braid_invariant_row() RETURNS trigger AS $$
DECLARE
  n INT;
BEGIN
  n := braid_invariants_check_row('braid_invariant', NEW.id);
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'braid_invariant row % is not valid (% problem(s))', NEW.id, n;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_braid_invariant_row ON braid_invariant;
CREATE TRIGGER trg_check_braid_invariant_row AFTER INSERT ON braid_invariant
FOR EACH ROW EXECUTE FUNCTION trg_check_braid_invariant_row();

-- Certificates are append-only: an UPDATE, DELETE or TRUNCATE is logged (and
-- refused in strict mode).
CREATE OR REPLACE FUNCTION trg_braid_invariant_append_only() RETURNS trigger AS $$
BEGIN
  PERFORM braid_invariants_record(TG_TABLE_NAME, CASE WHEN TG_LEVEL = 'ROW' THEN OLD.id END,
                                  'log_mutation', jsonb_build_object('op', TG_OP));
  IF functor_is_strict() THEN
    RAISE EXCEPTION '% on % refused: invariant certificates are append-only', TG_OP, TG_TABLE_NAME;
  END IF;
  IF TG_OP = 'DELETE' THEN RETURN OLD; END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_braid_invariant_append_only ON braid_invariant;
CREATE TRIGGER trg_braid_invariant_append_only BEFORE UPDATE OR DELETE ON braid_invariant
FOR EACH ROW EXECUTE FUNCTION trg_braid_invariant_append_only();
DROP TRIGGER IF EXISTS trg_braid_invariant_append_only_truncate ON braid_invariant;
CREATE TRIGGER trg_braid_invariant_append_only_truncate BEFORE TRUNCATE ON braid_invariant
FOR EACH STATEMENT EXECUTE FUNCTION trg_braid_invariant_append_only();

-- ---------------------------------------------------------------------------
-- Writer
-- ---------------------------------------------------------------------------

-- Compute and store the certificate of a registered braid; returns its id
-- (the existing one if the braid already has a certificate).
CREATE OR REPLACE FUNCTION certify_braid_invariants(p_braid UUID) RETURNS UUID AS $$
DECLARE
  b RECORD;
  v RECORD;
  c_id UUID;
BEGIN
  SELECT * INTO b FROM braid_word WHERE id = p_braid;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'certify_braid_invariants: unknown braid %', p_braid;
  END IF;
  IF NOT braid_is_well_formed(p_braid) THEN
    RAISE EXCEPTION 'certify_braid_invariants: braid_not_well_formed (%)', p_braid;
  END IF;
  SELECT id INTO c_id FROM braid_invariant WHERE braid_id = p_braid;
  IF c_id IS NOT NULL THEN
    RETURN c_id;
  END IF;
  SELECT * INTO v FROM braid_invariant_values(b.strand_count, b.word);
  INSERT INTO braid_invariant (braid_id, braid_hash, permutation, writhe, components, linking)
  VALUES (p_braid, b.braid_hash, v.permutation, v.writhe, v.components, v.linking)
  RETURNING id INTO c_id;
  RETURN c_id;
END;
$$ LANGUAGE plpgsql;
