-- ============================================================================
-- Categorical Ledger — Migration 022: Exact Representation Certificates
-- (Phase 2 sprint 4)
-- ============================================================================
-- Stores, for a braid of the braid ledger (migration 019) and a non-zero
-- rational parameter q = q_num / q_den (lowest terms, q_den > 0), the EXACT
-- matrix of the braid in the U_q(sl_2) quantum representation on (Q^2)^{⊗n}
-- (qbx_ir.quantum.r_matrix.SL2RMatrix), recomputed by the database from the
-- word with integer arithmetic only:
--
--   braid_representation   one certificate per braid and parameter:
--                            dimension    2^n;
--                            numerators   the integer numerators, row-major;
--                            denominator  the positive common denominator,
--                                         gcd(denominator, numerators) = 1;
--                            braid_hash   the hash of the certified braid.
--                          Append-only.
--
-- Computation (qbx_ir.quantum.exact.exact_sl2_matrix): every letter is
-- multiplied, in word order, by the scaled R-matrix p r · Ř (σ_i) or
-- p r · Ř⁻¹ (σ_i⁻¹), q = p / r, whose entries are integers; the denominator is
-- (p r)^length; the fraction is then reduced by ± gcd(denominator, entries),
-- the sign making the denominator positive.  Basis state (s_1, …, s_n) has
-- index Σ s_m 2^(n-m) (as numpy.kron).  Strand counts above 6 are refused
-- (the matrix has 4^n entries).
--
-- Uses of the certificates:
--   * braid_representation_equal(a, b, q_num, q_den): TRUE iff ρ_q(a) = ρ_q(b)
--     exactly (EqualityKind.REPRESENTATION, no tolerance; this is NOT equality
--     in B_n — the representation need not be faithful); FALSE: the braids are
--     different elements of B_n; NULL: not comparable;
--   * braid_representation_inequality_certified: the FALSE case;
--   * transport: along every accepted rewrite and derivation the certificates
--     at each common parameter must agree (batch tier);
--   * consistency with migration 021: braids certified equal by their normal
--     forms must not have different certificates (batch tier).
--
-- Reference implementation: qbx_ir.representation_ledger (same problems, same
-- order, same details).  Lean: QBX/Formal/BraidRepCert.lean — the
-- letter-by-letter matrix is the quantum operator of YangBaxter.lean
-- (toLin'_repMat), the integer computation is (p r)^length times the rational
-- matrix (scaledMat_cast), the reduced fraction is unique (reduced_unique), so
-- certificates are equal iff the matrices are (repCert_eq_iff); equal braids
-- have equal certificates (repCert_eq_of_eval_eq) and different certificates
-- prove different braids (eval_ne_of_repCert_ne); registry H-058, H-059.
--
-- Problems are logged to invariant_violation (migration 017) with module
-- 'braid_representations', object_id the row and details.table its table.
-- run_phase2_batch_checks() (redefined here) runs run_all_batch_checks(),
-- check_braid_ledger(), check_braid_invariants(), check_braid_normal_forms()
-- and check_braid_representations().
--
-- Write-time tier: every inserted certificate is checked (logged; raised in
-- strict mode).  The writer certify_braid_representation refuses a braid that
-- is not well formed, an invalid parameter and a strand count above 6.
-- ============================================================================

CREATE TABLE IF NOT EXISTS braid_representation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  seq BIGSERIAL,
  braid_id UUID NOT NULL REFERENCES braid_word(id) ON DELETE CASCADE,
  q_num BIGINT NOT NULL,
  q_den BIGINT NOT NULL,
  braid_hash TEXT NOT NULL,
  dimension INT NOT NULL,
  numerators NUMERIC[] NOT NULL DEFAULT '{}',
  denominator NUMERIC NOT NULL,
  created_at TIMESTAMPTZ DEFAULT now(),
  UNIQUE (braid_id, q_num, q_den)
);

-- ---------------------------------------------------------------------------
-- Recomputation (qbx_ir.quantum.exact)
-- ---------------------------------------------------------------------------

-- Largest strand count accepted (qbx_ir.representation_ledger.MAX_REP_STRANDS).
CREATE OR REPLACE FUNCTION braid_representation_max_strands() RETURNS INT AS $$
  SELECT 6
$$ LANGUAGE sql IMMUTABLE;

-- qbx_ir.quantum.exact.parameter_problem: q_num / q_den is a non-zero rational
-- in lowest terms with q_den > 0.
CREATE OR REPLACE FUNCTION braid_representation_parameter_ok(p_num BIGINT, p_den BIGINT)
RETURNS BOOLEAN AS $$
  SELECT p_num IS NOT NULL AND p_den IS NOT NULL AND p_den > 0 AND p_num <> 0
         AND gcd(p_num::numeric, p_den::numeric) = 1
$$ LANGUAGE sql IMMUTABLE;

-- The certificate fields of a well-formed braid (strand count 1..6, valid
-- parameter); one row.  The letter loop follows
-- qbx_ir.quantum.exact.scaled_product: U := U · (p r · Ř) at sites i, i+1.
CREATE OR REPLACE FUNCTION braid_representation_values(p_n INT, p_word INT[], p_num BIGINT,
                                                       p_den BIGINT)
RETURNS TABLE(dimension INT, numerators NUMERIC[], denominator NUMERIC) AS $$
DECLARE
  len INT := coalesce(cardinality(p_word), 0);
  dim INT := (2 ^ p_n)::int;
  p NUMERIC := p_num;
  r NUMERIC := p_den;
  gp NUMERIC[];
  gn NUMERIC[];
  g NUMERIC[];
  u NUMERIC[];
  v NUMERIC[];
  k INT;
  i INT;
  w1 INT;
  w2 INT;
  t INT;
  c INT;
  e INT;
  col INT;
  base INT;
  x INT;
  a INT;
  b INT;
  coef NUMERIC;
  acc NUMERIC;
  den NUMERIC := 1;
  gg NUMERIC;
BEGIN
  -- table[a*2+b][c*2+e] stored at index (a*2+b)*4 + (c*2+e) + 1.
  gp := ARRAY[p * p, 0, 0, 0,
              0, 0, p * r, 0,
              0, p * r, p * p - r * r, 0,
              0, 0, 0, p * p]::numeric[];
  gn := ARRAY[r * r, 0, 0, 0,
              0, -(p * p - r * r), p * r, 0,
              0, p * r, 0, 0,
              0, 0, 0, r * r]::numeric[];
  u := array_fill(0::numeric, ARRAY[dim * dim]);
  FOR x IN 0..dim - 1 LOOP
    u[x * dim + x + 1] := 1;
  END LOOP;
  FOR k IN 1..len LOOP
    i := abs(p_word[k]);
    g := CASE WHEN p_word[k] > 0 THEN gp ELSE gn END;
    w1 := (2 ^ (p_n - i))::int;
    w2 := (2 ^ (p_n - i - 1))::int;
    v := array_fill(0::numeric, ARRAY[dim * dim]);
    FOR t IN 0..dim - 1 LOOP
      c := (t / w1) % 2;
      e := (t / w2) % 2;
      base := t - c * w1 - e * w2;
      col := c * 2 + e;
      FOR x IN 0..dim - 1 LOOP
        acc := 0;
        FOR a IN 0..1 LOOP
          FOR b IN 0..1 LOOP
            coef := g[(a * 2 + b) * 4 + col + 1];
            IF coef <> 0 THEN
              acc := acc + u[x * dim + base + a * w1 + b * w2 + 1] * coef;
            END IF;
          END LOOP;
        END LOOP;
        v[x * dim + t + 1] := acc;
      END LOOP;
    END LOOP;
    u := v;
    den := den * (p * r);
  END LOOP;
  -- Reduce by ± gcd(denominator, entries) (qbx_ir.quantum.exact.reduce_fraction).
  gg := abs(den);
  FOR k IN 1..dim * dim LOOP
    gg := gcd(gg, u[k]);
  END LOOP;
  IF den < 0 THEN gg := -gg; END IF;
  dimension := dim;
  numerators := ARRAY(SELECT div(y, gg) FROM unnest(u) WITH ORDINALITY AS z(y, o) ORDER BY o);
  denominator := div(den, gg);
  RETURN NEXT;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Problems (qbx_ir.representation_ledger)
-- ---------------------------------------------------------------------------

-- qbx_ir.representation_ledger.certificate_problems.
CREATE OR REPLACE FUNCTION braid_representation_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  b RECORD;
  v RECORD;
  k INT;
  first_k INT;
  rl INT;
  el INT;
BEGIN
  SELECT * INTO c FROM braid_representation WHERE id = p_id;
  IF NOT FOUND THEN RETURN; END IF;
  IF NOT braid_is_well_formed(c.braid_id) THEN
    reason := 'braid_not_well_formed'; details := '{}'::jsonb; RETURN NEXT; RETURN;
  END IF;
  IF NOT braid_representation_parameter_ok(c.q_num, c.q_den) THEN
    reason := 'parameter_invalid';
    details := jsonb_build_object('q_num', c.q_num, 'q_den', c.q_den);
    RETURN NEXT; RETURN;
  END IF;
  SELECT * INTO b FROM braid_word WHERE id = c.braid_id;
  IF b.strand_count > braid_representation_max_strands() THEN
    reason := 'strand_count_too_large';
    details := jsonb_build_object('strand_count', b.strand_count,
                                  'max', braid_representation_max_strands());
    RETURN NEXT; RETURN;
  END IF;
  IF c.braid_hash IS DISTINCT FROM b.braid_hash THEN
    reason := 'braid_hash_mismatch';
    details := jsonb_build_object('recorded', c.braid_hash, 'expected', b.braid_hash);
    RETURN NEXT;
  END IF;
  SELECT * INTO v FROM braid_representation_values(b.strand_count, b.word, c.q_num, c.q_den);
  IF c.dimension IS DISTINCT FROM v.dimension THEN
    reason := 'dimension_mismatch';
    details := jsonb_build_object('recorded', c.dimension, 'expected', v.dimension);
    RETURN NEXT;
  END IF;
  IF c.denominator IS DISTINCT FROM v.denominator THEN
    reason := 'denominator_mismatch';
    details := jsonb_build_object('recorded', c.denominator::text, 'expected', v.denominator::text);
    RETURN NEXT;
  END IF;
  rl := coalesce(cardinality(c.numerators), 0);
  el := coalesce(cardinality(v.numerators), 0);
  IF rl <> el OR c.numerators IS DISTINCT FROM v.numerators THEN
    first_k := least(rl, el);
    FOR k IN 1..least(rl, el) LOOP
      IF c.numerators[k] IS DISTINCT FROM v.numerators[k] THEN
        first_k := k - 1;
        EXIT;
      END IF;
    END LOOP;
    reason := 'numerators_mismatch';
    details := jsonb_build_object('recorded_length', rl, 'expected_length', el,
                                  'first_index', first_k);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- The certificate of a braid at a parameter, if it has one without problems.
CREATE OR REPLACE FUNCTION braid_valid_representation(p_braid UUID, p_num BIGINT, p_den BIGINT)
RETURNS UUID AS $$
  SELECT c.id FROM braid_representation c
   WHERE c.braid_id = p_braid AND c.q_num = p_num AND c.q_den = p_den
     AND NOT EXISTS (SELECT 1 FROM braid_representation_problems(c.id))
$$ LANGUAGE sql;

-- qbx_ir.representation_ledger.representations_equal: NULL unless both braids
-- have valid certificates at q = p_num / p_den and the same strand count; TRUE
-- iff the exact matrices are equal (Lean: repCert_eq_iff) — representation
-- equality, not equality in B_n; FALSE certifies that the braids are
-- different (Lean: eval_ne_of_repCert_ne).
CREATE OR REPLACE FUNCTION braid_representation_equal(p_a UUID, p_b UUID, p_num BIGINT,
                                                      p_den BIGINT)
RETURNS BOOLEAN AS $$
DECLARE
  ia UUID;
  ib UUID;
  ca RECORD;
  cb RECORD;
BEGIN
  ia := braid_valid_representation(p_a, p_num, p_den);
  IF ia IS NULL THEN RETURN NULL; END IF;
  ib := braid_valid_representation(p_b, p_num, p_den);
  IF ib IS NULL THEN RETURN NULL; END IF;
  SELECT * INTO ca FROM braid_representation WHERE id = ia;
  SELECT * INTO cb FROM braid_representation WHERE id = ib;
  IF (SELECT strand_count FROM braid_word WHERE id = p_a)
     IS DISTINCT FROM (SELECT strand_count FROM braid_word WHERE id = p_b) THEN
    RETURN NULL;
  END IF;
  RETURN ca.denominator = cb.denominator AND ca.numerators = cb.numerators;
END;
$$ LANGUAGE plpgsql;

-- True iff the two braids have valid certificates at q that differ: a
-- certificate that they are different elements of B_n.  FALSE means "not
-- certified", not "equal".
CREATE OR REPLACE FUNCTION braid_representation_inequality_certified(p_a UUID, p_b UUID,
                                                                     p_num BIGINT DEFAULT 2,
                                                                     p_den BIGINT DEFAULT 1)
RETURNS BOOLEAN AS $$
  SELECT braid_representation_equal(p_a, p_b, p_num, p_den) IS FALSE
$$ LANGUAGE sql;

-- qbx_ir.representation_ledger.transport_problems between two braids.
CREATE OR REPLACE FUNCTION braid_rep_transport_between(p_a UUID, p_b UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
BEGIN
  FOR c IN SELECT * FROM braid_representation WHERE braid_id = p_a ORDER BY q_num, q_den LOOP
    IF braid_representation_equal(p_a, p_b, c.q_num, c.q_den) IS FALSE THEN
      reason := 'representation_not_preserved';
      details := jsonb_build_object('q_num', c.q_num, 'q_den', c.q_den);
      RETURN NEXT;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- The transport check for a rewrite record.
CREATE OR REPLACE FUNCTION braid_rewrite_rep_transport_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT * INTO r FROM braid_rewrite WHERE id = p_id;
  IF NOT FOUND OR NOT braid_rewrite_is_valid(p_id) THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM braid_rep_transport_between(r.input_braid_id, r.output_braid_id);
END;
$$ LANGUAGE plpgsql;

-- The transport check for a derivation.
CREATE OR REPLACE FUNCTION braid_derivation_rep_transport_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  d RECORD;
BEGIN
  SELECT * INTO d FROM braid_derivation WHERE id = p_id;
  IF NOT FOUND OR EXISTS (SELECT 1 FROM braid_derivation_problems(p_id)) THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM braid_rep_transport_between(d.source_braid_id, d.target_braid_id);
END;
$$ LANGUAGE plpgsql;

-- qbx_ir.representation_ledger.nf_consistency_problems: other braids certified
-- equal by their normal forms (migration 021) must not have a different valid
-- certificate at the same parameter.
CREATE OR REPLACE FUNCTION braid_rep_nf_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  o RECORD;
BEGIN
  SELECT * INTO c FROM braid_representation WHERE id = p_id;
  IF NOT FOUND OR EXISTS (SELECT 1 FROM braid_representation_problems(p_id)) THEN RETURN; END IF;
  -- Candidates: other braids whose stored normal form has the same power and
  -- factors (both are then re-validated by braid_nf_equality_certified).
  FOR o IN SELECT oc.braid_id, ob.braid_hash
             FROM braid_representation oc JOIN braid_word ob ON ob.id = oc.braid_id
             JOIN braid_normal_form onf ON onf.braid_id = oc.braid_id
             JOIN braid_normal_form cnf ON cnf.braid_id = c.braid_id
            WHERE oc.braid_id <> c.braid_id AND oc.q_num = c.q_num AND oc.q_den = c.q_den
              AND onf.power = cnf.power AND to_jsonb(onf.factors) = to_jsonb(cnf.factors)
            ORDER BY ob.braid_hash, oc.seq LOOP
    IF NOT braid_nf_equality_certified(c.braid_id, o.braid_id) THEN CONTINUE; END IF;
    IF braid_representation_equal(c.braid_id, o.braid_id, c.q_num, c.q_den) IS FALSE THEN
      reason := 'representation_contradicts_normal_form';
      details := jsonb_build_object('other_braid_hash', o.braid_hash);
      RETURN NEXT;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION braid_representations_problems_of(p_table TEXT, p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  CASE p_table
    WHEN 'braid_representation' THEN
      RETURN QUERY SELECT * FROM braid_representation_problems(p_id);
      RETURN QUERY SELECT * FROM braid_rep_nf_problems(p_id);
    WHEN 'braid_rewrite' THEN RETURN QUERY SELECT * FROM braid_rewrite_rep_transport_problems(p_id);
    WHEN 'braid_derivation' THEN RETURN QUERY SELECT * FROM braid_derivation_rep_transport_problems(p_id);
  END CASE;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_representations_record(p_table TEXT, p_id UUID, p_reason TEXT,
                                                        p_details JSONB)
RETURNS VOID AS $$
BEGIN
  PERFORM qbx_record_violation('braid_representations', p_reason,
                               coalesce(p_details, '{}'::jsonb) || jsonb_build_object('table', p_table),
                               p_id);
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_representations_check_row(p_table TEXT, p_id UUID) RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM braid_representations_problems_of(p_table, p_id) LOOP
    PERFORM braid_representations_record(p_table, p_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- Every certificate (with the normal-form consistency check), then the
-- transport check on every rewrite and derivation.  Returns the number of
-- problems found.
CREATE OR REPLACE FUNCTION check_braid_representations() RETURNS INT AS $$
DECLARE
  t RECORD;
  n INT := 0;
BEGIN
  FOR t IN SELECT 1 AS o0, 'braid_representation' AS tb, id, created_at AS o1, seq AS o2
             FROM braid_representation
           UNION ALL SELECT 2, 'braid_rewrite', id, created_at, seq FROM braid_rewrite
           UNION ALL SELECT 3, 'braid_derivation', id, created_at, seq FROM braid_derivation
           ORDER BY 1, 4, 5 LOOP
    n := n + braid_representations_check_row(t.tb, t.id);
  END LOOP;
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Braid representation certificates have problems (% problem(s))', n;
  END IF;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- Phase 1 batch checks (frozen migration 017) followed by the Phase 2 ones
-- (replaces the definition of migration 021).
CREATE OR REPLACE FUNCTION run_phase2_batch_checks() RETURNS VOID AS $$
BEGIN
  PERFORM run_all_batch_checks();
  PERFORM check_braid_ledger();
  PERFORM check_braid_invariants();
  PERFORM check_braid_normal_forms();
  PERFORM check_braid_representations();
  RAISE NOTICE 'run_phase2_batch_checks: complete';
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_braid_representation_row() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM braid_representation_problems(NEW.id) LOOP
    PERFORM braid_representations_record('braid_representation', NEW.id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'braid_representation row % is not valid (% problem(s))', NEW.id, n;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_braid_representation_row ON braid_representation;
CREATE TRIGGER trg_check_braid_representation_row AFTER INSERT ON braid_representation
FOR EACH ROW EXECUTE FUNCTION trg_check_braid_representation_row();

-- Certificates are append-only: an UPDATE, DELETE or TRUNCATE is logged (and
-- refused in strict mode).
CREATE OR REPLACE FUNCTION trg_braid_representation_append_only() RETURNS trigger AS $$
BEGIN
  PERFORM braid_representations_record(TG_TABLE_NAME, CASE WHEN TG_LEVEL = 'ROW' THEN OLD.id END,
                                       'log_mutation', jsonb_build_object('op', TG_OP));
  IF functor_is_strict() THEN
    RAISE EXCEPTION '% on % refused: representation certificates are append-only', TG_OP, TG_TABLE_NAME;
  END IF;
  IF TG_OP = 'DELETE' THEN RETURN OLD; END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_braid_representation_append_only ON braid_representation;
CREATE TRIGGER trg_braid_representation_append_only BEFORE UPDATE OR DELETE ON braid_representation
FOR EACH ROW EXECUTE FUNCTION trg_braid_representation_append_only();
DROP TRIGGER IF EXISTS trg_braid_representation_append_only_truncate ON braid_representation;
CREATE TRIGGER trg_braid_representation_append_only_truncate BEFORE TRUNCATE ON braid_representation
FOR EACH STATEMENT EXECUTE FUNCTION trg_braid_representation_append_only();

-- ---------------------------------------------------------------------------
-- Writer
-- ---------------------------------------------------------------------------

-- Compute and store the certificate of a registered braid at q = p_num / p_den
-- (default q = 2); returns its id (the existing one if there is already a
-- certificate for this braid and parameter).
CREATE OR REPLACE FUNCTION certify_braid_representation(p_braid UUID, p_num BIGINT DEFAULT 2,
                                                        p_den BIGINT DEFAULT 1)
RETURNS UUID AS $$
DECLARE
  b RECORD;
  v RECORD;
  c_id UUID;
BEGIN
  SELECT * INTO b FROM braid_word WHERE id = p_braid;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'certify_braid_representation: unknown braid %', p_braid;
  END IF;
  IF NOT braid_is_well_formed(p_braid) THEN
    RAISE EXCEPTION 'certify_braid_representation: braid_not_well_formed (%)', p_braid;
  END IF;
  IF NOT braid_representation_parameter_ok(p_num, p_den) THEN
    RAISE EXCEPTION 'certify_braid_representation: parameter_invalid (% / %)', p_num, p_den;
  END IF;
  IF b.strand_count > braid_representation_max_strands() THEN
    RAISE EXCEPTION 'certify_braid_representation: strand_count_too_large (%)', b.strand_count;
  END IF;
  SELECT id INTO c_id FROM braid_representation
   WHERE braid_id = p_braid AND q_num = p_num AND q_den = p_den;
  IF c_id IS NOT NULL THEN
    RETURN c_id;
  END IF;
  SELECT * INTO v FROM braid_representation_values(b.strand_count, b.word, p_num, p_den);
  INSERT INTO braid_representation (braid_id, q_num, q_den, braid_hash, dimension, numerators,
                                    denominator)
  VALUES (p_braid, p_num, p_den, b.braid_hash, v.dimension, v.numerators, v.denominator)
  RETURNING id INTO c_id;
  RETURN c_id;
END;
$$ LANGUAGE plpgsql;
