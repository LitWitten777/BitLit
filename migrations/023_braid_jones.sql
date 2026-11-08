-- ============================================================================
-- Categorical Ledger — Migration 023: Kauffman Bracket / Jones Certificates
-- (Phase 3 item 2)
-- ============================================================================
-- STATUS: written 2026-10-15 without access to a PostgreSQL server.  The
-- algorithm below was checked against the reference implementation by a
-- line-by-line Python transcription (tests/qbx_ir/test_jones_sql_model.py),
-- but this file itself has NOT yet been parsed or executed by PostgreSQL.
-- Run tests/test_migrations_parse.py and tests/live_db/test_braid_jones_db.py
-- before relying on it.
--
-- Stores, for a braid of the braid ledger (migration 019), the Kauffman
-- bracket of its closure in the variable A (⟨O⟩ = 1) of
-- qbx_ir.algebra.polynomial_invariants.kauffman_bracket and its Jones
-- polynomial V = (−A³)^(−w) ⟨B̂⟩ (w the writhe, A = t^(−1/4)), recomputed by
-- the database from the word with integer arithmetic only:
--
--   braid_jones    one certificate per braid:
--                    bracket_exp_min,       the bracket Σ_k c_k A^(exp_min + k),
--                    bracket_width,         0 ≤ k < width, in the smallest
--                    bracket_coefficients   window (c_0 ≠ 0, c_(width-1) ≠ 0);
--                                           exp_min = width = 0 for 0;
--                    jones_exp_min,         the Jones polynomial in A, same
--                    jones_width,           encoding;
--                    jones_coefficients
--                    braid_hash             the hash of the certified braid.
--                  Append-only.  Strand counts above 12 are refused.
--
-- Computation (qbx_ir.algebra.polynomial_invariants.kauffman_bracket): the
-- word is multiplied out in the Temperley–Lieb algebra, ⟨σ_i⟩ = A·1 + A⁻¹·e_i
-- and ⟨σ_i⁻¹⟩ = A⁻¹·1 + A·e_i.  A state is a planar matching of the 2n end
-- points (top j = j, bottom j = n + j, 0-based), stored as the text of its
-- matching array; the state set is a set of rows (matching, exponent,
-- coefficient), merged with GROUP BY after each letter.  Multiplying a
-- matching by e_i caps the bottom points i, i+1 (a closed loop when they were
-- matched to each other, giving the factor d = −A² − A⁻²) and adds a new cup.
-- The closure of a matching with L loops contributes d^(L−1).
--
-- Uses of the certificates:
--   * braid_bracket_equal(a, b) (same strand count): TRUE iff the brackets are
--     equal; FALSE: the braids are different elements of B_n and are not
--     conjugate (the bracket is a conjugacy invariant);
--     braid_bracket_non_conjugacy_certified is that case;
--   * braid_jones_equal(a, b) (any strand counts): FALSE: the closures are
--     not isotopic links (the Jones polynomial is invariant under Markov's
--     moves); braid_jones_non_isotopy_certified is that case;
--   * transport: along every accepted rewrite and derivation the bracket and
--     the Jones polynomial must agree (batch tier);
--   * consistency with migration 021: braids certified equal by their normal
--     forms must not have different certificates (batch tier).
--
-- Reference implementation: qbx_ir.jones_ledger (same problems, same order,
-- same details).  Lean: QBX/Formal/KauffmanBracket/ — the bracket recursion is
-- the quantum trace (quantumTrace_eq_bracket), so the Jones polynomial is a
-- Markov invariant (jonesPoly_markov); the bracket is a braid and conjugacy
-- invariant (bracketPoly_eq_of_eval_eq, bracketPoly_conj); the encoding is
-- unique (certPoly_inj); different Jones certificates prove non-isotopic
-- closures (not_markovEquiv_of_jonesCert_ne); the Lean model gives exactly the
-- Python values on test vectors (jones_agrees_with_python); registry H-278 …
-- H-281.
--
-- Problems are logged to invariant_violation (migration 017) with module
-- 'braid_jones', object_id the row and details.table its table.
-- check_braid_jones() is the batch check; run_phase3_batch_checks() (defined
-- here and again in migration 024) runs run_phase2_batch_checks() (frozen,
-- 022), check_braid_burau() (024) and check_braid_jones().  Migration files
-- are applied in name order, so on a fresh database this file runs before
-- 024; the definition below calls check_braid_burau() only when it exists, so
-- applying 023 after 024 on an existing database also keeps both checks.
--
-- Write-time tier: every inserted certificate is checked (logged; raised in
-- strict mode).  The writer certify_braid_jones refuses a braid that is not
-- well formed and a strand count above 12.
-- ============================================================================

CREATE TABLE IF NOT EXISTS braid_jones (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  seq BIGSERIAL,
  braid_id UUID NOT NULL REFERENCES braid_word(id) ON DELETE CASCADE,
  braid_hash TEXT NOT NULL,
  bracket_exp_min INT NOT NULL,
  bracket_width INT NOT NULL,
  bracket_coefficients NUMERIC[] NOT NULL DEFAULT '{}',
  jones_exp_min INT NOT NULL,
  jones_width INT NOT NULL,
  jones_coefficients NUMERIC[] NOT NULL DEFAULT '{}',
  created_at TIMESTAMPTZ DEFAULT now(),
  UNIQUE (braid_id)
);

-- ---------------------------------------------------------------------------
-- Recomputation (qbx_ir.jones_ledger.jones_values)
-- ---------------------------------------------------------------------------

-- Largest strand count accepted (qbx_ir.jones_ledger.MAX_JONES_STRANDS).
CREATE OR REPLACE FUNCTION braid_jones_max_strands() RETURNS INT AS $$
  SELECT 12
$$ LANGUAGE sql IMMUTABLE;

-- match · e_i for a matching of 2n points given as text ('m_0,m_1,…'), with
-- p_i the 0-based generator index: the new matching, and whether a closed loop
-- was removed (the bottom points i and i+1 were matched to each other).
CREATE OR REPLACE FUNCTION braid_jones_cup(p_key TEXT, p_n INT, p_i INT)
RETURNS TABLE(key2 TEXT, closed BOOLEAN) AS $$
DECLARE
  m INT[] := string_to_array(p_key, ',')::int[];
  bi INT := p_n + p_i;
  bj INT := p_n + p_i + 1;
  x INT;
  y INT;
BEGIN
  x := m[bi + 1];
  y := m[bj + 1];
  IF x = bj THEN
    closed := TRUE;
  ELSE
    closed := FALSE;
    m[x + 1] := y;
    m[y + 1] := x;
  END IF;
  m[bi + 1] := bj;
  m[bj + 1] := bi;
  key2 := array_to_string(m, ',');
  RETURN NEXT;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- Number of loops of the closure of a matching (top j joined to bottom j).
CREATE OR REPLACE FUNCTION braid_jones_loops(p_key TEXT, p_n INT) RETURNS INT AS $$
DECLARE
  m INT[] := string_to_array(p_key, ',')::int[];
  seen BOOLEAN[] := array_fill(FALSE, ARRAY[2 * p_n]);
  loops INT := 0;
  st INT;
  p INT;
  q INT;
BEGIN
  FOR st IN 0..2 * p_n - 1 LOOP
    IF seen[st + 1] THEN CONTINUE; END IF;
    loops := loops + 1;
    p := st;
    WHILE NOT seen[p + 1] LOOP
      seen[p + 1] := TRUE;
      q := m[p + 1];
      seen[q + 1] := TRUE;
      IF q >= p_n THEN p := q - p_n; ELSE p := q + p_n; END IF;
    END LOOP;
  END LOOP;
  RETURN loops;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- Binomial coefficient C(p_n, p_k), 0 ≤ p_k ≤ p_n.
CREATE OR REPLACE FUNCTION braid_jones_binom(p_n INT, p_k INT) RETURNS NUMERIC AS $$
DECLARE
  r NUMERIC := 1;
  j INT;
BEGIN
  FOR j IN 1..p_k LOOP
    r := div(r * (p_n - p_k + j), j);   -- exact: r·(n-k+j)/j = C(n-k+j, j)
  END LOOP;
  RETURN r;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- The certificate fields of a well-formed braid with 1..12 strands; one row.
CREATE OR REPLACE FUNCTION braid_jones_values(p_n INT, p_word INT[])
RETURNS TABLE(bracket_exp_min INT, bracket_width INT, bracket_coefficients NUMERIC[],
              jones_exp_min INT, jones_width INT, jones_coefficients NUMERIC[]) AS $$
DECLARE
  len INT := coalesce(cardinality(p_word), 0);
  keys TEXT[];
  es INT[];
  cs NUMERIC[];
  k INT;
  gi INT;
  a_id INT;
  a_cup INT;
  w INT := 0;
  lo INT;
  hi INT;
  sgn NUMERIC;
BEGIN
  -- The identity matching: top j ↔ bottom j.
  keys := ARRAY[array_to_string(ARRAY(SELECT CASE WHEN j < p_n THEN j + p_n ELSE j - p_n END
                                        FROM generate_series(0, 2 * p_n - 1) AS j
                                       ORDER BY j), ',')];
  es := ARRAY[0];
  cs := ARRAY[1]::numeric[];
  FOR k IN 1..len LOOP
    gi := abs(p_word[k]) - 1;
    IF p_word[k] > 0 THEN
      a_id := 1; a_cup := -1; w := w + 1;
    ELSE
      a_id := -1; a_cup := 1; w := w - 1;
    END IF;
    SELECT coalesce(array_agg(g.k ORDER BY g.k, g.e), '{}'),
           coalesce(array_agg(g.e ORDER BY g.k, g.e), '{}'),
           coalesce(array_agg(g.c ORDER BY g.k, g.e), '{}')
      INTO keys, es, cs
      FROM (SELECT u.k, u.e, sum(u.c) AS c
              FROM (SELECT z.k, z.e + a_id AS e, z.c
                      FROM unnest(keys, es, cs) AS z(k, e, c)
                    UNION ALL
                    SELECT t.key2, z.e + a_cup + dd.sh, z.c * dd.f
                      FROM unnest(keys, es, cs) AS z(k, e, c)
                      CROSS JOIN LATERAL braid_jones_cup(z.k, p_n, gi) AS t
                      JOIN (VALUES (0, 1, FALSE), (2, -1, TRUE), (-2, -1, TRUE))
                           AS dd(sh, f, cl) ON dd.cl = t.closed) AS u
             GROUP BY u.k, u.e
            HAVING sum(u.c) <> 0) AS g;
  END LOOP;
  -- Closure: a matching with L loops contributes
  -- d^(L-1) = (-1)^(L-1) Σ_i C(L-1, i) A^(2(L-1) - 4i).
  SELECT coalesce(array_agg(f.e ORDER BY f.e), '{}'),
         coalesce(array_agg(f.c ORDER BY f.e), '{}')
    INTO es, cs
    FROM (SELECT v.e, sum(v.c) AS c
            FROM (SELECT z.e + 2 * (l.n - 1) - 4 * i AS e,
                         z.c * (CASE WHEN (l.n - 1) % 2 = 0 THEN 1 ELSE -1 END)
                             * braid_jones_binom(l.n - 1, i) AS c
                    FROM unnest(keys, es, cs) AS z(k, e, c)
                    CROSS JOIN LATERAL (SELECT braid_jones_loops(z.k, p_n) AS n) AS l
                    CROSS JOIN LATERAL generate_series(0, l.n - 1) AS i) AS v
           GROUP BY v.e
          HAVING sum(v.c) <> 0) AS f;
  IF cardinality(es) = 0 THEN
    bracket_exp_min := 0; bracket_width := 0; bracket_coefficients := '{}';
    jones_exp_min := 0; jones_width := 0; jones_coefficients := '{}';
    RETURN NEXT; RETURN;
  END IF;
  lo := es[1];
  hi := es[cardinality(es)];
  bracket_exp_min := lo;
  bracket_width := hi - lo + 1;
  bracket_coefficients := ARRAY(
    SELECT coalesce((SELECT cs[o] FROM generate_series(1, cardinality(es)) AS o
                      WHERE es[o] = x), 0)
      FROM generate_series(lo, hi) AS x ORDER BY x);
  -- Jones: (−A³)^(−w) ⟨B̂⟩ = (−1)^w A^(−3w) ⟨B̂⟩.
  IF w % 2 = 0 THEN sgn := 1; ELSE sgn := -1; END IF;
  jones_exp_min := lo - 3 * w;
  jones_width := bracket_width;
  jones_coefficients := ARRAY(SELECT sgn * x FROM unnest(bracket_coefficients)
                                WITH ORDINALITY AS z(x, o) ORDER BY o);
  RETURN NEXT;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Problems (qbx_ir.jones_ledger)
-- ---------------------------------------------------------------------------

-- Index (0-based) of the first difference of two arrays, or the shorter length.
CREATE OR REPLACE FUNCTION braid_jones_first_difference(a NUMERIC[], b NUMERIC[])
RETURNS INT AS $$
DECLARE
  la INT := coalesce(cardinality(a), 0);
  lb INT := coalesce(cardinality(b), 0);
  k INT;
BEGIN
  FOR k IN 1..least(la, lb) LOOP
    IF a[k] IS DISTINCT FROM b[k] THEN RETURN k - 1; END IF;
  END LOOP;
  RETURN least(la, lb);
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- qbx_ir.jones_ledger.certificate_problems.
CREATE OR REPLACE FUNCTION braid_jones_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  b RECORD;
  v RECORD;
BEGIN
  SELECT * INTO c FROM braid_jones WHERE id = p_id;
  IF NOT FOUND THEN RETURN; END IF;
  IF NOT braid_is_well_formed(c.braid_id) THEN
    reason := 'braid_not_well_formed'; details := '{}'::jsonb; RETURN NEXT; RETURN;
  END IF;
  SELECT * INTO b FROM braid_word WHERE id = c.braid_id;
  IF b.strand_count > braid_jones_max_strands() THEN
    reason := 'strand_count_too_large';
    details := jsonb_build_object('strand_count', b.strand_count,
                                  'max', braid_jones_max_strands());
    RETURN NEXT; RETURN;
  END IF;
  IF c.braid_hash IS DISTINCT FROM b.braid_hash THEN
    reason := 'braid_hash_mismatch';
    details := jsonb_build_object('recorded', c.braid_hash, 'expected', b.braid_hash);
    RETURN NEXT;
  END IF;
  SELECT * INTO v FROM braid_jones_values(b.strand_count, b.word);
  IF c.bracket_exp_min IS DISTINCT FROM v.bracket_exp_min
     OR c.bracket_width IS DISTINCT FROM v.bracket_width THEN
    reason := 'bracket_window_mismatch';
    details := jsonb_build_object(
      'recorded', jsonb_build_array(c.bracket_exp_min, c.bracket_width),
      'expected', jsonb_build_array(v.bracket_exp_min, v.bracket_width));
    RETURN NEXT;
  END IF;
  IF coalesce(cardinality(c.bracket_coefficients), 0)
       <> coalesce(cardinality(v.bracket_coefficients), 0)
     OR c.bracket_coefficients IS DISTINCT FROM v.bracket_coefficients THEN
    reason := 'bracket_coefficients_mismatch';
    details := jsonb_build_object(
      'recorded_length', coalesce(cardinality(c.bracket_coefficients), 0),
      'expected_length', coalesce(cardinality(v.bracket_coefficients), 0),
      'first_index', braid_jones_first_difference(c.bracket_coefficients,
                                                  v.bracket_coefficients));
    RETURN NEXT;
  END IF;
  IF c.jones_exp_min IS DISTINCT FROM v.jones_exp_min
     OR c.jones_width IS DISTINCT FROM v.jones_width THEN
    reason := 'jones_window_mismatch';
    details := jsonb_build_object(
      'recorded', jsonb_build_array(c.jones_exp_min, c.jones_width),
      'expected', jsonb_build_array(v.jones_exp_min, v.jones_width));
    RETURN NEXT;
  END IF;
  IF coalesce(cardinality(c.jones_coefficients), 0)
       <> coalesce(cardinality(v.jones_coefficients), 0)
     OR c.jones_coefficients IS DISTINCT FROM v.jones_coefficients THEN
    reason := 'jones_coefficients_mismatch';
    details := jsonb_build_object(
      'recorded_length', coalesce(cardinality(c.jones_coefficients), 0),
      'expected_length', coalesce(cardinality(v.jones_coefficients), 0),
      'first_index', braid_jones_first_difference(c.jones_coefficients,
                                                  v.jones_coefficients));
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- The certificate of a braid, if it has one without problems.
CREATE OR REPLACE FUNCTION braid_valid_jones(p_braid UUID) RETURNS UUID AS $$
  SELECT c.id FROM braid_jones c
   WHERE c.braid_id = p_braid
     AND NOT EXISTS (SELECT 1 FROM braid_jones_problems(c.id))
$$ LANGUAGE sql;

-- qbx_ir.jones_ledger.bracket_equal: NULL unless both braids have valid
-- certificates and the same strand count; TRUE iff the brackets are equal
-- (Lean: bracketCert_eq_iff).  FALSE: the braids are different and not
-- conjugate in B_n (Lean: bracketCert_eq_of_eval_eq, bracketPoly_conj).
CREATE OR REPLACE FUNCTION braid_bracket_equal(p_a UUID, p_b UUID) RETURNS BOOLEAN AS $$
DECLARE
  ia UUID;
  ib UUID;
  ca RECORD;
  cb RECORD;
BEGIN
  ia := braid_valid_jones(p_a);
  IF ia IS NULL THEN RETURN NULL; END IF;
  ib := braid_valid_jones(p_b);
  IF ib IS NULL THEN RETURN NULL; END IF;
  IF (SELECT strand_count FROM braid_word WHERE id = p_a)
     IS DISTINCT FROM (SELECT strand_count FROM braid_word WHERE id = p_b) THEN
    RETURN NULL;
  END IF;
  SELECT * INTO ca FROM braid_jones WHERE id = ia;
  SELECT * INTO cb FROM braid_jones WHERE id = ib;
  RETURN ca.bracket_exp_min = cb.bracket_exp_min AND ca.bracket_width = cb.bracket_width
         AND ca.bracket_coefficients = cb.bracket_coefficients;
END;
$$ LANGUAGE plpgsql;

-- qbx_ir.jones_ledger.jones_equal: NULL unless both braids have valid
-- certificates (strand counts may differ); TRUE iff the Jones polynomials are
-- equal.  FALSE: the closures are not isotopic (Lean:
-- not_markovEquiv_of_jonesCert_ne).
CREATE OR REPLACE FUNCTION braid_jones_equal(p_a UUID, p_b UUID) RETURNS BOOLEAN AS $$
DECLARE
  ia UUID;
  ib UUID;
  ca RECORD;
  cb RECORD;
BEGIN
  ia := braid_valid_jones(p_a);
  IF ia IS NULL THEN RETURN NULL; END IF;
  ib := braid_valid_jones(p_b);
  IF ib IS NULL THEN RETURN NULL; END IF;
  SELECT * INTO ca FROM braid_jones WHERE id = ia;
  SELECT * INTO cb FROM braid_jones WHERE id = ib;
  RETURN ca.jones_exp_min = cb.jones_exp_min AND ca.jones_width = cb.jones_width
         AND ca.jones_coefficients = cb.jones_coefficients;
END;
$$ LANGUAGE plpgsql;

-- True iff the two braids (same strand count) have valid certificates with
-- different brackets: they are not conjugate in B_n.  FALSE means "not
-- certified", not "conjugate".
CREATE OR REPLACE FUNCTION braid_bracket_non_conjugacy_certified(p_a UUID, p_b UUID)
RETURNS BOOLEAN AS $$
  SELECT braid_bracket_equal(p_a, p_b) IS FALSE
$$ LANGUAGE sql;

-- True iff the two braids have valid certificates with different Jones
-- polynomials: their closures are not isotopic.
CREATE OR REPLACE FUNCTION braid_jones_non_isotopy_certified(p_a UUID, p_b UUID)
RETURNS BOOLEAN AS $$
  SELECT braid_jones_equal(p_a, p_b) IS FALSE
$$ LANGUAGE sql;

-- qbx_ir.jones_ledger.transport_problems between two braids.
CREATE OR REPLACE FUNCTION braid_jones_transport_between(p_a UUID, p_b UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF braid_bracket_equal(p_a, p_b) IS FALSE THEN
    reason := 'bracket_not_preserved'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
  IF braid_jones_equal(p_a, p_b) IS FALSE THEN
    reason := 'jones_not_preserved'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- The transport check for a rewrite record.
CREATE OR REPLACE FUNCTION braid_rewrite_jones_transport_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT * INTO r FROM braid_rewrite WHERE id = p_id;
  IF NOT FOUND OR NOT braid_rewrite_is_valid(p_id) THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM braid_jones_transport_between(r.input_braid_id, r.output_braid_id);
END;
$$ LANGUAGE plpgsql;

-- The transport check for a derivation.
CREATE OR REPLACE FUNCTION braid_derivation_jones_transport_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  d RECORD;
BEGIN
  SELECT * INTO d FROM braid_derivation WHERE id = p_id;
  IF NOT FOUND OR EXISTS (SELECT 1 FROM braid_derivation_problems(p_id)) THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM braid_jones_transport_between(d.source_braid_id, d.target_braid_id);
END;
$$ LANGUAGE plpgsql;

-- qbx_ir.jones_ledger.nf_consistency_problems: other braids certified equal by
-- their normal forms (migration 021) must not have a different valid
-- certificate.
CREATE OR REPLACE FUNCTION braid_jones_nf_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  o RECORD;
BEGIN
  SELECT * INTO c FROM braid_jones WHERE id = p_id;
  IF NOT FOUND OR EXISTS (SELECT 1 FROM braid_jones_problems(p_id)) THEN RETURN; END IF;
  FOR o IN SELECT oc.braid_id, ob.braid_hash
             FROM braid_jones oc JOIN braid_word ob ON ob.id = oc.braid_id
             JOIN braid_normal_form onf ON onf.braid_id = oc.braid_id
             JOIN braid_normal_form cnf ON cnf.braid_id = c.braid_id
            WHERE oc.braid_id <> c.braid_id
              AND onf.power = cnf.power AND to_jsonb(onf.factors) = to_jsonb(cnf.factors)
            ORDER BY ob.braid_hash, oc.seq LOOP
    IF NOT braid_nf_equality_certified(c.braid_id, o.braid_id) THEN CONTINUE; END IF;
    IF braid_bracket_equal(c.braid_id, o.braid_id) IS FALSE
       OR braid_jones_equal(c.braid_id, o.braid_id) IS FALSE THEN
      reason := 'jones_contradicts_normal_form';
      details := jsonb_build_object('other_braid_hash', o.braid_hash);
      RETURN NEXT;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION braid_jones_problems_of(p_table TEXT, p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  CASE p_table
    WHEN 'braid_jones' THEN
      RETURN QUERY SELECT * FROM braid_jones_problems(p_id);
      RETURN QUERY SELECT * FROM braid_jones_nf_problems(p_id);
    WHEN 'braid_rewrite' THEN RETURN QUERY SELECT * FROM braid_rewrite_jones_transport_problems(p_id);
    WHEN 'braid_derivation' THEN RETURN QUERY SELECT * FROM braid_derivation_jones_transport_problems(p_id);
  END CASE;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_jones_record(p_table TEXT, p_id UUID, p_reason TEXT,
                                              p_details JSONB)
RETURNS VOID AS $$
BEGIN
  PERFORM qbx_record_violation('braid_jones', p_reason,
                               coalesce(p_details, '{}'::jsonb) || jsonb_build_object('table', p_table),
                               p_id);
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_jones_check_row(p_table TEXT, p_id UUID) RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM braid_jones_problems_of(p_table, p_id) LOOP
    PERFORM braid_jones_record(p_table, p_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- Every certificate (with the normal-form consistency check), then the
-- transport check on every rewrite and derivation.  Returns the number of
-- problems found.
CREATE OR REPLACE FUNCTION check_braid_jones() RETURNS INT AS $$
DECLARE
  t RECORD;
  n INT := 0;
BEGIN
  FOR t IN SELECT 1 AS o0, 'braid_jones' AS tb, id, created_at AS o1, seq AS o2
             FROM braid_jones
           UNION ALL SELECT 2, 'braid_rewrite', id, created_at, seq FROM braid_rewrite
           UNION ALL SELECT 3, 'braid_derivation', id, created_at, seq FROM braid_derivation
           ORDER BY 1, 4, 5 LOOP
    n := n + braid_jones_check_row(t.tb, t.id);
  END LOOP;
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Braid Jones certificates have problems (% problem(s))', n;
  END IF;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- The frozen Phase 2 batch checks (run_phase2_batch_checks, migration 022)
-- followed by the Phase 3 ones.  Migration 024 redefines this function with
-- the same body; check_braid_burau() is called only when it exists.
CREATE OR REPLACE FUNCTION run_phase3_batch_checks() RETURNS VOID AS $$
BEGIN
  PERFORM run_phase2_batch_checks();
  IF to_regprocedure('check_braid_burau()') IS NOT NULL THEN
    EXECUTE 'SELECT check_braid_burau()';
  END IF;
  PERFORM check_braid_jones();
  RAISE NOTICE 'run_phase3_batch_checks: complete';
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_braid_jones_row() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM braid_jones_problems(NEW.id) LOOP
    PERFORM braid_jones_record('braid_jones', NEW.id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'braid_jones row % is not valid (% problem(s))', NEW.id, n;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_braid_jones_row ON braid_jones;
CREATE TRIGGER trg_check_braid_jones_row AFTER INSERT ON braid_jones
FOR EACH ROW EXECUTE FUNCTION trg_check_braid_jones_row();

-- Certificates are append-only: an UPDATE, DELETE or TRUNCATE is logged (and
-- refused in strict mode).
CREATE OR REPLACE FUNCTION trg_braid_jones_append_only() RETURNS trigger AS $$
BEGIN
  PERFORM braid_jones_record(TG_TABLE_NAME, CASE WHEN TG_LEVEL = 'ROW' THEN OLD.id END,
                             'log_mutation', jsonb_build_object('op', TG_OP));
  IF functor_is_strict() THEN
    RAISE EXCEPTION '% on % refused: Jones certificates are append-only', TG_OP, TG_TABLE_NAME;
  END IF;
  IF TG_OP = 'DELETE' THEN RETURN OLD; END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_braid_jones_append_only ON braid_jones;
CREATE TRIGGER trg_braid_jones_append_only BEFORE UPDATE OR DELETE ON braid_jones
FOR EACH ROW EXECUTE FUNCTION trg_braid_jones_append_only();
DROP TRIGGER IF EXISTS trg_braid_jones_append_only_truncate ON braid_jones;
CREATE TRIGGER trg_braid_jones_append_only_truncate BEFORE TRUNCATE ON braid_jones
FOR EACH STATEMENT EXECUTE FUNCTION trg_braid_jones_append_only();

-- ---------------------------------------------------------------------------
-- Writer
-- ---------------------------------------------------------------------------

-- Compute and store the certificate of a registered braid; returns its id (the
-- existing one if the braid already has a certificate).
CREATE OR REPLACE FUNCTION certify_braid_jones(p_braid UUID) RETURNS UUID AS $$
DECLARE
  b RECORD;
  v RECORD;
  c_id UUID;
BEGIN
  SELECT * INTO b FROM braid_word WHERE id = p_braid;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'certify_braid_jones: unknown braid %', p_braid;
  END IF;
  IF NOT braid_is_well_formed(p_braid) THEN
    RAISE EXCEPTION 'certify_braid_jones: braid_not_well_formed (%)', p_braid;
  END IF;
  IF b.strand_count > braid_jones_max_strands() THEN
    RAISE EXCEPTION 'certify_braid_jones: strand_count_too_large (%)', b.strand_count;
  END IF;
  SELECT id INTO c_id FROM braid_jones WHERE braid_id = p_braid;
  IF c_id IS NOT NULL THEN
    RETURN c_id;
  END IF;
  SELECT * INTO v FROM braid_jones_values(b.strand_count, b.word);
  INSERT INTO braid_jones (braid_id, braid_hash, bracket_exp_min, bracket_width,
                           bracket_coefficients, jones_exp_min, jones_width,
                           jones_coefficients)
  VALUES (p_braid, b.braid_hash, v.bracket_exp_min, v.bracket_width,
          v.bracket_coefficients, v.jones_exp_min, v.jones_width, v.jones_coefficients)
  RETURNING id INTO c_id;
  RETURN c_id;
END;
$$ LANGUAGE plpgsql;
