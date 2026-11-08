-- ============================================================================
-- Categorical Ledger — Migration 024: Reduced Burau / Alexander Certificates
-- (Phase 3 item 3; closes D2-005)
-- ============================================================================
-- Stores, for a braid of the braid ledger (migration 019), the SYMBOLIC
-- reduced Burau matrix ρ̄(B) ∈ GL_{n-1}(Z[t, t⁻¹]) of
-- qbx_ir.algebra.polynomial_invariants.burau_matrix (generators multiplied in
-- word order) and the Alexander polynomial of the closure of
-- qbx_ir.algebra.polynomial_invariants.alexander_polynomial, recomputed by the
-- database from the word with integer arithmetic only:
--
--   braid_burau    one certificate per braid:
--                    size          n - 1;
--                    exp_min,      the smallest common exponent window of the
--                    width         entries: every non-zero coefficient has
--                                  exponent in [exp_min, exp_min + width), some
--                                  entry has a non-zero coefficient at exp_min
--                                  and some at exp_min + width - 1
--                                  (exp_min = width = 0 for n = 1);
--                    coefficients  size² · width integers: the coefficient of
--                                  t^(exp_min + k) in entry (i, j), 0-indexed,
--                                  at index (i · size + j) · width + k
--                                  (0-based);
--                    alexander     the Alexander polynomial normalised up to
--                                  ±t^k (lowest degree 0, lowest coefficient
--                                  positive), as c_0, c_1, …; empty when it is
--                                  0 (split closures);
--                    braid_hash    the hash of the certified braid.
--                  Append-only.  Strand counts above 12 are refused.
--
-- Computation: the reduced Burau generator of σ_i is the identity except for
-- row r = i - 1, which is (t, -t, 1) in columns r-1, r, r+1 (σ_i⁻¹:
-- (1, -t⁻¹, t⁻¹)), entries outside the matrix dropped; U := U · G letter by
-- letter.  The Alexander polynomial is det(I - ρ̄(B)) / (1 + t + … + t^{n-1}),
-- computed by fraction-free (Bareiss) elimination over Z[t] after a shift by a
-- power of t, then normalised (the shift and the sign of row exchanges are
-- units, removed by the normalisation).
--
-- Uses of the certificates:
--   * braid_burau_equal(a, b): TRUE iff ρ̄(a) = ρ̄(b) (representation equality;
--     the reduced Burau representation is not faithful for n ≥ 5, so this is
--     NOT equality in B_n); FALSE: the braids are different elements of B_n;
--     NULL: not comparable;
--   * braid_burau_inequality_certified: the FALSE case;
--   * braid_alexander_equal(a, b): FALSE: the braids are not conjugate in B_n
--     (det(I - ρ̄) is a conjugacy invariant); braid_burau_non_conjugacy_certified
--     is that case;
--   * transport: along every accepted rewrite and derivation the matrix and
--     the Alexander polynomial must agree (batch tier);
--   * consistency with migration 021: braids certified equal by their normal
--     forms must not have different certificates (batch tier).
--
-- D2-005: v_braid_exact_representations lists the certificates of both exact
-- representations (migration 022, kind 'sl2_quantum', and this migration,
-- kind 'reduced_burau') with a representation-kind column.  Frozen migration
-- 022 is not changed.
--
-- Reference implementation: qbx_ir.burau_ledger (same problems, same order,
-- same details).  Lean: QBX/Formal/BurauRep.lean — the generator matrices
-- satisfy the braid relations for every n (burauRep,
-- Word.burau_eq_of_eval_eq); the characteristic polynomial and det(I - ρ̄) are
-- conjugacy invariants (Word.burau_charpoly_conj, Word.alexNum_conj).
-- QBX/Formal/BraidBurauCert.lean — the encoding is unique, so certificates are
-- equal iff the matrices are (burauCert_eq_iff); equal braids have equal
-- certificates (burauCert_eq_of_eval_eq, alexCert_eq_of_eval_eq); different
-- certificates prove different braids (eval_ne_of_burauCert_ne) and different
-- Alexander polynomials prove non-conjugate braids
-- (not_isConj_of_alexCert_ne); the Lean model gives exactly the Python values
-- on test vectors (burau_agrees_with_python); registry H-063, H-064.
--
-- Problems are logged to invariant_violation (migration 017) with module
-- 'braid_burau', object_id the row and details.table its table.
-- run_phase3_batch_checks() runs run_phase2_batch_checks() (frozen, 022),
-- check_braid_burau() and, when migration 023 is installed, check_braid_jones().
--
-- Write-time tier: every inserted certificate is checked (logged; raised in
-- strict mode).  The writer certify_braid_burau refuses a braid that is not
-- well formed and a strand count above 12.
-- ============================================================================

CREATE TABLE IF NOT EXISTS braid_burau (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  seq BIGSERIAL,
  braid_id UUID NOT NULL REFERENCES braid_word(id) ON DELETE CASCADE,
  braid_hash TEXT NOT NULL,
  size INT NOT NULL,
  exp_min INT NOT NULL,
  width INT NOT NULL,
  coefficients NUMERIC[] NOT NULL DEFAULT '{}',
  alexander NUMERIC[] NOT NULL DEFAULT '{}',
  created_at TIMESTAMPTZ DEFAULT now(),
  UNIQUE (braid_id)
);

-- ---------------------------------------------------------------------------
-- Recomputation (qbx_ir.burau_ledger.burau_values)
-- ---------------------------------------------------------------------------

-- Largest strand count accepted (qbx_ir.burau_ledger.MAX_BURAU_STRANDS).
CREATE OR REPLACE FUNCTION braid_burau_max_strands() RETURNS INT AS $$
  SELECT 12
$$ LANGUAGE sql IMMUTABLE;

-- Polynomials over Z in t, as NUMERIC[] with a[d + 1] the coefficient of t^d,
-- padded with zeros to a fixed length.  Degree (-1 for 0).
CREATE OR REPLACE FUNCTION braid_burau_poly_deg(a NUMERIC[]) RETURNS INT AS $$
DECLARE
  d INT;
BEGIN
  FOR d IN REVERSE coalesce(cardinality(a), 0)..1 LOOP
    IF a[d] <> 0 THEN RETURN d - 1; END IF;
  END LOOP;
  RETURN -1;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- a · b, truncated to length s (callers guarantee the degree fits).
CREATE OR REPLACE FUNCTION braid_burau_poly_mul(a NUMERIC[], b NUMERIC[], s INT)
RETURNS NUMERIC[] AS $$
DECLARE
  c NUMERIC[] := array_fill(0::numeric, ARRAY[s]);
  da INT := braid_burau_poly_deg(a);
  db INT := braid_burau_poly_deg(b);
  i INT;
  j INT;
BEGIN
  FOR i IN 0..da LOOP
    IF a[i + 1] <> 0 THEN
      FOR j IN 0..db LOOP
        IF b[j + 1] <> 0 THEN
          IF i + j >= s THEN
            RAISE EXCEPTION 'braid_burau_poly_mul: degree overflow';
          END IF;
          c[i + j + 1] := c[i + j + 1] + a[i + 1] * b[j + 1];
        END IF;
      END LOOP;
    END IF;
  END LOOP;
  RETURN c;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- a - b (same length).
CREATE OR REPLACE FUNCTION braid_burau_poly_sub(a NUMERIC[], b NUMERIC[]) RETURNS NUMERIC[] AS $$
  SELECT ARRAY(SELECT x - y FROM unnest(a, b) WITH ORDINALITY AS z(x, y, o) ORDER BY o)
$$ LANGUAGE sql IMMUTABLE;

-- The exact quotient a / b in Z[t] (raises if b does not divide a).
CREATE OR REPLACE FUNCTION braid_burau_poly_divexact(a NUMERIC[], b NUMERIC[], s INT)
RETURNS NUMERIC[] AS $$
DECLARE
  q NUMERIC[] := array_fill(0::numeric, ARRAY[s]);
  r NUMERIC[] := a;
  da INT := braid_burau_poly_deg(a);
  db INT := braid_burau_poly_deg(b);
  j INT;
  i INT;
  c NUMERIC;
BEGIN
  IF db < 0 THEN RAISE EXCEPTION 'braid_burau_poly_divexact: division by zero'; END IF;
  IF da < 0 THEN RETURN q; END IF;
  IF da < db THEN RAISE EXCEPTION 'braid_burau_poly_divexact: not divisible'; END IF;
  FOR j IN REVERSE da - db..0 LOOP
    IF mod(r[j + db + 1], b[db + 1]) <> 0 THEN
      RAISE EXCEPTION 'braid_burau_poly_divexact: not divisible';
    END IF;
    c := div(r[j + db + 1], b[db + 1]);
    q[j + 1] := c;
    IF c <> 0 THEN
      FOR i IN 0..db LOOP
        r[j + i + 1] := r[j + i + 1] - c * b[i + 1];
      END LOOP;
    END IF;
  END LOOP;
  IF braid_burau_poly_deg(r) >= 0 THEN
    RAISE EXCEPTION 'braid_burau_poly_divexact: not divisible';
  END IF;
  RETURN q;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- The certificate fields of a well-formed braid with 1..12 strands; one row.
CREATE OR REPLACE FUNCTION braid_burau_values(p_n INT, p_word INT[])
RETURNS TABLE(size INT, exp_min INT, width INT, coefficients NUMERIC[], alexander NUMERIC[]) AS $$
DECLARE
  len INT := coalesce(cardinality(p_word), 0);
  m INT := p_n - 1;
  w INT := 2 * coalesce(cardinality(p_word), 0) + 1;   -- exponent window [-len, len]
  off INT := coalesce(cardinality(p_word), 0);
  u NUMERIC[];
  c NUMERIC[];
  k INT;
  r INT;
  x INT;
  y INT;
  e INT;
  pos BOOLEAN;
  base INT;
  lo INT;
  hi INT;
  out_c NUMERIC[] := '{}';
  -- Alexander
  sh INT;
  s INT;
  mat NUMERIC[];
  prev NUMERIC[];
  piv NUMERIC[];
  aik NUMERIC[];
  akj NUMERIC[];
  aij NUMERIC[];
  tmp NUMERIC[];
  i INT;
  j INT;
  kk INT;
  rr INT;
  d NUMERIC[];
  phi NUMERIC[];
  q NUMERIC[];
  dq INT;
  low INT;
BEGIN
  size := m;
  IF m = 0 THEN
    exp_min := 0; width := 0; coefficients := '{}'; alexander := ARRAY[1]::numeric[];
    RETURN NEXT; RETURN;
  END IF;
  -- U = identity; entry (x, y) exponent e stored at (x*m + y)*w + (e + off) + 1.
  u := array_fill(0::numeric, ARRAY[m * m * w]);
  FOR x IN 0..m - 1 LOOP
    u[(x * m + x) * w + off + 1] := 1;
  END LOOP;
  FOR k IN 1..len LOOP
    r := abs(p_word[k]) - 1;
    pos := p_word[k] > 0;
    FOR x IN 0..m - 1 LOOP
      base := (x * m + r) * w;
      c := u[base + 1 : base + w];
      -- column r: -t·c (σ) or -t⁻¹·c (σ⁻¹)
      FOR e IN 1..w LOOP
        u[base + e] := 0;
      END LOOP;
      FOR e IN 1..w LOOP
        IF c[e] <> 0 THEN
          IF pos THEN u[base + e + 1] := u[base + e + 1] - c[e];
          ELSE u[base + e - 1] := u[base + e - 1] - c[e]; END IF;
        END IF;
      END LOOP;
      -- column r-1: + t·c (σ) or + c (σ⁻¹)
      IF r - 1 >= 0 THEN
        base := (x * m + r - 1) * w;
        FOR e IN 1..w LOOP
          IF c[e] <> 0 THEN
            IF pos THEN u[base + e + 1] := u[base + e + 1] + c[e];
            ELSE u[base + e] := u[base + e] + c[e]; END IF;
          END IF;
        END LOOP;
      END IF;
      -- column r+1: + c (σ) or + t⁻¹·c (σ⁻¹)
      IF r + 1 < m THEN
        base := (x * m + r + 1) * w;
        FOR e IN 1..w LOOP
          IF c[e] <> 0 THEN
            IF pos THEN u[base + e] := u[base + e] + c[e];
            ELSE u[base + e - 1] := u[base + e - 1] + c[e]; END IF;
          END IF;
        END LOOP;
      END IF;
    END LOOP;
  END LOOP;
  -- The smallest common window.
  lo := NULL; hi := NULL;
  FOR x IN 0..m * m - 1 LOOP
    FOR e IN 0..w - 1 LOOP
      IF u[x * w + e + 1] <> 0 THEN
        IF lo IS NULL OR e < lo THEN lo := e; END IF;
        IF hi IS NULL OR e > hi THEN hi := e; END IF;
      END IF;
    END LOOP;
  END LOOP;
  exp_min := lo - off;
  width := hi - lo + 1;
  FOR x IN 0..m * m - 1 LOOP
    out_c := out_c || u[x * w + lo + 1 : x * w + hi + 1];
  END LOOP;
  coefficients := out_c;
  -- Alexander: P = t^sh (I - U), entries polynomials of degree ≤ D = sh + max(hi - off, 0);
  -- Bareiss entries at step k are minors of degree ≤ (k + 2) D, and the products formed
  -- before the exact division have degree ≤ 2 (k + 1) D, so length 2 m D + 1 suffices.
  sh := greatest(0, -(lo - off));
  s := 2 * m * (sh + greatest(hi - off, 0)) + 1;
  mat := array_fill(0::numeric, ARRAY[m * m * s]);
  FOR x IN 0..m - 1 LOOP
    FOR y IN 0..m - 1 LOOP
      FOR e IN lo..hi LOOP
        IF u[(x * m + y) * w + e + 1] <> 0 THEN
          mat[(x * m + y) * s + (e - off + sh) + 1] := -u[(x * m + y) * w + e + 1];
        END IF;
      END LOOP;
      IF x = y THEN
        mat[(x * m + y) * s + sh + 1] := mat[(x * m + y) * s + sh + 1] + 1;
      END IF;
    END LOOP;
  END LOOP;
  -- Bareiss elimination (up to sign).
  prev := array_fill(0::numeric, ARRAY[s]);
  prev[1] := 1;
  d := NULL;
  FOR kk IN 0..m - 2 LOOP
    piv := mat[(kk * m + kk) * s + 1 : (kk * m + kk) * s + s];
    IF braid_burau_poly_deg(piv) < 0 THEN
      rr := NULL;
      FOR i IN kk + 1..m - 1 LOOP
        IF braid_burau_poly_deg(mat[(i * m + kk) * s + 1 : (i * m + kk) * s + s]) >= 0 THEN
          rr := i; EXIT;
        END IF;
      END LOOP;
      IF rr IS NULL THEN
        d := array_fill(0::numeric, ARRAY[s]);
        EXIT;
      END IF;
      FOR j IN 0..m - 1 LOOP
        tmp := mat[(kk * m + j) * s + 1 : (kk * m + j) * s + s];
        mat[(kk * m + j) * s + 1 : (kk * m + j) * s + s] :=
          mat[(rr * m + j) * s + 1 : (rr * m + j) * s + s];
        mat[(rr * m + j) * s + 1 : (rr * m + j) * s + s] := tmp;
      END LOOP;
      piv := mat[(kk * m + kk) * s + 1 : (kk * m + kk) * s + s];
    END IF;
    FOR i IN kk + 1..m - 1 LOOP
      aik := mat[(i * m + kk) * s + 1 : (i * m + kk) * s + s];
      FOR j IN kk + 1..m - 1 LOOP
        akj := mat[(kk * m + j) * s + 1 : (kk * m + j) * s + s];
        aij := mat[(i * m + j) * s + 1 : (i * m + j) * s + s];
        tmp := braid_burau_poly_sub(braid_burau_poly_mul(aij, piv, s),
                                    braid_burau_poly_mul(aik, akj, s));
        mat[(i * m + j) * s + 1 : (i * m + j) * s + s] := braid_burau_poly_divexact(tmp, prev, s);
      END LOOP;
    END LOOP;
    prev := piv;
  END LOOP;
  IF d IS NULL THEN
    d := mat[((m - 1) * m + m - 1) * s + 1 : ((m - 1) * m + m - 1) * s + s];
  END IF;
  IF braid_burau_poly_deg(d) < 0 THEN
    alexander := '{}';
    RETURN NEXT; RETURN;
  END IF;
  -- Divide by 1 + t + … + t^{n-1}, then normalise.
  phi := array_fill(0::numeric, ARRAY[s]);
  FOR i IN 1..least(p_n, s) LOOP phi[i] := 1; END LOOP;
  q := braid_burau_poly_divexact(d, phi, s);
  dq := braid_burau_poly_deg(q);
  low := 0;
  WHILE q[low + 1] = 0 LOOP low := low + 1; END LOOP;
  IF q[low + 1] < 0 THEN
    alexander := ARRAY(SELECT -q[z] FROM generate_series(low + 1, dq + 1) AS z ORDER BY z);
  ELSE
    alexander := ARRAY(SELECT q[z] FROM generate_series(low + 1, dq + 1) AS z ORDER BY z);
  END IF;
  RETURN NEXT;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Problems (qbx_ir.burau_ledger)
-- ---------------------------------------------------------------------------

-- qbx_ir.burau_ledger.certificate_problems.
CREATE OR REPLACE FUNCTION braid_burau_problems(p_id UUID)
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
  SELECT * INTO c FROM braid_burau WHERE id = p_id;
  IF NOT FOUND THEN RETURN; END IF;
  IF NOT braid_is_well_formed(c.braid_id) THEN
    reason := 'braid_not_well_formed'; details := '{}'::jsonb; RETURN NEXT; RETURN;
  END IF;
  SELECT * INTO b FROM braid_word WHERE id = c.braid_id;
  IF b.strand_count > braid_burau_max_strands() THEN
    reason := 'strand_count_too_large';
    details := jsonb_build_object('strand_count', b.strand_count,
                                  'max', braid_burau_max_strands());
    RETURN NEXT; RETURN;
  END IF;
  IF c.braid_hash IS DISTINCT FROM b.braid_hash THEN
    reason := 'braid_hash_mismatch';
    details := jsonb_build_object('recorded', c.braid_hash, 'expected', b.braid_hash);
    RETURN NEXT;
  END IF;
  SELECT * INTO v FROM braid_burau_values(b.strand_count, b.word);
  IF c.size IS DISTINCT FROM v.size THEN
    reason := 'size_mismatch';
    details := jsonb_build_object('recorded', c.size, 'expected', v.size);
    RETURN NEXT;
  END IF;
  IF c.exp_min IS DISTINCT FROM v.exp_min OR c.width IS DISTINCT FROM v.width THEN
    reason := 'window_mismatch';
    details := jsonb_build_object('recorded', jsonb_build_array(c.exp_min, c.width),
                                  'expected', jsonb_build_array(v.exp_min, v.width));
    RETURN NEXT;
  END IF;
  rl := coalesce(cardinality(c.coefficients), 0);
  el := coalesce(cardinality(v.coefficients), 0);
  IF rl <> el OR c.coefficients IS DISTINCT FROM v.coefficients THEN
    first_k := least(rl, el);
    FOR k IN 1..least(rl, el) LOOP
      IF c.coefficients[k] IS DISTINCT FROM v.coefficients[k] THEN
        first_k := k - 1;
        EXIT;
      END IF;
    END LOOP;
    reason := 'coefficients_mismatch';
    details := jsonb_build_object('recorded_length', rl, 'expected_length', el,
                                  'first_index', first_k);
    RETURN NEXT;
  END IF;
  IF coalesce(cardinality(c.alexander), 0) <> coalesce(cardinality(v.alexander), 0)
     OR c.alexander IS DISTINCT FROM v.alexander THEN
    reason := 'alexander_mismatch';
    details := jsonb_build_object(
      'recorded', coalesce((SELECT jsonb_agg(x::text ORDER BY o)
                              FROM unnest(c.alexander) WITH ORDINALITY AS z(x, o)), '[]'::jsonb),
      'expected', coalesce((SELECT jsonb_agg(x::text ORDER BY o)
                              FROM unnest(v.alexander) WITH ORDINALITY AS z(x, o)), '[]'::jsonb));
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- The certificate of a braid, if it has one without problems.
CREATE OR REPLACE FUNCTION braid_valid_burau(p_braid UUID) RETURNS UUID AS $$
  SELECT c.id FROM braid_burau c
   WHERE c.braid_id = p_braid
     AND NOT EXISTS (SELECT 1 FROM braid_burau_problems(c.id))
$$ LANGUAGE sql;

-- qbx_ir.burau_ledger.burau_equal: NULL unless both braids have valid
-- certificates and the same strand count; TRUE iff the Burau matrices are
-- equal (Lean: burauCert_eq_iff) — representation equality, not equality in
-- B_n; FALSE certifies that the braids are different (Lean:
-- eval_ne_of_burauCert_ne).
CREATE OR REPLACE FUNCTION braid_burau_equal(p_a UUID, p_b UUID) RETURNS BOOLEAN AS $$
DECLARE
  ia UUID;
  ib UUID;
  ca RECORD;
  cb RECORD;
BEGIN
  ia := braid_valid_burau(p_a);
  IF ia IS NULL THEN RETURN NULL; END IF;
  ib := braid_valid_burau(p_b);
  IF ib IS NULL THEN RETURN NULL; END IF;
  IF (SELECT strand_count FROM braid_word WHERE id = p_a)
     IS DISTINCT FROM (SELECT strand_count FROM braid_word WHERE id = p_b) THEN
    RETURN NULL;
  END IF;
  SELECT * INTO ca FROM braid_burau WHERE id = ia;
  SELECT * INTO cb FROM braid_burau WHERE id = ib;
  RETURN ca.exp_min = cb.exp_min AND ca.width = cb.width
         AND ca.coefficients = cb.coefficients;
END;
$$ LANGUAGE plpgsql;

-- qbx_ir.burau_ledger.alexander_equal: NULL unless comparable; TRUE iff the
-- Alexander polynomials agree.  FALSE certifies that the braids are not
-- conjugate in B_n (Lean: not_isConj_of_alexCert_ne).
CREATE OR REPLACE FUNCTION braid_alexander_equal(p_a UUID, p_b UUID) RETURNS BOOLEAN AS $$
DECLARE
  ia UUID;
  ib UUID;
BEGIN
  ia := braid_valid_burau(p_a);
  IF ia IS NULL THEN RETURN NULL; END IF;
  ib := braid_valid_burau(p_b);
  IF ib IS NULL THEN RETURN NULL; END IF;
  IF (SELECT strand_count FROM braid_word WHERE id = p_a)
     IS DISTINCT FROM (SELECT strand_count FROM braid_word WHERE id = p_b) THEN
    RETURN NULL;
  END IF;
  RETURN (SELECT alexander FROM braid_burau WHERE id = ia)
         = (SELECT alexander FROM braid_burau WHERE id = ib);
END;
$$ LANGUAGE plpgsql;

-- True iff the two braids have valid certificates that differ: they are
-- different elements of B_n.  FALSE means "not certified", not "equal".
CREATE OR REPLACE FUNCTION braid_burau_inequality_certified(p_a UUID, p_b UUID)
RETURNS BOOLEAN AS $$
  SELECT braid_burau_equal(p_a, p_b) IS FALSE
$$ LANGUAGE sql;

-- True iff the two braids have valid certificates with different Alexander
-- polynomials: they are not conjugate in B_n.
CREATE OR REPLACE FUNCTION braid_burau_non_conjugacy_certified(p_a UUID, p_b UUID)
RETURNS BOOLEAN AS $$
  SELECT braid_alexander_equal(p_a, p_b) IS FALSE
$$ LANGUAGE sql;

-- qbx_ir.burau_ledger.transport_problems between two braids.
CREATE OR REPLACE FUNCTION braid_burau_transport_between(p_a UUID, p_b UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF braid_burau_equal(p_a, p_b) IS FALSE THEN
    reason := 'burau_not_preserved'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
  IF braid_alexander_equal(p_a, p_b) IS FALSE THEN
    reason := 'alexander_not_preserved'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- The transport check for a rewrite record.
CREATE OR REPLACE FUNCTION braid_rewrite_burau_transport_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT * INTO r FROM braid_rewrite WHERE id = p_id;
  IF NOT FOUND OR NOT braid_rewrite_is_valid(p_id) THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM braid_burau_transport_between(r.input_braid_id, r.output_braid_id);
END;
$$ LANGUAGE plpgsql;

-- The transport check for a derivation.
CREATE OR REPLACE FUNCTION braid_derivation_burau_transport_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  d RECORD;
BEGIN
  SELECT * INTO d FROM braid_derivation WHERE id = p_id;
  IF NOT FOUND OR EXISTS (SELECT 1 FROM braid_derivation_problems(p_id)) THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM braid_burau_transport_between(d.source_braid_id, d.target_braid_id);
END;
$$ LANGUAGE plpgsql;

-- qbx_ir.burau_ledger.nf_consistency_problems: other braids certified equal by
-- their normal forms (migration 021) must not have a different valid
-- certificate.
CREATE OR REPLACE FUNCTION braid_burau_nf_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  o RECORD;
BEGIN
  SELECT * INTO c FROM braid_burau WHERE id = p_id;
  IF NOT FOUND OR EXISTS (SELECT 1 FROM braid_burau_problems(p_id)) THEN RETURN; END IF;
  FOR o IN SELECT oc.braid_id, ob.braid_hash
             FROM braid_burau oc JOIN braid_word ob ON ob.id = oc.braid_id
             JOIN braid_normal_form onf ON onf.braid_id = oc.braid_id
             JOIN braid_normal_form cnf ON cnf.braid_id = c.braid_id
            WHERE oc.braid_id <> c.braid_id
              AND onf.power = cnf.power AND to_jsonb(onf.factors) = to_jsonb(cnf.factors)
            ORDER BY ob.braid_hash, oc.seq LOOP
    IF NOT braid_nf_equality_certified(c.braid_id, o.braid_id) THEN CONTINUE; END IF;
    IF braid_burau_equal(c.braid_id, o.braid_id) IS FALSE
       OR braid_alexander_equal(c.braid_id, o.braid_id) IS FALSE THEN
      reason := 'burau_contradicts_normal_form';
      details := jsonb_build_object('other_braid_hash', o.braid_hash);
      RETURN NEXT;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION braid_burau_problems_of(p_table TEXT, p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  CASE p_table
    WHEN 'braid_burau' THEN
      RETURN QUERY SELECT * FROM braid_burau_problems(p_id);
      RETURN QUERY SELECT * FROM braid_burau_nf_problems(p_id);
    WHEN 'braid_rewrite' THEN RETURN QUERY SELECT * FROM braid_rewrite_burau_transport_problems(p_id);
    WHEN 'braid_derivation' THEN RETURN QUERY SELECT * FROM braid_derivation_burau_transport_problems(p_id);
  END CASE;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_burau_record(p_table TEXT, p_id UUID, p_reason TEXT,
                                              p_details JSONB)
RETURNS VOID AS $$
BEGIN
  PERFORM qbx_record_violation('braid_burau', p_reason,
                               coalesce(p_details, '{}'::jsonb) || jsonb_build_object('table', p_table),
                               p_id);
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_burau_check_row(p_table TEXT, p_id UUID) RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM braid_burau_problems_of(p_table, p_id) LOOP
    PERFORM braid_burau_record(p_table, p_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- Every certificate (with the normal-form consistency check), then the
-- transport check on every rewrite and derivation.  Returns the number of
-- problems found.
CREATE OR REPLACE FUNCTION check_braid_burau() RETURNS INT AS $$
DECLARE
  t RECORD;
  n INT := 0;
BEGIN
  FOR t IN SELECT 1 AS o0, 'braid_burau' AS tb, id, created_at AS o1, seq AS o2
             FROM braid_burau
           UNION ALL SELECT 2, 'braid_rewrite', id, created_at, seq FROM braid_rewrite
           UNION ALL SELECT 3, 'braid_derivation', id, created_at, seq FROM braid_derivation
           ORDER BY 1, 4, 5 LOOP
    n := n + braid_burau_check_row(t.tb, t.id);
  END LOOP;
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Braid Burau certificates have problems (% problem(s))', n;
  END IF;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- The frozen Phase 2 batch checks (run_phase2_batch_checks, migration 022)
-- followed by the Phase 3 ones.  Migration 023 defines the same function;
-- check_braid_jones() (023) is called only when it exists, so the result does
-- not depend on the order in which 023 and 024 were applied.
CREATE OR REPLACE FUNCTION run_phase3_batch_checks() RETURNS VOID AS $$
BEGIN
  PERFORM run_phase2_batch_checks();
  PERFORM check_braid_burau();
  IF to_regprocedure('check_braid_jones()') IS NOT NULL THEN
    EXECUTE 'SELECT check_braid_jones()';
  END IF;
  RAISE NOTICE 'run_phase3_batch_checks: complete';
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_braid_burau_row() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM braid_burau_problems(NEW.id) LOOP
    PERFORM braid_burau_record('braid_burau', NEW.id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'braid_burau row % is not valid (% problem(s))', NEW.id, n;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_braid_burau_row ON braid_burau;
CREATE TRIGGER trg_check_braid_burau_row AFTER INSERT ON braid_burau
FOR EACH ROW EXECUTE FUNCTION trg_check_braid_burau_row();

-- Certificates are append-only: an UPDATE, DELETE or TRUNCATE is logged (and
-- refused in strict mode).
CREATE OR REPLACE FUNCTION trg_braid_burau_append_only() RETURNS trigger AS $$
BEGIN
  PERFORM braid_burau_record(TG_TABLE_NAME, CASE WHEN TG_LEVEL = 'ROW' THEN OLD.id END,
                             'log_mutation', jsonb_build_object('op', TG_OP));
  IF functor_is_strict() THEN
    RAISE EXCEPTION '% on % refused: Burau certificates are append-only', TG_OP, TG_TABLE_NAME;
  END IF;
  IF TG_OP = 'DELETE' THEN RETURN OLD; END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_braid_burau_append_only ON braid_burau;
CREATE TRIGGER trg_braid_burau_append_only BEFORE UPDATE OR DELETE ON braid_burau
FOR EACH ROW EXECUTE FUNCTION trg_braid_burau_append_only();
DROP TRIGGER IF EXISTS trg_braid_burau_append_only_truncate ON braid_burau;
CREATE TRIGGER trg_braid_burau_append_only_truncate BEFORE TRUNCATE ON braid_burau
FOR EACH STATEMENT EXECUTE FUNCTION trg_braid_burau_append_only();

-- ---------------------------------------------------------------------------
-- Writer
-- ---------------------------------------------------------------------------

-- Compute and store the certificate of a registered braid; returns its id (the
-- existing one if the braid already has a certificate).
CREATE OR REPLACE FUNCTION certify_braid_burau(p_braid UUID) RETURNS UUID AS $$
DECLARE
  b RECORD;
  v RECORD;
  c_id UUID;
BEGIN
  SELECT * INTO b FROM braid_word WHERE id = p_braid;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'certify_braid_burau: unknown braid %', p_braid;
  END IF;
  IF NOT braid_is_well_formed(p_braid) THEN
    RAISE EXCEPTION 'certify_braid_burau: braid_not_well_formed (%)', p_braid;
  END IF;
  IF b.strand_count > braid_burau_max_strands() THEN
    RAISE EXCEPTION 'certify_braid_burau: strand_count_too_large (%)', b.strand_count;
  END IF;
  SELECT id INTO c_id FROM braid_burau WHERE braid_id = p_braid;
  IF c_id IS NOT NULL THEN
    RETURN c_id;
  END IF;
  SELECT * INTO v FROM braid_burau_values(b.strand_count, b.word);
  INSERT INTO braid_burau (braid_id, braid_hash, size, exp_min, width, coefficients, alexander)
  VALUES (p_braid, b.braid_hash, v.size, v.exp_min, v.width, v.coefficients, v.alexander)
  RETURNING id INTO c_id;
  RETURN c_id;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- D2-005: both exact representations, with a representation-kind column
-- ---------------------------------------------------------------------------
CREATE OR REPLACE VIEW v_braid_exact_representations AS
  SELECT 'sl2_quantum'::text AS kind, r.id AS certificate_id, r.braid_id, r.braid_hash,
         jsonb_build_object('q_num', r.q_num, 'q_den', r.q_den) AS parameter,
         r.created_at
    FROM braid_representation r
  UNION ALL
  SELECT 'reduced_burau'::text, c.id, c.braid_id, c.braid_hash, NULL::jsonb, c.created_at
    FROM braid_burau c;
