-- ============================================================================
-- Categorical Ledger — Migration 021: Garside Normal-Form Certificates
-- (Phase 2 sprint 3)
-- ============================================================================
-- Stores, for a braid of the braid ledger (migration 019), its Garside left
-- normal form  Δ^power · A_1 ⋯ A_k, recomputed by the database from the word
-- with the algorithm of qbx_ir.algebra.garside.left_normal_form_from_short:
--
--   braid_normal_form  one certificate per braid:
--                        power        the exponent of Δ;
--                        factors      the simple factors A_1 … A_k, one row
--                                     per factor, as 0-indexed permutations
--                                     (factors[j][k+1] = final position of the
--                                     strand that starts at position k);
--                        normal_word  the short form of the normal form
--                                     (GarsideNormalForm.to_short_form);
--                        braid_hash   the hash of the certified braid.
--                      Append-only.
--
-- Uses of the certificates:
--   * braid_normal_form_equal(a, b): TRUE when two braids with the same strand
--     count have the same valid normal form — a certificate that they are
--     EQUAL in B_n (proved in Lean); FALSE when the normal forms differ, which
--     means "different" only by Garside's uniqueness theorem (registry H-057,
--     provisional; formalized only for at most two strands); NULL when a
--     valid certificate is missing
--     or the strand counts differ.  braid_nf_equality_certified(a, b) is the
--     proved TRUE case only.
--   * transport (batch tier): along every accepted rewrite and derivation
--     whose two ends have valid certificates, the normal forms must agree
--     (relies on H-057; a failure would refute it or reveal a bug);
--   * consistency with migration 020 (batch tier): two braids with the same
--     valid normal form must not have different valid invariant certificates
--     (relies only on proved results).
--
-- Reference implementation: qbx_ir.normal_form_ledger (same problems, same
-- order, same details).  Lean: QBX/Formal/BraidNormalForm.lean — leftNormalForm
-- models this algorithm step for step and is proved sound: the normal form
-- stands for the braid of the word (nfValue_leftNormalForm), so equal normal
-- forms prove equal braids (eval_eq_of_leftNormalForm_eq) and equal invariant
-- certificates (cert_eq_of_leftNormalForm_eq); registry H-054 – H-056.
--
-- Problems are logged to invariant_violation (migration 017) with module
-- 'braid_normal_forms', object_id the row and details.table its table.
-- run_phase2_batch_checks() (redefined here) runs run_all_batch_checks(),
-- check_braid_ledger(), check_braid_invariants() and
-- check_braid_normal_forms().
--
-- Write-time tier: every inserted certificate is checked (logged; raised in
-- strict mode).  The writer certify_braid_normal_form refuses a braid that is
-- not well formed.
-- ============================================================================

CREATE TABLE IF NOT EXISTS braid_normal_form (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  seq BIGSERIAL,
  braid_id UUID NOT NULL UNIQUE REFERENCES braid_word(id) ON DELETE CASCADE,
  braid_hash TEXT NOT NULL,
  power INT NOT NULL,
  factors INT[] NOT NULL DEFAULT '{}',
  normal_word INT[] NOT NULL DEFAULT '{}',
  created_at TIMESTAMPTZ DEFAULT now()
);

-- ---------------------------------------------------------------------------
-- Permutation helpers (qbx_ir.algebra.garside).  A permutation of n strands is
-- an INT[] of length n holding 0-based values; p[k+1] = final position of the
-- strand that starts at position k.
-- ---------------------------------------------------------------------------

-- i (1-indexed) is in the starting set S(p): p[i-1] > p[i] (0-based).
CREATE OR REPLACE FUNCTION nf_starts_with(p INT[], i INT) RETURNS BOOLEAN AS $$
  SELECT p[i] > p[i + 1]
$$ LANGUAGE sql IMMUTABLE;

-- i (1-indexed) is in the finishing set F(p): the inverse has a descent at i.
CREATE OR REPLACE FUNCTION nf_finishes_with(p INT[], i INT) RETURNS BOOLEAN AS $$
  SELECT array_position(p, i - 1) > array_position(p, i)
$$ LANGUAGE sql IMMUTABLE;

-- simple_word: a positive word for the permutation braid of p.
CREATE OR REPLACE FUNCTION nf_simple_word(p_perm INT[]) RETURNS INT[] AS $$
DECLARE
  p INT[] := p_perm;
  n INT := coalesce(cardinality(p_perm), 0);
  w INT[] := '{}';
  i INT;
  t INT;
  found BOOLEAN;
BEGIN
  LOOP
    found := FALSE;
    FOR i IN 1..n - 1 LOOP
      IF p[i] > p[i + 1] THEN
        w := w || i;
        -- A = σ_i · A'  ⇒  p' = p ∘ s_i: swap the entries at positions i-1, i.
        t := p[i]; p[i] := p[i + 1]; p[i + 1] := t;
        found := TRUE;
        EXIT;
      END IF;
    END LOOP;
    EXIT WHEN NOT found;
  END LOOP;
  RETURN w;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- The left normal form (qbx_ir.normal_form_ledger.normal_form_values)
-- ---------------------------------------------------------------------------

-- The certificate fields of a well-formed braid (strand count >= 1, every
-- letter in ±1..±(n-1)); one row.  The factor list is kept flat (factor j is
-- f[(j-1)*n+1 .. j*n]) and returned as a two-dimensional array.
CREATE OR REPLACE FUNCTION braid_normal_form_values(p_n INT, p_word INT[])
RETURNS TABLE(power INT, factors INT[], normal_word INT[]) AS $$
DECLARE
  n INT := p_n;
  len INT := coalesce(cardinality(p_word), 0);
  pw INT := 0;
  f INT[] := '{}';
  g INT[];
  m INT;
  k INT;
  j INT;
  i INT;
  q INT;
  x INT;
  t INT;
  a INT[];
  b INT[];
  ident INT[];
  delta INT[];
  changed BOOLEAN;
  moved BOOLEAN;
  dw INT[];
  inv INT[];
  w INT[] := '{}';
BEGIN
  ident := ARRAY(SELECT generate_series(0, n - 1));
  delta := ARRAY(SELECT generate_series(n - 1, 0, -1));
  -- Read the word.
  FOR k IN 1..len LOOP
    x := p_word[k];
    i := abs(x);
    IF x > 0 THEN
      a := ident;
      a[i] := i; a[i + 1] := i - 1;
      f := f || a;
    ELSE
      -- σ_i⁻¹ = X_i · Δ⁻¹ with X_i = Δ ∘ s_i; push Δ⁻¹ to the front: every factor
      -- is conjugated by Δ (tau), then tau(X_i) is appended.
      m := coalesce(cardinality(f), 0) / greatest(n, 1);
      g := '{}';
      FOR j IN 1..m LOOP
        FOR q IN 0..n - 1 LOOP
          g := g || (n - 1 - f[(j - 1) * n + (n - 1 - q) + 1]);
        END LOOP;
      END LOOP;
      a := ident;
      a[i] := i; a[i + 1] := i - 1;           -- s_i
      b := ARRAY(SELECT n - 1 - a[z + 1] FROM generate_series(0, n - 1) AS gs(z) ORDER BY z);  -- X_i
      FOR q IN 0..n - 1 LOOP                  -- tau(X_i)
        g := g || (n - 1 - b[(n - 1 - q) + 1]);
      END LOOP;
      f := g;
      pw := pw - 1;
    END IF;
  END LOOP;
  -- Drop identity factors.
  m := coalesce(cardinality(f), 0) / greatest(n, 1);
  g := '{}';
  FOR j IN 1..m LOOP
    IF f[(j - 1) * n + 1 : j * n] IS DISTINCT FROM ident THEN
      g := g || f[(j - 1) * n + 1 : j * n];
    END IF;
  END LOOP;
  f := g;
  m := coalesce(cardinality(f), 0) / greatest(n, 1);
  -- Make left-weighted (_make_left_weighted).
  changed := TRUE;
  WHILE changed LOOP
    changed := FALSE;
    FOR j IN 1..m - 1 LOOP
      a := f[(j - 1) * n + 1 : j * n];
      b := f[j * n + 1 : (j + 1) * n];
      LOOP
        moved := FALSE;
        FOR i IN 1..n - 1 LOOP
          IF nf_starts_with(b, i) AND NOT nf_finishes_with(a, i) THEN
            -- A ← A·σ_i (values i-1, i exchanged); B ← σ_i⁻¹·B (entries swapped).
            FOR q IN 1..n LOOP
              IF a[q] = i - 1 THEN a[q] := i; ELSIF a[q] = i THEN a[q] := i - 1; END IF;
            END LOOP;
            t := b[i]; b[i] := b[i + 1]; b[i + 1] := t;
            changed := TRUE;
            moved := TRUE;
            EXIT;
          END IF;
        END LOOP;
        EXIT WHEN NOT moved;
      END LOOP;
      f := f[1 : (j - 1) * n] || a || b || f[(j + 1) * n + 1 : m * n];
    END LOOP;
  END LOOP;
  -- Absorb leading Δ's; drop trailing identities.
  WHILE m > 0 AND f[1 : n] = delta LOOP
    f := f[n + 1 : m * n];
    m := m - 1;
    pw := pw + 1;
  END LOOP;
  WHILE m > 0 AND f[(m - 1) * n + 1 : m * n] = ident LOOP
    f := f[1 : (m - 1) * n];
    m := m - 1;
  END LOOP;
  IF n = 1 THEN
    pw := 0;  -- B_1 is trivial; Δ_1 = 1
  END IF;
  -- The normal word (to_short_form).
  dw := nf_simple_word(delta);
  IF pw >= 0 THEN
    FOR k IN 1..pw LOOP w := w || dw; END LOOP;
  ELSE
    inv := ARRAY(SELECT -dw[z] FROM generate_series(coalesce(cardinality(dw), 0), 1, -1) AS gs(z)
                 ORDER BY z DESC);
    FOR k IN 1..-pw LOOP w := w || inv; END LOOP;
  END IF;
  FOR j IN 1..m LOOP
    w := w || nf_simple_word(f[(j - 1) * n + 1 : j * n]);
  END LOOP;
  power := pw;
  IF m = 0 THEN
    factors := '{}'::int[];
  ELSE
    factors := ARRAY(SELECT ARRAY(SELECT f[(y - 1) * n + z] FROM generate_series(1, n) AS gz(z) ORDER BY z)
                       FROM generate_series(1, m) AS gy(y) ORDER BY y);
  END IF;
  normal_word := w;
  RETURN NEXT;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Problems (qbx_ir.normal_form_ledger)
-- ---------------------------------------------------------------------------

-- qbx_ir.normal_form_ledger.certificate_problems.
CREATE OR REPLACE FUNCTION braid_normal_form_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  b RECORD;
  v RECORD;
BEGIN
  SELECT * INTO c FROM braid_normal_form WHERE id = p_id;
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
  SELECT * INTO v FROM braid_normal_form_values(b.strand_count, b.word);
  IF c.power IS DISTINCT FROM v.power THEN
    reason := 'power_mismatch';
    details := jsonb_build_object('recorded', c.power, 'expected', v.power);
    RETURN NEXT;
  END IF;
  IF to_jsonb(c.factors) IS DISTINCT FROM to_jsonb(v.factors) THEN
    reason := 'factors_mismatch';
    details := jsonb_build_object('recorded', to_jsonb(c.factors), 'expected', to_jsonb(v.factors));
    RETURN NEXT;
  END IF;
  IF c.normal_word IS DISTINCT FROM v.normal_word THEN
    reason := 'normal_word_mismatch';
    details := jsonb_build_object('recorded', to_jsonb(c.normal_word), 'expected', to_jsonb(v.normal_word));
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- The normal-form certificate of a braid, if it has one without problems.
CREATE OR REPLACE FUNCTION braid_valid_normal_form(p_braid UUID) RETURNS UUID AS $$
  SELECT c.id FROM braid_normal_form c
   WHERE c.braid_id = p_braid
     AND NOT EXISTS (SELECT 1 FROM braid_normal_form_problems(c.id))
$$ LANGUAGE sql;

-- qbx_ir.normal_form_ledger.normal_forms_equal: NULL unless both braids have
-- valid certificates and the same strand count; TRUE iff power and factors
-- coincide.  TRUE certifies equality in B_n (Lean:
-- eval_eq_of_leftNormalForm_eq); FALSE means different only under Garside's
-- uniqueness theorem (H-057, provisional).
CREATE OR REPLACE FUNCTION braid_normal_form_equal(p_a UUID, p_b UUID) RETURNS BOOLEAN AS $$
DECLARE
  ca RECORD;
  cb RECORD;
BEGIN
  SELECT * INTO ca FROM braid_normal_form WHERE id = braid_valid_normal_form(p_a);
  IF NOT FOUND THEN RETURN NULL; END IF;
  SELECT * INTO cb FROM braid_normal_form WHERE id = braid_valid_normal_form(p_b);
  IF NOT FOUND THEN RETURN NULL; END IF;
  IF (SELECT strand_count FROM braid_word WHERE id = p_a)
     IS DISTINCT FROM (SELECT strand_count FROM braid_word WHERE id = p_b) THEN
    RETURN NULL;
  END IF;
  RETURN ca.power = cb.power AND to_jsonb(ca.factors) = to_jsonb(cb.factors);
END;
$$ LANGUAGE plpgsql;

-- The proved direction only: TRUE iff the two braids are certified equal.
CREATE OR REPLACE FUNCTION braid_nf_equality_certified(p_a UUID, p_b UUID) RETURNS BOOLEAN AS $$
  SELECT coalesce(braid_normal_form_equal(p_a, p_b), FALSE)
$$ LANGUAGE sql;

-- qbx_ir.normal_form_ledger.transport_problems for a rewrite record.
CREATE OR REPLACE FUNCTION braid_rewrite_nf_transport_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT * INTO r FROM braid_rewrite WHERE id = p_id;
  IF NOT FOUND OR NOT braid_rewrite_is_valid(p_id) THEN RETURN; END IF;
  IF braid_normal_form_equal(r.input_braid_id, r.output_braid_id) IS FALSE THEN
    reason := 'normal_form_not_preserved'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- qbx_ir.normal_form_ledger.transport_problems for a derivation.
CREATE OR REPLACE FUNCTION braid_derivation_nf_transport_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  d RECORD;
BEGIN
  SELECT * INTO d FROM braid_derivation WHERE id = p_id;
  IF NOT FOUND OR EXISTS (SELECT 1 FROM braid_derivation_problems(p_id)) THEN RETURN; END IF;
  IF braid_normal_form_equal(d.source_braid_id, d.target_braid_id) IS FALSE THEN
    reason := 'normal_form_not_preserved'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- qbx_ir.normal_form_ledger.invariant_consistency_problems: other braids with
-- the same valid normal form must not have different valid invariant
-- certificates (Lean: cert_eq_of_leftNormalForm_eq).
CREATE OR REPLACE FUNCTION braid_nf_invariant_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  o RECORD;
  diff TEXT[];
BEGIN
  SELECT * INTO c FROM braid_normal_form WHERE id = p_id;
  IF NOT FOUND OR EXISTS (SELECT 1 FROM braid_normal_form_problems(p_id)) THEN RETURN; END IF;
  FOR o IN SELECT oc.braid_id, ob.braid_hash
             FROM braid_normal_form oc JOIN braid_word ob ON ob.id = oc.braid_id
            WHERE oc.braid_id <> c.braid_id
              AND oc.power = c.power
              AND to_jsonb(oc.factors) = to_jsonb(c.factors)
            ORDER BY ob.braid_hash, oc.seq LOOP
    IF braid_normal_form_equal(c.braid_id, o.braid_id) IS NOT TRUE THEN CONTINUE; END IF;
    diff := braid_invariant_differences(c.braid_id, o.braid_id);
    IF coalesce(cardinality(diff), 0) > 0 THEN
      reason := 'invariants_contradict_normal_form';
      details := jsonb_build_object('other_braid_hash', o.braid_hash, 'invariants', to_jsonb(diff));
      RETURN NEXT;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION braid_normal_forms_problems_of(p_table TEXT, p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  CASE p_table
    WHEN 'braid_normal_form' THEN
      RETURN QUERY SELECT * FROM braid_normal_form_problems(p_id);
      RETURN QUERY SELECT * FROM braid_nf_invariant_problems(p_id);
    WHEN 'braid_rewrite' THEN RETURN QUERY SELECT * FROM braid_rewrite_nf_transport_problems(p_id);
    WHEN 'braid_derivation' THEN RETURN QUERY SELECT * FROM braid_derivation_nf_transport_problems(p_id);
  END CASE;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_normal_forms_record(p_table TEXT, p_id UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  PERFORM qbx_record_violation('braid_normal_forms', p_reason,
                               coalesce(p_details, '{}'::jsonb) || jsonb_build_object('table', p_table),
                               p_id);
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION braid_normal_forms_check_row(p_table TEXT, p_id UUID) RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM braid_normal_forms_problems_of(p_table, p_id) LOOP
    PERFORM braid_normal_forms_record(p_table, p_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- Every certificate (its own problems, then the consistency with the
-- invariant certificates), then the transport check on every rewrite and
-- derivation.  Returns the number of problems found.
CREATE OR REPLACE FUNCTION check_braid_normal_forms() RETURNS INT AS $$
DECLARE
  t RECORD;
  n INT := 0;
BEGIN
  FOR t IN SELECT 1 AS o0, 'braid_normal_form' AS tb, id, created_at AS o1, seq AS o2 FROM braid_normal_form
           UNION ALL SELECT 2, 'braid_rewrite', id, created_at, seq FROM braid_rewrite
           UNION ALL SELECT 3, 'braid_derivation', id, created_at, seq FROM braid_derivation
           ORDER BY 1, 4, 5 LOOP
    n := n + braid_normal_forms_check_row(t.tb, t.id);
  END LOOP;
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Braid normal-form certificates have problems (% problem(s))', n;
  END IF;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- Phase 1 batch checks (frozen migration 017) followed by the Phase 2 ones
-- (replaces the definition of migration 020).
CREATE OR REPLACE FUNCTION run_phase2_batch_checks() RETURNS VOID AS $$
BEGIN
  PERFORM run_all_batch_checks();
  PERFORM check_braid_ledger();
  PERFORM check_braid_invariants();
  PERFORM check_braid_normal_forms();
  RAISE NOTICE 'run_phase2_batch_checks: complete';
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier: the certificate's own problems (the consistency and
-- transport checks are batch tier).
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION trg_check_braid_normal_form_row() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM braid_normal_form_problems(NEW.id) LOOP
    PERFORM braid_normal_forms_record('braid_normal_form', NEW.id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  IF n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'braid_normal_form row % is not valid (% problem(s))', NEW.id, n;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_braid_normal_form_row ON braid_normal_form;
CREATE TRIGGER trg_check_braid_normal_form_row AFTER INSERT ON braid_normal_form
FOR EACH ROW EXECUTE FUNCTION trg_check_braid_normal_form_row();

-- Certificates are append-only: an UPDATE, DELETE or TRUNCATE is logged (and
-- refused in strict mode).
CREATE OR REPLACE FUNCTION trg_braid_normal_form_append_only() RETURNS trigger AS $$
BEGIN
  PERFORM braid_normal_forms_record(TG_TABLE_NAME, CASE WHEN TG_LEVEL = 'ROW' THEN OLD.id END,
                                    'log_mutation', jsonb_build_object('op', TG_OP));
  IF functor_is_strict() THEN
    RAISE EXCEPTION '% on % refused: normal-form certificates are append-only', TG_OP, TG_TABLE_NAME;
  END IF;
  IF TG_OP = 'DELETE' THEN RETURN OLD; END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_braid_normal_form_append_only ON braid_normal_form;
CREATE TRIGGER trg_braid_normal_form_append_only BEFORE UPDATE OR DELETE ON braid_normal_form
FOR EACH ROW EXECUTE FUNCTION trg_braid_normal_form_append_only();
DROP TRIGGER IF EXISTS trg_braid_normal_form_append_only_truncate ON braid_normal_form;
CREATE TRIGGER trg_braid_normal_form_append_only_truncate BEFORE TRUNCATE ON braid_normal_form
FOR EACH STATEMENT EXECUTE FUNCTION trg_braid_normal_form_append_only();

-- ---------------------------------------------------------------------------
-- Writer
-- ---------------------------------------------------------------------------

-- Compute and store the normal-form certificate of a registered braid; returns
-- its id (the existing one if the braid already has a certificate).
CREATE OR REPLACE FUNCTION certify_braid_normal_form(p_braid UUID) RETURNS UUID AS $$
DECLARE
  b RECORD;
  v RECORD;
  c_id UUID;
BEGIN
  SELECT * INTO b FROM braid_word WHERE id = p_braid;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'certify_braid_normal_form: unknown braid %', p_braid;
  END IF;
  IF NOT braid_is_well_formed(p_braid) THEN
    RAISE EXCEPTION 'certify_braid_normal_form: braid_not_well_formed (%)', p_braid;
  END IF;
  SELECT id INTO c_id FROM braid_normal_form WHERE braid_id = p_braid;
  IF c_id IS NOT NULL THEN
    RETURN c_id;
  END IF;
  SELECT * INTO v FROM braid_normal_form_values(b.strand_count, b.word);
  INSERT INTO braid_normal_form (braid_id, braid_hash, power, factors, normal_word)
  VALUES (p_braid, b.braid_hash, v.power, v.factors, v.normal_word)
  RETURNING id INTO c_id;
  RETURN c_id;
END;
$$ LANGUAGE plpgsql;
