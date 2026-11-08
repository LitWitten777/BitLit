-- ============================================================================
-- Categorical Ledger — Migration 008: Enriched Categories
-- ============================================================================
-- An enriched category records, over the objects of a base category, one
-- hom-value per ordered pair of objects (enriched_hom).  Two families of
-- enrichment are supported.
--
-- 1. Quantale enrichment (kinds 'metric', 'ordered', 'quantale').  The base V
--    is a commutative monoid (⊗, unit) with a compatible order ≤_V, and the
--    recorded values h(x, y) ∈ V form a V-category iff
--      unit law:         unit ≤_V h(x, x)                 for every object x
--      composition law:  h(x, y) ⊗ h(y, z) ≤_V h(x, z)    for all objects x, y, z
--    (Formal/Enriched.lean: exists_enriched_iff — in a thin V nothing else needs
--    checking; neither law implies the other: unit_law_not_sufficient,
--    composition_law_not_sufficient).  A *missing* hom is the bottom of V
--    (distance ∞, truth value 0), so the check is exact over every object of
--    the base category, not just the recorded ones.  Bottom absorbs ⊗, so the
--    composition law only needs the triples whose first two homs are recorded
--    (triangle_iff_finite).
--
--    quantale      carrier    ≤_V   ⊗     unit  missing  value key
--    lawvere       [0, ∞]     ≥     +     0     ∞        distance | value
--    ultrametric   [0, ∞]     ≥     max   0     ∞        distance | value
--    boolean       {0, 1}     ≤     min   1     0        holds | value
--    goedel        [0, 1]     ≤     min   1     0        value
--    product       [0, 1]     ≤     ×     1     0        value
--
--    kind 'metric' = lawvere (Lawvere metric spaces: d(x, x) = 0 and the
--    triangle inequality; distances need not be symmetric and may be ∞,
--    written "Infinity"); kind 'ordered' = boolean (preorders: reflexive and
--    transitive); kind 'quantale' names one of the five in
--    metadata->>'quantale'.
--
-- 2. Probabilistic (kind 'probabilistic').  Each hom-value is a finite
--    stochastic kernel {"kernel": {"s": {"t": p, ...}, ...}} (row s of the
--    kernel from x to y; absent entries are 0).  The recorded kernels must be
--    consistent with a Markov process (a functor into finite stochastic
--    kernels), checked on the recorded data:
--      * every kernel is stochastic (entries ≥ 0, every row sums to 1);
--      * the kernels out of one object share one set of row states (its state
--        space), and a kernel into y puts mass only on states of y;
--      * a recorded h(x, x) is the identity kernel;
--      * Chapman–Kolmogorov: h(x, z) = h(x, y) ; h(y, z) whenever all three are
--        recorded, where (f ; g)(s, u) = Σ_t f(s, t) g(t, u).
--
-- Arithmetic is exact: JSON numbers are read as NUMERIC (decimal), so
-- 0.1 + 0.2 + 0.7 = 1 exactly.  enrichment_space.metadata->>'tolerance'
-- (a JSON number ≥ 0, default 0) relaxes every comparison by that amount.
--
-- Composition convention (migrations 001–007): an enriched_composition row
-- (left_hom_id = g : y → z, right_hom_id = f : x → y) records
-- composed_value = g ∘ f, f applied first: h(x, y) ⊗ h(y, z) for quantales,
-- f ; g for kernels.
--
-- Tiers: each hom (value well-formed and in range, endpoints in the base
-- category, kernel stochastic) and each enriched_composition row (typing,
-- composed value correct, composition law / Chapman–Kolmogorov for its
-- triple) are checked at write time; the unit and composition laws over all
-- objects are batch (check_enriched_category, run_all_batch_checks in 017),
-- as the architecture requires for the triangle inequality.  Every check logs
-- to enriched_violation and raises only when qbx.enforcement_mode = 'strict'.
--
-- Phase 1 sprint 5 rewrite.  Running the original on PostgreSQL 16 showed:
--   * check_metric_triangle_inequality reported lhs = d(X, Y) instead of
--     d(X, Z) (e.g. lhs 1, rhs 2 for d(X, Z) = 5);
--   * a missing d(X, Z) was silently accepted, although d(X, Y) and d(Y, Z)
--     finite force d(X, Z) finite;
--   * the unit law d(X, X) = 0 was never checked (d(X, X) = 7 passed), nor
--     were negative distances (-3 passed), NaN, or values without a
--     "distance" key (silently skipped by the NULL comparison);
--   * a hom could join objects outside the base category;
--   * enriched_composition accepted homs that do not compose (f ∘ f for
--     f : X → Y), from another enriched category, with any composed_value,
--     and let the writer set verified = TRUE;
--   * the enrichment kind was never consulted: the metric check ran on any
--     enriched category, and the 'ordered', 'quantale' and 'probabilistic'
--     kinds had no checks at all; nothing ran in run_all_batch_checks and no
--     violation was ever logged.
-- ============================================================================

CREATE TABLE IF NOT EXISTS enrichment_space (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  kind TEXT NOT NULL CHECK (kind IN ('metric','probabilistic','ordered','quantale')),
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now(),
  CONSTRAINT enrichment_space_quantale CHECK (
    kind <> 'quantale'
    OR coalesce(metadata->>'quantale', '') IN
         ('lawvere','ultrametric','boolean','goedel','product')),
  CONSTRAINT enrichment_space_tolerance CHECK (
    CASE
      WHEN metadata IS NULL OR NOT (metadata ? 'tolerance') THEN TRUE
      WHEN jsonb_typeof(metadata->'tolerance') <> 'number' THEN FALSE
      ELSE (metadata->>'tolerance')::numeric >= 0
    END)
);

CREATE TABLE IF NOT EXISTS enriched_category (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  base_category_id UUID NOT NULL REFERENCES category(id) ON DELETE CASCADE,
  enrichment_space_id UUID NOT NULL REFERENCES enrichment_space(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  UNIQUE (base_category_id, enrichment_space_id)
);

CREATE TABLE IF NOT EXISTS enriched_hom (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  enriched_category_id UUID NOT NULL REFERENCES enriched_category(id) ON DELETE CASCADE,
  source_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  target_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  value JSONB NOT NULL,
  last_updated TIMESTAMPTZ DEFAULT now(),
  metadata JSONB DEFAULT '{}'::jsonb,
  UNIQUE (enriched_category_id, source_object_id, target_object_id)
);

CREATE INDEX IF NOT EXISTS idx_enriched_hom_cat
  ON enriched_hom (enriched_category_id);

CREATE TABLE IF NOT EXISTS enriched_composition (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  enriched_category_id UUID NOT NULL REFERENCES enriched_category(id) ON DELETE CASCADE,
  left_hom_id UUID NOT NULL REFERENCES enriched_hom(id) ON DELETE CASCADE,
  right_hom_id UUID NOT NULL REFERENCES enriched_hom(id) ON DELETE CASCADE,
  composed_value JSONB NOT NULL,
  verified BOOLEAN DEFAULT FALSE,
  verified_at TIMESTAMPTZ,
  metadata JSONB DEFAULT '{}'::jsonb
);

-- ---------------------------------------------------------------------------
-- Violation log.  reason is one of
--   missing_enriched_category, foreign_object, malformed_value, out_of_range,
--   not_stochastic, unit_law, composition_law,
--   state_space, kernel_support, identity_kernel, chapman_kolmogorov,
--   composition_typing, composition_value
-- ---------------------------------------------------------------------------
CREATE TABLE IF NOT EXISTS enriched_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  enriched_category_id UUID,
  reason TEXT NOT NULL,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_enriched_violation_cat
  ON enriched_violation (enriched_category_id, detected_at DESC);

-- ---------------------------------------------------------------------------
-- The enrichment base of an enriched category
-- ---------------------------------------------------------------------------
-- Quantale name ('lawvere', ..., 'product'), or NULL for 'probabilistic'.
CREATE OR REPLACE FUNCTION enriched_quantale(p_ec UUID) RETURNS TEXT AS $$
  SELECT CASE s.kind
           WHEN 'metric'   THEN 'lawvere'
           WHEN 'ordered'  THEN 'boolean'
           WHEN 'quantale' THEN s.metadata->>'quantale'
         END
    FROM enriched_category e
    JOIN enrichment_space s ON s.id = e.enrichment_space_id
   WHERE e.id = p_ec;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION enriched_kind(p_ec UUID) RETURNS TEXT AS $$
  SELECT s.kind
    FROM enriched_category e
    JOIN enrichment_space s ON s.id = e.enrichment_space_id
   WHERE e.id = p_ec;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION enriched_tolerance(p_ec UUID) RETURNS NUMERIC AS $$
  SELECT coalesce((s.metadata->>'tolerance')::numeric, 0)
    FROM enriched_category e
    JOIN enrichment_space s ON s.id = e.enrichment_space_id
   WHERE e.id = p_ec;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Quantale operations (pure).  Values are NUMERIC; 'Infinity' is ∞.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION enriched_q_reversed(p_q TEXT) RETURNS BOOLEAN AS $$
  SELECT p_q IN ('lawvere', 'ultrametric');
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION enriched_q_unit(p_q TEXT) RETURNS NUMERIC AS $$
  SELECT CASE WHEN enriched_q_reversed(p_q) THEN 0::numeric ELSE 1::numeric END;
$$ LANGUAGE sql IMMUTABLE;

-- The value of a missing hom: the bottom of V.
CREATE OR REPLACE FUNCTION enriched_q_bottom(p_q TEXT) RETURNS NUMERIC AS $$
  SELECT CASE WHEN enriched_q_reversed(p_q) THEN 'Infinity'::numeric ELSE 0::numeric END;
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION enriched_q_tensor(p_q TEXT, a NUMERIC, b NUMERIC)
RETURNS NUMERIC AS $$
  SELECT CASE p_q
           WHEN 'lawvere'     THEN a + b
           WHEN 'ultrametric' THEN greatest(a, b)
           WHEN 'boolean'     THEN least(a, b)
           WHEN 'goedel'      THEN least(a, b)
           WHEN 'product'     THEN a * b
         END;
$$ LANGUAGE sql IMMUTABLE;

-- a ≤_V b, relaxed by p_tol.
CREATE OR REPLACE FUNCTION enriched_q_leq(p_q TEXT, a NUMERIC, b NUMERIC, p_tol NUMERIC)
RETURNS BOOLEAN AS $$
  SELECT CASE WHEN enriched_q_reversed(p_q) THEN a + p_tol >= b ELSE a <= b + p_tol END;
$$ LANGUAGE sql IMMUTABLE;

-- The hom-value as a NUMERIC, or NULL if it is malformed for this quantale.
CREATE OR REPLACE FUNCTION enriched_parse_value(p_q TEXT, p_value JSONB)
RETURNS NUMERIC AS $$
DECLARE
  j JSONB;
BEGIN
  IF p_value IS NULL OR jsonb_typeof(p_value) <> 'object' THEN
    RETURN NULL;
  END IF;
  IF p_q IN ('lawvere', 'ultrametric') THEN
    j := coalesce(p_value->'distance', p_value->'value');
  ELSIF p_q = 'boolean' THEN
    j := coalesce(p_value->'holds', p_value->'value');
  ELSE
    j := p_value->'value';
  END IF;
  IF j IS NULL THEN
    RETURN NULL;
  ELSIF jsonb_typeof(j) = 'number' THEN
    RETURN (j #>> '{}')::numeric;
  ELSIF jsonb_typeof(j) = 'boolean' AND p_q = 'boolean' THEN
    RETURN CASE WHEN (j #>> '{}')::boolean THEN 1 ELSE 0 END;
  ELSIF jsonb_typeof(j) = 'string' AND p_q IN ('lawvere', 'ultrametric')
        AND lower(j #>> '{}') IN ('infinity', 'inf') THEN
    RETURN 'Infinity'::numeric;
  END IF;
  RETURN NULL;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION enriched_in_range(p_q TEXT, v NUMERIC) RETURNS BOOLEAN AS $$
  SELECT CASE
           WHEN enriched_q_reversed(p_q) THEN v >= 0
           WHEN p_q = 'boolean' THEN v IN (0, 1)
           ELSE v >= 0 AND v <= 1
         END;
$$ LANGUAGE sql IMMUTABLE;

-- JSON form of a quantale value (∞ as the string "Infinity").
CREATE OR REPLACE FUNCTION enriched_q_json(v NUMERIC) RETURNS JSONB AS $$
  SELECT CASE WHEN v = 'Infinity'::numeric THEN to_jsonb('Infinity'::text) ELSE to_jsonb(v) END;
$$ LANGUAGE sql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Finite stochastic kernels (pure).  A kernel is a JSON object of rows, each
-- a JSON object of entries; absent entries are 0.
-- ---------------------------------------------------------------------------
-- The kernel of a hom-value, or NULL if it is not of the form
-- {"kernel": {row: {col: number ≥ 0, ...}, ...}} with at least one row.
CREATE OR REPLACE FUNCTION enriched_kernel(p_value JSONB) RETURNS JSONB AS $$
DECLARE
  k JSONB;
BEGIN
  IF p_value IS NULL OR jsonb_typeof(p_value) <> 'object' THEN
    RETURN NULL;
  END IF;
  k := p_value->'kernel';
  IF k IS NULL OR jsonb_typeof(k) <> 'object' OR k = '{}'::jsonb THEN
    RETURN NULL;
  END IF;
  IF EXISTS (SELECT 1 FROM jsonb_each(k) r WHERE jsonb_typeof(r.value) <> 'object') THEN
    RETURN NULL;
  END IF;
  IF EXISTS (SELECT 1 FROM jsonb_each(k) r, jsonb_each(r.value) e
              WHERE jsonb_typeof(e.value) <> 'number') THEN
    RETURN NULL;
  END IF;
  RETURN k;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- Rows of a (well-formed) kernel that are not probability distributions.
CREATE OR REPLACE FUNCTION enriched_kernel_bad_rows(p_k JSONB, p_tol NUMERIC)
RETURNS TEXT[] AS $$
  SELECT coalesce(array_agg(r.key ORDER BY r.key), ARRAY[]::text[])
    FROM jsonb_each(p_k) r
   WHERE EXISTS (SELECT 1 FROM jsonb_each(r.value) e WHERE (e.value #>> '{}')::numeric < 0)
      OR abs(coalesce((SELECT sum((e.value #>> '{}')::numeric) FROM jsonb_each(r.value) e), 0) - 1)
         > p_tol;
$$ LANGUAGE sql IMMUTABLE;

-- States carrying positive mass in kernel f that are not rows of kernel g.
CREATE OR REPLACE FUNCTION enriched_kernel_unsupported(p_f JSONB, p_g JSONB)
RETURNS TEXT[] AS $$
  SELECT coalesce(array_agg(DISTINCT e.key ORDER BY e.key), ARRAY[]::text[])
    FROM jsonb_each(p_f) r, jsonb_each(r.value) e
   WHERE (e.value #>> '{}')::numeric <> 0
     AND NOT (p_g ? e.key);
$$ LANGUAGE sql IMMUTABLE;

-- f ; g (f applied first): (f ; g)(s, u) = Σ_t f(s, t) g(t, u).
CREATE OR REPLACE FUNCTION enriched_compose_kernels(p_f JSONB, p_g JSONB)
RETURNS JSONB AS $$
  SELECT jsonb_object_agg(fr.key, coalesce((
           SELECT jsonb_object_agg(z.col, z.total)
             FROM (SELECT ge.key AS col,
                          sum((fe.value #>> '{}')::numeric * (ge.value #>> '{}')::numeric) AS total
                     FROM jsonb_each(fr.value) fe
                     JOIN jsonb_each(coalesce(p_g->fe.key, '{}'::jsonb)) ge ON TRUE
                    GROUP BY ge.key) z), '{}'::jsonb))
    FROM jsonb_each(p_f) fr;
$$ LANGUAGE sql IMMUTABLE;

-- Entrywise equality up to p_tol, absent entries = 0; the row sets must agree.
CREATE OR REPLACE FUNCTION enriched_kernels_equal(p_a JSONB, p_b JSONB, p_tol NUMERIC)
RETURNS BOOLEAN AS $$
  SELECT (SELECT coalesce(array_agg(k ORDER BY k), ARRAY[]::text[]) FROM jsonb_object_keys(p_a) k)
       = (SELECT coalesce(array_agg(k ORDER BY k), ARRAY[]::text[]) FROM jsonb_object_keys(p_b) k)
     AND NOT EXISTS (
       SELECT 1
         FROM jsonb_object_keys(p_a) r,
              LATERAL (SELECT jsonb_object_keys(p_a->r) AS c
                       UNION SELECT jsonb_object_keys(p_b->r)) cols
        WHERE abs(coalesce((p_a->r->>cols.c)::numeric, 0)
                  - coalesce((p_b->r->>cols.c)::numeric, 0)) > p_tol);
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION enriched_kernel_is_identity(p_k JSONB, p_tol NUMERIC)
RETURNS BOOLEAN AS $$
  SELECT enriched_kernels_equal(
           p_k,
           (SELECT jsonb_object_agg(k, jsonb_build_object(k, 1)) FROM jsonb_object_keys(p_k) k),
           p_tol);
$$ LANGUAGE sql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Problems of one hom (pure: no logging, no raising)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION enriched_hom_problems(p_hom UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  h RECORD;
  v_base UUID;
  v_kind TEXT;
  v_q TEXT;
  v_tol NUMERIC;
  v_num NUMERIC;
  v_k JSONB;
  v_bad TEXT[];
BEGIN
  SELECT eh.* INTO h FROM enriched_hom eh WHERE eh.id = p_hom;
  IF NOT FOUND THEN
    RETURN;
  END IF;
  SELECT e.base_category_id INTO v_base FROM enriched_category e WHERE e.id = h.enriched_category_id;
  v_kind := enriched_kind(h.enriched_category_id);
  v_q := enriched_quantale(h.enriched_category_id);
  v_tol := enriched_tolerance(h.enriched_category_id);

  IF NOT EXISTS (SELECT 1 FROM object o WHERE o.id = h.source_object_id AND o.category_id = v_base)
     OR NOT EXISTS (SELECT 1 FROM object o WHERE o.id = h.target_object_id AND o.category_id = v_base)
  THEN
    reason := 'foreign_object';
    details := jsonb_build_object('hom', h.id, 'source', h.source_object_id,
                                  'target', h.target_object_id, 'base_category', v_base);
    RETURN NEXT;
  END IF;

  IF v_kind = 'probabilistic' THEN
    v_k := enriched_kernel(h.value);
    IF v_k IS NULL THEN
      reason := 'malformed_value';
      details := jsonb_build_object('hom', h.id, 'source', h.source_object_id,
                                    'target', h.target_object_id, 'value', h.value);
      RETURN NEXT;
    ELSE
      v_bad := enriched_kernel_bad_rows(v_k, v_tol);
      IF cardinality(v_bad) > 0 THEN
        reason := 'not_stochastic';
        details := jsonb_build_object('hom', h.id, 'source', h.source_object_id,
                                      'target', h.target_object_id, 'rows', to_jsonb(v_bad));
        RETURN NEXT;
      END IF;
    END IF;
  ELSE
    v_num := enriched_parse_value(v_q, h.value);
    IF v_num IS NULL THEN
      reason := 'malformed_value';
      details := jsonb_build_object('hom', h.id, 'source', h.source_object_id,
                                    'target', h.target_object_id, 'quantale', v_q, 'value', h.value);
      RETURN NEXT;
    ELSIF NOT enriched_in_range(v_q, v_num) THEN
      reason := 'out_of_range';
      details := jsonb_build_object('hom', h.id, 'source', h.source_object_id,
                                    'target', h.target_object_id, 'quantale', v_q,
                                    'value', enriched_q_json(v_num));
      RETURN NEXT;
    END IF;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- Well-formed homs of a quantale-enriched category, as NUMERIC values.
CREATE OR REPLACE FUNCTION enriched_values(p_ec UUID)
RETURNS TABLE(hom_id UUID, src UUID, tgt UUID, val NUMERIC) AS $$
  SELECT eh.id, eh.source_object_id, eh.target_object_id,
         enriched_parse_value(enriched_quantale(p_ec), eh.value)
    FROM enriched_hom eh
    JOIN enriched_category e ON e.id = eh.enriched_category_id
   WHERE eh.enriched_category_id = p_ec
     AND EXISTS (SELECT 1 FROM object o
                  WHERE o.id = eh.source_object_id AND o.category_id = e.base_category_id)
     AND EXISTS (SELECT 1 FROM object o
                  WHERE o.id = eh.target_object_id AND o.category_id = e.base_category_id)
     AND enriched_parse_value(enriched_quantale(p_ec), eh.value) IS NOT NULL
     AND enriched_in_range(enriched_quantale(p_ec),
                           enriched_parse_value(enriched_quantale(p_ec), eh.value));
$$ LANGUAGE sql STABLE;

-- Well-formed stochastic kernels of a probabilistic enriched category.
CREATE OR REPLACE FUNCTION enriched_kernels(p_ec UUID)
RETURNS TABLE(hom_id UUID, src UUID, tgt UUID, kern JSONB) AS $$
  SELECT eh.id, eh.source_object_id, eh.target_object_id, enriched_kernel(eh.value)
    FROM enriched_hom eh
    JOIN enriched_category e ON e.id = eh.enriched_category_id
   WHERE eh.enriched_category_id = p_ec
     AND EXISTS (SELECT 1 FROM object o
                  WHERE o.id = eh.source_object_id AND o.category_id = e.base_category_id)
     AND EXISTS (SELECT 1 FROM object o
                  WHERE o.id = eh.target_object_id AND o.category_id = e.base_category_id)
     AND enriched_kernel(eh.value) IS NOT NULL
     AND cardinality(enriched_kernel_bad_rows(enriched_kernel(eh.value),
                                              enriched_tolerance(p_ec))) = 0;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- All problems of an enriched category (pure): every hom, then the laws.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION enriched_problems(p_ec UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  v_base UUID;
  v_kind TEXT;
  v_q TEXT;
  v_tol NUMERIC;
  r RECORD;
  pr RECORD;
BEGIN
  SELECT e.base_category_id INTO v_base FROM enriched_category e WHERE e.id = p_ec;
  IF v_base IS NULL THEN
    reason := 'missing_enriched_category';
    details := jsonb_build_object('enriched_category', p_ec);
    RETURN NEXT;
    RETURN;
  END IF;
  v_kind := enriched_kind(p_ec);
  v_q := enriched_quantale(p_ec);
  v_tol := enriched_tolerance(p_ec);

  FOR r IN SELECT eh.id FROM enriched_hom eh WHERE eh.enriched_category_id = p_ec ORDER BY eh.id LOOP
    FOR pr IN SELECT * FROM enriched_hom_problems(r.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
    END LOOP;
  END LOOP;

  IF v_kind <> 'probabilistic' THEN
    -- unit law at every object of the base category (missing hom = bottom)
    FOR r IN
      SELECT o.id AS obj, hv.val AS val
        FROM object o
        LEFT JOIN enriched_values(p_ec) hv ON hv.src = o.id AND hv.tgt = o.id
       WHERE o.category_id = v_base
       ORDER BY o.id
    LOOP
      IF NOT enriched_q_leq(v_q, enriched_q_unit(v_q),
                            coalesce(r.val, enriched_q_bottom(v_q)), v_tol) THEN
        reason := 'unit_law';
        details := jsonb_build_object('object', r.obj, 'quantale', v_q,
                                      'value', enriched_q_json(coalesce(r.val, enriched_q_bottom(v_q))),
                                      'missing', r.val IS NULL);
        RETURN NEXT;
      END IF;
    END LOOP;

    -- composition law h(x,y) ⊗ h(y,z) ≤_V h(x,z); triples with a missing
    -- first or second hom hold automatically (bottom absorbs ⊗)
    FOR r IN
      WITH hv AS (SELECT * FROM enriched_values(p_ec))
      SELECT a.src AS x, a.tgt AS y, b.tgt AS z, a.val AS xy, b.val AS yz, c.val AS xz,
             enriched_q_tensor(v_q, a.val, b.val) AS through
        FROM hv a
        JOIN hv b ON b.src = a.tgt
        LEFT JOIN hv c ON c.src = a.src AND c.tgt = b.tgt
       ORDER BY a.src, a.tgt, b.tgt
    LOOP
      IF r.through <> enriched_q_bottom(v_q)
         AND NOT enriched_q_leq(v_q, r.through, coalesce(r.xz, enriched_q_bottom(v_q)), v_tol) THEN
        reason := 'composition_law';
        details := jsonb_build_object(
          'source', r.x, 'middle', r.y, 'target', r.z, 'quantale', v_q,
          'direct', enriched_q_json(coalesce(r.xz, enriched_q_bottom(v_q))),
          'through', enriched_q_json(r.through),
          'missing', r.xz IS NULL);
        RETURN NEXT;
      END IF;
    END LOOP;
  ELSE
    -- one state space per object (the row sets of its outgoing kernels)
    FOR r IN
      SELECT a.src AS x, a.hom_id AS h1, b.hom_id AS h2
        FROM enriched_kernels(p_ec) a
        JOIN enriched_kernels(p_ec) b ON b.src = a.src AND a.hom_id < b.hom_id
       WHERE (SELECT array_agg(k ORDER BY k) FROM jsonb_object_keys(a.kern) k)
          <> (SELECT array_agg(k ORDER BY k) FROM jsonb_object_keys(b.kern) k)
       ORDER BY a.src, a.hom_id, b.hom_id
    LOOP
      reason := 'state_space';
      details := jsonb_build_object('object', r.x, 'hom', r.h1, 'other_hom', r.h2);
      RETURN NEXT;
    END LOOP;

    -- a kernel into y charges only states of y (rows of the kernels out of y)
    FOR r IN
      SELECT DISTINCT ON (f.hom_id) f.hom_id AS h, f.tgt AS y,
             enriched_kernel_unsupported(f.kern, g.kern) AS missing_states
        FROM enriched_kernels(p_ec) f
        JOIN enriched_kernels(p_ec) g ON g.src = f.tgt
       WHERE cardinality(enriched_kernel_unsupported(f.kern, g.kern)) > 0
       ORDER BY f.hom_id, g.hom_id
    LOOP
      reason := 'kernel_support';
      details := jsonb_build_object('hom', r.h, 'object', r.y, 'states', to_jsonb(r.missing_states));
      RETURN NEXT;
    END LOOP;

    -- identity kernels
    FOR r IN
      SELECT k.hom_id AS h, k.src AS x FROM enriched_kernels(p_ec) k
       WHERE k.src = k.tgt AND NOT enriched_kernel_is_identity(k.kern, v_tol)
       ORDER BY k.hom_id
    LOOP
      reason := 'identity_kernel';
      details := jsonb_build_object('hom', r.h, 'object', r.x);
      RETURN NEXT;
    END LOOP;

    -- Chapman–Kolmogorov on every recorded triple (skipped where the support
    -- check already failed)
    FOR r IN
      WITH hk AS (SELECT * FROM enriched_kernels(p_ec))
      SELECT a.src AS x, a.tgt AS y, b.tgt AS z, c.hom_id AS h,
             enriched_compose_kernels(a.kern, b.kern) AS through
        FROM hk a
        JOIN hk b ON b.src = a.tgt
        JOIN hk c ON c.src = a.src AND c.tgt = b.tgt
       WHERE cardinality(enriched_kernel_unsupported(a.kern, b.kern)) = 0
         AND NOT enriched_kernels_equal(enriched_compose_kernels(a.kern, b.kern), c.kern, v_tol)
       ORDER BY a.src, a.tgt, b.tgt
    LOOP
      reason := 'chapman_kolmogorov';
      details := jsonb_build_object('source', r.x, 'middle', r.y, 'target', r.z,
                                    'hom', r.h, 'through', r.through);
      RETURN NEXT;
    END LOOP;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Logging helpers and checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION enriched_record(p_ec UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  INSERT INTO enriched_violation (enriched_category_id, reason, details)
  VALUES (p_ec, p_reason, coalesce(p_details, '{}'::jsonb));
END;
$$ LANGUAGE plpgsql;

-- Batch tier: every hom and both laws (or the kernel laws).  Logs every
-- problem, raises in strict mode, returns TRUE iff there were none.
CREATE OR REPLACE FUNCTION check_enriched_category(p_ec UUID) RETURNS BOOLEAN AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM enriched_problems(p_ec) LOOP
    PERFORM enriched_record(p_ec, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Enriched category % violates its laws (% problem(s))', p_ec, n_problems;
  END IF;
  RETURN n_problems = 0;
END;
$$ LANGUAGE plpgsql;

-- Write-time tier: the hom row itself.
CREATE OR REPLACE FUNCTION trg_check_enriched_hom() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM enriched_hom_problems(NEW.id) LOOP
    PERFORM enriched_record(NEW.enriched_category_id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Enriched hom % is not valid (% problem(s))', NEW.id, n_problems;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_enriched_hom ON enriched_hom;
CREATE TRIGGER trg_check_enriched_hom
AFTER INSERT OR UPDATE ON enriched_hom
FOR EACH ROW EXECUTE FUNCTION trg_check_enriched_hom();

-- Problems of an enriched_composition row (pure).
CREATE OR REPLACE FUNCTION enriched_composition_problems(
  p_ec UUID, p_left UUID, p_right UUID, p_composed JSONB
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  g RECORD;   -- left hom, y → z
  f RECORD;   -- right hom, x → y (applied first)
  v_kind TEXT;
  v_q TEXT;
  v_tol NUMERIC;
  v_f NUMERIC;
  v_g NUMERIC;
  v_c NUMERIC;
  v_direct JSONB;
  v_direct_num NUMERIC;
  v_expected JSONB;
BEGIN
  SELECT eh.* INTO g FROM enriched_hom eh WHERE eh.id = p_left;
  SELECT eh.* INTO f FROM enriched_hom eh WHERE eh.id = p_right;
  IF g.id IS NULL OR f.id IS NULL
     OR g.enriched_category_id IS DISTINCT FROM p_ec
     OR f.enriched_category_id IS DISTINCT FROM p_ec
     OR f.target_object_id IS DISTINCT FROM g.source_object_id THEN
    reason := 'composition_typing';
    details := jsonb_build_object('left', p_left, 'right', p_right, 'enriched_category', p_ec,
                                  'right_target', f.target_object_id,
                                  'left_source', g.source_object_id);
    RETURN NEXT;
    RETURN;
  END IF;
  IF EXISTS (SELECT 1 FROM enriched_hom_problems(p_left))
     OR EXISTS (SELECT 1 FROM enriched_hom_problems(p_right)) THEN
    reason := 'composition_typing';
    details := jsonb_build_object('left', p_left, 'right', p_right, 'invalid_factor', TRUE);
    RETURN NEXT;
    RETURN;
  END IF;
  v_kind := enriched_kind(p_ec);
  v_q := enriched_quantale(p_ec);
  v_tol := enriched_tolerance(p_ec);
  SELECT eh.value INTO v_direct FROM enriched_hom eh
   WHERE eh.enriched_category_id = p_ec
     AND eh.source_object_id = f.source_object_id
     AND eh.target_object_id = g.target_object_id;

  IF v_kind = 'probabilistic' THEN
    IF cardinality(enriched_kernel_unsupported(enriched_kernel(f.value), enriched_kernel(g.value))) > 0 THEN
      reason := 'kernel_support';
      details := jsonb_build_object('hom', f.id, 'object', g.source_object_id,
                   'states', to_jsonb(enriched_kernel_unsupported(enriched_kernel(f.value),
                                                                   enriched_kernel(g.value))));
      RETURN NEXT;
      RETURN;
    END IF;
    v_expected := enriched_compose_kernels(enriched_kernel(f.value), enriched_kernel(g.value));
    IF enriched_kernel(p_composed) IS NULL
       OR NOT enriched_kernels_equal(enriched_kernel(p_composed), v_expected, v_tol) THEN
      reason := 'composition_value';
      details := jsonb_build_object('left', p_left, 'right', p_right,
                                    'recorded', p_composed, 'expected', v_expected);
      RETURN NEXT;
    END IF;
    IF enriched_kernel(v_direct) IS NOT NULL
       AND NOT enriched_kernels_equal(enriched_kernel(v_direct), v_expected, v_tol) THEN
      reason := 'chapman_kolmogorov';
      details := jsonb_build_object('source', f.source_object_id, 'middle', f.target_object_id,
                                    'target', g.target_object_id, 'through', v_expected);
      RETURN NEXT;
    END IF;
  ELSE
    v_f := enriched_parse_value(v_q, f.value);
    v_g := enriched_parse_value(v_q, g.value);
    v_c := enriched_parse_value(v_q, p_composed);
    IF v_c IS NULL OR abs(v_c - enriched_q_tensor(v_q, v_f, v_g)) > v_tol
       AND v_c IS DISTINCT FROM enriched_q_tensor(v_q, v_f, v_g) THEN
      reason := 'composition_value';
      details := jsonb_build_object('left', p_left, 'right', p_right, 'recorded', p_composed,
                                    'expected', enriched_q_json(enriched_q_tensor(v_q, v_f, v_g)));
      RETURN NEXT;
    END IF;
    v_direct_num := enriched_parse_value(v_q, v_direct);
    IF enriched_q_tensor(v_q, v_f, v_g) <> enriched_q_bottom(v_q)
       AND NOT enriched_q_leq(v_q, enriched_q_tensor(v_q, v_f, v_g),
                              coalesce(v_direct_num, enriched_q_bottom(v_q)), v_tol) THEN
      reason := 'composition_law';
      details := jsonb_build_object(
        'source', f.source_object_id, 'middle', f.target_object_id, 'target', g.target_object_id,
        'quantale', v_q,
        'direct', enriched_q_json(coalesce(v_direct_num, enriched_q_bottom(v_q))),
        'through', enriched_q_json(enriched_q_tensor(v_q, v_f, v_g)),
        'missing', v_direct_num IS NULL);
      RETURN NEXT;
    END IF;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- Write-time tier: an enriched_composition row.  `verified` is set by the
-- ledger, not by the writer.
CREATE OR REPLACE FUNCTION trg_check_enriched_composition() RETURNS trigger AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  FOR pr IN SELECT * FROM enriched_composition_problems(
              NEW.enriched_category_id, NEW.left_hom_id, NEW.right_hom_id, NEW.composed_value) LOOP
    PERFORM enriched_record(NEW.enriched_category_id, pr.reason,
                            pr.details || jsonb_build_object('composition', NEW.id));
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Enriched composition % is not valid (% problem(s))', NEW.id, n_problems;
  END IF;
  NEW.verified := (n_problems = 0);
  NEW.verified_at := CASE WHEN n_problems = 0 THEN now() END;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_enriched_composition ON enriched_composition;
CREATE TRIGGER trg_check_enriched_composition
BEFORE INSERT OR UPDATE ON enriched_composition
FOR EACH ROW EXECUTE FUNCTION trg_check_enriched_composition();

-- ---------------------------------------------------------------------------
-- Writers
-- ---------------------------------------------------------------------------
-- Metric hom-value.  'Infinity' is stored as the string "Infinity"; NaN is
-- stored as given and then rejected as malformed.
CREATE OR REPLACE FUNCTION update_enriched_hom_metric(
  p_enriched_cat UUID, p_src UUID, p_tgt UUID, p_dist DOUBLE PRECISION
) RETURNS VOID AS $$
DECLARE
  v_json JSONB;
BEGIN
  v_json := CASE
              WHEN p_dist = 'Infinity'::float8 THEN to_jsonb('Infinity'::text)
              WHEN p_dist = 'NaN'::float8 THEN to_jsonb('NaN'::text)
              ELSE to_jsonb(p_dist::numeric)
            END;
  INSERT INTO enriched_hom
    (enriched_category_id, source_object_id, target_object_id, value)
  VALUES
    (p_enriched_cat, p_src, p_tgt, jsonb_build_object('distance', v_json))
  ON CONFLICT (enriched_category_id, source_object_id, target_object_id)
  DO UPDATE SET value = EXCLUDED.value, last_updated = now();
END;
$$ LANGUAGE plpgsql;

-- Any hom-value (kernel descriptor, quantale value, ...).
CREATE OR REPLACE FUNCTION update_enriched_hom_value(
  p_enriched_cat UUID, p_src UUID, p_tgt UUID, p_value JSONB
) RETURNS VOID AS $$
BEGIN
  INSERT INTO enriched_hom
    (enriched_category_id, source_object_id, target_object_id, value)
  VALUES
    (p_enriched_cat, p_src, p_tgt, p_value)
  ON CONFLICT (enriched_category_id, source_object_id, target_object_id)
  DO UPDATE SET value = EXCLUDED.value, last_updated = now();
END;
$$ LANGUAGE plpgsql;

-- Probabilistic hom-value (kept for compatibility).
CREATE OR REPLACE FUNCTION update_enriched_hom_prob(
  p_enriched_cat UUID, p_src UUID, p_tgt UUID, p_kernel JSONB
) RETURNS VOID AS $$
BEGIN
  PERFORM update_enriched_hom_value(p_enriched_cat, p_src, p_tgt, p_kernel);
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- The original metric triangle check, corrected: every triple (X, Y, Z) with
-- d(X, Y), d(Y, Z) recorded and d(X, Z) > d(X, Y) + d(Y, Z), a missing
-- d(X, Z) counting as ∞.  lhs = d(X, Z), rhs = d(X, Y) + d(Y, Z).  Pure (no
-- logging); check_enriched_category logs.  Only for metric categories.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION check_metric_triangle_inequality(p_enriched_cat UUID)
RETURNS TABLE(violating_src UUID, violating_mid UUID, violating_tgt UUID,
              lhs DOUBLE PRECISION, rhs DOUBLE PRECISION) AS $$
BEGIN
  IF enriched_quantale(p_enriched_cat) IS DISTINCT FROM 'lawvere' THEN
    RAISE EXCEPTION 'Enriched category % is not metric-enriched', p_enriched_cat;
  END IF;
  RETURN QUERY
  WITH hv AS (SELECT * FROM enriched_values(p_enriched_cat))
  SELECT a.src, a.tgt, b.tgt,
         coalesce(c.val, 'Infinity'::numeric)::double precision,
         (a.val + b.val)::double precision
    FROM hv a
    JOIN hv b ON b.src = a.tgt
    LEFT JOIN hv c ON c.src = a.src AND c.tgt = b.tgt
   WHERE a.val + b.val <> 'Infinity'::numeric
     AND coalesce(c.val, 'Infinity'::numeric) > a.val + b.val
         + enriched_tolerance(p_enriched_cat);
END;
$$ LANGUAGE plpgsql STABLE;
