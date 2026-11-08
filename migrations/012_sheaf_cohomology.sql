-- ============================================================================
-- Categorical Ledger — Migration 012: Sheaf Cohomology
-- ============================================================================
-- Finite sites, covers, presheaves of sets with their restriction maps, the
-- sheaf condition, Čech H⁰, and stored cohomology descriptors.
--
-- Recording.
--   site            a finite topological space; base_space_object_id is the
--                   whole space (an open)
--   site_open       the opens: an object of the ledger and its points (a set
--                   of text labels, stored sorted and without repeats; two
--                   opens of a site never have the same points)
--   site_cover      a named cover of covered_object_id; its members are the
--                   cover rows with this site_cover_id (a cover row without
--                   one joins the site's cover 'default' of the base)
--   presheaf        a presheaf of sets on a site; presheaf_section holds the
--                   sections F(U) (text labels), presheaf_restriction the
--                   restriction maps res(U, V, s) = image for V ⊆ U.  is_sheaf
--                   is written only by check_sheaf_condition and is reset
--                   whenever the presheaf's data or its site changes.
--   cech_complex, cohomology_group
--                   Čech cochains / cohomology descriptors of a presheaf,
--                   optionally on a cover (site_cover_id).  A degree-0
--                   descriptor carries {"cardinality": n} (the number of
--                   compatible families, checked here); a degree-n ≥ 1
--                   descriptor carries {"rank": r} (computed elsewhere, e.g.
--                   over F₂ by qbx.categorical.sheaf.LinearPresheaf; only its
--                   type is checked here).
--   sheaf_descent_data
--                   a family {member open id: section} on a cover; verified is
--                   computed on write: the family is defined on exactly the
--                   members, compatible, and has exactly one gluing.
--   sheaf_cohomology_obstruction
--                   the violation table (column reason); store_sheaf_obstruction
--                   records a manual entry (reason 'obstruction').
--
-- Checks.  Every check logs to sheaf_cohomology_obstruction (site, presheaf,
-- degree, reason, details) and raises only when qbx.enforcement_mode = 'strict'.
--   site (sheaf_site_problems, check_site)
--     base_typing             the base is not an open, or its points are not
--                             the union of all opens (details: base)
--     topology_empty          no open with no points
--     topology_intersection   U ∩ V is not an open (details: opens = [U, V])
--     topology_union          U ∪ V is not an open (details: opens = [U, V])
--     cover_typing            the covered set or a member is not an open, or a
--                             member is not inside the covered set (details:
--                             cover, open)  — also at write time
--     cover_not_covering      the members do not cover the covered set
--                             (details: cover)
--   presheaf (sheaf_presheaf_problems, check_sheaf_condition), in stages, each
--   running only when the previous ones found nothing:
--     site_invalid            the site has problems (details: site)
--     section_typing          a section over a set that is not an open of the
--                             site (details: open, section)  — also at write time
--     restriction_typing      a restriction whose sets are not opens, whose
--                             target is not inside its source, or whose section
--                             / image is not a section (details: from, to,
--                             section)  — also at write time
--     cohomology_typing       a cohomology record with a negative degree, a site
--                             or cover of another site, or a descriptor without
--                             a non-negative integer "cardinality" (degree 0) /
--                             "rank" (degree ≥ 1) (details: degree, cover)
--                             — also at write time
--     cochain_typing          a cochain record with a negative degree, or a site
--                             or cover of another site (details: degree, cover)
--                             — also at write time
--     ---
--     restriction_missing     V ⊆ U, s ∈ F(U), no res(U, V, s) (details: from,
--                             to, section)
--     restriction_identity    res(U, U, s) ≠ s (details: open, section)
--     restriction_composition W ⊆ V ⊆ U pairwise distinct and
--                             res(V, W, res(U, V, s)) ≠ res(U, W, s) (details:
--                             from, via, to, section)
--     ---
--     sheaf_empty_open        F(∅) does not have exactly one section
--                             (details: count)
--     sheaf_locality          on a registered cover: the number of unordered
--                             pairs s ≠ t ∈ F(U) restricting equally to every
--                             member (details: cover, count)
--     sheaf_gluing            on a registered cover: the number of compatible
--                             families with no gluing (details: cover, count)
--     cohomology_h0_mismatch  a degree-0 record on a cover whose cardinality is
--                             not the number of compatible families (details:
--                             cover, recorded, computed)
-- The sheaf condition is checked on the registered covers and on the empty
-- cover of ∅ (sheaf_empty_open): a pass means "a sheaf for the registered
-- covers".  qbx.categorical.sheaf.Presheaf.is_sheaf checks every cover.
--
-- Formal backing (Formal/Sheaf.lean): locality and gluing over every cover are
-- exactly Mathlib's IsSheaf (isSheaf_iff_locality_and_gluing); a sheaf has
-- exactly one section over ∅ (uniqueBot); neither half implies the other
-- (constBool_gluing_not_locality, constEmpty_locality_not_gluing); for a sheaf
-- the number of compatible families on a cover is the number of sections over
-- the covered set (card_compatible_eq); the presheaf of all functions passes
-- (presheafToTypes_locality_and_gluing), which the live tests use as an oracle.
--
-- Phase 1 sprint 9 rewrite.  Running the original on PostgreSQL 16 showed:
--   * check_sheaf_condition only returned the stored is_sheaf flag: FALSE for
--     every presheaf until someone set the flag by hand, TRUE after;
--   * a presheaf had no restriction maps, so the sheaf condition could not be
--     stated; register_presheaf accepted sections over anything (keys that are
--     not opens, or not even ids);
--   * store_cohomology_group and store_cech_cochain accepted negative degrees
--     and a site other than the presheaf's;
--   * sheaf_descent_data accepted verified = TRUE with no check;
--   * covers were never checked to cover anything, nothing wrote to
--     sheaf_cohomology_obstruction, and nothing ran in run_all_batch_checks.
-- ============================================================================

CREATE TABLE IF NOT EXISTS site (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  base_space_object_id UUID REFERENCES object(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS site_open (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  site_id UUID NOT NULL REFERENCES site(id) ON DELETE CASCADE,
  object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  points TEXT[] NOT NULL DEFAULT '{}',
  UNIQUE (site_id, object_id),
  UNIQUE (site_id, points)
);

CREATE TABLE IF NOT EXISTS site_cover (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  site_id UUID NOT NULL REFERENCES site(id) ON DELETE CASCADE,
  name TEXT NOT NULL,
  covered_object_id UUID REFERENCES object(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb,
  UNIQUE (site_id, name)
);

CREATE TABLE IF NOT EXISTS cover (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  site_id UUID NOT NULL REFERENCES site(id) ON DELETE CASCADE,
  open_set_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  metadata JSONB DEFAULT '{}'::jsonb
);
ALTER TABLE cover ADD COLUMN IF NOT EXISTS
  site_cover_id UUID REFERENCES site_cover(id) ON DELETE CASCADE;

CREATE INDEX IF NOT EXISTS idx_cover_site ON cover (site_id);
CREATE INDEX IF NOT EXISTS idx_cover_site_cover ON cover (site_cover_id);

CREATE TABLE IF NOT EXISTS presheaf (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  site_id UUID NOT NULL REFERENCES site(id) ON DELETE CASCADE,
  name TEXT NOT NULL,
  assignment JSONB DEFAULT '{}'::jsonb,   -- open id → section labels (as registered)
  is_sheaf BOOLEAN DEFAULT FALSE,         -- written by check_sheaf_condition only
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now(),
  UNIQUE (site_id, name)
);

CREATE TABLE IF NOT EXISTS presheaf_section (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  presheaf_id UUID NOT NULL REFERENCES presheaf(id) ON DELETE CASCADE,
  open_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  label TEXT NOT NULL,
  UNIQUE (presheaf_id, open_object_id, label)
);

CREATE TABLE IF NOT EXISTS presheaf_restriction (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  presheaf_id UUID NOT NULL REFERENCES presheaf(id) ON DELETE CASCADE,
  from_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  to_object_id UUID NOT NULL REFERENCES object(id) ON DELETE CASCADE,
  section TEXT NOT NULL,
  image TEXT NOT NULL,
  UNIQUE (presheaf_id, from_object_id, to_object_id, section)
);

CREATE TABLE IF NOT EXISTS cech_complex (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  site_id UUID NOT NULL REFERENCES site(id) ON DELETE CASCADE,
  presheaf_id UUID NOT NULL REFERENCES presheaf(id) ON DELETE CASCADE,
  degree INT NOT NULL,
  data JSONB DEFAULT '{}'::jsonb,
  computed_at TIMESTAMPTZ DEFAULT now()
);
ALTER TABLE cech_complex ADD COLUMN IF NOT EXISTS
  site_cover_id UUID REFERENCES site_cover(id) ON DELETE CASCADE;

CREATE TABLE IF NOT EXISTS cohomology_group (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  site_id UUID REFERENCES site(id) ON DELETE CASCADE,
  presheaf_id UUID REFERENCES presheaf(id) ON DELETE CASCADE,
  degree INT NOT NULL,
  group_descriptor JSONB NOT NULL,   -- {"cardinality": n} (degree 0) / {"rank": r}
  computed_at TIMESTAMPTZ DEFAULT now()
);
ALTER TABLE cohomology_group ADD COLUMN IF NOT EXISTS
  site_cover_id UUID REFERENCES site_cover(id) ON DELETE CASCADE;

CREATE TABLE IF NOT EXISTS sheaf_cohomology_obstruction (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  site_id UUID REFERENCES site(id) ON DELETE CASCADE,
  presheaf_id UUID REFERENCES presheaf(id) ON DELETE CASCADE,
  degree INT,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);
ALTER TABLE sheaf_cohomology_obstruction ADD COLUMN IF NOT EXISTS reason TEXT;

CREATE INDEX IF NOT EXISTS idx_sheaf_obstruction_site
  ON sheaf_cohomology_obstruction (site_id, detected_at DESC);

CREATE TABLE IF NOT EXISTS sheaf_descent_data (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  presheaf_id UUID NOT NULL REFERENCES presheaf(id) ON DELETE CASCADE,
  cover_id UUID REFERENCES cover(id) ON DELETE CASCADE,
  descent_cocycle JSONB NOT NULL,
  verified BOOLEAN DEFAULT FALSE,
  verification_proof UUID REFERENCES proof_artifact(id),
  verified_at TIMESTAMPTZ
);
ALTER TABLE sheaf_descent_data ALTER COLUMN cover_id DROP NOT NULL;
ALTER TABLE sheaf_descent_data ADD COLUMN IF NOT EXISTS
  site_cover_id UUID REFERENCES site_cover(id) ON DELETE CASCADE;

-- ---------------------------------------------------------------------------
-- Upgrade path for a database holding the original 012 tables: legacy cover
-- rows become the members of the site's cover 'default' of the base, and
-- sections recorded in presheaf.assignment under an object id are imported.
-- ---------------------------------------------------------------------------
INSERT INTO site_cover (site_id, name, covered_object_id)
SELECT DISTINCT c.site_id, 'default', s.base_space_object_id
  FROM cover c JOIN site s ON s.id = c.site_id
 WHERE c.site_cover_id IS NULL
ON CONFLICT (site_id, name) DO NOTHING;

UPDATE cover c SET site_cover_id = sc.id
  FROM site_cover sc
 WHERE c.site_cover_id IS NULL AND sc.site_id = c.site_id AND sc.name = 'default';

INSERT INTO presheaf_section (presheaf_id, open_object_id, label)
SELECT p.id, ob.id, v.label
  FROM presheaf p
  CROSS JOIN LATERAL jsonb_each(CASE WHEN jsonb_typeof(p.assignment) = 'object'
                                     THEN p.assignment ELSE '{}'::jsonb END) k
  CROSS JOIN LATERAL jsonb_array_elements_text(CASE WHEN jsonb_typeof(k.value) = 'array'
                                                    THEN k.value ELSE '[]'::jsonb END) v(label)
  JOIN object ob ON ob.id::text = lower(k.key)
ON CONFLICT DO NOTHING;

-- ---------------------------------------------------------------------------
-- Helpers (pure)
-- ---------------------------------------------------------------------------
-- A point set in canonical form: sorted, without repeats.
CREATE OR REPLACE FUNCTION sheaf_pts(p TEXT[]) RETURNS TEXT[] AS $$
  SELECT coalesce(ARRAY(SELECT DISTINCT x FROM unnest(p) x WHERE x IS NOT NULL ORDER BY 1),
                  '{}'::text[]);
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION sheaf_pts_inter(a TEXT[], b TEXT[]) RETURNS TEXT[] AS $$
  SELECT ARRAY(SELECT x FROM unnest(a) x INTERSECT SELECT y FROM unnest(b) y ORDER BY 1);
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION sheaf_pts_union(a TEXT[], b TEXT[]) RETURNS TEXT[] AS $$
  SELECT ARRAY(SELECT x FROM unnest(a) x UNION SELECT y FROM unnest(b) y ORDER BY 1);
$$ LANGUAGE sql IMMUTABLE;

-- The points of p_obj as an open of p_site (NULL if it is not an open).
CREATE OR REPLACE FUNCTION sheaf_open_pts(p_site UUID, p_obj UUID) RETURNS TEXT[] AS $$
  SELECT so.points FROM site_open so WHERE so.site_id = p_site AND so.object_id = p_obj;
$$ LANGUAGE sql STABLE;

-- The open of p_site with exactly these (canonical) points, or NULL.
CREATE OR REPLACE FUNCTION sheaf_open_at(p_site UUID, p_pts TEXT[]) RETURNS UUID AS $$
  SELECT so.object_id FROM site_open so WHERE so.site_id = p_site AND so.points = p_pts;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION sheaf_is_section(p_presheaf UUID, p_open UUID, p_label TEXT)
RETURNS BOOLEAN AS $$
  SELECT EXISTS (SELECT 1 FROM presheaf_section ps
                  WHERE ps.presheaf_id = p_presheaf AND ps.open_object_id = p_open
                    AND ps.label = p_label);
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION sheaf_res(p_presheaf UUID, p_from UUID, p_to UUID, p_section TEXT)
RETURNS TEXT AS $$
  SELECT r.image FROM presheaf_restriction r
   WHERE r.presheaf_id = p_presheaf AND r.from_object_id = p_from
     AND r.to_object_id = p_to AND r.section = p_section;
$$ LANGUAGE sql STABLE;

-- The members of a cover (without repeats).
CREATE OR REPLACE FUNCTION sheaf_cover_members(p_cover UUID) RETURNS UUID[] AS $$
  SELECT coalesce(ARRAY(SELECT DISTINCT c.open_set_object_id FROM cover c
                         WHERE c.site_cover_id = p_cover ORDER BY 1), '{}'::uuid[]);
$$ LANGUAGE sql STABLE;

-- Is v a JSON non-negative integer?
CREATE OR REPLACE FUNCTION sheaf_nonneg_int(v JSONB) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(v) = 'number' AND v::text ~ '^[0-9]+$', FALSE);
$$ LANGUAGE sql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Site problems (pure)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION sheaf_cover_problems(p_cover UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  sc RECORD;
  v_cov TEXT[];
  v_pm TEXT[];
  v_union TEXT[];
  m UUID;
  v_ok BOOLEAN := TRUE;
BEGIN
  SELECT c.* INTO sc FROM site_cover c WHERE c.id = p_cover;
  IF sc.id IS NULL THEN
    RETURN;
  END IF;
  v_cov := sheaf_open_pts(sc.site_id, sc.covered_object_id);
  IF v_cov IS NULL THEN
    reason := 'cover_typing';
    details := jsonb_build_object('cover', sc.id, 'open', sc.covered_object_id);
    RETURN NEXT;
    RETURN;
  END IF;
  FOREACH m IN ARRAY sheaf_cover_members(p_cover) LOOP
    v_pm := sheaf_open_pts(sc.site_id, m);
    IF v_pm IS NULL OR NOT (v_pm <@ v_cov) THEN
      reason := 'cover_typing';
      details := jsonb_build_object('cover', sc.id, 'open', m);
      RETURN NEXT;
      v_ok := FALSE;
    END IF;
  END LOOP;
  IF v_ok THEN
    v_union := ARRAY(SELECT DISTINCT x FROM site_open so, unnest(so.points) x
                      WHERE so.site_id = sc.site_id
                        AND so.object_id = ANY (sheaf_cover_members(p_cover))
                      ORDER BY 1);
    IF v_union <> v_cov THEN
      reason := 'cover_not_covering';
      details := jsonb_build_object('cover', sc.id);
      RETURN NEXT;
    END IF;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION sheaf_site_problems(p_site UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  st RECORD;
  a RECORD;
  b RECORD;
  c RECORD;
  pr RECORD;
  v_all TEXT[];
  v_base TEXT[];
BEGIN
  SELECT s.* INTO st FROM site s WHERE s.id = p_site;
  IF st.id IS NULL THEN
    RETURN;
  END IF;
  v_all := ARRAY(SELECT DISTINCT x FROM site_open so, unnest(so.points) x
                  WHERE so.site_id = p_site ORDER BY 1);
  v_base := sheaf_open_pts(p_site, st.base_space_object_id);
  IF v_base IS NULL OR v_base <> v_all THEN
    reason := 'base_typing';
    details := jsonb_build_object('base', st.base_space_object_id);
    RETURN NEXT;
  END IF;
  IF NOT EXISTS (SELECT 1 FROM site_open so WHERE so.site_id = p_site AND so.points = '{}') THEN
    reason := 'topology_empty';
    details := '{}'::jsonb;
    RETURN NEXT;
  END IF;
  FOR a IN SELECT so.* FROM site_open so WHERE so.site_id = p_site ORDER BY so.object_id LOOP
    FOR b IN SELECT so.* FROM site_open so
              WHERE so.site_id = p_site AND so.object_id > a.object_id ORDER BY so.object_id LOOP
      IF sheaf_open_at(p_site, sheaf_pts_inter(a.points, b.points)) IS NULL THEN
        reason := 'topology_intersection';
        details := jsonb_build_object('opens', jsonb_build_array(a.object_id, b.object_id));
        RETURN NEXT;
      END IF;
      IF sheaf_open_at(p_site, sheaf_pts_union(a.points, b.points)) IS NULL THEN
        reason := 'topology_union';
        details := jsonb_build_object('opens', jsonb_build_array(a.object_id, b.object_id));
        RETURN NEXT;
      END IF;
    END LOOP;
  END LOOP;
  FOR c IN SELECT sc.id FROM site_cover sc WHERE sc.site_id = p_site ORDER BY sc.name LOOP
    FOR pr IN SELECT * FROM sheaf_cover_problems(c.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT;
    END LOOP;
  END LOOP;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Presheaf typing (pure, per row)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION sheaf_section_typing_problems(p_row UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT 'section_typing'::text,
         jsonb_build_object('open', ps.open_object_id, 'section', ps.label)
    FROM presheaf_section ps JOIN presheaf p ON p.id = ps.presheaf_id
   WHERE ps.id = p_row AND sheaf_open_pts(p.site_id, ps.open_object_id) IS NULL;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION sheaf_restriction_typing_problems(p_row UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT 'restriction_typing'::text,
         jsonb_build_object('from', r.from_object_id, 'to', r.to_object_id, 'section', r.section)
    FROM presheaf_restriction r JOIN presheaf p ON p.id = r.presheaf_id
   WHERE r.id = p_row
     AND NOT coalesce(sheaf_open_pts(p.site_id, r.to_object_id)
                        <@ sheaf_open_pts(p.site_id, r.from_object_id)
                      AND sheaf_is_section(p.id, r.from_object_id, r.section)
                      AND sheaf_is_section(p.id, r.to_object_id, r.image), FALSE);
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION sheaf_cohomology_typing_problems(p_row UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT 'cohomology_typing'::text,
         jsonb_build_object('degree', g.degree, 'cover', g.site_cover_id)
    FROM cohomology_group g JOIN presheaf p ON p.id = g.presheaf_id
   WHERE g.id = p_row
     AND (g.degree < 0
          OR (g.site_id IS NOT NULL AND g.site_id <> p.site_id)
          OR (g.site_cover_id IS NOT NULL
              AND NOT EXISTS (SELECT 1 FROM site_cover sc
                               WHERE sc.id = g.site_cover_id AND sc.site_id = p.site_id))
          OR NOT sheaf_nonneg_int(g.group_descriptor
                                  -> CASE WHEN g.degree = 0 THEN 'cardinality' ELSE 'rank' END));
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION sheaf_cochain_typing_problems(p_row UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT 'cochain_typing'::text,
         jsonb_build_object('degree', x.degree, 'cover', x.site_cover_id)
    FROM cech_complex x JOIN presheaf p ON p.id = x.presheaf_id
   WHERE x.id = p_row
     AND (x.degree < 0
          OR x.site_id <> p.site_id
          OR (x.site_cover_id IS NOT NULL
              AND NOT EXISTS (SELECT 1 FROM site_cover sc
                               WHERE sc.id = x.site_cover_id AND sc.site_id = p.site_id)));
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Families on a cover (pure).  Assumes a valid site and a functorial presheaf.
-- ---------------------------------------------------------------------------
-- Every compatible family on the cover, as {member id: section}  (Čech H⁰).
CREATE OR REPLACE FUNCTION sheaf_compatible_families(p_presheaf UUID, p_cover UUID)
RETURNS SETOF JSONB AS $$
DECLARE
  v_site UUID;
  v_members UUID[];
  v_fams JSONB[] := ARRAY['{}'::jsonb];
  v_next JSONB[];
  f JSONB;
  s TEXT;
  k INT;
  j INT;
  w UUID;
  v_ok BOOLEAN;
BEGIN
  SELECT sc.site_id INTO v_site FROM site_cover sc WHERE sc.id = p_cover;
  v_members := sheaf_cover_members(p_cover);
  FOR k IN 1 .. coalesce(array_length(v_members, 1), 0) LOOP
    v_next := '{}'::jsonb[];
    FOREACH f IN ARRAY v_fams LOOP
      FOR s IN SELECT ps.label FROM presheaf_section ps
                WHERE ps.presheaf_id = p_presheaf AND ps.open_object_id = v_members[k]
                ORDER BY ps.label LOOP
        v_ok := TRUE;
        FOR j IN 1 .. k - 1 LOOP
          w := sheaf_open_at(v_site, sheaf_pts_inter(sheaf_open_pts(v_site, v_members[j]),
                                                     sheaf_open_pts(v_site, v_members[k])));
          IF sheaf_res(p_presheaf, v_members[j], w, f ->> v_members[j]::text)
               IS DISTINCT FROM sheaf_res(p_presheaf, v_members[k], w, s) THEN
            v_ok := FALSE;
            EXIT;
          END IF;
        END LOOP;
        IF v_ok THEN
          v_next := array_append(v_next, f || jsonb_build_object(v_members[k]::text, s));
        END IF;
      END LOOP;
    END LOOP;
    v_fams := v_next;
  END LOOP;
  RETURN QUERY SELECT x FROM unnest(v_fams) x;
END;
$$ LANGUAGE plpgsql STABLE;

-- The sections over the covered set restricting to the family on every member.
CREATE OR REPLACE FUNCTION sheaf_gluings(p_presheaf UUID, p_cover UUID, p_family JSONB)
RETURNS SETOF TEXT AS $$
  SELECT ps.label FROM site_cover sc
    JOIN presheaf_section ps ON ps.presheaf_id = p_presheaf
                            AND ps.open_object_id = sc.covered_object_id
   WHERE sc.id = p_cover
     AND NOT EXISTS (
       SELECT 1 FROM unnest(sheaf_cover_members(p_cover)) m
        WHERE sheaf_res(p_presheaf, sc.covered_object_id, m, ps.label)
                IS DISTINCT FROM (p_family ->> m::text))
   ORDER BY ps.label;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION sheaf_locality_failures(p_presheaf UUID, p_cover UUID)
RETURNS INT AS $$
  SELECT count(*)::int
    FROM site_cover sc
    JOIN presheaf_section s1 ON s1.presheaf_id = p_presheaf
                            AND s1.open_object_id = sc.covered_object_id
    JOIN presheaf_section s2 ON s2.presheaf_id = p_presheaf
                            AND s2.open_object_id = sc.covered_object_id
                            AND s1.label < s2.label
   WHERE sc.id = p_cover
     AND NOT EXISTS (
       SELECT 1 FROM unnest(sheaf_cover_members(p_cover)) m
        WHERE sheaf_res(p_presheaf, sc.covered_object_id, m, s1.label)
                IS DISTINCT FROM sheaf_res(p_presheaf, sc.covered_object_id, m, s2.label));
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION sheaf_gluing_failures(p_presheaf UUID, p_cover UUID)
RETURNS INT AS $$
  SELECT count(*)::int FROM sheaf_compatible_families(p_presheaf, p_cover) f
   WHERE NOT EXISTS (SELECT 1 FROM sheaf_gluings(p_presheaf, p_cover, f));
$$ LANGUAGE sql STABLE;

-- Is p_family a descent datum with exactly one gluing?  (Defined on exactly the
-- members, compatible on every overlap, one gluing.)
CREATE OR REPLACE FUNCTION sheaf_descent_verified(p_presheaf UUID, p_cover UUID, p_family JSONB)
RETURNS BOOLEAN AS $$
DECLARE
  v_site UUID;
  v_members UUID[];
  j INT;
  k INT;
  w UUID;
BEGIN
  SELECT sc.site_id INTO v_site FROM site_cover sc WHERE sc.id = p_cover;
  IF v_site IS NULL OR p_family IS NULL OR jsonb_typeof(p_family) <> 'object' THEN
    RETURN FALSE;
  END IF;
  v_members := sheaf_cover_members(p_cover);
  IF ARRAY(SELECT k2 FROM jsonb_object_keys(p_family) k2 ORDER BY 1)
       IS DISTINCT FROM ARRAY(SELECT m::text FROM unnest(v_members) m ORDER BY 1) THEN
    RETURN FALSE;
  END IF;
  IF EXISTS (SELECT 1 FROM jsonb_each(p_family) e WHERE jsonb_typeof(e.value) <> 'string') THEN
    RETURN FALSE;
  END IF;
  FOR k IN 1 .. coalesce(array_length(v_members, 1), 0) LOOP
    IF NOT sheaf_is_section(p_presheaf, v_members[k], p_family ->> v_members[k]::text) THEN
      RETURN FALSE;
    END IF;
    FOR j IN 1 .. k - 1 LOOP
      w := sheaf_open_at(v_site, sheaf_pts_inter(sheaf_open_pts(v_site, v_members[j]),
                                                 sheaf_open_pts(v_site, v_members[k])));
      IF sheaf_res(p_presheaf, v_members[j], w, p_family ->> v_members[j]::text)
           IS DISTINCT FROM sheaf_res(p_presheaf, v_members[k], w, p_family ->> v_members[k]::text)
      THEN
        RETURN FALSE;
      END IF;
    END LOOP;
  END LOOP;
  RETURN (SELECT count(*) FROM sheaf_gluings(p_presheaf, p_cover, p_family)) = 1;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Every problem of a presheaf (pure)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION sheaf_presheaf_problems(p_presheaf UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  p RECORD;
  r RECORD;
  u RECORD;
  v RECORD;
  w RECORD;
  s RECORD;
  c RECORD;
  g RECORD;
  pr RECORD;
  v_found BOOLEAN := FALSE;
  v_a TEXT;
  v_b TEXT;
  v_c TEXT;
  v_n INT;
  v_empty UUID;
BEGIN
  SELECT ps.* INTO p FROM presheaf ps WHERE ps.id = p_presheaf;
  IF p.id IS NULL THEN
    RETURN;
  END IF;
  IF EXISTS (SELECT 1 FROM sheaf_site_problems(p.site_id)) THEN
    reason := 'site_invalid';
    details := jsonb_build_object('site', p.site_id);
    RETURN NEXT;
    RETURN;
  END IF;

  -- typing
  FOR r IN SELECT x.id FROM presheaf_section x WHERE x.presheaf_id = p.id ORDER BY x.id LOOP
    FOR pr IN SELECT * FROM sheaf_section_typing_problems(r.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT; v_found := TRUE;
    END LOOP;
  END LOOP;
  FOR r IN SELECT x.id FROM presheaf_restriction x WHERE x.presheaf_id = p.id ORDER BY x.id LOOP
    FOR pr IN SELECT * FROM sheaf_restriction_typing_problems(r.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT; v_found := TRUE;
    END LOOP;
  END LOOP;
  FOR r IN SELECT x.id FROM cohomology_group x WHERE x.presheaf_id = p.id ORDER BY x.id LOOP
    FOR pr IN SELECT * FROM sheaf_cohomology_typing_problems(r.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT; v_found := TRUE;
    END LOOP;
  END LOOP;
  FOR r IN SELECT x.id FROM cech_complex x WHERE x.presheaf_id = p.id ORDER BY x.id LOOP
    FOR pr IN SELECT * FROM sheaf_cochain_typing_problems(r.id) LOOP
      reason := pr.reason; details := pr.details; RETURN NEXT; v_found := TRUE;
    END LOOP;
  END LOOP;
  IF v_found THEN
    RETURN;
  END IF;

  -- functoriality
  FOR u IN SELECT so.* FROM site_open so WHERE so.site_id = p.site_id ORDER BY so.object_id LOOP
    FOR s IN SELECT x.label FROM presheaf_section x
              WHERE x.presheaf_id = p.id AND x.open_object_id = u.object_id ORDER BY x.label LOOP
      FOR v IN SELECT so.* FROM site_open so
                WHERE so.site_id = p.site_id AND so.points <@ u.points ORDER BY so.object_id LOOP
        IF sheaf_res(p.id, u.object_id, v.object_id, s.label) IS NULL THEN
          reason := 'restriction_missing';
          details := jsonb_build_object('from', u.object_id, 'to', v.object_id,
                                        'section', s.label);
          RETURN NEXT; v_found := TRUE;
        END IF;
      END LOOP;
      v_a := sheaf_res(p.id, u.object_id, u.object_id, s.label);
      IF v_a IS NOT NULL AND v_a <> s.label THEN
        reason := 'restriction_identity';
        details := jsonb_build_object('open', u.object_id, 'section', s.label);
        RETURN NEXT; v_found := TRUE;
      END IF;
      FOR v IN SELECT so.* FROM site_open so
                WHERE so.site_id = p.site_id AND so.points <@ u.points
                  AND so.object_id <> u.object_id ORDER BY so.object_id LOOP
        v_a := sheaf_res(p.id, u.object_id, v.object_id, s.label);
        CONTINUE WHEN v_a IS NULL;
        FOR w IN SELECT so.* FROM site_open so
                  WHERE so.site_id = p.site_id AND so.points <@ v.points
                    AND so.object_id <> v.object_id AND so.object_id <> u.object_id
                  ORDER BY so.object_id LOOP
          v_b := sheaf_res(p.id, v.object_id, w.object_id, v_a);
          v_c := sheaf_res(p.id, u.object_id, w.object_id, s.label);
          IF v_b IS NOT NULL AND v_c IS NOT NULL AND v_b <> v_c THEN
            reason := 'restriction_composition';
            details := jsonb_build_object('from', u.object_id, 'via', v.object_id,
                                          'to', w.object_id, 'section', s.label);
            RETURN NEXT; v_found := TRUE;
          END IF;
        END LOOP;
      END LOOP;
    END LOOP;
  END LOOP;
  IF v_found THEN
    RETURN;
  END IF;

  -- the sheaf condition
  v_empty := sheaf_open_at(p.site_id, '{}'::text[]);
  SELECT count(*) INTO v_n FROM presheaf_section x
   WHERE x.presheaf_id = p.id AND x.open_object_id = v_empty;
  IF v_n <> 1 THEN
    reason := 'sheaf_empty_open';
    details := jsonb_build_object('count', v_n);
    RETURN NEXT;
  END IF;
  FOR c IN SELECT sc.id FROM site_cover sc WHERE sc.site_id = p.site_id ORDER BY sc.name LOOP
    v_n := sheaf_locality_failures(p.id, c.id);
    IF v_n > 0 THEN
      reason := 'sheaf_locality';
      details := jsonb_build_object('cover', c.id, 'count', v_n);
      RETURN NEXT;
    END IF;
    v_n := sheaf_gluing_failures(p.id, c.id);
    IF v_n > 0 THEN
      reason := 'sheaf_gluing';
      details := jsonb_build_object('cover', c.id, 'count', v_n);
      RETURN NEXT;
    END IF;
  END LOOP;
  FOR g IN SELECT x.* FROM cohomology_group x
            WHERE x.presheaf_id = p.id AND x.degree = 0 AND x.site_cover_id IS NOT NULL
            ORDER BY x.id LOOP
    SELECT count(*) INTO v_n FROM sheaf_compatible_families(p.id, g.site_cover_id);
    IF (g.group_descriptor ->> 'cardinality')::int <> v_n THEN
      reason := 'cohomology_h0_mismatch';
      details := jsonb_build_object('cover', g.site_cover_id,
                                    'recorded', (g.group_descriptor -> 'cardinality'),
                                    'computed', v_n);
      RETURN NEXT;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION sheaf_record(p_site UUID, p_presheaf UUID, p_reason TEXT,
                                        p_details JSONB)
RETURNS VOID AS $$
BEGIN
  INSERT INTO sheaf_cohomology_obstruction (site_id, presheaf_id, degree, reason, details)
  VALUES (p_site, p_presheaf,
          CASE WHEN p_reason IN ('cohomology_typing', 'cochain_typing')
                 THEN (p_details ->> 'degree')::int
               WHEN p_reason IN ('sheaf_empty_open', 'sheaf_locality', 'sheaf_gluing',
                                 'cohomology_h0_mismatch')
                 THEN 0
          END,
          p_reason, p_details);
END;
$$ LANGUAGE plpgsql;

-- All checks of one site; logs every problem, raises in strict mode.
CREATE OR REPLACE FUNCTION check_site(p_site UUID) RETURNS BOOLEAN AS $$
DECLARE
  pr RECORD;
  n_problems INT := 0;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM site s WHERE s.id = p_site) THEN
    RAISE EXCEPTION 'check_site: site % not found', p_site;
  END IF;
  FOR pr IN SELECT * FROM sheaf_site_problems(p_site) LOOP
    PERFORM sheaf_record(p_site, NULL, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Site % is not a valid finite site (% problem(s))', p_site, n_problems;
  END IF;
  RETURN n_problems = 0;
END;
$$ LANGUAGE plpgsql;

-- All checks of one presheaf; logs every problem, records the verdict in
-- presheaf.is_sheaf, raises in strict mode.  Returns the verdict.
CREATE OR REPLACE FUNCTION check_sheaf_condition(p_presheaf_id UUID)
RETURNS BOOLEAN AS $$
DECLARE
  p RECORD;
  pr RECORD;
  n_problems INT := 0;
BEGIN
  SELECT ps.* INTO p FROM presheaf ps WHERE ps.id = p_presheaf_id;
  IF p.id IS NULL THEN
    RAISE EXCEPTION 'check_sheaf_condition: presheaf % not found', p_presheaf_id;
  END IF;
  FOR pr IN SELECT * FROM sheaf_presheaf_problems(p_presheaf_id) LOOP
    PERFORM sheaf_record(p.site_id, p.id, pr.reason, pr.details);
    n_problems := n_problems + 1;
  END LOOP;
  PERFORM set_config('qbx.sheaf_checker', 'on', true);
  UPDATE presheaf SET is_sheaf = (n_problems = 0) WHERE id = p.id;
  PERFORM set_config('qbx.sheaf_checker', 'off', true);
  IF n_problems > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION 'Presheaf % is not a sheaf (% problem(s))', p_presheaf_id, n_problems;
  END IF;
  RETURN n_problems = 0;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
-- Canonical point sets.
CREATE OR REPLACE FUNCTION trg_site_open_points() RETURNS trigger AS $$
BEGIN
  NEW.points := sheaf_pts(NEW.points);
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_site_open_points ON site_open;
CREATE TRIGGER trg_site_open_points
BEFORE INSERT OR UPDATE ON site_open
FOR EACH ROW EXECUTE FUNCTION trg_site_open_points();

-- is_sheaf can only be set by check_sheaf_condition.
CREATE OR REPLACE FUNCTION trg_presheaf_flag() RETURNS trigger AS $$
BEGIN
  IF NEW.is_sheaf AND coalesce(current_setting('qbx.sheaf_checker', true), '') <> 'on' THEN
    NEW.is_sheaf := FALSE;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_presheaf_flag ON presheaf;
CREATE TRIGGER trg_presheaf_flag
BEFORE INSERT OR UPDATE ON presheaf
FOR EACH ROW EXECUTE FUNCTION trg_presheaf_flag();

-- Any change to a presheaf's data, or to its site, resets is_sheaf.
CREATE OR REPLACE FUNCTION trg_sheaf_invalidate_presheaf() RETURNS trigger AS $$
BEGIN
  IF TG_OP <> 'INSERT' THEN
    UPDATE presheaf SET is_sheaf = FALSE WHERE id = OLD.presheaf_id AND is_sheaf;
  END IF;
  IF TG_OP <> 'DELETE' THEN
    UPDATE presheaf SET is_sheaf = FALSE WHERE id = NEW.presheaf_id AND is_sheaf;
  END IF;
  RETURN NULL;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION trg_sheaf_invalidate_site() RETURNS trigger AS $$
BEGIN
  IF TG_OP <> 'INSERT' THEN
    UPDATE presheaf SET is_sheaf = FALSE WHERE site_id = OLD.site_id AND is_sheaf;
  END IF;
  IF TG_OP <> 'DELETE' THEN
    UPDATE presheaf SET is_sheaf = FALSE WHERE site_id = NEW.site_id AND is_sheaf;
  END IF;
  RETURN NULL;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_sheaf_invalidate ON presheaf_section;
CREATE TRIGGER trg_sheaf_invalidate AFTER INSERT OR UPDATE OR DELETE ON presheaf_section
FOR EACH ROW EXECUTE FUNCTION trg_sheaf_invalidate_presheaf();
DROP TRIGGER IF EXISTS trg_sheaf_invalidate ON presheaf_restriction;
CREATE TRIGGER trg_sheaf_invalidate AFTER INSERT OR UPDATE OR DELETE ON presheaf_restriction
FOR EACH ROW EXECUTE FUNCTION trg_sheaf_invalidate_presheaf();
DROP TRIGGER IF EXISTS trg_sheaf_invalidate ON cohomology_group;
CREATE TRIGGER trg_sheaf_invalidate AFTER INSERT OR UPDATE OR DELETE ON cohomology_group
FOR EACH ROW EXECUTE FUNCTION trg_sheaf_invalidate_presheaf();
DROP TRIGGER IF EXISTS trg_sheaf_invalidate ON cech_complex;
CREATE TRIGGER trg_sheaf_invalidate AFTER INSERT OR UPDATE OR DELETE ON cech_complex
FOR EACH ROW EXECUTE FUNCTION trg_sheaf_invalidate_presheaf();
DROP TRIGGER IF EXISTS trg_sheaf_invalidate ON site_open;
CREATE TRIGGER trg_sheaf_invalidate AFTER INSERT OR UPDATE OR DELETE ON site_open
FOR EACH ROW EXECUTE FUNCTION trg_sheaf_invalidate_site();
DROP TRIGGER IF EXISTS trg_sheaf_invalidate ON site_cover;
CREATE TRIGGER trg_sheaf_invalidate AFTER INSERT OR UPDATE OR DELETE ON site_cover
FOR EACH ROW EXECUTE FUNCTION trg_sheaf_invalidate_site();
DROP TRIGGER IF EXISTS trg_sheaf_invalidate ON cover;
CREATE TRIGGER trg_sheaf_invalidate AFTER INSERT OR UPDATE OR DELETE ON cover
FOR EACH ROW EXECUTE FUNCTION trg_sheaf_invalidate_site();

-- A cover row without a cover joins the site's cover 'default' of the base.
CREATE OR REPLACE FUNCTION trg_cover_default() RETURNS trigger AS $$
DECLARE
  v_id UUID;
BEGIN
  IF NEW.site_cover_id IS NULL THEN
    INSERT INTO site_cover (site_id, name, covered_object_id)
    SELECT NEW.site_id, 'default', s.base_space_object_id FROM site s WHERE s.id = NEW.site_id
    ON CONFLICT (site_id, name) DO NOTHING;
    SELECT sc.id INTO v_id FROM site_cover sc
     WHERE sc.site_id = NEW.site_id AND sc.name = 'default';
    NEW.site_cover_id := v_id;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_cover_default ON cover;
CREATE TRIGGER trg_cover_default
BEFORE INSERT OR UPDATE ON cover
FOR EACH ROW EXECUTE FUNCTION trg_cover_default();

-- Typing at write time: log, and raise in strict mode.
CREATE OR REPLACE FUNCTION sheaf_write_check(p_site UUID, p_presheaf UUID, p_problems JSONB,
                                             p_what TEXT)
RETURNS VOID AS $$
DECLARE
  e JSONB;
BEGIN
  IF p_problems IS NULL OR jsonb_array_length(p_problems) = 0 THEN
    RETURN;
  END IF;
  FOR e IN SELECT * FROM jsonb_array_elements(p_problems) LOOP
    PERFORM sheaf_record(p_site, p_presheaf, e ->> 'reason', e -> 'details');
  END LOOP;
  IF functor_is_strict() THEN
    RAISE EXCEPTION '% is not well typed (%)', p_what, p_problems -> 0 ->> 'reason';
  END IF;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION trg_check_cover_member() RETURNS trigger AS $$
DECLARE
  sc RECORD;
  v_cov TEXT[];
  v_pm TEXT[];
BEGIN
  SELECT c.* INTO sc FROM site_cover c WHERE c.id = NEW.site_cover_id;
  v_cov := sheaf_open_pts(sc.site_id, sc.covered_object_id);
  v_pm := sheaf_open_pts(sc.site_id, NEW.open_set_object_id);
  IF sc.site_id IS DISTINCT FROM NEW.site_id OR v_pm IS NULL
     OR (v_cov IS NOT NULL AND NOT (v_pm <@ v_cov)) THEN
    PERFORM sheaf_write_check(NEW.site_id, NULL, jsonb_build_array(jsonb_build_object(
      'reason', 'cover_typing',
      'details', jsonb_build_object('cover', NEW.site_cover_id, 'open', NEW.open_set_object_id))),
      'Cover member');
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_cover_member ON cover;
CREATE TRIGGER trg_check_cover_member
AFTER INSERT OR UPDATE ON cover
FOR EACH ROW EXECUTE FUNCTION trg_check_cover_member();

CREATE OR REPLACE FUNCTION trg_check_site_cover() RETURNS trigger AS $$
BEGIN
  IF sheaf_open_pts(NEW.site_id, NEW.covered_object_id) IS NULL THEN
    PERFORM sheaf_write_check(NEW.site_id, NULL, jsonb_build_array(jsonb_build_object(
      'reason', 'cover_typing',
      'details', jsonb_build_object('cover', NEW.id, 'open', NEW.covered_object_id))),
      'Cover');
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_site_cover ON site_cover;
CREATE TRIGGER trg_check_site_cover
AFTER INSERT OR UPDATE ON site_cover
FOR EACH ROW EXECUTE FUNCTION trg_check_site_cover();

-- Generic row trigger for the presheaf tables: TG_ARGV[0] names the typing function.
CREATE OR REPLACE FUNCTION trg_check_presheaf_row() RETURNS trigger AS $$
DECLARE
  v_problems JSONB;
  v_site UUID;
BEGIN
  EXECUTE format('SELECT coalesce(jsonb_agg(jsonb_build_object(''reason'', reason, '
                 '''details'', details)), ''[]''::jsonb) FROM %I($1)', TG_ARGV[0])
    INTO v_problems USING NEW.id;
  SELECT p.site_id INTO v_site FROM presheaf p WHERE p.id = NEW.presheaf_id;
  PERFORM sheaf_write_check(v_site, NEW.presheaf_id, v_problems, TG_ARGV[1]);
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_presheaf_section ON presheaf_section;
CREATE TRIGGER trg_check_presheaf_section
AFTER INSERT OR UPDATE ON presheaf_section
FOR EACH ROW EXECUTE FUNCTION trg_check_presheaf_row('sheaf_section_typing_problems', 'Section');

DROP TRIGGER IF EXISTS trg_check_presheaf_restriction ON presheaf_restriction;
CREATE TRIGGER trg_check_presheaf_restriction
AFTER INSERT OR UPDATE ON presheaf_restriction
FOR EACH ROW EXECUTE FUNCTION trg_check_presheaf_row('sheaf_restriction_typing_problems',
                                                     'Restriction');

DROP TRIGGER IF EXISTS trg_check_cohomology_group ON cohomology_group;
CREATE TRIGGER trg_check_cohomology_group
AFTER INSERT OR UPDATE ON cohomology_group
FOR EACH ROW EXECUTE FUNCTION trg_check_presheaf_row('sheaf_cohomology_typing_problems',
                                                     'Cohomology record');

DROP TRIGGER IF EXISTS trg_check_cech_complex ON cech_complex;
CREATE TRIGGER trg_check_cech_complex
AFTER INSERT OR UPDATE ON cech_complex
FOR EACH ROW EXECUTE FUNCTION trg_check_presheaf_row('sheaf_cochain_typing_problems',
                                                     'Cochain record');

-- Descent data: verified is computed, never trusted.
CREATE OR REPLACE FUNCTION trg_descent_verify() RETURNS trigger AS $$
BEGIN
  IF NEW.site_cover_id IS NULL AND NEW.cover_id IS NOT NULL THEN
    SELECT c.site_cover_id INTO NEW.site_cover_id FROM cover c WHERE c.id = NEW.cover_id;
  END IF;
  NEW.verified := sheaf_descent_verified(NEW.presheaf_id, NEW.site_cover_id, NEW.descent_cocycle);
  NEW.verified_at := CASE WHEN NEW.verified THEN now() END;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_descent_verify ON sheaf_descent_data;
CREATE TRIGGER trg_descent_verify
BEFORE INSERT OR UPDATE ON sheaf_descent_data
FOR EACH ROW EXECUTE FUNCTION trg_descent_verify();

-- ---------------------------------------------------------------------------
-- Writers.  Each refuses, in every mode, input it cannot build a well-typed
-- row from, and never replaces an existing row by a different one.  Rows
-- inserted directly are checked by the triggers and in batch.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION register_site(p_name TEXT, p_base UUID) RETURNS UUID AS $$
DECLARE
  ex RECORD;
  new_id UUID;
BEGIN
  SELECT s.* INTO ex FROM site s WHERE s.name = p_name;
  IF ex.id IS NOT NULL THEN
    IF ex.base_space_object_id IS NOT DISTINCT FROM p_base THEN
      RETURN ex.id;
    END IF;
    RAISE EXCEPTION 'register_site: site % already exists with another base', p_name;
  END IF;
  INSERT INTO site (name, base_space_object_id) VALUES (p_name, p_base) RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION register_site_open(p_site UUID, p_obj UUID, p_points TEXT[])
RETURNS UUID AS $$
DECLARE
  ex RECORD;
  v_pts TEXT[] := sheaf_pts(p_points);
  new_id UUID;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM site s WHERE s.id = p_site) THEN
    RAISE EXCEPTION 'register_site_open: site % not found', p_site;
  END IF;
  IF NOT EXISTS (SELECT 1 FROM object o WHERE o.id = p_obj) THEN
    RAISE EXCEPTION 'register_site_open: object % not found', p_obj;
  END IF;
  SELECT so.* INTO ex FROM site_open so WHERE so.site_id = p_site AND so.object_id = p_obj;
  IF ex.id IS NOT NULL THEN
    IF ex.points = v_pts THEN
      RETURN ex.id;
    END IF;
    RAISE EXCEPTION 'register_site_open: the object is already an open with other points';
  END IF;
  IF sheaf_open_at(p_site, v_pts) IS NOT NULL THEN
    RAISE EXCEPTION 'register_site_open: another open has the same points';
  END IF;
  INSERT INTO site_open (site_id, object_id, points) VALUES (p_site, p_obj, v_pts)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION register_site_cover(p_site UUID, p_name TEXT, p_covered UUID,
                                               p_members UUID[])
RETURNS UUID AS $$
DECLARE
  ex RECORD;
  v_cov TEXT[];
  v_pm TEXT[];
  v_members UUID[];
  m UUID;
  new_id UUID;
BEGIN
  v_members := coalesce(ARRAY(SELECT DISTINCT x FROM unnest(p_members) x ORDER BY 1),
                        '{}'::uuid[]);
  SELECT sc.* INTO ex FROM site_cover sc WHERE sc.site_id = p_site AND sc.name = p_name;
  IF ex.id IS NOT NULL THEN
    IF ex.covered_object_id IS NOT DISTINCT FROM p_covered
       AND sheaf_cover_members(ex.id) = v_members THEN
      RETURN ex.id;
    END IF;
    RAISE EXCEPTION 'register_site_cover: cover % already exists with other data', p_name;
  END IF;
  v_cov := sheaf_open_pts(p_site, p_covered);
  IF v_cov IS NULL THEN
    RAISE EXCEPTION 'register_site_cover: the covered set is not an open of the site';
  END IF;
  FOREACH m IN ARRAY v_members LOOP
    v_pm := sheaf_open_pts(p_site, m);
    IF v_pm IS NULL OR NOT (v_pm <@ v_cov) THEN
      RAISE EXCEPTION 'register_site_cover: member % is not an open inside the covered set', m;
    END IF;
  END LOOP;
  INSERT INTO site_cover (site_id, name, covered_object_id) VALUES (p_site, p_name, p_covered)
  RETURNING id INTO new_id;
  INSERT INTO cover (site_id, open_set_object_id, site_cover_id)
  SELECT p_site, x, new_id FROM unnest(v_members) x;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Register a presheaf with its sections: p_assignment = {open id: [labels]}.
CREATE OR REPLACE FUNCTION register_presheaf(
  p_site_id UUID, p_name TEXT, p_assignment JSONB
) RETURNS UUID AS $$
DECLARE
  k RECORD;
  v_obj UUID;
  new_id UUID;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM site s WHERE s.id = p_site_id) THEN
    RAISE EXCEPTION 'register_presheaf: site % not found', p_site_id;
  END IF;
  IF p_assignment IS NULL THEN
    p_assignment := '{}'::jsonb;
  END IF;
  IF jsonb_typeof(p_assignment) <> 'object' THEN
    RAISE EXCEPTION 'register_presheaf: the assignment is not an object';
  END IF;
  FOR k IN SELECT * FROM jsonb_each(p_assignment) LOOP
    SELECT so.object_id INTO v_obj FROM site_open so
     WHERE so.site_id = p_site_id AND so.object_id::text = lower(k.key);
    IF v_obj IS NULL THEN
      RAISE EXCEPTION 'register_presheaf: % is not an open of the site', k.key;
    END IF;
    IF jsonb_typeof(k.value) <> 'array'
       OR EXISTS (SELECT 1 FROM jsonb_array_elements(k.value) e
                   WHERE jsonb_typeof(e) <> 'string') THEN
      RAISE EXCEPTION 'register_presheaf: the sections over % are not a list of labels', k.key;
    END IF;
  END LOOP;
  INSERT INTO presheaf (site_id, name, assignment)
  VALUES (p_site_id, p_name, p_assignment)
  RETURNING id INTO new_id;
  INSERT INTO presheaf_section (presheaf_id, open_object_id, label)
  SELECT new_id, j.key::uuid, e
    FROM jsonb_each(p_assignment) j, jsonb_array_elements_text(j.value) e
  ON CONFLICT DO NOTHING;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Record res(from, to, section) = image.
CREATE OR REPLACE FUNCTION record_restriction(
  p_presheaf UUID, p_from UUID, p_to UUID, p_section TEXT, p_image TEXT
) RETURNS UUID AS $$
DECLARE
  p RECORD;
  ex RECORD;
  new_id UUID;
BEGIN
  SELECT ps.* INTO p FROM presheaf ps WHERE ps.id = p_presheaf;
  IF p.id IS NULL THEN
    RAISE EXCEPTION 'record_restriction: presheaf % not found', p_presheaf;
  END IF;
  SELECT r.* INTO ex FROM presheaf_restriction r
   WHERE r.presheaf_id = p_presheaf AND r.from_object_id = p_from AND r.to_object_id = p_to
     AND r.section = p_section;
  IF ex.id IS NOT NULL THEN
    IF ex.image = p_image THEN
      RETURN ex.id;
    END IF;
    RAISE EXCEPTION 'record_restriction: a different restriction is already recorded';
  END IF;
  IF NOT coalesce(sheaf_open_pts(p.site_id, p_to) <@ sheaf_open_pts(p.site_id, p_from), FALSE) THEN
    RAISE EXCEPTION 'record_restriction: the target is not an open inside the source';
  END IF;
  IF NOT sheaf_is_section(p_presheaf, p_from, p_section)
     OR NOT sheaf_is_section(p_presheaf, p_to, p_image) THEN
    RAISE EXCEPTION 'record_restriction: the section or the image is not a section';
  END IF;
  INSERT INTO presheaf_restriction (presheaf_id, from_object_id, to_object_id, section, image)
  VALUES (p_presheaf, p_from, p_to, p_section, p_image)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION sheaf_store_check(p_site UUID, p_presheaf UUID, p_degree INT,
                                             p_cover UUID, p_what TEXT)
RETURNS VOID AS $$
BEGIN
  IF NOT EXISTS (SELECT 1 FROM presheaf p WHERE p.id = p_presheaf AND p.site_id = p_site) THEN
    RAISE EXCEPTION '%: the presheaf is not a presheaf on the site', p_what;
  END IF;
  IF p_degree IS NULL OR p_degree < 0 THEN
    RAISE EXCEPTION '%: the degree must be non-negative', p_what;
  END IF;
  IF p_cover IS NOT NULL
     AND NOT EXISTS (SELECT 1 FROM site_cover sc WHERE sc.id = p_cover AND sc.site_id = p_site) THEN
    RAISE EXCEPTION '%: the cover is not a cover of the site', p_what;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- Store a Čech cochain record (computed elsewhere).
CREATE OR REPLACE FUNCTION store_cech_cochain(
  p_site_id UUID, p_presheaf_id UUID, p_degree INT, p_data JSONB, p_cover UUID
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  PERFORM sheaf_store_check(p_site_id, p_presheaf_id, p_degree, p_cover, 'store_cech_cochain');
  INSERT INTO cech_complex (site_id, presheaf_id, degree, data, site_cover_id)
  VALUES (p_site_id, p_presheaf_id, p_degree, coalesce(p_data, '{}'::jsonb), p_cover)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION store_cech_cochain(
  p_site_id UUID, p_presheaf_id UUID, p_degree INT, p_data JSONB
) RETURNS UUID AS $$
  SELECT store_cech_cochain(p_site_id, p_presheaf_id, p_degree, p_data, NULL::uuid);
$$ LANGUAGE sql;

-- Store a cohomology descriptor: {"cardinality": n} in degree 0 (checked in
-- batch against the compatible families when a cover is given), {"rank": r}
-- in degree ≥ 1.  One descriptor per (presheaf, cover, degree): storing the
-- same one again returns it, a different one is refused.
CREATE OR REPLACE FUNCTION store_cohomology_group(
  p_site_id UUID, p_presheaf_id UUID, p_degree INT, p_descriptor JSONB, p_cover UUID
) RETURNS UUID AS $$
DECLARE
  ex RECORD;
  new_id UUID;
BEGIN
  PERFORM sheaf_store_check(p_site_id, p_presheaf_id, p_degree, p_cover,
                            'store_cohomology_group');
  IF NOT sheaf_nonneg_int(p_descriptor -> CASE WHEN p_degree = 0 THEN 'cardinality'
                                               ELSE 'rank' END) THEN
    RAISE EXCEPTION 'store_cohomology_group: the descriptor needs a non-negative integer %',
      CASE WHEN p_degree = 0 THEN 'cardinality' ELSE 'rank' END;
  END IF;
  SELECT g.* INTO ex FROM cohomology_group g
   WHERE g.presheaf_id = p_presheaf_id AND g.degree = p_degree
     AND g.site_cover_id IS NOT DISTINCT FROM p_cover
   ORDER BY g.computed_at, g.id LIMIT 1;
  IF ex.id IS NOT NULL THEN
    IF ex.group_descriptor = p_descriptor THEN
      RETURN ex.id;
    END IF;
    RAISE EXCEPTION 'store_cohomology_group: a different descriptor is already stored';
  END IF;
  INSERT INTO cohomology_group (site_id, presheaf_id, degree, group_descriptor, site_cover_id)
  VALUES (p_site_id, p_presheaf_id, p_degree, p_descriptor, p_cover)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION store_cohomology_group(
  p_site_id UUID, p_presheaf_id UUID, p_degree INT, p_descriptor JSONB
) RETURNS UUID AS $$
  SELECT store_cohomology_group(p_site_id, p_presheaf_id, p_degree, p_descriptor, NULL::uuid);
$$ LANGUAGE sql;

-- Record a manual obstruction (reason 'obstruction').
CREATE OR REPLACE FUNCTION store_sheaf_obstruction(
  p_site_id UUID, p_presheaf_id UUID, p_degree INT, p_details JSONB
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  INSERT INTO sheaf_cohomology_obstruction (site_id, presheaf_id, degree, reason, details)
  VALUES (p_site_id, p_presheaf_id, p_degree, 'obstruction', p_details)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Record a descent datum on a cover; returns whether it is verified.
CREATE OR REPLACE FUNCTION verify_descent(p_presheaf UUID, p_cover UUID, p_family JSONB)
RETURNS BOOLEAN AS $$
DECLARE
  v BOOLEAN;
BEGIN
  INSERT INTO sheaf_descent_data (presheaf_id, site_cover_id, descent_cocycle)
  VALUES (p_presheaf, p_cover, p_family)
  RETURNING verified INTO v;
  RETURN v;
END;
$$ LANGUAGE plpgsql;
