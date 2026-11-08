-- ============================================================================
-- Categorical Ledger — Migration 014: Hebrew Primacy
-- ============================================================================
-- Hebrew letters, the gematria functor and its naturality obligations, Torah
-- sites (sections of a sheaf) and language adjunctions, following the skill
-- agents/skills/hebrew_primacy_rules.md (rules R1–R7).  The Python reference is
-- qbx.hebrew (text, functor, torah): every *_problems function below reports
-- the same problems, with the same details, as the Python function it names.
--
-- Recording.
--   hebrew_letter        the seeded 27 letters (22 letters, then the final
--                        forms ך ם ן ף ץ at 500–900; R7): letter, value,
--                        ordinal 1–27, is_final.  hebrew_seed_letters() is the
--                        seed; the table must stay equal to it (changing it
--                        needs approval: escalation rule gematria_functor_change).
--   hebrew_word          a word: NFC text of letters and Hebrew marks (Mn in
--                        U+0591–U+05C7, each following a letter); root (letters
--                        only); total_gematria, recomputed by a trigger on
--                        every write; embedding_vector, when stored, must be
--                        gematria_vector(text) (R4; store_hebrew_embedding).
--   gematria_functor     a gematria scheme from base_category_id (words) to
--                        target_category_id (numbers): mapping_rules {} is the
--                        seeded table, otherwise exactly the 27 letters, each
--                        with a non-negative integer value ≤ 2³¹ − 1 (R1, R3).
--   gematria_obligation  a naturality obligation of a functor (R2): values
--                        claimed for u, w and u ++ w.
--   torah_site           a corpus as a sheaf (R5): site_id, a finite site of
--                        migration 012 whose points are verse references, and
--                        presheaf_id, a presheaf on it (build_torah_presheaf
--                        builds the passage presheaf).
--   torah_section        the text of one verse: verse_ref "<book> <ch>:<v>"
--                        (a Torah book, English or Hebrew name; chapter within
--                        the book; verse 1–999); section_text is NFC Hebrew
--                        (letters, marks, space, ־ ׀ ׃ ׆ ׳ ״).
--   language_adjunction  a language adjunction: languages, its functor, an
--                        optional adjunction of migration 005; status
--                        'provisional' (the default) or 'lean_verified', which
--                        needs a proof artifact of type 'lean4' (R6).
--   hebrew_violation     the violation table (subject_table, subject_id,
--                        reason, details).
--
-- Checks.  Every check logs to hebrew_violation and raises only when
-- qbx.enforcement_mode = 'strict'.  Rows are checked when written (triggers)
-- and in batch (check_hebrew and the check_* functions, run_all_batch_checks);
-- the checks marked "batch" need other rows and run only in batch.
-- Offsets count code points from 0; code points are written U+XXXX.
--   hebrew_letter (statement trigger; hebrew_letter_table_problems)
--     letter_missing        a seeded letter has no row (details: letter)
--     letter_value          a field differs from the seed (details: letter,
--                           field ∈ gematria_value, ordinal, is_final,
--                           expected, found)
--     letter_unknown        a row for something else (details: letter)
--   hebrew_word (hebrew_word_problems)
--     word_typing           error ∈ empty, non_nfc, character (offset,
--                           codepoint), leading_mark (offset), no_letter
--     root_typing           error ∈ empty, character (offset, codepoint)
--     gematria_mismatch     total_gematria is not the seeded value of the text
--                           (details: recorded, computed)
--     embedding_mismatch    the first component differing from
--                           gematria_vector(text) (details: index)
--   gematria_functor (gematria_functor_problems)
--     functor_typing        error ∈ base_category, target_category,
--                           same_category
--     functor_rules         error ∈ not_object, unknown_letter (key), value
--                           (key), missing (letter)
--     naturality_missing    batch: no recorded obligation
--   gematria_obligation (gematria_obligation_problems)
--     obligation_typing     error ∈ left, right (not a word), rules (the
--                           functor's rules are invalid)
--     naturality_value      a recorded value is not the functor's value
--                           (details: which ∈ left, right, concat, recorded,
--                           computed)
--     naturality_square     left + right ≠ concat as recorded (details: left,
--                           right, concat)
--   torah_site (torah_site_problems)
--     torah_no_site         no site
--     torah_no_presheaf     batch: no presheaf (a site under construction has
--                           none yet; build_torah_presheaf links one)
--     torah_presheaf_typing the presheaf is on another site (details: presheaf)
--     torah_not_sheaf       batch: check_sheaf_condition fails (details:
--                           presheaf; the presheaf's own problems are logged
--                           by migration 012)
--     torah_section_mismatch batch: a verse whose singleton {verse} is an open
--                           and whose sections there are not exactly the label
--                           {"verse":"text"} (details: verse)
--   torah_section (torah_section_problems)
--     verse_ref_format      error ∈ syntax, book, chapter
--     verse_not_point       the site has no point with this reference
--     section_text_typing   as word_typing, punctuation allowed
--   language_adjunction (language_adjunction_problems)
--     language_typing       error ∈ left, right (blank), same
--     adjunction_mismatch   the functor is neither adjoint of the adjunction
--     status_value          the status is not provisional / lean_verified
--                           (details: status)
--     unverified_claim      lean_verified without a lean4 proof artifact
--                           (details: error ∈ no_artifact, artifact_type
--                           (found))
--
-- Writers (register_hebrew_word, register_gematria_functor,
-- record_gematria_obligation, register_torah_site, register_torah_section,
-- register_language_adjunction) refuse input with any write-time problem.
--
-- Formal backing (Formal/Gematria.lean): the value of a word is a monoid
-- homomorphism from words to (ℕ, +) for every scheme (wordValue_append,
-- gemHom_toAdd), determined by the 27 letter values (additive_eq_wordValue) —
-- so checking mapping_rules checks the functor; a failed square implies a
-- wrong value (obligation_value_mismatch_of_square); the seeded values are
-- pairwise distinct, finals included (standard_injective, final_ne_base);
-- gematria does not identify words (wordValue_not_injective); the passage
-- presheaf is a sheaf with at most one section per open, present exactly when
-- every verse of the open has a text (textSheaf_locality_and_gluing,
-- textSheaf_subsingleton, textSheaf_nonempty_iff).
--
-- Phase 1 sprint 11 rewrite.  Running the original on PostgreSQL 16 showed:
--   * UPDATE hebrew_word SET total_gematria = 1 was accepted and kept (the
--     trigger recomputed the total only on UPDATE OF text);
--   * compute_gematria was declared IMMUTABLE but reads hebrew_letter, which
--     could be changed freely (א set to 7, a row 'X' with value −5); totals
--     written before the change were never revisited;
--   * any text was a word: 'hello world 123' and the root '!!' were accepted
--     with total 0, and the presentation form U+FB2A (שׁ) counted 0 while its
--     NFC form counts 300;
--   * a stored embedding was never compared with gematria_vector (any vector
--     was accepted);
--   * register_gematria_functor accepted rules {"א": -3, "zz": "x"} and no
--     categories, and no naturality obligation could be recorded (R2);
--   * torah sites were not connected to any site or presheaf, and a section
--     'nonsense 999' with text 'abc' was accepted (R5);
--   * language adjunctions had no status (R6), a left and right language could
--     be equal, and the adjunction need not involve the functor;
--   * nothing was checked, logged, or part of run_all_batch_checks.
-- ============================================================================

CREATE TABLE IF NOT EXISTS hebrew_letter (
  id SERIAL PRIMARY KEY,
  letter TEXT NOT NULL UNIQUE,
  gematria_value INT NOT NULL,
  ordinal INT NOT NULL,
  is_final BOOLEAN DEFAULT FALSE,
  metadata JSONB DEFAULT '{}'::jsonb
);

-- The seed: 22 letters (mispar hechrachi), then the five final forms (500–900).
CREATE OR REPLACE FUNCTION hebrew_seed_letters()
RETURNS TABLE(letter TEXT, gematria_value INT, ordinal INT, is_final BOOLEAN) AS $$
  SELECT * FROM (VALUES
    ('א', 1,   1,  FALSE), ('ב', 2,   2,  FALSE), ('ג', 3,   3,  FALSE),
    ('ד', 4,   4,  FALSE), ('ה', 5,   5,  FALSE), ('ו', 6,   6,  FALSE),
    ('ז', 7,   7,  FALSE), ('ח', 8,   8,  FALSE), ('ט', 9,   9,  FALSE),
    ('י', 10,  10, FALSE), ('כ', 20,  11, FALSE), ('ל', 30,  12, FALSE),
    ('מ', 40,  13, FALSE), ('נ', 50,  14, FALSE), ('ס', 60,  15, FALSE),
    ('ע', 70,  16, FALSE), ('פ', 80,  17, FALSE), ('צ', 90,  18, FALSE),
    ('ק', 100, 19, FALSE), ('ר', 200, 20, FALSE), ('ש', 300, 21, FALSE),
    ('ת', 400, 22, FALSE),
    ('ך', 500, 23, TRUE),  ('ם', 600, 24, TRUE),  ('ן', 700, 25, TRUE),
    ('ף', 800, 26, TRUE),  ('ץ', 900, 27, TRUE)
  ) AS s(letter, gematria_value, ordinal, is_final);
$$ LANGUAGE sql IMMUTABLE;

INSERT INTO hebrew_letter (letter, gematria_value, ordinal, is_final)
SELECT s.letter, s.gematria_value, s.ordinal, s.is_final FROM hebrew_seed_letters() s
ON CONFLICT (letter) DO NOTHING;

CREATE TABLE IF NOT EXISTS hebrew_word (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  text TEXT NOT NULL,
  root TEXT,
  total_gematria INT,
  object_id UUID REFERENCES object(id) ON DELETE SET NULL,
  embedding_vector vector(256),
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_hebrew_word_text ON hebrew_word (text);

CREATE TABLE IF NOT EXISTS gematria_functor (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  base_category_id UUID REFERENCES category(id) ON DELETE CASCADE,
  target_category_id UUID REFERENCES category(id) ON DELETE CASCADE,
  mapping_rules JSONB DEFAULT '{}'::jsonb,
  embedding_model TEXT,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS gematria_obligation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  functor_id UUID NOT NULL REFERENCES gematria_functor(id) ON DELETE CASCADE,
  left_text TEXT NOT NULL,
  right_text TEXT NOT NULL,
  left_value BIGINT NOT NULL,
  right_value BIGINT NOT NULL,
  concat_value BIGINT NOT NULL,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_gematria_obligation_functor ON gematria_obligation (functor_id);

CREATE TABLE IF NOT EXISTS torah_site (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  base_object_id UUID REFERENCES object(id) ON DELETE SET NULL,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);
ALTER TABLE torah_site ADD COLUMN IF NOT EXISTS
  site_id UUID REFERENCES site(id) ON DELETE SET NULL;
ALTER TABLE torah_site ADD COLUMN IF NOT EXISTS
  presheaf_id UUID REFERENCES presheaf(id) ON DELETE SET NULL;

CREATE TABLE IF NOT EXISTS torah_section (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  site_id UUID NOT NULL REFERENCES torah_site(id) ON DELETE CASCADE,
  verse_ref TEXT NOT NULL,
  section_text TEXT,
  metadata JSONB DEFAULT '{}'::jsonb,
  UNIQUE (site_id, verse_ref)
);

CREATE TABLE IF NOT EXISTS language_adjunction (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  left_language TEXT NOT NULL,
  right_language TEXT NOT NULL,
  functor_id UUID NOT NULL REFERENCES functor(id) ON DELETE CASCADE,
  adjunction_id UUID REFERENCES adjunction(id) ON DELETE SET NULL,
  metadata JSONB DEFAULT '{}'::jsonb
);
ALTER TABLE language_adjunction ADD COLUMN IF NOT EXISTS
  status TEXT NOT NULL DEFAULT 'provisional';
ALTER TABLE language_adjunction ADD COLUMN IF NOT EXISTS
  proof_artifact_id UUID REFERENCES proof_artifact(id) ON DELETE SET NULL;

CREATE TABLE IF NOT EXISTS hebrew_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  subject_table TEXT NOT NULL,
  subject_id UUID,
  reason TEXT NOT NULL,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_hebrew_violation_subject
  ON hebrew_violation (subject_table, subject_id, detected_at DESC);

-- ---------------------------------------------------------------------------
-- Gematria
-- ---------------------------------------------------------------------------
-- The value of a word under the registered table (non-letters count 0; NULL
-- counts 0).  STABLE: it reads hebrew_letter.
CREATE OR REPLACE FUNCTION compute_gematria(p_word TEXT) RETURNS INT AS $$
  SELECT coalesce(sum(l.gematria_value), 0)::int
    FROM unnest(string_to_array(p_word, NULL)) AS ch
    JOIN hebrew_letter l ON l.letter = ch;
$$ LANGUAGE sql STABLE;

-- The value of a word under the seed (what the checks compare with).
CREATE OR REPLACE FUNCTION hebrew_seed_value(p_word TEXT) RETURNS BIGINT AS $$
  SELECT coalesce(sum(s.gematria_value), 0)::bigint
    FROM unnest(string_to_array(p_word, NULL)) AS ch
    JOIN hebrew_seed_letters() s ON s.letter = ch;
$$ LANGUAGE sql IMMUTABLE;

-- gematria_vector(text, 256) (qbx.hebrew.gematria, rule R4): byte i of
-- SHA-256(decimal value) (repeated), mapped to (b − 128) / 128.
CREATE OR REPLACE FUNCTION hebrew_gematria_vector(p_word TEXT) RETURNS REAL[] AS $$
  SELECT array_agg(((get_byte(d, i % 32) - 128)::real / 128) ORDER BY i)
    FROM (SELECT sha256(convert_to(hebrew_seed_value(p_word)::text, 'UTF8')) AS d) x,
         generate_series(0, 255) AS i;
$$ LANGUAGE sql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Text checks (qbx.hebrew.text)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION hebrew_codepoint(p_ch TEXT) RETURNS TEXT AS $$
  SELECT 'U+' || CASE WHEN length(h) < 4 THEN lpad(h, 4, '0') ELSE h END
    FROM (SELECT upper(to_hex(ascii(p_ch))) AS h) x;
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION hebrew_is_letter(p_ch TEXT) RETURNS BOOLEAN AS $$
  SELECT EXISTS (SELECT 1 FROM hebrew_seed_letters() s WHERE s.letter = p_ch);
$$ LANGUAGE sql IMMUTABLE;

-- Hebrew combining marks: general category Mn in U+0591–U+05C7.
CREATE OR REPLACE FUNCTION hebrew_is_mark(p_ch TEXT) RETURNS BOOLEAN AS $$
  SELECT ascii(p_ch) BETWEEN 1425 AND 1469 OR ascii(p_ch) IN (1471, 1473, 1474, 1476, 1477, 1479);
$$ LANGUAGE sql IMMUTABLE;

-- Punctuation of a verse text: space, ־ ׀ ׃ ׆ ׳ ״.
CREATE OR REPLACE FUNCTION hebrew_is_verse_punct(p_ch TEXT) RETURNS BOOLEAN AS $$
  SELECT ascii(p_ch) IN (32, 1470, 1472, 1475, 1478, 1523, 1524);
$$ LANGUAGE sql IMMUTABLE;

-- qbx.hebrew.text.letter_table_problems
CREATE OR REPLACE FUNCTION hebrew_letter_table_problems()
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  s RECORD;
  r RECORD;
BEGIN
  FOR s IN SELECT * FROM hebrew_seed_letters() x ORDER BY x.ordinal LOOP
    SELECT l.* INTO r FROM hebrew_letter l WHERE l.letter = s.letter;
    IF NOT FOUND THEN
      reason := 'letter_missing'; details := jsonb_build_object('letter', s.letter); RETURN NEXT;
      CONTINUE;
    END IF;
    reason := 'letter_value';
    IF r.gematria_value IS DISTINCT FROM s.gematria_value THEN
      details := jsonb_build_object('letter', s.letter, 'field', 'gematria_value',
                                    'expected', s.gematria_value, 'found', r.gematria_value);
      RETURN NEXT;
    END IF;
    IF r.ordinal IS DISTINCT FROM s.ordinal THEN
      details := jsonb_build_object('letter', s.letter, 'field', 'ordinal',
                                    'expected', s.ordinal, 'found', r.ordinal);
      RETURN NEXT;
    END IF;
    IF r.is_final IS DISTINCT FROM s.is_final THEN
      details := jsonb_build_object('letter', s.letter, 'field', 'is_final',
                                    'expected', s.is_final, 'found', r.is_final);
      RETURN NEXT;
    END IF;
  END LOOP;
  FOR r IN SELECT l.letter FROM hebrew_letter l
            WHERE NOT hebrew_is_letter(l.letter) ORDER BY l.letter COLLATE "C" LOOP
    reason := 'letter_unknown'; details := jsonb_build_object('letter', r.letter); RETURN NEXT;
  END LOOP;
END;
$$ LANGUAGE plpgsql STABLE;

-- qbx.hebrew.text.text_problems: p_kind 'word' (word_typing) or 'verse'
-- (section_text_typing).
CREATE OR REPLACE FUNCTION hebrew_text_problems(p_text TEXT, p_kind TEXT DEFAULT 'word')
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  ch TEXT;
  attached BOOLEAN := FALSE;
  n_letters INT := 0;
BEGIN
  reason := CASE WHEN p_kind = 'word' THEN 'word_typing' ELSE 'section_text_typing' END;
  IF p_text IS NULL OR p_text = '' THEN
    details := jsonb_build_object('error', 'empty'); RETURN NEXT; RETURN;
  END IF;
  IF NOT (p_text IS NFC NORMALIZED) THEN
    details := jsonb_build_object('error', 'non_nfc'); RETURN NEXT; RETURN;
  END IF;
  FOR i IN 1 .. char_length(p_text) LOOP
    ch := substr(p_text, i, 1);
    IF hebrew_is_letter(ch) THEN
      n_letters := n_letters + 1;
      attached := TRUE;
    ELSIF hebrew_is_mark(ch) THEN
      IF NOT attached THEN
        details := jsonb_build_object('error', 'leading_mark', 'offset', i - 1); RETURN NEXT;
      END IF;
    ELSIF p_kind <> 'word' AND hebrew_is_verse_punct(ch) THEN
      attached := FALSE;
    ELSE
      details := jsonb_build_object('error', 'character', 'offset', i - 1,
                                    'codepoint', hebrew_codepoint(ch));
      RETURN NEXT;
      attached := FALSE;
    END IF;
  END LOOP;
  IF n_letters = 0 THEN
    details := jsonb_build_object('error', 'no_letter'); RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- qbx.hebrew.text.root_problems
CREATE OR REPLACE FUNCTION hebrew_root_problems(p_root TEXT)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  ch TEXT;
BEGIN
  IF p_root IS NULL THEN RETURN; END IF;
  reason := 'root_typing';
  IF p_root = '' THEN
    details := jsonb_build_object('error', 'empty'); RETURN NEXT; RETURN;
  END IF;
  FOR i IN 1 .. char_length(p_root) LOOP
    ch := substr(p_root, i, 1);
    IF NOT hebrew_is_letter(ch) THEN
      details := jsonb_build_object('error', 'character', 'offset', i - 1,
                                    'codepoint', hebrew_codepoint(ch));
      RETURN NEXT;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- qbx.hebrew.text.word_row_problems
CREATE OR REPLACE FUNCTION hebrew_word_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
  computed BIGINT;
  got REAL[];
  exp REAL[];
BEGIN
  SELECT w.* INTO r FROM hebrew_word w WHERE w.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM hebrew_text_problems(r.text, 'word');
  RETURN QUERY SELECT * FROM hebrew_root_problems(r.root);
  computed := hebrew_seed_value(r.text);
  IF r.total_gematria IS DISTINCT FROM computed THEN
    reason := 'gematria_mismatch';
    details := jsonb_build_object('recorded', r.total_gematria, 'computed', computed);
    RETURN NEXT;
  END IF;
  IF r.embedding_vector IS NOT NULL THEN
    got := r.embedding_vector::real[];
    exp := hebrew_gematria_vector(r.text);
    FOR i IN 1 .. 256 LOOP
      IF got[i] IS DISTINCT FROM exp[i] THEN
        reason := 'embedding_mismatch'; details := jsonb_build_object('index', i - 1);
        RETURN NEXT;
        EXIT;
      END IF;
    END LOOP;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Gematria functors (qbx.hebrew.functor)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION gematria_rule_value_ok(v JSONB) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(v) = 'number'
                  AND (v::text)::numeric = trunc((v::text)::numeric)
                  AND (v::text)::numeric BETWEEN 0 AND 2147483647, FALSE);
$$ LANGUAGE sql IMMUTABLE;

-- qbx.hebrew.functor.rules_problems
CREATE OR REPLACE FUNCTION gematria_rules_problems(p_rules JSONB)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  k RECORD;
  s RECORD;
BEGIN
  reason := 'functor_rules';
  IF p_rules IS NULL OR jsonb_typeof(p_rules) <> 'object' THEN
    details := jsonb_build_object('error', 'not_object'); RETURN NEXT; RETURN;
  END IF;
  IF p_rules = '{}'::jsonb THEN RETURN; END IF;
  FOR k IN SELECT j.key, j.value FROM jsonb_each(p_rules) j ORDER BY j.key COLLATE "C" LOOP
    IF NOT hebrew_is_letter(k.key) THEN
      details := jsonb_build_object('error', 'unknown_letter', 'key', k.key); RETURN NEXT;
    ELSIF NOT gematria_rule_value_ok(k.value) THEN
      details := jsonb_build_object('error', 'value', 'key', k.key); RETURN NEXT;
    END IF;
  END LOOP;
  FOR s IN SELECT x.letter FROM hebrew_seed_letters() x ORDER BY x.ordinal LOOP
    IF NOT p_rules ? s.letter THEN
      details := jsonb_build_object('error', 'missing', 'letter', s.letter); RETURN NEXT;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- The value of a word under a scheme; NULL when the rules are invalid.
CREATE OR REPLACE FUNCTION gematria_rules_value(p_rules JSONB, p_text TEXT) RETURNS BIGINT AS $$
  SELECT CASE
    WHEN p_text IS NULL OR EXISTS (SELECT 1 FROM gematria_rules_problems(p_rules)) THEN NULL
    WHEN p_rules = '{}'::jsonb THEN hebrew_seed_value(p_text)
    ELSE (SELECT coalesce(sum(((p_rules ->> ch)::numeric)::bigint), 0)::bigint
            FROM unnest(string_to_array(p_text, NULL)) AS ch
           WHERE p_rules ? ch)
  END;
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION gematria_functor_value(p_functor UUID, p_text TEXT) RETURNS BIGINT AS $$
  SELECT gematria_rules_value(g.mapping_rules, p_text) FROM gematria_functor g WHERE g.id = p_functor;
$$ LANGUAGE sql STABLE;

-- qbx.hebrew.functor.functor_problems (p_batch: naturality_missing too)
CREATE OR REPLACE FUNCTION gematria_functor_problems(p_id UUID, p_batch BOOLEAN DEFAULT TRUE)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT g.* INTO r FROM gematria_functor g WHERE g.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  reason := 'functor_typing';
  IF r.base_category_id IS NULL THEN
    details := jsonb_build_object('error', 'base_category'); RETURN NEXT;
  END IF;
  IF r.target_category_id IS NULL THEN
    details := jsonb_build_object('error', 'target_category'); RETURN NEXT;
  END IF;
  IF r.base_category_id = r.target_category_id THEN
    details := jsonb_build_object('error', 'same_category'); RETURN NEXT;
  END IF;
  RETURN QUERY SELECT * FROM gematria_rules_problems(r.mapping_rules);
  IF p_batch AND NOT EXISTS (SELECT 1 FROM gematria_obligation o WHERE o.functor_id = p_id) THEN
    reason := 'naturality_missing'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- qbx.hebrew.functor.obligation_problems
CREATE OR REPLACE FUNCTION gematria_obligation_values_problems(
  p_rules JSONB, p_left TEXT, p_right TEXT, p_lv BIGINT, p_rv BIGINT, p_cv BIGINT
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  w RECORD;
  computed BIGINT;
BEGIN
  reason := 'obligation_typing';
  IF EXISTS (SELECT 1 FROM hebrew_text_problems(p_left, 'word')) THEN
    details := jsonb_build_object('error', 'left'); RETURN NEXT;
  END IF;
  IF EXISTS (SELECT 1 FROM hebrew_text_problems(p_right, 'word')) THEN
    details := jsonb_build_object('error', 'right'); RETURN NEXT;
  END IF;
  IF EXISTS (SELECT 1 FROM gematria_rules_problems(p_rules)) THEN
    details := jsonb_build_object('error', 'rules'); RETURN NEXT;
  ELSE
    FOR w IN SELECT * FROM (VALUES (1, 'left', p_lv, coalesce(p_left, '')),
                                   (2, 'right', p_rv, coalesce(p_right, '')),
                                   (3, 'concat', p_cv, coalesce(p_left, '') || coalesce(p_right, '')))
                           AS t(n, which, recorded, txt) ORDER BY n LOOP
      computed := gematria_rules_value(p_rules, w.txt);
      IF w.recorded IS DISTINCT FROM computed THEN
        reason := 'naturality_value';
        details := jsonb_build_object('which', w.which, 'recorded', w.recorded, 'computed', computed);
        RETURN NEXT;
      END IF;
    END LOOP;
  END IF;
  IF p_lv + p_rv IS DISTINCT FROM p_cv THEN
    reason := 'naturality_square';
    details := jsonb_build_object('left', p_lv, 'right', p_rv, 'concat', p_cv);
    RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION gematria_obligation_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT o.*, g.mapping_rules INTO r
    FROM gematria_obligation o JOIN gematria_functor g ON g.id = o.functor_id
   WHERE o.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM gematria_obligation_values_problems(
    r.mapping_rules, r.left_text, r.right_text, r.left_value, r.right_value, r.concat_value);
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Torah sites and sections (qbx.hebrew.torah)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION torah_book_chapters(p_book TEXT) RETURNS INT AS $$
  SELECT n FROM (VALUES ('Genesis', 50), ('Exodus', 40), ('Leviticus', 27), ('Numbers', 36),
                        ('Deuteronomy', 34), ('בראשית', 50), ('שמות', 40), ('ויקרא', 27),
                        ('במדבר', 36), ('דברים', 34)) AS b(book, n)
   WHERE b.book = p_book;
$$ LANGUAGE sql IMMUTABLE;

-- qbx.hebrew.torah.verse_ref_problems
CREATE OR REPLACE FUNCTION torah_verse_ref_problems(p_ref TEXT)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  m TEXT[];
BEGIN
  reason := 'verse_ref_format';
  m := regexp_match(p_ref, '^([^:]+) ([1-9][0-9]{0,2}):([1-9][0-9]{0,2})$');
  IF m IS NULL THEN
    details := jsonb_build_object('error', 'syntax'); RETURN NEXT;
  ELSIF torah_book_chapters(m[1]) IS NULL THEN
    details := jsonb_build_object('error', 'book'); RETURN NEXT;
  ELSIF m[2]::int > torah_book_chapters(m[1]) THEN
    details := jsonb_build_object('error', 'chapter'); RETURN NEXT;
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- The points of a Torah site's site (its base open); NULL without a site.
CREATE OR REPLACE FUNCTION torah_site_points(p_torah_site UUID) RETURNS TEXT[] AS $$
  SELECT CASE WHEN t.site_id IS NULL THEN NULL
              ELSE coalesce(sheaf_open_pts(t.site_id, s.base_space_object_id), '{}'::text[]) END
    FROM torah_site t LEFT JOIN site s ON s.id = t.site_id
   WHERE t.id = p_torah_site;
$$ LANGUAGE sql STABLE;

-- qbx.hebrew.torah.section_problems
CREATE OR REPLACE FUNCTION torah_section_values_problems(p_ref TEXT, p_text TEXT, p_points TEXT[])
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  RETURN QUERY SELECT * FROM torah_verse_ref_problems(p_ref);
  IF p_points IS NOT NULL AND NOT (p_ref = ANY (p_points)) THEN
    reason := 'verse_not_point'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
  RETURN QUERY SELECT * FROM hebrew_text_problems(p_text, 'verse');
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION torah_section_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT s.* INTO r FROM torah_section s WHERE s.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM torah_section_values_problems(r.verse_ref, r.section_text,
                                                           torah_site_points(r.site_id));
END;
$$ LANGUAGE plpgsql STABLE;

-- The passage label of {verse: text, ...}: compact JSON, keys in code point
-- order (qbx.hebrew.torah.passage_label).
CREATE OR REPLACE FUNCTION torah_passage_label(p_verses TEXT[], p_texts TEXT[]) RETURNS TEXT AS $$
  SELECT '{' || coalesce(string_agg(to_json(v)::text || ':' || to_json(t)::text, ','
                                    ORDER BY v COLLATE "C"), '') || '}'
    FROM unnest(p_verses, p_texts) AS x(v, t);
$$ LANGUAGE sql IMMUTABLE;

-- qbx.hebrew.torah.site_problems (p_batch: the sheaf check and the singleton
-- sections too; the sheaf check logs the presheaf's own problems)
CREATE OR REPLACE FUNCTION torah_site_problems(p_id UUID, p_batch BOOLEAN DEFAULT TRUE)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
  v_psite UUID;
  sec RECORD;
  v_open UUID;
  got TEXT[];
BEGIN
  SELECT t.* INTO r FROM torah_site t WHERE t.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  IF r.site_id IS NULL THEN
    reason := 'torah_no_site'; details := '{}'::jsonb; RETURN NEXT;
  END IF;
  IF r.presheaf_id IS NULL THEN
    IF p_batch THEN
      reason := 'torah_no_presheaf'; details := '{}'::jsonb; RETURN NEXT;
    END IF;
    RETURN;
  END IF;
  SELECT p.site_id INTO v_psite FROM presheaf p WHERE p.id = r.presheaf_id;
  IF r.site_id IS NULL OR v_psite IS DISTINCT FROM r.site_id THEN
    reason := 'torah_presheaf_typing'; details := jsonb_build_object('presheaf', r.presheaf_id);
    RETURN NEXT;
    RETURN;
  END IF;
  IF NOT p_batch THEN RETURN; END IF;
  IF NOT check_sheaf_condition(r.presheaf_id) THEN
    reason := 'torah_not_sheaf'; details := jsonb_build_object('presheaf', r.presheaf_id);
    RETURN NEXT;
  END IF;
  FOR sec IN SELECT s.verse_ref, s.section_text FROM torah_section s
              WHERE s.site_id = p_id ORDER BY s.verse_ref COLLATE "C" LOOP
    v_open := sheaf_open_at(r.site_id, ARRAY[sec.verse_ref]);
    CONTINUE WHEN v_open IS NULL;
    got := ARRAY(SELECT ps.label FROM presheaf_section ps
                  WHERE ps.presheaf_id = r.presheaf_id AND ps.open_object_id = v_open
                  ORDER BY ps.label COLLATE "C");
    IF sec.section_text IS NULL
       OR got IS DISTINCT FROM ARRAY[torah_passage_label(ARRAY[sec.verse_ref],
                                                         ARRAY[sec.section_text])] THEN
      reason := 'torah_section_mismatch'; details := jsonb_build_object('verse', sec.verse_ref);
      RETURN NEXT;
    END IF;
  END LOOP;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Language adjunctions (qbx.hebrew.torah.language_adjunction_problems)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION language_adjunction_values_problems(
  p_left TEXT, p_right TEXT, p_functor UUID, p_adjunction UUID, p_status TEXT, p_artifact UUID
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  a RECORD;
  v_type TEXT;
BEGIN
  reason := 'language_typing';
  IF p_left IS NULL OR btrim(p_left) = '' THEN
    details := jsonb_build_object('error', 'left'); RETURN NEXT;
  END IF;
  IF p_right IS NULL OR btrim(p_right) = '' THEN
    details := jsonb_build_object('error', 'right'); RETURN NEXT;
  END IF;
  IF p_left IS NOT NULL AND btrim(p_left) <> '' AND p_left = p_right THEN
    details := jsonb_build_object('error', 'same'); RETURN NEXT;
  END IF;
  IF p_adjunction IS NOT NULL THEN
    SELECT ad.left_functor_id, ad.right_functor_id INTO a FROM adjunction ad WHERE ad.id = p_adjunction;
    IF p_functor IS DISTINCT FROM a.left_functor_id AND p_functor IS DISTINCT FROM a.right_functor_id THEN
      reason := 'adjunction_mismatch'; details := '{}'::jsonb; RETURN NEXT;
    END IF;
  END IF;
  IF p_status IS NULL OR p_status NOT IN ('provisional', 'lean_verified') THEN
    reason := 'status_value'; details := jsonb_build_object('status', p_status); RETURN NEXT;
  END IF;
  IF p_status = 'lean_verified' THEN
    reason := 'unverified_claim';
    SELECT pa.artifact_type INTO v_type FROM proof_artifact pa WHERE pa.id = p_artifact;
    IF NOT FOUND THEN
      details := jsonb_build_object('error', 'no_artifact'); RETURN NEXT;
    ELSIF v_type IS DISTINCT FROM 'lean4' THEN
      details := jsonb_build_object('error', 'artifact_type', 'found', v_type); RETURN NEXT;
    END IF;
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

CREATE OR REPLACE FUNCTION language_adjunction_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  r RECORD;
BEGIN
  SELECT l.* INTO r FROM language_adjunction l WHERE l.id = p_id;
  IF r.id IS NULL THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM language_adjunction_values_problems(
    r.left_language, r.right_language, r.functor_id, r.adjunction_id, r.status,
    r.proof_artifact_id);
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION hebrew_record(p_table TEXT, p_id UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  INSERT INTO hebrew_violation (subject_table, subject_id, reason, details)
  VALUES (p_table, p_id, p_reason, coalesce(p_details, '{}'::jsonb));
END;
$$ LANGUAGE plpgsql;

-- The problems of one row (p_batch: include the batch-only checks).
CREATE OR REPLACE FUNCTION hebrew_problems_of(p_table TEXT, p_id UUID, p_batch BOOLEAN)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  CASE p_table
    WHEN 'hebrew_letter' THEN RETURN QUERY SELECT * FROM hebrew_letter_table_problems();
    WHEN 'hebrew_word' THEN RETURN QUERY SELECT * FROM hebrew_word_problems(p_id);
    WHEN 'gematria_functor' THEN RETURN QUERY SELECT * FROM gematria_functor_problems(p_id, p_batch);
    WHEN 'gematria_obligation' THEN RETURN QUERY SELECT * FROM gematria_obligation_problems(p_id);
    WHEN 'torah_site' THEN RETURN QUERY SELECT * FROM torah_site_problems(p_id, p_batch);
    WHEN 'torah_section' THEN RETURN QUERY SELECT * FROM torah_section_problems(p_id);
    WHEN 'language_adjunction' THEN RETURN QUERY SELECT * FROM language_adjunction_problems(p_id);
  END CASE;
END;
$$ LANGUAGE plpgsql;

-- Check one row (or the letter table): log every problem; returns their number.
CREATE OR REPLACE FUNCTION hebrew_check_row(p_table TEXT, p_id UUID, p_batch BOOLEAN DEFAULT TRUE)
RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM hebrew_problems_of(p_table, p_id, p_batch) LOOP
    PERFORM hebrew_record(p_table, p_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION hebrew_check_raise(p_n INT, p_what TEXT) RETURNS VOID AS $$
BEGIN
  IF p_n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION '% (% problem(s))', p_what, p_n;
  END IF;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION check_hebrew_letters() RETURNS BOOLEAN AS $$
DECLARE
  n INT;
BEGIN
  n := hebrew_check_row('hebrew_letter', NULL);
  PERFORM hebrew_check_raise(n, 'The Hebrew letter table differs from the seed');
  RETURN n = 0;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION check_hebrew_word(p_id UUID) RETURNS BOOLEAN AS $$
DECLARE
  n INT;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM hebrew_word w WHERE w.id = p_id) THEN
    RAISE EXCEPTION 'check_hebrew_word: word % not found', p_id;
  END IF;
  n := hebrew_check_row('hebrew_word', p_id);
  PERFORM hebrew_check_raise(n, format('Hebrew word %s is not valid', p_id));
  RETURN n = 0;
END;
$$ LANGUAGE plpgsql;

-- A functor and all its obligations.
CREATE OR REPLACE FUNCTION check_gematria_functor(p_id UUID) RETURNS BOOLEAN AS $$
DECLARE
  o RECORD;
  n INT;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM gematria_functor g WHERE g.id = p_id) THEN
    RAISE EXCEPTION 'check_gematria_functor: functor % not found', p_id;
  END IF;
  n := hebrew_check_row('gematria_functor', p_id);
  FOR o IN SELECT ob.id FROM gematria_obligation ob WHERE ob.functor_id = p_id LOOP
    n := n + hebrew_check_row('gematria_obligation', o.id);
  END LOOP;
  PERFORM hebrew_check_raise(n, format('Gematria functor %s is not a valid functor', p_id));
  RETURN n = 0;
END;
$$ LANGUAGE plpgsql;

-- A Torah site and all its sections.
CREATE OR REPLACE FUNCTION check_torah_site(p_id UUID) RETURNS BOOLEAN AS $$
DECLARE
  s RECORD;
  n INT;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM torah_site t WHERE t.id = p_id) THEN
    RAISE EXCEPTION 'check_torah_site: Torah site % not found', p_id;
  END IF;
  n := hebrew_check_row('torah_site', p_id);
  FOR s IN SELECT ts.id FROM torah_section ts WHERE ts.site_id = p_id LOOP
    n := n + hebrew_check_row('torah_section', s.id);
  END LOOP;
  PERFORM hebrew_check_raise(n, format('Torah site %s is not a sheaf of sections', p_id));
  RETURN n = 0;
END;
$$ LANGUAGE plpgsql;

-- Everything: the letter table and every row of every Hebrew table.  Returns
-- the number of problems found.
CREATE OR REPLACE FUNCTION check_hebrew() RETURNS INT AS $$
DECLARE
  t RECORD;
  n INT;
BEGIN
  n := hebrew_check_row('hebrew_letter', NULL);
  FOR t IN SELECT 'hebrew_word' AS tb, id FROM hebrew_word
           UNION ALL SELECT 'gematria_functor', id FROM gematria_functor
           UNION ALL SELECT 'gematria_obligation', id FROM gematria_obligation
           UNION ALL SELECT 'torah_site', id FROM torah_site
           UNION ALL SELECT 'torah_section', id FROM torah_section
           UNION ALL SELECT 'language_adjunction', id FROM language_adjunction LOOP
    n := n + hebrew_check_row(t.tb, t.id);
  END LOOP;
  PERFORM hebrew_check_raise(n, 'Hebrew tables have problems');
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
-- The total is recomputed on every write (the original only on UPDATE OF text).
CREATE OR REPLACE FUNCTION trg_hebrew_word_gematria() RETURNS trigger AS $$
BEGIN
  NEW.total_gematria := compute_gematria(NEW.text);
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_hebrew_word_gematria ON hebrew_word;
CREATE TRIGGER trg_hebrew_word_gematria
BEFORE INSERT OR UPDATE ON hebrew_word
FOR EACH ROW EXECUTE FUNCTION trg_hebrew_word_gematria();

-- Generic row check (write-time checks only): log, and raise in strict mode.
CREATE OR REPLACE FUNCTION trg_check_hebrew_row() RETURNS trigger AS $$
DECLARE
  n INT;
BEGIN
  n := hebrew_check_row(TG_TABLE_NAME, NEW.id, FALSE);
  PERFORM hebrew_check_raise(n, format('%s row %s is not well formed', TG_TABLE_NAME, NEW.id));
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_hebrew_row ON hebrew_word;
CREATE TRIGGER trg_check_hebrew_row AFTER INSERT OR UPDATE ON hebrew_word
FOR EACH ROW EXECUTE FUNCTION trg_check_hebrew_row();
DROP TRIGGER IF EXISTS trg_check_hebrew_row ON gematria_functor;
CREATE TRIGGER trg_check_hebrew_row AFTER INSERT OR UPDATE ON gematria_functor
FOR EACH ROW EXECUTE FUNCTION trg_check_hebrew_row();
DROP TRIGGER IF EXISTS trg_check_hebrew_row ON gematria_obligation;
CREATE TRIGGER trg_check_hebrew_row AFTER INSERT OR UPDATE ON gematria_obligation
FOR EACH ROW EXECUTE FUNCTION trg_check_hebrew_row();
DROP TRIGGER IF EXISTS trg_check_hebrew_row ON torah_site;
CREATE TRIGGER trg_check_hebrew_row AFTER INSERT OR UPDATE ON torah_site
FOR EACH ROW EXECUTE FUNCTION trg_check_hebrew_row();
DROP TRIGGER IF EXISTS trg_check_hebrew_row ON torah_section;
CREATE TRIGGER trg_check_hebrew_row AFTER INSERT OR UPDATE ON torah_section
FOR EACH ROW EXECUTE FUNCTION trg_check_hebrew_row();
DROP TRIGGER IF EXISTS trg_check_hebrew_row ON language_adjunction;
CREATE TRIGGER trg_check_hebrew_row AFTER INSERT OR UPDATE ON language_adjunction
FOR EACH ROW EXECUTE FUNCTION trg_check_hebrew_row();

-- Any change to the letter table is compared with the seed.
CREATE OR REPLACE FUNCTION trg_check_hebrew_letters() RETURNS trigger AS $$
DECLARE
  n INT;
BEGIN
  n := hebrew_check_row('hebrew_letter', NULL);
  PERFORM hebrew_check_raise(n, 'The Hebrew letter table differs from the seed');
  RETURN NULL;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_hebrew_letters ON hebrew_letter;
CREATE TRIGGER trg_check_hebrew_letters
AFTER INSERT OR UPDATE OR DELETE OR TRUNCATE ON hebrew_letter
FOR EACH STATEMENT EXECUTE FUNCTION trg_check_hebrew_letters();

-- ---------------------------------------------------------------------------
-- Writers.  Each refuses input with a write-time problem.  Rows inserted
-- directly are checked by the triggers and in batch.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION hebrew_refuse(p_what TEXT, p_problems JSONB) RETURNS VOID AS $$
BEGIN
  IF p_problems IS NOT NULL AND jsonb_array_length(p_problems) > 0 THEN
    RAISE EXCEPTION '%: % (%)', p_what, p_problems -> 0 ->> 'reason', p_problems -> 0 -> 'details';
  END IF;
END;
$$ LANGUAGE plpgsql;

-- Register a Hebrew word; its total is computed.
CREATE OR REPLACE FUNCTION register_hebrew_word(
  p_text TEXT, p_root TEXT DEFAULT NULL,
  p_object_id UUID DEFAULT NULL
) RETURNS UUID AS $$
DECLARE
  new_id UUID;
BEGIN
  PERFORM hebrew_refuse('register_hebrew_word', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM (SELECT * FROM hebrew_text_problems(p_text, 'word')
            UNION ALL SELECT * FROM hebrew_root_problems(p_root)) x));
  INSERT INTO hebrew_word (text, root, object_id)
  VALUES (p_text, p_root, p_object_id)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Store gematria_vector(text) as the word's embedding (rule R4).
CREATE OR REPLACE FUNCTION store_hebrew_embedding(p_word UUID) RETURNS VOID AS $$
BEGIN
  UPDATE hebrew_word SET embedding_vector = hebrew_gematria_vector(text)::vector
   WHERE id = p_word;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'store_hebrew_embedding: word % not found', p_word;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- Register a gematria functor (rules NULL or {} = the seeded table).
CREATE OR REPLACE FUNCTION register_gematria_functor(
  p_name TEXT, p_base_cat UUID, p_target_cat UUID,
  p_rules JSONB, p_model TEXT
) RETURNS UUID AS $$
DECLARE
  new_id UUID;
  probs JSONB;
BEGIN
  p_rules := coalesce(p_rules, '{}'::jsonb);
  probs := (SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
              FROM gematria_rules_problems(p_rules));
  IF p_base_cat IS NULL THEN
    probs := probs || jsonb_build_array(jsonb_build_object('reason', 'functor_typing',
               'details', jsonb_build_object('error', 'base_category')));
  END IF;
  IF p_target_cat IS NULL THEN
    probs := probs || jsonb_build_array(jsonb_build_object('reason', 'functor_typing',
               'details', jsonb_build_object('error', 'target_category')));
  END IF;
  IF p_base_cat = p_target_cat THEN
    probs := probs || jsonb_build_array(jsonb_build_object('reason', 'functor_typing',
               'details', jsonb_build_object('error', 'same_category')));
  END IF;
  PERFORM hebrew_refuse('register_gematria_functor', probs);
  INSERT INTO gematria_functor
    (name, base_category_id, target_category_id, mapping_rules, embedding_model)
  VALUES
    (p_name, p_base_cat, p_target_cat, p_rules, p_model)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Record a naturality obligation; omitted values are the functor's values.
CREATE OR REPLACE FUNCTION record_gematria_obligation(
  p_functor UUID, p_left TEXT, p_right TEXT,
  p_left_value BIGINT DEFAULT NULL, p_right_value BIGINT DEFAULT NULL,
  p_concat_value BIGINT DEFAULT NULL
) RETURNS UUID AS $$
DECLARE
  g RECORD;
  new_id UUID;
BEGIN
  SELECT f.* INTO g FROM gematria_functor f WHERE f.id = p_functor;
  IF g.id IS NULL THEN
    RAISE EXCEPTION 'record_gematria_obligation: functor % not found', p_functor;
  END IF;
  p_left_value := coalesce(p_left_value, gematria_rules_value(g.mapping_rules, p_left));
  p_right_value := coalesce(p_right_value, gematria_rules_value(g.mapping_rules, p_right));
  p_concat_value := coalesce(p_concat_value,
                             gematria_rules_value(g.mapping_rules, p_left || p_right));
  PERFORM hebrew_refuse('record_gematria_obligation', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM gematria_obligation_values_problems(g.mapping_rules, p_left, p_right,
                                               p_left_value, p_right_value, p_concat_value)));
  INSERT INTO gematria_obligation
    (functor_id, left_text, right_text, left_value, right_value, concat_value)
  VALUES (p_functor, p_left, p_right, p_left_value, p_right_value, p_concat_value)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Register a Torah site on a finite site of migration 012.
CREATE OR REPLACE FUNCTION register_torah_site(p_name TEXT, p_site UUID) RETURNS UUID AS $$
DECLARE
  new_id UUID;
BEGIN
  IF p_site IS NULL OR NOT EXISTS (SELECT 1 FROM site s WHERE s.id = p_site) THEN
    RAISE EXCEPTION 'register_torah_site: site % not found', p_site;
  END IF;
  INSERT INTO torah_site (name, site_id) VALUES (p_name, p_site) RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Register the text of a verse of a Torah site.
CREATE OR REPLACE FUNCTION register_torah_section(p_torah_site UUID, p_ref TEXT, p_text TEXT)
RETURNS UUID AS $$
DECLARE
  new_id UUID;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM torah_site t WHERE t.id = p_torah_site) THEN
    RAISE EXCEPTION 'register_torah_section: Torah site % not found', p_torah_site;
  END IF;
  PERFORM hebrew_refuse('register_torah_section', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM torah_section_values_problems(p_ref, p_text, torah_site_points(p_torah_site))));
  INSERT INTO torah_section (site_id, verse_ref, section_text)
  VALUES (p_torah_site, p_ref, p_text)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Build the passage presheaf of a Torah site and link it: over each open U,
-- the single section torah_passage_label(U's verses, their texts) when every
-- point of U has a text, none otherwise; restrictions to every open V ⊆ U.
CREATE OR REPLACE FUNCTION build_torah_presheaf(p_torah_site UUID, p_name TEXT DEFAULT NULL)
RETURNS UUID AS $$
DECLARE
  t RECORD;
  o RECORD;
  v RECORD;
  opens JSONB;
  new_id UUID;
BEGIN
  SELECT ts.* INTO t FROM torah_site ts WHERE ts.id = p_torah_site;
  IF t.id IS NULL THEN
    RAISE EXCEPTION 'build_torah_presheaf: Torah site % not found', p_torah_site;
  END IF;
  IF t.site_id IS NULL THEN
    RAISE EXCEPTION 'build_torah_presheaf: Torah site % has no site', p_torah_site;
  END IF;
  -- {open id: {"points": [...], "label": text}} for the opens with a section
  SELECT coalesce(jsonb_object_agg(x.object_id::text,
                                   jsonb_build_object('points', to_jsonb(x.points),
                                                      'label', x.label)), '{}'::jsonb)
    INTO opens
    FROM (SELECT so.object_id, so.points,
                 (SELECT torah_passage_label(array_agg(s.verse_ref), array_agg(s.section_text))
                    FROM torah_section s
                   WHERE s.site_id = p_torah_site AND s.verse_ref = ANY (so.points)) AS label
            FROM site_open so
           WHERE so.site_id = t.site_id
             AND (SELECT count(*) FROM torah_section s
                   WHERE s.site_id = p_torah_site AND s.section_text IS NOT NULL
                     AND s.verse_ref = ANY (so.points)) = cardinality(so.points)) x;
  new_id := register_presheaf(t.site_id, coalesce(p_name, 'passages:' || t.name),
              (SELECT coalesce(jsonb_object_agg(j.key, jsonb_build_array(j.value -> 'label')),
                               '{}'::jsonb)
                 FROM jsonb_each(opens) j));
  FOR o IN SELECT j.key, j.value FROM jsonb_each(opens) j LOOP
    FOR v IN SELECT j.key, j.value FROM jsonb_each(opens) j
              WHERE (j.value -> 'points') <@ (o.value -> 'points') LOOP
      PERFORM record_restriction(new_id, o.key::uuid, v.key::uuid,
                                 o.value ->> 'label', v.value ->> 'label');
    END LOOP;
  END LOOP;
  UPDATE torah_site SET presheaf_id = new_id WHERE id = p_torah_site;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Register a language adjunction (status 'provisional' unless a lean4 proof
-- artifact backs it).
CREATE OR REPLACE FUNCTION register_language_adjunction(
  p_left TEXT, p_right TEXT, p_functor UUID, p_adjunction UUID DEFAULT NULL,
  p_status TEXT DEFAULT 'provisional', p_artifact UUID DEFAULT NULL
) RETURNS UUID AS $$
DECLARE
  new_id UUID;
BEGIN
  PERFORM hebrew_refuse('register_language_adjunction', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM language_adjunction_values_problems(p_left, p_right, p_functor, p_adjunction,
                                               p_status, p_artifact)));
  INSERT INTO language_adjunction
    (left_language, right_language, functor_id, adjunction_id, status, proof_artifact_id)
  VALUES (p_left, p_right, p_functor, p_adjunction, p_status, p_artifact)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;
