-- ============================================================================
-- Categorical Ledger — Migration 016: Empirical Grounding
-- ============================================================================
-- Measurement contracts, measurement bundles and their validations,
-- uncertainty types, dynamical models and simulation runs, agent models, and
-- finite direct mechanisms with checked incentive claims.  The Python
-- reference is qbx.empirical (measurement, models, mechanism): every
-- *_problems function below reports the same problems, with the same details,
-- as the Python function it names.
--
-- Numbers are JSON numbers (jsonb_typeof 'number'); arithmetic on them is
-- exact (numeric).  Blank text is text of only space, tab, LF, CR, FF, VT (the
-- empty text included); a *name* is a JSON string that is not blank.  *Given*
-- means not NULL.
--
-- Recording.
--   uncertainty_type     name; descriptor: a JSON object with kind
--                          interval  uncertainty u = half-width of an interval
--                                    containing the true value  (factor 1)
--                          uniform   u = half-width of the support of a
--                                    uniform distribution       (factor 1)
--                          gaussian  u = standard uncertainty; coverage_factor
--                                    k > 0                      (factor k)
--   measurement_contract name, observable_id, version MAJOR.MINOR.PATCH;
--                        body: optional bounds min ≤ max (numbers) and unit (a
--                        name); expected_precision: optional absolute and
--                        relative (numbers ≥ 0); validation_tests: a JSON
--                        array of distinct tests among
--                          range_check      [v − h, v + h] within the bounds,
--                                           h = factor × u
--                          precision_check  u ≤ absolute + relative × |v|
--                          unit_check       the observation's unit is the
--                                           contract's;
--                        uncertainty_type_id: optional (none: factor 1).
--   measurement_bundle   observations: a non-empty JSON array of objects with
--                        a number value, optionally uncertainty (a number ≥ 0;
--                        0 when missing) and unit (a name); context and
--                        provenance: JSON objects.  validated /
--                        validation_report must be those of the bundle's
--                        latest validation (false / NULL without one).
--   measurement_validation  append-only (seq orders it).  A validation of a
--                        bundle against a contract: report is the JSON array
--                        of failures {"test", "index"} in the contract's test
--                        order, then by observation index (from 0); ok is true
--                        exactly when the report is empty.  Both are
--                        recomputed by the checks.
--   dynamical_model      name, model_type (ODE / SDE / PDE / discrete; a
--                        column constraint), model_spec (not blank),
--                        solver_config (a JSON object; tolerance, when
--                        present, a number > 0), metadata (a JSON object).
--   simulation_run       a run of a model: initial_conditions (an object);
--                        solver, result_uri (when given, not blank); tolerance
--                        (when given, finite and > 0); result_summary (when
--                        given, an object); started_at ≤ finished_at.
--   agent_model          name; body_spec, learning_module (when given,
--                        objects); sensors, actuators (when given, arrays of
--                        distinct names); safety_constraints (when given, an
--                        array of objects naming a declared actuator, with
--                        optional numbers min ≤ max); metadata (an object).
--   mechanism            a direct mechanism for one agent.  mechanism_spec:
--                        types, outcomes (non-empty arrays of distinct names);
--                        allocation (every type → an outcome), payment (every
--                        type → a number), valuation (every type → every
--                        outcome → a number).  The utility of type t reporting
--                        r is valuation[t][allocation[r]] − payment[r].
--                        incentive_constraints may claim "ic": true (no type
--                        gains by misreporting) and "ir": true (truthful
--                        utility ≥ 0); every claim is checked.
--   empirical_violation  the violation table (subject_table, subject_id,
--                        reason, details).
--
-- Checks.  Every check logs to empirical_violation and raises only when
-- qbx.enforcement_mode = 'strict'.  Rows are checked when written (triggers)
-- and in batch (check_empirical, part of run_all_batch_checks); the checks
-- marked "batch" need other rows and run only in batch.
--   uncertainty_type        uncertainty_typing (error ∈ name, descriptor,
--                           kind, coverage_factor)
--   measurement_contract    contract_typing (error ∈ name, observable,
--                           version, body, bounds, unit, precision, tests,
--                           test {test} (unknown), duplicate_test {test},
--                           unit_check (no unit), precision_check (no
--                           precision))
--   measurement_bundle      bundle_typing (error ∈ observations, observation
--                           {index, field ∈ object, value, uncertainty, unit},
--                           context, provenance)
--                           bundle_validated  batch: field ∈ validated, report
--                           differs from the latest validation
--   measurement_validation  validation_typing (error ∈ bundle, contract
--                           (missing), ok (NULL), report (not an array));
--                           validation_input (error ∈ bundle, contract,
--                           uncertainty: that row has problems);
--                           validation_result {recorded, computed}: the
--                           recorded ok or report is not the computed one
--   dynamical_model         model_typing (error ∈ name, model_type, spec,
--                           solver_config, tolerance, metadata)
--   simulation_run          simulation_typing (error ∈ model, initial_
--                           conditions, solver, tolerance, result_uri,
--                           result_summary, started_at, window)
--   agent_model             agent_typing (error ∈ name, body_spec, sensors,
--                           duplicate_sensor {name}, actuators,
--                           duplicate_actuator {name}, learning_module,
--                           safety, safety_constraint {index}, metadata)
--   mechanism               mechanism_typing (error ∈ name, spec, types,
--                           outcomes, allocation, payment, valuation,
--                           constraints, metadata); when well typed:
--                           mechanism_ic {type, report, gain} (ic claimed: a
--                           misreport that gains), mechanism_ir {type,
--                           utility} (ir claimed: negative truthful utility)
--   measurement_validation (always, at the change)
--                           log_mutation (an UPDATE, DELETE or TRUNCATE;
--                           details: table, op)
--
-- Writers (register_uncertainty_type, register_measurement_contract,
-- record_measurement_bundle, validate_measurement_bundle,
-- register_dynamical_model, record_simulation_run, register_agent_model,
-- register_mechanism) refuse input with any problem.
--
-- Formal backing (Formal/Empirical.lean): for h ≥ 0 the range check holds
-- iff every value the measurement allows (|x − v| ≤ h) is within the bounds
-- (rangeOk_iff, range_pass_sound), and passing with a larger coverage factor
-- implies passing with a smaller one (rangeOk_factor_antitone); the report is
-- empty iff every test passes on every observation, and lists exactly the
-- failing (test, index) pairs (report_eq_nil_iff, mem_report_iff); the IC / IR
-- failure lists are empty iff the mechanism is IC / IR
-- (icFailures_eq_nil_iff, irFailures_eq_nil_iff); an IC mechanism's payment
-- differences lie between valuation differences, so it is weakly monotone
-- (ic_payment_bounds, ic_weak_monotone, ic_single_parameter_monotone).
--
-- Phase 1 sprint 13 rewrite.  Running the original on PostgreSQL 16 showed:
--   * validate_measurement_bundle of a bundle that does not exist returned
--     true;
--   * an observation without a "value" passed the range check; observations
--     given as an object made validation fail with a raw error;
--   * a misspelled test ('rnage_check') was silently ignored and bounds
--     min 10 > max 0 accepted, so the bundle validated;
--   * validated could be set to true without a validation, and stayed true
--     after the observations were changed;
--   * blank names, negative precision, a solver_config [1], a simulation with
--     tolerance −1 finishing before it started and initial conditions 7, a
--     mechanism spec "x", a gaussian sigma −2 and sensors 5 were accepted;
--   * mechanism incentive claims were never checked;
--   * nothing was logged, and nothing was part of run_all_batch_checks.
-- ============================================================================

CREATE TABLE IF NOT EXISTS uncertainty_type (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  descriptor JSONB NOT NULL,
  created_at TIMESTAMPTZ DEFAULT now()
);
ALTER TABLE uncertainty_type ADD COLUMN IF NOT EXISTS created_at TIMESTAMPTZ DEFAULT now();

CREATE TABLE IF NOT EXISTS measurement_contract (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL UNIQUE,
  observable_id TEXT NOT NULL,
  mapping_function TEXT,
  expected_precision JSONB DEFAULT '{}'::jsonb,
  validation_tests JSONB DEFAULT '[]'::jsonb,
  body JSONB NOT NULL DEFAULT '{}'::jsonb,
  version TEXT NOT NULL DEFAULT '1.0.0',
  uncertainty_type_id UUID REFERENCES uncertainty_type(id) ON DELETE SET NULL,
  active BOOLEAN DEFAULT TRUE,
  created_at TIMESTAMPTZ DEFAULT now()
);
ALTER TABLE measurement_contract
  ADD COLUMN IF NOT EXISTS uncertainty_type_id UUID REFERENCES uncertainty_type(id) ON DELETE SET NULL;

CREATE TABLE IF NOT EXISTS measurement_bundle (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  sensor_id TEXT,
  observations JSONB NOT NULL,
  context JSONB DEFAULT '{}'::jsonb,
  provenance JSONB DEFAULT '{}'::jsonb,
  validated BOOLEAN DEFAULT FALSE,
  validation_report JSONB,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_measurement_bundle_sensor
  ON measurement_bundle (sensor_id, created_at DESC);

CREATE TABLE IF NOT EXISTS measurement_validation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  seq BIGSERIAL,
  bundle_id UUID REFERENCES measurement_bundle(id) ON DELETE SET NULL,
  contract_id UUID REFERENCES measurement_contract(id) ON DELETE SET NULL,
  ok BOOLEAN,
  report JSONB,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_measurement_validation_bundle
  ON measurement_validation (bundle_id, seq DESC);

CREATE TABLE IF NOT EXISTS dynamical_model (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL,
  model_type TEXT NOT NULL CHECK (model_type IN ('ODE','SDE','PDE','discrete')),
  model_spec TEXT NOT NULL,
  solver_config JSONB DEFAULT '{}'::jsonb,
  verification_proof UUID REFERENCES proof_artifact(id) ON DELETE SET NULL,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS agent_model (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL,
  body_spec JSONB,
  sensors JSONB,
  actuators JSONB,
  learning_module JSONB,
  safety_constraints JSONB,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS mechanism (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  name TEXT NOT NULL,
  mechanism_spec JSONB NOT NULL,
  incentive_constraints JSONB,
  verification_proof UUID REFERENCES proof_artifact(id) ON DELETE SET NULL,
  metadata JSONB DEFAULT '{}'::jsonb,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS simulation_run (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  model_id UUID REFERENCES dynamical_model(id) ON DELETE CASCADE,
  initial_conditions JSONB NOT NULL,
  solver_used TEXT,
  tolerance DOUBLE PRECISION,
  result_uri TEXT,
  result_summary JSONB,
  started_at TIMESTAMPTZ DEFAULT now(),
  finished_at TIMESTAMPTZ
);

CREATE TABLE IF NOT EXISTS empirical_violation (
  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
  subject_table TEXT NOT NULL,
  subject_id UUID,
  reason TEXT NOT NULL,
  details JSONB DEFAULT '{}'::jsonb,
  detected_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_empirical_violation_subject
  ON empirical_violation (subject_table, subject_id, detected_at DESC);

-- ---------------------------------------------------------------------------
-- Helpers (qbx.empirical.values).  gov_blank and gov_problem: migration 015.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION emp_is_object(j JSONB) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(j) = 'object', FALSE);
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION emp_is_number(j JSONB) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(j) = 'number', FALSE);
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION emp_num(j JSONB) RETURNS NUMERIC AS $$
  SELECT CASE WHEN jsonb_typeof(j) = 'number' THEN (j #>> '{}')::numeric END;
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION emp_is_name(j JSONB) RETURNS BOOLEAN AS $$
  SELECT coalesce(jsonb_typeof(j) = 'string' AND NOT gov_blank(j #>> '{}'), FALSE);
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION emp_is_nonempty_array(j JSONB) RETURNS BOOLEAN AS $$
  SELECT CASE WHEN jsonb_typeof(j) = 'array' THEN jsonb_array_length(j) > 0 ELSE FALSE END;
$$ LANGUAGE sql IMMUTABLE;

-- A JSON array of names (repeats allowed).
CREATE OR REPLACE FUNCTION emp_is_name_list(j JSONB) RETURNS BOOLEAN AS $$
  SELECT CASE WHEN jsonb_typeof(j) = 'array'
              THEN NOT EXISTS (SELECT 1 FROM jsonb_array_elements(j) e WHERE NOT emp_is_name(e))
              ELSE FALSE END;
$$ LANGUAGE sql IMMUTABLE;

-- A non-empty JSON array of distinct names.
CREATE OR REPLACE FUNCTION emp_is_name_set(j JSONB) RETURNS BOOLEAN AS $$
  SELECT CASE WHEN emp_is_name_list(j)
              THEN jsonb_array_length(j) > 0
                   AND (SELECT count(DISTINCT e) FROM jsonb_array_elements(j) e) = jsonb_array_length(j)
              ELSE FALSE END;
$$ LANGUAGE sql IMMUTABLE;

-- The elements of a name list equal to an earlier one, in order.
CREATE OR REPLACE FUNCTION emp_repeats(j JSONB) RETURNS TABLE(name TEXT) AS $$
  SELECT e.v FROM jsonb_array_elements_text(j) WITH ORDINALITY e(v, i)
   WHERE EXISTS (SELECT 1 FROM jsonb_array_elements_text(j) WITH ORDINALITY f(v, i)
                  WHERE f.i < e.i AND f.v = e.v)
   ORDER BY e.i;
$$ LANGUAGE sql IMMUTABLE;

-- Optional bounds: min / max, when present, numbers with min ≤ max.
CREATE OR REPLACE FUNCTION emp_bounds_ok(j JSONB) RETURNS BOOLEAN AS $$
  SELECT (NOT j ? 'min' OR emp_is_number(j -> 'min'))
     AND (NOT j ? 'max' OR emp_is_number(j -> 'max'))
     AND NOT coalesce(emp_num(j -> 'min') > emp_num(j -> 'max'), FALSE);
$$ LANGUAGE sql IMMUTABLE;

-- An object whose keys are exactly the names of the array p_keys (distinct).
CREATE OR REPLACE FUNCTION emp_keyed(j JSONB, p_keys JSONB) RETURNS BOOLEAN AS $$
  SELECT CASE WHEN emp_is_object(j)
              THEN coalesce((SELECT array_agg(k ORDER BY k COLLATE "C") FROM jsonb_object_keys(j) k)
                            = (SELECT array_agg(t ORDER BY t COLLATE "C")
                                 FROM jsonb_array_elements_text(p_keys) t), FALSE)
              ELSE FALSE END;
$$ LANGUAGE sql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Uncertainty types (qbx.empirical.measurement.uncertainty_problems)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION empirical_uncertainty_values_problems(p_name TEXT, p_descriptor JSONB)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF gov_blank(p_name) THEN
    RETURN QUERY SELECT * FROM gov_problem('uncertainty_typing', '{"error":"name"}');
  END IF;
  IF NOT emp_is_object(p_descriptor) THEN
    RETURN QUERY SELECT * FROM gov_problem('uncertainty_typing', '{"error":"descriptor"}');
    RETURN;
  END IF;
  IF jsonb_typeof(p_descriptor -> 'kind') IS DISTINCT FROM 'string'
     OR (p_descriptor ->> 'kind') NOT IN ('interval', 'uniform', 'gaussian') THEN
    RETURN QUERY SELECT * FROM gov_problem('uncertainty_typing', '{"error":"kind"}');
  ELSIF p_descriptor ->> 'kind' = 'gaussian'
        AND NOT coalesce(emp_num(p_descriptor -> 'coverage_factor') > 0, FALSE) THEN
    RETURN QUERY SELECT * FROM gov_problem('uncertainty_typing', '{"error":"coverage_factor"}');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION empirical_uncertainty_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM uncertainty_type u,
    LATERAL empirical_uncertainty_values_problems(u.name, u.descriptor) pr
   WHERE u.id = p_id;
$$ LANGUAGE sql STABLE;

-- The half-width factor: 1 without a type or for interval / uniform; the
-- coverage factor for gaussian (for descriptors without problems).
CREATE OR REPLACE FUNCTION empirical_half_width_factor(p_descriptor JSONB) RETURNS NUMERIC AS $$
  SELECT CASE WHEN p_descriptor ->> 'kind' = 'gaussian'
              THEN emp_num(p_descriptor -> 'coverage_factor') ELSE 1 END;
$$ LANGUAGE sql IMMUTABLE;

-- ---------------------------------------------------------------------------
-- Contracts (qbx.empirical.measurement.contract_problems)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION empirical_contract_values_problems(
  p_name TEXT, p_observable TEXT, p_version TEXT, p_body JSONB, p_precision JSONB, p_tests JSONB
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  tests_ok BOOLEAN;
  t RECORD;
BEGIN
  IF gov_blank(p_name) THEN
    RETURN QUERY SELECT * FROM gov_problem('contract_typing', '{"error":"name"}');
  END IF;
  IF gov_blank(p_observable) THEN
    RETURN QUERY SELECT * FROM gov_problem('contract_typing', '{"error":"observable"}');
  END IF;
  IF p_version IS NULL
     OR p_version !~ '^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$' THEN
    RETURN QUERY SELECT * FROM gov_problem('contract_typing', '{"error":"version"}');
  END IF;
  IF NOT emp_is_object(p_body) THEN
    RETURN QUERY SELECT * FROM gov_problem('contract_typing', '{"error":"body"}');
  ELSE
    IF NOT emp_bounds_ok(p_body) THEN
      RETURN QUERY SELECT * FROM gov_problem('contract_typing', '{"error":"bounds"}');
    END IF;
    IF p_body ? 'unit' AND NOT emp_is_name(p_body -> 'unit') THEN
      RETURN QUERY SELECT * FROM gov_problem('contract_typing', '{"error":"unit"}');
    END IF;
  END IF;
  IF NOT emp_is_object(p_precision)
     OR (p_precision ? 'absolute' AND NOT coalesce(emp_num(p_precision -> 'absolute') >= 0, FALSE))
     OR (p_precision ? 'relative' AND NOT coalesce(emp_num(p_precision -> 'relative') >= 0, FALSE)) THEN
    RETURN QUERY SELECT * FROM gov_problem('contract_typing', '{"error":"precision"}');
  END IF;
  tests_ok := CASE WHEN jsonb_typeof(p_tests) = 'array'
                   THEN NOT EXISTS (SELECT 1 FROM jsonb_array_elements(p_tests) e
                                     WHERE jsonb_typeof(e) <> 'string')
                   ELSE FALSE END;
  IF NOT tests_ok THEN
    RETURN QUERY SELECT * FROM gov_problem('contract_typing', '{"error":"tests"}');
  ELSE
    FOR t IN SELECT e.v, e.i FROM jsonb_array_elements_text(p_tests) WITH ORDINALITY e(v, i)
              ORDER BY e.i LOOP
      IF t.v NOT IN ('range_check', 'precision_check', 'unit_check') THEN
        RETURN QUERY SELECT * FROM gov_problem('contract_typing',
          jsonb_build_object('error', 'test', 'test', t.v));
      ELSIF EXISTS (SELECT 1 FROM jsonb_array_elements_text(p_tests) WITH ORDINALITY f(v, i)
                     WHERE f.i < t.i AND f.v = t.v) THEN
        RETURN QUERY SELECT * FROM gov_problem('contract_typing',
          jsonb_build_object('error', 'duplicate_test', 'test', t.v));
      END IF;
    END LOOP;
    IF p_tests @> '["unit_check"]'
       AND NOT (emp_is_object(p_body) AND emp_is_name(p_body -> 'unit')) THEN
      RETURN QUERY SELECT * FROM gov_problem('contract_typing', '{"error":"unit_check"}');
    END IF;
    IF p_tests @> '["precision_check"]'
       AND NOT (emp_is_object(p_precision)
                AND (p_precision ? 'absolute' OR p_precision ? 'relative')) THEN
      RETURN QUERY SELECT * FROM gov_problem('contract_typing', '{"error":"precision_check"}');
    END IF;
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION empirical_contract_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM measurement_contract c,
    LATERAL empirical_contract_values_problems(c.name, c.observable_id, c.version, c.body,
                                               c.expected_precision, c.validation_tests) pr
   WHERE c.id = p_id;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Bundles (qbx.empirical.measurement.bundle_problems)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION empirical_bundle_values_problems(
  p_observations JSONB, p_context JSONB, p_provenance JSONB
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  o RECORD;
BEGIN
  IF NOT emp_is_nonempty_array(p_observations) THEN
    RETURN QUERY SELECT * FROM gov_problem('bundle_typing', '{"error":"observations"}');
  ELSE
    FOR o IN SELECT e.v, e.i - 1 AS idx
               FROM jsonb_array_elements(p_observations) WITH ORDINALITY e(v, i) ORDER BY e.i LOOP
      IF NOT emp_is_object(o.v) THEN
        RETURN QUERY SELECT * FROM gov_problem('bundle_typing',
          jsonb_build_object('error', 'observation', 'index', o.idx, 'field', 'object'));
        CONTINUE;
      END IF;
      IF NOT emp_is_number(o.v -> 'value') THEN
        RETURN QUERY SELECT * FROM gov_problem('bundle_typing',
          jsonb_build_object('error', 'observation', 'index', o.idx, 'field', 'value'));
      END IF;
      IF o.v ? 'uncertainty' AND NOT coalesce(emp_num(o.v -> 'uncertainty') >= 0, FALSE) THEN
        RETURN QUERY SELECT * FROM gov_problem('bundle_typing',
          jsonb_build_object('error', 'observation', 'index', o.idx, 'field', 'uncertainty'));
      END IF;
      IF o.v ? 'unit' AND NOT emp_is_name(o.v -> 'unit') THEN
        RETURN QUERY SELECT * FROM gov_problem('bundle_typing',
          jsonb_build_object('error', 'observation', 'index', o.idx, 'field', 'unit'));
      END IF;
    END LOOP;
  END IF;
  IF NOT emp_is_object(p_context) THEN
    RETURN QUERY SELECT * FROM gov_problem('bundle_typing', '{"error":"context"}');
  END IF;
  IF NOT emp_is_object(p_provenance) THEN
    RETURN QUERY SELECT * FROM gov_problem('bundle_typing', '{"error":"provenance"}');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- qbx.empirical.measurement.bundle_validated_problems
CREATE OR REPLACE FUNCTION empirical_bundle_validated_values_problems(
  p_validated BOOLEAN, p_report JSONB, p_has_latest BOOLEAN, p_ok BOOLEAN, p_latest_report JSONB
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF p_validated IS DISTINCT FROM (CASE WHEN p_has_latest THEN p_ok ELSE FALSE END) THEN
    RETURN QUERY SELECT * FROM gov_problem('bundle_validated', '{"field":"validated"}');
  END IF;
  IF p_report IS DISTINCT FROM (CASE WHEN p_has_latest THEN p_latest_report END) THEN
    RETURN QUERY SELECT * FROM gov_problem('bundle_validated', '{"field":"report"}');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION empirical_bundle_problems(p_id UUID, p_batch BOOLEAN DEFAULT TRUE)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  b RECORD;
  v RECORD;
BEGIN
  SELECT * INTO b FROM measurement_bundle WHERE id = p_id;
  IF NOT FOUND THEN RETURN; END IF;
  RETURN QUERY SELECT * FROM empirical_bundle_values_problems(b.observations, b.context, b.provenance);
  IF p_batch THEN
    SELECT * INTO v FROM measurement_validation WHERE bundle_id = p_id ORDER BY seq DESC LIMIT 1;
    RETURN QUERY SELECT * FROM empirical_bundle_validated_values_problems(
      b.validated, b.validation_report, FOUND, v.ok, v.report);
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Validation (qbx.empirical.measurement.validation_report / validate)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION empirical_test_passes(
  p_test TEXT, p_body JSONB, p_precision JSONB, p_factor NUMERIC, p_obs JSONB
) RETURNS BOOLEAN AS $$
DECLARE
  v NUMERIC := emp_num(p_obs -> 'value');
  u NUMERIC := coalesce(emp_num(p_obs -> 'uncertainty'), 0);
BEGIN
  IF p_test = 'range_check' THEN
    RETURN (NOT p_body ? 'min' OR emp_num(p_body -> 'min') <= v - p_factor * u)
       AND (NOT p_body ? 'max' OR v + p_factor * u <= emp_num(p_body -> 'max'));
  ELSIF p_test = 'precision_check' THEN
    RETURN u <= coalesce(emp_num(p_precision -> 'absolute'), 0)
                + coalesce(emp_num(p_precision -> 'relative'), 0) * abs(v);
  ELSE
    RETURN (p_obs ->> 'unit') IS NOT DISTINCT FROM (p_body ->> 'unit');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- The report: failures {"test", "index"} in test order, then by index.
CREATE OR REPLACE FUNCTION empirical_validation_report(
  p_body JSONB, p_precision JSONB, p_tests JSONB, p_factor NUMERIC, p_observations JSONB
) RETURNS JSONB AS $$
  SELECT coalesce(jsonb_agg(jsonb_build_object('test', t.v, 'index', o.i - 1) ORDER BY t.i, o.i),
                  '[]'::jsonb)
    FROM jsonb_array_elements_text(p_tests) WITH ORDINALITY t(v, i)
   CROSS JOIN jsonb_array_elements(p_observations) WITH ORDINALITY o(e, i)
   WHERE NOT empirical_test_passes(t.v, p_body, p_precision, p_factor, o.e);
$$ LANGUAGE sql IMMUTABLE;

-- The computed report of a bundle against a contract (both rows present).
CREATE OR REPLACE FUNCTION empirical_compute_report(p_bundle UUID, p_contract UUID) RETURNS JSONB AS $$
  SELECT empirical_validation_report(c.body, c.expected_precision, c.validation_tests,
           empirical_half_width_factor((SELECT u.descriptor FROM uncertainty_type u
                                         WHERE u.id = c.uncertainty_type_id)),
           b.observations)
    FROM measurement_bundle b, measurement_contract c
   WHERE b.id = p_bundle AND c.id = p_contract;
$$ LANGUAGE sql STABLE;

-- The inputs of a validation, as validation_input errors (bundle, contract,
-- uncertainty: that row has problems).
CREATE OR REPLACE FUNCTION empirical_validation_input_problems(p_bundle UUID, p_contract UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF EXISTS (SELECT 1 FROM measurement_bundle WHERE id = p_bundle)
     AND EXISTS (SELECT 1 FROM empirical_bundle_problems(p_bundle, FALSE)) THEN
    RETURN QUERY SELECT * FROM gov_problem('validation_input', '{"error":"bundle"}');
  END IF;
  IF EXISTS (SELECT 1 FROM empirical_contract_problems(p_contract)) THEN
    RETURN QUERY SELECT * FROM gov_problem('validation_input', '{"error":"contract"}');
  END IF;
  IF EXISTS (SELECT 1 FROM measurement_contract c,
               LATERAL empirical_uncertainty_problems(c.uncertainty_type_id) pr
              WHERE c.id = p_contract) THEN
    RETURN QUERY SELECT * FROM gov_problem('validation_input', '{"error":"uncertainty"}');
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- qbx.empirical.measurement.validation_problems
CREATE OR REPLACE FUNCTION empirical_validation_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  v RECORD;
  n INT := 0;
  pr RECORD;
  computed JSONB;
BEGIN
  SELECT * INTO v FROM measurement_validation WHERE id = p_id;
  IF NOT FOUND THEN RETURN; END IF;
  IF NOT EXISTS (SELECT 1 FROM measurement_bundle WHERE id = v.bundle_id) THEN
    RETURN QUERY SELECT * FROM gov_problem('validation_typing', '{"error":"bundle"}'); n := n + 1;
  END IF;
  IF NOT EXISTS (SELECT 1 FROM measurement_contract WHERE id = v.contract_id) THEN
    RETURN QUERY SELECT * FROM gov_problem('validation_typing', '{"error":"contract"}'); n := n + 1;
  END IF;
  IF v.ok IS NULL THEN
    RETURN QUERY SELECT * FROM gov_problem('validation_typing', '{"error":"ok"}'); n := n + 1;
  END IF;
  IF jsonb_typeof(v.report) IS DISTINCT FROM 'array' THEN
    RETURN QUERY SELECT * FROM gov_problem('validation_typing', '{"error":"report"}'); n := n + 1;
  END IF;
  FOR pr IN SELECT * FROM empirical_validation_input_problems(v.bundle_id, v.contract_id) LOOP
    RETURN QUERY SELECT pr.reason, pr.details; n := n + 1;
  END LOOP;
  IF n > 0 THEN RETURN; END IF;
  computed := empirical_compute_report(v.bundle_id, v.contract_id);
  IF v.ok IS DISTINCT FROM (jsonb_array_length(computed) = 0) OR v.report IS DISTINCT FROM computed THEN
    RETURN QUERY SELECT * FROM gov_problem('validation_result',
      jsonb_build_object('recorded', v.ok, 'computed', jsonb_array_length(computed) = 0));
  END IF;
END;
$$ LANGUAGE plpgsql STABLE;

-- ---------------------------------------------------------------------------
-- Dynamical models, simulation runs, agent models (qbx.empirical.models)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION empirical_model_values_problems(
  p_name TEXT, p_type TEXT, p_spec TEXT, p_config JSONB, p_metadata JSONB
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF gov_blank(p_name) THEN
    RETURN QUERY SELECT * FROM gov_problem('model_typing', '{"error":"name"}');
  END IF;
  IF p_type IS NULL OR p_type NOT IN ('ODE', 'SDE', 'PDE', 'discrete') THEN
    RETURN QUERY SELECT * FROM gov_problem('model_typing', '{"error":"model_type"}');
  END IF;
  IF gov_blank(p_spec) THEN
    RETURN QUERY SELECT * FROM gov_problem('model_typing', '{"error":"spec"}');
  END IF;
  IF NOT emp_is_object(p_config) THEN
    RETURN QUERY SELECT * FROM gov_problem('model_typing', '{"error":"solver_config"}');
  ELSIF p_config ? 'tolerance' AND NOT coalesce(emp_num(p_config -> 'tolerance') > 0, FALSE) THEN
    RETURN QUERY SELECT * FROM gov_problem('model_typing', '{"error":"tolerance"}');
  END IF;
  IF NOT emp_is_object(p_metadata) THEN
    RETURN QUERY SELECT * FROM gov_problem('model_typing', '{"error":"metadata"}');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION empirical_model_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM dynamical_model m,
    LATERAL empirical_model_values_problems(m.name, m.model_type, m.model_spec,
                                            m.solver_config, m.metadata) pr
   WHERE m.id = p_id;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION empirical_simulation_values_problems(
  p_model_exists BOOLEAN, p_initial JSONB, p_solver TEXT, p_tolerance DOUBLE PRECISION,
  p_result_uri TEXT, p_summary JSONB, p_started TIMESTAMPTZ, p_finished TIMESTAMPTZ
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  IF NOT coalesce(p_model_exists, FALSE) THEN
    RETURN QUERY SELECT * FROM gov_problem('simulation_typing', '{"error":"model"}');
  END IF;
  IF NOT emp_is_object(p_initial) THEN
    RETURN QUERY SELECT * FROM gov_problem('simulation_typing', '{"error":"initial_conditions"}');
  END IF;
  IF p_solver IS NOT NULL AND gov_blank(p_solver) THEN
    RETURN QUERY SELECT * FROM gov_problem('simulation_typing', '{"error":"solver"}');
  END IF;
  -- NaN compares greater than every number, so it fails "< Infinity".
  IF p_tolerance IS NOT NULL
     AND NOT (p_tolerance > 0 AND p_tolerance < 'Infinity'::double precision) THEN
    RETURN QUERY SELECT * FROM gov_problem('simulation_typing', '{"error":"tolerance"}');
  END IF;
  IF p_result_uri IS NOT NULL AND gov_blank(p_result_uri) THEN
    RETURN QUERY SELECT * FROM gov_problem('simulation_typing', '{"error":"result_uri"}');
  END IF;
  IF p_summary IS NOT NULL AND NOT emp_is_object(p_summary) THEN
    RETURN QUERY SELECT * FROM gov_problem('simulation_typing', '{"error":"result_summary"}');
  END IF;
  IF p_started IS NULL THEN
    RETURN QUERY SELECT * FROM gov_problem('simulation_typing', '{"error":"started_at"}');
  ELSIF p_finished IS NOT NULL AND p_finished < p_started THEN
    RETURN QUERY SELECT * FROM gov_problem('simulation_typing', '{"error":"window"}');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION empirical_simulation_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM simulation_run s,
    LATERAL empirical_simulation_values_problems(
      EXISTS (SELECT 1 FROM dynamical_model m WHERE m.id = s.model_id),
      s.initial_conditions, s.solver_used, s.tolerance, s.result_uri, s.result_summary,
      s.started_at, s.finished_at) pr
   WHERE s.id = p_id;
$$ LANGUAGE sql STABLE;

CREATE OR REPLACE FUNCTION empirical_agent_values_problems(
  p_name TEXT, p_body JSONB, p_sensors JSONB, p_actuators JSONB, p_learning JSONB,
  p_safety JSONB, p_metadata JSONB
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  c RECORD;
  actuators_ok BOOLEAN := emp_is_name_list(p_actuators);
BEGIN
  IF gov_blank(p_name) THEN
    RETURN QUERY SELECT * FROM gov_problem('agent_typing', '{"error":"name"}');
  END IF;
  IF p_body IS NOT NULL AND NOT emp_is_object(p_body) THEN
    RETURN QUERY SELECT * FROM gov_problem('agent_typing', '{"error":"body_spec"}');
  END IF;
  IF p_sensors IS NOT NULL THEN
    IF NOT emp_is_name_list(p_sensors) THEN
      RETURN QUERY SELECT * FROM gov_problem('agent_typing', '{"error":"sensors"}');
    ELSE
      RETURN QUERY SELECT 'agent_typing'::text,
                          jsonb_build_object('error', 'duplicate_sensor', 'name', r.name)
                     FROM emp_repeats(p_sensors) r;
    END IF;
  END IF;
  IF p_actuators IS NOT NULL THEN
    IF NOT actuators_ok THEN
      RETURN QUERY SELECT * FROM gov_problem('agent_typing', '{"error":"actuators"}');
    ELSE
      RETURN QUERY SELECT 'agent_typing'::text,
                          jsonb_build_object('error', 'duplicate_actuator', 'name', r.name)
                     FROM emp_repeats(p_actuators) r;
    END IF;
  END IF;
  IF p_learning IS NOT NULL AND NOT emp_is_object(p_learning) THEN
    RETURN QUERY SELECT * FROM gov_problem('agent_typing', '{"error":"learning_module"}');
  END IF;
  IF p_safety IS NOT NULL THEN
    IF jsonb_typeof(p_safety) <> 'array' THEN
      RETURN QUERY SELECT * FROM gov_problem('agent_typing', '{"error":"safety"}');
    ELSE
      FOR c IN SELECT e.v, e.i - 1 AS idx
                 FROM jsonb_array_elements(p_safety) WITH ORDINALITY e(v, i) ORDER BY e.i LOOP
        IF NOT (emp_is_object(c.v)
                AND coalesce(jsonb_typeof(c.v -> 'actuator') = 'string', FALSE)
                AND actuators_ok AND p_actuators @> jsonb_build_array(c.v -> 'actuator')
                AND emp_bounds_ok(c.v)) THEN
          RETURN QUERY SELECT * FROM gov_problem('agent_typing',
            jsonb_build_object('error', 'safety_constraint', 'index', c.idx));
        END IF;
      END LOOP;
    END IF;
  END IF;
  IF NOT emp_is_object(p_metadata) THEN
    RETURN QUERY SELECT * FROM gov_problem('agent_typing', '{"error":"metadata"}');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION empirical_agent_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM agent_model a,
    LATERAL empirical_agent_values_problems(a.name, a.body_spec, a.sensors, a.actuators,
                                            a.learning_module, a.safety_constraints,
                                            a.metadata) pr
   WHERE a.id = p_id;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Mechanisms (qbx.empirical.mechanism)
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION empirical_spec_problems(p_spec JSONB)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  types JSONB;
  outcomes JSONB;
  alloc JSONB;
  pay JSONB;
  val JSONB;
  bad BOOLEAN := FALSE;
BEGIN
  IF NOT emp_is_object(p_spec) THEN
    RETURN QUERY SELECT * FROM gov_problem('mechanism_typing', '{"error":"spec"}');
    RETURN;
  END IF;
  types := p_spec -> 'types';
  outcomes := p_spec -> 'outcomes';
  IF NOT emp_is_name_set(types) THEN
    RETURN QUERY SELECT * FROM gov_problem('mechanism_typing', '{"error":"types"}'); bad := TRUE;
  END IF;
  IF NOT emp_is_name_set(outcomes) THEN
    RETURN QUERY SELECT * FROM gov_problem('mechanism_typing', '{"error":"outcomes"}'); bad := TRUE;
  END IF;
  IF bad THEN RETURN; END IF;
  alloc := p_spec -> 'allocation';
  pay := p_spec -> 'payment';
  val := p_spec -> 'valuation';
  IF NOT (emp_keyed(alloc, types)
          AND NOT EXISTS (SELECT 1 FROM jsonb_array_elements_text(types) t
                           WHERE NOT (coalesce(jsonb_typeof(alloc -> t) = 'string', FALSE)
                                      AND outcomes @> jsonb_build_array(alloc -> t)))) THEN
    RETURN QUERY SELECT * FROM gov_problem('mechanism_typing', '{"error":"allocation"}');
  END IF;
  IF NOT (emp_keyed(pay, types)
          AND NOT EXISTS (SELECT 1 FROM jsonb_array_elements_text(types) t
                           WHERE NOT emp_is_number(pay -> t))) THEN
    RETURN QUERY SELECT * FROM gov_problem('mechanism_typing', '{"error":"payment"}');
  END IF;
  IF NOT (emp_keyed(val, types)
          AND NOT EXISTS (SELECT 1 FROM jsonb_array_elements_text(types) t
                           WHERE NOT (emp_keyed(val -> t, outcomes)
                                      AND NOT EXISTS (
                                        SELECT 1 FROM jsonb_array_elements_text(outcomes) o
                                         WHERE NOT emp_is_number(val -> t -> o))))) THEN
    RETURN QUERY SELECT * FROM gov_problem('mechanism_typing', '{"error":"valuation"}');
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- The utility of type t reporting r (a well-typed spec).
CREATE OR REPLACE FUNCTION empirical_utility(p_spec JSONB, p_t TEXT, p_r TEXT) RETURNS NUMERIC AS $$
  SELECT emp_num(p_spec -> 'valuation' -> p_t -> (p_spec -> 'allocation' ->> p_r))
         - emp_num(p_spec -> 'payment' -> p_r);
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION empirical_ic_failures(p_spec JSONB)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT 'mechanism_ic'::text,
         jsonb_build_object('type', t.v, 'report', r.v,
                            'gain', empirical_utility(p_spec, t.v, r.v)
                                    - empirical_utility(p_spec, t.v, t.v))
    FROM jsonb_array_elements_text(p_spec -> 'types') WITH ORDINALITY t(v, i)
   CROSS JOIN jsonb_array_elements_text(p_spec -> 'types') WITH ORDINALITY r(v, i)
   WHERE r.v <> t.v
     AND empirical_utility(p_spec, t.v, r.v) > empirical_utility(p_spec, t.v, t.v)
   ORDER BY t.i, r.i;
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION empirical_ir_failures(p_spec JSONB)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT 'mechanism_ir'::text,
         jsonb_build_object('type', t.v, 'utility', empirical_utility(p_spec, t.v, t.v))
    FROM jsonb_array_elements_text(p_spec -> 'types') WITH ORDINALITY t(v, i)
   WHERE empirical_utility(p_spec, t.v, t.v) < 0
   ORDER BY t.i;
$$ LANGUAGE sql IMMUTABLE;

CREATE OR REPLACE FUNCTION empirical_mechanism_values_problems(
  p_name TEXT, p_spec JSONB, p_constraints JSONB, p_metadata JSONB
) RETURNS TABLE(reason TEXT, details JSONB) AS $$
DECLARE
  n INT := 0;
  pr RECORD;
BEGIN
  IF gov_blank(p_name) THEN
    RETURN QUERY SELECT * FROM gov_problem('mechanism_typing', '{"error":"name"}'); n := n + 1;
  END IF;
  FOR pr IN SELECT * FROM empirical_spec_problems(p_spec) LOOP
    RETURN QUERY SELECT pr.reason, pr.details; n := n + 1;
  END LOOP;
  IF p_constraints IS NOT NULL
     AND NOT (emp_is_object(p_constraints)
              AND (NOT p_constraints ? 'ic' OR jsonb_typeof(p_constraints -> 'ic') = 'boolean')
              AND (NOT p_constraints ? 'ir' OR jsonb_typeof(p_constraints -> 'ir') = 'boolean')) THEN
    RETURN QUERY SELECT * FROM gov_problem('mechanism_typing', '{"error":"constraints"}'); n := n + 1;
  END IF;
  IF NOT emp_is_object(p_metadata) THEN
    RETURN QUERY SELECT * FROM gov_problem('mechanism_typing', '{"error":"metadata"}'); n := n + 1;
  END IF;
  IF n > 0 THEN RETURN; END IF;
  IF p_constraints -> 'ic' = 'true'::jsonb THEN
    RETURN QUERY SELECT * FROM empirical_ic_failures(p_spec);
  END IF;
  IF p_constraints -> 'ir' = 'true'::jsonb THEN
    RETURN QUERY SELECT * FROM empirical_ir_failures(p_spec);
  END IF;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

CREATE OR REPLACE FUNCTION empirical_mechanism_problems(p_id UUID)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
  SELECT pr.* FROM mechanism m,
    LATERAL empirical_mechanism_values_problems(m.name, m.mechanism_spec,
                                                m.incentive_constraints, m.metadata) pr
   WHERE m.id = p_id;
$$ LANGUAGE sql STABLE;

-- ---------------------------------------------------------------------------
-- Logging and batch checks
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION empirical_record(p_table TEXT, p_id UUID, p_reason TEXT, p_details JSONB)
RETURNS VOID AS $$
BEGIN
  INSERT INTO empirical_violation (subject_table, subject_id, reason, details)
  VALUES (p_table, p_id, p_reason, coalesce(p_details, '{}'::jsonb));
END;
$$ LANGUAGE plpgsql;

-- The problems of one row (p_batch FALSE: write-time checks only).
CREATE OR REPLACE FUNCTION empirical_problems_of(p_table TEXT, p_id UUID, p_batch BOOLEAN)
RETURNS TABLE(reason TEXT, details JSONB) AS $$
BEGIN
  CASE p_table
    WHEN 'uncertainty_type' THEN RETURN QUERY SELECT * FROM empirical_uncertainty_problems(p_id);
    WHEN 'measurement_contract' THEN RETURN QUERY SELECT * FROM empirical_contract_problems(p_id);
    WHEN 'measurement_bundle' THEN RETURN QUERY SELECT * FROM empirical_bundle_problems(p_id, p_batch);
    WHEN 'measurement_validation' THEN RETURN QUERY SELECT * FROM empirical_validation_problems(p_id);
    WHEN 'dynamical_model' THEN RETURN QUERY SELECT * FROM empirical_model_problems(p_id);
    WHEN 'simulation_run' THEN RETURN QUERY SELECT * FROM empirical_simulation_problems(p_id);
    WHEN 'agent_model' THEN RETURN QUERY SELECT * FROM empirical_agent_problems(p_id);
    WHEN 'mechanism' THEN RETURN QUERY SELECT * FROM empirical_mechanism_problems(p_id);
  END CASE;
END;
$$ LANGUAGE plpgsql;

-- Check one row: log every problem; returns their number.
CREATE OR REPLACE FUNCTION empirical_check_row(p_table TEXT, p_id UUID, p_batch BOOLEAN DEFAULT TRUE)
RETURNS INT AS $$
DECLARE
  pr RECORD;
  n INT := 0;
BEGIN
  FOR pr IN SELECT * FROM empirical_problems_of(p_table, p_id, p_batch) LOOP
    PERFORM empirical_record(p_table, p_id, pr.reason, pr.details);
    n := n + 1;
  END LOOP;
  RETURN n;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION empirical_check_raise(p_n INT, p_what TEXT) RETURNS VOID AS $$
BEGIN
  IF p_n > 0 AND functor_is_strict() THEN
    RAISE EXCEPTION '% (% problem(s))', p_what, p_n;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- Every row of every empirical table.  Returns the number of problems found.
CREATE OR REPLACE FUNCTION check_empirical() RETURNS INT AS $$
DECLARE
  t RECORD;
  n INT := 0;
BEGIN
  FOR t IN SELECT 'uncertainty_type' AS tb, id FROM uncertainty_type
           UNION ALL SELECT 'measurement_contract', id FROM measurement_contract
           UNION ALL SELECT 'measurement_bundle', id FROM measurement_bundle
           UNION ALL SELECT 'measurement_validation', id FROM measurement_validation
           UNION ALL SELECT 'dynamical_model', id FROM dynamical_model
           UNION ALL SELECT 'simulation_run', id FROM simulation_run
           UNION ALL SELECT 'agent_model', id FROM agent_model
           UNION ALL SELECT 'mechanism', id FROM mechanism LOOP
    n := n + empirical_check_row(t.tb, t.id);
  END LOOP;
  PERFORM empirical_check_raise(n, 'Empirical tables have problems');
  RETURN n;
END;
$$ LANGUAGE plpgsql;

-- ---------------------------------------------------------------------------
-- Write-time tier
-- ---------------------------------------------------------------------------
-- Generic row check (write-time checks only): log, and raise in strict mode.
CREATE OR REPLACE FUNCTION trg_check_empirical_row() RETURNS trigger AS $$
DECLARE
  n INT;
BEGIN
  n := empirical_check_row(TG_TABLE_NAME, NEW.id, FALSE);
  PERFORM empirical_check_raise(n, format('%s row %s is not well formed', TG_TABLE_NAME, NEW.id));
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_check_empirical_row ON uncertainty_type;
CREATE TRIGGER trg_check_empirical_row AFTER INSERT OR UPDATE ON uncertainty_type
FOR EACH ROW EXECUTE FUNCTION trg_check_empirical_row();
DROP TRIGGER IF EXISTS trg_check_empirical_row ON measurement_contract;
CREATE TRIGGER trg_check_empirical_row AFTER INSERT OR UPDATE ON measurement_contract
FOR EACH ROW EXECUTE FUNCTION trg_check_empirical_row();
DROP TRIGGER IF EXISTS trg_check_empirical_row ON measurement_bundle;
CREATE TRIGGER trg_check_empirical_row AFTER INSERT OR UPDATE ON measurement_bundle
FOR EACH ROW EXECUTE FUNCTION trg_check_empirical_row();
DROP TRIGGER IF EXISTS trg_check_empirical_row ON dynamical_model;
CREATE TRIGGER trg_check_empirical_row AFTER INSERT OR UPDATE ON dynamical_model
FOR EACH ROW EXECUTE FUNCTION trg_check_empirical_row();
DROP TRIGGER IF EXISTS trg_check_empirical_row ON simulation_run;
CREATE TRIGGER trg_check_empirical_row AFTER INSERT OR UPDATE ON simulation_run
FOR EACH ROW EXECUTE FUNCTION trg_check_empirical_row();
DROP TRIGGER IF EXISTS trg_check_empirical_row ON agent_model;
CREATE TRIGGER trg_check_empirical_row AFTER INSERT OR UPDATE ON agent_model
FOR EACH ROW EXECUTE FUNCTION trg_check_empirical_row();
DROP TRIGGER IF EXISTS trg_check_empirical_row ON mechanism;
CREATE TRIGGER trg_check_empirical_row AFTER INSERT OR UPDATE ON mechanism
FOR EACH ROW EXECUTE FUNCTION trg_check_empirical_row();
-- The validation log is append-only: only inserts are checked here.
DROP TRIGGER IF EXISTS trg_check_empirical_row ON measurement_validation;
CREATE TRIGGER trg_check_empirical_row AFTER INSERT ON measurement_validation
FOR EACH ROW EXECUTE FUNCTION trg_check_empirical_row();

-- The validation log is append-only: an UPDATE, DELETE or TRUNCATE is logged
-- (and refused in strict mode).  A foreign-key SET NULL (deleting a bundle or
-- contract that validations refer to) is an UPDATE and is logged too.
CREATE OR REPLACE FUNCTION trg_empirical_append_only() RETURNS trigger AS $$
BEGIN
  PERFORM empirical_record(TG_TABLE_NAME, CASE WHEN TG_LEVEL = 'ROW' THEN OLD.id END,
                           'log_mutation', jsonb_build_object('table', TG_TABLE_NAME, 'op', TG_OP));
  IF functor_is_strict() THEN
    RAISE EXCEPTION '% on % refused: the log is append-only', TG_OP, TG_TABLE_NAME;
  END IF;
  IF TG_OP = 'DELETE' THEN RETURN OLD; END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_empirical_append_only ON measurement_validation;
CREATE TRIGGER trg_empirical_append_only BEFORE UPDATE OR DELETE ON measurement_validation
FOR EACH ROW EXECUTE FUNCTION trg_empirical_append_only();
DROP TRIGGER IF EXISTS trg_empirical_append_only_truncate ON measurement_validation;
CREATE TRIGGER trg_empirical_append_only_truncate BEFORE TRUNCATE ON measurement_validation
FOR EACH STATEMENT EXECUTE FUNCTION trg_empirical_append_only();

-- ---------------------------------------------------------------------------
-- Writers.  Each refuses input with a problem.  Rows inserted directly are
-- checked by the triggers and in batch.
-- ---------------------------------------------------------------------------
CREATE OR REPLACE FUNCTION empirical_refuse(p_what TEXT, p_problems JSONB) RETURNS VOID AS $$
BEGIN
  IF p_problems IS NOT NULL AND jsonb_array_length(p_problems) > 0 THEN
    RAISE EXCEPTION '%: % (%)', p_what, p_problems -> 0 ->> 'reason', p_problems -> 0 -> 'details';
  END IF;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION empirical_problems_json(p_table TEXT, p_id UUID, p_batch BOOLEAN)
RETURNS JSONB AS $$
  SELECT coalesce(jsonb_agg(jsonb_build_object('reason', pr.reason, 'details', pr.details)), '[]')
    FROM empirical_problems_of(p_table, p_id, p_batch) pr;
$$ LANGUAGE sql;

CREATE OR REPLACE FUNCTION register_uncertainty_type(p_name TEXT, p_descriptor JSONB)
RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  INSERT INTO uncertainty_type (name, descriptor) VALUES (p_name, p_descriptor)
  RETURNING id INTO new_id;
  PERFORM empirical_refuse('register_uncertainty_type',
                           empirical_problems_json('uncertainty_type', new_id, FALSE));
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Register a contract; p_uncertainty names an uncertainty type (NULL: none).
CREATE OR REPLACE FUNCTION register_measurement_contract(
  p_name TEXT, p_observable TEXT, p_tests JSONB,
  p_body JSONB DEFAULT '{}'::jsonb, p_precision JSONB DEFAULT '{}'::jsonb,
  p_version TEXT DEFAULT '1.0.0', p_uncertainty TEXT DEFAULT NULL, p_mapping TEXT DEFAULT NULL
) RETURNS UUID AS $$
DECLARE
  u_id UUID;
  new_id UUID;
BEGIN
  IF p_uncertainty IS NOT NULL THEN
    SELECT id INTO u_id FROM uncertainty_type WHERE name = p_uncertainty;
    IF u_id IS NULL THEN
      RAISE EXCEPTION 'register_measurement_contract: unknown uncertainty type %', p_uncertainty;
    END IF;
    PERFORM empirical_refuse('register_measurement_contract (uncertainty type)',
                             empirical_problems_json('uncertainty_type', u_id, FALSE));
  END IF;
  INSERT INTO measurement_contract (name, observable_id, mapping_function, expected_precision,
                                    validation_tests, body, version, uncertainty_type_id)
  VALUES (p_name, p_observable, p_mapping, p_precision, p_tests, p_body, p_version, u_id)
  RETURNING id INTO new_id;
  PERFORM empirical_refuse('register_measurement_contract',
                           empirical_problems_json('measurement_contract', new_id, FALSE));
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION record_measurement_bundle(
  p_observations JSONB, p_sensor TEXT DEFAULT NULL,
  p_context JSONB DEFAULT '{}'::jsonb, p_provenance JSONB DEFAULT '{}'::jsonb
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  INSERT INTO measurement_bundle (sensor_id, observations, context, provenance)
  VALUES (p_sensor, p_observations, p_context, p_provenance)
  RETURNING id INTO new_id;
  PERFORM empirical_refuse('record_measurement_bundle',
                           empirical_problems_json('measurement_bundle', new_id, FALSE));
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Validate a bundle against a contract: records the validation (ok, report),
-- sets the bundle's validated / validation_report, and returns ok.
CREATE OR REPLACE FUNCTION validate_measurement_bundle(
  p_bundle_id UUID, p_contract_id UUID
) RETURNS BOOLEAN AS $$
DECLARE
  rep JSONB;
  ok BOOLEAN;
BEGIN
  IF NOT EXISTS (SELECT 1 FROM measurement_bundle WHERE id = p_bundle_id) THEN
    RAISE EXCEPTION 'validate_measurement_bundle: bundle % not found', p_bundle_id;
  END IF;
  IF NOT EXISTS (SELECT 1 FROM measurement_contract WHERE id = p_contract_id) THEN
    RAISE EXCEPTION 'validate_measurement_bundle: contract % not found', p_contract_id;
  END IF;
  PERFORM empirical_refuse('validate_measurement_bundle', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM empirical_validation_input_problems(p_bundle_id, p_contract_id)));
  rep := empirical_compute_report(p_bundle_id, p_contract_id);
  ok := jsonb_array_length(rep) = 0;
  INSERT INTO measurement_validation (bundle_id, contract_id, ok, report)
  VALUES (p_bundle_id, p_contract_id, ok, rep);
  UPDATE measurement_bundle SET validated = ok, validation_report = rep WHERE id = p_bundle_id;
  RETURN ok;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION register_dynamical_model(
  p_name TEXT, p_type TEXT, p_spec TEXT, p_config JSONB DEFAULT '{}'::jsonb
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  PERFORM empirical_refuse('register_dynamical_model', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM empirical_model_values_problems(p_name, p_type, p_spec, p_config, '{}'::jsonb)));
  INSERT INTO dynamical_model (name, model_type, model_spec, solver_config)
  VALUES (p_name, p_type, p_spec, p_config)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION record_simulation_run(
  p_model UUID, p_initial JSONB, p_solver TEXT DEFAULT NULL,
  p_tolerance DOUBLE PRECISION DEFAULT NULL, p_result_uri TEXT DEFAULT NULL,
  p_summary JSONB DEFAULT NULL, p_started TIMESTAMPTZ DEFAULT now(),
  p_finished TIMESTAMPTZ DEFAULT NULL
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  PERFORM empirical_refuse('record_simulation_run', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM empirical_simulation_values_problems(
        EXISTS (SELECT 1 FROM dynamical_model WHERE id = p_model), p_initial, p_solver,
        p_tolerance, p_result_uri, p_summary, p_started, p_finished)));
  INSERT INTO simulation_run (model_id, initial_conditions, solver_used, tolerance, result_uri,
                              result_summary, started_at, finished_at)
  VALUES (p_model, p_initial, p_solver, p_tolerance, p_result_uri, p_summary, p_started, p_finished)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION register_agent_model(
  p_name TEXT, p_body JSONB DEFAULT NULL, p_sensors JSONB DEFAULT NULL,
  p_actuators JSONB DEFAULT NULL, p_learning JSONB DEFAULT NULL, p_safety JSONB DEFAULT NULL
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  PERFORM empirical_refuse('register_agent_model', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM empirical_agent_values_problems(p_name, p_body, p_sensors, p_actuators, p_learning,
                                           p_safety, '{}'::jsonb)));
  INSERT INTO agent_model (name, body_spec, sensors, actuators, learning_module, safety_constraints)
  VALUES (p_name, p_body, p_sensors, p_actuators, p_learning, p_safety)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;

-- Register a mechanism; its claimed incentive properties must hold.
CREATE OR REPLACE FUNCTION register_mechanism(
  p_name TEXT, p_spec JSONB, p_constraints JSONB DEFAULT '{}'::jsonb
) RETURNS UUID AS $$
DECLARE new_id UUID;
BEGIN
  PERFORM empirical_refuse('register_mechanism', (
    SELECT coalesce(jsonb_agg(jsonb_build_object('reason', reason, 'details', details)), '[]')
      FROM empirical_mechanism_values_problems(p_name, p_spec, p_constraints, '{}'::jsonb)));
  INSERT INTO mechanism (name, mechanism_spec, incentive_constraints)
  VALUES (p_name, p_spec, p_constraints)
  RETURNING id INTO new_id;
  RETURN new_id;
END;
$$ LANGUAGE plpgsql;
