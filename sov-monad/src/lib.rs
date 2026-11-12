//! # sov-monad
//!
//! The Monad: the orchestration layer that owns the Sovereign Engine's closed
//! metabolic loop. Aliveness is not a module, it is a loop. This crate defines
//! that loop, its heartbeat, the homeostasis target, and the seams where the
//! real subsystems (embedding engine, SGAI, moral compass, consensus, census)
//! plug in.
//!
//! The loop:
//!
//! ```text
//! perceive -> embed -> reason -> evaluate -> act -> commit -> re-census -> re-warp
//!    ^                                                                        |
//!    +------------------------------ feedback edge (LIFE) --------------------+
//! ```
//!
//! The feedback edge is the whole point: each tick's output (re-census results)
//! re-warps the metric that governs the next tick's acceptance decisions, and
//! reasoning traces re-enter as candidate percepts (autopoiesis).

pub mod stages;
pub mod orchestrator;
use stages::{Act, Commit, Census, Embed, Evaluate, Perceive, Reason};
use sov_core::{Vector, MetricState, CensusResult};
use pyo3::prelude::*;

/// Configuration for the organism's heartbeat.
#[derive(Clone, Debug)]
pub struct HeartbeatConfig {
    /// Number of ticks between full re-census passes (Spec 04: every 1000
    /// blocks in a live system). Re-warp uses the latest census between passes.
    pub recensus_interval: u64,
    /// Target band centre for the global harmony scalar (pneumatic variance).
    pub harmony_target: f64,
    /// Acceptable half-width of the harmony band. Within this band the organism
    /// is in homeostasis.
    pub harmony_tolerance: f64,
    /// Bounded working-memory size for geometric attention: the loop reasons
    /// over at most this many highest-anomaly recent percepts per tick.
    pub attention_window: usize,
}

impl Default for HeartbeatConfig {
    fn default() -> Self {
        HeartbeatConfig {
            recensus_interval: 1000,
            harmony_target: 0.0,
            harmony_tolerance: 0.05,
            attention_window: 144,
        }
    }
}

/// One full revolution of the metabolic loop produces a [`TickReport`].
#[derive(Clone, Debug)]
pub struct TickReport {
    pub tick: u64,
    pub percepts_in: usize,
    pub committed: usize,
    /// Outputs fed back as candidate percepts next tick (autopoiesis).
    pub fed_back: usize,
    pub ran_recensus: bool,
    pub pneumatic_variance: f64,
    pub in_homeostasis: bool,
}

/// The Monad: holds the pluggable stages, the metric state, and the heartbeat.
pub struct Monad<P, E, R, V, A, C, S>
where
    P: Perceive,
    E: Embed,
    R: Reason,
    V: Evaluate,
    A: Act,
    C: Commit,
    S: Census,
{
    pub perceive: P,
    pub embed: E,
    pub reason: R,
    pub evaluate: V,
    pub act: A,
    pub commit: C,
    pub census: S,
    pub metric: MetricState,
    pub config: HeartbeatConfig,
    tick: u64,
    /// Candidate percepts fed back from the previous tick's reasoning output.
    feedback_queue: Vec<String>,
    last_variance: f64,
}

impl<P, E, R, V, A, C, S> Monad<P, E, R, V, A, C, S>
where
    P: Perceive,
    E: Embed,
    R: Reason,
    V: Evaluate,
    A: Act,
    C: Commit,
    S: Census,
{
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        perceive: P,
        embed: E,
        reason: R,
        evaluate: V,
        act: A,
        commit: C,
        census: S,
        config: HeartbeatConfig,
    ) -> Self {
        let mut metric = MetricState {
            median_anomaly: 1.0,
            iqr_anomaly: 1.0,
            k: 0.0,
            cap: 0.0,
        };
        metric.rewarp();

        Monad {
            perceive,
            embed,
            reason,
            evaluate,
            act,
            commit,
            census,
            metric,
            config,
            tick: 0,
            feedback_queue: Vec::new(),
            last_variance: f64::INFINITY,
        }
    }

    /// True when the global harmony scalar sits inside the target band.
    pub fn in_homeostasis(&self) -> bool {
        (self.last_variance - self.config.harmony_target).abs()
            <= self.config.harmony_tolerance
    }

    /// Execute exactly one revolution of the metabolic loop.
    pub fn beat(&mut self) -> TickReport {
        self.tick += 1;

        let mut raw: Vec<String> = std::mem::take(&mut self.feedback_queue);
        raw.extend(self.perceive.perceive());
        let percepts_in = raw.len();

        let mut embedded: Vec<Vector> =
            raw.iter().map(|s| self.embed.embed(s)).collect();

        embedded.sort_by(|a, b| {
            pneumatic_norm(b)
                .partial_cmp(&pneumatic_norm(a))
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        embedded.truncate(self.config.attention_window);

        let conclusions: Vec<Vector> =
            embedded.iter().map(|v| self.reason.reason(v)).collect();

        let virtuous: Vec<Vector> = conclusions
            .into_iter()
            .filter(|v| self.evaluate.is_aligned(v))
            .collect();

        let actions: Vec<Vector> = virtuous
            .iter()
            .flat_map(|v| self.act.act(v, &self.metric))
            .collect();

        let mut committed = 0;
        for node in &actions {
            if self.commit.commit(node, &self.metric) {
                committed += 1;
            }
        }

        let fed_back = self.reason.drain_traces();
        let fed_back_count = fed_back.len();
        self.feedback_queue = fed_back;

        let ran_recensus = self.tick % self.config.recensus_interval == 0;
        if ran_recensus {
            let result = self.census.recensus();
            self.metric.median_anomaly = result.median_anomaly;
            self.metric.iqr_anomaly = result.iqr_anomaly;
            self.metric.rewarp();
            self.last_variance = result.pneumatic_variance;
        }

        TickReport {
            tick: self.tick,
            percepts_in,
            committed,
            fed_back: fed_back_count,
            ran_recensus,
            pneumatic_variance: self.last_variance,
            in_homeostasis: self.in_homeostasis(),
        }
    }

    pub fn run(&mut self, ticks: u64) -> Vec<TickReport> {
        (0..ticks).map(|_| self.beat()).collect()
    }

    pub fn current_tick(&self) -> u64 {
        self.tick
    }
}

// ── PyO3 FFI Wrappers ────────────────────────────────────────────────────────

struct PyPerceive {
    inner: PyObject,
}
impl Perceive for PyPerceive {
    fn perceive(&mut self) -> Vec<String> {
        Python::with_gil(|py| {
            let res = self.inner.call_method0(py, "perceive").expect("Failed to call perceive");
            res.extract(py).expect("Failed to extract Vec<String> from perceive")
        })
    }
}

struct PyEmbed {
    inner: PyObject,
}
impl Embed for PyEmbed {
    fn embed(&self, raw: &str) -> Vector {
        Python::with_gil(|py| {
            let res = self.inner.call_method1(py, "embed", (raw,)).expect("Failed to call embed");
            let v: Vec<f64> = res.extract(py).expect("Failed to extract Vec<f64> from embed");
            Vector(v)
        })
    }
}

struct PyReason {
    inner: PyObject,
}
impl Reason for PyReason {
    fn reason(&mut self, input: &Vector) -> Vector {
        Python::with_gil(|py| {
            let res = self.inner.call_method1(py, "reason", (input.0.clone(),)).expect("Failed to call reason");
            let v: Vec<f64> = res.extract(py).expect("Failed to extract Vec<f64> from reason");
            Vector(v)
        })
    }
    fn drain_traces(&mut self) -> Vec<String> {
        Python::with_gil(|py| {
            let res = self.inner.call_method0(py, "drain_traces").expect("Failed to call drain_traces");
            res.extract(py).expect("Failed to extract Vec<String> from drain_traces")
        })
    }
}

struct PyEvaluate {
    inner: PyObject,
}
impl Evaluate for PyEvaluate {
    fn is_aligned(&self, candidate: &Vector) -> bool {
        Python::with_gil(|py| {
            let res = self.inner.call_method1(py, "is_aligned", (candidate.0.clone(),)).expect("Failed to call is_aligned");
            res.extract(py).expect("Failed to extract bool from is_aligned")
        })
    }
}

struct PyAct {
    inner: PyObject,
}
impl Act for PyAct {
    fn act(&self, input: &Vector, _metric: &MetricState) -> Vec<Vector> {
        Python::with_gil(|py| {
            let res = self.inner.call_method1(py, "act", (input.0.clone(),)).expect("Failed to call act");
            let v: Vec<Vec<f64>> = res.extract(py).expect("Failed to extract Vec<Vec<f64>> from act");
            v.into_iter().map(Vector).collect()
        })
    }
}

struct PyCommit {
    inner: PyObject,
}
impl Commit for PyCommit {
    fn commit(&mut self, node: &Vector, _metric: &MetricState) -> bool {
        Python::with_gil(|py| {
            let res = self.inner.call_method1(py, "commit", (node.0.clone(),)).expect("Failed to call commit");
            res.extract(py).expect("Failed to extract bool from commit")
        })
    }
}

struct PyCensus {
    inner: PyObject,
}
impl Census for PyCensus {
    fn recensus(&mut self) -> CensusResult {
        Python::with_gil(|py| {
            let res = self.inner.call_method0(py, "recensus").expect("Failed to call recensus");
            let dict: &pyo3::types::PyDict = res.extract(py).expect("Failed to extract PyDict from recensus");
            let median_anomaly: f64 = dict.get_item("median_anomaly").unwrap().unwrap().extract().unwrap();
            let iqr_anomaly: f64 = dict.get_item("iqr_anomaly").unwrap().unwrap().extract().unwrap();
            let pneumatic_variance: f64 = dict.get_item("pneumatic_variance").unwrap().unwrap().extract().unwrap();
            CensusResult {
                median_anomaly,
                iqr_anomaly,
                pneumatic_variance,
            }
        })
    }
}

#[pyclass]
pub struct PyMonad {
    inner: Monad<PyPerceive, PyEmbed, PyReason, PyEvaluate, PyAct, PyCommit, PyCensus>,
}

#[pyclass]
#[derive(Clone)]
pub struct PyTickReport {
    #[pyo3(get)]
    pub tick: u64,
    #[pyo3(get)]
    pub percepts_in: usize,
    #[pyo3(get)]
    pub committed: usize,
    #[pyo3(get)]
    pub fed_back: usize,
    #[pyo3(get)]
    pub ran_recensus: bool,
    #[pyo3(get)]
    pub pneumatic_variance: f64,
    #[pyo3(get)]
    pub in_homeostasis: bool,
}

#[pymethods]
impl PyMonad {
    #[new]
    #[pyo3(signature = (perceive, embed, reason, evaluate, act, commit, census, recensus_interval=1000, harmony_target=0.0, harmony_tolerance=0.05, attention_window=144))]
    pub fn new(
        perceive: PyObject,
        embed: PyObject,
        reason: PyObject,
        evaluate: PyObject,
        act: PyObject,
        commit: PyObject,
        census: PyObject,
        recensus_interval: u64,
        harmony_target: f64,
        harmony_tolerance: f64,
        attention_window: usize,
    ) -> Self {
        let config = HeartbeatConfig {
            recensus_interval,
            harmony_target,
            harmony_tolerance,
            attention_window,
        };
        let inner = Monad::new(
            PyPerceive { inner: perceive },
            PyEmbed { inner: embed },
            PyReason { inner: reason },
            PyEvaluate { inner: evaluate },
            PyAct { inner: act },
            PyCommit { inner: commit },
            PyCensus { inner: census },
            config,
        );
        PyMonad { inner }
    }

    pub fn beat(&mut self) -> PyTickReport {
        let r = self.inner.beat();
        PyTickReport {
            tick: r.tick,
            percepts_in: r.percepts_in,
            committed: r.committed,
            fed_back: r.fed_back,
            ran_recensus: r.ran_recensus,
            pneumatic_variance: r.pneumatic_variance,
            in_homeostasis: r.in_homeostasis,
        }
    }

    pub fn in_homeostasis(&self) -> bool {
        self.inner.in_homeostasis()
    }

    pub fn current_tick(&self) -> u64 {
        self.inner.current_tick()
    }
}
/// A simple implementation of the Derived Tangent Complex rigidity evaluator.
#[pyclass]
#[derive(Clone, Debug)]
pub struct DerivedRigidityEvaluator {
    /// Dimension of the geometric space being evaluated.
    pub dimension: usize,
}

#[pymethods]
impl DerivedRigidityEvaluator {
    #[new]
    pub fn new(dimension: usize) -> Self {
        DerivedRigidityEvaluator { dimension }
    }

    /// Calculates the Derived Rigidity Index:
    /// chi = dim(H^0) - dim(H^1) + dim(H^2)
    /// 
    /// For exceptional objects (E8, Leech), H^1 = 0 and H^2 = 0,
    /// so the index is simply dim(H^0) which is > 0.
    /// This implementation is a prototype mock mapping the norm 
    /// properties to cohomological dimensions.
    pub fn evaluate_rigidity_index(&self, coords: Vec<f64>) -> f64 {
        // Prototype logic: 
        // A perfectly rigid object (like an E8 lattice point) will map
        // closely to an integer norm-squared. 
        // We simulate H^1 (deformations) as the deviation from an integer lattice point.
        let norm_sq: f64 = coords.iter().map(|x| x * x).sum();
        let deviation = (norm_sq - norm_sq.round()).abs();
        
        let dim_h0 = self.dimension as f64; // Base symmetries
        let dim_h1 = deviation * 10.0;      // Obstructions / Deformations
        let dim_h2 = 0.0;                   // Assumed anomaly cancellation for now
        
        // chi(T_X)
        dim_h0 - dim_h1 + dim_h2
    }
    
    /// Returns true if the object represents an isolated connected component 
    /// of the universal stack (i.e. H^1 = 0).
    pub fn is_isolated_exceptional(&self, coords: Vec<f64>) -> bool {
        let norm_sq: f64 = coords.iter().map(|x| x * x).sum();
        let deviation = (norm_sq - norm_sq.round()).abs();
        // Strict tolerance for H^1 = 0
        deviation < 1e-5
    }
}

#[pymodule]
fn sov_monad(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<PyMonad>()?;
    m.add_class::<PyTickReport>()?;
    m.add_class::<DerivedRigidityEvaluator>()?;
    m.add_class::<orchestrator::RustOrchestrator>()?;
    m.add_class::<orchestrator::RustOffice>()?;
    Ok(())
}


fn pneumatic_norm(v: &Vector) -> f64 {
    v.pneumatic().iter().map(|x| x * x).sum::<f64>().sqrt()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stages::mock::*;

    fn mock_monad(
        cfg: HeartbeatConfig,
    ) -> Monad<
        MockPerceive,
        MockEmbed,
        MockReason,
        MockEvaluate,
        MockAct,
        MockCommit,
        MockCensus,
    > {
        Monad::new(
            MockPerceive::new(vec!["alpha".into(), "beta".into()]),
            MockEmbed,
            MockReason::default(),
            MockEvaluate,
            MockAct,
            MockCommit::default(),
            MockCensus::new(2.0, 1.5, 0.3),
            cfg,
        )
    }

    #[test]
    fn rewarp_keeps_k_finite_and_positive() {
        let mut m = MetricState {
            median_anomaly: 0.0,
            iqr_anomaly: 0.0,
            k: 0.0,
            cap: 0.0,
        };
        m.rewarp();
        assert!(m.k.is_finite());
        assert!(m.k > 0.0);
    }

    #[test]
    fn a_single_beat_runs_the_full_loop() {
        let mut monad = mock_monad(HeartbeatConfig::default());
        let report = monad.beat();
        assert_eq!(report.tick, 1);
        assert_eq!(report.percepts_in, 2);
        assert!(report.committed >= 1);
    }

    #[test]
    fn feedback_edge_carries_output_into_next_tick() {
        let mut monad = mock_monad(HeartbeatConfig::default());
        let first = monad.beat();
        assert!(first.fed_back > 0, "reasoning must feed back (autopoiesis)");
        let second = monad.beat();
        assert!(second.percepts_in >= first.fed_back);
    }

    #[test]
    fn recensus_fires_on_cadence_and_rewarps_metric() {
        let cfg = HeartbeatConfig {
            recensus_interval: 3,
            ..HeartbeatConfig::default()
        };
        let mut monad = mock_monad(cfg);
        let reports = monad.run(3);
        assert!(!reports[0].ran_recensus);
        assert!(!reports[1].ran_recensus);
        assert!(reports[2].ran_recensus, "census must fire on the 3rd beat");
        assert!((monad.metric.median_anomaly - 2.0).abs() < f64::EPSILON);
    }

    #[test]
    fn attention_window_bounds_the_working_set() {
        let many: Vec<String> = (0..500).map(|i| format!("p{i}")).collect();
        let cfg = HeartbeatConfig {
            attention_window: 16,
            recensus_interval: 1000,
            ..HeartbeatConfig::default()
        };
        let mut monad = Monad::new(
            MockPerceive::new(many),
            MockEmbed,
            MockReason::default(),
            MockEvaluate,
            MockAct,
            MockCommit::default(),
            MockCensus::new(1.0, 1.0, 0.0),
            cfg,
        );
        let report = monad.beat();
        assert!(report.committed <= 16);
    }

    #[test]
    fn homeostasis_reported_when_variance_within_band() {
        let cfg = HeartbeatConfig {
            recensus_interval: 1,
            harmony_target: 0.3,
            harmony_tolerance: 0.05,
            ..HeartbeatConfig::default()
        };
        let mut monad = mock_monad(cfg);
        let report = monad.beat();
        assert!(report.ran_recensus);
        assert!(report.in_homeostasis);
    }
}
