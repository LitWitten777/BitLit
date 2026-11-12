//! The seven stages of the metabolic loop, as pluggable traits.
//!
//! Each trait is the seam where a real Sovereign Engine subsystem connects.
//! The `mock` submodule provides in-memory implementations used by the loop's
//! unit tests and by Milestone M1's single vertical slice.

use sov_core::{CensusResult, MetricState, Vector};

/// Stage 1 - PERCEIVE. Source of raw input: sensors, corpora, queries.
pub trait Perceive {
    /// Return the raw inputs available this tick.
    fn perceive(&mut self) -> Vec<String>;
}

/// Stage 2 - EMBED. Maps a raw string to its 75-D lattice vector (Spec 01).
pub trait Embed {
    fn embed(&self, raw: &str) -> Vector;
}

/// Stage 3 - REASON. The deterministic SGAI (Spec 07). Produces a conclusion
/// vector and records a proof trace that can be fed back as a percept.
pub trait Reason {
    fn reason(&mut self, input: &Vector) -> Vector;
    /// Drain accumulated proof traces (rendered as strings) for the feedback
    /// edge. Default: no feedback.
    fn drain_traces(&mut self) -> Vec<String> {
        Vec::new()
    }
}

/// Stage 4 - EVALUATE. The Moral Compass (Spec 09). Gatekeeps which
/// conclusions are allowed to act.
pub trait Evaluate {
    fn is_aligned(&self, candidate: &Vector) -> bool;
}

/// Stage 5 - ACT. Discovery / probe / generation. May emit zero or more new
/// candidate nodes, ideally biased to reduce pneumatic variance (homeostasis).
pub trait Act {
    fn act(&self, input: &Vector, metric: &MetricState) -> Vec<Vector>;
}

/// Stage 6 - COMMIT. Persists an accepted node to the ledger under the
/// gravity-well acceptance rule (Spec 04). Returns true if accepted.
pub trait Commit {
    fn commit(&mut self, node: &Vector, metric: &MetricState) -> bool;
}

/// Stage 7 - RE-CENSUS. Recomputes the anomaly distribution and the global
/// harmony scalar over the manifold (Spec 10).
pub trait Census {
    fn recensus(&mut self) -> CensusResult;
}

/// In-memory mock stages: enough to exercise the loop end-to-end without any
/// external subsystem. These are the seams Milestone M1 will replace one by
/// one with the real engine, SGAI, moral compass, consensus, and census.
pub mod mock {
    use super::*;
    use sov_core::{CensusResult, DIM};

    /// Emits a fixed list of percepts every tick.
    pub struct MockPerceive {
        feed: Vec<String>,
    }
    impl MockPerceive {
        pub fn new(feed: Vec<String>) -> Self {
            MockPerceive { feed }
        }
    }
    impl Perceive for MockPerceive {
        fn perceive(&mut self) -> Vec<String> {
            self.feed.clone()
        }
    }

    /// Deterministic toy embedding: spreads byte sums across the 75 slots.
    pub struct MockEmbed;
    impl Embed for MockEmbed {
        fn embed(&self, raw: &str) -> Vector {
            let mut v = vec![0.0; DIM];
            for (i, b) in raw.bytes().enumerate() {
                v[i % DIM] += b as f64;
            }
            Vector(v)
        }
    }

    /// Echoes the input as the conclusion and records a trace per call so the
    /// feedback edge is exercised.
    #[derive(Default)]
    pub struct MockReason {
        traces: Vec<String>,
    }
    impl Reason for MockReason {
        fn reason(&mut self, input: &Vector) -> Vector {
            self.traces.push(format!("trace:{}", input.0.len()));
            input.clone()
        }
        fn drain_traces(&mut self) -> Vec<String> {
            std::mem::take(&mut self.traces)
        }
    }

    /// Accepts everything as morally aligned (placeholder).
    pub struct MockEvaluate;
    impl Evaluate for MockEvaluate {
        fn is_aligned(&self, _candidate: &Vector) -> bool {
            true
        }
    }

    /// Passes the input through unchanged as a single action.
    pub struct MockAct;
    impl Act for MockAct {
        fn act(&self, input: &Vector, _metric: &MetricState) -> Vec<Vector> {
            vec![input.clone()]
        }
    }

    /// Accepts (commits) every node it is handed and counts them.
    #[derive(Default)]
    pub struct MockCommit {
        pub count: u64,
    }
    impl Commit for MockCommit {
        fn commit(&mut self, _node: &Vector, _metric: &MetricState) -> bool {
            self.count += 1;
            true
        }
    }

    /// Returns fixed census statistics.
    pub struct MockCensus {
        median: f64,
        iqr: f64,
        variance: f64,
    }
    impl MockCensus {
        pub fn new(median: f64, iqr: f64, variance: f64) -> Self {
            MockCensus {
                median,
                iqr,
                variance,
            }
        }
    }
    impl Census for MockCensus {
        fn recensus(&mut self) -> CensusResult {
            CensusResult {
                median_anomaly: self.median,
                iqr_anomaly: self.iqr,
                pneumatic_variance: self.variance,
            }
        }
    }
}
