//! The 75D Triune Logos Plenum
//!
//! The Plenum is the canonical invariant representation of any ingested entity.
//! Every word, letter, address, or feature vector maps deterministically to a
//! single point in R^75.
//!
//! ## The Three Trees (24D Seeds)
//!
//! - **Life Tree** (dims 1-8): The structural/physical encoding
//! - **Knowledge Tree** (dims 9-16): The logical/relational encoding  
//! - **Wisdom Tree** (dims 17-24): The pneumatic/spiritual encoding
//!
//! ## The Cross as Bridge
//!
//! The Cross is not merely symbolic - it is the mathematical bridge that allows
//! meaning to propagate coherently from 8D (E8 lattice) through 75D (Plenum)
//! to infinite dimensions (the Logos). The vertical beam connects heaven and earth
//! (dimensions); the horizontal beam connects all languages and domains.
//!
//! Christ's position at the intersection is the FIXED POINT - the only coordinate
//! that remains invariant under ALL Weyl reflections, ALL functor transformations,
//! ALL language translations. This is why meaning can exist at all.

use crate::metabolism::snap_with_metabolism;
use sha2::{Sha256, Digest};

/// The 75-dimensional Plenum vector
#[derive(Debug, Clone)]
pub struct Plenum75D {
    /// The full 75D coordinates
    pub coords: [f64; 75],
    /// The three 8D seed vectors (Life, Knowledge, Wisdom)
    pub seeds: [[f64; 8]; 3],
    /// The snapped E8 roots for each seed
    pub snapped_seeds: [[f64; 8]; 3],
    /// Cross-couplings (the three witnesses)
    pub witnesses: [f64; 3],
    /// Whether this Plenum passes the three-witness test
    pub witness_pass: bool,
    /// The linguistic polarity (Hebrew/Greek/Aramaic)
    pub polarity: Polarity,
}

/// Linguistic polarity classification
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Polarity {
    /// Ascending/Structural (Hebrew) - positive net coordinate sum
    Hebrew,
    /// Descending/Pneumatic (Greek) - negative net coordinate sum
    Greek,
    /// Origin/Bridge (Aramaic) - zero net coordinate sum
    Aramaic,
}

/// The golden ratio threshold for witness consensus
pub const WITNESS_THRESHOLD: f64 = 0.618;

/// Small perturbations for the three trees
const EPSILON_LIFE: f64 = 0.0;
const EPSILON_KNOWLEDGE: f64 = 1e-4;
const EPSILON_WISDOM: f64 = 2e-4;

impl Plenum75D {
    /// Construct a 75D Plenum from any input feature vector
    pub fn from_features(input: &[f64]) -> Self {
        let seed_life = Self::project_to_8d(input, EPSILON_LIFE, 0);
        let seed_knowledge = Self::project_to_8d(input, EPSILON_KNOWLEDGE, 1);
        let seed_wisdom = Self::project_to_8d(input, EPSILON_WISDOM, 2);
        
        let snap_life = snap_with_metabolism(&seed_life);
        let snap_knowledge = snap_with_metabolism(&seed_knowledge);
        let snap_wisdom = snap_with_metabolism(&seed_wisdom);
        
        let snapped_seeds = [
            snap_life.snapped,
            snap_knowledge.snapped,
            snap_wisdom.snapped,
        ];
        
        let witness_lk = Self::inner_product(&seed_life, &seed_knowledge);
        let witness_kw = Self::inner_product(&seed_knowledge, &seed_wisdom);
        let witness_wl = Self::inner_product(&seed_wisdom, &seed_life);
        let witnesses = [witness_lk, witness_kw, witness_wl];
        
        let witness_pass = witnesses.iter().all(|&w| w >= WITNESS_THRESHOLD);
        let moments = Self::compute_moments(&seed_life, &seed_knowledge, &seed_wisdom);
        let hash_padding = Self::compute_hash_padding(&snapped_seeds);
        
        let mut coords = [0.0; 75];
        coords[0..8].copy_from_slice(&seed_life);
        coords[8..16].copy_from_slice(&seed_knowledge);
        coords[16..24].copy_from_slice(&seed_wisdom);
        coords[24..36].copy_from_slice(&moments);
        coords[36] = witness_lk;
        coords[37] = witness_kw;
        coords[38] = witness_wl;
        coords[39] = witness_lk * witness_lk;
        coords[40] = witness_kw * witness_kw;
        coords[41] = witness_wl * witness_wl;
        coords[42..75].copy_from_slice(&hash_padding);
        
        let norm: f64 = coords.iter().map(|x| x * x).sum::<f64>().sqrt();
        if norm > 1e-12 {
            for c in &mut coords {
                *c /= norm;
            }
        }
        
        let net_sum: f64 = snapped_seeds.iter().flat_map(|s| s.iter()).sum();
        let polarity = if net_sum > 0.01 {
            Polarity::Hebrew
        } else if net_sum < -0.01 {
            Polarity::Greek
        } else {
            Polarity::Aramaic
        };
        
        Plenum75D {
            coords,
            seeds: [seed_life, seed_knowledge, seed_wisdom],
            snapped_seeds,
            witnesses,
            witness_pass,
            polarity,
        }
    }
    
    /// Construct a Plenum from a text string
    pub fn from_text(text: &str) -> Self {
        let features: Vec<f64> = text.chars()
            .map(|c| c as u32 as f64 / 65536.0)
            .collect();
        Self::from_features(&features)
    }
    
    fn project_to_8d(input: &[f64], epsilon: f64, tree_index: usize) -> [f64; 8] {
        let mut seed = [0.0; 8];
        if input.is_empty() { return seed; }
        
        for (i, &val) in input.iter().enumerate() {
            seed[i % 8] += val;
        }
        
        let norm: f64 = seed.iter().map(|x| x * x).sum::<f64>().sqrt();
        if norm > 1e-12 {
            for s in &mut seed { *s /= norm; }
        }
        seed[tree_index % 8] += epsilon;
        seed
    }
    
    fn inner_product(a: &[f64; 8], b: &[f64; 8]) -> f64 {
        a.iter().zip(b.iter()).map(|(x, y)| x * y).sum()
    }
    
    fn compute_moments(life: &[f64; 8], knowledge: &[f64; 8], wisdom: &[f64; 8]) -> [f64; 12] {
        let mut moments = [0.0; 12];
        for i in 0..8 {
            moments[i] = (life[i].powi(2) + knowledge[i].powi(2) + wisdom[i].powi(2)) / 3.0;
        }
        moments[8] = life[0] * knowledge[0];
        moments[9] = knowledge[0] * wisdom[0];
        moments[10] = wisdom[0] * life[0];
        moments[11] = life[0] * knowledge[0] * wisdom[0];
        moments
    }
    
    fn compute_hash_padding(snapped: &[[f64; 8]; 3]) -> [f64; 33] {
        let mut hasher = Sha256::new();
        for seed in snapped {
            for &val in seed {
                hasher.update(val.to_le_bytes());
            }
        }
        let hash = hasher.finalize();
        let mut padding = [0.0; 33];
        for i in 0..32 {
            padding[i] = (hash[i] as f64 / 127.5) - 1.0;
        }
        padding[32] = (hash.iter().map(|&b| b as u32).sum::<u32>() % 256) as f64 / 127.5 - 1.0;
        padding
    }
    
    /// Compute the torus distance to another Plenum
    pub fn torus_distance(&self, other: &Plenum75D) -> f64 {
        let mut dist_sq = 0.0;
        for i in 0..75 {
            let diff = self.coords[i] - other.coords[i];
            let wrapped = if diff > 0.5 { diff - 1.0 } else if diff < -0.5 { diff + 1.0 } else { diff };
            dist_sq += wrapped * wrapped;
        }
        dist_sq.sqrt()
    }
    
    /// Apply a functor transformation
    pub fn apply_functor(&self, functor_name: &str) -> Plenum75D {
        let mut new_coords = self.coords;
        match functor_name {
            "hebrew_to_greek" => {
                for i in 0..24 { new_coords[i] = -new_coords[i]; }
            },
            "greek_to_latin" => {
                let cos_t = 0.866;
                let sin_t = 0.5;
                for i in 0..8 {
                    let k = new_coords[8 + i];
                    let w = new_coords[16 + i];
                    new_coords[8 + i] = k * cos_t - w * sin_t;
                    new_coords[16 + i] = k * sin_t + w * cos_t;
                }
            },
            "to_machine_code" => {
                for c in &mut new_coords { *c = (*c * 256.0).round() / 256.0; }
            },
            _ => {}
        }
        let mut result = self.clone();
        result.coords = new_coords;
        result
    }
    
    /// Check if this Plenum represents a valid, coherent meaning
    pub fn is_coherent(&self) -> bool {
        self.witness_pass && self.coords.iter().all(|&c| c.is_finite())
    }
    
    /// Get the Beast classification
    pub fn beast_classification(&self) -> &'static str {
        let life = &self.seeds[0];
        let lion_score = life[0].abs() + life[1].abs();
        let ox_score = life[2].abs() + life[3].abs();
        let eagle_score = life[4].abs() + life[5].abs();
        let man_score = life[6].abs() + life[7].abs();
        let max_score = lion_score.max(ox_score).max(eagle_score).max(man_score);
        
        if (lion_score - max_score).abs() < 1e-10 { "Lion (Fire/Courage)" }
        else if (ox_score - max_score).abs() < 1e-10 { "Ox (Earth/Service)" }
        else if (eagle_score - max_score).abs() < 1e-10 { "Eagle (Air/Vision)" }
        else { "Man (Water/Wisdom)" }
    }
}

/// The Cross - the fixed point that bridges all dimensions
#[derive(Debug, Clone)]
pub struct Cross {
    pub e8_center: [f64; 8],
    pub plenum_center: [f64; 75],
    pub vertical_beam: Vec<f64>,
    pub horizontal_beam: Vec<f64>,
}

impl Cross {
    pub fn new() -> Self {
        Cross {
            e8_center: [0.0; 8],
            plenum_center: [0.0; 75],
            vertical_beam: vec![1.0, 8.0, 24.0, 75.0, f64::INFINITY],
            horizontal_beam: vec![-2.0, -1.0, 0.0, 1.0, 2.0],
        }
    }
    
    pub fn project_upward(&self, e8_point: &[f64; 8]) -> Plenum75D {
        Plenum75D::from_features(e8_point)
    }
    
    pub fn project_downward(&self, plenum: &Plenum75D) -> [f64; 8] {
        plenum.snapped_seeds[0]
    }
}

impl Default for Cross {
    fn default() -> Self { Self::new() }
}
