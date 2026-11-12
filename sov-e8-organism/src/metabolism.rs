//! Metabolic Functions for the E₈ Organism
//!
//! The organism feeds on negentropy - ordered information extracted from chaos.
//! When a point is "snapped" to the E₈ lattice, the residual (distance to nearest
//! lattice point) represents the negentropy harvested.
//!
//! The organism breathes through the 112/128 split:
//! - Inhale: Process through integer roots (D₈ sublattice)
//! - Exhale: Process through half-integer roots (8-demicube)
//! - Pause: The Aramaic origin (Φ⁰) between breaths

use pyo3::prelude::*;
use crate::roots::RootType;

/// The phase of the organism's respiration cycle
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RespirationPhase {
    /// Processing through integer roots (Hebrew/structural)
    Inhale,
    /// Processing through half-integer roots (Greek/pneumatic)
    Exhale,
    /// The pause between breaths (Aramaic/origin)
    Pause,
}

/// The result of a metabolic snap operation
#[pyclass]
#[derive(Debug, Clone)]
pub struct NegentropicYield {
    /// The snapped lattice point
    #[pyo3(get)]
    pub snapped: [f64; 8],
    /// The residual vector (input - snapped)
    #[pyo3(get)]
    pub residual: [f64; 8],
    /// The negentropy harvested (magnitude of residual)
    #[pyo3(get)]
    pub negentropy: f64,
    /// The type of root we snapped to
    pub root_type: RootType,
    /// The respiration phase this snap belongs to
    pub phase: RespirationPhase,
    /// Coherence score (inverse of negentropy, normalized)
    #[pyo3(get)]
    pub coherence: f64,
}

#[pymethods]
impl NegentropicYield {
    #[getter]
    fn get_phase(&self) -> String {
        match self.phase {
            RespirationPhase::Inhale => "inhale".to_string(),
            RespirationPhase::Exhale => "exhale".to_string(),
            RespirationPhase::Pause => "pause".to_string(),
        }
    }
    
    #[getter]
    fn get_root_type(&self) -> String {
        match self.root_type {
            RootType::Integer => "integer".to_string(),
            RootType::HalfInteger => "half_integer".to_string(),
        }
    }
}

/// Snap a point to the E₈ lattice and extract metabolic information
/// 
/// This is the core metabolic operation. The organism:
/// 1. Finds the nearest E₈ lattice point (the "food")
/// 2. Computes the residual (the "waste" that becomes energy)
/// 3. Determines the respiration phase based on root type
pub fn snap_with_metabolism(target: &[f64; 8]) -> NegentropicYield {
    // Snap to nearest E₈ point using the two-family approach
    let (snapped, root_type) = snap_to_e8_with_type(target);
    
    // Compute residual
    let mut residual = [0.0; 8];
    let mut residual_norm_sq = 0.0;
    for i in 0..8 {
        residual[i] = target[i] - snapped[i];
        residual_norm_sq += residual[i] * residual[i];
    }
    let negentropy = residual_norm_sq.sqrt();
    
    // Determine respiration phase
    let phase = if negentropy < 1e-10 {
        RespirationPhase::Pause // Exact lattice point - the pause between breaths
    } else {
        match root_type {
            RootType::Integer => RespirationPhase::Inhale,
            RootType::HalfInteger => RespirationPhase::Exhale,
        }
    };
    
    // Coherence is inverse of negentropy, normalized to [0, 1]
    // Maximum negentropy in E₈ is bounded by the covering radius ≈ 1
    let coherence = 1.0 / (1.0 + negentropy);
    
    NegentropicYield {
        snapped,
        residual,
        negentropy,
        root_type,
        phase,
        coherence,
    }
}

/// Snap to E₈ lattice and return the root type
fn snap_to_e8_with_type(target: &[f64; 8]) -> ([f64; 8], RootType) {
    // Try integer family
    let (int_snap, int_dist) = snap_to_integer_family(target);
    
    // Try half-integer family
    let (half_snap, half_dist) = snap_to_half_integer_family(target);
    
    if int_dist <= half_dist {
        (int_snap, RootType::Integer)
    } else {
        (half_snap, RootType::HalfInteger)
    }
}

/// Snap to the integer family of E₈ (D₈ sublattice)
fn snap_to_integer_family(target: &[f64; 8]) -> ([f64; 8], f64) {
    let mut snapped = [0.0; 8];
    let mut sum = 0i32;
    
    // Round each coordinate to nearest integer
    for i in 0..8 {
        snapped[i] = target[i].round();
        sum += snapped[i] as i32;
    }
    
    // Ensure even sum (E₈ constraint)
    if sum % 2 != 0 {
        // Find coordinate with largest rounding error and adjust
        let mut max_err = 0.0;
        let mut max_idx = 0;
        for i in 0..8 {
            let err = (target[i] - snapped[i]).abs();
            if err > max_err {
                max_err = err;
                max_idx = i;
            }
        }
        // Adjust by ±1 to fix parity
        if target[max_idx] > snapped[max_idx] {
            snapped[max_idx] += 1.0;
        } else {
            snapped[max_idx] -= 1.0;
        }
    }
    
    // Compute distance
    let dist: f64 = (0..8).map(|i| {
        let d = target[i] - snapped[i];
        d * d
    }).sum::<f64>().sqrt();
    
    (snapped, dist)
}

/// Snap to the half-integer family of E₈ (8-demicube)
fn snap_to_half_integer_family(target: &[f64; 8]) -> ([f64; 8], f64) {
    let mut snapped = [0.0; 8];
    let mut minus_count = 0;
    
    // Round each coordinate to nearest half-integer
    for i in 0..8 {
        let shifted = target[i] - 0.5;
        let rounded = shifted.round();
        snapped[i] = rounded + 0.5;
        if snapped[i] < 0.0 {
            minus_count += 1;
        }
    }
    
    // Ensure even number of negative signs (E₈ constraint)
    if minus_count % 2 != 0 {
        // Find coordinate with largest rounding error and flip sign
        let mut max_err = 0.0;
        let mut max_idx = 0;
        for i in 0..8 {
            let err = (target[i] - snapped[i]).abs();
            if err > max_err {
                max_err = err;
                max_idx = i;
            }
        }
        // Flip by ±1 to fix parity
        if snapped[max_idx] > 0.0 {
            snapped[max_idx] -= 1.0;
        } else {
            snapped[max_idx] += 1.0;
        }
    }
    
    // Compute distance
    let dist: f64 = (0..8).map(|i| {
        let d = target[i] - snapped[i];
        d * d
    }).sum::<f64>().sqrt();
    
    (snapped, dist)
}

/// Compute the total negentropy accumulated by the organism
pub fn total_negentropy(yields: &[NegentropicYield]) -> f64 {
    yields.iter().map(|y| y.negentropy).sum()
}

/// Compute the respiration balance (inhale vs exhale ratio)
/// 
/// A healthy organism maintains balance. Too much inhale = rigidity.
/// Too much exhale = dissolution.
pub fn respiration_balance(yields: &[NegentropicYield]) -> f64 {
    let inhale_count = yields.iter()
        .filter(|y| y.phase == RespirationPhase::Inhale)
        .count() as f64;
    let exhale_count = yields.iter()
        .filter(|y| y.phase == RespirationPhase::Exhale)
        .count() as f64;
    
    if exhale_count < 1e-10 {
        return f64::INFINITY; // All inhale, no exhale
    }
    
    inhale_count / exhale_count
}

/// The ideal respiration ratio (112/128 ≈ 0.875)
pub const IDEAL_RESPIRATION_RATIO: f64 = 112.0 / 128.0;

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_snap_to_origin() {
        let target = [0.0; 8];
        let result = snap_with_metabolism(&target);
        assert!(result.negentropy < 1e-10, "Origin should snap exactly");
        assert_eq!(result.phase, RespirationPhase::Pause);
    }
    
    #[test]
    fn test_snap_to_integer_root() {
        let target = [1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        let result = snap_with_metabolism(&target);
        assert!(result.negentropy < 1e-10, "Integer root should snap exactly");
        assert_eq!(result.root_type, RootType::Integer);
    }
    
    #[test]
    fn test_snap_to_half_integer_root() {
        let target = [0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5];
        let result = snap_with_metabolism(&target);
        assert!(result.negentropy < 1e-10, "Half-integer root should snap exactly");
        assert_eq!(result.root_type, RootType::HalfInteger);
    }
    
    #[test]
    fn test_negentropy_extraction() {
        // A point not on the lattice should yield negentropy
        let target = [0.3, 0.3, 0.3, 0.3, 0.3, 0.3, 0.3, 0.3];
        let result = snap_with_metabolism(&target);
        assert!(result.negentropy > 0.0, "Off-lattice point should yield negentropy");
        assert!(result.coherence < 1.0, "Off-lattice point should have coherence < 1");
    }
}
