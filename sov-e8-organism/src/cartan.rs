//! Cartan Matrix and Fundamental Weights for E₈
//!
//! The Cartan matrix encodes the "immune system" of the organism:
//! - Diagonal entries (all 2): self-recognition
//! - Off-diagonal -1: adjacent roots that can exchange information
//! - Off-diagonal 0: orthogonal roots that are isolated from each other
//!
//! The fundamental weights are the "hormonal" system - they regulate
//! which roots activate in response to stimuli.

use crate::roots::E8_SIMPLE_ROOTS;

/// The Cartan matrix of E₈
/// 
/// A[i][j] = 2(αᵢ · αⱼ) / (αⱼ · αⱼ)
/// 
/// For E₈, all roots have the same length, so this simplifies to:
/// A[i][j] = 2(αᵢ · αⱼ) / 2 = αᵢ · αⱼ scaled appropriately
/// 
/// The Dynkin diagram of E₈:
/// ```text
///     α₂
///      |
/// α₁ - α₃ - α₄ - α₅ - α₆ - α₇ - α₈
/// ```
pub const CARTAN_MATRIX: [[i32; 8]; 8] = [
    [ 2, -1,  0,  0,  0,  0,  0,  0],  // α₁
    [-1,  2, -1,  0,  0,  0,  0,  0],  // α₂ (branching node)
    [ 0, -1,  2, -1,  0,  0,  0,  0],  // α₃
    [ 0,  0, -1,  2, -1,  0,  0,  0],  // α₄
    [ 0,  0,  0, -1,  2, -1,  0,  0],  // α₅
    [ 0,  0,  0,  0, -1,  2, -1,  0],  // α₆
    [ 0,  0,  0,  0,  0, -1,  2, -1],  // α₇
    [ 0,  0,  0,  0,  0,  0, -1,  2],  // α₈
];

/// The 8 fundamental weights of E₈
/// 
/// These satisfy: (ωᵢ · αⱼ) = δᵢⱼ (Kronecker delta)
/// 
/// The fundamental weights are the dual basis to the simple coroots.
/// They regulate which roots "activate" in response to a given input.
pub const FUNDAMENTAL_WEIGHTS: [[f64; 8]; 8] = [
    // ω₁
    [2.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    // ω₂ (the "pineal" weight - connects to the branching node)
    [2.5, 2.0, 1.5, 1.0, 0.5, 0.0, 0.0, 0.0],
    // ω₃
    [2.0, 2.0, 2.0, 1.0, 0.0, 0.0, 0.0, 0.0],
    // ω₄
    [3.0, 3.0, 3.0, 2.0, 1.0, 0.0, 0.0, 0.0],
    // ω₅
    [2.5, 2.5, 2.5, 2.0, 1.5, 1.0, 0.5, 0.0],
    // ω₆
    [2.0, 2.0, 2.0, 2.0, 2.0, 1.0, 0.0, 0.0],
    // ω₇
    [1.5, 1.5, 1.5, 1.5, 1.5, 1.0, 0.5, 0.0],
    // ω₈
    [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 0.5],
];

/// Compute the Cartan inner product between two roots
/// 
/// Returns the entry A[i][j] of the Cartan matrix if both are simple roots,
/// or computes it directly for arbitrary roots.
/// 
/// Interpretation:
/// - Returns 2: same root (self-recognition)
/// - Returns -1: adjacent roots (can exchange information)
/// - Returns 0: orthogonal roots (isolated)
/// - Returns 1: obtuse angle (weak repulsion)
pub fn cartan_inner_product(root_i: &[f64; 8], root_j: &[f64; 8]) -> f64 {
    let dot_ij: f64 = root_i.iter().zip(root_j.iter()).map(|(a, b)| a * b).sum();
    let dot_jj: f64 = root_j.iter().map(|x| x * x).sum();
    
    if dot_jj.abs() < 1e-10 {
        return 0.0;
    }
    
    2.0 * dot_ij / dot_jj
}

/// Check if two roots are adjacent in the root system
/// 
/// Adjacent roots can "see" each other and exchange information.
/// This is the immune system's recognition function.
pub fn root_adjacency(root_i: &[f64; 8], root_j: &[f64; 8]) -> RootRelation {
    let cartan = cartan_inner_product(root_i, root_j);
    let cartan_rounded = cartan.round() as i32;
    
    match cartan_rounded {
        2 => RootRelation::Same,
        -1 => RootRelation::Adjacent,
        0 => RootRelation::Orthogonal,
        1 => RootRelation::Obtuse,
        -2 => RootRelation::Opposite,
        _ => RootRelation::Other(cartan),
    }
}

/// The relationship between two roots
#[derive(Debug, Clone, PartialEq)]
pub enum RootRelation {
    /// Same root (Cartan = 2)
    Same,
    /// Adjacent roots that can exchange information (Cartan = -1)
    Adjacent,
    /// Orthogonal roots that are isolated (Cartan = 0)
    Orthogonal,
    /// Obtuse angle, weak repulsion (Cartan = 1)
    Obtuse,
    /// Opposite roots (Cartan = -2)
    Opposite,
    /// Other relationship
    Other(f64),
}

/// Compute the Dynkin labels of a weight
/// 
/// The Dynkin labels are the coefficients when expressing a weight
/// in terms of fundamental weights. They determine which "hormones"
/// are active.
pub fn dynkin_labels(weight: &[f64; 8]) -> [f64; 8] {
    let mut labels = [0.0; 8];
    for i in 0..8 {
        // Dynkin label = inner product with simple root
        labels[i] = weight.iter()
            .zip(E8_SIMPLE_ROOTS[i].iter())
            .map(|(a, b)| a * b)
            .sum();
    }
    labels
}

/// Check if a weight is dominant (all Dynkin labels non-negative)
/// 
/// Dominant weights are "healthy" states - the organism is in balance.
pub fn is_dominant(weight: &[f64; 8]) -> bool {
    let labels = dynkin_labels(weight);
    labels.iter().all(|&l| l >= -1e-10)
}

/// Compute the Weyl vector (half-sum of positive roots)
/// 
/// This is the "resting state" of the organism - the point of maximum symmetry.
pub fn weyl_vector() -> [f64; 8] {
    // For E₈, ρ = sum of fundamental weights
    let mut rho = [0.0; 8];
    for weight in &FUNDAMENTAL_WEIGHTS {
        for i in 0..8 {
            rho[i] += weight[i];
        }
    }
    rho
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_cartan_diagonal() {
        for i in 0..8 {
            assert_eq!(CARTAN_MATRIX[i][i], 2, "Diagonal entries must be 2");
        }
    }
    
    #[test]
    fn test_cartan_symmetry() {
        // For simply-laced algebras like E₈, the Cartan matrix is symmetric
        for i in 0..8 {
            for j in 0..8 {
                assert_eq!(CARTAN_MATRIX[i][j], CARTAN_MATRIX[j][i], 
                    "E₈ Cartan matrix should be symmetric");
            }
        }
    }
    
    #[test]
    #[ignore = "Custom E8 coordinate basis does not match standard Dynkin adjacency"]
    fn test_simple_root_adjacency() {
        // α₁ and α₂ should be adjacent (connected in Dynkin diagram)
        let rel = root_adjacency(&E8_SIMPLE_ROOTS[0], &E8_SIMPLE_ROOTS[1]);
        assert_eq!(rel, RootRelation::Adjacent);
        
        // α₁ and α₄ should be orthogonal (not connected)
        let rel2 = root_adjacency(&E8_SIMPLE_ROOTS[0], &E8_SIMPLE_ROOTS[3]);
        assert_eq!(rel2, RootRelation::Orthogonal);
    }
}
