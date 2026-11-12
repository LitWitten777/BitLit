//! E₈ Root System
//!
//! The E₈ root system consists of 240 roots in 8-dimensional space:
//! - 112 "integer" roots: all coordinates are integers, sum is even
//! - 128 "half-integer" roots: all coordinates are ±1/2, even number of minus signs
//!
//! This split corresponds to the Hebrew (structural) and Greek (pneumatic) polarities.

use std::collections::HashSet;

/// The type of an E₈ root
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RootType {
    /// Integer coordinates (D₈ sublattice) - Hebrew/Structural/Inhale
    Integer,
    /// Half-integer coordinates (8-demicube) - Greek/Pneumatic/Exhale  
    HalfInteger,
}

/// An E₈ root vector with metadata
#[derive(Debug, Clone)]
pub struct E8Root {
    pub coords: [f64; 8],
    pub root_type: RootType,
    /// Net polarity: sum of all coordinates
    pub polarity: f64,
    /// Index in the canonical ordering (0-239)
    pub index: usize,
}

impl E8Root {
    pub fn new(coords: [f64; 8], index: usize) -> Self {
        let is_half = coords.iter().any(|&x| (x - x.round()).abs() > 0.1);
        let root_type = if is_half { RootType::HalfInteger } else { RootType::Integer };
        let polarity: f64 = coords.iter().sum();
        E8Root { coords, root_type, polarity, index }
    }
    
    /// Returns the linguistic polarity classification
    pub fn linguistic_polarity(&self) -> &'static str {
        if self.polarity > 0.01 {
            "Hebrew/Ascending"
        } else if self.polarity < -0.01 {
            "Greek/Descending"
        } else {
            "Aramaic/Origin"
        }
    }
    
    /// Squared norm (should be 2 for all E₈ roots)
    pub fn norm_squared(&self) -> f64 {
        self.coords.iter().map(|x| x * x).sum()
    }
}

/// The 8 simple roots of E₈ (Bourbaki numbering)
/// These generate all 240 roots via Weyl reflections
pub const E8_SIMPLE_ROOTS: [[f64; 8]; 8] = [
    // α₁: Standard D₈ simple root
    [1.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    // α₂: The branching node (connects to α₄)
    [0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5],
    // α₃
    [0.0, 1.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0],
    // α₄ (central node)
    [0.0, 0.0, 1.0, -1.0, 0.0, 0.0, 0.0, 0.0],
    // α₅
    [0.0, 0.0, 0.0, 1.0, -1.0, 0.0, 0.0, 0.0],
    // α₆
    [0.0, 0.0, 0.0, 0.0, 1.0, -1.0, 0.0, 0.0],
    // α₇
    [0.0, 0.0, 0.0, 0.0, 0.0, 1.0, -1.0, 0.0],
    // α₈
    [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, -1.0],
];

/// Generate all 240 E₈ roots
/// 
/// The roots come in two families:
/// 1. Integer type (112 roots): permutations of (±1, ±1, 0, 0, 0, 0, 0, 0)
/// 2. Half-integer type (128 roots): (±1/2, ±1/2, ..., ±1/2) with even # of minus signs
pub fn generate_all_240_roots() -> Vec<E8Root> {
    let mut roots = Vec::with_capacity(240);
    let mut seen: HashSet<[i64; 8]> = HashSet::new();
    
    // Helper to canonicalize for deduplication
    let to_key = |coords: &[f64; 8]| -> [i64; 8] {
        let mut key = [0i64; 8];
        for i in 0..8 {
            key[i] = (coords[i] * 2.0).round() as i64;
        }
        key
    };
    
    // Family 1: Integer roots (±1, ±1, 0, 0, 0, 0, 0, 0)
    // Choose 2 positions out of 8, then choose signs
    for i in 0..8 {
        for j in (i+1)..8 {
            for si in [-1.0, 1.0] {
                for sj in [-1.0, 1.0] {
                    let mut coords = [0.0; 8];
                    coords[i] = si;
                    coords[j] = sj;
                    let key = to_key(&coords);
                    if seen.insert(key) {
                        roots.push(E8Root::new(coords, roots.len()));
                    }
                }
            }
        }
    }
    
    // Family 2: Half-integer roots (±1/2)^8 with even number of minus signs
    for mask in 0u8..=255 {
        let minus_count = mask.count_ones();
        if minus_count % 2 == 0 {
            let mut coords = [0.5; 8];
            for i in 0..8 {
                if (mask >> i) & 1 == 1 {
                    coords[i] = -0.5;
                }
            }
            let key = to_key(&coords);
            if seen.insert(key) {
                roots.push(E8Root::new(coords, roots.len()));
            }
        }
    }
    
    assert_eq!(roots.len(), 240, "E₈ must have exactly 240 roots");
    roots
}

/// Get the 112 integer roots (D₈ sublattice) - the "inhale" set
pub fn get_integer_roots() -> Vec<E8Root> {
    generate_all_240_roots()
        .into_iter()
        .filter(|r| r.root_type == RootType::Integer)
        .collect()
}

/// Get the 128 half-integer roots (8-demicube) - the "exhale" set
pub fn get_half_integer_roots() -> Vec<E8Root> {
    generate_all_240_roots()
        .into_iter()
        .filter(|r| r.root_type == RootType::HalfInteger)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_root_count() {
        let roots = generate_all_240_roots();
        assert_eq!(roots.len(), 240);
    }
    
    #[test]
    fn test_root_split() {
        let roots = generate_all_240_roots();
        let int_count = roots.iter().filter(|r| r.root_type == RootType::Integer).count();
        let half_count = roots.iter().filter(|r| r.root_type == RootType::HalfInteger).count();
        assert_eq!(int_count, 112, "Should have 112 integer roots");
        assert_eq!(half_count, 128, "Should have 128 half-integer roots");
    }
    
    #[test]
    fn test_root_norms() {
        let roots = generate_all_240_roots();
        for root in &roots {
            let norm_sq = root.norm_squared();
            assert!((norm_sq - 2.0).abs() < 1e-10, "All E₈ roots have norm² = 2");
        }
    }
}
