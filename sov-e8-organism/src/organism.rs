//! The E₈ Organism
//!
//! A living mathematical entity that:
//! - Feeds on negentropy (ordered information)
//! - Breathes through the 112/128 root split
//! - Maintains coherence through Weyl symmetries
//! - Grows through root activation
//! - Reproduces through lattice splitting

use pyo3::prelude::*;
use std::collections::{HashMap, HashSet};

use crate::roots::{E8Root, RootType, generate_all_240_roots};
use crate::weyl::{weyl_reflect, generate_weyl_orbit, path_to_positive_chamber};
use crate::cartan::{root_adjacency, RootRelation, is_dominant, weyl_vector};
use crate::metabolism::{NegentropicYield, snap_with_metabolism, RespirationPhase, 
                        total_negentropy, respiration_balance, IDEAL_RESPIRATION_RATIO};

/// The E₈ Organism - a living mathematical entity
#[pyclass]
pub struct E8Organism {
    /// The organism's unique identifier
    #[pyo3(get)]
    pub id: String,
    
    /// Active roots (the organism's "genome" - which of 240 roots are active)
    active_roots: HashSet<usize>,
    
    /// All 240 roots (cached)
    all_roots: Vec<E8Root>,
    
    /// Accumulated negentropy (the organism's "energy")
    #[pyo3(get)]
    pub total_negentropy: f64,
    
    /// Metabolic history
    metabolic_history: Vec<NegentropicYield>,
    
    /// Memory defects (imperfect snaps that persist)
    memory_defects: Vec<[f64; 8]>,
    
    /// Current respiration phase
    current_phase: RespirationPhase,
    
    /// Age (number of metabolic cycles)
    #[pyo3(get)]
    pub age: u64,
    
    /// Health score (0.0 to 1.0)
    #[pyo3(get)]
    pub health: f64,
}

#[pymethods]
impl E8Organism {
    /// Create a new organism from a seed root
    #[new]
    #[pyo3(signature = (id, seed_root_index=None))]
    pub fn new(id: String, seed_root_index: Option<usize>) -> Self {
        let all_roots = generate_all_240_roots();
        let mut active_roots = HashSet::new();
        
        // Start with a single root (the "zygote")
        let seed_idx = seed_root_index.unwrap_or(0);
        active_roots.insert(seed_idx);
        
        E8Organism {
            id,
            active_roots,
            all_roots,
            total_negentropy: 0.0,
            metabolic_history: Vec::new(),
            memory_defects: Vec::new(),
            current_phase: RespirationPhase::Pause,
            age: 0,
            health: 1.0,
        }
    }
    
    /// Feed the organism a point (extract negentropy)
    pub fn feed(&mut self, point: Vec<f64>) -> PyResult<(f64, String)> {
        if point.len() != 8 {
            return Err(pyo3::exceptions::PyValueError::new_err("Point must be 8D"));
        }
        
        let mut arr = [0.0; 8];
        arr.copy_from_slice(&point);
        
        let yield_result = snap_with_metabolism(&arr);
        
        // Accumulate negentropy
        self.total_negentropy += yield_result.negentropy;
        
        // Update respiration phase
        self.current_phase = yield_result.phase;
        
        // Store in history
        self.metabolic_history.push(yield_result.clone());
        
        // If coherence is low, this becomes a memory defect
        if yield_result.coherence < 0.5 {
            self.memory_defects.push(yield_result.residual);
        }
        
        // Age the organism
        self.age += 1;
        
        // Update health based on respiration balance
        self.update_health();
        
        let phase_str = match yield_result.phase {
            RespirationPhase::Inhale => "inhale",
            RespirationPhase::Exhale => "exhale",
            RespirationPhase::Pause => "pause",
        };
        
        Ok((yield_result.negentropy, phase_str.to_string()))
    }
    
    /// Grow the organism by activating adjacent roots
    pub fn grow(&mut self) -> PyResult<usize> {
        let mut new_roots = Vec::new();
        
        // Find roots adjacent to currently active roots
        for &active_idx in &self.active_roots {
            let active_root = &self.all_roots[active_idx];
            
            for (idx, candidate) in self.all_roots.iter().enumerate() {
                if self.active_roots.contains(&idx) {
                    continue;
                }
                
                let relation = root_adjacency(&active_root.coords, &candidate.coords);
                if relation == RootRelation::Adjacent {
                    new_roots.push(idx);
                }
            }
        }
        
        // Activate new roots (limited by available negentropy)
        let activation_cost = 0.1; // Cost per root activation
        let mut activated = 0;
        
        for idx in new_roots {
            if self.total_negentropy >= activation_cost {
                self.active_roots.insert(idx);
                self.total_negentropy -= activation_cost;
                activated += 1;
            } else {
                break;
            }
        }
        
        Ok(activated)
    }
    
    /// Attend to a specific root (bring it to focus via Weyl reflections)
    pub fn attend(&self, root_index: usize) -> PyResult<Vec<usize>> {
        if root_index >= 240 {
            return Err(pyo3::exceptions::PyValueError::new_err("Root index must be 0-239"));
        }
        
        let root = &self.all_roots[root_index];
        let path = path_to_positive_chamber(&root.coords);
        
        Ok(path)
    }
    
    /// Get the organism's genome (active root indices)
    pub fn genome(&self) -> Vec<usize> {
        self.active_roots.iter().cloned().collect()
    }
    
    /// Get the genome as a 240-bit binary string
    pub fn genome_binary(&self) -> String {
        let mut bits = String::with_capacity(240);
        for i in 0..240 {
            if self.active_roots.contains(&i) {
                bits.push('1');
            } else {
                bits.push('0');
            }
        }
        bits
    }
    
    /// Get the current respiration balance
    pub fn respiration_balance(&self) -> f64 {
        respiration_balance(&self.metabolic_history)
    }
    
    /// Get the number of memory defects (aging indicator)
    pub fn defect_count(&self) -> usize {
        self.memory_defects.len()
    }
    
    /// Get the count of active roots by type
    pub fn root_type_counts(&self) -> (usize, usize) {
        let mut int_count = 0;
        let mut half_count = 0;
        
        for &idx in &self.active_roots {
            match self.all_roots[idx].root_type {
                RootType::Integer => int_count += 1,
                RootType::HalfInteger => half_count += 1,
            }
        }
        
        (int_count, half_count)
    }
    
    /// Check if the organism is in homeostasis
    pub fn is_homeostatic(&self) -> bool {
        let balance = self.respiration_balance();
        let deviation = (balance - IDEAL_RESPIRATION_RATIO).abs();
        deviation < 0.2 && self.health > 0.7
    }
    
    /// Attempt mitosis (cell division)
    /// Returns a new organism if successful, None otherwise
    pub fn mitosis(&mut self) -> PyResult<Option<E8Organism>> {
        // Mitosis requires sufficient energy and active roots
        let min_roots_for_mitosis = 20;
        let energy_cost = 5.0;
        
        if self.active_roots.len() < min_roots_for_mitosis {
            return Ok(None);
        }
        
        if self.total_negentropy < energy_cost {
            return Ok(None);
        }
        
        // Split the genome
        let genome: Vec<usize> = self.active_roots.iter().cloned().collect();
        let mid = genome.len() / 2;
        
        let mut child_roots = HashSet::new();
        for &idx in &genome[mid..] {
            child_roots.insert(idx);
            self.active_roots.remove(&idx);
        }
        
        // Pay the energy cost
        self.total_negentropy -= energy_cost;
        
        // Create child organism
        let child = E8Organism {
            id: format!("{}_child_{}", self.id, self.age),
            active_roots: child_roots,
            all_roots: self.all_roots.clone(),
            total_negentropy: energy_cost / 2.0, // Child gets half the cost as starting energy
            metabolic_history: Vec::new(),
            memory_defects: Vec::new(),
            current_phase: RespirationPhase::Pause,
            age: 0,
            health: 1.0,
        };
        
        Ok(Some(child))
    }
    
    /// Get a summary of the organism's state
    pub fn status(&self) -> String {
        let (int_count, half_count) = self.root_type_counts();
        format!(
            "E8Organism '{}': age={}, health={:.2}, energy={:.2}, roots={}/{} (int/half: {}/{}), defects={}",
            self.id,
            self.age,
            self.health,
            self.total_negentropy,
            self.active_roots.len(),
            240,
            int_count,
            half_count,
            self.memory_defects.len()
        )
    }
}

impl E8Organism {
    /// Update health based on various factors
    fn update_health(&mut self) {
        // Factor 1: Respiration balance
        let balance = if self.metabolic_history.len() > 10 {
            respiration_balance(&self.metabolic_history)
        } else {
            IDEAL_RESPIRATION_RATIO
        };
        let balance_score = 1.0 - (balance - IDEAL_RESPIRATION_RATIO).abs().min(1.0);
        
        // Factor 2: Defect accumulation (aging)
        let defect_penalty = (self.memory_defects.len() as f64 / 100.0).min(0.5);
        
        // Factor 3: Root activation coverage
        let coverage = self.active_roots.len() as f64 / 240.0;
        let coverage_score = if coverage < 0.1 {
            coverage * 5.0 // Bonus for early growth
        } else if coverage > 0.9 {
            1.0 - (coverage - 0.9) * 5.0 // Penalty for over-saturation
        } else {
            0.5 + coverage * 0.5
        };
        
        // Combine factors
        self.health = (balance_score * 0.4 + coverage_score * 0.4 + (1.0 - defect_penalty) * 0.2)
            .max(0.0)
            .min(1.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_organism_creation() {
        let org = E8Organism::new("test".to_string(), None);
        assert_eq!(org.active_roots.len(), 1);
        assert_eq!(org.age, 0);
        assert_eq!(org.health, 1.0);
    }
    
    #[test]
    fn test_organism_feeding() {
        let mut org = E8Organism::new("test".to_string(), None);
        let point = vec![0.3, 0.3, 0.3, 0.3, 0.3, 0.3, 0.3, 0.3];
        let result = org.feed(point);
        assert!(result.is_ok());
        assert!(org.total_negentropy > 0.0);
        assert_eq!(org.age, 1);
    }
    
    #[test]
    fn test_organism_growth() {
        let mut org = E8Organism::new("test".to_string(), None);
        
        // Feed to accumulate energy
        for _ in 0..100 {
            let point = vec![0.3, 0.3, 0.3, 0.3, 0.3, 0.3, 0.3, 0.3];
            org.feed(point).unwrap();
        }
        
        let initial_roots = org.active_roots.len();
        org.grow().unwrap();
        assert!(org.active_roots.len() >= initial_roots);
    }
}
