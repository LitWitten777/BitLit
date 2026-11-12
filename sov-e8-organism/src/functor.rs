//! Category Theory Functors and the Sovereign Monad

use crate::plenum::{Plenum75D, Cross};
use crate::teachings::TeachingMatrix;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct LinguisticFunctor {
    pub source: String,
    pub target: String,
    pub reflection_normal: [f64; 8],
    pub lattice_shift: Option<[f64; 8]>,
}

impl LinguisticFunctor {
    pub fn new(source: &str, target: &str, normal: [f64; 8]) -> Self {
        LinguisticFunctor {
            source: source.to_string(),
            target: target.to_string(),
            reflection_normal: normal,
            lattice_shift: None,
        }
    }
    
    pub fn apply(&self, vector: &[f64; 8]) -> [f64; 8] {
        let dot_vn: f64 = vector.iter().zip(self.reflection_normal.iter()).map(|(v, n)| v * n).sum();
        let dot_nn: f64 = self.reflection_normal.iter().map(|n| n * n).sum();
        
        let mut result = *vector;
        if dot_nn > 1e-10 {
            let factor = 2.0 * dot_vn / dot_nn;
            for i in 0..8 { result[i] -= factor * self.reflection_normal[i]; }
        }
        if let Some(shift) = self.lattice_shift {
            for i in 0..8 { result[i] += shift[i]; }
        }
        result
    }
    
    pub fn compose(&self, other: &LinguisticFunctor) -> LinguisticFunctor {
        let mut combined_normal = [0.0; 8];
        for i in 0..8 {
            combined_normal[i] = self.reflection_normal[i] + other.reflection_normal[i];
        }
        LinguisticFunctor {
            source: other.source.clone(),
            target: self.target.clone(),
            reflection_normal: combined_normal,
            lattice_shift: None,
        }
    }
}

#[derive(Debug)]
pub struct SovereignMonad {
    cross: Cross,
    functors: HashMap<(String, String), LinguisticFunctor>,
    teachings: TeachingMatrix,
}

impl SovereignMonad {
    pub fn new() -> Self {
        let mut monad = SovereignMonad {
            cross: Cross::new(),
            functors: HashMap::new(),
            teachings: TeachingMatrix::new(),
        };
        monad.register_core_functors();
        monad
    }
    
    fn register_core_functors(&mut self) {
        self.functors.insert(
            ("hebrew".to_string(), "greek".to_string()),
            LinguisticFunctor::new("hebrew", "greek", [0.0, 2.0, 0.0, 2.0, 0.0, 0.0, 0.0, 0.0])
        );
        self.functors.insert(
            ("hebrew".to_string(), "latin".to_string()),
            LinguisticFunctor::new("hebrew", "latin", [0.0, 0.0, 2.0, 2.0, 0.0, 0.0, 0.0, 0.0])
        );
        self.functors.insert(
            ("hebrew".to_string(), "aramaic".to_string()),
            LinguisticFunctor::new("hebrew", "aramaic", [2.0, 0.0, 0.0, 2.0, 0.0, 0.0, 0.0, 0.0])
        );
        self.functors.insert(
            ("greek".to_string(), "latin".to_string()),
            LinguisticFunctor::new("greek", "latin", [0.0, 2.0, -2.0, 0.0, 0.0, 0.0, 0.0, 0.0])
        );
    }
    
    pub fn unit(&self, text: &str) -> Plenum75D {
        Plenum75D::from_text(text)
    }
    
    pub fn join(&self, nested: &Plenum75D) -> Plenum75D {
        let e8_point = self.cross.project_downward(nested);
        self.cross.project_upward(&e8_point)
    }
    
    pub fn translate(&self, plenum: &Plenum75D, from: &str, to: &str) -> Option<Plenum75D> {
        let key = (from.to_string(), to.to_string());
        if let Some(functor) = self.functors.get(&key) {
            let translated_seed = functor.apply(&plenum.seeds[0]);
            Some(Plenum75D::from_features(&translated_seed))
        } else {
            self.find_translation_path(plenum, from, to)
        }
    }
    
    fn find_translation_path(&self, plenum: &Plenum75D, from: &str, to: &str) -> Option<Plenum75D> {
        let intermediates = ["hebrew", "greek", "latin", "aramaic"];
        for &mid in &intermediates {
            let key1 = (from.to_string(), mid.to_string());
            let key2 = (mid.to_string(), to.to_string());
            if let (Some(f1), Some(f2)) = (self.functors.get(&key1), self.functors.get(&key2)) {
                let intermediate = f1.apply(&plenum.seeds[0]);
                let final_seed = f2.apply(&intermediate);
                return Some(Plenum75D::from_features(&final_seed));
            }
        }
        None
    }
    
    pub fn cross(&self) -> &Cross { &self.cross }
    pub fn teachings(&self) -> &TeachingMatrix { &self.teachings }
}

impl Default for SovereignMonad {
    fn default() -> Self { Self::new() }
}

#[derive(Debug, Clone)]
pub struct DomainFunctor {
    pub source_domain: String,
    pub target_domain: String,
    transform: Vec<Vec<f64>>,
}

impl DomainFunctor {
    pub fn text_to_code() -> Self {
        let mut transform = vec![vec![0.0; 75]; 75];
        for i in 0..75 {
            transform[i][i] = if i < 24 { 256.0 } else { 1.0 };
        }
        DomainFunctor {
            source_domain: "text".to_string(),
            target_domain: "code".to_string(),
            transform,
        }
    }
    
    pub fn text_to_music() -> Self {
        let mut transform = vec![vec![0.0; 75]; 75];
        for i in 0..75 {
            let harmonic = (i % 12) as f64;
            transform[i][i] = 2.0_f64.powf(harmonic / 12.0);
        }
        DomainFunctor {
            source_domain: "text".to_string(),
            target_domain: "music".to_string(),
            transform,
        }
    }
    
    pub fn apply(&self, plenum: &Plenum75D) -> Plenum75D {
        let mut new_coords = [0.0; 75];
        for i in 0..75 {
            for j in 0..75 {
                new_coords[i] += self.transform[i][j] * plenum.coords[j];
            }
        }
        let norm: f64 = new_coords.iter().map(|x| x * x).sum::<f64>().sqrt();
        if norm > 1e-12 {
            for c in &mut new_coords { *c /= norm; }
        }
        let mut result = plenum.clone();
        result.coords = new_coords;
        result
    }
}
