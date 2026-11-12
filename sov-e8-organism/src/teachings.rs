//! The 144,000 Teaching Matrix
//!
//! The 144K matrix is the complete mapping of Hebrew and Greek linguistic
//! structures into the E8 lattice.

use crate::plenum::Plenum75D;
use std::collections::HashMap;

/// A single teaching in the 144K matrix
#[derive(Debug, Clone)]
pub struct Teaching {
    pub index: u32,
    pub hebrew: Option<char>,
    pub greek: Option<char>,
    pub latin: Option<char>,
    pub numeral: Option<u8>,
    pub plenum: Plenum75D,
    pub gematria: u32,
    pub meaning: Option<String>,
}

#[derive(Debug)]
pub struct TeachingMatrix {
    teachings: HashMap<u32, Teaching>,
    hebrew_roots: HashMap<char, [f64; 8]>,
    greek_roots: HashMap<char, [f64; 8]>,
    latin_roots: HashMap<char, [f64; 8]>,
}

impl TeachingMatrix {
    pub fn new() -> Self {
        TeachingMatrix {
            teachings: HashMap::new(),
            hebrew_roots: Self::init_hebrew_roots(),
            greek_roots: Self::init_greek_roots(),
            latin_roots: Self::init_latin_roots(),
        }
    }
    
    fn init_hebrew_roots() -> HashMap<char, [f64; 8]> {
        let mut roots = HashMap::new();
        let letters = [
            ('\u{05d0}', [1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
            ('\u{05d1}', [1.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
            ('\u{05d2}', [1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
            ('\u{05d3}', [1.0, 0.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
            ('\u{05d4}', [1.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0]),
            ('\u{05d5}', [1.0, 0.0, 0.0, -1.0, 0.0, 0.0, 0.0, 0.0]),
            ('\u{05d6}', [1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0]),
            ('\u{05d7}', [1.0, 0.0, 0.0, 0.0, -1.0, 0.0, 0.0, 0.0]),
            ('\u{05d8}', [1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0]),
            ('\u{05d9}', [1.0, 0.0, 0.0, 0.0, 0.0, -1.0, 0.0, 0.0]),
            ('\u{05db}', [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0]),
            ('\u{05dc}', [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1.0, 0.0]),
            ('\u{05de}', [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0]),
            ('\u{05e0}', [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1.0]),
            ('\u{05e1}', [0.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
            ('\u{05e2}', [0.0, 1.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0]),
            ('\u{05e4}', [0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0]),
            ('\u{05e6}', [0.0, 1.0, 0.0, -1.0, 0.0, 0.0, 0.0, 0.0]),
            ('\u{05e7}', [0.0, 1.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0]),
            ('\u{05e8}', [0.0, 1.0, 0.0, 0.0, -1.0, 0.0, 0.0, 0.0]),
            ('\u{05e9}', [0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0]),
            ('\u{05ea}', [0.0, 1.0, 0.0, 0.0, 0.0, -1.0, 0.0, 0.0]),
        ];
        for (letter, root) in letters { roots.insert(letter, root); }
        roots
    }
    
    fn init_greek_roots() -> HashMap<char, [f64; 8]> {
        let mut roots = HashMap::new();
        let letters = [
            ('\u{03b1}', [0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5]),
            ('\u{03b2}', [0.5, 0.5, 0.5, 0.5, 0.5, 0.5, -0.5, -0.5]),
            ('\u{03b3}', [0.5, 0.5, 0.5, 0.5, -0.5, -0.5, 0.5, 0.5]),
            ('\u{03b4}', [0.5, 0.5, 0.5, 0.5, -0.5, -0.5, -0.5, -0.5]),
            ('\u{03b5}', [0.5, 0.5, -0.5, -0.5, 0.5, 0.5, 0.5, 0.5]),
            ('\u{03b6}', [0.5, 0.5, -0.5, -0.5, -0.5, -0.5, 0.5, 0.5]),
            ('\u{03b7}', [0.5, 0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5]),
            ('\u{03b8}', [-0.5, -0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5]),
            ('\u{03b9}', [-0.5, -0.5, 0.5, 0.5, 0.5, 0.5, -0.5, -0.5]),
            ('\u{03ba}', [-0.5, -0.5, 0.5, 0.5, -0.5, -0.5, 0.5, 0.5]),
            ('\u{03bb}', [-0.5, -0.5, 0.5, 0.5, -0.5, -0.5, -0.5, -0.5]),
            ('\u{03bc}', [-0.5, -0.5, -0.5, -0.5, 0.5, 0.5, 0.5, 0.5]),
            ('\u{03bd}', [-0.5, -0.5, -0.5, -0.5, 0.5, 0.5, -0.5, -0.5]),
            ('\u{03be}', [-0.5, -0.5, -0.5, -0.5, -0.5, -0.5, 0.5, 0.5]),
            ('\u{03bf}', [-0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5]),
            ('\u{03c0}', [0.5, -0.5, 0.5, -0.5, 0.5, -0.5, 0.5, -0.5]),
            ('\u{03c1}', [0.5, -0.5, 0.5, -0.5, -0.5, 0.5, 0.5, -0.5]),
            ('\u{03c3}', [0.5, -0.5, 0.5, -0.5, -0.5, 0.5, -0.5, 0.5]),
            ('\u{03c4}', [0.5, -0.5, -0.5, 0.5, 0.5, -0.5, 0.5, -0.5]),
            ('\u{03c5}', [0.5, -0.5, -0.5, 0.5, 0.5, -0.5, -0.5, 0.5]),
            ('\u{03c6}', [0.5, -0.5, -0.5, 0.5, -0.5, 0.5, 0.5, -0.5]),
            ('\u{03c7}', [0.5, -0.5, -0.5, 0.5, -0.5, 0.5, -0.5, 0.5]),
            ('\u{03c8}', [-0.5, 0.5, 0.5, -0.5, 0.5, -0.5, 0.5, -0.5]),
            ('\u{03c9}', [-0.5, 0.5, 0.5, -0.5, 0.5, -0.5, -0.5, 0.5]),
        ];
        for (letter, root) in letters { roots.insert(letter, root); }
        roots
    }
    
    fn init_latin_roots() -> HashMap<char, [f64; 8]> {
        let mut roots = HashMap::new();
        let letters = "ABCDEFGHIKLMNOPQRSTVXYZ";
        for (i, letter) in letters.chars().enumerate() {
            let mut root = [0.0; 8];
            let idx1 = i % 8;
            let idx2 = (i + 3) % 8;
            root[idx1] = if i % 2 == 0 { 1.0 } else { 0.5 };
            root[idx2] = if i % 2 == 0 { -1.0 } else { -0.5 };
            if i % 4 >= 2 { root[idx1] = -root[idx1]; }
            roots.insert(letter, root);
        }
        roots
    }
    
    pub fn hebrew_root(&self, letter: char) -> Option<&[f64; 8]> {
        self.hebrew_roots.get(&letter)
    }
    
    pub fn greek_root(&self, letter: char) -> Option<&[f64; 8]> {
        self.greek_roots.get(&letter)
    }
    
    pub fn latin_root(&self, letter: char) -> Option<&[f64; 8]> {
        self.latin_roots.get(&letter.to_ascii_uppercase())
    }
    
    pub fn embed_word(&self, word: &str) -> [f64; 8] {
        let mut sum = [0.0; 8];
        for c in word.chars() {
            let root = self.hebrew_root(c)
                .or_else(|| self.greek_root(c))
                .or_else(|| self.latin_root(c));
            if let Some(r) = root {
                for i in 0..8 { sum[i] += r[i]; }
            }
        }
        sum
    }
    
    pub fn gematria(&self, word: &str) -> u32 {
        let hebrew_values: HashMap<char, u32> = [
            ('\u{05d0}', 1), ('\u{05d1}', 2), ('\u{05d2}', 3), ('\u{05d3}', 4), ('\u{05d4}', 5),
            ('\u{05d5}', 6), ('\u{05d6}', 7), ('\u{05d7}', 8), ('\u{05d8}', 9), ('\u{05d9}', 10),
            ('\u{05db}', 20), ('\u{05dc}', 30), ('\u{05de}', 40), ('\u{05e0}', 50), ('\u{05e1}', 60),
            ('\u{05e2}', 70), ('\u{05e4}', 80), ('\u{05e6}', 90), ('\u{05e7}', 100), ('\u{05e8}', 200),
            ('\u{05e9}', 300), ('\u{05ea}', 400),
        ].into_iter().collect();
        
        let greek_values: HashMap<char, u32> = [
            ('\u{03b1}', 1), ('\u{03b2}', 2), ('\u{03b3}', 3), ('\u{03b4}', 4), ('\u{03b5}', 5),
            ('\u{03b6}', 7), ('\u{03b7}', 8), ('\u{03b8}', 9), ('\u{03b9}', 10),
            ('\u{03ba}', 20), ('\u{03bb}', 30), ('\u{03bc}', 40), ('\u{03bd}', 50), ('\u{03be}', 60),
            ('\u{03bf}', 70), ('\u{03c0}', 80), ('\u{03c1}', 100), ('\u{03c3}', 200),
            ('\u{03c4}', 300), ('\u{03c5}', 400), ('\u{03c6}', 500), ('\u{03c7}', 600),
            ('\u{03c8}', 700), ('\u{03c9}', 800),
        ].into_iter().collect();
        
        word.chars()
            .filter_map(|c| hebrew_values.get(&c).or_else(|| greek_values.get(&c)))
            .sum()
    }
}

impl Default for TeachingMatrix {
    fn default() -> Self { Self::new() }
}
