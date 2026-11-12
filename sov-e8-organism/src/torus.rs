//! UTF-4 Torus Navigation

use crate::plenum::Plenum75D;
use std::f64::consts::PI;

#[derive(Debug, Clone)]
pub struct TorusPoint {
    pub angles: [f64; 75],
    pub radii: TorusRadii,
}

#[derive(Debug, Clone, Copy)]
pub struct TorusRadii {
    pub life: f64,
    pub knowledge: f64,
    pub wisdom: f64,
    pub moments: f64,
    pub witnesses: f64,
    pub hash: f64,
}

impl Default for TorusRadii {
    fn default() -> Self {
        TorusRadii { life: 1.0, knowledge: 0.8, wisdom: 0.6, moments: 0.4, witnesses: 0.3, hash: 0.2 }
    }
}

impl TorusPoint {
    pub fn from_plenum(plenum: &Plenum75D) -> Self {
        let mut angles = [0.0; 75];
        for i in 0..75 {
            angles[i] = (plenum.coords[i] + 1.0) * PI;
        }
        TorusPoint { angles, radii: TorusRadii::default() }
    }
    
    pub fn to_plenum(&self) -> Plenum75D {
        let mut coords = [0.0; 75];
        for i in 0..75 {
            coords[i] = (self.angles[i] / PI) - 1.0;
        }
        Plenum75D::from_features(&coords)
    }
    
    pub fn geodesic_distance(&self, other: &TorusPoint) -> f64 {
        let mut dist_sq = 0.0;
        for i in 0..75 {
            let diff = self.angles[i] - other.angles[i];
            let wrapped = if diff > PI { diff - 2.0 * PI } 
                         else if diff < -PI { diff + 2.0 * PI } 
                         else { diff };
            let radius = self.radius_for_dimension(i);
            dist_sq += (wrapped * radius).powi(2);
        }
        dist_sq.sqrt()
    }
    
    fn radius_for_dimension(&self, dim: usize) -> f64 {
        match dim {
            0..=7 => self.radii.life,
            8..=15 => self.radii.knowledge,
            16..=23 => self.radii.wisdom,
            24..=35 => self.radii.moments,
            36..=41 => self.radii.witnesses,
            _ => self.radii.hash,
        }
    }
    
    pub fn rotate(&self, axis: TorusAxis, angle: f64) -> TorusPoint {
        let mut new_angles = self.angles;
        match axis {
            TorusAxis::Poloidal(layer) => {
                let (start, end) = layer.dimension_range();
                for i in start..end {
                    new_angles[i] = (new_angles[i] + angle) % (2.0 * PI);
                }
            },
            TorusAxis::Toroidal => {
                for i in 0..75 {
                    let layer_offset = (i / 8) as f64 * 0.1;
                    new_angles[i] = (new_angles[i] + angle * (1.0 + layer_offset)) % (2.0 * PI);
                }
            },
        }
        TorusPoint { angles: new_angles, radii: self.radii }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TorusAxis {
    Poloidal(TorusLayer),
    Toroidal,
}

#[derive(Debug, Clone, Copy)]
pub enum TorusLayer {
    Life, Knowledge, Wisdom, Moments, Witnesses, Hash,
}

impl TorusLayer {
    pub fn dimension_range(&self) -> (usize, usize) {
        match self {
            TorusLayer::Life => (0, 8),
            TorusLayer::Knowledge => (8, 16),
            TorusLayer::Wisdom => (16, 24),
            TorusLayer::Moments => (24, 36),
            TorusLayer::Witnesses => (36, 42),
            TorusLayer::Hash => (42, 75),
        }
    }
}

#[derive(Debug, Clone)]
pub struct MerkabaProjector {
    projection: [[f64; 75]; 3],
}

impl MerkabaProjector {
    pub fn new() -> Self {
        let mut projection = [[0.0; 75]; 3];
        for i in 0..4 {
            projection[0][i] = if i % 2 == 0 { 1.0 } else { -1.0 };
        }
        for i in 4..8 {
            projection[1][i] = if i % 2 == 0 { 1.0 } else { -1.0 };
        }
        for i in 0..8 {
            projection[2][i] = 0.5;
            projection[2][i + 16] = -0.5;
        }
        MerkabaProjector { projection }
    }
    
    pub fn project(&self, point: &TorusPoint) -> [f64; 3] {
        let plenum = point.to_plenum();
        let mut result = [0.0; 3];
        for axis in 0..3 {
            for i in 0..75 {
                result[axis] += self.projection[axis][i] * plenum.coords[i];
            }
        }
        result
    }
}

impl Default for MerkabaProjector {
    fn default() -> Self { Self::new() }
}

pub struct Utf4Encoder;

impl Utf4Encoder {
    pub fn encode(plenum: &Plenum75D) -> [u8; 4] {
        let mut bytes = [0u8; 4];
        let life_sig: f64 = plenum.coords[0..8].iter().sum();
        bytes[0] = ((life_sig + 4.0) * 32.0).clamp(0.0, 255.0) as u8;
        let knowledge_sig: f64 = plenum.coords[8..16].iter().sum();
        bytes[1] = ((knowledge_sig + 4.0) * 32.0).clamp(0.0, 255.0) as u8;
        let wisdom_sig: f64 = plenum.coords[16..24].iter().sum();
        bytes[2] = ((wisdom_sig + 4.0) * 32.0).clamp(0.0, 255.0) as u8;
        let witness_sig: f64 = plenum.witnesses.iter().sum();
        bytes[3] = ((witness_sig + 1.5) * 85.0).clamp(0.0, 255.0) as u8;
        bytes
    }
    
    pub fn decode(bytes: &[u8; 4]) -> Plenum75D {
        let mut features = vec![0.0; 24];
        let life_sig = (bytes[0] as f64 / 32.0) - 4.0;
        let knowledge_sig = (bytes[1] as f64 / 32.0) - 4.0;
        let wisdom_sig = (bytes[2] as f64 / 32.0) - 4.0;
        for i in 0..8 {
            features[i] = life_sig / 8.0;
            features[i + 8] = knowledge_sig / 8.0;
            features[i + 16] = wisdom_sig / 8.0;
        }
        Plenum75D::from_features(&features)
    }
}
