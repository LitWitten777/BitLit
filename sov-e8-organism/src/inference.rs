use ndarray::{Array1, Array2, Axis};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};
use numpy::{PyReadonlyArray2, ToPyArray, PyArray1, PyReadonlyArray1};
use std::collections::HashMap;

/// Weyl reflection across a hyperplane perpendicular to `root`,
/// applied to a sequence of vectors `v` of shape (seq_len, 8).
pub fn seq_weyl_reflect(v: &Array2<f64>, root: &Array1<f64>) -> Array2<f64> {
    let dot_aa = root.dot(root);
    if dot_aa < 1e-12 {
        return v.clone();
    }
    
    let dot_va = v.dot(root);
    let mut result = v.clone();
    
    let factor = dot_va / dot_aa * 2.0;
    
    for i in 0..v.nrows() {
        for j in 0..8 {
            result[[i, j]] -= factor[i] * root[j];
        }
    }
    result
}

/// Applies a sequence of Weyl reflections defined by `invariant_path`
pub fn apply_geometric_layer(x: &Array2<f64>, invariant_path: &Array2<f64>) -> Array2<f64> {
    let mut out = x.clone();
    for i in 0..invariant_path.nrows() {
        let root = invariant_path.row(i).to_owned();
        out = seq_weyl_reflect(&out, &root);
    }
    out
}

/// Computes geometric causal attention: softmax(Q K^T / sqrt(8)) V
pub fn geometric_attention(q: &Array2<f64>, k: &Array2<f64>, v: &Array2<f64>) -> Array2<f64> {
    let seq_len = q.nrows();
    let mut scores = Array2::<f64>::zeros((seq_len, seq_len));
    
    // Pseudo-Riemannian Inner Product (Minkowski Signature -1, 1, 1, 1, 1, 1, 1, 1)
    for i in 0..seq_len {
        for j in 0..seq_len {
            if i < j {
                // Strict forward-time causality
                scores[[i, j]] = -1e9;
            } else {
                let mut dot = 0.0;
                dot += -q[[i, 0]] * k[[j, 0]]; // Time-like coordinate
                for dim in 1..8 {
                    dot += q[[i, dim]] * k[[j, dim]]; // Space-like coordinates
                }
                
                // Topological Light Cone penalty: if ds^2 is highly space-like, dampen it
                if dot > 0.0 {
                    scores[[i, j]] = (dot / (8.0f64).sqrt()) - (dot * 0.1); 
                } else {
                    scores[[i, j]] = dot / (8.0f64).sqrt();
                }
            }
        }
    }
    
    // Softmax
    for i in 0..seq_len {
        let mut max_val = f64::NEG_INFINITY;
        for j in 0..seq_len {
            if scores[[i, j]] > max_val {
                max_val = scores[[i, j]];
            }
        }
        
        let mut sum = 0.0;
        for j in 0..seq_len {
            let exp_val = (scores[[i, j]] - max_val).exp();
            scores[[i, j]] = exp_val;
            sum += exp_val;
        }
        
        for j in 0..seq_len {
            scores[[i, j]] /= sum;
        }
    }
    
    scores.dot(v)
}

#[pyclass]
pub struct PyGeometricTransformer {
    weights: HashMap<String, Array2<f64>>,
}

#[pymethods]
impl PyGeometricTransformer {
    #[new]
    pub fn new(weights_dict: &PyDict) -> PyResult<Self> {
        let mut weights = HashMap::new();
        
        for (k, v) in weights_dict.iter() {
            let key_str = k.extract::<String>()?;
            let val_arr = v.extract::<PyReadonlyArray2<f64>>()?;
            let arr2 = val_arr.as_array().to_owned();
            weights.insert(key_str, arr2);
        }
        
        Ok(PyGeometricTransformer { weights })
    }

    /// Process a sequence of tokens into next-token probabilities
    /// sequence: (seq_len,)
    /// returns logits: (vocab_size,)
    pub fn forward<'py>(&self, py: Python<'py>, sequence: Vec<usize>) -> PyResult<(&'py PyArray1<f64>, &'py PyArray1<f64>)> {
        let embeddings = self.weights.get("roberta.embeddings.word_embeddings.weight").unwrap();
        let pos_embeddings = self.weights.get("roberta.embeddings.position_embeddings.weight").unwrap();
        
        let seq_len = sequence.len();
        
        // 1. Embedding lookup
        let mut x = Array2::<f64>::zeros((seq_len, 8));
        for i in 0..seq_len {
            let tid = sequence[i];
            let emb = embeddings.row(tid);
            let pos_id = i + 2; // offset by 2 for RoBERTa
            let pos_emb = pos_embeddings.row(pos_id);
            for j in 0..8 {
                x[[i, j]] = emb[j] + pos_emb[j];
            }
        }
        
        // Count layers dynamically
        let num_layers = self.weights.keys().filter(|k| k.contains("roberta.encoder.layer.") && k.contains(".attention.self.query.weight")).count();
        
        // Process through layers
        for layer_i in 0..num_layers {
            let prefix = format!("roberta.encoder.layer.{}", layer_i);
            
            let q_path = self.weights.get(&format!("{}.attention.self.query.weight", prefix)).unwrap();
            let k_path = self.weights.get(&format!("{}.attention.self.key.weight", prefix)).unwrap();
            let v_path = self.weights.get(&format!("{}.attention.self.value.weight", prefix)).unwrap();
            
            let q = apply_geometric_layer(&x, q_path);
            let k = apply_geometric_layer(&x, k_path);
            let v = apply_geometric_layer(&x, v_path);
            
            let attn_out = geometric_attention(&q, &k, &v);
            
            // Skip connection
            x = x + attn_out;
            
            let attn_dense_path = self.weights.get(&format!("{}.attention.output.dense.weight", prefix)).unwrap();
            x = apply_geometric_layer(&x, attn_dense_path);
            
            let ff_inter_path = self.weights.get(&format!("{}.intermediate.dense.weight", prefix)).unwrap();
            x = apply_geometric_layer(&x, ff_inter_path);
            
            let ff_out_path = self.weights.get(&format!("{}.output.dense.weight", prefix)).unwrap();
            x = apply_geometric_layer(&x, ff_out_path);
        }
        
        // 4. Language Modeling Head on last token
        let mut x_last = Array2::<f64>::zeros((1, 8));
        for j in 0..8 {
            x_last[[0, j]] = x[[seq_len - 1, j]];
        }
        
        let lm_dense_path = self.weights.get("lm_head.dense.weight").unwrap();
        x_last = apply_geometric_layer(&x_last, lm_dense_path);
        
        let x_last_1d = x_last.row(0);
        
        // Score against vocabulary
        // embeddings is (vocab_size, 8)
        let scores = embeddings.dot(&x_last_1d); // (vocab_size,)
        
        Ok((scores.to_pyarray(py), x_last_1d.to_owned().to_pyarray(py)))
    }
}
