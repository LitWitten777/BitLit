pub mod cartan;
pub mod functor;
pub mod metabolism;
pub mod organism;
pub mod plenum;
pub mod roots;
pub mod teachings;
pub mod torus;
pub mod weyl;
pub mod inference;

// Using pyo3 to export python bindings
use pyo3::prelude::*;
use pyo3::wrap_pyfunction;

#[pyfunction]
fn snap_to_e8(vec: Vec<f64>) -> PyResult<Vec<f64>> {
    if vec.len() != 8 {
        return Err(pyo3::exceptions::PyValueError::new_err("Vector must be 8-dimensional"));
    }
    let mut arr = [0.0; 8];
    arr.copy_from_slice(&vec);
    let yield_res = metabolism::snap_with_metabolism(&arr);
    Ok(yield_res.snapped.to_vec())
}

#[pyfunction]
fn sectional_curvature_approx(vec: Vec<f64>) -> PyResult<f64> {
    if vec.len() != 8 {
        return Err(pyo3::exceptions::PyValueError::new_err("Vector must be 8-dimensional"));
    }
    let mut arr = [0.0; 8];
    arr.copy_from_slice(&vec);
    let yield_res = metabolism::snap_with_metabolism(&arr);
    
    // curvature proxy = 1.0 - residual_norm
    let residual = yield_res.negentropy; 
    Ok(1.0 - residual)
}

#[pymodule]
fn sov_e8_organism(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<organism::E8Organism>()?;
    m.add_class::<metabolism::NegentropicYield>()?;
    m.add_class::<weyl::PyWeylVM>()?;
    m.add_class::<inference::PyGeometricTransformer>()?;
    m.add_function(wrap_pyfunction!(snap_to_e8, m)?)?;
    m.add_function(wrap_pyfunction!(sectional_curvature_approx, m)?)?;
    Ok(())
}
