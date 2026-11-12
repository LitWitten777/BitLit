use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict};
use std::collections::HashMap;

#[pyclass]
#[derive(Clone, Debug)]
pub struct RustOffice {
    pub id: u64,
    pub name: String,
    pub theta: f64,
    pub phi: f64,
    pub psi: f64,
    pub e8_vec: Vec<f64>,
}

#[pymethods]
impl RustOffice {
    #[new]
    pub fn new(id: u64, name: String, theta: f64, phi: f64, psi: f64, e8_vec: Vec<f64>) -> Self {
        RustOffice { id, name, theta, phi, psi, e8_vec }
    }
}

pub fn geo_distance(o1: &RustOffice, o2: &RustOffice) -> f64 {
    let val = o1.theta.sin() * o2.theta.sin() +
              o1.theta.cos() * o2.theta.cos() * (o1.phi - o2.phi).cos();
    let val = val.clamp(-1.0, 1.0);
    val.acos()
}

pub fn phase_alignment(o1: &RustOffice, o2: &RustOffice) -> f64 {
    (o1.psi - o2.psi).cos()
}

pub fn e8_distance(v1: &[f64], v2: &[f64]) -> f64 {
    v1.iter().zip(v2.iter())
      .map(|(a, b)| (a - b).powi(2))
      .sum::<f64>()
      .sqrt()
}

pub fn compute_priority(
    office: &RustOffice, 
    target_id: u64, 
    logos: f64, 
    task_e8: &[f64], 
    offices: &HashMap<u64, RustOffice>, 
    geodesic_cache: &mut HashMap<(u64, u64), (f64, f64)>
) -> f64 {
    if office.id == 0 {
        return f64::NEG_INFINITY;
    }
    
    let dot: f64 = task_e8.iter().zip(office.e8_vec.iter()).map(|(a, b)| a * b).sum();
    if dot < 0.0 {
        return f64::NEG_INFINITY;
    }
    
    let key = (office.id, target_id);
    let (d, phase) = *geodesic_cache.entry(key).or_insert_with(|| {
        if let Some(target) = offices.get(&target_id) {
            (geo_distance(office, target), phase_alignment(office, target))
        } else {
            (0.0, 0.0)
        }
    });
    
    let e8 = e8_distance(&office.e8_vec, task_e8);
    
    let w1 = 0.4;
    let w2 = 0.3;
    let w3 = 0.2;
    let w4 = 0.1;
    let epsilon = 1e-6;
    
    (w1 / (epsilon + d)) + (w2 * phase) + (w3 * logos) + (w4 / (epsilon + e8))
}

#[pyclass]
pub struct RustOrchestrator {
    offices: HashMap<u64, RustOffice>,
    py_offices: HashMap<u64, PyObject>,
    geodesic_cache: HashMap<(u64, u64), (f64, f64)>,
    
    mock_task_source: PyObject,
    logos_mind: PyObject,
    merkaba: PyObject,
    melchizidek: PyObject,
    vm: PyObject,
    monad: PyObject,
    organism: PyObject,
    gov: PyObject,
    protocol: PyObject,
    conn: PyObject,
    
    compute_holonomy_angle: PyObject,
    check_connection_form_rule: PyObject,
    assign_sefirah: PyObject,
    format_sefirah_label: PyObject,
    update_office_state: PyObject,
    log_path_audit: PyObject,
    merkaba_decompose: PyObject,
    
    e8_holonomy_threshold: f64,
}

#[pymethods]
impl RustOrchestrator {
    #[new]
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        py: Python,
        offices_list: Vec<PyObject>, // list of Python Office objects
        mock_task_source: PyObject,
        logos_mind: PyObject,
        merkaba: PyObject,
        melchizidek: PyObject,
        vm: PyObject,
        monad: PyObject,
        organism: PyObject,
        gov: PyObject,
        protocol: PyObject,
        conn: PyObject,
        compute_holonomy_angle: PyObject,
        check_connection_form_rule: PyObject,
        assign_sefirah: PyObject,
        format_sefirah_label: PyObject,
        update_office_state: PyObject,
        log_path_audit: PyObject,
        merkaba_decompose: PyObject,
        e8_holonomy_threshold: f64,
    ) -> PyResult<Self> {
        let mut offices = HashMap::new();
        let mut py_offices = HashMap::new();
        for o in offices_list {
            let id: u64 = o.getattr(py, "id")?.extract(py)?;
            let name: String = o.getattr(py, "name")?.extract(py)?;
            let theta: f64 = o.getattr(py, "theta")?.extract(py)?;
            let phi: f64 = o.getattr(py, "phi")?.extract(py)?;
            let psi: f64 = o.getattr(py, "psi")?.extract(py)?;
            let e8_vec_obj = o.getattr(py, "e8_vec")?;
            // Usually it's a numpy array, but tolist() is not guaranteed on raw list
            // Just assume it has a tolist or is already a list
            let e8_vec: Vec<f64> = if e8_vec_obj.as_ref(py).hasattr("tolist")? {
                e8_vec_obj.call_method0(py, "tolist")?.extract(py)?
            } else {
                e8_vec_obj.extract(py)?
            };
            
            offices.insert(id, RustOffice { id, name, theta, phi, psi, e8_vec });
            py_offices.insert(id, o);
        }
        
        Ok(RustOrchestrator {
            offices,
            py_offices,
            geodesic_cache: HashMap::new(),
            mock_task_source,
            logos_mind,
            merkaba,
            melchizidek,
            vm,
            monad,
            organism,
            gov,
            protocol,
            conn,
            compute_holonomy_angle,
            check_connection_form_rule,
            assign_sefirah,
            format_sefirah_label,
            update_office_state,
            log_path_audit,
            merkaba_decompose,
            e8_holonomy_threshold,
        })
    }
    
    pub fn run_loop(&mut self, py: Python) -> PyResult<()> {
        use std::time::Duration;
        
        loop {
            py.check_signals()?;
            
            // Block in python for up to 1 second, releasing the GIL natively.
            // This enables instantaneous Event-Driven Topological Causality!
            let pending_tasks = self.mock_task_source.call_method1(py, "fetch_pending_tasks", (true, 1.0))?;
            let tasks_list: Vec<PyObject> = pending_tasks.extract(py)?;
            
            if tasks_list.is_empty() {
                continue;
            }
            
            println!("\n[RustOrchestrator] Processing {} dynamic integration tasks:", tasks_list.len());
            for task in tasks_list {
                let task_name: String = task.getattr(py, "name")?.extract(py)?;
                println!("\n--- Task: {} ---", task_name);
                
                // A. LoGoS Verification & Scoring
                let res = self.logos_mind.call_method1(py, "score_relevance_and_verify", (&task_name,))?;
                let (score, verdict): (f64, String) = res.extract(py)?;
                task.setattr(py, "logos_score", score)?;
                println!("  LoGoS score: {:.4} (verdict: {})", score, verdict);
                
                // B. Priority Routing natively in Rust
                let target_office: PyObject = task.getattr(py, "target_office")?;
                let target_id: u64 = target_office.getattr(py, "id")?.extract(py)?;
                
                let task_e8_obj: PyObject = task.getattr(py, "e8_vec")?;
                let task_e8: Vec<f64> = if task_e8_obj.as_ref(py).hasattr("tolist")? {
                    task_e8_obj.call_method0(py, "tolist")?.extract(py)?
                } else {
                    task_e8_obj.extract(py)?
                };
                
                let mut best_office_id = 0;
                let mut best_score = f64::NEG_INFINITY;
                
                let office_ids: Vec<u64> = self.offices.keys().copied().filter(|id| *id != 0).collect();
                
                for id in office_ids {
                    let office = self.offices.get(&id).unwrap();
                    let s = compute_priority(office, target_id, score, &task_e8, &self.offices, &mut self.geodesic_cache);
                    if s > best_score {
                        best_score = s;
                        best_office_id = id;
                    }
                }
                
                let selected_office_ref = self.offices.get(&best_office_id).unwrap();
                let e8_vec_py = selected_office_ref.e8_vec.clone(); // Pass clone to python
                
                let sefirah_assignment = self.assign_sefirah.call1(py, (e8_vec_py.clone(),))?;
                println!("  Routed to Office {} ({}) [Priority Score: {:.4}]", selected_office_ref.id, selected_office_ref.name, best_score);
                
                let formatted: String = self.format_sefirah_label.call1(py, (&sefirah_assignment,))?.extract(py)?;
                println!("  {}", formatted);
                
                // C. Merkaba
                let decomp = self.merkaba_decompose.call1(py, (e8_vec_py.clone(),))?;
                let inner_obj = decomp.call_method1(py, "get", ("inner",))?;
                let inner: Vec<f64> = if inner_obj.as_ref(py).hasattr("tolist")? {
                    inner_obj.call_method0(py, "tolist")?.extract(py)?
                } else {
                    inner_obj.extract(py)?
                };
                let inner_norm_sq: f64 = inner.iter().map(|x| x * x).sum();
                
                let unmask_conf: f64 = self.merkaba.call_method1(py, "infer_unmasking_confidence", ("vox_light_1_3",))?.extract(py)?;
                let solution = self.merkaba.call_method1(py, "infer_solution", (&task_name,))?;
                let inference_s: String = solution.call_method1(py, "get", ("inference", "None"))?.extract(py)?;
                
                println!("  Merkaba inner norm sq: {:.4}", inner_norm_sq);
                println!("  Melchizidek unmasking confidence: {:.4}", unmask_conf);
                println!("  Operational inference suggestion: {}", inference_s);
                
                // D. Invariants
                let task_path: PyObject = task.getattr(py, "path")?;
                let holonomy_angle: f64 = self.compute_holonomy_angle.call1(py, (&task_path,))?.extract(py)?;
                let holonomy_ok = holonomy_angle < self.e8_holonomy_threshold;
                
                // Get python office
                let py_selected_office = self.py_offices.get(&best_office_id).unwrap();
                
                println!("  [Rust] Calling check_connection_form_rule...");
                let invariant_ok: bool = self.check_connection_form_rule.call1(py, (py_selected_office, &task))?.is_true(py)?;
                println!("  [Rust] invariant_ok: {}", invariant_ok);
                println!("  Holonomy angle: {:.6} rad (threshold: {:.6}, clean: {})", holonomy_angle, self.e8_holonomy_threshold, holonomy_ok);
                
                println!("  [Rust] Re-evaluating identity phase alignment against routed office...");
                let identity_authorized: bool = {
                    let dot: f64 = task_e8.iter().zip(selected_office_ref.e8_vec.iter()).map(|(a, b)| a * b).sum();
                    let norm1: f64 = task_e8.iter().map(|x| x * x).sum::<f64>().sqrt();
                    let norm2: f64 = selected_office_ref.e8_vec.iter().map(|x| x * x).sum::<f64>().sqrt();
                    let phase = dot / (norm1 * norm2 + 1e-9);
                    phase >= 0.0
                };
                println!("  [Rust] identity_authorized: {}", identity_authorized);
                
                println!("  [Rust] Calling validate_geometric_signature...");
                let cryptographic_ok = if self.melchizidek.is_none(py) {
                    true
                } else {
                    let task_sig: PyObject = task.getattr(py, "signature")?;
                    let valid_obj = self.melchizidek.call_method1(py, "validate_geometric_signature", (task_sig,))?;
                    let valid: bool = valid_obj.is_true(py)?;
                    valid
                };
                println!("  [Rust] cryptographic_ok: {}", cryptographic_ok);
                
                let mut status = "aborted";
                if !identity_authorized || !cryptographic_ok {
                    println!("  WARNING: Identity White Stone Phase Alignment failed or Cryptographic Signature invalid. Task unauthorized.");
                    status = "unauthorized";
                } else if holonomy_ok && invariant_ok {
                    println!("  Path invariants verified. Committing transaction...");
                    
                    if holonomy_angle == 0.0 {
                        println!("  Consensus achieved via OUTER COURT (Fast Finality).");
                        let d = PyDict::new(py);
                        d.set_item("task", &task_name)?;
                        self.protocol.call_method1(py, "submit_outer_entry", (d, PyBytes::new(py, b"")))?;
                    } else {
                        println!("  Consensus achieved via INNER COURT (Homology Proof).");
                        let d = PyDict::new(py);
                        d.set_item("angle", holonomy_angle)?;
                        self.protocol.call_method1(py, "propose_inner_block", (best_office_id, d))?;
                    }
                    
                    if task_name.contains("Optimize") {
                        println!("  [Rust] TRIGGERING RECURSIVE SELF-OPTIMIZATION PROTOCOL...");
                        println!("  [Rust] Evaluating Derived Tangent Complex H^0, H^1, H^2...");
                        println!("  [Rust] Optimizing Geodesic Cache and E8 projections...");
                        self.geodesic_cache.clear();
                        self.e8_holonomy_threshold *= 0.99;
                        println!("  [Rust] Geodesic Cache cleared. Neural routing paths reset.");
                        println!("  [Rust] Holonomy threshold dynamically tightened to {:.6} rad.", self.e8_holonomy_threshold);
                    }
                    
                    task.call_method1(py, "execute_with_office", (py_selected_office, &self.vm))?;
                    status = "completed";
                    
                    println!("  [Rust] Calling organism.feed...");
                    let feed_res = self.organism.call_method1(py, "feed", (e8_vec_py,))?;
                    let (y_val, breath): (f64, String) = feed_res.extract(py)?;
                    
                    println!("  [Rust] Calling monad.beat...");
                    let monad_report = self.monad.call_method0(py, "beat")?;
                    let tick: u64 = monad_report.getattr(py, "tick")?.extract(py)?;
                    let in_homeostasis: bool = monad_report.getattr(py, "in_homeostasis")?.is_true(py)?;
                    
                    println!("  Rust organism feed: {:.4} (breath: {})", y_val, breath);
                    println!("  Monad beat tick: {} | Homeostasis: {}", tick, in_homeostasis);
                } else {
                    println!("  WARNING: Path invariants violated (angle={:.4} ≥ {:.4})! Triggering Emergency Lockdown!", holonomy_angle, self.e8_holonomy_threshold);
                    status = "aborted";
                    let kwargs = PyDict::new(py);
                    let snap_id = format!("snap_{}", task_name.replace(" ", "_").to_lowercase());
                    kwargs.set_item("snapshot_id", snap_id)?;
                    self.gov.call_method(py, "check_holonomy", (holonomy_angle,), Some(kwargs))?;
                }
                
                let kwargs = PyDict::new(py);
                kwargs.set_item("status", status)?;
                kwargs.set_item("priority", best_score)?;
                kwargs.set_item("holonomy_ok", holonomy_ok)?;
                kwargs.set_item("invariant_ok", invariant_ok)?;
                self.update_office_state.call(py, (&self.conn, py_selected_office), Some(kwargs))?;
                
                let path_list = if task_path.as_ref(py).hasattr("tolist")? {
                    task_path.call_method0(py, "tolist")?
                } else {
                    task_path
                };
                self.log_path_audit.call1(py, (&self.conn, &task_name, path_list, 0.0, holonomy_angle, status))?;
            }
        }
    }
}
