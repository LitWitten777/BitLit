# Research Protocols and Standards

## Established: Comprehensive Research Framework

This document summarizes the rigorous research, coding, organization, and management protocols established for the Sovereign research project.

---

## 1. Standardized Naming Conventions

All research artifacts follow strict naming conventions enforced by `NamingProtocol`:

| Pattern | Format | Example | Description |
|---------|--------|---------|-------------|
| Hypothesis ID | `HYP-XXX` | `HYP-046`, `HYP-047` | Three-digit hypothesis identifier |
| Workstream ID | `WXX` | `W1`, `W2`, `W5` | Numeric workstream identifier |
| Python code | `snake_case` | `compute_moment`, `verify_doubling_law` | Functions and variables |
| Python classes | `PascalCase` | `ResearchLogger`, `VerificationResult` | Classes and types |
| Constants | `UPPER_CASE` | `MAX_DIMENSION`, `TOLERANCE` | Module-level constants |
| Documentation | `kebab-case` | `research-protocols.md` | File names |

**Validation:**
```python
from sedenion import NamingProtocol

NamingProtocol.validate_hypothesis_id("HYP-001")  # True
NamingProtocol.validate_workstream_id("W1")       # True
```

---

## 2. Logging Infrastructure

Every research operation is logged with adversarial metadata using `ResearchLogger`:

### Log Entry Structure
- **timestamp**: ISO 8601 UTC timestamp
- **hypothesis_id**: Associated HYP-XXX (if applicable)
- **workstream_id**: Associated WXX (if applicable)
- **operation**: Description of the operation
- **input_data**: Parameters and input values
- **output_data**: Results and outputs
- **verification_status**: `pending`, `verified`, `falsified`, or `error`
- **falsification_criteria**: List of conditions that would invalidate results
- **checksum**: SHA-256 hash for data integrity
- **notes**: Additional context and evidence

### Usage Example
```python
from sedenion import initialize_research_environment
from pathlib import Path

logger, verifier = initialize_research_environment(Path('logs/research'))

entry = logger.log_operation(
    operation="zero_divisor_count",
    input_data={"D": 16},
    output_data={"count": 72},
    hypothesis_id="HYP-001",
    workstream_id="W1",
    falsification_criteria=["count != (D-2)*(D-4)"]
)

# Mark as verified with evidence
logger.mark_verified(entry, "Matches universal formula")
```

---

## 3. Adversarial Testing Framework

Following Popperian falsification principle: scientific claims must be testable and potentially disprovable.

### FalsificationTest
```python
from sedenion import FalsificationTest

test = FalsificationTest(
    test_id="TEST-001",
    target_hypothesis="HYP-001",
    test_description="Verify zero-divisor count formula",
    failure_conditions=["result != (D-2)*(D-4)"],
    test_parameters={"D": 16},
    expected_outcome="72"
)

passed = test.run(compute_zero_divisors)
```

### Key Principles
1. **Explicit failure conditions**: Every test defines what would falsify the hypothesis
2. **Automated checking**: Tests run automatically and report pass/fail status
3. **Evidence tracking**: All results are logged with supporting evidence

---

## 4. Computational Verification Protocol

Every computation must specify:
- What would falsify the result
- Tolerance bounds for numerical comparisons
- Expected invariants that must hold

### VerificationResult Structure
```python
@dataclass
class VerificationResult:
    computation_id: str
    hypothesis_id: str
    workstream_id: Optional[str]
    computation_type: str
    input_parameters: Dict[str, Any]
    computed_value: Any
    expected_value: Optional[Any]
    tolerance: float
    passed: bool
    error_message: Optional[str]
    timestamp: str
```

### Usage Example
```python
result = verifier.verify_computation(
    computation_id="COMP-001",
    hypothesis_id="HYP-001",
    workstream_id="W1",
    computation_type="zero_divisor_count",
    compute_func=count_zero_divisors,
    input_parameters={"D": 16},
    expected_value=72,
    invariants=["value > 0", "value % 8 == 0"]
)

print(f"Passed: {result.passed}")
```

---

## 5. Git-Ignored Workspace

The `.local/` directory (and related patterns) are git-ignored for experimental work:

### Ignored Directories
- `.local/` - Primary sandbox for random/experimental work
- `tmp/`, `temp/`, `scratch/` - Temporary files
- `sandbox/` - Experimental code
- `dev_notes/`, `drafts/` - Working documents
- `__pycache__/`, `*.pyc` - Python artifacts
- `*.log` - Log files (except `logs/research/`)
- `.venv/`, `venv/` - Virtual environments

### Tracked Directories
- `logs/research/` - Research logs (JSON format)
- `src/sedenion/` - Source code
- `tests/` - Test suite
- `docs/` - Documentation
- `Sovereign/` - Lean 4 formal proofs

---

## 6. Double Verification Principle

Every mathematical claim requires:
1. **Exact computation**: Python implementation with logged results
2. **Formal proof**: Lean 4 theorem with 0 `sorry` and 0 external axioms

### Workflow
```
Computation (Python) → Evidence → Formal Proof (Lean 4) → Verified
      ↓                      ↓              ↓
   Run tests            Check against   Compile with
   Log results          conjecture      lake build
```

### Status Tracking
| Status | Meaning |
|--------|---------|
| `computed` | Python computation complete, no formal proof yet |
| `partial` | Some aspects proved, others pending |
| `proved` | Full Lean 4 proof complete |
| `verified` | Both computation and proof agree |

---

## 7. Workstream Organization

Each workstream follows a standard template:

### Template
```markdown
## WXX — [Title]

**Question.** [Mathematical question being investigated]

**Computation** (`wXX_*.py`). [Description of computational approach]

**Result of the run.** [Summary of findings]

**Formal target** — [Status]. [Lean file proving the result]

**Next.** [Open questions and future work]

**Falsification Criteria:**
- [Criterion 1]
- [Criterion 2]
```

### Current Workstreams
| ID | Title | Status | Formal Target |
|----|-------|--------|---------------|
| W1 | Higher moments of degree census | Partial | TowerDegreeMomentsHigher.lean |
| W2 | Charge-sector census | Proved | TowerSectorCensus.lean |
| W3 | Prefix-depth classes | Computed | (open) |
| W4 | Graph vertex/edge counts | Proved | CrossHalfVertexDegree.lean |
| W5 | Sector spectra | Computed | (open) |

---

## 8. Sprint Planning

Research organized into time-boxed sprints with clear deliverables:

### Sprint Structure
- **Duration**: 10-14 days
- **Hypotheses**: 1-2 primary hypotheses per sprint
- **Deliverables**: 
  - Python implementation
  - Computational verification
  - Lean 4 formal proof (when applicable)

### Upcoming Sprints
| Sprint | Dates | Hypothesis | Deliverables |
|--------|-------|------------|--------------|
| 46 | 2026-09-10 to 2026-09-20 | HYP-046 | QLDPC distance bounds |
| 47 | 2026-09-15 to 2026-09-27 | HYP-047 | Lattice surgery |
| 48 | 2026-09-20 to 2026-10-04 | HYP-048 | 3D spectral Galerkin DNS |
| 49 | 2026-09-25 to 2026-10-09 | HYP-049 | Coupled Hou-Chen enclosure |
| 50 | 2026-10-01 to 2026-10-11 | HYP-050 | AVX-512 / Vulkan kernel |

---

## 9. File Organization

```
/workspace/
├── .gitignore                    # Git ignore rules
├── .local/                       # Git-ignored sandbox
├── src/sedenion/                 # Python source
│   ├── __init__.py               # Core framework
│   └── research/                 # Workstream implementations
│       ├── w1_census_moments.py
│       ├── roadmap.py
│       └── ...
├── tests/research/               # Test suite
│   └── test_framework.py
├── logs/research/                # Research logs (tracked)
│   ├── w1.json
│   ├── w2.json
│   └── ...
├── docs/                         # Documentation
│   └── roadmap_complete.json
├── Sovereign/                    # Lean 4 formal proofs
│   ├── Combinatorics/
│   ├── Graph/
│   └── ...
└── RESEARCH_ROADMAP.md           # Master roadmap
```

---

## 10. Quick Start

```bash
# Initialize environment
cd /workspace

# Run all workstreams
python src/sedenion/research/run_all.py

# Run specific workstream
python src/sedenion/research/w1_census_moments.py

# Run tests
pytest tests/research/test_framework.py -v

# View roadmap summary
python src/sedenion/research/roadmap.py
```

---

## References

- `RESEARCH_ROADMAP.md` - Complete research trajectory
- `RESEARCH_COMPUTE_ROADMAP.md` - Computational workstream details
- `src/sedenion/__init__.py` - Framework implementation
- `tests/research/test_framework.py` - Test suite
