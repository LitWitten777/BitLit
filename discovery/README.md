# Automated discovery loop

A closed loop that proposes conjectures, tries to break them, and keeps only what the Lean
kernel proves:

```
entropy pool ──► mutation engine ──► falsification arbiter ──► Lean stager ──► ledger
 (os.urandom,     (annealing chains     (fuzz, boundary,          (lake env lean,   (Lean module per
  ESP32 stream,    over conjecture       exhaustive, vacuity,      #print axioms)    run + JSONL index,
  health tests,    genomes)              counter-hypothesis,                         re-checked by
  HMAC-DRBG)                             generalization,                             lake build)
                                         null model, irreducibility)
```

Python only proposes and filters.  Acceptance is decided by the Lean kernel, and only claims
that compile with no `sorry` and only standard axioms are kept.  An error in the Python code can
therefore cost search time or let a claim through the screens, but it cannot put a false
theorem into the ledger.

## Quick start

```bash
lake build Discovery.Kernel                     # import-free vocabulary of staged claims
python3 -m discovery.engine entropy             # health-test the entropy sources
python3 -m discovery.engine run --dry-run       # explore + falsify, no Lean
python3 -m discovery.engine run --generations 600 --max-burn 40
python3 -m discovery.engine ledger              # list everything burned so far
lake build Discovery                            # re-check every burned claim + bridge + interpretation
python3 -m unittest tests.test_discovery_engine # 22 tests (1 needs DISCOVERY_LEAN=1: Lean staging)
```

Replay a run exactly: `python3 -m discovery.engine run --seed-hex <seed from the ledger>` (same
domains and options).

Use hardware entropy with
`--entropy-device /dev/ttyACM0 --device-h 1.0`, with the board running
`firmware/esp32s3_entropy_stream.ino`.  That sketch has not been tested on hardware.  A device
stream that fails the health tests is dropped and the run continues on `os.urandom`.

## Layout

| Path | Role |
|---|---|
| `engine/entropy.py` | sources; SP 800-90B repetition-count and adaptive-proportion tests; SHA-256 conditioning; HMAC-DRBG; replay |
| `engine/domains/base.py` | the domain interface (genomes, instances, ladder, screens, Lean rendering) |
| `engine/domains/cd_signs.py` | sign laws of the Cayley–Dickson basis at dimensions 2–32 (canonical form up to GF(2) change of variables) |
| `engine/domains/primes.py` | primes of a residue class represented by `a x² + b y²`; prime-producing quadratics `n² + bn + c` |
| `engine/arbiter.py` | the adversarial falsification protocol (9 stages, see its docstring) |
| `engine/loop.py` | annealing chains, novelty, restarts, promotion, journal |
| `engine/stager.py` | Lean rendering, `lake env lean`, axiom check, burning, ledger rebuild + axiom audit |
| `Discovery/Kernel.lean` | `cdSign`, `isPrimeB` (import-free, so a staged claim takes ~2 s) |
| `Discovery/Bridge.lean` | `cdSign_eq`, `cdMul_basis`: the sign is that of the real Cayley–Dickson product; `isPrimeB_iff`: it is `Nat.Prime` |
| `Discovery/Ledger/*.lean` | burned claims, one module per run |
| `Discovery/Interpret.lean` | some burned claims restated as theorems about primes and the 32-dim CD algebra |
| `ledger/burned.jsonl` | index of burned claims (statement, run, seed, arbiter counts, kernel time) |
| `ledger/journal/*.jsonl` | complete event log per run (every verdict, every staging, every defect) |
| `firmware/esp32s3_entropy_stream.ino` | ESP32-S3 raw ADC / hardware-RNG byte stream (untested) |

## Adding a domain

Subclass `engine.domains.base.Domain`.  Every claim must be a closed, bounded proposition over
`Discovery.Kernel` (add a definition there if needed and a meaning theorem to
`Discovery/Bridge.lean`), decidable by `decide +kernel`.  The `ladder` must be monotone (if one
rung is false, all later rungs are false).  Register the domain in `engine/domains/__init__.py`.
