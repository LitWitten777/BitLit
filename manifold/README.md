# `manifold/` — the runnable hypercube manifold

A tick engine that pushes any byte stream through the 64-cell hypercube `Q6`. It splits the
stream into spectra, shapes them, joins them back, and repairs itself along the way. Every
mechanism it relies on is mirrored by a Lean theorem in `RequestProject/Manifold/`. The self-test
compares the Python against the values proved there.

Python 3 standard library only. Run from the repository root:

```
python3 -m manifold selftest                 # 26 checks against the Lean results
python3 -m manifold demo                     # start, speed 6, speed 2 (auto-brake), stop
python3 -m manifold run --speed 6 --ticks 60 [--source S] [--bands B] [--attack R]
python3 -m manifold repl                     # live: start | stop | speed N | chip B.. | unchip B.. |
                                             #       blow B G | spectrum | status | quit
python3 -m manifold spectrum --bands hopf    # band energies of one block
python3 -m manifold zd                       # sedenion zero-divisor census
python3 -m manifold tower                    # which laws survive at each Cayley-Dickson level
python3 -m manifold gematria                 # Torah gematria lab -> artifacts/manifold/gematria_lab.txt
```

Sources `S`: `synthetic` (default; has a clean reference, so SNR is measured), `synthetic-repeat`,
`text:<string>`, `file:<path>`, `torah` (letter values of the Hebrew Torah as a signal).
Bands `B`: `shells` (Hamming weight 0–6: 1, 6, 15, 20, 15, 6, 1 frequencies), `hopf` (the nine
`GF(8)` Hopf fibres plus the zero frequency), `octaves` (dyadic sequency bands).

## Controls

`start` sets running, `stop` clears it, and `speed N` sets the target. Each tick moves the speed
toward `min(target, vmax)`, or toward 0 when stopped, by at most `accel` up or `brake` down. It
never moves past that goal. Speed = blocks of 64 samples processed per tick. Lowering the speed
brakes automatically; `stop` brakes to 0.
Proved (`Control.lean`): no overshoot, no jolts, never above `vmax`, reaches the goal within
`ceil(gap / min(accel, brake))` ticks and stays there, `stop` halts.

## One block

| step | what happens | module | proved in |
|---|---|---|---|
| store | bytes → cells with the `[6,3,3]` code (3 cells per byte) | `heal.py` | `Heal.lean` |
| attack | Adversarial Critic flips bits | `agents.py` | — |
| heal | nearest codeword: every single flip per cell repaired, double flips detected | `heal.py` | `heal_single_error`, `double_error_detected`, `scrub_restores` |
| split | Walsh–Hadamard spectrum by the doubling butterfly, band energies | `spectrum.py` | `wht_wht`, `wht_eq_sum`, `wht_parseval`, `sum_shells`, `energy_band_add_compl` |
| shape | denoise (threshold tuned online), chip away / blow up bands | `spectrum.py` | `gain_gain`, `band_idem`, `energy_gain_le`, `le_energy_gain` |
| double | resonant consecutive blocks are joined as `(a, b)`; spectrum `(A+B, A−B)`; the `A−B` half is dropped when it carries < 1 % of the energy | `runtime.py` | `wht_double`, `wht_parseval` |
| join | back to bytes; Pipeline Auditor checks invariants; self-heal on violation | `runtime.py` | — |

The control state (running flag, target) is kept in three replicas. A corrupted replica is
repaired by bitwise majority (`maj_heals`).

## Personas (the project's AI variations, as deterministic policies)

| persona | from | job |
|---|---|---|
| Harmonic Analyst | `refinery/personas/harmonic_analyst.md` | reports dominant bands and block-to-block resonance |
| Adversarial Critic | `refinery/personas/adversarial_critic.md` | injects bit flips and replica corruption |
| Pipeline Auditor | `refinery/personas/pipeline_auditor.md` | checks lossless split/join, energy partition, speed limit, replica agreement; triggers healing |
| Structural Engineer | `refinery/personas/structural_engineer.md` | self-improvement: paired-probe tuning of the denoise threshold |
| Cross-Domain Architect | `refinery/personas/cross_domain_architect.md` | turns CD doubling on when blocks resonate |

Example (synthetic source, speed 6): input SNR ≈ 12 dB. The Engineer moves the threshold
multiplier from 1.0 to about 0.4, and output SNR rises from about 12.7 dB to 15–16 dB. These
are measured numbers and are not proved.

Full write-up: `docs/MANIFOLD_RUNTIME_2026-10-24.md`.
