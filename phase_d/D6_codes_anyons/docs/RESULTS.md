# D6 — Results (numerical; reproducible with `python3 -m pytest phase_d/D6_codes_anyons/tests`)

Everything below is a numerical check by the tests named in brackets, not a
proof.

## 1. Surface codes on `Σ_g`

Integrated on 2026-10-04: this section moved to `foundation/ws4_toric/SURFACE_CODES.md`
(code `ws4_toric/surface_code.py`, tests `foundation/tests/test_fnd_surface_code.py`).

## 2. `SU(2)_k` anyons

Labels `0, ½, …, k/2`; truncated Clebsch–Gordan fusion; F-symbols from the
Racah–Wigner quantum 6j symbol at `q = e^{iπ/(k+2)}`,
`[F^{abc}_d]_{ef} = (−1)^{a+b+c+d} √([2e+1][2f+1]) {a b e; c d f}_q`;
`R^{ab}_c = (−1)^{c−a−b} q^{c(c+1)−a(a+1)−b(b+1)}`. Conventions are those of
`qbx_ir.anyon.AnyonModel` / `tests/qbx_ir/test_anyon_coherence.py`.

### Coherence [`test_pentagon_hexagons_unitarity`, `test_pentagon_on_random_label_tuples`]

Maximum residual over **all** label assignments:

| k | pentagon | hexagon | reversed hexagon | `F Fᵀ − 1` |
|---|---|---|---|---|
| 2 | 6.7e−16 | 5.2e−16 | 5.2e−16 | 8.9e−16 |
| 3 | 6.7e−16 | 4.4e−16 | 4.4e−16 | 6.7e−16 |
| 4 | 8.9e−16 | 8.0e−16 | 8.1e−16 | 8.9e−16 |
| 5 | 1.3e−15 | 1.1e−15 | 1.1e−15 | 1.2e−15 |

The same holds for the complex-conjugate data (`q → q⁻¹`) and for `k = 1, 6`.
All are far below the `1e−10` target.

### `SU(2)_2` against Ising [`test_su2_2_vs_ising`]

Same fusion rules (`0, ½, 1` ↔ `1, σ, ψ`), different braided categories:

| Invariant (gauge invariant) | `SU(2)_2` | Ising (`qbx_ir`) | Agree? |
|---|---|---|---|
| `θ` of `½` / `σ` | `e^{2πi·3/16}` | `e^{2πi/16}` | no |
| `θ` of `1` / `ψ` | `−1` | `−1` | yes |
| Frobenius–Schur indicator of `½` / `σ` (`d [F^{aaa}_a]_{00}`) | `−1` | `+1` | no |
| `F^{ψσψ}_σ`, `R^{ψψ}_1` (the `ψ` sector) | `−1`, `−1` | `−1`, `−1` | yes |

Since `θ` and the Frobenius–Schur indicator are gauge invariant, no gauge
relates the two sets of F/R data; a search over gauges with values `±1, ±i`
finds none, consistently.

### `SU(2)_3` integer-spin part against Fibonacci [`test_su2_3_integer_part_is_fibonacci`]

The labels `{0, 1}` of `SU(2)_3` are closed under fusion (`1 ⊗ 1 = 0 ⊕ 1`) and
form **Fibonacci, not its complex conjugate**: the R-symbols agree exactly
(`R^{11}_0 = e^{−4πi/5}`, `R^{11}_1 = e^{3πi/5}`, as in `fibonacci_model()`),
`θ_1 = e^{4πi/5} = θ_τ`, and the F-symbols agree in the gauge `u^{ττ}_τ = i`
(all other vertices `1`), which flips the sign of the off-diagonal entries of
`F^{τττ}_τ` (`SU(2)_3` gives `[[1/φ, −1/√φ], [−1/√φ, −1/φ]]`). The conjugate
data `q → q⁻¹` matches no gauge.
