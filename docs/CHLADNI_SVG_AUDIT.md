# Audit of `artifacts/chladni_nodal_d4.svg`

The artifact is a scatter plot of the near-nodal samples of the degenerate
Helmholtz mode

```
u(x, y) = cos (3x) cos (5y) - cos (5x) cos (3y)
```

on the square `[-π, π]²`, captioned *"Dihedral D4 Symmetry Invariant Manifold"*.
It is produced by `scripts/research/chladni_nodal.py`.  Before this pass, the
Lean side (`Sovereign/Taxonomy/ChladniNodalManifold.lean`) certified only one of
the eight symmetries the caption claims — the diagonal reflection `(x, y) ↦ (y, x)`.

## What is now proved

`Sovereign/Taxonomy/ChladniNodalD4.lean` (builds with no `sorry`; only
`propext`, `Classical.choice`, `Quot.sound`):

| statement | content |
| --- | --- |
| `chladni_d4_equivariant` | each of the eight elements of `D₄` multiplies the mode by a sign: `+1` for the identity, the half turn and the two axis reflections, `-1` for the two quarter turns and the two diagonal reflections |
| `chladni_nodal_d4_invariant` | hence the nodal set is invariant under all of `D₄`, for *all* real mode numbers `m, n` — the caption's claim about the mathematical object |
| `chladni_diagonal_subset`, `chladni_antidiagonal_subset` | the two diagonals `y = x`, `y = -x` lie in the nodal set |
| `cos_odd_multiple_half_pi`, `chladni_vertical_quarter_line`, `chladni_horizontal_quarter_line` | for **odd** integer mode numbers (such as `3, 5`) the four straight lines `x = ±π/2`, `y = ±π/2` lie in the nodal set — these are the straight crossing lines visible in the picture |
| `sample_swap_invariant` | the *plotted* sample is invariant under the coordinate swap for any grid and any tolerance |
| `gridPt_neg`, `sample_d4_invariant` | on the **closed** grid `i ≤ res` one has `gridPt res (res - i) = -gridPt res i`, so the plotted sample carries the whole `D₄` action |
| `pi_not_mem_halfOpen_grid`, `gridPt_zero` | the **half-open** grid `i < res` used by the original exporter samples the edge `x = -π` but never its mirror `x = π` |
| `chladni_svg_d4_settled` | master statement collecting the above |

## What the picture actually shows

The mathematical nodal set is `D₄`-invariant, but the *rendered point cloud* in
`artifacts/chladni_nodal_d4.svg` is not: the exporter sampled `x_i = -π + 2πi/res`
for `i < res`, a half-open grid.  Reading the 4464 plotted circles back out of
the file and applying the geometric symmetries gives

| symmetry | plotted points whose image is missing |
| --- | --- |
| diagonal swap `(x, y) ↦ (y, x)` | 0 |
| `x ↦ -x` | 20 |
| `y ↦ -y` | 20 |
| quarter turn | 20 |

which is exactly the behaviour the two Lean facts predict: the half-open grid is
a product grid, hence closed under the swap, but not closed under negation, so
the left/top edge samples have no mirror partner.

## The correction

`scripts/research/chladni_nodal.py` now also provides `sample_grid`,
`nodal_sample_points`, `check_render_symmetry` and `export_nodal_svg_symmetric`,
which use the closed grid `i ≤ res`.  The new artifact
`artifacts/chladni_nodal_d4_symmetric.svg` has 4505 plotted points and **zero**
violations of all four symmetries checked, matching `sample_d4_invariant`.  The
original artifact and its exporter are left in place unchanged, and the script's
run reports the symmetry census of both grids.

Note that these point-cloud counts are numerical observations about the rendered
files, not machine-checked claims; the machine-checked content is the Lean module
above, in particular the fact that the half-open grid cannot support the mirror
symmetries while the closed grid does.
