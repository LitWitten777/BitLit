module

public import Mathlib

@[expose] public section

/-!
# Cosmohedra and associahedra: tree-level face counts

Source: N. Arkani-Hamed, C. Figueiredo, F. Vazão, *Cosmohedra* (`Cosmohedra.tar.gz`, `main.tex`).

Polygon vertices are `0, 1, …, n-1` in cyclic order; a chord `(i, j)` with `i < j` is a pair of
non-adjacent vertices.

* **Associahedron `Assoc_n`** (dimension `n-3`): faces are sets of pairwise non-crossing chords
  (*partial triangulations*); vertices are complete triangulations, facets single chords.
* **Cosmohedron `Cosmo_n`** (dimension `n-3`): faces are "russian dolls", collections of nested
  sub-polygons in which every sub-polygon that contains another one is completely covered by
  the sub-polygons inside it.  Equivalently, a face is a recursive dissection: the full polygon
  is either left alone or cut by a non-empty set of non-crossing chords, and each piece is again
  either left alone or cut, and so on.  The codimension of a face is the number of polygons that
  are cut.  So facets are the non-empty partial triangulations, and vertices are the dolls in
  which every non-triangle is cut by exactly one chord.

This file

1. counts chords and partial triangulations explicitly (`diagonals`, `partialTriangulations`);
2. computes the face numbers of `Cosmo_n` from the recursive description (`cosmoFaces`);
3. checks the paper's claims against these computations and checks that the face numbers of
   both polytopes satisfy the Euler–Poincaré relation, a necessary condition for a face lattice
   of a polytope;
4. checks that the paper's recursion for the number of wavefunction terms `Ψ_n` gives the
   vertex count of `Cosmo_n`.
-/

namespace QBX.Notes.Cosmohedra

/-! ## 1. Chords and partial triangulations -/

/-- `(i, j)` is a chord (diagonal) of the convex `n`-gon with vertices `0, …, n-1`. -/
def IsDiagonal (n : ℕ) (d : ℕ × ℕ) : Prop :=
  d.1 + 2 ≤ d.2 ∧ d.2 < n ∧ ¬ (d.1 = 0 ∧ d.2 + 1 = n)

instance (n : ℕ) : DecidablePred (IsDiagonal n) := fun _ => by
  unfold IsDiagonal; infer_instance

/-- The chords of the convex `n`-gon. -/
def diagonals (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter (IsDiagonal n)

/-- Two chords cross in their interiors (their endpoints interleave). -/
def Crosses (d e : ℕ × ℕ) : Prop :=
  (d.1 < e.1 ∧ e.1 < d.2 ∧ d.2 < e.2) ∨ (e.1 < d.1 ∧ d.1 < e.2 ∧ e.2 < d.2)

instance : DecidableRel Crosses := fun _ _ => by unfold Crosses; infer_instance

/-- Partial triangulations of the `n`-gon: sets of pairwise non-crossing chords.  These label the
faces of `Assoc_n` (and, when non-empty, the facets of `Cosmo_n`). -/
def partialTriangulations (n : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (diagonals n).powerset.filter (fun s => ∀ d ∈ s, ∀ e ∈ s, ¬ Crosses d e)

/-- Number of partial triangulations of the `n`-gon with exactly `k` chords
(= number of faces of `Assoc_n` of codimension `k`). -/
def assocFaceCount (n k : ℕ) : ℕ :=
  ((partialTriangulations n).filter (fun s => s.card = k)).card


/-- Face numbers of `Assoc_n` listed by codimension `0, 1, …, n-3`. -/
def assocFaces (n : ℕ) : List ℕ := (List.range (n - 2)).map (assocFaceCount n)

/-- The `n`-gon has `n(n-3)/2` chords: the facet count of `Assoc_n` (checked for `3 ≤ n ≤ 12`). -/
theorem diagonals_card :
    ∀ n ∈ Finset.Icc 3 12, (diagonals n).card = n * (n - 3) / 2 := by
  decide +kernel

/-- Face numbers of the associahedra `Assoc_4, …, Assoc_7` (codimension `0, 1, 2, …`).  The last
entry is the number of vertices = complete triangulations. -/
theorem assocFaces_values :
    assocFaces 4 = [1, 2] ∧ assocFaces 5 = [1, 5, 5] ∧ assocFaces 6 = [1, 9, 21, 14] ∧
    assocFaces 7 = [1, 14, 56, 84, 42] := by
  decide +kernel

/-! ## 2. Face numbers of the cosmohedron from the recursive description -/

/-- Coefficient-list addition (polynomials in one variable `t`, lowest degree first). -/
def padd : List ℕ → List ℕ → List ℕ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: padd p q

/-- Coefficient-list multiplication. -/
def pmul : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: p, q => padd (q.map (a * ·)) (0 :: pmul p q)

/-- Drop trailing zero coefficients. -/
def trim (p : List ℕ) : List ℕ := (p.reverse.dropWhile (· == 0)).reverse

/-- Entry `k` of a table holds, for the `k`-gon, the pair `(F k, G k)` where
* `F k` = face polynomial of `Cosmo_k`: coefficient of `t^c` = number of russian dolls of the
  `k`-gon in which exactly `c` polygons are cut (= faces of codimension `c`);
* `G k` = sum over **all** dissections of the `k`-gon (including the trivial one) of the product
  of `F` over the pieces. -/
abbrev Table := List (List ℕ × List ℕ)

/-- Weight of a gap of `g` polygon edges between two consecutive vertices of the piece containing
the edge `(0, k-1)`: a single edge (`g = 1`) contributes `1`; otherwise the `(g+1)`-gon beyond the
gap is dissected arbitrarily (`G (g+1)`). -/
def gapWeight (T : Table) (g : ℕ) : List ℕ :=
  if g ≤ 1 then [1] else (T.getD (g + 1) ([], [])).2

/-- Sum over compositions of `j` into `r` positive gaps of the product of the gap weights. -/
def gapSum (T : Table) : ℕ → ℕ → List ℕ
  | j, 0 => if j = 0 then [1] else []
  | j, r + 1 => (List.range j).foldr
      (fun i acc => padd (pmul (gapWeight T (i + 1)) (gapSum T (j - (i + 1)) r)) acc) []

/-- Sum over **non-trivial** dissections of the `k`-gon of the product of `F` over the pieces,
organised by the piece containing the edge `(0, k-1)` (which has `m + 1` vertices, `2 ≤ m ≤ k-2`). -/
def cutSum (T : Table) (k : ℕ) : List ℕ :=
  ((List.range (k - 1)).filter (2 ≤ ·)).foldr
    (fun m acc => padd (pmul (T.getD (m + 1) ([], [])).1 (gapSum T (k - 1) m)) acc) []

/-- A `k`-gon is either left alone (`1`) or cut (`t ×` non-trivial dissections). -/
def nextEntry (T : Table) (k : ℕ) : List ℕ × List ℕ :=
  let c := trim (cutSum T k)
  let f := padd [1] (0 :: c)
  (trim f, trim (padd f c))

/-- The table for polygons with `0, 1, …, n` vertices (entries below `3` are placeholders). -/
def table : ℕ → Table
  | 0 => [([1], [1])]
  | k + 1 => table k ++ [nextEntry (table k) (k + 1)]

/-- Face numbers of `Cosmo_n` by codimension `0, 1, …, n-3`: entry `0` is the polytope itself,
entry `1` the facets, the last entry the vertices. -/
def cosmoFaces (n : ℕ) : List ℕ := ((table n).getD n ([], [])).1

/-- Face numbers of the cosmohedra `Cosmo_4, …, Cosmo_12`, by codimension.  `Cosmo_5` is a
decagon (10 edges, 10 vertices); `Cosmo_6` has 44 facets, 114 edges and 72 vertices. -/
theorem cosmoFaces_values :
    cosmoFaces 4 = [1, 2] ∧
    cosmoFaces 5 = [1, 10, 10] ∧
    cosmoFaces 6 = [1, 44, 114, 72] ∧
    cosmoFaces 7 = [1, 196, 952, 1400, 644] ∧
    cosmoFaces 8 = [1, 902, 7116, 18040, 18528, 6704] ∧
    cosmoFaces 9 = [1, 4278, 50550, 194616, 332664, 262728, 78408] ∧
    cosmoFaces 10 = [1, 20792, 349670, 1904800, 4795520, 6178920, 3967800, 1008480] ∧
    cosmoFaces 11 = [1, 103048, 2383172, 17558464, 60841924, 113395656, 117265632, 63499304,
      14065744] ∧
    cosmoFaces 12 = [1, 518858, 16106272, 155578056, 710633608, 1792650712, 2649477408,
      2289330592, 1072543008, 210682080] := by
  decide +kernel

/-! ## 3. The paper's claims, and the Euler–Poincaré relation -/

/-- Alternating sum `a₀ - a₁ + a₂ - …` of a list of face numbers. -/
def altSum : List ℕ → ℤ
  | [] => 0
  | a :: l => (a : ℤ) - altSum l

/-- **Euler–Poincaré for cosmohedra.**  For a `d`-polytope, counting faces by codimension
(including the polytope itself), `∑ (-1)^c f^c = (-1)^d`.  The face numbers of `Cosmo_n`
obtained from the russian-doll description satisfy this for every `n` from `3` to `12`. -/
theorem cosmo_euler_poincare :
    ∀ n ∈ Finset.Icc 3 12, altSum (cosmoFaces n) = (-1) ^ (n - 3) := by
  decide +kernel

/-- **Euler–Poincaré for associahedra** (`n = 3, …, 7`), from the explicit partial
triangulations. -/
theorem assoc_euler_poincare :
    ∀ n ∈ Finset.Icc 3 7, altSum (assocFaces n) = (-1) ^ (n - 3) := by
  decide +kernel

/-- **Facets of `Cosmo_n` are the non-empty partial triangulations** (the paper: "the total
number of facets of the cosmohedron is equal to the total number of all (not just complete)
triangulations of the `n`-gon").  Checked for `n = 4, …, 7` against the explicit enumeration. -/
theorem cosmo_facets_eq_partialTriangulations :
    ∀ n ∈ Finset.Icc 4 7, (cosmoFaces n)[1]! = (partialTriangulations n).card - 1 := by
  decide +kernel

/-- **Vertices of `Assoc_n` are counted by Catalan numbers**: `C_{n-2}` complete triangulations
(`n = 3, …, 7`). -/
theorem assoc_vertices_catalan :
    ∀ n ∈ Finset.Icc 3 7, assocFaceCount n (n - 3) = catalan (n - 2) := by
  decide +kernel

/-- The paper's recursion for the number of terms of the tree-level wavefunction,
`Ψ₃ = 1`, `Ψ_n = ∑_{k=3}^{n-1} (k-1) Ψ_k Ψ_{n+2-k}`, as a table `[Ψ₀, …, Ψ_n]`
(entries below `3` are placeholders `0`). -/
def psiTable : ℕ → List ℕ
  | 0 => [0]
  | k + 1 =>
    let T := psiTable k
    let n := k + 1
    T ++ [if n < 3 then 0 else if n = 3 then 1 else
      ((List.range n).filter (3 ≤ ·)).foldr
        (fun j acc => (j - 1) * T.getD j 0 * T.getD (n + 2 - j) 0 + acc) 0]

/-- `Ψ_n`, the number of terms in the `n`-point tree-level wavefunction. -/
def psi (n : ℕ) : ℕ := (psiTable n).getD n 0

/-- **Vertices of `Cosmo_n` = wavefunction terms `Ψ_n`**: the last face number (codimension
`n-3`, i.e. the vertices, i.e. the maximal russian dolls) equals the paper's `Ψ_n` for
`n = 3, …, 12`. -/
theorem cosmo_vertices_eq_psi :
    ∀ n ∈ Finset.Icc 3 12, (cosmoFaces n).getLast! = psi n := by
  decide +kernel

/-- The values `Ψ_3, …, Ψ_12`. -/
theorem psi_values :
    (List.range 10).map (fun i => psi (i + 3)) =
      [1, 2, 10, 72, 644, 6704, 78408, 1008480, 14065744, 210682080] := by
  decide +kernel

/-! ## 4. The pentagon: `Assoc_5` and the flip graph

The two-dimensional associahedron `Assoc_5` is a pentagon.  Its vertices are the five
triangulations of a pentagon and its edges are *flips* (replace one chord by the other diagonal
of the quadrilateral it sits in).  This is the pentagon of the pentagon equation for F-moves in
`QBX.Formal.AnyonCoherence` (`IsPentagon`): an F-move is a flip of the dual trivalent tree, and
the equation compares the two flip paths (of lengths 2 and 3) between opposite vertices. -/

/-- Two triangulations of the `n`-gon differ by a flip: they share all chords but one. -/
def IsFlip (n : ℕ) (S T : Finset (ℕ × ℕ)) : Prop := (S ∩ T).card + 4 = n ∧ S ≠ T

instance (n : ℕ) (S T : Finset (ℕ × ℕ)) : Decidable (IsFlip n S T) := by
  unfold IsFlip; infer_instance

/-- Complete triangulations of the `n`-gon. -/
def triangulations (n : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (partialTriangulations n).filter (fun s => s.card + 3 = n)

/-- The five triangulations of the pentagon, in cyclic flip order. -/
def pentagonCycle : List (Finset (ℕ × ℕ)) :=
  [{(0, 2), (0, 3)}, {(0, 3), (1, 3)}, {(1, 3), (1, 4)}, {(1, 4), (2, 4)}, {(2, 4), (0, 2)}]

/-- **The flip graph of the pentagon is a 5-cycle**: the five listed sets are exactly the
triangulations, consecutive ones (cyclically) differ by a flip, and every triangulation has
exactly two flip neighbours. -/
theorem pentagon_flip_graph :
    pentagonCycle.toFinset = triangulations 5 ∧ pentagonCycle.Nodup ∧
    (∀ i : Fin 5, IsFlip 5 (pentagonCycle.getD i ∅) (pentagonCycle.getD ((i + 1) % 5) ∅)) ∧
    ∀ T ∈ triangulations 5, ((triangulations 5).filter (IsFlip 5 T)).card = 2 := by
  decide +kernel

end QBX.Notes.Cosmohedra
