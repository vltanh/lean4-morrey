module

public import Morrey.NonEmptiness.Statements

/-!
# Corollary 7.2, Proposition 7.1 and the summary of Step 2 are false

A counterexample at the level `l = 1`, for the mold `TriMold.canonical 1`: the grid has `2 × 2`
cells and `τ_1` has `8` triangles.

* `tri x = |x − round x|`, the distance from `x` to the nearest integer, a `1`-periodic triangle
  wave, affine on each interval `[k/2, (k + 1)/2]`.
* `uCex = tri(x₀) − tri(x₁) − tri(x₀ + x₁)` and `vCex = −tri(x₀) + tri(x₁) − tri(x₀ + x₁)`
  (so `vCex (x₀, x₁) = uCex (x₁, x₀)`) lie in `ℙ_1`. Their values at the nodes
  `(0,0), (½,0), (0,½), (½,½)` are `0, 0, −1, 0` and `0, −1, 0, 0`.
* `tCex`: the uniform weights `1/48`, in `Θ_1`.

The first mixture above the first level of the sub-mold `0` of `TriMold.canonical 1` mixes the
vertical interfaces `(0, 0, 0)` and `(0, 0, 1)`. Across a vertical interface the derivative
`∂₂` of a function of `ℙ_l` is continuous, so the mass points of these two first-level mixtures
have second coordinates `∂₂w` on the interfaces, whatever the weights. For `uCex` and `tCex` the
two mass points are `(1, 0)` and `(−1, 0)`, so the decomposition direction is `(2, 0)`. For `vCex`
the second coordinates are `2` and `−2` for all weights `r`, so the direction is `(*, 4)`, never
parallel to `(2, 0)`. Hence no `r` satisfies the condition of Definition 6.1 at this mixture:
`𝐓(tCex) = ∅` (`T_cex_eq_empty`). The same mixture refutes Proposition 7.1 (with `w := vCex`) and
the summary of Step 2 (with `j = 0`).
-/

@[expose] public section

namespace Morrey

/-- The distance from `x` to the nearest integer. -/
noncomputable def tri (x : ℝ) : ℝ :=
  |x - round x|

/-- The first component of the counterexample. -/
noncomputable def uCex : (Fin 2 → ℝ) → ℝ :=
  fun x => tri (x 0) - tri (x 1) - tri (x 0 + x 1)

/-- The second component of the counterexample. -/
noncomputable def vCex : (Fin 2 → ℝ) → ℝ :=
  fun x => -tri (x 0) + tri (x 1) - tri (x 0 + x 1)

/-- The uniform weights of `Θ_1`. -/
noncomputable def tCex : Leaf 1 → ℝ :=
  fun _ => 1 / 48

theorem uCex_mem : uCex ∈ PL 1 := by
  sorry

theorem vCex_mem : vCex ∈ PL 1 := by
  sorry

theorem tCex_mem : tCex ∈ Theta (TriMold.canonical 1) := by
  sorry

/-- For the mold `TriMold.canonical 1`, the image `𝐓(tCex)` of the counterexample is empty. -/
theorem T_cex_eq_empty : T (TriMold.canonical 1) uCex vCex tCex = ∅ := by
  sorry

/-- **Corollary 7.2 is false.** -/
theorem corollary7_2_false : ¬ Corollary7_2 := by
  sorry

/-- **Proposition 7.1** (`esta`) **is false.** -/
theorem proposition7_1_false : ¬ Proposition7_1 := by
  sorry

/-- **The summary of Step 2 of the proof of Proposition 7.1 is false**, already for the sub-mold
`j = 0`: no weights at all make the decomposition directions of `vCex` parallel to those of
`uCex` along it. -/
theorem step2Claim_false : ¬ Step2Claim := by
  sorry

end Morrey
