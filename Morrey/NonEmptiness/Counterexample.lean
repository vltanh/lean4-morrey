module

public import Morrey.NonEmptiness.Statements

/-!
# Corollary 7.2 and Proposition 7.1 are false

A counterexample at the level `l = 1`: the grid has `2 × 2` cells, `τ_1` has `8` triangles, each
sub-mold has `8` interfaces and `16` leaves, and the mold has `48` leaves.

* `tri x = |x − round x|`, the distance from `x` to the nearest integer, a `1`-periodic triangle
  wave, affine on each interval `[k/2, (k + 1)/2]`.
* `uCex = −2 tri(x₀) − 2 tri(x₁) + 4 tri(x₀ + x₁)` and `vCex = 3 tri(x₀) − tri(x₁) + tri(x₀ + x₁)`
  lie in `ℙ_1`. Their values at the nodes `(0,0), (½,0), (0,½), (½,½)` are `0, 1, 1, −2` and
  `0, 2, 0, 1`.
* `tCex`: the uniform weights `1/48`, in `Θ_1`.
* `T_cex_eq_empty`: for the explicit mold `TriMold.canonical 1`, `𝐓(tCex) = ∅`. The linear
  conditions that define `𝐓(tCex)` are inconsistent: a linear combination of 16 of the
  first-level conditions (5.5), 4 of the triangle conditions (5.6) and 14 of the parallelism
  conditions of Definition 6.1 reads `0 = 1`. The coefficients were found with exact rational
  linear algebra.
-/

@[expose] public section

namespace Morrey

/-- The distance from `x` to the nearest integer. -/
noncomputable def tri (x : ℝ) : ℝ :=
  |x - round x|

/-- The first component of the counterexample. -/
noncomputable def uCex : (Fin 2 → ℝ) → ℝ :=
  fun x => -2 * tri (x 0) - 2 * tri (x 1) + 4 * tri (x 0 + x 1)

/-- The second component of the counterexample. -/
noncomputable def vCex : (Fin 2 → ℝ) → ℝ :=
  fun x => 3 * tri (x 0) - tri (x 1) + tri (x 0 + x 1)

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

end Morrey
