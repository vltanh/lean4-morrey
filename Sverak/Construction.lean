module

public import Sverak.Lemma1
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Šverák 1992, Section 2: the subspace `L`, the function `f` and the map `w`

* `ofRST r s t = (r 0; 0 s; t t)`, `L` the subspace of these matrices, `sverakP` (in
  `Morrey.Defs`) the orthogonal projection onto `L` (`sverakP_mem`, `sverakP_of_mem`,
  `sverakP_orth`).
* `sverakf (P X) = −r s t` (`sverakf_ofRST`).
* `rank_ofRST_eq_one`, `sverakf_affine_of_rankOne` (`sv-L`): "the only rank-one directions in `L`
  are" the three coordinate directions, "therefore the function `f` is convex (in fact linear) on
  each rank-one line contained in `L`".
* `w (x) = (2π)⁻¹ (sin 2πx₁, sin 2πx₂, sin 2π(x₁ + x₂))`, smooth and periodic, with
  `D w (x) ∈ L` (`jac_w`).
* `equation4` (`sv-eq4`): `∫_{[0,1]²} f (D w) = −∫ (cos 2πx₁)² (cos 2πx₂)² < 0 = f (0)`.
-/

@[expose] public section

open MeasureTheory Morrey Real

namespace Sverak

/-- The matrix `(r 0; 0 s; t t)`. -/
def ofRST (r s t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![r, 0; 0, s; t, t]

/-- Šverák's subspace `L = {(r 0; 0 s; t t) : r, s, t ∈ ℝ}` of `M^{3×2}`. -/
def L : Set (Matrix (Fin 3) (Fin 2) ℝ) :=
  Set.range fun p : ℝ × ℝ × ℝ => ofRST p.1 p.2.1 p.2.2

theorem sverakP_mem (X : Matrix (Fin 3) (Fin 2) ℝ) : sverakP X ∈ L := by
  sorry

theorem sverakP_of_mem {X : Matrix (Fin 3) (Fin 2) ℝ} (hX : X ∈ L) : sverakP X = X := by
  sorry

/-- `X − P X` is orthogonal to `L` for the Frobenius inner product: `P` is the orthogonal
projection onto `L`. -/
theorem sverakP_orth (X : Matrix (Fin 3) (Fin 2) ℝ) {Y : Matrix (Fin 3) (Fin 2) ℝ} (hY : Y ∈ L) :
    ∑ i, ∑ j, (X - sverakP X) i j * Y i j = 0 := by
  sorry

theorem sverakf_ofRST (r s t : ℝ) : sverakf (ofRST r s t) = -(r * s * t) := by
  sorry

/-- (`sv-L`) The rank-one matrices of `L` are the nonzero multiples of the three directions
`(1 0; 0 0; 0 0)`, `(0 0; 0 1; 0 0)`, `(0 0; 0 0; 1 1)`. -/
theorem rank_ofRST_eq_one (r s t : ℝ) :
    (ofRST r s t).rank = 1 ↔
      (r ≠ 0 ∧ s = 0 ∧ t = 0) ∨ (r = 0 ∧ s ≠ 0 ∧ t = 0) ∨ (r = 0 ∧ s = 0 ∧ t ≠ 0) := by
  sorry

/-- (`sv-L`) The function `f` is affine on each rank-one line contained in `L`. -/
theorem sverakf_affine_of_rankOne {A B : Matrix (Fin 3) (Fin 2) ℝ} (hA : A ∈ L) (hB : B ∈ L)
    (hB1 : B.rank = 1) : ∃ a b : ℝ, ∀ τ : ℝ, sverakf (A + τ • B) = a + b * τ := by
  sorry

/-- Šverák's map `w : ℝ² → ℝ³`, `w (x) = (2π)⁻¹ (sin 2πx₁, sin 2πx₂, sin 2π(x₁ + x₂))`. -/
noncomputable def w (x : Fin 2 → ℝ) : Fin 3 → ℝ :=
  (2 * π)⁻¹ • ![sin (2 * π * x 0), sin (2 * π * x 1), sin (2 * π * (x 0 + x 1))]

theorem w_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
  sorry

theorem w_periodic : IsPeriodic w := by
  sorry

/-- `D w (x) = (cos 2πx₁ 0; 0 cos 2πx₂; cos 2π(x₁+x₂) cos 2π(x₁+x₂)) ∈ L`. -/
theorem jac_w (x : Fin 2 → ℝ) :
    jac w x = ofRST (cos (2 * π * x 0)) (cos (2 * π * x 1)) (cos (2 * π * (x 0 + x 1))) := by
  sorry

/-- **Equation (4)** (`sv-eq4`). `∫_{[0,1]²} f (D w (x)) dx = −∫_{[0,1]²} (cos 2πx₁)² (cos 2πx₂)² dx
< 0 = f (0)`. -/
theorem equation4 :
    ∫ x in unitCube 2, sverakf (jac w x) =
        -∫ x in unitCube 2, cos (2 * π * x 0) ^ 2 * cos (2 * π * x 1) ^ 2 ∧
      ∫ x in unitCube 2, sverakf (jac w x) < sverakf 0 := by
  sorry

end Sverak
