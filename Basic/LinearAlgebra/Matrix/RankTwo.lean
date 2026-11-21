module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The rank of a `2 × 2` matrix

A `2 × 2` matrix over a field has rank at most one exactly when its determinant vanishes, that
is, when its two rows are linearly dependent.
-/

@[expose] public section

namespace Matrix

variable {K : Type*} [Field K]

/-- A `2 × 2` matrix over a field has rank at most one exactly when its determinant vanishes. -/
theorem rank_le_one_iff_det_eq_zero_of_fin_two (A : Matrix (Fin 2) (Fin 2) K) :
    A.rank ≤ 1 ↔ A.det = 0 := by
  constructor
  · intro h
    by_contra hdet
    have h2 := Matrix.rank_of_det_ne_zero hdet
    rw [Fintype.card_fin] at h2
    omega
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hker : v ∈ LinearMap.ker A.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hv]
    have hpos : 0 < Module.finrank K (LinearMap.ker A.mulVecLin) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨⟨v, hker⟩, fun h => hv0 (congrArg Subtype.val h)⟩
    have hsum := A.mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
    rw [Matrix.rank]
    omega

/-- The determinant of the matrix with rows `x` and `y`. -/
theorem det_of_rows_fin_two (x y : Fin 2 → K) :
    (Matrix.of ![x, y]).det = x 0 * y 1 - x 1 * y 0 := by
  simp [Matrix.det_fin_two]

end Matrix
