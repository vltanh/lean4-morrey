module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

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
  sorry

/-- The determinant of the matrix with rows `x` and `y`. -/
theorem det_of_rows_fin_two (x y : Fin 2 → K) :
    (Matrix.of ![x, y]).det = x 0 * y 1 - x 1 * y 0 := by
  sorry

end Matrix
