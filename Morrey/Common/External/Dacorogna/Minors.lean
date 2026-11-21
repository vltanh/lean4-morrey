module

public import Morrey.Common.Basic.CalculusOfVariations.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Dacorogna: rank-one affine functions and quadratic forms

B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer 2008,
Theorems 5.20 and 5.25 (i). Cassese uses both in the proof of Proposition 5.1 only. Theorem 5.20
is large but feasible (class L): a proposition with no proof, a hypothesis of every statement
whose proof uses it. Theorem 5.25 (i) (Fourier–Plancherel) is within reach (class Mod): stated,
to be proved.
-/

@[expose] public section

namespace External.Dacorogna

open CalculusOfVariations

variable {d m : ℕ}

/-- The `k × k` minor of `A` with the rows `r` and the columns `c` (strictly increasing). -/
noncomputable def minor (A : Matrix (Fin d) (Fin m) ℝ) {k : ℕ} (r : Fin k ↪o Fin d)
    (c : Fin k ↪o Fin m) : ℝ :=
  (A.submatrix r c).det

/-- Dacorogna, Theorem 5.20 (used in the proof of Cassese's Proposition 5.1): a
continuous rank-one affine `f : ℝ^{d×m} → ℝ` is an affine combination of the minors of its
argument (the `0 × 0` minor is the constant `1`). -/
def RankOneAffineMinors : Prop :=
  ∀ (d m : ℕ) (f : Matrix (Fin d) (Fin m) ℝ → ℝ), Continuous f → RankOneAffine f →
    ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
      ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c

/-- Dacorogna, Theorem 5.25 (i) (used in the proof of Cassese's Proposition 5.1): a rank-one
convex quadratic form is quasiconvex. -/
theorem quadraticForm_quasiconvex
    (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ))
    (hQ : RankOneConvex fun A => Q A A) : Quasiconvex fun A => Q A A := by
  sorry

end External.Dacorogna
