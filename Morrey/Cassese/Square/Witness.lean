module

public import Morrey.Cassese.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The trigonometric witness of Propositions 6.1 and 6.6

The paper's witness is `u : 𝕋^d → ℝ^d`, `u_i (x) = Σ_{j ≠ i} cos (x_i − x_j)`, on
`𝕋^d = ℝ^d / (2πℤ)^d`. On the unit torus `ℝ^d / ℤ^d` it is `w (x) = (2π)⁻¹ u (2π x)`
(`squareWitness`), so that `∇w (x) = ∇u (2π x)`: with `θ = 2π x`,
`(∇w)_{ik} = sin (θ_i − θ_k) − δ_{ik} Σ_j sin (θ_i − θ_j)` (`jac_squareWitness`), the paper's
`∇u = a ⊗ b − b ⊗ a + diag (A b − B a)` (`a_i = sin θ_i`, `b_i = cos θ_i`, `A = Σ a_i`,
`B = Σ b_i`) written entrywise. `w` is smooth and `ℤ^d`-periodic.
-/

@[expose] public section

open Real

namespace Cassese

variable {d : ℕ}

/-- The witness of Propositions 6.1 and 6.6 on the unit torus:
`w_i (x) = (2π)⁻¹ Σ_{j ≠ i} cos (2π (x_i − x_j))`. -/
noncomputable def squareWitness (d : ℕ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (2 * π)⁻¹ * ∑ j ∈ Finset.univ.erase i, cos (2 * π * (x i - x j))

theorem squareWitness_eq (x : Fin d → ℝ) (i : Fin d) :
    squareWitness d x i = (2 * π)⁻¹ * ((∑ j, cos (2 * π * (x i - x j))) - 1) := by
  rw [squareWitness, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), sub_self, mul_zero,
    cos_zero, add_sub_cancel_right]

theorem squareWitness_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (squareWitness d) := by
  refine contDiff_pi.2 fun i => ?_
  simp only [squareWitness]
  fun_prop

/-- `w` is `ℤ^d`-periodic. -/
theorem squareWitness_periodic (x : Fin d → ℝ) (z : Fin d → ℤ) :
    squareWitness d (x + fun i => (z i : ℝ)) = squareWitness d x := by
  funext i
  simp only [squareWitness, Pi.add_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * π * (x i + (z i : ℝ) - (x j + (z j : ℝ))) =
    2 * π * (x i - x j) + ((z i - z j : ℤ) : ℝ) * (2 * π) by push_cast; ring,
    cos_add_int_mul_two_pi]

theorem square_hasFDerivAt_witness (x : Fin d → ℝ) (i : Fin d) :
    HasFDerivAt (fun y => squareWitness d y i)
      ((2 * π)⁻¹ • ∑ j, (-sin (2 * π * (x i - x j))) •
        ((2 * π) • ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj j))) x := by
  have h : ∀ j, HasFDerivAt (fun y : Fin d → ℝ => cos (2 * π * (y i - y j)))
      ((-sin (2 * π * (x i - x j))) •
        ((2 * π) • ((ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj j))) x := fun j =>
    (((hasFDerivAt_apply i x).sub (hasFDerivAt_apply j x)).const_mul (2 * π)).cos
  have hs := (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => h j).sub_const 1
  have := hs.const_mul (2 * π)⁻¹
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  exact squareWitness_eq y i

/-- The gradient of the witness: with `θ = 2π x`,
`(∇w)_{ik} = sin (θ_i − θ_k) − δ_{ik} Σ_j sin (θ_i − θ_j)`. -/
theorem jac_squareWitness (x : Fin d → ℝ) :
    jac (squareWitness d) x = Matrix.of fun i k =>
      sin (2 * π * (x i - x k)) - if i = k then ∑ j, sin (2 * π * (x i - x j)) else 0 := by
  ext i k
  simp only [jac, Matrix.of_apply, (square_hasFDerivAt_witness x i).fderiv]
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply,
    sub_apply, ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul]
  have hπ : (2 * π) ≠ 0 := mul_ne_zero two_ne_zero pi_ne_zero
  have : ∀ j, (2 * π)⁻¹ * ((-sin (2 * π * (x i - x j))) *
      (2 * π * ((if i = k then (1:ℝ) else 0) - if j = k then 1 else 0))) =
      sin (2 * π * (x i - x j)) * (if j = k then 1 else 0) -
        (if i = k then sin (2 * π * (x i - x j)) else 0) := by
    intro j
    split_ifs <;> field_simp <;> ring
  rw [Finset.mul_sum]
  simp_rw [this, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  split_ifs <;> simp
end Cassese
