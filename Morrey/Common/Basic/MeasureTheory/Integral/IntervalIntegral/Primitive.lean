module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Primitives of functions that are continuous on an open set

* `intervalIntegral.hasDerivAt_integral_of_continuousOn`,
  `intervalIntegral.hasDerivAt_exp_integral`: if `ρ` is continuous on an open set that contains
  the interval between `0` and `x`, then `u ↦ ∫₀^u ρ` has the derivative `ρ x` at `x`, and
  `u ↦ exp (∫₀^u ρ)` the derivative `exp (∫₀^x ρ) ρ x`.
* `intervalIntegral.exists_exp_integral_eq`: a logarithmic divergence. If `ρ` is continuous on an
  open set that contains `[0, b)` and `ρ x ≥ κ/(b − x)` there, `κ > 0`, then `x ↦ exp (∫₀^x ρ)`
  takes every value `R ≥ 1` on `[0, b)`: `∫₀^x ρ + κ log (b − x)` is nondecreasing.
-/

@[expose] public section

open Set MeasureTheory

namespace intervalIntegral

/-- The derivative of a primitive: if `ρ` is continuous on an open set that contains the interval
between `0` and `x`, then `u ↦ ∫₀^u ρ` has the derivative `ρ x` at `x`. -/
theorem hasDerivAt_integral_of_continuousOn {ρ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hc : ContinuousOn ρ U) {x : ℝ} (hx : uIcc 0 x ⊆ U) :
    HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, ρ y) (ρ x) x := by
  have hxU : x ∈ U := hx right_mem_uIcc
  exact integral_hasDerivAt_right (hc.mono hx).intervalIntegrable
    (hc.stronglyMeasurableAtFilter hU x hxU) (hc.continuousAt (hU.mem_nhds hxU))

/-- The derivative of the exponential of a primitive: if `ρ` is continuous on an open set that
contains the interval between `0` and `x`, then `S u = exp (∫₀^u ρ)` has the derivative
`S x * ρ x` at `x`. -/
theorem hasDerivAt_exp_integral {ρ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hc : ContinuousOn ρ U)
    {x : ℝ} (hx : uIcc 0 x ⊆ U) :
    HasDerivAt (fun u => Real.exp (∫ y in (0 : ℝ)..u, ρ y))
      (Real.exp (∫ y in (0 : ℝ)..x, ρ y) * ρ x) x :=
  (hasDerivAt_integral_of_continuousOn hU hc hx).exp

/-- A logarithmic divergence. Let `ρ` be continuous on an open set that contains `[0, b)`, with
`ρ x ≥ κ/(b − x)` on `[0, b)` for some `κ > 0`. Then `x ↦ exp (∫₀^x ρ)`, which is `1` at `0`,
takes every value `R ≥ 1` on `[0, b)`. -/
theorem exists_exp_integral_eq {ρ : ℝ → ℝ} {U : Set ℝ} {b κ : ℝ} (hU : IsOpen U)
    (hc : ContinuousOn ρ U) (hsub : Ico 0 b ⊆ U) (hb : 0 < b) (hκ : 0 < κ)
    (hρ : ∀ x ∈ Ico 0 b, κ / (b - x) ≤ ρ x) {R : ℝ} (hR : 1 ≤ R) :
    ∃ L ∈ Ico 0 b, Real.exp (∫ y in (0 : ℝ)..L, ρ y) = R := by
  have hder : ∀ x ∈ Ico 0 b, HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, ρ y) (ρ x) x := by
    intro x hx
    refine hasDerivAt_integral_of_continuousOn hU hc fun y hy => hsub ?_
    rw [uIcc_of_le hx.1] at hy
    exact ⟨hy.1, hy.2.trans_lt hx.2⟩
  -- `E = ∫₀^x ρ + κ log (b − x)` is nondecreasing on `[0, b)`
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ, ∀ u, E u = (∫ y in (0 : ℝ)..u, ρ y) + κ * Real.log (b - u) :=
    ⟨_, fun _ => rfl⟩
  have hEder : ∀ x ∈ Ico 0 b, HasDerivAt E (ρ x + κ * ((0 - 1) / (b - x))) x := by
    intro x hx
    have h1 : HasDerivAt (fun u : ℝ => b - u) (0 - 1) x :=
      (hasDerivAt_const x b).sub (hasDerivAt_id x)
    have h2 := h1.log (sub_pos.2 hx.2).ne'
    rw [funext hE]
    exact (hder x hx).add (h2.const_mul κ)
  have hmono : MonotoneOn E (Ico 0 b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 b)
      (fun x hx => (hEder x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
      (fun x hx => ?_)
    · rw [interior_Ico] at hx
      exact (hEder x ⟨hx.1.le, hx.2⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Ico] at hx
      rw [(hEder x ⟨hx.1.le, hx.2⟩).deriv]
      have h := hρ x ⟨hx.1.le, hx.2⟩
      have e : κ * ((0 - 1) / (b - x)) = -(κ / (b - x)) := by ring
      linarith
  -- a point where the exponential is at least `R`
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.exp (-(Real.log R / κ)) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; exact Real.exp_pos _
  have hq1 : q ≤ 1 := by
    rw [hq, Real.exp_le_one_iff, neg_nonpos]
    exact div_nonneg (Real.log_nonneg hR) hκ.le
  have hlogq : Real.log q = -(Real.log R / κ) := by rw [hq, Real.log_exp]
  have hx₁ : b * (1 - q) ∈ Ico 0 b := ⟨mul_nonneg hb.le (by linarith), by nlinarith⟩
  have hE01 := hmono ⟨le_rfl, hb⟩ hx₁ hx₁.1
  have hE0 : E 0 = κ * Real.log b := by simp [hE]
  have hE1 : E (b * (1 - q)) =
      (∫ y in (0 : ℝ)..b * (1 - q), ρ y) + κ * (Real.log b - Real.log R / κ) := by
    rw [hE, show b - b * (1 - q) = b * q by ring, Real.log_mul hb.ne' hq0.ne', hlogq]
    ring
  have hΛ : Real.log R ≤ ∫ y in (0 : ℝ)..b * (1 - q), ρ y := by
    rw [hE0, hE1] at hE01
    have h : κ * (Real.log b - Real.log R / κ) = κ * Real.log b - Real.log R := by
      field_simp
    linarith
  have hS1 : R ≤ Real.exp (∫ y in (0 : ℝ)..b * (1 - q), ρ y) := by
    calc R = Real.exp (Real.log R) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (∫ y in (0 : ℝ)..b * (1 - q), ρ y) := Real.exp_le_exp.2 hΛ
  -- the intermediate value theorem
  have hcont : ContinuousOn (fun u => Real.exp (∫ y in (0 : ℝ)..u, ρ y))
      (Icc 0 (b * (1 - q))) := fun x hx =>
    (hder x ⟨hx.1, hx.2.trans_lt hx₁.2⟩).exp.continuousAt.continuousWithinAt
  have hRmem : R ∈ Icc (Real.exp (∫ y in (0 : ℝ)..0, ρ y))
      (Real.exp (∫ y in (0 : ℝ)..b * (1 - q), ρ y)) := by
    rw [integral_same, Real.exp_zero]
    exact ⟨hR, hS1⟩
  obtain ⟨L, hL, hLR⟩ := intermediate_value_Icc hx₁.1 hcont hRmem
  exact ⟨L, ⟨hL.1, hL.2.trans_lt hx₁.2⟩, hLR⟩

end intervalIntegral
