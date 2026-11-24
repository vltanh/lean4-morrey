module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact

/-!
# One-variable facts behind the supports

* `norm_ofReal_add_mul`, `hasDerivAt_norm_ofReal_add_mul`: the modulus of `x + τ α` for real
  `x`, `τ`, and its derivative `Re α` in `τ` at `τ = 0` when `x > 0`.
* `half_mul_sq_sub_le_rpow`: `(p/2) σ² − (p/2 − 1) ≤ σ^p` for `p ≥ 2` (weighted AM–GM).
* `burkholder_support_le`: the inequality behind the Burkholder-type supports,
  `−(p−1) c₀ + p c₀ σ − (p−2) m δ + (p−1) m σ δ ≤ max (0, σ^{p−1} (c₀ σ + m δ))`
  for `p ≥ 2`, `(p − 2) |m| ≤ p c₀`, `|δ| ≤ σ`.
* `exists_stationary_ge`: for `p > 2` and `a < 0`, the function
  `ψ (l) = a l^p + b l^{p−1} + e l^{p−2}` has, if `ψ (1) > 0`, a critical point `l > 0` with
  `ψ (l) ≥ ψ (1)`.
-/

@[expose] public section

open Set Filter Topology

namespace HomogeneousIsotropic

/-- The modulus of `x + τ α`, for real `x` and `τ`. -/
theorem norm_ofReal_add_mul (x τ : ℝ) (α : ℂ) :
    ‖(x : ℂ) + τ * α‖ = √((x + τ * α.re) ^ 2 + (τ * α.im) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

/-- For `x > 0`, the modulus of `x + τ α` has the derivative `Re α` in `τ` at `τ = 0`. -/
theorem hasDerivAt_norm_ofReal_add_mul {x : ℝ} (hx : 0 < x) (α : ℂ) :
    HasDerivAt (fun τ : ℝ => ‖(x : ℂ) + τ * α‖) α.re 0 := by
  have hf : (fun τ : ℝ => ‖(x : ℂ) + τ * α‖) =
      fun τ : ℝ => √((x + τ * α.re) ^ 2 + (τ * α.im) ^ 2) := by
    funext τ
    exact norm_ofReal_add_mul x τ α
  rw [hf]
  have ha : HasDerivAt (fun τ : ℝ => x + τ * α.re) α.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const α.re).const_add x
  have hb : HasDerivAt (fun τ : ℝ => τ * α.im) α.im 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const α.im
  have h1 := (ha.pow 2).add (hb.pow 2)
  have h2 := h1.sqrt (by simp; positivity)
  have h0 : √(((fun τ : ℝ => x + τ * α.re) ^ 2 + (fun τ : ℝ => τ * α.im) ^ 2) 0) = x := by
    simp [Real.sqrt_sq hx.le]
  convert h2 using 1
  rw [h0]
  simp only [zero_mul, add_zero, mul_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp

/-- Weighted AM–GM: `(p/2) σ² − (p/2 − 1) ≤ σ^p` for `p ≥ 2` and `σ ≥ 0`. -/
theorem half_mul_sq_sub_le_rpow {p σ : ℝ} (hp : 2 ≤ p) (hσ : 0 ≤ σ) :
    p / 2 * σ ^ 2 - (p / 2 - 1) ≤ σ ^ p := by
  have h := one_add_mul_self_le_rpow_one_add (s := σ ^ 2 - 1) (by nlinarith [sq_nonneg σ])
    (p := p / 2) (by linarith)
  have h2 : (1 + (σ ^ 2 - 1)) ^ (p / 2) = σ ^ p := by
    rw [show 1 + (σ ^ 2 - 1) = σ ^ (2 : ℝ) by rw [Real.rpow_two]; ring, ← Real.rpow_mul hσ]
    congr 1
    ring
  linarith

/-- The inequality behind the Burkholder-type supports. For `p ≥ 2`, `(p − 2) |m| ≤ p c₀` and
`|δ| ≤ σ`,
`−(p−1) c₀ + p c₀ σ − (p−2) m δ + (p−1) m σ δ ≤ max (0, σ^{p−1} (c₀ σ + m δ))`. -/
theorem burkholder_support_le {p c₀ m σ δ : ℝ} (hp : 2 ≤ p) (hc : (p - 2) * |m| ≤ p * c₀)
    (hσ : 0 ≤ σ) (hδ : |δ| ≤ σ) :
    -(p - 1) * c₀ + p * c₀ * σ - (p - 2) * m * δ + (p - 1) * m * σ * δ ≤
      max 0 (σ ^ (p - 1) * (c₀ * σ + m * δ)) := by
  have hc₀ : 0 ≤ c₀ := by
    have h : 0 ≤ p * c₀ := le_trans (mul_nonneg (by linarith) (abs_nonneg m)) hc
    exact nonneg_of_mul_nonneg_right h (by linarith)
  -- `(p − 2) m δ ≤ p c₀ σ` and `−(p − 2) m δ ≤ p c₀ σ`
  have hmδ : (p - 2) * |m * δ| ≤ p * c₀ * σ := by
    rw [abs_mul]
    calc (p - 2) * (|m| * |δ|) = (p - 2) * |m| * |δ| := by ring
      _ ≤ (p - 2) * |m| * σ :=
        mul_le_mul_of_nonneg_left hδ (mul_nonneg (by linarith) (abs_nonneg m))
      _ ≤ p * c₀ * σ := mul_le_mul_of_nonneg_right hc hσ
  have hmδ1 : (p - 2) * (m * δ) ≤ p * c₀ * σ :=
    le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)) hmδ
  have hmδ2 : (p - 2) * (-(m * δ)) ≤ p * c₀ * σ :=
    le_trans (mul_le_mul_of_nonneg_left (neg_le_abs _) (by linarith)) hmδ
  rcases hσ.eq_or_lt with rfl | hσpos
  · have hδ0 : δ = 0 := abs_eq_zero.1 (le_antisymm hδ (abs_nonneg δ))
    subst hδ0
    refine le_trans ?_ (le_max_left _ _)
    nlinarith
  by_cases hA : 0 ≤ c₀ * σ + m * δ
  · refine le_trans ?_ (le_max_right _ _)
    have hpow : σ ^ p = σ ^ (p - 1) * σ := by
      rw [← Real.rpow_add_one hσpos.ne']
      congr 1
      ring
    have hamgm := half_mul_sq_sub_le_rpow hp hσ
    have hid : (c₀ * σ + m * δ) * (p / 2 * σ ^ 2 - (p / 2 - 1)) -
        σ * (-(p - 1) * c₀ + p * c₀ * σ - (p - 2) * m * δ + (p - 1) * m * σ * δ) =
        (σ - 1) ^ 2 * (p / 2 * c₀ * σ - (p / 2 - 1) * (m * δ)) := by
      ring
    have hnn : 0 ≤ (σ - 1) ^ 2 * (p / 2 * c₀ * σ - (p / 2 - 1) * (m * δ)) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    have h3 : (c₀ * σ + m * δ) * (p / 2 * σ ^ 2 - (p / 2 - 1)) ≤ (c₀ * σ + m * δ) * σ ^ p :=
      mul_le_mul_of_nonneg_left hamgm hA
    refine le_of_mul_le_mul_left ?_ hσpos
    calc σ * (-(p - 1) * c₀ + p * c₀ * σ - (p - 2) * m * δ + (p - 1) * m * σ * δ)
        ≤ (c₀ * σ + m * δ) * (p / 2 * σ ^ 2 - (p / 2 - 1)) := by linarith
      _ ≤ (c₀ * σ + m * δ) * σ ^ p := h3
      _ = σ * (σ ^ (p - 1) * (c₀ * σ + m * δ)) := by rw [hpow]; ring
  · refine le_trans ?_ (le_max_left _ _)
    replace hA : c₀ * σ + m * δ < 0 := not_le.1 hA
    -- `N = −m δ > c₀ σ ≥ 0`
    set N : ℝ := -(m * δ) with hN
    have hNpos : 0 < N := by nlinarith [mul_nonneg hc₀ hσ]
    have hNc : c₀ * σ < N := by linarith
    have hpN : (p - 2) * N ≤ p * c₀ * σ := hmδ2
    set q : ℝ := -(p - 1) * c₀ + p * c₀ * σ - (p - 2) * m * δ + (p - 1) * m * σ * δ with hq
    have hid : 4 * (p - 1) * N * σ * q =
        -(2 * (p - 1) * N * σ - (p * c₀ * σ + (p - 2) * N)) ^ 2 +
          (c₀ * σ - N) * (p ^ 2 * c₀ * σ - (p - 2) ^ 2 * N) := by
      rw [hq, hN]
      ring
    have h2 : 0 ≤ p ^ 2 * c₀ * σ - (p - 2) ^ 2 * N := by
      have : (p - 2) ^ 2 * N ≤ p * ((p - 2) * N) := by nlinarith
      nlinarith [mul_nonneg hc₀ hσ]
    have h3 : 4 * (p - 1) * N * σ * q ≤ 0 := by
      rw [hid]
      nlinarith [sq_nonneg (2 * (p - 1) * N * σ - (p * c₀ * σ + (p - 2) * N)),
        mul_nonneg (sub_nonneg.2 hNc.le) h2]
    by_contra hcon
    replace hcon : 0 < q := not_le.1 hcon
    have : 0 < 4 * (p - 1) * N * σ * q := by
      have h4 : 0 < 4 * (p - 1) * N * σ := by
        have : 0 < p - 1 := by linarith
        positivity
      exact mul_pos h4 hcon
    linarith

/-- For `p > 2`, `a < 0` and any `b`, `e`, if `ψ (l) = a l^p + b l^{p−1} + e l^{p−2}` is positive
at `l = 1`, then `ψ` has a critical point `l > 0` with `ψ (l) ≥ ψ (1)`; the critical points are
the positive roots of `p a l² + (p − 1) b l + (p − 2) e`. -/
theorem exists_stationary_ge {p a b e : ℝ} (hp : 2 < p) (ha : a < 0) (hpos : 0 < a + b + e) :
    ∃ l : ℝ, 0 < l ∧ p * a * l ^ 2 + (p - 1) * b * l + (p - 2) * e = 0 ∧
      a + b + e ≤ a * l ^ p + b * l ^ (p - 1) + e * l ^ (p - 2) := by
  set ψ : ℝ → ℝ := fun l => a * l ^ p + b * l ^ (p - 1) + e * l ^ (p - 2) with hψ
  have hcont : Continuous ψ := by
    have h1 : Continuous fun l : ℝ => l ^ p := Real.continuous_rpow_const (by linarith)
    have h2 : Continuous fun l : ℝ => l ^ (p - 1) := Real.continuous_rpow_const (by linarith)
    have h3 : Continuous fun l : ℝ => l ^ (p - 2) := Real.continuous_rpow_const (by linarith)
    exact ((continuous_const.mul h1).add (continuous_const.mul h2)).add (continuous_const.mul h3)
  set Λ : ℝ := max 1 ((b + |e|) / (-a)) with hΛ
  have hΛ1 : 1 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := by linarith
  have hΛ2 : b + |e| ≤ Λ * (-a) := by
    have := le_max_right 1 ((b + |e|) / (-a))
    rwa [div_le_iff₀ (by linarith)] at this
  have hψΛ : ψ Λ ≤ 0 := by
    have e1 : Λ ^ p = Λ ^ (p - 2) * Λ ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hΛpos]
      congr 1
      norm_num
    have e2 : Λ ^ (p - 1) = Λ ^ (p - 2) * Λ := by
      rw [← Real.rpow_add_one hΛpos.ne']
      congr 1
      ring
    have h4 : a * Λ ^ 2 + b * Λ + e ≤ 0 := by
      nlinarith [abs_nonneg e, le_abs_self e, mul_nonneg (abs_nonneg e) (sub_nonneg.2 hΛ1),
        mul_le_mul_of_nonneg_left hΛ2 hΛpos.le]
    have h5 : ψ Λ = Λ ^ (p - 2) * (a * Λ ^ 2 + b * Λ + e) := by
      simp only [hψ]
      rw [e1, e2]
      ring
    rw [h5]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hΛpos.le _) h4
  obtain ⟨l, hl, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hΛpos.le)
    hcont.continuousOn
  have hψ1 : ψ 1 = a + b + e := by simp [hψ]
  have hψ0 : ψ 0 = 0 := by
    simp only [hψ]
    rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
    ring
  have h1 : ψ 1 ≤ ψ l := hmax ⟨zero_le_one, hΛ1⟩
  have hl0 : l ≠ 0 := by
    rintro rfl
    linarith
  have hlΛ : l ≠ Λ := by
    rintro rfl
    linarith
  have hlpos : 0 < l := lt_of_le_of_ne hl.1 (Ne.symm hl0)
  have hlt : l < Λ := lt_of_le_of_ne hl.2 hlΛ
  have hloc : IsLocalMax ψ l := hmax.isLocalMax (Icc_mem_nhds hlpos hlt)
  have hder : HasDerivAt ψ (a * (p * l ^ (p - 1)) + b * ((p - 1) * l ^ (p - 1 - 1)) +
      e * ((p - 2) * l ^ (p - 2 - 1))) l :=
    (((Real.hasDerivAt_rpow_const (p := p) (Or.inl hlpos.ne')).const_mul a).add
      ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hlpos.ne')).const_mul b)).add
      ((Real.hasDerivAt_rpow_const (p := p - 2) (Or.inl hlpos.ne')).const_mul e)
  have hzero := hloc.hasDerivAt_eq_zero hder
  refine ⟨l, hlpos, ?_, by rw [← hψ1]; exact h1⟩
  have e1 : l ^ (p - 1) = l ^ (p - 3) * l ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hlpos]
    congr 1
    push_cast
    ring
  have e2 : l ^ (p - 1 - 1) = l ^ (p - 3) * l := by
    rw [← Real.rpow_add_one hlpos.ne']
    congr 1
    ring
  have e3 : l ^ (p - 2 - 1) = l ^ (p - 3) := by
    congr 1
    ring
  have hpos3 : 0 < l ^ (p - 3) := Real.rpow_pos_of_pos hlpos _
  rw [e1, e2, e3] at hzero
  have h6 : l ^ (p - 3) * (p * a * l ^ 2 + (p - 1) * b * l + (p - 2) * e) = 0 := by
    linear_combination hzero
  exact (mul_eq_zero.1 h6).resolve_left hpos3.ne'

end HomogeneousIsotropic
