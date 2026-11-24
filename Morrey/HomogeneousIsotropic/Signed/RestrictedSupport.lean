module

public import Morrey.HomogeneousIsotropic.Signed.Basic
public import Morrey.HomogeneousIsotropic.Supports
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Restricted supports at a hard base

Let `Φ` be a profile of degree `p > 1`, `p ≠ 2`, with `h (−1) < 0` for its slice `h`, and let
`(t, m)` be a hard base, `H = h t`. The function
`q (x, y) = α + v r + c (x² − y²)` (`restrictedSupport`) equals `Φ` at
`((1 + t)/2, (1 − t)/2)`, and on the segment `x + y = 1` it is the supporting line. It is not
below `Φ` on the whole quadrant, but:

* `IsHardBase.restrictedSupport_le_of_lt` (`p < 2`): `q ≤ Φ` where `x < y`;
* `IsHardBase.restrictedSupport_le_of_nonneg` (`p > 2`): `q ≤ Φ` where `Φ ≥ 0`;
* `IsHardBase.restrictedSupport_le_of_add_le_one`: `q ≤ Φ` where `x + y ≤ 1`.

Hence the supporting planes are monotone along scaled hard bases
(`IsHardBase.scaled_monotone`): for hard bases `(tᵢ, mᵢ)` and scales `Sᵢ > 0`,
`(V₂ − V₁) (r₂ − r₁) + (C₂ − C₁) (d₂ − d₁) ≥ 0`, where `Vᵢ = Sᵢ^{p−1} vᵢ`, `Cᵢ = Sᵢ^{p−2} cᵢ`,
`rᵢ = Sᵢ (1 − e tᵢ)/2`, `dᵢ = Sᵢ² tᵢ`.

The proofs study `ψ (l) = l^p q (x/l, y/l) = α l^p + v r l^{p−1} + c (x² − y²) l^{p−2}`, whose
critical points are the positive roots of `p α l² + (p − 1) v r l + (p − 2) c (x² − y²)`:

* for `p > 2` and `Φ (x, y) ≥ 0`, as in `IsProfile.support_of_neg_aux`
  (`IsProfile.support_of_neg_of_nonneg`);
* for `p < 2` and `x < y`, `ψ` tends to `−∞` at `0` and at `∞`
  (`exists_stationary_ge_of_lt_two`), and at a maximizer the point `(x/l, y/l)` is on the image
  of a rank-one line through the base point, along which the first-order inequality is `q ≤ Φ`
  (`IsProfile.support_of_stationary_of_lt_two`, `IsProfile.support_of_lt`);
* for `x + y = s ≤ 1` and the remaining points, `ψ` is nonincreasing on `[s, 1]`
  (`add_add_le_of_forall_quadratic_nonpos`), and `ψ (s)` is the value at `(x, y)` of the
  Burkholder-type minorant (`restrictedSupport_rpow_eq`,
  `IsHardBase.restrictedSupport_le_of_forall_le`).
-/

@[expose] public section

open Set

namespace HomogeneousIsotropic

variable {p e : ℝ} {Φ : ℝ → ℝ → ℝ}

/-! ### The algebra of the coefficients -/

/-- The defining relation of the determinant coefficient. -/
theorem supportDet_mul {p e H m t : ℝ} (h : 1 + e * t ≠ 0) :
    supportDet p e H m t * (1 + e * t) = e * p * H + (1 - e * t) * m := by
  rw [supportDet, div_mul_cancel₀ _ h]

/-- The defining relation of the coefficient of the modulus. -/
theorem supportMod_mul {p e H m t : ℝ} (h : 1 + e * t ≠ 0) :
    supportMod p e H m t * (1 + e * t) = 2 * (p * H - 2 * t * m) := by
  rw [supportMod, div_mul_cancel₀ _ h]

/-- The restricted support has the value `H` at the base point. -/
theorem restrictedSupport_base {p e H m t : ℝ} (h : 1 + e * t ≠ 0) :
    restrictedSupport p e H m t ((1 + t) / 2) ((1 - t) / 2) = H := by
  simp only [restrictedSupport, supportConst, supportMod, supportDet]
  field_simp
  ring

/-- `c − e v/2 = m`. -/
theorem supportDet_sub {p e H m t : ℝ} (h : 1 + e * t ≠ 0) :
    supportDet p e H m t - e * supportMod p e H m t / 2 = m := by
  simp only [supportMod, supportDet]
  field_simp
  ring

/-- `α + v/2 = H − t m`. -/
theorem supportConst_add {p e H m t : ℝ} (h : 1 + e * t ≠ 0) :
    supportConst p e H m t + supportMod p e H m t / 2 = H - t * m := by
  simp only [supportConst, supportMod, supportDet]
  field_simp
  ring

/-- On the segment `x + y = 1` the restricted support is the supporting line. -/
theorem restrictedSupport_of_add_eq_one {p e H m t x y : ℝ} (h : 1 + e * t ≠ 0)
    (hxy : x + y = 1) :
    restrictedSupport p e H m t x y = H - t * m + m * (x - y) := by
  have h1 := supportDet_sub (p := p) (H := H) (m := m) h
  have h2 := supportConst_add (p := p) (H := H) (m := m) h
  have hy : y = 1 - x := by linarith
  subst hy
  simp only [restrictedSupport]
  linear_combination h2 + (x - (1 - x)) * h1

/-- Homogeneity of the restricted support along the ray through `(x, y)`: at the scale
`s = x + y`, the function `l ↦ l^p q (x/l, y/l)` is the Burkholder-type function with the
supporting line, `s^{p−1} ((H − m t) s + m (x − y))`. -/
theorem restrictedSupport_rpow_eq {p e H m t x y : ℝ} (h : 1 + e * t ≠ 0) (hs : 0 < x + y) :
    supportConst p e H m t * (x + y) ^ p +
        supportMod p e H m t * ((x + y - e * (x - y)) / 2) * (x + y) ^ (p - 1) +
        supportDet p e H m t * (x ^ 2 - y ^ 2) * (x + y) ^ (p - 2) =
      (x + y) ^ (p - 1) * ((H - m * t) * (x + y) + m * (x - y)) := by
  have h1 := supportDet_sub (p := p) (H := H) (m := m) h
  have h2 := supportConst_add (p := p) (H := H) (m := m) h
  have e1 : (x + y) ^ p = (x + y) ^ (p - 1) * (x + y) := by
    rw [← Real.rpow_add_one hs.ne']
    congr 1
    ring
  have e2 : (x + y) ^ (p - 2) * (x + y) = (x + y) ^ (p - 1) := by
    rw [← Real.rpow_add_one hs.ne']
    congr 1
    ring
  have e3 : supportDet p e H m t * (x ^ 2 - y ^ 2) * (x + y) ^ (p - 2) =
      supportDet p e H m t * (x - y) * ((x + y) ^ (p - 2) * (x + y)) := by
    ring
  rw [e3, e2, e1]
  linear_combination ((x + y) ^ (p - 1) * (x + y)) * h2 + ((x + y) ^ (p - 1) * (x - y)) * h1

/-- The relations between the coefficients `c`, `β` of the restricted support for `p < 2` (the
mirror image of `caseOne_relations`): the stationarity relation at the base point, and the two
expressions of `β`. -/
theorem caseTwo_relations {p H m t c β : ℝ} (ht2 : t < 1)
    (hc : c * (1 - t) = (1 + t) * m - p * H) (hβ : β * (1 - t) = 2 * (p * H - 2 * t * m)) :
    β * ((1 + t) / 2) + 2 * c * t = p * H ∧ β + c * (1 + t) = p * H + (1 - t) * m ∧
      p * (c * t - (p - 1) * H) + (p - 1) * β * ((1 + t) / 2) + (p - 2) * c * t = 0 := by
  have h1t : (1 - t) ≠ 0 := by linarith
  have h1 : β * ((1 + t) / 2) + 2 * c * t = p * H := by
    have h : (β * ((1 + t) / 2) + 2 * c * t) * (1 - t) = p * H * (1 - t) := by
      linear_combination ((1 + t) / 2) * hβ + (2 * t) * hc
    exact mul_right_cancel₀ h1t h
  have h2 : β + c * (1 + t) = p * H + (1 - t) * m := by
    have h : (β + c * (1 + t)) * (1 - t) = (p * H + (1 - t) * m) * (1 - t) := by
      linear_combination hβ + (1 + t) * hc
    exact mul_right_cancel₀ h1t h
  exact ⟨h1, h2, by linear_combination (p - 1) * h1⟩

/-- For `p < 2` and `H < 0` the constant term `c t − (p − 1) H` of the restricted support is
negative. -/
theorem caseTwo_const_neg {p H m t c : ℝ} (hp : p < 2) (ht1 : -1 < t) (ht2 : t < 1) (hH : H < 0)
    (hC : 0 ≤ p * H - 2 * t * m) (hc : c * (1 - t) = (1 + t) * m - p * H) :
    c * t - (p - 1) * H < 0 := by
  have e : (c * t - (p - 1) * H) * (2 * (1 - t)) =
      -((1 + t) * (p * H - 2 * t * m) + (p - 2) * (1 - t) * H) := by
    linear_combination (2 * t) * hc
  have h2 : 0 ≤ (1 + t) * (p * H - 2 * t * m) := mul_nonneg (by linarith) hC
  have h3 : 0 < (p - 2) * (1 - t) * H := by
    have := mul_pos (mul_pos (by linarith : 0 < 2 - p) (by linarith : 0 < 1 - t)) (neg_pos.2 hH)
    linarith
  by_contra hcon
  have h4 := mul_nonneg (not_lt.1 hcon) (by linarith : (0 : ℝ) ≤ 2 * (1 - t))
  linarith

/-- For `1 < p < 2` the slope `μ = (p − 1) β/((2 − p) c)` lies in `[0, 2]`. -/
theorem caseTwo_slope_bounds {p H m t c β μ : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ht2 : t < 1)
    (hcpos : 0 < c) (hβ0 : 0 ≤ β) (hneg : p * (H - m * t) + (p - 2) * m < 0)
    (hc : c * (1 - t) = (1 + t) * m - p * H) (hβ : β * (1 - t) = 2 * (p * H - 2 * t * m))
    (hμ : μ * ((2 - p) * c) = (p - 1) * β) : 0 ≤ μ ∧ μ ≤ 2 := by
  have hK : 0 < (2 - p) * c := mul_pos (by linarith) hcpos
  constructor
  · exact nonneg_of_mul_nonneg_left (by rw [hμ]; exact mul_nonneg (by linarith) hβ0) hK
  · have h : (2 - μ) * ((2 - p) * c * (1 - t)) = -2 * (p * (H - m * t) + (p - 2) * m) := by
      linear_combination (2 * (2 - p)) * hc - (1 - t) * hμ - (p - 1) * hβ
    have h2 : 0 ≤ 2 - μ :=
      nonneg_of_mul_nonneg_left (by rw [h]; linarith) (mul_pos hK (by linarith))
    linarith

/-! ### Two facts about `ψ (l) = a l^p + b l^{p−1} + d l^{p−2}` -/

/-- For `1 < p < 2`, `a < 0` and `d < 0`, the function
`ψ (l) = a l^p + b l^{p−1} + d l^{p−2}` tends to `−∞` at `0` and at `∞`, so that it has a
maximizer `l > 0`, a critical point with `ψ (l) ≥ ψ (1)`; the critical points are the positive
roots of `p a l² + (p − 1) b l + (p − 2) d`. -/
theorem exists_stationary_ge_of_lt_two {p a b d : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (ha : a < 0)
    (hd : d < 0) :
    ∃ l : ℝ, 0 < l ∧ p * a * l ^ 2 + (p - 1) * b * l + (p - 2) * d = 0 ∧
      a + b + d ≤ a * l ^ p + b * l ^ (p - 1) + d * l ^ (p - 2) := by
  set ψ : ℝ → ℝ := fun l => a * l ^ p + b * l ^ (p - 1) + d * l ^ (p - 2) with hψ
  have hψ1 : ψ 1 = a + b + d := by simp [hψ]
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |a + b + d| + 1 := ⟨_, rfl⟩
  have hK1 : -K < ψ 1 := by
    rw [hψ1, hK]
    linarith [neg_abs_le (a + b + d)]
  have hK0 : 0 < K := by rw [hK]; positivity
  -- a point `Λ ≥ 1` with `ψ (Λ) ≤ −K`
  set Λ : ℝ := max 1 ((b + K) / (-a)) with hΛ
  have hΛ1 : 1 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := by linarith
  have hΛ2 : b + K ≤ Λ * (-a) := by
    have := le_max_right 1 ((b + K) / (-a))
    rwa [div_le_iff₀ (by linarith)] at this
  have hψΛ : ψ Λ ≤ -K := by
    have e1 : Λ ^ p = Λ ^ (p - 1) * Λ := by
      rw [← Real.rpow_add_one hΛpos.ne']
      congr 1
      ring
    have h1 : 1 ≤ Λ ^ (p - 1) := Real.one_le_rpow hΛ1 (by linarith)
    have h2 : 0 ≤ Λ ^ (p - 2) := Real.rpow_nonneg hΛpos.le _
    have h3 : d * Λ ^ (p - 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd.le h2
    have h4 : Λ ^ (p - 1) * (a * Λ + b) ≤ -K := by
      have h5 : a * Λ + b ≤ -K := by linarith
      nlinarith
    simp only [hψ]
    rw [e1]
    linarith
  -- a point `ε ≤ 1` with `ψ (ε) ≤ −K`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (|b| + K) / (-d) := ⟨_, rfl⟩
  set B : ℝ := max 1 C with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBC : C ≤ B := le_max_right _ _
  set ε : ℝ := B ^ (1 / (p - 2)) with hε
  have hεpos : 0 < ε := Real.rpow_pos_of_pos (by linarith) _
  have hε1 : ε ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hB1 (div_nonpos_of_nonneg_of_nonpos zero_le_one
      (by linarith))
  have hεB : ε ^ (p - 2) = B := by
    rw [hε, ← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ (by linarith : p - 2 ≠ 0),
      Real.rpow_one]
  have hψε : ψ ε ≤ -K := by
    have h1 : a * ε ^ p ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ha.le (Real.rpow_nonneg hεpos.le _)
    have h2 : ε ^ (p - 1) ≤ 1 := Real.rpow_le_one hεpos.le hε1 (by linarith)
    have h2' : 0 ≤ ε ^ (p - 1) := Real.rpow_nonneg hεpos.le _
    have h3 : b * ε ^ (p - 1) ≤ |b| := by
      have := mul_le_mul_of_nonneg_right (le_abs_self b) h2'
      nlinarith [abs_nonneg b]
    have h4 : d * B ≤ -(|b| + K) := by
      have h5 : d * B ≤ d * C := mul_le_mul_of_nonpos_left hBC hd.le
      have h6 : d * C = -(|b| + K) := by
        have hd0 : d ≠ 0 := hd.ne
        rw [hC]
        field_simp
      linarith
    simp only [hψ]
    rw [hεB]
    linarith
  have hcont : ContinuousOn ψ (Icc ε Λ) := by
    intro l hl
    have hl0 : l ≠ 0 := (lt_of_lt_of_le hεpos hl.1).ne'
    exact (((continuousAt_const.mul (Real.continuousAt_rpow_const l p (Or.inl hl0))).add
      (continuousAt_const.mul (Real.continuousAt_rpow_const l (p - 1) (Or.inl hl0)))).add
      (continuousAt_const.mul
        (Real.continuousAt_rpow_const l (p - 2) (Or.inl hl0)))).continuousWithinAt
  obtain ⟨l, hl, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (hε1.trans hΛ1)) hcont
  have h1 : ψ 1 ≤ ψ l := hmax ⟨hε1, hΛ1⟩
  have hlε : l ≠ ε := by
    rintro rfl
    linarith
  have hlΛ : l ≠ Λ := by
    rintro rfl
    linarith
  have hεl : ε < l := lt_of_le_of_ne hl.1 (Ne.symm hlε)
  have hlt : l < Λ := lt_of_le_of_ne hl.2 hlΛ
  have hlpos : 0 < l := hεpos.trans hεl
  have hloc : IsLocalMax ψ l := hmax.isLocalMax (Icc_mem_nhds hεl hlt)
  have hder : HasDerivAt ψ (a * (p * l ^ (p - 1)) + b * ((p - 1) * l ^ (p - 1 - 1)) +
      d * ((p - 2) * l ^ (p - 2 - 1))) l :=
    (((Real.hasDerivAt_rpow_const (p := p) (Or.inl hlpos.ne')).const_mul a).add
      ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hlpos.ne')).const_mul b)).add
      ((Real.hasDerivAt_rpow_const (p := p - 2) (Or.inl hlpos.ne')).const_mul d)
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
  have h6 : l ^ (p - 3) * (p * a * l ^ 2 + (p - 1) * b * l + (p - 2) * d) = 0 := by
    linear_combination hzero
  exact (mul_eq_zero.1 h6).resolve_left hpos3.ne'

/-- If `p a l² + (p − 1) b l + (p − 2) d ≤ 0` for `l ∈ [s, 1]`, `s > 0`, then
`ψ (l) = a l^p + b l^{p−1} + d l^{p−2}` is nonincreasing on `[s, 1]`, so that
`ψ (1) ≤ ψ (s)`. -/
theorem add_add_le_of_forall_quadratic_nonpos {p a b d s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (h : ∀ l : ℝ, s ≤ l → l ≤ 1 → p * a * l ^ 2 + (p - 1) * b * l + (p - 2) * d ≤ 0) :
    a + b + d ≤ a * s ^ p + b * s ^ (p - 1) + d * s ^ (p - 2) := by
  set ψ : ℝ → ℝ := fun l => a * l ^ p + b * l ^ (p - 1) + d * l ^ (p - 2) with hψ
  have hder : ∀ l : ℝ, 0 < l →
      HasDerivAt ψ (l ^ (p - 3) * (p * a * l ^ 2 + (p - 1) * b * l + (p - 2) * d)) l := by
    intro l hl
    have h1 : HasDerivAt ψ (a * (p * l ^ (p - 1)) + b * ((p - 1) * l ^ (p - 1 - 1)) +
        d * ((p - 2) * l ^ (p - 2 - 1))) l :=
      (((Real.hasDerivAt_rpow_const (p := p) (Or.inl hl.ne')).const_mul a).add
        ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hl.ne')).const_mul b)).add
        ((Real.hasDerivAt_rpow_const (p := p - 2) (Or.inl hl.ne')).const_mul d)
    have e1 : l ^ (p - 1) = l ^ (p - 3) * l ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hl]
      congr 1
      push_cast
      ring
    have e2 : l ^ (p - 1 - 1) = l ^ (p - 3) * l := by
      rw [← Real.rpow_add_one hl.ne']
      congr 1
      ring
    have e3 : l ^ (p - 2 - 1) = l ^ (p - 3) := by
      congr 1
      ring
    rw [e1, e2, e3] at h1
    convert h1 using 1
    ring
  have hanti : AntitoneOn ψ (Icc s 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s 1)
      (fun l hl => (hder l (hs.trans_le hl.1)).continuousAt.continuousWithinAt) (fun l hl => ?_)
      (fun l hl => ?_)
    · rw [interior_Icc] at hl
      exact (hder l (hs.trans hl.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hl
      rw [(hder l (hs.trans hl.1)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hs.trans hl.1).le _)
        (h l hl.1.le hl.2.le)
  have h1 := hanti ⟨le_rfl, hs1⟩ ⟨hs1, le_rfl⟩ hs1
  simpa [hψ] using h1

namespace IsProfile

/-- Case I at one point. Let a Burkholder-type minorant with slope `m` touch the profile `Φ` of
degree `p > 2` at `((1 + t)/2, (1 − t)/2)` with value `H > 0`, and let
`p (H − m t) − (p − 2) m < 0`. With the coefficients `c`, `γ` of Case I,
`c t − (p − 1) H + γ y + c (x² − y²) ≤ Φ (x, y)` at every point of the quadrant where
`Φ (x, y) ≥ 0`: the proof of `IsProfile.support_of_neg_aux`, which uses the sign of `Φ` at the
point `(x, y)` only. -/
theorem support_of_neg_of_nonneg (hΦ : IsProfile p Φ) (hp : 2 < p) {H m t c γ : ℝ}
    (ht : |t| < 1) (hmin : BurkholderMinorant p (H - m * t) m Φ)
    (heq : Φ ((1 + t) / 2) ((1 - t) / 2) = H) (hH : 0 < H)
    (hneg : p * (H - m * t) - (p - 2) * m < 0) (hc : c * (1 + t) = p * H + (1 - t) * m)
    (hγ : γ * (1 + t) = 2 * (p * H - 2 * t * m)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h0 : 0 ≤ Φ x y) : c * t - (p - 1) * H + γ * y + c * (x ^ 2 - y ^ 2) ≤ Φ x y := by
  obtain ⟨ht1, ht2⟩ := abs_lt.1 ht
  have h1t : 0 < 1 + t := by linarith
  have hC : 0 ≤ p * H - 2 * t * m := hΦ.baker_ericksen ht hmin heq
  have hm : 0 < m := caseOne_slope_pos hp ht1 hC hneg
  have hΦx : 0 < p * H + (1 - t) * m :=
    add_pos (mul_pos (by linarith) hH) (mul_pos (by linarith) hm)
  have hcpos : 0 < c := pos_of_mul_pos_left (by rw [hc]; exact hΦx) h1t.le
  have ha_neg : c * t - (p - 1) * H < 0 := caseOne_const_neg hp ht1 ht2 hH hC hc
  by_cases hψ1 : c * t - (p - 1) * H + γ * y + c * (x ^ 2 - y ^ 2) ≤ 0
  · exact hψ1.trans h0
  obtain ⟨l, hl, hstat, hge⟩ := exists_stationary_ge (a := c * t - (p - 1) * H) (b := γ * y)
    (e := c * (x ^ 2 - y ^ 2)) hp ha_neg (not_le.1 hψ1)
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ * ((p - 2) * c) = -((p - 1) * γ) :=
    ⟨-((p - 1) * γ) / ((p - 2) * c), by
      have : (p - 2) * c ≠ 0 := (mul_pos (by linarith) hcpos).ne'
      field_simp⟩
  obtain ⟨hμ1, hμ2⟩ := caseOne_slope_bounds hp ht1 hH hm hC hneg hcpos hc hγ hμ
  have hstat' : p * (c * t - (p - 1) * H) + (p - 1) * γ * (y / l) +
      (p - 2) * c * ((x / l) ^ 2 - (y / l) ^ 2) = 0 := by
    have h3 : (p * (c * t - (p - 1) * H) + (p - 1) * γ * (y / l) +
        (p - 2) * c * ((x / l) ^ 2 - (y / l) ^ 2)) * l ^ 2 = 0 := by
      field_simp
      linarith [hstat]
    exact (mul_eq_zero.1 h3).resolve_right (by positivity)
  have hline := hΦ.support_of_stationary hp ht hmin heq hcpos hc hγ hμ hμ1 hμ2
    (div_nonneg hx hl.le) (div_nonneg hy hl.le) hstat'
  have hhom : Φ x y = l ^ p * Φ (x / l) (y / l) := by
    have h := hΦ.homog l (x / l) (y / l) hl (div_nonneg hx hl.le) (div_nonneg hy hl.le)
    rwa [mul_div_cancel₀ _ hl.ne', mul_div_cancel₀ _ hl.ne'] at h
  have e1 : l ^ (p - 1) = l ^ p / l := Real.rpow_sub_one hl.ne' p
  have e2 : l ^ (p - 2) = l ^ p / l ^ 2 := by
    rw [Real.rpow_sub hl, Real.rpow_two]
  have hlp : 0 < l ^ p := Real.rpow_pos_of_pos hl p
  calc c * t - (p - 1) * H + γ * y + c * (x ^ 2 - y ^ 2)
      ≤ (c * t - (p - 1) * H) * l ^ p + γ * y * l ^ (p - 1) +
          c * (x ^ 2 - y ^ 2) * l ^ (p - 2) := hge
    _ = l ^ p * (c * t - (p - 1) * H + γ * (y / l) + c * ((x / l) ^ 2 - (y / l) ^ 2)) := by
        rw [e1, e2]
        field_simp
    _ ≤ l ^ p * Φ (x / l) (y / l) := mul_le_mul_of_nonneg_left hline hlp.le
    _ = Φ x y := hhom.symm

/-- The support inequality on the curve of stationary points, for `p < 2`. Let a Burkholder-type
minorant with slope `m` touch `Φ` at `((1 + t)/2, (1 − t)/2)` with value `H`, let
`c (1 − t) = (1 + t) m − p H`, `c > 0`, `β (1 − t) = 2 (p H − 2 t m)`, and let
`μ = (p − 1) β/((2 − p) c)` lie in `[2 t, 2]`. If `(X, Y)` satisfies the stationarity relation
`p (c t − (p − 1) H) + (p − 1) β X + (p − 2) c (X² − Y²) = 0`, then it is the image of a point of
the rank-one line `τ ↦ (x₀ + τ, y₀ + τ e^{iθ})`, `cos θ = (1 + t − μ)/(1 − t)`, and the
first-order inequality along that line is
`c t − (p − 1) H + β X + c (X² − Y²) ≤ Φ (X, Y)`. -/
theorem support_of_stationary_of_lt_two (hΦ : IsProfile p Φ) (hp : p < 2) {H m t c β μ : ℝ}
    (ht : |t| < 1) (hmin : BurkholderMinorant p (H - m * t) m Φ)
    (heq : Φ ((1 + t) / 2) ((1 - t) / 2) = H) (hcpos : 0 < c)
    (hc : c * (1 - t) = (1 + t) * m - p * H) (hβ : β * (1 - t) = 2 * (p * H - 2 * t * m))
    (hμ : μ * ((2 - p) * c) = (p - 1) * β) (hμ1 : 2 * t ≤ μ) (hμ2 : μ ≤ 2) {X Y : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hstat : p * (c * t - (p - 1) * H) + (p - 1) * β * X + (p - 2) * c * (X ^ 2 - Y ^ 2) = 0) :
    c * t - (p - 1) * H + β * X + c * (X ^ 2 - Y ^ 2) ≤ Φ X Y := by
  obtain ⟨ht1, ht2⟩ := abs_lt.1 ht
  have h1t : 0 < 1 - t := by linarith
  have hpc : (2 - p) * c ≠ 0 := (mul_pos (by linarith) hcpos).ne'
  obtain ⟨r1, r2, r3⟩ := caseTwo_relations (p := p) ht2 hc hβ
  -- the direction of the rank-one line
  obtain ⟨cosθ, hcos_eq⟩ : ∃ cosθ : ℝ, cosθ * (1 - t) = 1 + t - μ :=
    ⟨(1 + t - μ) / (1 - t), by field_simp⟩
  have hcos1 : -1 ≤ cosθ := by
    have h : 0 ≤ (cosθ + 1) * (1 - t) := by linarith
    linarith [nonneg_of_mul_nonneg_left h h1t]
  have hcos2 : cosθ ≤ 1 := by
    have h : 0 ≤ (1 - cosθ) * (1 - t) := by linarith
    linarith [nonneg_of_mul_nonneg_left h h1t]
  have hsin : 0 ≤ 1 - cosθ ^ 2 := by nlinarith
  obtain ⟨u, hu_re, hu_im⟩ : ∃ u : ℂ, u.re = cosθ ∧ u.im = √(1 - cosθ ^ 2) :=
    ⟨⟨cosθ, √(1 - cosθ ^ 2)⟩, rfl, rfl⟩
  have hnu : ‖u‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply, hu_re, hu_im, Real.mul_self_sqrt hsin]
    rw [show cosθ * cosθ + (1 - cosθ ^ 2) = 1 by ring, Real.sqrt_one]
  -- `(X, Y)` is on the image of the line
  have hd : X ^ 2 - Y ^ 2 = t + μ * (X - (1 + t) / 2) := by
    have h4 : (2 - p) * c * (X ^ 2 - Y ^ 2 - (t + μ * (X - (1 + t) / 2))) = 0 := by
      linear_combination -hstat + r3 - (X - (1 + t) / 2) * hμ
    have h5 := (mul_eq_zero.1 h4).resolve_left hpc
    linarith
  have hnx : ‖(((1 + t) / 2 : ℝ) : ℂ) + ((X - (1 + t) / 2 : ℝ) : ℂ) * 1‖ = X := by
    have h2 : (((1 + t) / 2 : ℝ) : ℂ) + ((X - (1 + t) / 2 : ℝ) : ℂ) * 1 = ((X : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX]
  have hny : ‖(((1 - t) / 2 : ℝ) : ℂ) + ((X - (1 + t) / 2 : ℝ) : ℂ) * u‖ = Y := by
    rw [norm_ofReal_add_mul]
    have h2 : ((1 - t) / 2 + (X - (1 + t) / 2) * u.re) ^ 2 + ((X - (1 + t) / 2) * u.im) ^ 2 =
        Y ^ 2 := by
      rw [hu_re, hu_im, mul_pow, Real.sq_sqrt hsin]
      linear_combination (X - (1 + t) / 2) * hcos_eq + hd
    rw [h2, Real.sqrt_sq hY]
  have htan := hΦ.tangent ht hmin heq (α := 1) (β := u) (by rw [hnu, norm_one])
    (X - (1 + t) / 2)
  rw [hnx, hny, hu_re, Complex.one_re] at htan
  have hslope : H + (X - (1 + t) / 2) *
      ((p * H + (1 - t) * m) * 1 + (p * H - (1 + t) * m) * cosθ) =
      c * t - (p - 1) * H + β * X + c * (X ^ 2 - Y ^ 2) := by
    linear_combination -r1 - (X - (1 + t) / 2) * r2 - (X - (1 + t) / 2) * c * hcos_eq +
      (X - (1 + t) / 2) * cosθ * hc - c * hd
  rw [hslope] at htan
  exact htan

/-- The restricted support for `1 < p < 2`, in terms of coefficients `c`, `β` given by their
defining relations. Let a Burkholder-type minorant with slope `m > 0` touch the profile `Φ` at
`((1 + t)/2, (1 − t)/2)`, `−1 < t ≤ 0`, with value `H < 0`, and let
`p (H − m t) + (p − 2) m < 0`. Then
`c t − (p − 1) H + β x + c (x² − y²) ≤ Φ (x, y)` at the points of the quadrant with `x < y`: the
function `l ↦ l^p q (x/l, y/l)` has a maximizer, which is a stationary point. -/
theorem support_of_lt (hΦ : IsProfile p Φ) (hp1 : 1 < p) (hp2 : p < 2) {H m t c β : ℝ}
    (ht : |t| < 1) (hmin : BurkholderMinorant p (H - m * t) m Φ)
    (heq : Φ ((1 + t) / 2) ((1 - t) / 2) = H) (hH : H < 0) (hm : 0 < m) (ht0 : t ≤ 0)
    (hneg : p * (H - m * t) + (p - 2) * m < 0) (hc : c * (1 - t) = (1 + t) * m - p * H)
    (hβ : β * (1 - t) = 2 * (p * H - 2 * t * m)) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    c * t - (p - 1) * H + β * x + c * (x ^ 2 - y ^ 2) ≤ Φ x y := by
  obtain ⟨ht1, ht2⟩ := abs_lt.1 ht
  have h1t : 0 < 1 - t := by linarith
  have hy : 0 ≤ y := hx.trans hxy.le
  have hC : 0 ≤ p * H - 2 * t * m := hΦ.baker_ericksen ht hmin heq
  have hcpos : 0 < c := by
    refine pos_of_mul_pos_left (b := 1 - t) ?_ h1t.le
    rw [hc]
    nlinarith [mul_pos (by linarith : 0 < 1 + t) hm, mul_pos (by linarith : 0 < p) (neg_pos.2 hH)]
  have hβ0 : 0 ≤ β := nonneg_of_mul_nonneg_left (by rw [hβ]; linarith) h1t
  have ha_neg : c * t - (p - 1) * H < 0 := caseTwo_const_neg hp2 ht1 ht2 hH hC hc
  have hd : c * (x ^ 2 - y ^ 2) < 0 := by
    have : x ^ 2 < y ^ 2 := by nlinarith
    nlinarith
  obtain ⟨l, hl, hstat, hge⟩ := exists_stationary_ge_of_lt_two (a := c * t - (p - 1) * H)
    (b := β * x) hp1 hp2 ha_neg hd
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ * ((2 - p) * c) = (p - 1) * β :=
    ⟨(p - 1) * β / ((2 - p) * c), by
      have : (2 - p) * c ≠ 0 := (mul_pos (by linarith) hcpos).ne'
      field_simp⟩
  obtain ⟨hμ0, hμ2⟩ := caseTwo_slope_bounds hp1 hp2 ht2 hcpos hβ0 hneg hc hβ hμ
  have hstat' : p * (c * t - (p - 1) * H) + (p - 1) * β * (x / l) +
      (p - 2) * c * ((x / l) ^ 2 - (y / l) ^ 2) = 0 := by
    have h3 : (p * (c * t - (p - 1) * H) + (p - 1) * β * (x / l) +
        (p - 2) * c * ((x / l) ^ 2 - (y / l) ^ 2)) * l ^ 2 = 0 := by
      field_simp
      linarith [hstat]
    exact (mul_eq_zero.1 h3).resolve_right (by positivity)
  have hline := hΦ.support_of_stationary_of_lt_two hp2 ht hmin heq hcpos hc hβ hμ
    (by linarith) hμ2 (div_nonneg hx hl.le) (div_nonneg hy hl.le) hstat'
  have hhom : Φ x y = l ^ p * Φ (x / l) (y / l) := by
    have h := hΦ.homog l (x / l) (y / l) hl (div_nonneg hx hl.le) (div_nonneg hy hl.le)
    rwa [mul_div_cancel₀ _ hl.ne', mul_div_cancel₀ _ hl.ne'] at h
  have e1 : l ^ (p - 1) = l ^ p / l := Real.rpow_sub_one hl.ne' p
  have e2 : l ^ (p - 2) = l ^ p / l ^ 2 := by
    rw [Real.rpow_sub hl, Real.rpow_two]
  have hlp : 0 < l ^ p := Real.rpow_pos_of_pos hl p
  calc c * t - (p - 1) * H + β * x + c * (x ^ 2 - y ^ 2)
      ≤ (c * t - (p - 1) * H) * l ^ p + β * x * l ^ (p - 1) +
          c * (x ^ 2 - y ^ 2) * l ^ (p - 2) := hge
    _ = l ^ p * (c * t - (p - 1) * H + β * (x / l) + c * ((x / l) ^ 2 - (y / l) ^ 2)) := by
        rw [e1, e2]
        field_simp
    _ ≤ l ^ p * Φ (x / l) (y / l) := mul_le_mul_of_nonneg_left hline hlp.le
    _ = Φ x y := hhom.symm

end IsProfile

namespace IsHardBase

variable {t m : ℝ}

/-- The determinant coefficient of the restricted support at a hard base is positive. -/
theorem supportDet_pos (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) (hor : slice Φ (-1) < 0) (hb : IsHardBase p e Φ t m) :
    0 < supportDet p e (slice Φ t) m t := by
  have h1 := hb.one_add_pos he
  have hm := hb.slope_pos hΦ hp hor
  have hH := hb.e_mul_slice_pos hΦ hp he hpe hor
  obtain ⟨ht1, ht2⟩ := _root_.abs_lt.1 hb.abs_lt
  have h2 : 0 < 1 - e * t := by rcases he with rfl | rfl <;> linarith
  have h3 : e * p * slice Φ t = p * (e * slice Φ t) := by ring
  rw [supportDet, h3]
  exact div_pos (add_pos (mul_pos (by linarith) hH) (mul_pos h2 hm)) h1

/-- The coefficient of the modulus in the restricted support at a hard base is nonnegative. -/
theorem supportMod_nonneg (hΦ : IsProfile p Φ) (he : e = 1 ∨ e = -1)
    (hb : IsHardBase p e Φ t m) : 0 ≤ supportMod p e (slice Φ t) m t := by
  rw [supportMod]
  exact div_nonneg (mul_nonneg zero_le_two (hb.baker_ericksen hΦ)) (hb.one_add_pos he).le

/-- The constant of the restricted support at a hard base is negative. -/
theorem supportConst_neg (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) (hor : slice Φ (-1) < 0) (hb : IsHardBase p e Φ t m) :
    supportConst p e (slice Φ t) m t < 0 := by
  have h1 := hb.one_add_pos he
  have hH := hb.e_mul_slice_pos hΦ hp he hpe hor
  have hC := hb.baker_ericksen hΦ
  have hc := supportDet_mul (p := p) (H := slice Φ t) (m := m) h1.ne'
  obtain ⟨ht1, ht2⟩ := _root_.abs_lt.1 hb.abs_lt
  rw [supportConst]
  rcases he with rfl | rfl
  · exact caseOne_const_neg (by linarith) ht1 ht2 (by linarith) hC (by linarith)
  · exact caseTwo_const_neg (by linarith) ht1 ht2 (by linarith) hC (by linarith)

/-- **Restricted support, `1 < p < 2`.** At a hard base, `q ≤ Φ` at the points of the quadrant
with `x < y` (negative determinant). -/
theorem restrictedSupport_le_of_lt (hΦ : IsProfile p Φ) (hp1 : 1 < p) (hp2 : p < 2)
    (hor : slice Φ (-1) < 0) (hb : IsHardBase p (-1) Φ t m) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x < y) : restrictedSupport p (-1) (slice Φ t) m t x y ≤ Φ x y := by
  have he : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  have hpe : (0 : ℝ) < -1 * (p - 2) := by linarith
  have h1 := hb.one_add_pos he
  have hm := hb.slope_pos hΦ hp1 hor
  have hH := hb.e_mul_slice_pos hΦ hp1 he hpe hor
  have hbase := hb.base_pos hΦ hp1 he hpe
  have hneg := hb.neg
  have hc := supportDet_mul (p := p) (H := slice Φ t) (m := m) h1.ne'
  have hβ := supportMod_mul (p := p) (H := slice Φ t) (m := m) h1.ne'
  have ht0 : t ≤ 0 := by
    by_contra hcon
    have := mul_pos (by linarith : 0 < p) (not_le.1 hcon)
    linarith
  have h := hΦ.support_of_lt hp1 hp2 hb.abs_lt hb.minorant rfl (by linarith) hm ht0
    (by linarith) (c := supportDet p (-1) (slice Φ t) m t)
    (β := supportMod p (-1) (slice Φ t) m t) (by linarith) (by linarith) hx hxy
  have hq : restrictedSupport p (-1) (slice Φ t) m t x y =
      supportDet p (-1) (slice Φ t) m t * t - (p - 1) * slice Φ t +
        supportMod p (-1) (slice Φ t) m t * x +
        supportDet p (-1) (slice Φ t) m t * (x ^ 2 - y ^ 2) := by
    simp only [restrictedSupport, supportConst]
    ring
  rw [hq]
  exact h

/-- **Restricted support, `p > 2`.** At a hard base, `q ≤ Φ` at the points of the quadrant where
`Φ ≥ 0`. -/
theorem restrictedSupport_le_of_nonneg (hΦ : IsProfile p Φ) (hp : 2 < p)
    (hor : slice Φ (-1) < 0) (hb : IsHardBase p 1 Φ t m) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h0 : 0 ≤ Φ x y) : restrictedSupport p 1 (slice Φ t) m t x y ≤ Φ x y := by
  have he : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have hpe : (0 : ℝ) < 1 * (p - 2) := by linarith
  have hp1 : 1 < p := by linarith
  have h1 := hb.one_add_pos he
  have hH := hb.e_mul_slice_pos hΦ hp1 he hpe hor
  have hneg := hb.neg
  have hc := supportDet_mul (p := p) (H := slice Φ t) (m := m) h1.ne'
  have hγ := supportMod_mul (p := p) (H := slice Φ t) (m := m) h1.ne'
  have h := hΦ.support_of_neg_of_nonneg hp hb.abs_lt hb.minorant rfl (by linarith)
    (by linarith) (c := supportDet p 1 (slice Φ t) m t)
    (γ := supportMod p 1 (slice Φ t) m t) (by linarith) (by linarith) hx hy h0
  have hq : restrictedSupport p 1 (slice Φ t) m t x y =
      supportDet p 1 (slice Φ t) m t * t - (p - 1) * slice Φ t +
        supportMod p 1 (slice Φ t) m t * y +
        supportDet p 1 (slice Φ t) m t * (x ^ 2 - y ^ 2) := by
    simp only [restrictedSupport, supportConst]
    ring
  rw [hq]
  exact h

/-- If the polynomial `p α l² + (p − 1) v r l + (p − 2) c (x² − y²)`, whose sign is that of the
derivative of `l ↦ l^p q (x/l, y/l)`, is nonpositive on `[x + y, 1]`, then `q ≤ Φ` at
`(x, y)`: at `l = x + y` that function is the value of the Burkholder-type minorant. -/
theorem restrictedSupport_le_of_forall_le (hb : IsHardBase p e Φ t m) (h1 : 1 + e * t ≠ 0)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : 0 < x + y) (hs1 : x + y ≤ 1)
    (h : ∀ l : ℝ, x + y ≤ l → l ≤ 1 →
      p * supportConst p e (slice Φ t) m t * l ^ 2 +
        (p - 1) * (supportMod p e (slice Φ t) m t * ((x + y - e * (x - y)) / 2)) * l +
        (p - 2) * (supportDet p e (slice Φ t) m t * (x ^ 2 - y ^ 2)) ≤ 0) :
    restrictedSupport p e (slice Φ t) m t x y ≤ Φ x y := by
  have h2 := add_add_le_of_forall_quadratic_nonpos hs hs1 h
  rw [restrictedSupport_rpow_eq h1 hs] at h2
  exact h2.trans (hb.minorant x y hx hy)

/-- The restricted support on the unit ball for `1 < p < 2`: where `x < y` by
`restrictedSupport_le_of_lt`, and where `y ≤ x` because `l ↦ l^p q (x/l, y/l)` is nonincreasing
on `[x + y, 1]`. -/
theorem restrictedSupport_le_of_add_le_one_of_lt_two (hΦ : IsProfile p Φ) (hp1 : 1 < p)
    (hp2 : p < 2) (hor : slice Φ (-1) < 0) (hb : IsHardBase p (-1) Φ t m) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    restrictedSupport p (-1) (slice Φ t) m t x y ≤ Φ x y := by
  rcases lt_or_ge x y with hlt | hge
  · exact hb.restrictedSupport_le_of_lt hΦ hp1 hp2 hor hx hlt
  have he : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  have hpe : (0 : ℝ) < -1 * (p - 2) := by linarith
  have h1 := hb.one_add_pos he
  have hα := hb.supportConst_neg hΦ hp1 he hpe hor
  rcases (add_nonneg hx hy).eq_or_lt with h0 | hs
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    rw [hx0, hy0, hΦ.zero_zero (by linarith)]
    simp only [restrictedSupport]
    linarith
  have hbase := hb.base_pos hΦ hp1 he hpe
  have hneg := hb.neg
  obtain ⟨ht1, ht2⟩ := _root_.abs_lt.1 hb.abs_lt
  have hcpos := hb.supportDet_pos hΦ hp1 he hpe hor
  have hβ0 := hb.supportMod_nonneg hΦ he
  have hc := supportDet_mul (p := p) (H := slice Φ t) (m := m) h1.ne'
  have hβ := supportMod_mul (p := p) (H := slice Φ t) (m := m) h1.ne'
  have ht0 : t ≤ 0 := by
    by_contra hcon
    have := mul_pos (by linarith : 0 < p) (not_le.1 hcon)
    linarith
  refine hb.restrictedSupport_le_of_forall_le h1.ne' hx hy hs hxy fun l hl hl1 => ?_
  rw [supportConst]
  generalize supportDet p (-1) (slice Φ t) m t = c at hc hcpos ⊢
  generalize supportMod p (-1) (slice Φ t) m t = β at hβ hβ0 ⊢
  have hc' : c * (1 - t) = (1 + t) * m - p * slice Φ t := by linarith
  have hβ' : β * (1 - t) = 2 * (p * slice Φ t - 2 * t * m) := by linarith
  obtain ⟨-, -, r3⟩ := caseTwo_relations (p := p) ht2 hc' hβ'
  have hK : 0 < (2 - p) * c := mul_pos (by linarith) hcpos
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ * ((2 - p) * c) = (p - 1) * β :=
    ⟨(p - 1) * β / ((2 - p) * c), by
      have := hK.ne'
      field_simp⟩
  obtain ⟨hμ0, hμ2⟩ := caseTwo_slope_bounds hp1 hp2 ht2 hcpos hβ0 (by linarith) hc' hβ' hμ
  have hP : p * (c * t - (p - 1) * slice Φ t) * l ^ 2 +
      (p - 1) * (β * ((x + y - -1 * (x - y)) / 2)) * l + (p - 2) * (c * (x ^ 2 - y ^ 2)) =
      (2 - p) * c * ((x + y) * (t * (x + y) - (x - y)) * (1 - μ / 2) +
        (l - (x + y)) * (t * (1 - μ / 2) * (l + (x + y)) + μ / 2 * (x - y - l))) := by
    linear_combination l ^ 2 * r3 - (x * l - (1 + t) / 2 * l ^ 2) * hμ
  rw [hP]
  have hA : (x + y) * (t * (x + y) - (x - y)) * (1 - μ / 2) ≤ 0 := by
    have h2 := mul_nonpos_of_nonpos_of_nonneg ht0 hs.le
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith)) (by linarith)
  have hB : t * (1 - μ / 2) * (l + (x + y)) + μ / 2 * (x - y - l) ≤ 0 := by
    have h2 : t * (1 - μ / 2) * (l + (x + y)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg ht0 (by linarith)) (by linarith)
    have h3 : μ / 2 * (x - y - l) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  have hR := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hl) hB
  exact mul_nonpos_of_nonneg_of_nonpos hK.le (by linarith)

/-- The restricted support on the unit ball for `p > 2`: where `Φ ≥ 0` by
`restrictedSupport_le_of_nonneg`, and where `Φ < 0`, which is on the side `(x − y)/(x + y) < t`
of the base point, because `l ↦ l^p q (x/l, y/l)` is nonincreasing on `[x + y, 1]`. -/
theorem restrictedSupport_le_of_add_le_one_of_two_lt (hΦ : IsProfile p Φ) (hp : 2 < p)
    (hor : slice Φ (-1) < 0) (hb : IsHardBase p 1 Φ t m) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ 1) : restrictedSupport p 1 (slice Φ t) m t x y ≤ Φ x y := by
  by_cases h0 : 0 ≤ Φ x y
  · exact hb.restrictedSupport_le_of_nonneg hΦ hp hor hx hy h0
  have he : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have hpe : (0 : ℝ) < 1 * (p - 2) := by linarith
  have hp1 : 1 < p := by linarith
  have h1 := hb.one_add_pos he
  have hm := hb.slope_pos hΦ hp1 hor
  have hH := hb.e_mul_slice_pos hΦ hp1 he hpe hor
  have hneg := hb.neg
  obtain ⟨ht1, ht2⟩ := _root_.abs_lt.1 hb.abs_lt
  have hcpos := hb.supportDet_pos hΦ hp1 he hpe hor
  have hγ0 := hb.supportMod_nonneg hΦ he
  have hc := supportDet_mul (p := p) (H := slice Φ t) (m := m) h1.ne'
  have hγ := supportMod_mul (p := p) (H := slice Φ t) (m := m) h1.ne'
  -- the point is on the side of the base point where the minorant is negative
  have hmin := hb.minorant x y hx hy
  have hB : (slice Φ t - m * t) * (x + y) + m * (x - y) < 0 := by
    by_contra hcon
    have := mul_nonneg (Real.rpow_nonneg (add_nonneg hx hy) (p - 1)) (not_lt.1 hcon)
    linarith
  have hs : 0 < x + y := by
    rcases (add_nonneg hx hy).eq_or_lt with h | h
    · exfalso
      have hx0 : x = 0 := by linarith
      have hy0 : y = 0 := by linarith
      rw [hx0, hy0] at hB
      simp at hB
    · exact h
  have hδ : x - y ≤ t * (x + y) := by
    by_contra hcon
    have h2 := mul_pos hm (by linarith : 0 < x - y - t * (x + y))
    have h3 := mul_pos (by linarith : 0 < slice Φ t) hs
    linarith
  refine hb.restrictedSupport_le_of_forall_le h1.ne' hx hy hs hxy fun l hl hl1 => ?_
  rw [supportConst]
  generalize supportDet p 1 (slice Φ t) m t = c at hc hcpos ⊢
  generalize supportMod p 1 (slice Φ t) m t = γ at hγ hγ0 ⊢
  have hc' : c * (1 + t) = p * slice Φ t + (1 - t) * m := by linarith
  have hγ' : γ * (1 + t) = 2 * (p * slice Φ t - 2 * t * m) := by linarith
  obtain ⟨r1, -, r3⟩ := caseOne_relations (p := p) ht1 hc' hγ'
  have hK : 0 < 2 * ((p - 2) * c) := by
    have := mul_pos (by linarith : 0 < p - 2) hcpos
    linarith
  obtain ⟨b, hb'⟩ : ∃ b : ℝ, b * (2 * ((p - 2) * c)) = (p - 1) * γ :=
    ⟨(p - 1) * γ / (2 * ((p - 2) * c)), by
      have := hK.ne'
      field_simp⟩
  have hb0 : 0 ≤ b :=
    nonneg_of_mul_nonneg_left (by rw [hb']; exact mul_nonneg (by linarith) hγ0) hK
  have hb1 : b ≤ 1 := by
    have h : (1 - b) * (2 * ((p - 2) * c) * (1 + t)) =
        -2 * (p * (slice Φ t - m * t) - (p - 2) * m) := by
      linear_combination (2 * (p - 2)) * hc' - (p - 1) * hγ' - (1 + t) * hb'
    have h2 : 0 ≤ 1 - b :=
      nonneg_of_mul_nonneg_left (by rw [h]; linarith) (mul_pos hK (by linarith))
    linarith
  have hk : 0 < b * (1 - t) + 2 * t := by
    have e : c * ((p - 2) * b * (1 - t) + 2 * (p - 1) * t) = (p - 1) * (p * slice Φ t) := by
      linear_combination (p - 1) * r1 + ((1 - t) / 2) * hb'
    have h2 : 0 < (p - 2) * b * (1 - t) + 2 * (p - 1) * t := by
      refine pos_of_mul_pos_right (a := c) ?_ hcpos.le
      rw [e]
      exact mul_pos (by linarith) (mul_pos (by linarith) (by linarith))
    have h3 : 0 ≤ b * (1 - t) := mul_nonneg hb0 (by linarith)
    by_contra hcon
    have h4 := mul_nonneg (by linarith : (0 : ℝ) ≤ p - 1)
      (by linarith [not_lt.1 hcon] : 0 ≤ -(b * (1 - t) + 2 * t))
    linarith
  have hbt : 0 ≤ b + t := by
    rcases le_or_gt 0 t with h | h
    · linarith
    · by_contra hcon
      have h3 := mul_pos (by linarith : 0 < -(b + t)) (by linarith : 0 < 1 - t)
      have h4 := mul_pos (neg_pos.2 h) (by linarith : 0 < 1 + t)
      linarith
  have hk0 : 0 ≤ b * (1 - t) + t := by
    rcases le_or_gt t 0 with h | h
    · linarith
    · have := mul_nonneg hb0 (by linarith : (0 : ℝ) ≤ 1 - t)
      linarith
  have hP : p * (c * t - (p - 1) * slice Φ t) * l ^ 2 +
      (p - 1) * (γ * ((x + y - 1 * (x - y)) / 2)) * l + (p - 2) * (c * (x ^ 2 - y ^ 2)) =
      (p - 2) * c * (-(b * (1 - t) + t) * l ^ 2 + 2 * b * y * l + (x ^ 2 - y ^ 2)) := by
    linear_combination l ^ 2 * r3 - (y * l - (1 - t) / 2 * l ^ 2) * hb'
  rw [hP]
  have hR : (1 + t) * (x + y) * (-(b * (1 - t) + t) * l ^ 2 + 2 * b * y * l + (x ^ 2 - y ^ 2)) =
      (t * (x + y) - (x - y)) * (-((1 - b) * (b + t)) * l ^ 2 - (b * l - (x + y)) ^ 2) +
        2 * x * ((l - (x + y)) * (-(b * (1 - t) + t) * l - t * (x + y))) := by
    ring
  have hT1 : (t * (x + y) - (x - y)) * (-((1 - b) * (b + t)) * l ^ 2 - (b * l - (x + y)) ^ 2) ≤
      0 := by
    refine mul_nonpos_of_nonneg_of_nonpos (by linarith) ?_
    have h2 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - b) hbt) (sq_nonneg l)
    have h3 := sq_nonneg (b * l - (x + y))
    linarith
  have hT2 : 2 * x * ((l - (x + y)) * (-(b * (1 - t) + t) * l - t * (x + y))) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos (by linarith) ?_
    refine mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hl) ?_
    have h2 := mul_le_mul_of_nonneg_left hl hk0
    have h3 := mul_pos hk hs
    linarith
  have hR0 : -(b * (1 - t) + t) * l ^ 2 + 2 * b * y * l + (x ^ 2 - y ^ 2) ≤ 0 := by
    have h2 : 0 < (1 + t) * (x + y) := mul_pos (by linarith) hs
    by_contra hcon
    have h3 := mul_pos h2 (not_le.1 hcon)
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos (mul_pos (by linarith) hcpos).le hR0

/-- **Restricted support on the unit ball.** At a hard base, `q ≤ Φ` at the points of the
quadrant with `x + y ≤ 1`. -/
theorem restrictedSupport_le_of_add_le_one (hΦ : IsProfile p Φ) (hp : 1 < p)
    (he : e = 1 ∨ e = -1) (hpe : 0 < e * (p - 2)) (hor : slice Φ (-1) < 0)
    (hb : IsHardBase p e Φ t m) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    restrictedSupport p e (slice Φ t) m t x y ≤ Φ x y := by
  rcases he with rfl | rfl
  · exact hb.restrictedSupport_le_of_add_le_one_of_two_lt hΦ (by linarith) hor hx hy hxy
  · exact hb.restrictedSupport_le_of_add_le_one_of_lt_two hΦ hp (by linarith) hor hx hy hxy

/-- The restricted support of a hard base at a positive multiple of the base point of another
hard base lies below `Φ` there: that point has `x < y` if `p < 2`, and `Φ > 0` there if
`p > 2`. -/
theorem restrictedSupport_smul_base_le (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) (hor : slice Φ (-1) < 0) {t₁ m₁ t₂ m₂ S : ℝ}
    (h₁ : IsHardBase p e Φ t₁ m₁) (h₂ : IsHardBase p e Φ t₂ m₂) (hS : 0 < S) :
    restrictedSupport p e (slice Φ t₁) m₁ t₁ (S * ((1 + t₂) / 2)) (S * ((1 - t₂) / 2)) ≤
      S ^ p * slice Φ t₂ := by
  obtain ⟨ht1, ht2⟩ := _root_.abs_lt.1 h₂.abs_lt
  have hH := h₂.e_mul_slice_pos hΦ hp he hpe hor
  have hbase := h₂.base_pos hΦ hp he hpe
  have hhom : Φ (S * ((1 + t₂) / 2)) (S * ((1 - t₂) / 2)) = S ^ p * slice Φ t₂ :=
    hΦ.homog S _ _ hS (by linarith) (by linarith)
  have hx : 0 ≤ S * ((1 + t₂) / 2) := mul_nonneg hS.le (by linarith)
  have hy : 0 ≤ S * ((1 - t₂) / 2) := mul_nonneg hS.le (by linarith)
  rw [← hhom]
  rcases he with rfl | rfl
  · refine h₁.restrictedSupport_le_of_nonneg hΦ (by linarith) hor hx hy ?_
    rw [hhom]
    exact mul_nonneg (Real.rpow_nonneg hS.le p) (by linarith)
  · refine h₁.restrictedSupport_le_of_lt hΦ hp (by linarith) hor hx ?_
    have ht0 : t₂ < 0 := by
      by_contra hcon
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ p) (not_lt.1 hcon)
      linarith
    exact mul_lt_mul_of_pos_left (by linarith) hS

/-- The scaled restricted support `S₁^p α₁ + S₁^{p−1} v₁ r + S₁^{p−2} c₁ (x² − y²)` of a hard
base lies below `Φ` at the scaled base point of another hard base, where `Φ` is `S₂^p h (t₂)`. -/
theorem scaled_le (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) (hor : slice Φ (-1) < 0) {t₁ m₁ t₂ m₂ S₁ S₂ : ℝ}
    (h₁ : IsHardBase p e Φ t₁ m₁) (h₂ : IsHardBase p e Φ t₂ m₂) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) :
    S₁ ^ p * supportConst p e (slice Φ t₁) m₁ t₁ +
        S₁ ^ (p - 1) * supportMod p e (slice Φ t₁) m₁ t₁ * (S₂ * (1 - e * t₂) / 2) +
        S₁ ^ (p - 2) * supportDet p e (slice Φ t₁) m₁ t₁ * (S₂ ^ 2 * t₂) ≤
      S₂ ^ p * slice Φ t₂ := by
  have h := restrictedSupport_smul_base_le hΦ hp he hpe hor h₁ h₂ (div_pos hS₂ hS₁)
  have h' := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hS₁.le p)
  have hne : S₁ ≠ 0 := hS₁.ne'
  have hpos : 0 < S₁ ^ p := Real.rpow_pos_of_pos hS₁ p
  have e1 : S₁ ^ (p - 1) = S₁ ^ p / S₁ := Real.rpow_sub_one hS₁.ne' p
  have e2 : S₁ ^ (p - 2) = S₁ ^ p / S₁ ^ 2 := by
    rw [Real.rpow_sub hS₁, Real.rpow_two]
  have e3 : S₁ ^ p * ((S₂ / S₁) ^ p * slice Φ t₂) = S₂ ^ p * slice Φ t₂ := by
    rw [Real.div_rpow hS₂.le hS₁.le]
    field_simp
  have e4 : S₁ ^ p * restrictedSupport p e (slice Φ t₁) m₁ t₁ (S₂ / S₁ * ((1 + t₂) / 2))
      (S₂ / S₁ * ((1 - t₂) / 2)) =
      S₁ ^ p * supportConst p e (slice Φ t₁) m₁ t₁ +
        S₁ ^ (p - 1) * supportMod p e (slice Φ t₁) m₁ t₁ * (S₂ * (1 - e * t₂) / 2) +
        S₁ ^ (p - 2) * supportDet p e (slice Φ t₁) m₁ t₁ * (S₂ ^ 2 * t₂) := by
    simp only [restrictedSupport]
    rw [e1, e2]
    field_simp
    ring
  rw [e3, e4] at h'
  exact h'

/-- The scaled restricted support of a hard base equals `Φ` at its scaled base point. -/
theorem scaled_eq (he : e = 1 ∨ e = -1) (hb : IsHardBase p e Φ t m) {S : ℝ} (hS : 0 < S) :
    S ^ p * supportConst p e (slice Φ t) m t +
        S ^ (p - 1) * supportMod p e (slice Φ t) m t * (S * (1 - e * t) / 2) +
        S ^ (p - 2) * supportDet p e (slice Φ t) m t * (S ^ 2 * t) =
      S ^ p * slice Φ t := by
  have h := restrictedSupport_base (p := p) (H := slice Φ t) (m := m) (hb.one_add_pos he).ne'
  simp only [restrictedSupport] at h
  have e1 : S ^ (p - 1) * S = S ^ p := by
    rw [← Real.rpow_add_one hS.ne']
    congr 1
    ring
  have e2 : S ^ (p - 2) * S ^ 2 = S ^ p := by
    rw [← Real.rpow_natCast S 2, ← Real.rpow_add hS]
    congr 1
    push_cast
    ring
  have key : S ^ p * supportConst p e (slice Φ t) m t +
      S ^ (p - 1) * supportMod p e (slice Φ t) m t * (S * (1 - e * t) / 2) +
      S ^ (p - 2) * supportDet p e (slice Φ t) m t * (S ^ 2 * t) =
      S ^ p * supportConst p e (slice Φ t) m t +
        S ^ (p - 1) * S * (supportMod p e (slice Φ t) m t * ((1 - e * t) / 2)) +
        S ^ (p - 2) * S ^ 2 * (supportDet p e (slice Φ t) m t * t) := by
    ring
  rw [key, e1, e2]
  linear_combination S ^ p * h

/-- **Monotonicity of the supporting planes.** For two hard bases `(t₁, m₁)`, `(t₂, m₂)` and
scales `S₁, S₂ > 0`, the scaled restricted supports
`Sᵢ^p αᵢ + Sᵢ^{p−1} vᵢ r + Sᵢ^{p−2} cᵢ (x² − y²)` touch `Φ` at the scaled base points
`(rᵢ, dᵢ) = (Sᵢ (1 − e tᵢ)/2, Sᵢ² tᵢ)` and each lies below `Φ` at the base point of the other;
adding the two inequalities,
`(V₂ − V₁) (r₂ − r₁) + (C₂ − C₁) (d₂ − d₁) ≥ 0`. -/
theorem scaled_monotone (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) (hor : slice Φ (-1) < 0) {t₁ m₁ t₂ m₂ S₁ S₂ : ℝ}
    (h₁ : IsHardBase p e Φ t₁ m₁) (h₂ : IsHardBase p e Φ t₂ m₂) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) :
    0 ≤ (S₂ ^ (p - 1) * supportMod p e (slice Φ t₂) m₂ t₂ -
          S₁ ^ (p - 1) * supportMod p e (slice Φ t₁) m₁ t₁) *
        (S₂ * (1 - e * t₂) / 2 - S₁ * (1 - e * t₁) / 2) +
      (S₂ ^ (p - 2) * supportDet p e (slice Φ t₂) m₂ t₂ -
          S₁ ^ (p - 2) * supportDet p e (slice Φ t₁) m₁ t₁) *
        (S₂ ^ 2 * t₂ - S₁ ^ 2 * t₁) := by
  have i1 := scaled_le hΦ hp he hpe hor h₁ h₂ hS₁ hS₂
  have i2 := scaled_le hΦ hp he hpe hor h₂ h₁ hS₂ hS₁
  have e1 := scaled_eq he h₁ hS₁
  have e2 := scaled_eq he h₂ hS₂
  linarith

end IsHardBase

end HomogeneousIsotropic
