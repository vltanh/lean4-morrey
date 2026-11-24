module

public import Morrey.HomogeneousIsotropic.LowExponent

/-!
# Polyaffine supports of a nonnegative profile, `p ≥ 2`

Let `Φ ≥ 0` be a profile of degree `p ≥ 2`. A function `k + b x + g y + c (x² − y²)` with
`b, g ≥ 0` that lies below `Φ` on the quadrant and touches it at `(x₀, y₀)` is the profile form of
a polyaffine support `k + b Re z + g Re w + c det A`. This file builds one at every `(x₀, y₀)`.

At `(x₀, y₀) = ((1 + t)/2, (1 − t)/2)`, `|t| < 1`, let `H = Φ (x₀, y₀) > 0` and let a
Burkholder-type minorant with slope `m` touch `Φ` there (`m` is the slope of a supporting line of
the slice). With `c₀ = H − m t`:

* `BurkholderMinorant.support` (Case III, `(p − 2) |m| ≤ p c₀`): the support has
  `c = (p − 1) m`; it lies below the minorant.
* `IsProfile.support_of_neg` (Case I, `p c₀ − (p − 2) m < 0`): the support has
  `c = (p H + (1 − t) m)/(1 + t)` and `b = 0`; one first-order inequality along one rank-one
  line gives it.
* `IsProfile.support_of_neg_aux'` (Case II, `p c₀ + (p − 2) m < 0`): the mirror image, `g = 0`.
* `IsProfile.support_multiplier`: in all three cases `c = multiplier p H m t`, the value
  `(p − 1) m` clamped to `[L, U]`, `L = ((1 + t) m − p H)/(1 − t)`,
  `U = (p H + (1 − t) m)/(1 + t)`.
* `IsProfile.support_one_zero`: the support `Φ (1, 0) (1 + (p/2) (x² − y² − 1))` at `(1, 0)`.
* `IsProfile.exists_support`: a support at every point of the quadrant.
* `IsProfile.exists_support_two`: the same for `p = 2` and a profile of any sign.
-/

@[expose] public section

open Set

namespace HomogeneousIsotropic

/-- Case III. If `(p − 2) |m| ≤ p c₀`, a Burkholder-type minorant of a nonnegative `Φ` has the
polyaffine minorant
`−(p − 1) c₀ + (p c₀ − (p − 2) m) x + (p c₀ + (p − 2) m) y + (p − 1) m (x² − y²)`. -/
theorem BurkholderMinorant.support {p c₀ m : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hmin : BurkholderMinorant p c₀ m Φ) (hΦ0 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Φ x y)
    (hp : 2 ≤ p) (hc : (p - 2) * |m| ≤ p * c₀) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    -(p - 1) * c₀ + (p * c₀ - (p - 2) * m) * x + (p * c₀ + (p - 2) * m) * y +
      (p - 1) * m * (x ^ 2 - y ^ 2) ≤ Φ x y := by
  have hδ : |x - y| ≤ x + y := by
    rw [abs_le]
    constructor <;> linarith
  have h := burkholder_support_le hp hc (add_nonneg hx hy) hδ
  have h2 : max 0 ((x + y) ^ (p - 1) * (c₀ * (x + y) + m * (x - y))) ≤ Φ x y :=
    max_le (hΦ0 x y hx hy) (hmin x y hx hy)
  calc -(p - 1) * c₀ + (p * c₀ - (p - 2) * m) * x + (p * c₀ + (p - 2) * m) * y +
        (p - 1) * m * (x ^ 2 - y ^ 2)
      = -(p - 1) * c₀ + p * c₀ * (x + y) - (p - 2) * m * (x - y) +
        (p - 1) * m * (x + y) * (x - y) := by ring
    _ ≤ Φ x y := h.trans h2

/-- For `p = 2` no sign condition is needed: a Burkholder-type minorant with `c₀ ≥ 0` has the
polyaffine minorant `−c₀ + 2 c₀ (x + y) + m (x² − y²)`. -/
theorem BurkholderMinorant.support_two {c₀ m : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hmin : BurkholderMinorant 2 c₀ m Φ) (hc : 0 ≤ c₀) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    -c₀ + 2 * c₀ * x + 2 * c₀ * y + m * (x ^ 2 - y ^ 2) ≤ Φ x y := by
  have h := hmin x y hx hy
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at h
  nlinarith [mul_nonneg hc (sq_nonneg (x + y - 1))]

/-! ### The algebra of Case I -/

/-- In Case I the slope of the supporting line is positive. -/
theorem caseOne_slope_pos {p H m t : ℝ} (hp : 2 < p) (ht1 : -1 < t)
    (hC : 0 ≤ p * H - 2 * t * m) (hneg : p * (H - m * t) - (p - 2) * m < 0) : 0 < m := by
  by_contra hcon
  have hm' : 0 ≤ -m := by linarith [not_lt.1 hcon]
  have h := mul_nonneg (mul_nonneg hm' (sub_nonneg.2 hp.le)) (by linarith : (0 : ℝ) ≤ 1 + t)
  linarith

/-- In Case I the constant term `c t − (p − 1) H` of the support is negative. -/
theorem caseOne_const_neg {p H m t c : ℝ} (hp : 2 < p) (ht1 : -1 < t) (ht2 : t < 1) (hH : 0 < H)
    (hC : 0 ≤ p * H - 2 * t * m) (hc : c * (1 + t) = p * H + (1 - t) * m) :
    c * t - (p - 1) * H < 0 := by
  have e : (c * t - (p - 1) * H) * ((1 + t) * 2) =
      -((1 - t) * (p * H - 2 * t * m) + (p - 2) * (1 + t) * H) := by
    linear_combination (2 * t) * hc
  have h2 : 0 ≤ (1 - t) * (p * H - 2 * t * m) := mul_nonneg (by linarith) hC
  have h3 : 0 < (p - 2) * (1 + t) * H := mul_pos (mul_pos (by linarith) (by linarith)) hH
  by_contra hcon
  have h4 := mul_nonneg (not_lt.1 hcon) (by linarith : (0 : ℝ) ≤ (1 + t) * 2)
  linarith

/-- The relations between the coefficients `c`, `γ` of the support of Case I: the stationarity
relation at the base point, and the two expressions of `γ`. -/
theorem caseOne_relations {p H m t c γ : ℝ} (ht1 : -1 < t)
    (hc : c * (1 + t) = p * H + (1 - t) * m) (hγ : γ * (1 + t) = 2 * (p * H - 2 * t * m)) :
    γ * ((1 - t) / 2) + 2 * c * t = p * H ∧ c * (1 - t) + (p * H - (1 + t) * m) = γ ∧
      p * (c * t - (p - 1) * H) + (p - 1) * γ * ((1 - t) / 2) + (p - 2) * c * t = 0 := by
  have h1t : (1 + t) ≠ 0 := by linarith
  have h1 : γ * ((1 - t) / 2) + 2 * c * t = p * H := by
    have h : (γ * ((1 - t) / 2) + 2 * c * t) * (1 + t) = p * H * (1 + t) := by
      linear_combination ((1 - t) / 2) * hγ + (2 * t) * hc
    exact mul_right_cancel₀ h1t h
  have h2 : c * (1 - t) + (p * H - (1 + t) * m) = γ := by
    have h : (c * (1 - t) + (p * H - (1 + t) * m)) * (1 + t) = γ * (1 + t) := by
      linear_combination (1 - t) * hc - hγ
    exact mul_right_cancel₀ h1t h
  exact ⟨h1, h2, by linear_combination (p - 1) * h1⟩

/-- In Case I the slope `μ = −(p − 1) γ / ((p − 2) c)` lies in `[−2, 2 t]`: the line of
stationary points is the image of a rank-one line. -/
theorem caseOne_slope_bounds {p H m t c γ μ : ℝ} (hp : 2 < p) (ht1 : -1 < t) (hH : 0 < H)
    (hm : 0 < m) (hC : 0 ≤ p * H - 2 * t * m) (hneg : p * (H - m * t) - (p - 2) * m < 0)
    (hcpos : 0 < c) (hc : c * (1 + t) = p * H + (1 - t) * m)
    (hγ : γ * (1 + t) = 2 * (p * H - 2 * t * m)) (hμ : μ * ((p - 2) * c) = -((p - 1) * γ)) :
    -2 ≤ μ ∧ μ ≤ 2 * t := by
  have h1t : 0 < 1 + t := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hK : 0 < (p - 2) * c * (1 + t) := mul_pos (mul_pos hp2 hcpos) h1t
  have hΦx : 0 < p * H + (1 - t) * m := by rw [← hc]; exact mul_pos hcpos h1t
  constructor
  · have h : (μ + 2) * ((p - 2) * c * (1 + t)) = -2 * (p * (H - m * t) - (p - 2) * m) := by
      linear_combination (1 + t) * hμ - (p - 1) * hγ + 2 * (p - 2) * hc
    have h2 : 0 ≤ μ + 2 := nonneg_of_mul_nonneg_left (by rw [h]; linarith) hK
    linarith
  · have hN : 0 ≤ t * (p - 2) * (p * H + (1 - t) * m) + (p - 1) * (p * H - 2 * t * m) := by
      rcases le_or_gt 0 t with h | h
      · exact add_nonneg (mul_nonneg (mul_nonneg h hp2.le) hΦx.le)
          (mul_nonneg (by linarith) hC)
      · have e : t * (p - 2) * (p * H + (1 - t) * m) + (p - 1) * (p * H - 2 * t * m) =
            p * H * ((p - 1) + (p - 2) * t) + -t * m * (p + (p - 2) * t) := by ring
        rw [e]
        have h0 := mul_pos hp2 h1t
        have h3 : 0 < (p - 1) + (p - 2) * t := by linarith
        have h4 : 0 < p + (p - 2) * t := by linarith
        exact (add_pos (mul_pos (mul_pos (by linarith) hH) h3)
          (mul_pos (mul_pos (neg_pos.2 h) hm) h4)).le
    have h : (2 * t - μ) * ((p - 2) * c * (1 + t)) =
        2 * (t * (p - 2) * (p * H + (1 - t) * m) + (p - 1) * (p * H - 2 * t * m)) := by
      linear_combination -(1 + t) * hμ + (p - 1) * hγ + 2 * t * (p - 2) * hc
    have h2 : 0 ≤ 2 * t - μ := nonneg_of_mul_nonneg_left (by rw [h]; linarith) hK
    linarith

namespace IsProfile

variable {p : ℝ} {Φ : ℝ → ℝ → ℝ}

/-- The support inequality of Case I on the curve of stationary points. Let a Burkholder-type
minorant with slope `m` touch `Φ` at `((1 + t)/2, (1 − t)/2)` with value `H`, let `c > 0` and `γ`
be the coefficients of Case I, and `μ ∈ [−2, 2 t]` the slope. If `(X, Y)` satisfies the
stationarity relation `p (c t − (p − 1) H) + (p − 1) γ Y + (p − 2) c (X² − Y²) = 0`, then it is
the image of a point of the rank-one line `τ ↦ (x₀ + τ e^{iθ}, y₀ + τ)`, `cos θ = (μ + 1 − t) /
(1 + t)`, and the first-order inequality along that line is
`c t − (p − 1) H + γ Y + c (X² − Y²) ≤ Φ (X, Y)`. -/
theorem support_of_stationary (hΦ : IsProfile p Φ) (hp : 2 < p) {H m t c γ μ : ℝ} (ht : |t| < 1)
    (hmin : BurkholderMinorant p (H - m * t) m Φ) (heq : Φ ((1 + t) / 2) ((1 - t) / 2) = H)
    (hcpos : 0 < c) (hc : c * (1 + t) = p * H + (1 - t) * m)
    (hγ : γ * (1 + t) = 2 * (p * H - 2 * t * m)) (hμ : μ * ((p - 2) * c) = -((p - 1) * γ))
    (hμ1 : -2 ≤ μ) (hμ2 : μ ≤ 2 * t) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hstat : p * (c * t - (p - 1) * H) + (p - 1) * γ * Y + (p - 2) * c * (X ^ 2 - Y ^ 2) = 0) :
    c * t - (p - 1) * H + γ * Y + c * (X ^ 2 - Y ^ 2) ≤ Φ X Y := by
  obtain ⟨ht1, ht2⟩ := abs_lt.1 ht
  have h1t : 0 < 1 + t := by linarith
  have hpc : (p - 2) * c ≠ 0 := (mul_pos (by linarith) hcpos).ne'
  obtain ⟨h1, h3, h53⟩ := caseOne_relations (p := p) ht1 hc hγ
  -- the direction of the rank-one line
  obtain ⟨cosθ, hcos_eq⟩ : ∃ cosθ : ℝ, cosθ * (1 + t) = μ + 1 - t :=
    ⟨(μ + 1 - t) / (1 + t), by field_simp⟩
  have hcos1 : -1 ≤ cosθ := by
    have h : 0 ≤ (cosθ + 1) * (1 + t) := by linarith
    linarith [nonneg_of_mul_nonneg_left h h1t]
  have hcos2 : cosθ ≤ 1 := by
    have h : 0 ≤ (1 - cosθ) * (1 + t) := by linarith
    linarith [nonneg_of_mul_nonneg_left h h1t]
  have hsin : 0 ≤ 1 - cosθ ^ 2 := by nlinarith
  obtain ⟨e, he_re, he_im⟩ : ∃ e : ℂ, e.re = cosθ ∧ e.im = √(1 - cosθ ^ 2) :=
    ⟨⟨cosθ, √(1 - cosθ ^ 2)⟩, rfl, rfl⟩
  have hne : ‖e‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply, he_re, he_im, Real.mul_self_sqrt hsin]
    rw [show cosθ * cosθ + (1 - cosθ ^ 2) = 1 by ring, Real.sqrt_one]
  -- `(X, Y)` is on the image of the line
  have hd : X ^ 2 - Y ^ 2 = t + μ * (Y - (1 - t) / 2) := by
    have h4 : (p - 2) * c * (X ^ 2 - Y ^ 2 - (t + μ * (Y - (1 - t) / 2))) = 0 := by
      linear_combination hstat - h53 - (Y - (1 - t) / 2) * hμ
    have h5 := (mul_eq_zero.1 h4).resolve_left hpc
    linarith
  have hny : ‖(((1 - t) / 2 : ℝ) : ℂ) + ((Y - (1 - t) / 2 : ℝ) : ℂ) * 1‖ = Y := by
    have h2 : (((1 - t) / 2 : ℝ) : ℂ) + ((Y - (1 - t) / 2 : ℝ) : ℂ) * 1 = ((Y : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hY]
  have hnx : ‖(((1 + t) / 2 : ℝ) : ℂ) + ((Y - (1 - t) / 2 : ℝ) : ℂ) * e‖ = X := by
    rw [norm_ofReal_add_mul]
    have h2 : ((1 + t) / 2 + (Y - (1 - t) / 2) * e.re) ^ 2 + ((Y - (1 - t) / 2) * e.im) ^ 2 =
        X ^ 2 := by
      rw [he_re, he_im, mul_pow, Real.sq_sqrt hsin]
      linear_combination (Y - (1 - t) / 2) * hcos_eq - hd
    rw [h2, Real.sqrt_sq hX]
  have htan := hΦ.tangent ht hmin heq (α := e) (β := 1) (by rw [hne, norm_one])
    (Y - (1 - t) / 2)
  rw [hnx, hny, he_re, Complex.one_re] at htan
  have h2 : (p * H + (1 - t) * m) * cosθ = c * (μ + 1 - t) := by
    rw [← hc, ← hcos_eq]
    ring
  have hslope : H + (Y - (1 - t) / 2) *
      ((p * H + (1 - t) * m) * cosθ + (p * H - (1 + t) * m) * 1) =
      c * t - (p - 1) * H + γ * Y + c * (X ^ 2 - Y ^ 2) := by
    rw [hd]
    linear_combination (Y - (1 - t) / 2) * h2 + (Y - (1 - t) / 2) * h3 - h1
  rw [hslope] at htan
  exact htan

/-- Case I, in terms of coefficients `c`, `γ` given by their defining relations. -/
theorem support_of_neg_aux (hΦ : IsProfile p Φ) (hΦ0 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Φ x y)
    (hp : 2 < p) {H m t c γ : ℝ} (ht : |t| < 1) (hmin : BurkholderMinorant p (H - m * t) m Φ)
    (heq : Φ ((1 + t) / 2) ((1 - t) / 2) = H) (hH : 0 < H)
    (hneg : p * (H - m * t) - (p - 2) * m < 0) (hc : c * (1 + t) = p * H + (1 - t) * m)
    (hγ : γ * (1 + t) = 2 * (p * H - 2 * t * m)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    c * t - (p - 1) * H + γ * y + c * (x ^ 2 - y ^ 2) ≤ Φ x y := by
  obtain ⟨ht1, ht2⟩ := abs_lt.1 ht
  have h1t : 0 < 1 + t := by linarith
  have hC : 0 ≤ p * H - 2 * t * m := hΦ.baker_ericksen ht hmin heq
  have hm : 0 < m := caseOne_slope_pos hp ht1 hC hneg
  have hΦx : 0 < p * H + (1 - t) * m :=
    add_pos (mul_pos (by linarith) hH) (mul_pos (by linarith) hm)
  have hcpos : 0 < c := pos_of_mul_pos_left (by rw [hc]; exact hΦx) h1t.le
  have ha_neg : c * t - (p - 1) * H < 0 := caseOne_const_neg hp ht1 ht2 hH hC hc
  -- the trivial case
  by_cases hψ1 : c * t - (p - 1) * H + γ * y + c * (x ^ 2 - y ^ 2) ≤ 0
  · exact hψ1.trans (hΦ0 x y hx hy)
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
  -- homogeneity
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

/-- Case I. Let a Burkholder-type minorant with slope `m` touch the nonnegative profile `Φ` at
`((1 + t)/2, (1 − t)/2)` with value `H > 0`, and let `p (H − m t) − (p − 2) m < 0`. Then, with
`c = (p H + (1 − t) m)/(1 + t)` and `γ = 2 (p H − 2 t m)/(1 + t)`,
`c t − (p − 1) H + γ y + c (x² − y²) ≤ Φ (x, y)` on the quadrant. -/
theorem support_of_neg (hΦ : IsProfile p Φ) (hΦ0 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Φ x y)
    (hp : 2 < p) {H m t : ℝ} (ht : |t| < 1) (hmin : BurkholderMinorant p (H - m * t) m Φ)
    (heq : Φ ((1 + t) / 2) ((1 - t) / 2) = H) (hH : 0 < H)
    (hneg : p * (H - m * t) - (p - 2) * m < 0) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (p * H + (1 - t) * m) / (1 + t) * t - (p - 1) * H +
      2 * (p * H - 2 * t * m) / (1 + t) * y +
        (p * H + (1 - t) * m) / (1 + t) * (x ^ 2 - y ^ 2) ≤ Φ x y := by
  have h1t : (1 + t) ≠ 0 := by linarith [(abs_lt.1 ht).1]
  exact hΦ.support_of_neg_aux hΦ0 hp ht hmin heq hH hneg (by field_simp) (by field_simp) hx hy

/-- Case II, the mirror image of Case I, in terms of coefficients `c`, `β` given by their
defining relations: if `p (H − m t) + (p − 2) m < 0`, `c (1 − t) = (1 + t) m − p H` and
`β (1 − t) = 2 (p H − 2 t m)`, then `c t − (p − 1) H + β x + c (x² − y²) ≤ Φ (x, y)`. -/
theorem support_of_neg_aux' (hΦ : IsProfile p Φ) (hΦ0 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Φ x y)
    (hp : 2 < p) {H m t c β : ℝ} (ht : |t| < 1) (hmin : BurkholderMinorant p (H - m * t) m Φ)
    (heq : Φ ((1 + t) / 2) ((1 - t) / 2) = H) (hH : 0 < H)
    (hneg : p * (H - m * t) + (p - 2) * m < 0) (hc : c * (1 - t) = (1 + t) * m - p * H)
    (hβ : β * (1 - t) = 2 * (p * H - 2 * t * m)) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    c * t - (p - 1) * H + β * x + c * (x ^ 2 - y ^ 2) ≤ Φ x y := by
  have hmin' : BurkholderMinorant p (H - -m * -t) (-m) fun x y => Φ y x := by
    have h := hmin.swap
    rwa [show H - m * t = H - -m * -t by ring] at h
  have heq' : (fun x y => Φ y x) ((1 + -t) / 2) ((1 - -t) / 2) = H := by
    change Φ ((1 - -t) / 2) ((1 + -t) / 2) = H
    rw [show (1 - -t) / 2 = (1 + t) / 2 by ring, show (1 + -t) / 2 = (1 - t) / 2 by ring]
    exact heq
  have h := hΦ.swap.support_of_neg_aux (c := -c) (γ := β) (fun x y hx hy => hΦ0 y x hy hx) hp
    (t := -t) (by rwa [abs_neg]) hmin' heq' hH (by linarith) (by linarith) (by linarith) hy hx
  linarith

/-- The support with the clamped multiplier. Let a Burkholder-type minorant with slope `m`
touch the nonnegative profile `Φ` of degree `p ≥ 2` at `((1 + t)/2, (1 − t)/2)`, `|t| < 1`, with
value `H > 0`. With `c = multiplier p H m t`, `b = p H + (1 − t) m − (1 + t) c` and
`g = p H − (1 + t) m + (1 − t) c`, one has `b, g ≥ 0` and
`c t − (p − 1) H + b x + g y + c (x² − y²) ≤ Φ (x, y)` on the quadrant. -/
theorem support_multiplier (hΦ : IsProfile p Φ) (hΦ0 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Φ x y)
    (hp : 2 ≤ p) {H m t : ℝ} (ht : |t| < 1) (hmin : BurkholderMinorant p (H - m * t) m Φ)
    (heq : Φ ((1 + t) / 2) ((1 - t) / 2) = H) (hH : 0 < H) :
    0 ≤ p * H + (1 - t) * m - (1 + t) * multiplier p H m t ∧
      0 ≤ p * H - (1 + t) * m + (1 - t) * multiplier p H m t ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        multiplier p H m t * t - (p - 1) * H +
          (p * H + (1 - t) * m - (1 + t) * multiplier p H m t) * x +
          (p * H - (1 + t) * m + (1 - t) * multiplier p H m t) * y +
          multiplier p H m t * (x ^ 2 - y ^ 2) ≤ Φ x y := by
  obtain ⟨ht1, ht2⟩ := abs_lt.1 ht
  have h1t : 0 < 1 + t := by linarith
  have h1t' : 0 < 1 - t := by linarith
  have hC : 0 ≤ p * H - 2 * t * m := hΦ.baker_ericksen ht hmin heq
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = (p * H + (1 - t) * m) / (1 + t) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ((1 + t) * m - p * H) / (1 - t) := ⟨_, rfl⟩
  have hU_eq : U * (1 + t) = p * H + (1 - t) * m := by
    rw [hU]
    field_simp
  have hL_eq : L * (1 - t) = (1 + t) * m - p * H := by
    rw [hL]
    field_simp
  have hmul : multiplier p H m t = min U (max L ((p - 1) * m)) := by
    rw [multiplier, hU, hL]
  have hLU : L ≤ U := by
    have h : 0 ≤ (U - L) * ((1 + t) * (1 - t)) := by
      have e : (U - L) * ((1 + t) * (1 - t)) = 2 * (p * H - 2 * t * m) := by
        linear_combination (1 - t) * hU_eq - (1 + t) * hL_eq
      rw [e]
      linarith
    linarith [nonneg_of_mul_nonneg_left h (mul_pos h1t h1t')]
  by_cases hc3 : (p - 2) * |m| ≤ p * (H - m * t)
  · -- Case III
    have hm1 : (p - 2) * m ≤ p * (H - m * t) :=
      (mul_le_mul_of_nonneg_left (le_abs_self m) (by linarith)).trans hc3
    have hm2 : (p - 2) * -m ≤ p * (H - m * t) :=
      (mul_le_mul_of_nonneg_left (neg_le_abs m) (by linarith)).trans hc3
    have h1 : (p - 1) * m ≤ U := by
      have h : 0 ≤ (U - (p - 1) * m) * (1 + t) := by
        have e : (U - (p - 1) * m) * (1 + t) = p * (H - m * t) - (p - 2) * m := by
          linear_combination hU_eq
        rw [e]
        linarith
      linarith [nonneg_of_mul_nonneg_left h h1t]
    have h2 : L ≤ (p - 1) * m := by
      have h : 0 ≤ ((p - 1) * m - L) * (1 - t) := by
        have e : ((p - 1) * m - L) * (1 - t) = p * (H - m * t) + (p - 2) * m := by
          linear_combination -hL_eq
        rw [e]
        linarith
      linarith [nonneg_of_mul_nonneg_left h h1t']
    have hc : multiplier p H m t = (p - 1) * m := by
      rw [hmul, max_eq_right h2, min_eq_right h1]
    rw [hc]
    refine ⟨by linarith, by linarith, fun x y hx hy => ?_⟩
    have h := hmin.support hΦ0 hp hc3 hx hy
    linarith
  · -- Cases I and II: here `p > 2`
    have hp2 : 2 < p := by
      rcases hp.eq_or_lt with h | h
      · exfalso
        apply hc3
        rw [← h] at hC ⊢
        linarith
      · exact h
    have hc3' : p * (H - m * t) < (p - 2) * |m| := not_le.1 hc3
    rcases le_or_gt 0 m with hm | hm
    · -- Case I
      rw [abs_of_nonneg hm] at hc3'
      have h1 : U ≤ (p - 1) * m := by
        have h : 0 ≤ ((p - 1) * m - U) * (1 + t) := by
          have e : ((p - 1) * m - U) * (1 + t) = -(p * (H - m * t) - (p - 2) * m) := by
            linear_combination -hU_eq
          rw [e]
          linarith
        linarith [nonneg_of_mul_nonneg_left h h1t]
      have hc : multiplier p H m t = U := by
        rw [hmul, min_eq_left (h1.trans (le_max_right _ _))]
      rw [hc]
      have hg : (p * H - (1 + t) * m + (1 - t) * U) * (1 + t) = 2 * (p * H - 2 * t * m) := by
        linear_combination (1 - t) * hU_eq
      have hg0 : 0 ≤ p * H - (1 + t) * m + (1 - t) * U :=
        nonneg_of_mul_nonneg_left (by rw [hg]; linarith) h1t
      refine ⟨by linarith, hg0, fun x y hx hy => ?_⟩
      have h := hΦ.support_of_neg_aux hΦ0 hp2 ht hmin heq hH (by linarith) hU_eq hg hx hy
      have e : (p * H + (1 - t) * m - (1 + t) * U) * x = 0 := by
        rw [show p * H + (1 - t) * m - (1 + t) * U = 0 by linarith, zero_mul]
      linarith
    · -- Case II
      rw [abs_of_neg hm] at hc3'
      have h1 : (p - 1) * m ≤ L := by
        have h : 0 ≤ (L - (p - 1) * m) * (1 - t) := by
          have e : (L - (p - 1) * m) * (1 - t) = -(p * (H - m * t) + (p - 2) * m) := by
            linear_combination hL_eq
          rw [e]
          linarith
        linarith [nonneg_of_mul_nonneg_left h h1t']
      have hc : multiplier p H m t = L := by
        rw [hmul, max_eq_left h1, min_eq_right hLU]
      rw [hc]
      have hb : (p * H + (1 - t) * m - (1 + t) * L) * (1 - t) = 2 * (p * H - 2 * t * m) := by
        linear_combination -(1 + t) * hL_eq
      have hb0 : 0 ≤ p * H + (1 - t) * m - (1 + t) * L :=
        nonneg_of_mul_nonneg_left (by rw [hb]; linarith) h1t'
      refine ⟨hb0, by linarith, fun x y hx hy => ?_⟩
      have h := hΦ.support_of_neg_aux' hΦ0 hp2 ht hmin heq hH (by linarith) hL_eq hb hx hy
      have e : (p * H - (1 + t) * m + (1 - t) * L) * y = 0 := by
        rw [show p * H - (1 + t) * m + (1 - t) * L = 0 by linarith, zero_mul]
      linarith

/-- The support at `(1, 0)`, the profile of the conformal matrices: for `p ≥ 2`,
`Φ (1, 0) (1 + (p/2) (x² − y² − 1)) ≤ Φ (x, y)`. -/
theorem support_one_zero (hΦ : IsProfile p Φ) (hΦ0 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Φ x y)
    (hp : 2 ≤ p) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Φ 1 0 * (1 - p / 2) + p / 2 * Φ 1 0 * (x ^ 2 - y ^ 2) ≤ Φ x y := by
  have h10 : 0 ≤ Φ 1 0 := hΦ0 1 0 zero_le_one le_rfl
  rcases le_or_gt (x ^ 2 - y ^ 2) 0 with hd | hd
  · have h1 : Φ 1 0 * (1 - p / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h10 (by linarith)
    have h2 : p / 2 * Φ 1 0 * (x ^ 2 - y ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) h10) hd
    linarith [hΦ0 x y hx hy]
  · have hr : 0 < √(x ^ 2 - y ^ 2) := Real.sqrt_pos.2 hd
    have hr2 : √(x ^ 2 - y ^ 2) ^ 2 = x ^ 2 - y ^ 2 := Real.sq_sqrt hd.le
    have hxr : √(x ^ 2 - y ^ 2) ≤ x := by
      rw [show x = √(x ^ 2) from (Real.sqrt_sq hx).symm]
      exact Real.sqrt_le_sqrt (by rw [Real.sqrt_sq hx]; nlinarith [sq_nonneg y])
    have h1 : Φ √(x ^ 2 - y ^ 2) 0 ≤ Φ x y :=
      hΦ.le_of_sq_sub_sq_eq hr.le le_rfl hxr hy (by rw [hr2]; ring)
    have h2 : Φ √(x ^ 2 - y ^ 2) 0 = √(x ^ 2 - y ^ 2) ^ p * Φ 1 0 := by
      simpa using hΦ.homog √(x ^ 2 - y ^ 2) 1 0 hr zero_le_one le_rfl
    have h3 : √(x ^ 2 - y ^ 2) ^ p = (x ^ 2 - y ^ 2) ^ (p / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hd.le]
      congr 1
      ring
    have h4 : 1 + p / 2 * (x ^ 2 - y ^ 2 - 1) ≤ (x ^ 2 - y ^ 2) ^ (p / 2) := by
      have h := one_add_mul_self_le_rpow_one_add (s := x ^ 2 - y ^ 2 - 1) (by linarith)
        (p := p / 2) (by linarith)
      rwa [show 1 + (x ^ 2 - y ^ 2 - 1) = x ^ 2 - y ^ 2 by ring] at h
    calc Φ 1 0 * (1 - p / 2) + p / 2 * Φ 1 0 * (x ^ 2 - y ^ 2)
        = (1 + p / 2 * (x ^ 2 - y ^ 2 - 1)) * Φ 1 0 := by ring
      _ ≤ (x ^ 2 - y ^ 2) ^ (p / 2) * Φ 1 0 := mul_le_mul_of_nonneg_right h4 h10
      _ = Φ √(x ^ 2 - y ^ 2) 0 := by rw [h2, h3]
      _ ≤ Φ x y := h1

/-- A support at every point of the segment `x₀ + y₀ = 1` of the quadrant. -/
theorem exists_support_of_add_eq_one (hΦ : IsProfile p Φ)
    (hΦ0 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Φ x y) (hp : 2 ≤ p) {x₀ y₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) (h1 : x₀ + y₀ = 1) :
    ∃ k b g c : ℝ, 0 ≤ b ∧ 0 ≤ g ∧
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → k + b * x + g * y + c * (x ^ 2 - y ^ 2) ≤ Φ x y) ∧
      k + b * x₀ + g * y₀ + c * (x₀ ^ 2 - y₀ ^ 2) = Φ x₀ y₀ := by
  rcases hy₀.eq_or_lt with hy0 | hy0
  · -- the conformal point `(1, 0)`
    have hx1 : x₀ = 1 := by linarith
    subst hx1
    rw [← hy0]
    refine ⟨Φ 1 0 * (1 - p / 2), 0, 0, p / 2 * Φ 1 0, le_rfl, le_rfl, fun x y hx hy => ?_, by ring⟩
    have h := hΦ.support_one_zero hΦ0 hp hx hy
    linarith
  rcases hx₀.eq_or_lt with hx0 | hx0
  · -- the anticonformal point `(0, 1)`
    have hy1 : y₀ = 1 := by linarith
    subst hy1
    rw [← hx0]
    refine ⟨Φ 0 1 * (1 - p / 2), 0, 0, -(p / 2 * Φ 0 1), le_rfl, le_rfl, fun x y hx hy => ?_,
      by ring⟩
    have h := hΦ.swap.support_one_zero (fun x y hx hy => hΦ0 y x hy hx) hp hy hx
    linarith
  -- an interior point
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x₀ - y₀ := ⟨_, rfl⟩
  have hxt : x₀ = (1 + t) / 2 := by rw [ht]; linarith
  have hyt : y₀ = (1 - t) / 2 := by rw [ht]; linarith
  have habs : |t| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rcases (hΦ0 x₀ y₀ hx₀ hy₀).eq_or_lt with hH | hH
  · exact ⟨0, 0, 0, 0, le_rfl, le_rfl, fun x y hx hy => by simpa using hΦ0 x y hx hy,
      by rw [← hH]; ring⟩
  obtain ⟨m, hm⟩ := hΦ.exists_burkholderMinorant (by linarith) (t := t) (by linarith)
    (by linarith)
  rw [← hxt, ← hyt] at hm
  obtain ⟨hb, hg, hle⟩ := hΦ.support_multiplier hΦ0 hp habs hm (by rw [← hxt, ← hyt]) hH
  refine ⟨_, _, _, _, hb, hg, hle, ?_⟩
  rw [hxt, hyt]
  ring

/-- Supports scale: if `Φ` has a support at every point of the segment `x₀ + y₀ = 1`, it has
one at every point of the quadrant other than the origin. -/
theorem exists_support_of_pos (hΦ : IsProfile p Φ)
    (h1 : ∀ x₀ y₀ : ℝ, 0 ≤ x₀ → 0 ≤ y₀ → x₀ + y₀ = 1 → ∃ k b g c : ℝ, 0 ≤ b ∧ 0 ≤ g ∧
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → k + b * x + g * y + c * (x ^ 2 - y ^ 2) ≤ Φ x y) ∧
      k + b * x₀ + g * y₀ + c * (x₀ ^ 2 - y₀ ^ 2) = Φ x₀ y₀)
    {x₀ y₀ : ℝ} (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) (hpos : 0 < x₀ + y₀) :
    ∃ k b g c : ℝ, 0 ≤ b ∧ 0 ≤ g ∧
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → k + b * x + g * y + c * (x ^ 2 - y ^ 2) ≤ Φ x y) ∧
      k + b * x₀ + g * y₀ + c * (x₀ ^ 2 - y₀ ^ 2) = Φ x₀ y₀ := by
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = x₀ + y₀ := ⟨_, rfl⟩
  rw [← hσ] at hpos
  obtain ⟨k, b, g, c, hb, hg, hle, heq⟩ := h1 (x₀ / σ) (y₀ / σ) (div_nonneg hx₀ hpos.le)
    (div_nonneg hy₀ hpos.le) (by rw [← add_div, ← hσ, div_self hpos.ne'])
  have hσp : 0 < σ ^ p := Real.rpow_pos_of_pos hpos p
  have e1 : σ ^ (p - 1) = σ ^ p / σ := Real.rpow_sub_one hpos.ne' p
  have e2 : σ ^ (p - 2) = σ ^ p / σ ^ 2 := by
    rw [Real.rpow_sub hpos, Real.rpow_two]
  have hscale : ∀ x y : ℝ, σ ^ p * k + σ ^ (p - 1) * b * x + σ ^ (p - 1) * g * y +
      σ ^ (p - 2) * c * (x ^ 2 - y ^ 2) =
      σ ^ p * (k + b * (x / σ) + g * (y / σ) + c * ((x / σ) ^ 2 - (y / σ) ^ 2)) := by
    intro x y
    rw [e1, e2]
    field_simp
  have hhom : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → Φ x y = σ ^ p * Φ (x / σ) (y / σ) := by
    intro x y hx hy
    have h := hΦ.homog σ (x / σ) (y / σ) hpos (div_nonneg hx hpos.le) (div_nonneg hy hpos.le)
    rwa [mul_div_cancel₀ _ hpos.ne', mul_div_cancel₀ _ hpos.ne'] at h
  refine ⟨σ ^ p * k, σ ^ (p - 1) * b, σ ^ (p - 1) * g, σ ^ (p - 2) * c,
    mul_nonneg (Real.rpow_nonneg hpos.le _) hb, mul_nonneg (Real.rpow_nonneg hpos.le _) hg,
    fun x y hx hy => ?_, ?_⟩
  · rw [hscale, hhom x y hx hy]
    exact mul_le_mul_of_nonneg_left (hle _ _ (div_nonneg hx hpos.le) (div_nonneg hy hpos.le))
      hσp.le
  · rw [hscale, hhom x₀ y₀ hx₀ hy₀, heq]

/-- **Supports of a nonnegative profile.** Let `Φ ≥ 0` be a profile of degree `p ≥ 2`. At every
point `(x₀, y₀)` of the quadrant there are `k`, `b ≥ 0`, `g ≥ 0`, `c` with
`k + b x + g y + c (x² − y²) ≤ Φ (x, y)` on the quadrant and equality at `(x₀, y₀)`. -/
theorem exists_support (hΦ : IsProfile p Φ) (hΦ0 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Φ x y)
    (hp : 2 ≤ p) {x₀ y₀ : ℝ} (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    ∃ k b g c : ℝ, 0 ≤ b ∧ 0 ≤ g ∧
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → k + b * x + g * y + c * (x ^ 2 - y ^ 2) ≤ Φ x y) ∧
      k + b * x₀ + g * y₀ + c * (x₀ ^ 2 - y₀ ^ 2) = Φ x₀ y₀ := by
  rcases (add_nonneg hx₀ hy₀).eq_or_lt with h0 | hpos
  · have hx0 : x₀ = 0 := by linarith
    have hy0 : y₀ = 0 := by linarith
    subst hx0 hy0
    exact ⟨0, 0, 0, 0, le_rfl, le_rfl, fun x y hx hy => by simpa using hΦ0 x y hx hy,
      by rw [hΦ.zero_zero (by linarith)]; ring⟩
  · exact hΦ.exists_support_of_pos
      (fun x y hx hy h => hΦ.exists_support_of_add_eq_one hΦ0 hp hx hy h) hx₀ hy₀ hpos

/-! ### The exponent `p = 2`, with no sign condition -/

/-- For `p = 2` the profile lies above `Φ (1, 0) (x² − y²)`, with no sign condition. -/
theorem support_two_one_zero (hΦ : IsProfile 2 Φ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Φ 1 0 * (x ^ 2 - y ^ 2) ≤ Φ x y := by
  have hmin : BurkholderMinorant 2 0 (Φ 1 0) Φ := by
    refine hΦ.burkholderMinorant_of_slice two_pos fun s hs1 hs2 => ?_
    have h := hΦ.slice_ge_of_one s
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
    linarith
  have h := hmin.support_two le_rfl hx hy
  linarith

/-- A support at every point of the segment `x₀ + y₀ = 1`, for `p = 2` and a profile of any
sign. -/
theorem exists_support_two_of_add_eq_one (hΦ : IsProfile 2 Φ) {x₀ y₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) (h1 : x₀ + y₀ = 1) :
    ∃ k b g c : ℝ, 0 ≤ b ∧ 0 ≤ g ∧
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → k + b * x + g * y + c * (x ^ 2 - y ^ 2) ≤ Φ x y) ∧
      k + b * x₀ + g * y₀ + c * (x₀ ^ 2 - y₀ ^ 2) = Φ x₀ y₀ := by
  rcases hy₀.eq_or_lt with hy0 | hy0
  · have hx1 : x₀ = 1 := by linarith
    subst hx1
    rw [← hy0]
    refine ⟨0, 0, 0, Φ 1 0, le_rfl, le_rfl, fun x y hx hy => ?_, by ring⟩
    have h := hΦ.support_two_one_zero hx hy
    linarith
  rcases hx₀.eq_or_lt with hx0 | hx0
  · have hy1 : y₀ = 1 := by linarith
    subst hy1
    rw [← hx0]
    refine ⟨0, 0, 0, -Φ 0 1, le_rfl, le_rfl, fun x y hx hy => ?_, by ring⟩
    have h := hΦ.swap.support_two_one_zero hy hx
    linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x₀ - y₀ := ⟨_, rfl⟩
  have hxt : x₀ = (1 + t) / 2 := by rw [ht]; linarith
  have hyt : y₀ = (1 - t) / 2 := by rw [ht]; linarith
  have habs : |t| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  obtain ⟨m, hm⟩ := hΦ.exists_burkholderMinorant two_pos (t := t) (by linarith) (by linarith)
  rw [← hxt, ← hyt] at hm
  have hC := hΦ.baker_ericksen habs hm (by rw [← hxt, ← hyt])
  refine ⟨-(Φ x₀ y₀ - m * t), 2 * (Φ x₀ y₀ - m * t), 2 * (Φ x₀ y₀ - m * t), m, by linarith,
    by linarith, fun x y hx hy => ?_, ?_⟩
  · have h := hm.support_two (by linarith) hx hy
    linarith
  · rw [show x₀ ^ 2 - y₀ ^ 2 = (x₀ - y₀) * (x₀ + y₀) by ring, h1, ← ht]
    linear_combination 2 * (Φ x₀ y₀ - m * t) * h1

/-- **Supports for `p = 2`.** A profile of degree `2`, of any sign, has a support
`k + b x + g y + c (x² − y²)`, `b, g ≥ 0`, at every point of the quadrant. -/
theorem exists_support_two (hΦ : IsProfile 2 Φ) {x₀ y₀ : ℝ} (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    ∃ k b g c : ℝ, 0 ≤ b ∧ 0 ≤ g ∧
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → k + b * x + g * y + c * (x ^ 2 - y ^ 2) ≤ Φ x y) ∧
      k + b * x₀ + g * y₀ + c * (x₀ ^ 2 - y₀ ^ 2) = Φ x₀ y₀ := by
  rcases (add_nonneg hx₀ hy₀).eq_or_lt with h0 | hpos
  · have hx0 : x₀ = 0 := by linarith
    have hy0 : y₀ = 0 := by linarith
    subst hx0 hy0
    refine ⟨0, 0, 0, Φ 1 0, le_rfl, le_rfl, fun x y hx hy => ?_,
      by rw [hΦ.zero_zero two_pos]; ring⟩
    have h := hΦ.support_two_one_zero hx hy
    linarith
  · exact hΦ.exists_support_of_pos
      (fun x y hx hy h => hΦ.exists_support_two_of_add_eq_one hx hy h) hx₀ hy₀ hpos

/-! ### The supports touch at the base point

The supports above are stated as inequalities on the quadrant. Each equals `Φ` at its base point;
these are the equalities. -/

/-- The support of Case III has the value `c₀ + m t` at `((1 + t)/2, (1 − t)/2)`: the value of
the minorant, hence of `Φ`. -/
theorem _root_.HomogeneousIsotropic.support_slice_eq (p c₀ m t : ℝ) :
    -(p - 1) * c₀ + (p * c₀ - (p - 2) * m) * ((1 + t) / 2) +
        (p * c₀ + (p - 2) * m) * ((1 - t) / 2) +
        (p - 1) * m * (((1 + t) / 2) ^ 2 - ((1 - t) / 2) ^ 2) = c₀ + m * t := by
  ring

/-- **Proposition 4.2, the equality.** The support of Case I has the value `H` at
`((1 + t)/2, (1 − t)/2)`. -/
theorem _root_.HomogeneousIsotropic.support_of_neg_eq {p H m t : ℝ} (ht : -1 < t) :
    (p * H + (1 - t) * m) / (1 + t) * t - (p - 1) * H +
        2 * (p * H - 2 * t * m) / (1 + t) * ((1 - t) / 2) +
        (p * H + (1 - t) * m) / (1 + t) * (((1 + t) / 2) ^ 2 - ((1 - t) / 2) ^ 2) = H := by
  have h : (1 + t) ≠ 0 := by linarith
  field_simp
  ring

/-- **Case II, the equality.** The support of Case II has the value `H` at
`((1 + t)/2, (1 − t)/2)`. -/
theorem _root_.HomogeneousIsotropic.support_of_neg_eq' {p H m t c β : ℝ} (ht : t < 1)
    (hc : c * (1 - t) = (1 + t) * m - p * H) (hβ : β * (1 - t) = 2 * (p * H - 2 * t * m)) :
    c * t - (p - 1) * H + β * ((1 + t) / 2) +
        c * (((1 + t) / 2) ^ 2 - ((1 - t) / 2) ^ 2) = H := by
  have h : (1 - t) ≠ 0 := by linarith
  have key : (c * t - (p - 1) * H + β * ((1 + t) / 2) +
      c * (((1 + t) / 2) ^ 2 - ((1 - t) / 2) ^ 2) - H) * (1 - t) = 0 := by
    linear_combination (2 * t) * hc + ((1 + t) / 2) * hβ
  have := mul_eq_zero.1 key
  rcases this with h1 | h1
  · linarith
  · exact absurd h1 h

/-- **Proposition 4.5, the equality.** For every determinant coefficient `c`, the function
tangent to the minorant at `((1 + t)/2, (1 − t)/2)` has the value `H` there; in particular the
support of `support_multiplier` does. -/
theorem _root_.HomogeneousIsotropic.support_multiplier_eq (p H m t c : ℝ) :
    c * t - (p - 1) * H + (p * H + (1 - t) * m - (1 + t) * c) * ((1 + t) / 2) +
        (p * H - (1 + t) * m + (1 - t) * c) * ((1 - t) / 2) +
        c * (((1 + t) / 2) ^ 2 - ((1 - t) / 2) ^ 2) = H := by
  ring

/-- The support at the conformal point has the value `Φ (1, 0)` there. -/
theorem _root_.HomogeneousIsotropic.support_one_zero_eq (p a : ℝ) :
    a * (1 - p / 2) + p / 2 * a * ((1 : ℝ) ^ 2 - (0 : ℝ) ^ 2) = a := by
  ring

/-- **The support at the anticonformal point** (the mirror image of `support_one_zero`):
`Φ (0, 1) (1 + (p/2) (y² − x² − 1)) ≤ Φ (x, y)`; at `(0, 1)` the left side is `Φ (0, 1)`. -/
theorem support_zero_one (hΦ : IsProfile p Φ) (hΦ0 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Φ x y)
    (hp : 2 ≤ p) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Φ 0 1 * (1 - p / 2) + p / 2 * Φ 0 1 * (y ^ 2 - x ^ 2) ≤ Φ x y :=
  hΦ.swap.support_one_zero (fun x y hx hy => hΦ0 y x hy hx) hp hy hx

end IsProfile

end HomogeneousIsotropic
