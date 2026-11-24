module

public import Morrey.HomogeneousIsotropic.Profile

/-!
# Burkholder-type supports of a profile, `1 ≤ p < 2`

Let `Φ ≥ 0` be a profile of degree `p ∈ [1, 2)`. At every point of the quadrant `Φ` has a
touching Burkholder-type minorant `(x + y)^{p−1} (c₀ (x + y) + m (x − y))` with
`(2 − p) |m| ≤ p c₀` (`IsProfile.exists_burkholderMinorant_of_lt_two`), that is, a nonnegative
combination of the Burkholder function and its mirror image.

* `IsProfile.slice_ge_of_one`, `IsProfile.slice_ge_of_neg_one`: the supporting lines of the slice
  at `s = 1` and `s = −1`, with the slopes `(p/2) Φ (1, 0)` and `−(p/2) Φ (0, 1)`, for every
  `p > 0`.
* `IsProfile.nonneg_of_one`: a profile of degree `1` is nonnegative.
-/

@[expose] public section

open Set Filter Topology

namespace HomogeneousIsotropic

namespace IsProfile

variable {p : ℝ} {Φ : ℝ → ℝ → ℝ}

/-- The supporting line of the slice at `s = 1`: `Φ (1, 0) (1 + (p/2) (s − 1))` lies below the
slice. The slice lies above `s ↦ s^{p/2} Φ (1, 0)` near `1`, by the monotonicity along
hyperbolas, and is convex. -/
theorem slice_ge_of_one (hΦ : IsProfile p Φ) (s : ℝ) :
    Φ 1 0 * (1 + p / 2 * (s - 1)) ≤ Φ (|1 + s| / 2) (|1 - s| / 2) := by
  have hle : ∀ᶠ u in 𝓝 (1 : ℝ), u ^ (p / 2) * Φ 1 0 ≤ Φ (|1 + u| / 2) (|1 - u| / 2) := by
    filter_upwards [eventually_gt_nhds (zero_lt_one' ℝ)] with u hu
    have hr : 0 < √u := Real.sqrt_pos.2 hu
    have hr2 : √u ^ 2 = u := Real.sq_sqrt hu.le
    have habs : |1 + u| = 1 + u := abs_of_pos (by linarith)
    have hxr : √u ≤ |1 + u| / 2 := by
      rw [habs, show (1 + u) / 2 = √(((1 + u) / 2) ^ 2) from
        (Real.sqrt_sq (by linarith)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 - u)])
    have h1 : Φ √u 0 ≤ Φ (|1 + u| / 2) (|1 - u| / 2) :=
      hΦ.le_of_sq_sub_sq_eq hr.le le_rfl hxr (by positivity) (by
        rw [hr2, div_pow, div_pow, sq_abs, sq_abs]
        ring)
    have h2 : Φ √u 0 = √u ^ p * Φ 1 0 := by
      simpa using hΦ.homog √u 1 0 hr zero_le_one le_rfl
    have h3 : √u ^ p = u ^ (p / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le]
      congr 1
      ring
    rw [← h3, ← h2]
    exact h1
  have hd : HasDerivAt (fun u : ℝ => u ^ (p / 2) * Φ 1 0) (p / 2 * Φ 1 0) 1 := by
    have h := (Real.hasDerivAt_rpow_const (p := p / 2) (Or.inl (one_ne_zero' ℝ))).mul_const
      (Φ 1 0)
    simpa using h
  have h := hΦ.convexOn_slice.add_mul_le_of_hasDerivAt_le hle (by norm_num) hd s
  norm_num at h
  linarith

/-- The supporting line of the slice at `s = −1`: `Φ (0, 1) (1 − (p/2) (s + 1))` lies below the
slice. -/
theorem slice_ge_of_neg_one (hΦ : IsProfile p Φ) (s : ℝ) :
    Φ 0 1 * (1 - p / 2 * (s + 1)) ≤ Φ (|1 + s| / 2) (|1 - s| / 2) := by
  have h := hΦ.swap.slice_ge_of_one (-s)
  rw [show 1 + -s = 1 - s by ring, show 1 - -s = 1 + s by ring] at h
  linarith

/-- A profile of degree `1` is nonnegative on the quadrant. -/
theorem nonneg_of_one (hΦ : IsProfile 1 Φ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ Φ x y := by
  have h01 : 0 ≤ Φ 1 0 := by
    have h := hΦ.slice_ge_of_neg_one 1
    norm_num at h
    exact h
  have hmin : BurkholderMinorant 1 (Φ 1 0 / 2) (Φ 1 0 / 2) Φ := by
    refine hΦ.burkholderMinorant_of_slice one_pos fun s hs1 hs2 => ?_
    have h := hΦ.slice_ge_of_one s
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
    linarith
  have h := hmin x y hx hy
  rw [sub_self, Real.rpow_zero, one_mul] at h
  have h2 : 0 ≤ Φ 1 0 * x := mul_nonneg h01 hx
  linarith

/-- **Burkholder-type supports, `1 ≤ p < 2`.** Let `Φ ≥ 0` be a profile of degree
`p ∈ [1, 2)`. At every point `(x₀, y₀)` of the segment `x₀ + y₀ = 1` of the quadrant there are
`c₀`, `m` with `(2 − p) |m| ≤ p c₀` such that the Burkholder-type function with profile
`s ↦ c₀ + m s` lies below `Φ` and equals `Φ` at `(x₀, y₀)`. -/
theorem exists_burkholderMinorant_of_lt_two (hΦ : IsProfile p Φ)
    (hΦ0 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Φ x y) (hp1 : 1 ≤ p) (hp2 : p < 2) {x₀ y₀ : ℝ}
    (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) (h1 : x₀ + y₀ = 1) :
    ∃ c₀ m : ℝ, (2 - p) * |m| ≤ p * c₀ ∧ BurkholderMinorant p c₀ m Φ ∧
      c₀ + m * (x₀ - y₀) = Φ x₀ y₀ := by
  have hp0 : 0 < p := by linarith
  have hE1 : ∀ s : ℝ, -1 ≤ s → s ≤ 1 →
      Φ 1 0 * (1 + p / 2 * (s - 1)) ≤ Φ ((1 + s) / 2) ((1 - s) / 2) := by
    intro s hs1 hs2
    have h := hΦ.slice_ge_of_one s
    rwa [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
  have hE2 : ∀ s : ℝ, -1 ≤ s → s ≤ 1 →
      Φ 0 1 * (1 - p / 2 * (s + 1)) ≤ Φ ((1 + s) / 2) ((1 - s) / 2) := by
    intro s hs1 hs2
    have h := hΦ.slice_ge_of_neg_one s
    rwa [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
  have h10 : 0 ≤ Φ 1 0 := hΦ0 1 0 zero_le_one le_rfl
  have h01 : 0 ≤ Φ 0 1 := hΦ0 0 1 le_rfl zero_le_one
  rcases hy₀.eq_or_lt with hy0 | hy0
  · -- the conformal point `(1, 0)`
    have hx1 : x₀ = 1 := by linarith
    subst hx1
    rw [← hy0]
    refine ⟨Φ 1 0 * (1 - p / 2), p / 2 * Φ 1 0, ?_, ?_, by ring⟩
    · rw [abs_of_nonneg (mul_nonneg (by linarith) h10)]
      exact le_of_eq (by ring)
    · exact hΦ.burkholderMinorant_of_slice hp0 fun s hs1 hs2 => by
        have h := hE1 s hs1 hs2
        linarith
  rcases hx₀.eq_or_lt with hx0 | hx0
  · -- the anticonformal point `(0, 1)`
    have hy1 : y₀ = 1 := by linarith
    subst hy1
    rw [← hx0]
    refine ⟨Φ 0 1 * (1 - p / 2), -(p / 2 * Φ 0 1), ?_, ?_, by ring⟩
    · rw [abs_neg, abs_of_nonneg (mul_nonneg (by linarith) h01)]
      exact le_of_eq (by ring)
    · exact hΦ.burkholderMinorant_of_slice hp0 fun s hs1 hs2 => by
        have h := hE2 s hs1 hs2
        linarith
  -- an interior point
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x₀ - y₀ := ⟨_, rfl⟩
  have hxt : x₀ = (1 + t) / 2 := by rw [ht]; linarith
  have hyt : y₀ = (1 - t) / 2 := by rw [ht]; linarith
  have ht1 : -1 < t := by rw [ht]; linarith
  have ht2 : t < 1 := by rw [ht]; linarith
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = Φ x₀ y₀ := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := by rw [hH]; exact hΦ0 x₀ y₀ hx₀ hy₀
  obtain ⟨m, hm⟩ := hΦ.convexOn_slice.exists_add_mul_le t
  have hm' : ∀ s : ℝ, -1 ≤ s → s ≤ 1 → H + m * (s - t) ≤ Φ ((1 + s) / 2) ((1 - s) / 2) := by
    intro s hs1 hs2
    have h : Φ (|1 + t| / 2) (|1 - t| / 2) + m * (s - t) ≤ Φ (|1 + s| / 2) (|1 - s| / 2) := hm s
    rwa [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith), ← hxt, ← hyt, ← hH] at h
  -- the supporting line at the ends of the slice, and the end lines at `t`
  have hs1 : m * (1 - t) ≤ Φ 1 0 - H := by
    have h := hm' 1 (by norm_num) le_rfl
    norm_num at h
    linarith
  have hs2 : H - Φ 0 1 ≤ m * (1 + t) := by
    have h := hm' (-1) le_rfl (by norm_num)
    norm_num at h
    linarith
  have he1 : Φ 1 0 * (p * t + 2 - p) ≤ 2 * H := by
    have h := hE1 t ht1.le ht2.le
    rw [← hxt, ← hyt, ← hH] at h
    linarith
  have he2 : Φ 0 1 * (2 - p - p * t) ≤ 2 * H := by
    have h := hE2 t ht1.le ht2.le
    rw [← hxt, ← hyt, ← hH] at h
    linarith
  have hA' : 0 ≤ p * t + 2 - p → 0 ≤ p * H - m * (p * t + 2 - p) := by
    intro hq
    have h3 := mul_le_mul_of_nonneg_left hs1 hq
    have h4 : 0 ≤ (p * H - m * (p * t + 2 - p)) * (1 - t) := by linarith
    exact nonneg_of_mul_nonneg_left h4 (by linarith)
  have hB' : 0 ≤ 2 - p - p * t → 0 ≤ p * H + m * (2 - p - p * t) := by
    intro hq
    have h3 := mul_le_mul_of_nonneg_left hs2 hq
    have h4 : 0 ≤ (p * H + m * (2 - p - p * t)) * (1 + t) := by linarith
    exact nonneg_of_mul_nonneg_left h4 (by linarith)
  have hpH : 0 ≤ p * H := mul_nonneg hp0.le hH0
  have hA : 0 ≤ p * H - m * (p * t + 2 - p) := by
    by_cases hq : 0 ≤ p * t + 2 - p
    · exact hA' hq
    · have hq' : p * t + 2 - p < 0 := not_le.1 hq
      rcases le_or_gt 0 m with hm0 | hm0
      · have := mul_nonneg hm0 (by linarith : 0 ≤ -(p * t + 2 - p))
        linarith
      · have hb := hB' (by linarith)
        have := mul_nonneg (by linarith : 0 ≤ -m) (by linarith : (0 : ℝ) ≤ 4 - 2 * p)
        linarith
  have hB : 0 ≤ p * H + m * (2 - p - p * t) := by
    by_cases hq : 0 ≤ 2 - p - p * t
    · exact hB' hq
    · have hq' : 2 - p - p * t < 0 := not_le.1 hq
      rcases le_or_gt m 0 with hm0 | hm0
      · have := mul_nonneg (by linarith : 0 ≤ -m) (by linarith : 0 ≤ -(2 - p - p * t))
        linarith
      · have ha := hA' (by linarith)
        have := mul_nonneg hm0.le (by linarith : (0 : ℝ) ≤ 4 - 2 * p)
        linarith
  refine ⟨H - m * t, m, ?_, ?_, by rw [← ht, hH]; ring⟩
  · rcases abs_cases m with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  · exact hΦ.burkholderMinorant_of_slice hp0 fun s hs1 hs2 => by
      have h := hm' s hs1 hs2
      linarith

end IsProfile

end HomogeneousIsotropic
