module

public import Morrey.HomogeneousIsotropic.Signed.Defs
public import Morrey.HomogeneousIsotropic.LowExponent
public import Mathlib.Analysis.Convex.Continuous

/-!
# Profiles of any sign: the slice

Let `Φ` be a profile of degree `p > 0` (`IsProfile p Φ`) and `h = slice Φ` its slice on
`[−1, 1]`.

* `IsProfile.convexOn_slice_Icc`, `IsProfile.continuousOn_slice`: `h` is convex and continuous
  on `[−1, 1]`; `IsProfile.eq_rpow_mul_slice`: `Φ (x, y) = (x + y)^p h ((x − y)/(x + y))`.
* `IsProfile.slice_zero_nonneg`: `h 0 ≥ 0`.
* `IsProfile.rpow_mul_slice_neg_one_le`, `IsProfile.rpow_mul_slice_one_le`:
  `(−t)^{p/2} h (−1) ≤ h t` for `t ∈ [−1, 0]` and `t^{p/2} h 1 ≤ h t` for `t ∈ [0, 1]`; hence a
  negative value of `Φ` forces `h (−1) < 0` or `h 1 < 0`
  (`IsProfile.slice_neg_one_neg_or_slice_one_neg`).
* `IsProfile.neg_one_line_le_slice`, `IsProfile.one_line_le_slice`: the supporting lines of `h`
  at `−1` and at `1`, with the slopes `−(p/2) h (−1)` and `(p/2) h 1`.
* `IsProfile.slope_ge`, `IsProfile.slope_le`, `IsProfile.slope_pos`: a supporting slope `m` of
  `h` at a point of `(−1, 1]` satisfies `m ≥ −(p/2) h (−1)`, and one at a point of `[−1, 1)`
  satisfies `m ≤ (p/2) h 1`; the slopes are positive if `h (−1) < 0`.
* `IsProfile.slice_neg_nonneg`: `h (−a) ≥ 0` for `a = e (p − 2)/p`.
* `IsHardBase.base_pos`, `IsHardBase.e_mul_slice_pos`: a hard base `t` satisfies `t < −a` and
  `h t < 0` if `p < 2`, and `t > −a` and `h t > 0` if `p > 2`.
-/

@[expose] public section

open Set

namespace HomogeneousIsotropic

variable {p e : ℝ} {Φ : ℝ → ℝ → ℝ}

/-- The slice of the mirror image of a profile is the reflected slice. -/
theorem slice_swap (Φ : ℝ → ℝ → ℝ) (t : ℝ) : slice (fun x y => Φ y x) t = slice Φ (-t) := by
  simp only [slice]
  rw [show (1 + -t) / 2 = (1 - t) / 2 by ring, show (1 - -t) / 2 = (1 + t) / 2 by ring]

/-- The slice at `−1` is the value of the profile at `(0, 1)`. -/
theorem slice_neg_one (Φ : ℝ → ℝ → ℝ) : slice Φ (-1) = Φ 0 1 := by
  simp only [slice]
  norm_num

/-- The slice at `1` is the value of the profile at `(1, 0)`. -/
theorem slice_one (Φ : ℝ → ℝ → ℝ) : slice Φ 1 = Φ 1 0 := by
  simp only [slice]
  norm_num

namespace IsProfile

/-- The slice of a profile is convex on `[−1, 1]`. -/
theorem convexOn_slice_Icc (hΦ : IsProfile p Φ) : ConvexOn ℝ (Icc (-1) 1) (slice Φ) := by
  refine (hΦ.convexOn_slice.subset (subset_univ _) (convex_Icc _ _)).congr ?_
  intro s hs
  simp only [slice]
  rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith [hs.2])]

/-- The slice of a profile is continuous on `[−1, 1]`. -/
theorem continuousOn_slice (hΦ : IsProfile p Φ) : ContinuousOn (slice Φ) (Icc (-1) 1) := by
  have h := (hΦ.convexOn_slice.continuousOn isOpen_univ).mono (subset_univ (Icc (-1 : ℝ) 1))
  refine h.congr ?_
  intro s hs
  simp only [slice]
  rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith [hs.2])]

/-- Homogeneity in terms of the slice: `Φ (x, y) = (x + y)^p h ((x − y)/(x + y))`. -/
theorem eq_rpow_mul_slice (hΦ : IsProfile p Φ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) : Φ x y = (x + y) ^ p * slice Φ ((x - y) / (x + y)) := by
  have hxs : (1 + (x - y) / (x + y)) / 2 = x / (x + y) := by field_simp; ring
  have hys : (1 - (x - y) / (x + y)) / 2 = y / (x + y) := by field_simp; ring
  rw [slice, hxs, hys]
  exact hΦ.eq_rpow_mul hx hy hxy

/-- A Burkholder-type function with the line of slope `m` through `(t, h t)` lies below a
profile of positive degree if and only if the line lies below the slice on `[−1, 1]`. -/
theorem burkholderMinorant_slice_iff (hΦ : IsProfile p Φ) (hp : 0 < p) {t m : ℝ} :
    BurkholderMinorant p (slice Φ t - m * t) m Φ ↔
      ∀ s ∈ Icc (-1 : ℝ) 1, slice Φ t + m * (s - t) ≤ slice Φ s := by
  rw [hΦ.burkholderMinorant_iff_slice hp]
  constructor
  · intro h s hs
    have h' := h s hs.1 hs.2
    simp only [slice] at h' ⊢
    linarith
  · intro h s hs1 hs2
    have h' := h s ⟨hs1, hs2⟩
    simp only [slice] at h' ⊢
    linarith

/-- The slice of a profile of positive degree is nonnegative at `0`. -/
theorem slice_zero_nonneg (hΦ : IsProfile p Φ) (hp : 0 < p) : 0 ≤ slice Φ 0 := by
  have hconv := hΦ.convex 0 0 (1 / 2) (1 / 2) rfl
  have key : ∀ s : ℝ, ‖(0 : ℂ) + (s : ℂ) * (1 / 2)‖ = |s| / 2 := by
    intro s
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, h2]
    ring
  have hmid := hconv.2 (mem_univ (1 : ℝ)) (mem_univ (-1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, key] at hmid
  rw [show (1 / 2 : ℝ) * 1 + 1 / 2 * -1 = 0 by ring, abs_zero, zero_div, abs_neg, abs_one,
    hΦ.zero_zero hp] at hmid
  simp only [slice]
  rw [show (1 + (0 : ℝ)) / 2 = 1 / 2 by ring, show (1 - (0 : ℝ)) / 2 = 1 / 2 by ring]
  linarith

/-- `(−t)^{p/2} h (−1) ≤ h (t)` for `t ∈ [−1, 0]`: the monotonicity along the hyperbola from
`(0, √(−t))` to `((1 + t)/2, (1 − t)/2)`. -/
theorem rpow_mul_slice_neg_one_le (hΦ : IsProfile p Φ) (hp : 0 < p) {t : ℝ} (ht1 : -1 ≤ t)
    (ht0 : t ≤ 0) : (-t) ^ (p / 2) * slice Φ (-1) ≤ slice Φ t := by
  rcases ht0.eq_or_lt with rfl | ht
  · rw [neg_zero, Real.zero_rpow (by linarith : p / 2 ≠ 0), zero_mul]
    exact hΦ.slice_zero_nonneg hp
  have hu : 0 < -t := by linarith
  have hr : 0 < √(-t) := Real.sqrt_pos.2 hu
  have hr2 : √(-t) ^ 2 = -t := Real.sq_sqrt hu.le
  have hyr : √(-t) ≤ (1 - t) / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [sq_nonneg (1 + t)]⟩
  have h1 : Φ 0 √(-t) ≤ Φ ((1 + t) / 2) ((1 - t) / 2) :=
    hΦ.le_of_sq_sub_sq_eq le_rfl hr.le (by linarith) hyr (by rw [hr2]; ring)
  have h2 : Φ 0 √(-t) = √(-t) ^ p * Φ 0 1 := by
    simpa using hΦ.homog √(-t) 0 1 hr le_rfl zero_le_one
  have h3 : √(-t) ^ p = (-t) ^ (p / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le]
    congr 1
    ring
  rw [slice_neg_one, ← h3, ← h2]
  exact h1

/-- `t^{p/2} h (1) ≤ h (t)` for `t ∈ [0, 1]`. -/
theorem rpow_mul_slice_one_le (hΦ : IsProfile p Φ) (hp : 0 < p) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : t ^ (p / 2) * slice Φ 1 ≤ slice Φ t := by
  have h := hΦ.swap.rpow_mul_slice_neg_one_le hp (t := -t) (by linarith) (by linarith)
  rwa [slice_swap Φ (-1), slice_swap Φ (-t), neg_neg, neg_neg] at h

/-- If a profile of positive degree has a negative value on the quadrant, its slice is negative
at `−1` or at `1`. -/
theorem slice_neg_one_neg_or_slice_one_neg (hΦ : IsProfile p Φ) (hp : 0 < p) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : Φ x y < 0) : slice Φ (-1) < 0 ∨ slice Φ 1 < 0 := by
  have hpos : 0 < x + y := by
    rcases (add_nonneg hx hy).eq_or_lt with h0 | hpos
    · have hx0 : x = 0 := by linarith
      have hy0 : y = 0 := by linarith
      rw [hx0, hy0, hΦ.zero_zero hp] at h
      exact absurd h (lt_irrefl _)
    · exact hpos
  have hpw : 0 < (x + y) ^ p := Real.rpow_pos_of_pos hpos p
  have hη : slice Φ ((x - y) / (x + y)) < 0 := by
    rw [hΦ.eq_rpow_mul_slice hx hy hpos] at h
    by_contra hcon
    have := mul_nonneg hpw.le (not_lt.1 hcon)
    linarith
  have hη1 : -1 ≤ (x - y) / (x + y) := by rw [le_div_iff₀ hpos]; linarith
  have hη2 : (x - y) / (x + y) ≤ 1 := by rw [div_le_iff₀ hpos]; linarith
  rcases le_total ((x - y) / (x + y)) 0 with h0 | h0
  · left
    have h1 := hΦ.rpow_mul_slice_neg_one_le hp hη1 h0
    by_contra hcon
    have := mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ -((x - y) / (x + y))) (p / 2))
      (not_lt.1 hcon)
    linarith
  · right
    have h1 := hΦ.rpow_mul_slice_one_le hp h0 hη2
    by_contra hcon
    have := mul_nonneg (Real.rpow_nonneg h0 (p / 2)) (not_lt.1 hcon)
    linarith

/-- The supporting line of the slice at `−1`, with slope `−(p/2) h (−1)`, lies below the slice
on `[−1, 1]`. -/
theorem neg_one_line_le_slice (hΦ : IsProfile p Φ) {s : ℝ} (hs1 : -1 ≤ s) (hs2 : s ≤ 1) :
    slice Φ (-1) * (1 - p / 2 * (s + 1)) ≤ slice Φ s := by
  have h := hΦ.slice_ge_of_neg_one s
  rwa [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), ← slice_neg_one Φ] at h

/-- The supporting line of the slice at `1`, with slope `(p/2) h (1)`, lies below the slice on
`[−1, 1]`. -/
theorem one_line_le_slice (hΦ : IsProfile p Φ) {s : ℝ} (hs1 : -1 ≤ s) (hs2 : s ≤ 1) :
    slice Φ 1 * (1 + p / 2 * (s - 1)) ≤ slice Φ s := by
  have h := hΦ.slice_ge_of_one s
  rwa [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), ← slice_one Φ] at h

/-- The slopes of the supporting lines of the slice at the points of `(−1, 1]` are at least
`−(p/2) h (−1)`, the slope of the supporting line at `−1`. -/
theorem slope_ge (hΦ : IsProfile p Φ) (hp : 0 < p) {t m : ℝ} (ht1 : -1 < t) (ht2 : t ≤ 1)
    (hmin : BurkholderMinorant p (slice Φ t - m * t) m Φ) : -(p / 2) * slice Φ (-1) ≤ m := by
  have h1 := (hΦ.burkholderMinorant_slice_iff hp).1 hmin (-1) ⟨le_rfl, by norm_num⟩
  have h2 := hΦ.neg_one_line_le_slice ht1.le ht2
  have h3 : 0 ≤ (m - -(p / 2) * slice Φ (-1)) * (1 + t) := by linarith
  linarith [nonneg_of_mul_nonneg_left h3 (by linarith : 0 < 1 + t)]

/-- The slopes of the supporting lines of the slice at the points of `[−1, 1)` are at most
`(p/2) h (1)`, the slope of the supporting line at `1`. -/
theorem slope_le (hΦ : IsProfile p Φ) (hp : 0 < p) {t m : ℝ} (ht1 : -1 ≤ t) (ht2 : t < 1)
    (hmin : BurkholderMinorant p (slice Φ t - m * t) m Φ) : m ≤ p / 2 * slice Φ 1 := by
  have h1 := (hΦ.burkholderMinorant_slice_iff hp).1 hmin 1 ⟨by norm_num, le_rfl⟩
  have h2 := hΦ.one_line_le_slice ht1 ht2.le
  have h3 : 0 ≤ (p / 2 * slice Φ 1 - m) * (1 - t) := by linarith
  linarith [nonneg_of_mul_nonneg_left h3 (by linarith : 0 < 1 - t)]

/-- If `h (−1) < 0`, the supporting lines of the slice at the points of `(−1, 1]` have positive
slopes. -/
theorem slope_pos (hΦ : IsProfile p Φ) (hp : 0 < p) (hor : slice Φ (-1) < 0) {t m : ℝ}
    (ht1 : -1 < t) (ht2 : t ≤ 1) (hmin : BurkholderMinorant p (slice Φ t - m * t) m Φ) :
    0 < m := by
  have h := hΦ.slope_ge hp ht1 ht2 hmin
  have h2 : 0 < -(p / 2) * slice Φ (-1) := by
    have := mul_pos (by linarith : (0 : ℝ) < p / 2) (neg_pos.2 hor)
    linarith
  linarith

/-- The slice is nonnegative at `−a`, `a = e (p − 2)/p`: there the supporting line at `1` (if
`p < 2`) or at `−1` (if `p > 2`) vanishes. -/
theorem slice_neg_nonneg (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) : 0 ≤ slice Φ (-(e * (p - 2) / p)) := by
  have hp0 : 0 < p := by linarith
  rcases he with rfl | rfl
  · have hp2 : 2 < p := by linarith
    have hs1 : -1 ≤ -(1 * (p - 2) / p) := by
      rw [neg_le_neg_iff, div_le_iff₀ hp0]
      linarith
    have hs2 : -(1 * (p - 2) / p) ≤ 1 := by
      have : 0 ≤ 1 * (p - 2) / p := div_nonneg (by linarith) hp0.le
      linarith
    have h := hΦ.neg_one_line_le_slice hs1 hs2
    have h0 : 1 - p / 2 * (-(1 * (p - 2) / p) + 1) = 0 := by
      field_simp
      ring
    rwa [h0, mul_zero] at h
  · have hp2 : p < 2 := by linarith
    have hs1 : -1 ≤ -(-1 * (p - 2) / p) := by
      rw [neg_le_neg_iff, div_le_iff₀ hp0]
      linarith
    have hs2 : -(-1 * (p - 2) / p) ≤ 1 := by
      have : 0 ≤ -1 * (p - 2) / p := div_nonneg (by linarith) hp0.le
      linarith
    have h := hΦ.one_line_le_slice hs1 hs2
    have h0 : 1 + p / 2 * (-(-1 * (p - 2) / p) - 1) = 0 := by
      field_simp
      ring
    rwa [h0, mul_zero] at h

end IsProfile

namespace IsHardBase

variable {t m : ℝ}

/-- At a hard base, `1 + e t > 0`. -/
theorem one_add_pos (he : e = 1 ∨ e = -1) (hb : IsHardBase p e Φ t m) : 0 < 1 + e * t := by
  obtain ⟨ht1, ht2⟩ := _root_.abs_lt.1 hb.abs_lt
  rcases he with rfl | rfl <;> linarith

/-- The Baker–Ericksen inequality at a hard base. -/
theorem baker_ericksen (hΦ : IsProfile p Φ) (hb : IsHardBase p e Φ t m) :
    0 ≤ p * slice Φ t - 2 * t * m :=
  hΦ.baker_ericksen hb.abs_lt hb.minorant rfl

/-- The slope of a hard base is positive, if `h (−1) < 0`. -/
theorem slope_pos (hΦ : IsProfile p Φ) (hp : 1 < p) (hor : slice Φ (-1) < 0)
    (hb : IsHardBase p e Φ t m) : 0 < m :=
  hΦ.slope_pos (by linarith) hor (_root_.abs_lt.1 hb.abs_lt).1 (_root_.abs_lt.1 hb.abs_lt).2.le
    hb.minorant

/-- A hard base lies beyond `−a`: `t < −a` if `p < 2` and `t > −a` if `p > 2`, that is,
`e (t + a) > 0`, written as `e p t + (p − 2) > 0`. -/
theorem base_pos (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1) (hpe : 0 < e * (p - 2))
    (hb : IsHardBase p e Φ t m) : 0 < e * p * t + (p - 2) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨ht1, ht2⟩ := _root_.abs_lt.1 hb.abs_lt
  have hneg := hb.neg
  by_contra hcon
  rw [not_lt] at hcon
  rcases he with rfl | rfl
  · -- `p > 2`: compare with the supporting line at `−1`
    have h1 := hΦ.neg_one_line_le_slice ht1.le ht2.le
    have h2 := hΦ.slope_ge hp0 ht1 ht2.le hb.minorant
    have e1 : p * (slice Φ t - m * t) - 1 * (p - 2) * m =
        p * (slice Φ t - slice Φ (-1) * (1 - p / 2 * (t + 1))) +
          (m - -(p / 2) * slice Φ (-1)) * (-(1 * p * t + (p - 2))) := by
      ring
    have h3 := mul_nonneg hp0.le (sub_nonneg.2 h1)
    have h4 := mul_nonneg (sub_nonneg.2 h2) (neg_nonneg.2 hcon)
    linarith
  · -- `p < 2`: compare with the supporting line at `1`
    have h1 := hΦ.one_line_le_slice ht1.le ht2.le
    have h2 := hΦ.slope_le hp0 ht1.le ht2 hb.minorant
    have e1 : p * (slice Φ t - m * t) - -1 * (p - 2) * m =
        p * (slice Φ t - slice Φ 1 * (1 + p / 2 * (t - 1))) +
          (p / 2 * slice Φ 1 - m) * (-(-1 * p * t + (p - 2))) := by
      ring
    have h3 := mul_nonneg hp0.le (sub_nonneg.2 h1)
    have h4 := mul_nonneg (sub_nonneg.2 h2) (neg_nonneg.2 hcon)
    linarith

/-- The value of the slice at a hard base has the sign of `e`, if `h (−1) < 0`: it is negative
if `p < 2` and positive if `p > 2`. -/
theorem e_mul_slice_pos (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) (hor : slice Φ (-1) < 0) (hb : IsHardBase p e Φ t m) :
    0 < e * slice Φ t := by
  have hp0 : 0 < p := by linarith
  obtain ⟨ht1, ht2⟩ := _root_.abs_lt.1 hb.abs_lt
  have hbase := hb.base_pos hΦ hp he hpe
  have hm := hb.slope_pos hΦ hp hor
  have hneg := hb.neg
  rcases he with rfl | rfl
  · -- `p > 2`: the supporting line at `−1` is positive beyond `−a`
    have h1 := hΦ.neg_one_line_le_slice ht1.le ht2.le
    have h2 : 0 < slice Φ (-1) * (1 - p / 2 * (t + 1)) :=
      mul_pos_of_neg_of_neg hor (by linarith)
    linarith
  · -- `p < 2`: the supporting line of slope `m > 0` is negative at `−a > t`
    have h2 : 0 < m * (-1 * p * t + (p - 2)) := mul_pos hm hbase
    have h3 : p * slice Φ t < 0 := by linarith
    have h4 : slice Φ t < 0 := by
      by_contra hcon
      have := mul_nonneg hp0.le (not_lt.1 hcon)
      linarith
    linarith

end IsHardBase

end HomogeneousIsotropic
