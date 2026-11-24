module

public import Morrey.HomogeneousIsotropic.Defs
public import Morrey.HomogeneousIsotropic.Inequalities
public import Morrey.Common.Basic.Analysis.Convex.Tangent

/-!
# Profiles: what rank-one convexity gives

Let `Φ` be a profile (`IsProfile p Φ`): `Φ (|z|, |w|) = F (A)` for an isotropic, positively
`p`-homogeneous, rank-one convex `F`. Write `h (s) = Φ ((1 + s)/2, (1 − s)/2)` for `s ∈ [−1, 1]`,
so that `Φ (x, y) = (x + y)^p h ((x − y)/(x + y))`.

* `IsProfile.le_of_sq_sub_sq_eq`: `Φ` grows along the hyperbolas `x² − y² = const`.
* `IsProfile.convexOn_slice`: `s ↦ Φ (|1 + s|/2, |1 − s|/2)` is convex on `ℝ`; on `[−1, 1]` it
  is `h`.
* `BurkholderMinorant p c₀ m Φ`: `(x + y)^{p−1} (c₀ (x + y) + m (x − y)) ≤ Φ (x, y)` on the
  quadrant; in terms of `h`, the line `s ↦ c₀ + m s` lies below `h`
  (`IsProfile.burkholderMinorant_of_slice`). Every supporting line of `h` gives one
  (`IsProfile.exists_burkholderMinorant`).
* `IsProfile.tangent`: if such a minorant touches `Φ` at `((1 + t)/2, (1 − t)/2)`, `|t| < 1`,
  with value `H`, then along every rank-one line through that point
  `Φ (|x₀ + τ α|, |y₀ + τ β|) ≥ H + τ (Φ_x Re α + Φ_y Re β)`, where `Φ_x = p H + (1 − t) m` and
  `Φ_y = p H − (1 + t) m` are the partial derivatives of the minorant.
* `IsProfile.baker_ericksen`: then `p H − 2 t m ≥ 0`.
-/

@[expose] public section

open Set Filter Topology

namespace HomogeneousIsotropic

/-- The Burkholder-type function with profile `s ↦ c₀ + m s` lies below `Φ` on the quadrant:
`(x + y)^{p−1} (c₀ (x + y) + m (x − y)) ≤ Φ (x, y)` for `x, y ≥ 0`. -/
def BurkholderMinorant (p c₀ m : ℝ) (Φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ (p - 1) * (c₀ * (x + y) + m * (x - y)) ≤ Φ x y

/-- Exchanging the variables turns a minorant with slope `m` into one with slope `−m`. -/
theorem BurkholderMinorant.swap {p c₀ m : ℝ} {Φ : ℝ → ℝ → ℝ} (h : BurkholderMinorant p c₀ m Φ) :
    BurkholderMinorant p c₀ (-m) fun x y => Φ y x := by
  intro x y hx hy
  have := h y x hy hx
  rw [show x + y = y + x by ring, show -m * (x - y) = m * (y - x) by ring]
  exact this

namespace IsProfile

variable {p : ℝ} {Φ : ℝ → ℝ → ℝ}

/-- Exchanging the variables of a profile gives a profile (the profile of `A ↦ F (J A)`,
`J = diag (1, −1)`). -/
theorem swap (hΦ : IsProfile p Φ) : IsProfile p fun x y => Φ y x :=
  ⟨fun c x y hc hx hy => hΦ.homog c y x hc hy hx, fun z w α β h => hΦ.convex w z β α h.symm⟩

/-- A profile of positive degree vanishes at the origin. -/
theorem zero_zero (hΦ : IsProfile p Φ) (hp : 0 < p) : Φ 0 0 = 0 := by
  have h := hΦ.homog 2 0 0 two_pos le_rfl le_rfl
  simp only [mul_zero] at h
  have h2 : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow one_lt_two hp
  nlinarith

/-- `Φ` is nondecreasing along the hyperbolas `x² − y² = const` (the Baker–Ericksen inequality
in integrated form): the rank-one line `τ ↦ (x₀ + i τ, y₀ + i τ)` gives a convex, even function
of `τ`. -/
theorem le_of_sq_sub_sq_eq (hΦ : IsProfile p Φ) {x₀ y₀ x₁ y₁ : ℝ} (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) (h : x₁ ^ 2 - x₀ ^ 2 = y₁ ^ 2 - y₀ ^ 2) :
    Φ x₀ y₀ ≤ Φ x₁ y₁ := by
  set τ : ℝ := √(x₁ ^ 2 - x₀ ^ 2) with hτ
  have hτ2 : τ ^ 2 = x₁ ^ 2 - x₀ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hconv := hΦ.convex x₀ y₀ Complex.I Complex.I rfl
  have key : ∀ s : ℝ, s ^ 2 = τ ^ 2 →
      Φ ‖(x₀ : ℂ) + s * Complex.I‖ ‖(y₀ : ℂ) + s * Complex.I‖ = Φ x₁ y₁ := by
    intro s hs
    rw [norm_ofReal_add_mul, norm_ofReal_add_mul]
    simp only [Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one]
    rw [show x₀ ^ 2 + s ^ 2 = x₁ ^ 2 by nlinarith, show y₀ ^ 2 + s ^ 2 = y₁ ^ 2 by nlinarith,
      Real.sqrt_sq (hx₀.trans hx), Real.sqrt_sq (hy₀.trans hy)]
  have h0 : Φ ‖(x₀ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I‖ ‖(y₀ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I‖ =
      Φ x₀ y₀ := by
    simp [abs_of_nonneg hx₀, abs_of_nonneg hy₀]
  have hmid := hconv.2 (mem_univ τ) (mem_univ (-τ)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  rw [show (1 / 2 : ℝ) * τ + 1 / 2 * -τ = (0 : ℝ) by ring, key τ rfl, key (-τ) (by ring), h0]
    at hmid
  linarith

/-- The slice `s ↦ Φ (|1 + s|/2, |1 − s|/2)` is convex on `ℝ`: it is `s ↦ F (diag (1, s))`. -/
theorem convexOn_slice (hΦ : IsProfile p Φ) :
    ConvexOn ℝ univ fun s : ℝ => Φ (|1 + s| / 2) (|1 - s| / 2) := by
  have h := hΦ.convex (1 / 2) (1 / 2) (1 / 2) (-(1 / 2)) (by simp)
  have he : (fun s : ℝ => Φ ‖(1 / 2 : ℂ) + s * (1 / 2)‖ ‖(1 / 2 : ℂ) + s * (-(1 / 2))‖) =
      fun s : ℝ => Φ (|1 + s| / 2) (|1 - s| / 2) := by
    funext s
    have h1 : (1 / 2 : ℂ) + s * (1 / 2) = (((1 + s) / 2 : ℝ) : ℂ) := by push_cast; ring
    have h2 : (1 / 2 : ℂ) + s * (-(1 / 2)) = (((1 - s) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_div, abs_div, abs_two]
  rwa [he] at h

/-- Homogeneity: `Φ (x, y) = (x + y)^p Φ (x/(x + y), y/(x + y))`. -/
theorem eq_rpow_mul (hΦ : IsProfile p Φ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 0 < x + y) :
    Φ x y = (x + y) ^ p * Φ (x / (x + y)) (y / (x + y)) := by
  have h := hΦ.homog (x + y) (x / (x + y)) (y / (x + y)) hxy (div_nonneg hx hxy.le)
    (div_nonneg hy hxy.le)
  rwa [mul_div_cancel₀ _ hxy.ne', mul_div_cancel₀ _ hxy.ne'] at h

/-- A line `s ↦ c₀ + m s` below the slice on `[−1, 1]` gives a Burkholder-type minorant of `Φ`
on the quadrant. -/
theorem burkholderMinorant_of_slice (hΦ : IsProfile p Φ) (hp : 0 < p) {c₀ m : ℝ}
    (h : ∀ s : ℝ, -1 ≤ s → s ≤ 1 → c₀ + m * s ≤ Φ ((1 + s) / 2) ((1 - s) / 2)) :
    BurkholderMinorant p c₀ m Φ := by
  intro x y hx hy
  rcases (add_nonneg hx hy).eq_or_lt with h0 | hpos
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst hx0 hy0
    simp [hΦ.zero_zero hp]
  · have hs1 : -1 ≤ (x - y) / (x + y) := by rw [le_div_iff₀ hpos]; linarith
    have hs2 : (x - y) / (x + y) ≤ 1 := by rw [div_le_iff₀ hpos]; linarith
    have hxs : (1 + (x - y) / (x + y)) / 2 = x / (x + y) := by field_simp; ring
    have hys : (1 - (x - y) / (x + y)) / 2 = y / (x + y) := by field_simp; ring
    have hh := h _ hs1 hs2
    rw [hxs, hys] at hh
    rw [hΦ.eq_rpow_mul hx hy hpos]
    have hpow : (x + y) ^ p = (x + y) ^ (p - 1) * (x + y) := by
      rw [← Real.rpow_add_one hpos.ne']
      congr 1
      ring
    have he : (x + y) ^ (p - 1) * (c₀ * (x + y) + m * (x - y)) =
        (x + y) ^ p * (c₀ + m * ((x - y) / (x + y))) := by
      rw [hpow]
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hpos.le _)

/-- A supporting line of the slice at `t ∈ [−1, 1]` gives a Burkholder-type minorant that
touches `Φ` at `((1 + t)/2, (1 − t)/2)`. -/
theorem exists_burkholderMinorant (hΦ : IsProfile p Φ) (hp : 0 < p) {t : ℝ} (ht1 : -1 ≤ t)
    (ht2 : t ≤ 1) :
    ∃ m : ℝ, BurkholderMinorant p (Φ ((1 + t) / 2) ((1 - t) / 2) - m * t) m Φ := by
  obtain ⟨m, hm⟩ := hΦ.convexOn_slice.exists_add_mul_le t
  refine ⟨m, hΦ.burkholderMinorant_of_slice hp fun s hs1 hs2 => ?_⟩
  have h : Φ (|1 + t| / 2) (|1 - t| / 2) + m * (s - t) ≤ Φ (|1 + s| / 2) (|1 - s| / 2) := hm s
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
    abs_of_nonneg (by linarith)] at h
  linarith

/-- The first-order inequality along rank-one lines. If a Burkholder-type minorant with slope `m`
touches `Φ` at `(x₀, y₀) = ((1 + t)/2, (1 − t)/2)`, `|t| < 1`, with value `H`, then for all
`α`, `β` with `|α| = |β|` and all real `τ`,
`Φ (|x₀ + τ α|, |y₀ + τ β|) ≥ H + τ (Φ_x Re α + Φ_y Re β)`, where `Φ_x = p H + (1 − t) m` and
`Φ_y = p H − (1 + t) m`. -/
theorem tangent (hΦ : IsProfile p Φ) {H m t : ℝ} (ht : |t| < 1)
    (hmin : BurkholderMinorant p (H - m * t) m Φ) (heq : Φ ((1 + t) / 2) ((1 - t) / 2) = H)
    {α β : ℂ} (hαβ : ‖α‖ = ‖β‖) (τ : ℝ) :
    H + τ * ((p * H + (1 - t) * m) * α.re + (p * H - (1 + t) * m) * β.re) ≤
      Φ ‖(((1 + t) / 2 : ℝ) : ℂ) + τ * α‖ ‖(((1 - t) / 2 : ℝ) : ℂ) + τ * β‖ := by
  obtain ⟨ht1, ht2⟩ := abs_lt.1 ht
  have hx₀pos : 0 < (1 + t) / 2 := by linarith
  have hy₀pos : 0 < (1 - t) / 2 := by linarith
  set x₀ : ℝ := (1 + t) / 2 with hx₀
  set y₀ : ℝ := (1 - t) / 2 with hy₀
  set g : ℝ → ℝ := fun τ => Φ ‖(x₀ : ℂ) + τ * α‖ ‖(y₀ : ℂ) + τ * β‖ with hg
  set k : ℝ → ℝ := fun τ => (‖(x₀ : ℂ) + τ * α‖ + ‖(y₀ : ℂ) + τ * β‖) ^ (p - 1) *
    ((H - m * t) * (‖(x₀ : ℂ) + τ * α‖ + ‖(y₀ : ℂ) + τ * β‖) +
      m * (‖(x₀ : ℂ) + τ * α‖ - ‖(y₀ : ℂ) + τ * β‖)) with hk
  have hconv : ConvexOn ℝ univ g := hΦ.convex x₀ y₀ α β hαβ
  have hle : ∀ τ, k τ ≤ g τ := fun τ => hmin _ _ (norm_nonneg _) (norm_nonneg _)
  have hX := hasDerivAt_norm_ofReal_add_mul hx₀pos α
  have hY := hasDerivAt_norm_ofReal_add_mul hy₀pos β
  have hX0 : ‖(x₀ : ℂ) + ((0 : ℝ) : ℂ) * α‖ = x₀ := by simp [abs_of_pos hx₀pos]
  have hY0 : ‖(y₀ : ℂ) + ((0 : ℝ) : ℂ) * β‖ = y₀ := by simp [abs_of_pos hy₀pos]
  have hsum : x₀ + y₀ = 1 := by rw [hx₀, hy₀]; ring
  have hdiff : x₀ - y₀ = t := by rw [hx₀, hy₀]; ring
  have hk0 : k 0 = H := by
    simp only [hk]
    rw [hX0, hY0, hsum, hdiff, Real.one_rpow]
    ring
  have hg0 : g 0 = H := by
    simp only [hg]
    rw [hX0, hY0]
    exact heq
  have hS := hX.add hY
  have hD := hX.sub hY
  have hne : ‖(x₀ : ℂ) + ((0 : ℝ) : ℂ) * α‖ + ‖(y₀ : ℂ) + ((0 : ℝ) : ℂ) * β‖ ≠ 0 := by
    rw [hX0, hY0, hsum]
    exact one_ne_zero
  have hpowd := hS.rpow_const (p := p - 1) (Or.inl hne)
  have hkd : HasDerivAt k ((p * H + (1 - t) * m) * α.re + (p * H - (1 + t) * m) * β.re) 0 := by
    have h1 := hpowd.mul ((hS.const_mul (H - m * t)).add (hD.const_mul m))
    convert h1 using 1
    simp only [Pi.add_apply, Pi.sub_apply, hX0, hY0, hsum, hdiff, Real.one_rpow]
    ring
  have h := hconv.add_mul_le_of_hasDerivAt_le (Eventually.of_forall hle) (hk0.trans hg0.symm) hkd τ
  rw [hg0, sub_zero] at h
  linarith

/-- The Baker–Ericksen inequality at a point where a Burkholder-type minorant with slope `m`
touches `Φ` with value `H`: `p H − 2 t m ≥ 0`. It is the first-order inequality along the chord
from the base matrix to a rotated copy of it. -/
theorem baker_ericksen (hΦ : IsProfile p Φ) {H m t : ℝ} (ht : |t| < 1)
    (hmin : BurkholderMinorant p (H - m * t) m Φ) (heq : Φ ((1 + t) / 2) ((1 - t) / 2) = H) :
    0 ≤ p * H - 2 * t * m := by
  obtain ⟨ht1, ht2⟩ := abs_lt.1 ht
  have hx₀pos : 0 < (1 + t) / 2 := by linarith
  have hy₀pos : 0 < (1 - t) / 2 := by linarith
  set x₀ : ℝ := (1 + t) / 2 with hx₀
  set y₀ : ℝ := (1 - t) / 2 with hy₀
  have hx₀1 : x₀ < 1 := by rw [hx₀]; linarith
  have hy₀1 : y₀ < 1 := by rw [hy₀]; linarith
  have hx2 : 0 ≤ 1 - x₀ ^ 2 := by nlinarith
  have hy2 : 0 ≤ 1 - y₀ ^ 2 := by nlinarith
  set α : ℂ := ⟨-y₀, √(1 - y₀ ^ 2)⟩ with hα
  set β : ℂ := ⟨-x₀, √(1 - x₀ ^ 2)⟩ with hβ
  have hnα : ‖α‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, Real.mul_self_sqrt hy2]
    rw [show -y₀ * -y₀ + (1 - y₀ ^ 2) = 1 by ring, Real.sqrt_one]
  have hnβ : ‖β‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, Real.mul_self_sqrt hx2]
    rw [show -x₀ * -x₀ + (1 - x₀ ^ 2) = 1 by ring, Real.sqrt_one]
  have hnx : ‖(x₀ : ℂ) + ((2 * x₀ * y₀ : ℝ) : ℂ) * α‖ = x₀ := by
    rw [norm_ofReal_add_mul]
    have : (x₀ + 2 * x₀ * y₀ * α.re) ^ 2 + (2 * x₀ * y₀ * α.im) ^ 2 = x₀ ^ 2 := by
      simp only [hα, mul_pow, Real.sq_sqrt hy2]
      ring
    rw [this, Real.sqrt_sq hx₀pos.le]
  have hny : ‖(y₀ : ℂ) + ((2 * x₀ * y₀ : ℝ) : ℂ) * β‖ = y₀ := by
    rw [norm_ofReal_add_mul]
    have : (y₀ + 2 * x₀ * y₀ * β.re) ^ 2 + (2 * x₀ * y₀ * β.im) ^ 2 = y₀ ^ 2 := by
      simp only [hβ, mul_pow, Real.sq_sqrt hx2]
      ring
    rw [this, Real.sqrt_sq hy₀pos.le]
  have h := hΦ.tangent ht hmin heq (hnα.trans hnβ.symm) (2 * x₀ * y₀)
  rw [hnx, hny, heq] at h
  have hre : (p * H + (1 - t) * m) * α.re + (p * H - (1 + t) * m) * β.re =
      -(p * H - 2 * t * m) := by
    simp only [hα, hβ, hx₀, hy₀]
    ring
  rw [hre] at h
  have hxy : 0 < 2 * x₀ * y₀ := by positivity
  nlinarith
