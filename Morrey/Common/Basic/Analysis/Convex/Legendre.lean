module

public import Mathlib.Analysis.Convex.Strict
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Order.Compact

/-!
# The Legendre transform of a strictly convex function on an interval

For a strictly convex, continuous `h` on `[a, b]` and a slope `m`, the function `t ↦ h t − m t`
has a unique minimizer `T m` on `[a, b]`; `k m = h (T m) − m T m` is the minimum, so that the line
`s ↦ k m + m s` lies below `h` on `[a, b]` and touches it at `T m`.

* `StrictConvexOn.exists_legendre`: such `T` and `k` exist; `T` is nondecreasing and continuous,
  `T m = t` whenever the line of slope `m` through `(t, h t)` lies below `h` on `[a, b]`, and
  `k` is differentiable with derivative `−T`.
-/

@[expose] public section

open Set Filter Topology

/-- The Legendre transform of a strictly convex, continuous function `h` on `[a, b]`: there are
`T`, `k : ℝ → ℝ` such that, for every slope `m`, `T m ∈ [a, b]` minimizes `t ↦ h t − m t` on
`[a, b]` with minimum `k m`; a point of `[a, b]` at which the line of slope `m` supports `h` is
`T m`; `T` is nondecreasing and continuous; and `k` has the derivative `−T m` at `m`. -/
theorem StrictConvexOn.exists_legendre {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hh : StrictConvexOn ℝ (Icc a b) h) (hc : ContinuousOn h (Icc a b)) :
    ∃ T k : ℝ → ℝ, (∀ m, T m ∈ Icc a b) ∧ (∀ m, k m = h (T m) - m * T m) ∧
      (∀ m, ∀ s ∈ Icc a b, k m + m * s ≤ h s) ∧
      (∀ m, ∀ t ∈ Icc a b, (∀ s ∈ Icc a b, h t + m * (s - t) ≤ h s) → T m = t) ∧
      Monotone T ∧ Continuous T ∧ ∀ m, HasDerivAt k (-T m) m := by
  -- a minimizer of `t ↦ h t - m t` on `[a, b]`
  have hex : ∀ m : ℝ, ∃ t ∈ Icc a b, ∀ s ∈ Icc a b, h t - m * t ≤ h s - m * s := by
    intro m
    obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab)
      (hc.sub (continuousOn_const.mul continuousOn_id) : ContinuousOn (fun t => h t - m * t) _)
    exact ⟨t, ht, fun s hs => hmin hs⟩
  choose T hT hTmin using hex
  -- the minimizer is unique
  have huniq : ∀ m : ℝ, ∀ t ∈ Icc a b, (∀ s ∈ Icc a b, h t - m * t ≤ h s - m * s) →
      T m = t := by
    intro m t ht hmin
    by_contra hne
    have hmid := hh.2 (hT m) ht hne (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hmem : (1 / 2 : ℝ) • T m + (1 / 2 : ℝ) • t ∈ Icc a b :=
      hh.1 (hT m) ht (by norm_num) (by norm_num) (by norm_num)
    have h1 := hTmin m _ hmem
    have h3 := hTmin m t ht
    have h4 := hmin (T m) (hT m)
    simp only [smul_eq_mul] at hmid h1
    linarith
  have hmono : Monotone T := by
    intro m₁ m₂ hm
    rcases hm.eq_or_lt with rfl | hlt
    · exact le_rfl
    · by_contra hcon
      have hgt : T m₂ < T m₁ := not_le.1 hcon
      have h1 := hTmin m₁ (T m₂) (hT m₂)
      have h2 := hTmin m₂ (T m₁) (hT m₁)
      nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hgt)]
  -- a limit of minimizers is the minimizer
  have hlim : ∀ (m τ : ℝ) (l : Filter ℝ) [l.NeBot], l ≤ 𝓝 m → Tendsto T l (𝓝 τ) → τ = T m := by
    intro m τ l _ hl hτ
    have hτmem : τ ∈ Icc a b := isClosed_Icc.mem_of_tendsto hτ (Eventually.of_forall hT)
    refine (huniq m τ hτmem fun s hs => ?_).symm
    have hid : Tendsto (fun m' : ℝ => m') l (𝓝 m) := hl
    have hT' : Tendsto T l (𝓝[Icc a b] τ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ (Eventually.of_forall hT)
    have hhT : Tendsto (fun m' => h (T m')) l (𝓝 (h τ)) := (hc τ hτmem).tendsto.comp hT'
    have hL : Tendsto (fun m' => h (T m') - m' * T m') l (𝓝 (h τ - m * τ)) :=
      hhT.sub (hid.mul hτ)
    have hR : Tendsto (fun m' => h s - m' * s) l (𝓝 (h s - m * s)) :=
      tendsto_const_nhds.sub (hid.mul_const s)
    exact le_of_tendsto_of_tendsto' hL hR fun m' => hTmin m' s hs
  have hcont : Continuous T := by
    rw [continuous_iff_continuousAt]
    intro m
    rw [continuousAt_iff_continuous_left'_right']
    constructor
    · have h1 := hmono.tendsto_nhdsLT m
      rw [hlim m _ (𝓝[<] m) nhdsWithin_le_nhds h1] at h1
      exact h1
    · have h1 := hmono.tendsto_nhdsGT m
      rw [hlim m _ (𝓝[>] m) nhdsWithin_le_nhds h1] at h1
      exact h1
  have hderiv : ∀ m, HasDerivAt (fun m => h (T m) - m * T m) (-T m) m := by
    intro m
    rw [hasDerivAt_iff_tendsto]
    have hT0 : Tendsto (fun m' => |T m' - T m|) (𝓝 m) (𝓝 0) := by
      have h1 := ((hcont.tendsto m).sub_const (T m)).abs
      rwa [sub_self, abs_zero] at h1
    refine squeeze_zero (fun m' => by positivity) (fun m' => ?_) hT0
    rcases eq_or_ne m' m with rfl | hne
    · simp
    have hpos : 0 < ‖m' - m‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    rw [inv_mul_le_iff₀ hpos, Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, ← abs_mul]
    have h1 := hTmin m' (T m) (hT m)
    have h2 := hTmin m (T m') (hT m')
    have hle : h (T m') - m' * T m' - (h (T m) - m * T m) - (m' - m) * -T m ≤ 0 := by
      linarith
    have hge : (m' - m) * (T m - T m') ≤
        h (T m') - m' * T m' - (h (T m) - m * T m) - (m' - m) * -T m := by
      linarith
    rw [abs_of_nonpos hle]
    calc -(h (T m') - m' * T m' - (h (T m) - m * T m) - (m' - m) * -T m)
        ≤ -((m' - m) * (T m - T m')) := neg_le_neg hge
      _ = (m' - m) * (T m' - T m) := by ring
      _ ≤ |(m' - m) * (T m' - T m)| := le_abs_self _
  refine ⟨T, fun m => h (T m) - m * T m, hT, fun m => rfl, fun m s hs => ?_,
    fun m t ht hsup => huniq m t ht fun s hs => ?_, hmono, hcont, hderiv⟩
  · have := hTmin m s hs
    linarith
  · have := hsup s hs
    linarith
