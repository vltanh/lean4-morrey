module

public import Morrey.HomogeneousIsotropic.Signed.Basic
public import Morrey.Common.Basic.Analysis.Convex.Legendre
public import Morrey.Common.Basic.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# The path of hard bases

Let `Φ` be a profile of degree `p > 1`, `p ≠ 2`, whose slice `h` is strictly convex on
`[−1, 1]`, and let `(t₀, m₀)` be a hard base. For a slope `m` let `T m` be the point of
`[−1, 1]` where the line of slope `m` supports `h`, and `k m` its intercept
(`StrictConvexOn.exists_legendre`); `g m = k m − a m` is the value of that line at `−a`,
`a = e (p − 2)/p`, and `g m₀ < 0`.

* `IsHardBase.exists_isPath`: for every `R ≥ 1` there is a path of hard bases (`IsPath`) from
  `(t₀, m₀)`, with the slopes `m₀ − e ξ`, `ξ ∈ [0, L]`, along which the scale `S`, the solution of
  `S' = −S (1 + e T)/(p g)`, `S 0 = 1`, grows from `1` to `R`. The slopes move towards a
  supporting slope of `h` at `−a`, where `g ≥ 0`; up to the first zero `ξ_∞` of `g`, the points
  `T` stay between `t₀` and `−a`, and `S = exp (∫₀^ξ −(1 + e T)/(p g))` tends to `∞` at `ξ_∞`,
  since `|g| ≤ 2 (ξ_∞ − ξ)`.

Two general facts about primitives are used
(`Morrey/Common/Basic/MeasureTheory/Integral/IntervalIntegral/Primitive.lean`):

* `intervalIntegral.hasDerivAt_exp_integral`: the derivative of `u ↦ exp (∫₀^u ρ)`, for `ρ`
  continuous on an open set;
* `intervalIntegral.exists_exp_integral_eq`: if `ρ ≥ κ/(b − x)` on `[0, b)` with `κ > 0`, then
  `exp (∫₀^x ρ)` takes every value `R ≥ 1` on `[0, b)`.
-/

@[expose] public section

open Set MeasureTheory

namespace HomogeneousIsotropic

variable {p e : ℝ} {Φ : ℝ → ℝ → ℝ}

/-- **The path of hard bases.** Let the slice of the profile `Φ` of degree `p > 1`, `p ≠ 2`, be
strictly convex on `[−1, 1]`. From every hard base `(t₀, m₀)` and for every `R ≥ 1` there is a
path of hard bases along which the scale grows from `1` to `R`. -/
theorem IsHardBase.exists_isPath (hΦ : IsProfile p Φ) (hp : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) (hsc : StrictConvexOn ℝ (Icc (-1) 1) (slice Φ))
    {t₀ m₀ : ℝ} (hb : IsHardBase p e Φ t₀ m₀) {R : ℝ} (hR : 1 ≤ R) :
    ∃ (L : ℝ) (T k S : ℝ → ℝ), IsPath p e Φ t₀ m₀ L R T k S := by
  have hp0 : 0 < p := by linarith
  have he2 : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have habs : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
  -- the Legendre transform of the slice
  obtain ⟨Tl, kl, hTmem, hkl, hmin, huniq, hTmono, hTcont, hkder⟩ :=
    hsc.exists_legendre (by norm_num) hΦ.continuousOn_slice
  obtain ⟨ht₀1, ht₀2⟩ := _root_.abs_lt.1 hb.abs_lt
  have hT₀ : Tl m₀ = t₀ := huniq m₀ t₀ ⟨ht₀1.le, ht₀2.le⟩
    ((hΦ.burkholderMinorant_slice_iff hp0).1 hb.minorant)
  -- the point `−a` and a supporting slope there
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = e * (p - 2) / p := ⟨_, rfl⟩
  have hpa : p * a = e * (p - 2) := by rw [ha]; field_simp
  have ha0 : 0 < a := by rw [ha]; exact div_pos hpe hp0
  have ha1 : a < 1 := by
    rw [ha, div_lt_one hp0]
    rcases he with rfl | rfl <;> linarith
  obtain ⟨ma, hma⟩ := hΦ.exists_burkholderMinorant hp0 (t := -a) (by linarith) (by linarith)
  have hma' : ∀ s ∈ Icc (-1 : ℝ) 1, slice Φ (-a) + ma * (s - -a) ≤ slice Φ s :=
    (hΦ.burkholderMinorant_slice_iff hp0).1 hma
  have hTa : Tl ma = -a := huniq ma (-a) ⟨by linarith, by linarith⟩ hma'
  -- the slopes `m₀ − e ξ` reach `ma` at `ξa > 0`
  have hbp := hb.base_pos hΦ hp he hpe
  obtain ⟨ξa, hξa⟩ : ∃ ξa : ℝ, ξa = -e * (ma - m₀) := ⟨_, rfl⟩
  have hmξa : m₀ - e * ξa = ma := by rw [hξa]; linear_combination (ma - m₀) * he2
  have hξa0 : 0 < ξa := by
    by_contra hcon
    rcases he with rfl | rfl
    · have h1 : 0 < p * (t₀ + a) := by linarith
      have h2 : 0 < t₀ + a := (mul_pos_iff_of_pos_left hp0).1 h1
      have h3 := hTmono (show m₀ ≤ ma by linarith)
      rw [hT₀, hTa] at h3
      linarith
    · have h1 : 0 < p * (-a - t₀) := by linarith
      have h2 : 0 < -a - t₀ := (mul_pos_iff_of_pos_left hp0).1 h1
      have h3 := hTmono (show ma ≤ m₀ by linarith)
      rw [hT₀, hTa] at h3
      linarith
  -- the path, in the parameter `ξ`
  obtain ⟨T, hT⟩ : ∃ T : ℝ → ℝ, ∀ ξ, T ξ = Tl (m₀ - e * ξ) := ⟨_, fun _ => rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℝ, ∀ ξ, k ξ = kl (m₀ - e * ξ) := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ ξ, G ξ = p * k ξ - e * (p - 2) * (m₀ - e * ξ) :=
    ⟨_, fun _ => rfl⟩
  have hTc : Continuous T := by
    rw [funext hT]
    exact hTcont.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hT1 : ∀ ξ, |T ξ| ≤ 1 := fun ξ => by
    rw [hT]
    exact abs_le.2 (hTmem _)
  have hin : ∀ ξ : ℝ, HasDerivAt (fun ξ : ℝ => m₀ - e * ξ) (-e) ξ := fun ξ => by
    simpa using ((hasDerivAt_id ξ).const_mul e).const_sub m₀
  have hkd : ∀ ξ, HasDerivAt k (e * T ξ) ξ := fun ξ => by
    have h := (hkder (m₀ - e * ξ)).comp ξ (hin ξ)
    have hfun : k = kl ∘ fun ξ : ℝ => m₀ - e * ξ := funext hk
    rw [hfun, hT]
    convert h using 1
    ring
  have hGd : ∀ ξ, HasDerivAt G (p * (e * T ξ) + (p - 2)) ξ := fun ξ => by
    have h := ((hkd ξ).const_mul p).sub ((hin ξ).const_mul (e * (p - 2)))
    rw [funext hG]
    convert h using 1
    linear_combination -(p - 2) * he2
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun ξ => (hGd ξ).continuousAt
  have hG0 : G 0 < 0 := by
    rw [hG, hk, mul_zero, sub_zero, hkl, hT₀]
    exact hb.neg
  have hGa : 0 ≤ G ξa := by
    have hsl := hΦ.slice_neg_nonneg hp he hpe
    rw [← ha] at hsl
    rw [hG, hk, hmξa, hkl, hTa]
    have e1 : p * (slice Φ (-a) - ma * -a) - e * (p - 2) * ma = p * slice Φ (-a) := by
      linear_combination ma * hpa
    rw [e1]
    exact mul_nonneg hp0.le hsl
  -- the first zero `b` of `G`
  obtain ⟨b, hbmem, hbleast⟩ : ∃ b, IsLeast {ξ | ξ ∈ Icc 0 ξa ∧ 0 ≤ G ξ} b := by
    have hcl : IsClosed {ξ | ξ ∈ Icc 0 ξa ∧ 0 ≤ G ξ} :=
      isClosed_Icc.inter (isClosed_le continuous_const hGc)
    exact (isCompact_Icc.of_isClosed_subset hcl fun x hx => hx.1).exists_isLeast
      ⟨ξa, ⟨hξa0.le, le_rfl⟩, hGa⟩
  have hb0 : 0 < b := by
    rcases hbmem.1.1.eq_or_lt with h | h
    · rw [← h] at hbmem
      exact absurd hbmem.2 (not_le.2 hG0)
    · exact h
  have hGneg : ∀ ξ ∈ Ico 0 b, G ξ < 0 := by
    intro ξ hξ
    by_contra hcon
    have := hbleast ⟨⟨hξ.1, hξ.2.le.trans hbmem.1.2⟩, not_lt.1 hcon⟩
    linarith [hξ.2]
  -- the base points stay between `t₀` and `−a`
  have hθ1 : max |t₀| a < 1 := max_lt hb.abs_lt ha1
  have hTθ : ∀ ξ ∈ Icc 0 ξa, |T ξ| ≤ max |t₀| a := by
    intro ξ hξ
    rw [hT, abs_le]
    have h1 := le_max_left |t₀| a
    have h2 := le_max_right |t₀| a
    have h3 := neg_abs_le t₀
    have h4 := le_abs_self t₀
    rcases he with rfl | rfl
    · have h5 := hTmono (show ma ≤ m₀ - 1 * ξ by rw [← hmξa]; linarith [hξ.2])
      have h6 := hTmono (show m₀ - 1 * ξ ≤ m₀ by linarith [hξ.1])
      rw [hTa] at h5
      rw [hT₀] at h6
      constructor <;> linarith
    · have h5 := hTmono (show m₀ - -1 * ξ ≤ ma by rw [← hmξa]; linarith [hξ.2])
      have h6 := hTmono (show m₀ ≤ m₀ - -1 * ξ by linarith [hξ.1])
      rw [hTa] at h5
      rw [hT₀] at h6
      constructor <;> linarith
  -- the scale
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ → ℝ, ∀ ξ, ρ ξ = -(1 + e * T ξ) / G ξ := ⟨_, fun _ => rfl⟩
  have hUo : IsOpen {ξ | G ξ < 0} := isOpen_lt hGc continuous_const
  have hρc : ContinuousOn ρ {ξ | G ξ < 0} := by
    rw [funext hρ]
    exact ContinuousOn.div (continuous_const.add (continuous_const.mul hTc)).neg.continuousOn
      hGc.continuousOn fun ξ hξ => ne_of_lt hξ
  have hGb : ∀ ξ ∈ Ico 0 b, -G ξ ≤ 2 * p * (b - ξ) := by
    intro ξ hξ
    have hmono : Monotone fun x => 2 * p * x - G x := by
      have hd : ∀ x, HasDerivAt (fun x => 2 * p * x - G x)
          (2 * p * 1 - (p * (e * T x) + (p - 2))) x := fun x =>
        ((hasDerivAt_id x).const_mul (2 * p)).sub (hGd x)
      refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) fun x => ?_
      rw [(hd x).deriv]
      have h1 : e * T x ≤ 1 := by
        have := le_abs_self (e * T x)
        rw [abs_mul, habs, one_mul] at this
        exact this.trans (hT1 x)
      nlinarith
    have h := hmono hξ.2.le
    simp only at h
    linarith [hbmem.2]
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - max |t₀| a) / (2 * p) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; exact div_pos (by linarith) (by linarith)
  have hρlow : ∀ ξ ∈ Ico 0 b, κ / (b - ξ) ≤ ρ ξ := by
    intro ξ hξ
    have hGξ := hGneg ξ hξ
    have hbξ : 0 < b - ξ := sub_pos.2 hξ.2
    have hnum : 1 - max |t₀| a ≤ 1 + e * T ξ := by
      have h1 := neg_abs_le (e * T ξ)
      rw [abs_mul, habs, one_mul] at h1
      linarith [hTθ ξ ⟨hξ.1, hξ.2.le.trans hbmem.1.2⟩]
    have e1 : ρ ξ = (1 + e * T ξ) / (-G ξ) := by rw [hρ, neg_div, div_neg]
    rw [e1, hκ, div_div, div_le_div_iff₀ (by positivity) (by linarith)]
    calc (1 - max |t₀| a) * -G ξ ≤ (1 - max |t₀| a) * (2 * p * (b - ξ)) :=
          mul_le_mul_of_nonneg_left (hGb ξ hξ) (by linarith)
      _ ≤ (1 + e * T ξ) * (2 * p * (b - ξ)) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
  obtain ⟨L, hL, hLR⟩ := intervalIntegral.exists_exp_integral_eq hUo hρc
    (fun ξ hξ => hGneg ξ hξ) hb0 hκ0 hρlow hR
  have hLsub : ∀ ξ ∈ Icc 0 L, ξ ∈ Ico 0 b := fun ξ hξ => ⟨hξ.1, hξ.2.trans_lt hL.2⟩
  refine ⟨L, T, k, fun ξ => Real.exp (∫ y in (0 : ℝ)..ξ, ρ y), ?_⟩
  exact
    { length_nonneg := hL.1
      hard := fun ξ hξ => by
        have hξb := hLsub ξ hξ
        refine ⟨(hTθ ξ ⟨hξb.1, hξb.2.le.trans hbmem.1.2⟩).trans_lt hθ1, ?_, ?_⟩
        · refine (hΦ.burkholderMinorant_slice_iff hp0).2 fun s hs => ?_
          have h := hmin (m₀ - e * ξ) s hs
          rw [hkl] at h
          rw [hT]
          linarith
        · have h := hGneg ξ hξb
          rw [hG, hk, hkl] at h
          rw [hT]
          exact h
      intercept := fun ξ _ => by rw [hk, hkl, hT]
      base_zero := by rw [hT, mul_zero, sub_zero, hT₀]
      continuousOn_base := hTc.continuousOn
      hasDerivAt_intercept := fun ξ _ => hkd ξ
      scale_zero := by simp
      scale_length := hLR
      scale_pos := fun ξ _ => Real.exp_pos _
      hasDerivAt_scale := fun ξ hξ => by
        have hξb := hLsub ξ hξ
        have h := intervalIntegral.hasDerivAt_exp_integral hUo hρc (x := ξ) fun y hy => by
          rw [uIcc_of_le hξb.1] at hy
          exact hGneg y ⟨hy.1, hy.2.trans_lt hξb.2⟩
        convert h using 1
        rw [hρ, hG]
        ring }

end HomogeneousIsotropic
