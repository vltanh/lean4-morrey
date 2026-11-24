module

public import Morrey.HomogeneousIsotropic.Signed.Minorant
public import Morrey.HomogeneousIsotropic.Signed.BurkholderRadial

/-!
# Jensen's inequality at the matrices with two nonzero coordinates

Let `F` be isotropic, positively `p`-homogeneous and rank-one convex on `ℝ^{2×2}`, `p > 1`,
`p ≠ 2`, and let the slice `h` of its profile be strictly convex on `[−1, 1]` with `h (−1) < 0`.
Let `A₀` have nonzero conformal and anticonformal parts, `σ₀ = |z₀| + |w₀|`,
`t₀ = (|z₀| − |w₀|)/σ₀ ∈ (−1, 1)`, and let `m₀` be a supporting slope of `h` at `t₀`; it is
positive.

* If the supporting line is nonnegative at `−a`, `a = |p − 2|/p`, the Burkholder-type function
  with that line lies below `F`, touches it at `A₀`, and is a nonnegative combination of the
  Burkholder function and of `|A|^p` (`burkholderTypeCoord_eq_burkholder_add`), hence
  quasiconvex (`quasiconvex_burkholderTypeCoord_of_two_lt` for `p > 2`,
  `quasiconvex_burkholderTypeCoord_of_lt_two` for `p < 2`): the Burkholder function is
  quasiconvex by Proposition 6.8 (`quasiconvex_burkholder_of_one_lt`).
* Otherwise `(t₀, m₀)` is a hard base. For a Lipschitz test map `φ`, the matrices `A₀ + ∇φ` have
  operator norm at most `R σ₀` for some `R ≥ 1`; with the function `N` of
  `IsHardBase.exists_convex_minorant` for this `R`, the function
  `X ↦ σ₀^p (α₀ + radial e N (X/σ₀))` is quasiconvex (`quasiconvex_radial`), lies below `F` on
  the matrices of operator norm at most `R σ₀`, and equals `F` at `A₀`
  (`quasiconvexAtOn_of_isHardBase`).

In both cases Jensen's inequality for `F` at `A₀` follows
(`quasiconvexAtOn_of_strictConvexOn_slice`).
-/

@[expose] public section

open Set CalculusOfVariations MeasureTheory

namespace HomogeneousIsotropic

variable {p : ℝ} {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}

/-! ### The power of the operator norm -/

/-- A convex function on `ℝ^{2×2}` is quasiconvex. -/
theorem quasiconvex_of_convexOn {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    Quasiconvex f :=
  Polyconvex.quasiconvex ⟨fun y => f y.1, ⟨convex_univ, fun x _ y _ _ _ ha hb hab =>
    hf.2 (mem_univ x.1) (mem_univ y.1) ha hb hab⟩, fun _ => rfl⟩

/-- `A ↦ (|z| + |w|)^p`, the `p`-th power of the operator norm, is convex for `p ≥ 1`. -/
theorem convexOn_norm_add_norm_rpow (hp : 1 ≤ p) :
    ConvexOn ℝ univ fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ p := by
  refine ⟨convex_univ, fun A _ B _ a b ha hb hab => ?_⟩
  have hz : ‖conformalPart (a • A + b • B)‖ ≤ a * ‖conformalPart A‖ + b * ‖conformalPart B‖ := by
    rw [conformalPart_add, conformalPart_smul, conformalPart_smul]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  have hw : ‖anticonformalPart (a • A + b • B)‖ ≤
      a * ‖anticonformalPart A‖ + b * ‖anticonformalPart B‖ := by
    rw [anticonformalPart_add, anticonformalPart_smul, anticonformalPart_smul]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  have hA : 0 ≤ ‖conformalPart A‖ + ‖anticonformalPart A‖ := by positivity
  have hB : 0 ≤ ‖conformalPart B‖ + ‖anticonformalPart B‖ := by positivity
  have h1 : (‖conformalPart (a • A + b • B)‖ + ‖anticonformalPart (a • A + b • B)‖) ^ p ≤
      (a * (‖conformalPart A‖ + ‖anticonformalPart A‖) +
        b * (‖conformalPart B‖ + ‖anticonformalPart B‖)) ^ p :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have h2 := (convexOn_rpow hp).2 (mem_Ici.2 hA) (mem_Ici.2 hB) ha hb hab
  simp only [smul_eq_mul] at h2 ⊢
  exact h1.trans h2

/-- `A ↦ (|z| + |w|)^p` is continuous for `p ≥ 0`. -/
theorem continuous_norm_add_norm_rpow (hp : 0 ≤ p) :
    Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ p :=
  (Real.continuous_rpow_const hp).comp
    (continuous_norm_conformalPart.add continuous_norm_anticonformalPart)

/-! ### The Burkholder-type functions at the easy bases -/

/-- **The identity (6.1).** For `p ≠ 0`, a Burkholder-type function is
`G_{c₀,m} = m B_p + (c₀ − |1 − 2/p| m) |A|^p`, with `|A| = |z| + |w|`. -/
theorem burkholderTypeCoord_eq_burkholder_add (hp : p ≠ 0) (c₀ m : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderTypeCoord p c₀ m A = m * burkholder p A +
      (c₀ - |1 - 2 / p| * m) * (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ p := by
  have hpow : (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ p =
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
        (‖conformalPart A‖ + ‖anticonformalPart A‖) := by
    rw [← Real.rpow_add_one' (by positivity) (by rwa [sub_add_cancel])]
    congr 1
    ring
  rw [burkholder_eq_burkholderTypeCoord, burkholderTypeCoord, burkholderTypeCoord, hpow]
  ring

/-- **Lemma 6.4.** For `p > 2`, a Burkholder-type function with `m ≥ 0` and `(p − 2) m ≤ p c₀` is
quasiconvex: it is `m B_p + ((p c₀ − (p − 2) m)/p) |A|^p`, a nonnegative combination of the
Burkholder function and of the convex function `|A|^p`. -/
theorem quasiconvex_burkholderTypeCoord_of_two_lt (hp : 2 < p) {c₀ m : ℝ} (hm : 0 ≤ m)
    (hc : (p - 2) * m ≤ p * c₀) : Quasiconvex (burkholderTypeCoord p c₀ m) := by
  have hp0 : 0 < p := by linarith
  have hcm : 0 ≤ c₀ - |1 - 2 / p| * m := by
    have ha : |1 - 2 / p| * m = (p - 2) * m / p := by
      rw [abs_of_nonneg (by rw [sub_nonneg, div_le_one hp0]; linarith)]
      field_simp
    rw [ha, sub_nonneg, div_le_iff₀ hp0]
    linarith
  have h := quasiconvex_add_mul hm hcm (quasiconvex_burkholder_of_one_lt (p := p) (by linarith))
    (continuous_burkholder (p := p) (by linarith))
    (quasiconvex_of_convexOn (convexOn_norm_add_norm_rpow (p := p) (by linarith)))
    (continuous_norm_add_norm_rpow (p := p) (by linarith))
  rw [funext (burkholderTypeCoord_eq_burkholder_add hp0.ne' c₀ m)]
  exact h

/-- For `1 < p < 2`, a Burkholder-type function with `(2 − p) |m| ≤ p c₀` is quasiconvex: a
nonnegative combination of the Burkholder function and of its mirror image (Theorem 1.5). -/
theorem quasiconvex_burkholderTypeCoord_of_lt_two (hp1 : 1 < p) (hp2 : p < 2) {c₀ m : ℝ}
    (hc : (2 - p) * |m| ≤ p * c₀) : Quasiconvex (burkholderTypeCoord p c₀ m) :=
  quasiconvex_burkholderTypeCoord hp1.le hp2 hc (quasiconvex_burkholderCoord hp1 hp2.le)

/-! ### Jensen's inequality -/

/-- **Jensen's inequality at a hard base.** Let `A₀` have nonzero coordinates, and let
`t₀ = (|z₀| − |w₀|)/(|z₀| + |w₀|)` be a hard base of the profile of `F` with the slope `m₀`.
For a test map `φ`, the function `N` of `IsHardBase.exists_convex_minorant` for a large `R` gives
a quasiconvex function that lies below `F` at all the matrices `A₀ + ∇φ` and equals `F` at
`A₀`. -/
theorem quasiconvexAtOn_of_isHardBase {e : ℝ} (hp1 : 1 < p) (he : e = 1 ∨ e = -1)
    (hpe : 0 < e * (p - 2)) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : RankOneConvex F) (hsc : StrictConvexOn ℝ (Icc (-1) 1) (slice (profile F)))
    (hor : slice (profile F) (-1) < 0) {A₀ : Matrix (Fin 2) (Fin 2) ℝ}
    (hσ : 0 < ‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) {m₀ : ℝ}
    (hb : IsHardBase p e (profile F)
      ((‖conformalPart A₀‖ - ‖anticonformalPart A₀‖) /
        (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖)) m₀) :
    QuasiconvexAtOn (unitCube 2) F A₀ := by
  have hΦ := isProfile_profile hiso hhom hrc
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ = ‖conformalPart A₀‖ := ⟨_, rfl⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, y₀ = ‖anticonformalPart A₀‖ := ⟨_, rfl⟩
  rw [← hx₀, ← hy₀] at hσ hb
  have hx₀0 : 0 ≤ x₀ := by rw [hx₀]; exact norm_nonneg _
  have hy₀0 : 0 ≤ y₀ := by rw [hy₀]; exact norm_nonneg _
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = x₀ + y₀ := ⟨_, rfl⟩
  rw [← hσ₀] at hσ hb
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = (x₀ - y₀) / σ₀ := ⟨_, rfl⟩
  rw [← ht₀] at hb
  have hxt : σ₀⁻¹ * x₀ = (1 + t₀) / 2 := by
    rw [ht₀]
    field_simp
    rw [hσ₀]
    ring
  have hyt : σ₀⁻¹ * y₀ = (1 - t₀) / 2 := by
    rw [ht₀]
    field_simp
    rw [hσ₀]
    ring
  have hσp : 0 < σ₀ ^ p := Real.rpow_pos_of_pos hσ p
  have hinv : 0 < σ₀⁻¹ := inv_pos.2 hσ
  intro φ K hφ h0 hI
  -- the radius and the function `N`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 1 + 4 * K / σ₀ := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by
    rw [hR]
    have : 0 ≤ 4 * (K : ℝ) / σ₀ := by positivity
    linarith
  have hRσ : R * σ₀ = σ₀ + 4 * K := by
    rw [hR]
    field_simp
  obtain ⟨N, hNconv, hN0, hle, heq⟩ := hb.exists_convex_minorant hΦ hp1 he hpe hsc hor hR1
  have hNc : Continuous N := continuousOn_univ.1 (hNconv.continuousOn isOpen_univ)
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : ℝ, α₀ = supportConst p e (slice (profile F) t₀) m₀ t₀ := ⟨_, rfl⟩
  rw [← hα₀] at hle heq
  -- the minorant
  have hqc : Quasiconvex fun X : Matrix (Fin 2) (Fin 2) ℝ =>
      σ₀ ^ p * (α₀ + radial e N (σ₀⁻¹ • X)) :=
    Agazzi.quasiconvex_const_mul (quasiconvex_comp_smul (quasiconvex_const_add
      (quasiconvex_radial he (hNconv.subset (subset_univ _) (convex_Ici 0)) hNc hN0) α₀) σ₀⁻¹)
      hσp
  have hrc : Continuous fun X : Matrix (Fin 2) (Fin 2) ℝ => radial e N (σ₀⁻¹ • X) :=
    (continuous_radial e hNc).comp (continuous_const_smul σ₀⁻¹)
  have hGc : Continuous fun X : Matrix (Fin 2) (Fin 2) ℝ =>
      σ₀ ^ p * (α₀ + radial e N (σ₀⁻¹ • X)) :=
    continuous_const.mul (continuous_const.add hrc)
  have hrad : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, radial e N (σ₀⁻¹ • X) =
      radialProfile e N (σ₀⁻¹ * ‖conformalPart X‖) (σ₀⁻¹ * ‖anticonformalPart X‖) := by
    intro X
    rw [radial, conformalPart_smul, anticonformalPart_smul, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hinv]
  have hhom' : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      profile F x y = σ₀ ^ p * profile F (σ₀⁻¹ * x) (σ₀⁻¹ * y) := by
    intro x y hx hy
    have h := hΦ.homog σ₀ (σ₀⁻¹ * x) (σ₀⁻¹ * y) hσ (mul_nonneg hinv.le hx)
      (mul_nonneg hinv.le hy)
    rwa [mul_inv_cancel_left₀ hσ.ne', mul_inv_cancel_left₀ hσ.ne'] at h
  have hGle : ∀ X : Matrix (Fin 2) (Fin 2) ℝ,
      ‖conformalPart X‖ + ‖anticonformalPart X‖ ≤ R * σ₀ →
        σ₀ ^ p * (α₀ + radial e N (σ₀⁻¹ • X)) ≤ F X := by
    intro X hX
    have hsum : σ₀⁻¹ * ‖conformalPart X‖ + σ₀⁻¹ * ‖anticonformalPart X‖ ≤ R := by
      rw [← mul_add]
      calc σ₀⁻¹ * (‖conformalPart X‖ + ‖anticonformalPart X‖) ≤ σ₀⁻¹ * (R * σ₀) :=
            mul_le_mul_of_nonneg_left hX hinv.le
        _ = R := by field_simp
    have h := hle _ _ (mul_nonneg hinv.le (norm_nonneg (conformalPart X)))
      (mul_nonneg hinv.le (norm_nonneg (anticonformalPart X))) hsum
    rw [hrad, hiso.eq_profile X, hhom' _ _ (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left h hσp.le
  have hGeq : σ₀ ^ p * (α₀ + radial e N (σ₀⁻¹ • A₀)) = F A₀ := by
    rw [hrad, hiso.eq_profile A₀, ← hx₀, ← hy₀, hhom' _ _ hx₀0 hy₀0, hxt, hyt, heq, slice]
  -- the matrices `A₀ + ∇φ` are in the region where the minorant is below `F`
  have hbound : ∀ x, ‖conformalPart (A₀ + grad φ x)‖ + ‖anticonformalPart (A₀ + grad φ x)‖ ≤
      R * σ₀ := by
    intro x
    have h1 := norm_add_norm_add_grad_le hφ A₀ x
    rw [hRσ, hσ₀, hx₀, hy₀]
    linarith
  have hGI := nl_integrableOn_cube hφ hGc A₀ (unitCube 2) volume_unitCube_two_ne_top
  rw [← hGeq]
  exact (hqc A₀ φ K hφ h0 hGI).trans (setIntegral_mono hGI hI fun x => hGle _ (hbound x))

/-- Let `F` be isotropic, positively `p`-homogeneous and rank-one convex, `p > 1`, `p ≠ 2`, with
the slice of its profile strictly convex on `[−1, 1]` and negative at `−1`. Then `F` is
quasiconvex at every matrix whose conformal and anticonformal parts are both nonzero. -/
theorem quasiconvexAtOn_of_strictConvexOn_slice (hp1 : 1 < p) (hp2 : p ≠ 2)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F)
    (hsc : StrictConvexOn ℝ (Icc (-1) 1) (slice (profile F)))
    (hor : slice (profile F) (-1) < 0) {A₀ : Matrix (Fin 2) (Fin 2) ℝ}
    (hz : conformalPart A₀ ≠ 0) (hw : anticonformalPart A₀ ≠ 0) :
    QuasiconvexAtOn (unitCube 2) F A₀ := by
  have hΦ := isProfile_profile hiso hhom hrc
  have hp0 : 0 < p := by linarith
  obtain ⟨e, he, hpe⟩ : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ 0 < e * (p - 2) := by
    rcases lt_or_gt_of_ne hp2 with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  have hx₀ : 0 < ‖conformalPart A₀‖ := norm_pos_iff.2 hz
  have hy₀ : 0 < ‖anticonformalPart A₀‖ := norm_pos_iff.2 hw
  have hσ : 0 < ‖conformalPart A₀‖ + ‖anticonformalPart A₀‖ := add_pos hx₀ hy₀
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = (‖conformalPart A₀‖ - ‖anticonformalPart A₀‖) /
      (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) := ⟨_, rfl⟩
  have ht1 : -1 < t₀ := by
    rw [ht₀, lt_div_iff₀ hσ]
    linarith
  have ht2 : t₀ < 1 := by
    rw [ht₀, div_lt_iff₀ hσ]
    linarith
  have habs : |t₀| < 1 := abs_lt.2 ⟨ht1, ht2⟩
  obtain ⟨m₀, hmin⟩ := hΦ.exists_burkholderMinorant hp0 ht1.le ht2.le
  replace hmin : BurkholderMinorant p (slice (profile F) t₀ - m₀ * t₀) m₀ (profile F) := hmin
  have hm : 0 < m₀ := hΦ.slope_pos hp0 hor ht1 ht2.le hmin
  by_cases hg : 0 ≤ p * (slice (profile F) t₀ - m₀ * t₀) - e * (p - 2) * m₀
  · -- the supporting line is nonnegative at `−a`: a Burkholder-type minorant
    have hle : ∀ A, burkholderTypeCoord p (slice (profile F) t₀ - m₀ * t₀) m₀ A ≤ F A := by
      intro A
      rw [hiso.eq_profile A]
      exact hmin _ _ (norm_nonneg _) (norm_nonneg _)
    have heq : burkholderTypeCoord p (slice (profile F) t₀ - m₀ * t₀) m₀ A₀ = F A₀ := by
      have hxs : (1 + t₀) / 2 = ‖conformalPart A₀‖ /
          (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) := by
        rw [ht₀]
        field_simp
        ring
      have hys : (1 - t₀) / 2 = ‖anticonformalPart A₀‖ /
          (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) := by
        rw [ht₀]
        field_simp
        ring
      have hpow : (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) ^ p =
          (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) ^ (p - 1) *
            (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) := by
        rw [← Real.rpow_add_one hσ.ne']
        congr 1
        ring
      have hF : F A₀ = (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) ^ p *
          slice (profile F) t₀ := by
        rw [hiso.eq_profile A₀, hΦ.eq_rpow_mul hx₀.le hy₀.le hσ, slice, hxs, hys]
      have hd : ‖conformalPart A₀‖ - ‖anticonformalPart A₀‖ =
          t₀ * (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) := by
        rw [ht₀]
        field_simp
      rw [hF, burkholderTypeCoord, hpow, hd]
      ring
    have hqc : Quasiconvex (burkholderTypeCoord p (slice (profile F) t₀ - m₀ * t₀) m₀) := by
      rcases he with rfl | rfl
      · exact quasiconvex_burkholderTypeCoord_of_two_lt (by linarith) hm.le (by linarith)
      · exact quasiconvex_burkholderTypeCoord_of_lt_two hp1 (by linarith)
          (by rw [abs_of_pos hm]; linarith)
    exact quasiconvexAtOn_of_le_of_eq (hqc A₀) (continuous_burkholderTypeCoord hp1.le _ _) hle heq
  · -- a hard base
    have hb : IsHardBase p e (profile F) t₀ m₀ := ⟨habs, hmin, not_le.1 hg⟩
    rw [ht₀] at hb
    exact quasiconvexAtOn_of_isHardBase hp1 he hpe hiso hhom hrc hsc hor hσ hb

end HomogeneousIsotropic
