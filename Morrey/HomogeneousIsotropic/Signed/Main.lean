module

public import Morrey.HomogeneousIsotropic.Signed.Interior
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Isotropic, positively homogeneous, rank-one convex integrands on `ℝ^{2×2}` are quasiconvex

* `quasiconvex_of_rankOneConvex_of_isotropic`: for every `p > 0`, an isotropic, positively
  `p`-homogeneous, rank-one convex `F : ℝ^{2×2} → ℝ` is quasiconvex.

For `F ≥ 0`, for `p = 2`, for `p = 1` and for `0 < p < 1` this is in
`Morrey/HomogeneousIsotropic/Main.lean` and `Signed/BurkholderRadial.lean`. Let `p > 1`, `p ≠ 2`,
and let `F` have a negative value. The slice `h` of the profile is then negative at `−1` or at
`1`, and the reflection `A ↦ F (J A)` exchanges the two cases. The integrands
`F + ε (|z|^p + |w|^p)`, `ε > 0` small, satisfy the same hypotheses and their slices are strictly
convex, so that they are quasiconvex at the matrices with two nonzero coordinates
(`quasiconvexAtOn_of_strictConvexOn_slice`); these matrices are dense and both sides of Jensen's
inequality for a fixed test map are continuous in the matrix; finally `ε → 0`.

The steps:

* `isIsotropic_comp_reflection_mul`, `IsPosHomogeneous.comp_reflection_mul`,
  `rankOneConvex_comp_reflection_mul`, `slice_profile_comp_reflection_mul_neg_one`: the
  integrand `A ↦ F (J A)` satisfies the hypotheses, and its slice at `−1` is the slice of `F`
  at `1`.
* `coordPowSum p`: the integrand `A ↦ |z|^p + |w|^p`; it is isotropic, positively
  `p`-homogeneous and, for `p ≥ 1`, rank-one convex; `strictConvexOn_add_mul_rpow`: adding a
  positive multiple of its slice to a convex function on `[−1, 1]` gives a strictly convex one,
  for `p > 1`.
* `quasiconvex_of_forall_ne_zero`: a continuous integrand that is quasiconvex at the matrices
  with two nonzero coordinates is quasiconvex.
* `quasiconvex_of_strictConvexOn_slice`, `quasiconvex_of_slice_neg_one_neg`: quasiconvexity when
  the slice is strictly convex and negative at `−1`, then when it is negative at `−1`.
-/

@[expose] public section

open Set CalculusOfVariations MeasureTheory Filter Topology

namespace HomogeneousIsotropic

variable {p : ℝ} {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}

/-! ### The reflection -/

/-- The reflection `J = diag (1, −1)` is an involution. -/
theorem reflection_mul_reflection : reflection * reflection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflection, Matrix.mul_apply, Fin.sum_univ_two]

/-- An isotropic function at `J A` is its profile at `(|w|, |z|)`: the reflection exchanges the
moduli of the conformal and of the anticonformal part. -/
theorem IsIsotropic.apply_reflection_mul (hiso : IsIsotropic F)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    F (reflection * A) = profile F ‖anticonformalPart A‖ ‖conformalPart A‖ := by
  rw [hiso.eq_profile, conformalPart_reflection_mul, anticonformalPart_reflection_mul,
    RCLike.norm_conj, RCLike.norm_conj]

/-- If `F` is isotropic, so is `A ↦ F (J A)`. -/
theorem isIsotropic_comp_reflection_mul (hiso : IsIsotropic F) :
    IsIsotropic fun A => F (reflection * A) :=
  isIsotropic_of_eq (Φ := fun x y => profile F y x) fun A => hiso.apply_reflection_mul A

/-- If `F` is positively `p`-homogeneous, so is `A ↦ F (J A)`. -/
theorem IsPosHomogeneous.comp_reflection_mul (hhom : IsPosHomogeneous p F) :
    IsPosHomogeneous p fun A => F (reflection * A) := by
  intro c hc A
  simp only [Matrix.mul_smul]
  exact hhom c hc _

/-- If `F` is rank-one convex, so is `A ↦ F (J A)`. -/
theorem rankOneConvex_comp_reflection_mul (hrc : RankOneConvex F) :
    RankOneConvex fun A => F (reflection * A) := by
  intro A B hB
  have hJ : IsUnit reflection.det := by simp [reflection, Matrix.det_fin_two]
  have hB' : (reflection * B).rank = 1 := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ hJ, hB]
  have h := hrc (reflection * A) (reflection * B) hB'
  have he : (fun t : ℝ => F (reflection * (A + t • B))) =
      fun t : ℝ => F (reflection * A + t • (reflection * B)) := by
    funext t
    rw [Matrix.mul_add, Matrix.mul_smul]
  rw [he]
  exact h

/-- The slice at `−1` of the profile of `A ↦ F (J A)` is the slice at `1` of the profile of
`F`. -/
theorem slice_profile_comp_reflection_mul_neg_one (hiso : IsIsotropic F) :
    slice (profile fun A => F (reflection * A)) (-1) = slice (profile F) 1 := by
  simp only [slice, profile]
  rw [hiso.apply_reflection_mul, conformalPart_ofComplex, anticonformalPart_ofComplex,
    Complex.norm_real, Complex.norm_real]
  norm_num [profile]

/-! ### The convex integrand `|z|^p + |w|^p` -/

/-- The integrand `A ↦ |z|^p + |w|^p`, for the conformal part `z` and the anticonformal part `w`
of `A`. -/
noncomputable def coordPowSum (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ‖conformalPart A‖ ^ p + ‖anticonformalPart A‖ ^ p

/-- `A ↦ |z|^p + |w|^p` is isotropic. -/
theorem isIsotropic_coordPowSum (p : ℝ) : IsIsotropic (coordPowSum p) :=
  isIsotropic_of_eq (Φ := fun x y => x ^ p + y ^ p) fun _ => rfl

/-- `A ↦ |z|^p + |w|^p` is positively `p`-homogeneous. -/
theorem isPosHomogeneous_coordPowSum (p : ℝ) : IsPosHomogeneous p (coordPowSum p) := by
  intro c hc A
  simp only [coordPowSum, conformalPart_smul, anticonformalPart_smul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [Real.mul_rpow hc.le (norm_nonneg _), Real.mul_rpow hc.le (norm_nonneg _)]
  ring

/-- `A ↦ |z|^p + |w|^p` is continuous for `p ≥ 0`. -/
theorem continuous_coordPowSum (hp : 0 ≤ p) : Continuous (coordPowSum p) :=
  (continuous_norm_conformalPart.rpow_const fun _ => Or.inr hp).add
    (continuous_norm_anticonformalPart.rpow_const fun _ => Or.inr hp)

/-- `t ↦ |z + t u|^p` is convex on `ℝ` for `p ≥ 1`. -/
theorem convexOn_norm_add_mul_rpow (hp : 1 ≤ p) (z u : ℂ) :
    ConvexOn ℝ univ fun t : ℝ => ‖z + t * u‖ ^ p := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  have h1 : ‖z + ((a • s + b • t : ℝ) : ℂ) * u‖ ≤ a * ‖z + s * u‖ + b * ‖z + t * u‖ := by
    have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
    have e : z + ((a • s + b • t : ℝ) : ℂ) * u =
        (a : ℂ) * (z + s * u) + (b : ℂ) * (z + t * u) := by
      simp only [smul_eq_mul]
      push_cast
      linear_combination (-z) * hab'
    rw [e]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  have h2 := (convexOn_rpow hp).2 (mem_Ici.2 (norm_nonneg (z + s * u)))
    (mem_Ici.2 (norm_nonneg (z + t * u))) ha hb hab
  simp only [smul_eq_mul] at h2 ⊢
  exact (Real.rpow_le_rpow (norm_nonneg _) (by simpa only [smul_eq_mul] using h1)
    (by linarith)).trans h2

/-- `A ↦ |z|^p + |w|^p` is rank-one convex for `p ≥ 1` (it is convex). -/
theorem rankOneConvex_coordPowSum (hp : 1 ≤ p) : RankOneConvex (coordPowSum p) := by
  intro A B _
  have h := (convexOn_norm_add_mul_rpow hp (conformalPart A) (conformalPart B)).add
    (convexOn_norm_add_mul_rpow hp (anticonformalPart A) (anticonformalPart B))
  have he : (fun t : ℝ => coordPowSum p (A + t • B)) =
      (fun t : ℝ => ‖conformalPart A + t * conformalPart B‖ ^ p) +
        fun t : ℝ => ‖anticonformalPart A + t * anticonformalPart B‖ ^ p := by
    funext t
    simp only [coordPowSum, conformalPart_add, conformalPart_smul, anticonformalPart_add,
      anticonformalPart_smul, Pi.add_apply]
  rw [he]
  exact h

/-- The profile of `A ↦ |z|^p + |w|^p`. -/
theorem profile_coordPowSum (p x y : ℝ) : profile (coordPowSum p) x y = |x| ^ p + |y| ^ p := by
  simp only [profile, coordPowSum, conformalPart_ofComplex, anticonformalPart_ofComplex,
    Complex.norm_real, Real.norm_eq_abs]

/-- Adding a positive multiple of the slice `|(1 + t)/2|^p + |(1 − t)/2|^p` of
`A ↦ |z|^p + |w|^p`, `p > 1`, to a convex function on `[−1, 1]` gives a strictly convex
function. -/
theorem strictConvexOn_add_mul_rpow {h : ℝ → ℝ} (hh : ConvexOn ℝ (Icc (-1) 1) h) (hp : 1 < p)
    {ε : ℝ} (hε : 0 < ε) :
    StrictConvexOn ℝ (Icc (-1) 1)
      fun t => h t + ε * (|(1 + t) / 2| ^ p + |(1 - t) / 2| ^ p) := by
  refine ⟨convex_Icc _ _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hz := (convex_Icc (-1 : ℝ) 1) hx hy ha.le hb.le hab
  have h1 := hh.2 hx hy ha.le hb.le hab
  have h2 := (strictConvexOn_rpow hp).2 (x := (1 + x) / 2) (mem_Ici.2 (by linarith [hx.1]))
    (y := (1 + y) / 2) (mem_Ici.2 (by linarith [hy.1])) (fun hcon => hxy (by linarith)) ha hb hab
  have h3 := (convexOn_rpow hp.le).2 (x := (1 - x) / 2) (mem_Ici.2 (by linarith [hx.2]))
    (y := (1 - y) / 2) (mem_Ici.2 (by linarith [hy.2])) ha.le hb.le hab
  simp only [smul_eq_mul] at hz h1 h2 h3 ⊢
  have e1 : (1 + (a * x + b * y)) / 2 = a * ((1 + x) / 2) + b * ((1 + y) / 2) := by
    linear_combination (1 / 2 : ℝ) * hab.symm
  have e2 : (1 - (a * x + b * y)) / 2 = a * ((1 - x) / 2) + b * ((1 - y) / 2) := by
    linear_combination (1 / 2 : ℝ) * hab.symm
  rw [abs_of_nonneg (by linarith [hz.1] : 0 ≤ (1 + (a * x + b * y)) / 2),
    abs_of_nonneg (by linarith [hz.2] : 0 ≤ (1 - (a * x + b * y)) / 2),
    abs_of_nonneg (by linarith [hx.1] : 0 ≤ (1 + x) / 2),
    abs_of_nonneg (by linarith [hx.2] : 0 ≤ (1 - x) / 2),
    abs_of_nonneg (by linarith [hy.1] : 0 ≤ (1 + y) / 2),
    abs_of_nonneg (by linarith [hy.2] : 0 ≤ (1 - y) / 2), e1, e2]
  have h4 := mul_lt_mul_of_pos_left h2 hε
  have h5 := mul_le_mul_of_nonneg_left h3 hε.le
  linarith

/-! ### From the matrices with two nonzero coordinates to all matrices -/

/-- A continuous integrand that is quasiconvex at every matrix whose conformal and anticonformal
parts are both nonzero is quasiconvex: these matrices are dense, and for a fixed test map both
sides of Jensen's inequality are continuous in the matrix. -/
theorem quasiconvex_of_forall_ne_zero (hFc : Continuous F)
    (h : ∀ A, conformalPart A ≠ 0 → anticonformalPart A ≠ 0 →
      QuasiconvexAtOn (unitCube 2) F A) : Quasiconvex F := by
  intro A₀ φ K hφ h0 _
  -- a direction along which both coordinates become nonzero
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = if conformalPart A₀ = 0 then 1 else conformalPart A₀ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℂ, v = if anticonformalPart A₀ = 0 then 1 else anticonformalPart A₀ :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin 2) (Fin 2) ℝ, B = ofComplex u v := ⟨_, rfl⟩
  have hne : ∀ (z w : ℂ), (w = if z = 0 then 1 else z) → ∀ n : ℕ,
      z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * w ≠ 0 := by
    intro z w hw n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_cases hz : z = 0
    · have hw1 : w = 1 := by simpa [hz] using hw
      rw [hw1, hz, zero_add, mul_one]
      exact Complex.ofReal_ne_zero.2 hpos.ne'
    · have hwz : w = z := by simpa [hz] using hw
      rw [hwz]
      have e : z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z =
          ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * z := by
        push_cast
        ring
      rw [e]
      exact mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) hz
  have hzn : ∀ n : ℕ, conformalPart (A₀ + (1 / ((n : ℝ) + 1)) • B) ≠ 0 := by
    intro n
    rw [conformalPart_add, conformalPart_smul, hB, conformalPart_ofComplex]
    exact hne _ _ hu n
  have hwn : ∀ n : ℕ, anticonformalPart (A₀ + (1 / ((n : ℝ) + 1)) • B) ≠ 0 := by
    intro n
    rw [anticonformalPart_add, anticonformalPart_smul, hB, anticonformalPart_ofComplex]
    exact hne _ _ hv n
  have hA : Tendsto (fun n : ℕ => A₀ + (1 / ((n : ℝ) + 1)) • B) atTop (𝓝 A₀) := by
    have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • B) atTop (𝓝 ((0 : ℝ) • B)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const B
    have h2 := h1.const_add A₀
    rwa [zero_smul, add_zero] at h2
  -- the two sides of Jensen's inequality converge
  have hlim1 : Tendsto (fun n : ℕ => (volume (unitCube 2)).toReal *
      F (A₀ + (1 / ((n : ℝ) + 1)) • B)) atTop (𝓝 ((volume (unitCube 2)).toReal * F A₀)) :=
    ((hFc.tendsto A₀).comp hA).const_mul _
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = K + (|B 0 0| + |B 0 1| + |B 1 0| + |B 1 1|) := ⟨_, rfl⟩
  have hBL : ∀ i k : Fin 2, |B i k| + K ≤ L := by
    intro i k
    rw [hL]
    fin_cases i <;> fin_cases k <;> simp <;>
      linarith [abs_nonneg (B 0 0), abs_nonneg (B 0 1), abs_nonneg (B 1 0), abs_nonneg (B 1 1)]
  obtain ⟨C, -, hC⟩ := rd_bound_near (isLocallyBounded_of_continuous hFc) A₀ L
  have hlim2 : Tendsto (fun n : ℕ => ∫ x in unitCube 2,
      F (A₀ + (1 / ((n : ℝ) + 1)) • B + grad φ x)) atTop
      (𝓝 (∫ x in unitCube 2, F (A₀ + grad φ x))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_)
      (integrableOn_const volume_unitCube_two_ne_top enorm_ne_top)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact (hFc.measurable.comp (rd_measurable_add_grad _ φ)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, add_assoc]
      refine hC _ fun i k => ?_
      have hc0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      have hc1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h1 : |(1 / ((n : ℝ) + 1)) * B i k| ≤ |B i k| := by
        rw [abs_mul, abs_of_nonneg hc0]
        exact mul_le_of_le_one_left (abs_nonneg _) hc1
      have h2 := rd_grad_abs_le hφ x i k
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact (abs_add_le _ _).trans (by linarith [hBL i k])
    · exact (hFc.tendsto _).comp (hA.add_const (grad φ x))
  refine le_of_tendsto_of_tendsto' hlim1 hlim2 fun n => ?_
  exact h _ (hzn n) (hwn n) φ K hφ h0
    (nl_integrableOn_cube hφ hFc _ _ volume_unitCube_two_ne_top)

/-! ### Quasiconvexity when the slice is negative at `−1` -/

/-- Let `F` be isotropic, positively `p`-homogeneous and rank-one convex, `p > 1`, `p ≠ 2`, with
the slice of its profile strictly convex on `[−1, 1]` and negative at `−1`. Then `F` is
quasiconvex. -/
theorem quasiconvex_of_strictConvexOn_slice (hp1 : 1 < p) (hp2 : p ≠ 2) (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F)
    (hsc : StrictConvexOn ℝ (Icc (-1) 1) (slice (profile F)))
    (hor : slice (profile F) (-1) < 0) : Quasiconvex F :=
  quasiconvex_of_forall_ne_zero (continuous_of_rankOneConvex hrc) fun _ hz hw =>
    quasiconvexAtOn_of_strictConvexOn_slice hp1 hp2 hiso hhom hrc hsc hor hz hw

/-- Let `F` be isotropic, positively `p`-homogeneous and rank-one convex, `p > 1`, `p ≠ 2`, with
the slice of its profile negative at `−1`. Then `F` is quasiconvex: the integrands
`F + ε (|z|^p + |w|^p)`, `ε > 0` small, have strictly convex slices that are negative at `−1`. -/
theorem quasiconvex_of_slice_neg_one_neg (hp1 : 1 < p) (hp2 : p ≠ 2) (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F) (hor : slice (profile F) (-1) < 0) :
    Quasiconvex F := by
  have hp0 : 0 < p := by linarith
  have hΦ := isProfile_profile hiso hhom hrc
  have hFc : Continuous F := continuous_of_rankOneConvex hrc
  have hΘc : Continuous (coordPowSum p) := continuous_coordPowSum hp0.le
  -- the perturbed integrands are quasiconvex
  have key : ∀ ε : ℝ, 0 < ε → ε < -slice (profile F) (-1) →
      Quasiconvex fun A => F A + ε * coordPowSum p A := by
    intro ε hε hε2
    have hiso' : IsIsotropic fun A => F A + ε * coordPowSum p A := by
      intro Q hQ R hR A
      simp only
      rw [hiso Q hQ R hR A, isIsotropic_coordPowSum p Q hQ R hR A]
    have hhom' : IsPosHomogeneous p fun A => F A + ε * coordPowSum p A := by
      intro c hc A
      simp only
      rw [hhom c hc, isPosHomogeneous_coordPowSum p c hc]
      ring
    have hrc' : RankOneConvex fun A => F A + ε * coordPowSum p A := by
      intro A B hB
      exact (hrc A B hB).add ((rankOneConvex_coordPowSum hp1.le A B hB).smul hε.le)
    have hslice : slice (profile fun A => F A + ε * coordPowSum p A) =
        fun t => slice (profile F) t + ε * (|(1 + t) / 2| ^ p + |(1 - t) / 2| ^ p) := by
      funext t
      rw [← profile_coordPowSum]
      rfl
    refine quasiconvex_of_strictConvexOn_slice hp1 hp2 hiso' hhom' hrc' ?_ ?_
    · rw [hslice]
      exact strictConvexOn_add_mul_rpow hΦ.convexOn_slice_Icc hp1 hε
    · rw [hslice]
      norm_num [Real.zero_rpow hp0.ne']
      linarith
  -- Jensen's inequality for `F`, as the limit `ε → 0`
  intro A φ K hφ h0 hI
  have hΘI : IntegrableOn (fun x => coordPowSum p (A + grad φ x)) (unitCube 2) :=
    nl_integrableOn_cube hφ hΘc A _ volume_unitCube_two_ne_top
  have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (volume (unitCube 2)).toReal * F A + ε * ((volume (unitCube 2)).toReal * coordPowSum p A) ≤
        (∫ x in unitCube 2, F (A + grad φ x)) +
          ε * ∫ x in unitCube 2, coordPowSum p (A + grad φ x) := by
    filter_upwards [Ioo_mem_nhdsGT (neg_pos.2 hor)] with ε hε
    have h := key ε hε.1 hε.2 A φ K hφ h0 (hI.add (hΘI.const_mul ε))
    rw [integral_add hI (hΘI.const_mul ε), integral_const_mul] at h
    linarith
  have hl1 : Tendsto (fun ε : ℝ => (volume (unitCube 2)).toReal * F A +
      ε * ((volume (unitCube 2)).toReal * coordPowSum p A)) (𝓝[>] (0 : ℝ))
      (𝓝 ((volume (unitCube 2)).toReal * F A)) := by
    have h : Tendsto (fun ε : ℝ => (volume (unitCube 2)).toReal * F A +
        ε * ((volume (unitCube 2)).toReal * coordPowSum p A)) (𝓝 (0 : ℝ))
        (𝓝 ((volume (unitCube 2)).toReal * F A +
          0 * ((volume (unitCube 2)).toReal * coordPowSum p A))) :=
      (tendsto_id.mul_const _).const_add _
    rw [zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hl2 : Tendsto (fun ε : ℝ => (∫ x in unitCube 2, F (A + grad φ x)) +
      ε * ∫ x in unitCube 2, coordPowSum p (A + grad φ x)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in unitCube 2, F (A + grad φ x))) := by
    have h : Tendsto (fun ε : ℝ => (∫ x in unitCube 2, F (A + grad φ x)) +
        ε * ∫ x in unitCube 2, coordPowSum p (A + grad φ x)) (𝓝 (0 : ℝ))
        (𝓝 ((∫ x in unitCube 2, F (A + grad φ x)) +
          0 * ∫ x in unitCube 2, coordPowSum p (A + grad φ x))) :=
      (tendsto_id.mul_const _).const_add _
    rw [zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hl1 hl2 hle

/-! ### All exponents -/

/-- **Theorem A. Isotropic, positively homogeneous, rank-one convex integrands on `ℝ^{2×2}` are
quasiconvex.** For every `p > 0`. -/
theorem quasiconvex_of_rankOneConvex_of_isotropic (hp : 0 < p) (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F) : Quasiconvex F := by
  by_cases h0 : ∀ A, 0 ≤ F A
  · exact quasiconvex_of_rankOneConvex_of_pos hp h0 hiso hhom hrc
  obtain ⟨A, hA⟩ := not_forall.1 h0
  replace hA : F A < 0 := not_le.1 hA
  -- a negative value excludes `p ≤ 1`
  have hp1 : 1 < p := by
    by_contra hcon
    rcases (not_lt.1 hcon).lt_or_eq with h | h
    · rw [eq_zero_of_rankOneConvex_of_lt_one hp h hhom hrc A] at hA
      exact lt_irrefl _ hA
    · subst h
      exact absurd (nonneg_of_rankOneConvex_one hiso hhom hrc A) (not_le.2 hA)
  by_cases hp2 : p = 2
  · subst hp2
    exact (polyconvex_of_rankOneConvex_two hiso hhom hrc).quasiconvex
  have hΦ := isProfile_profile hiso hhom hrc
  have hneg : profile F ‖conformalPart A‖ ‖anticonformalPart A‖ < 0 := by
    rw [← hiso.eq_profile]
    exact hA
  rcases hΦ.slice_neg_one_neg_or_slice_one_neg hp (norm_nonneg _) (norm_nonneg _) hneg with
    h | h
  · exact quasiconvex_of_slice_neg_one_neg hp1 hp2 hiso hhom hrc h
  · -- the mirror image: `A ↦ F (J A)`
    have h' := quasiconvex_of_slice_neg_one_neg hp1 hp2 (isIsotropic_comp_reflection_mul hiso)
      hhom.comp_reflection_mul (rankOneConvex_comp_reflection_mul hrc)
      (by rw [slice_profile_comp_reflection_mul_neg_one hiso]; exact h)
    have h2 := quasiconvex_comp_reflection_mul h'
    have e : (fun A => F (reflection * (reflection * A))) = F := by
      funext A
      rw [← Matrix.mul_assoc, reflection_mul_reflection, Matrix.one_mul]
    rwa [e] at h2

end HomogeneousIsotropic
