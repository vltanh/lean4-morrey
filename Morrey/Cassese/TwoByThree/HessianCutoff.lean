module

public import Morrey.Cassese.TwoByThree.Hessian
public import Morrey.Cassese.TwoByThree.WitnessCutoff

/-!
# Corollary 5.4: the Hessian quartic

The cut-off `φ_R = χ (·/R) φ` of the potential `φ` of `Morrey/Cassese/TwoByThree/Hessian.lean`
(`tbt6PhiR`), the decomposition `B D²φ_R = χ_R B D²φ + E_R` (`tbt6_hessB_hessian_PhiR`), the bound
`|E_R|² ≲ R⁻²` (`tbt6_frobSq_ER_le`), the energy estimate (through `tbt4_energy`), the rescaling
into the unit cube for Hessians (`tbt6_not_hessianQuasiconvexAt_of_witness`), and Corollary 5.4.

Helpers are prefixed `tbt6_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace Cassese


/-- `χ_R = χ (·/R)`. -/
noncomputable def tbt6ChiR (R : ℝ) (x : Fin 3 → ℝ) : ℝ := tbt4Chi (R⁻¹ • x)

/-- The cut-off potential `φ_R = χ (·/R) φ`. -/
noncomputable def tbt6PhiR (R : ℝ) (x : Fin 3 → ℝ) : ℝ := tbt6ChiR R x * tbt5Pot x

/-- The Leibniz remainder `∇χ_R ⊗ ∇φ + ∇φ ⊗ ∇χ_R + φ D²χ_R`. -/
noncomputable def tbt6M (R : ℝ) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => tbt5D (tbt6ChiR R) i x * tbt5D tbt5Pot j x +
    tbt5D (tbt6ChiR R) j x * tbt5D tbt5Pot i x + tbt5Pot x * hessian (tbt6ChiR R) x i j

/-- The cut-off error `E_R = B (∇χ_R ⊗ ∇φ + ∇φ ⊗ ∇χ_R + φ D²χ_R)`. -/
noncomputable def tbt6ER (R : ℝ) (x : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ := hessB * tbt6M R x

theorem tbt6_contDiff_chiR (R : ℝ) : ContDiff ℝ tbt3Top (tbt6ChiR R) :=
  tbt4_contDiff_chi.comp (contDiff_const_smul _)

theorem tbt6_contDiff_PhiR (R : ℝ) : ContDiff ℝ tbt3Top (tbt6PhiR R) :=
  (tbt6_contDiff_chiR R).mul tbt5_Pot_contDiff

theorem tbt6_hessian_PhiR (R : ℝ) (x : Fin 3 → ℝ) :
    hessian (tbt6PhiR R) x = tbt6ChiR R x • hessian tbt5Pot x + tbt6M R x := by
  ext i j
  have := tbt5_hessian_mul ((tbt6_contDiff_chiR R).of_le (by simp))
    (tbt5_Pot_contDiff (n := 2)) x i j
  show hessian (fun y => tbt6ChiR R y * tbt5Pot y) x i j = _
  rw [this]
  simp only [tbt6M, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  ring

/-- `B D²φ_R = χ_R (B D²φ) + E_R`. -/
theorem tbt6_hessB_hessian_PhiR (R : ℝ) (x : Fin 3 → ℝ) :
    hessB * hessian (tbt6PhiR R) x = tbt6ChiR R x • (hessB * hessian tbt5Pot x) + tbt6ER R x := by
  rw [tbt6_hessian_PhiR, Matrix.mul_add, Matrix.mul_smul]; rfl

/-- The Hessian vanishes off the topological support. -/
theorem tbt6_hessian_eq_zero {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ} (hx : x ∉ tsupport f) :
    hessian f x = 0 := by
  have hU : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  have h0 : ∀ y ∈ (tsupport f)ᶜ, fderiv ℝ f y = 0 := fun y hy => by
    have : f =ᶠ[nhds y] fun _ => 0 := Filter.eventuallyEq_of_mem (hU.mem_nhds hy)
      fun z hz => image_eq_zero_of_notMem_tsupport hz
    rw [this.fderiv_eq]; exact fderiv_const_apply 0
  ext i j
  rw [tbt5_hessian_eq]
  have : tbt5D f j =ᶠ[nhds x] fun _ => 0 := Filter.eventuallyEq_of_mem (hU.mem_nhds hx)
    fun y hy => by simp [tbt5D, h0 y hy]
  simp only [tbt5D] at this ⊢
  rw [this.fderiv_eq]
  simp

theorem tbt6_continuous_hessian {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous fun x => hessian f x := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact ((tbt5_D_contDiff hf j).continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem tbt6_D_chiR (R : ℝ) (i : Fin 3) (x : Fin 3 → ℝ) :
    tbt5D (tbt6ChiR R) i x = R⁻¹ * tbt5D tbt4Chi i (R⁻¹ • x) :=
  tbt5_D_comp_smul (tbt4_contDiff_chi.differentiable (by simp)) R⁻¹ i x

theorem tbt6_hessian_chiR (R : ℝ) (x : Fin 3 → ℝ) (i j : Fin 3) :
    hessian (tbt6ChiR R) x i j = R⁻¹ ^ 2 * hessian tbt4Chi (R⁻¹ • x) i j :=
  tbt5_hessian_comp_smul (tbt4_contDiff_chi.of_le (by simp)) R⁻¹ x i j

theorem tbt6_abs_D_chi_le {G : ℝ} (hG : 0 ≤ G) (hGb : ∀ y, ‖fderiv ℝ tbt4Chi y‖ ≤ G)
    (i : Fin 3) (y : Fin 3 → ℝ) : |tbt5D tbt4Chi i y| ≤ G := by
  have h1 := (fderiv ℝ tbt4Chi y).le_opNorm (Pi.single i 1)
  have h2 : ‖(Pi.single i (1 : ℝ) : Fin 3 → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
  rw [← Real.norm_eq_abs]
  calc _ ≤ ‖fderiv ℝ tbt4Chi y‖ * ‖(Pi.single i (1 : ℝ) : Fin 3 → ℝ)‖ := h1
    _ ≤ G * 1 := mul_le_mul (hGb _) h2 (norm_nonneg _) hG
    _ = G := mul_one G

theorem tbt6_tsupport_chi : tsupport tbt4Chi ⊆ {y : Fin 3 → ℝ | ∑ i, y i ^ 2 ≤ 2} := by
  refine closure_minimal (fun y hy => ?_) (isClosed_le (tbt4_contDiff_sumSq (n := 0)).continuous
    continuous_const)
  by_contra h
  exact hy (tbt4_chi_zero (le_of_lt (not_le.mp h)))

/-- The Hessian of `χ` is bounded. -/
theorem tbt6_hessian_chi_bound : ∃ H : ℝ, 0 ≤ H ∧ ∀ y i j, |hessian tbt4Chi y i j| ≤ H := by
  have hc : Continuous fun y => ∑ i, ∑ j, |hessian tbt4Chi y i j| := by
    have := tbt6_continuous_hessian (tbt4_contDiff_chi.of_le (by simp))
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp this)).abs
  obtain ⟨H₀, hH₀⟩ := (tbt4_isCompact_sum_sq_le 2).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max H₀ 0, le_max_right _ _, fun y i j => ?_⟩
  by_cases hy : y ∈ tsupport tbt4Chi
  · have h1 := hH₀ y (tbt6_tsupport_chi hy)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h1
    have h2 : |hessian tbt4Chi y i j| ≤ ∑ j, |hessian tbt4Chi y i j| :=
      Finset.single_le_sum (f := fun j => |hessian tbt4Chi y i j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h3 : ∑ j, |hessian tbt4Chi y i j| ≤ ∑ i, ∑ j, |hessian tbt4Chi y i j| :=
      Finset.single_le_sum (f := fun i => ∑ j, |hessian tbt4Chi y i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [le_max_left H₀ 0]
  · rw [tbt6_hessian_eq_zero hy]; simp

theorem tbt6_tsupport_chiR {R : ℝ} (hR : 0 < R) :
    tsupport (tbt6ChiR R) ⊆ {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2} := by
  refine closure_minimal (fun x hx => ?_) (isClosed_le (tbt4_contDiff_sumSq (n := 0)).continuous
    continuous_const)
  by_contra h
  exact hx (tbt4_chiR_zero hR (not_le.mp h))

theorem tbt6_fderiv_eq_zero {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ} (hx : x ∉ tsupport f) :
    fderiv ℝ f x = 0 := by
  have hU : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  have : f =ᶠ[nhds x] fun _ => 0 := Filter.eventuallyEq_of_mem (hU.mem_nhds hx)
    fun z hz => image_eq_zero_of_notMem_tsupport hz
  rw [this.fderiv_eq]; exact fderiv_const_apply 0

theorem tbt6_ER_zero {R : ℝ} (hR : 0 < R) {x : Fin 3 → ℝ} (hx : 2 * R ^ 2 < ∑ i, x i ^ 2) :
    tbt6ER R x = 0 := by
  have hx' : x ∉ tsupport (tbt6ChiR R) := fun h => absurd (tbt6_tsupport_chiR hR h) (not_le.mpr hx)
  have hD : ∀ i, tbt5D (tbt6ChiR R) i x = 0 := fun i => by
    simp [tbt5D, tbt6_fderiv_eq_zero hx']
  have hM : tbt6M R x = 0 := by
    ext i j
    simp [tbt6M, hD, tbt6_hessian_eq_zero hx']
  simp [tbt6ER, hM]

theorem tbt6_abs_Pot_le {R : ℝ} (hR : 1 ≤ R) {x : Fin 3 → ℝ} (hx : ∑ i, x i ^ 2 ≤ 2 * R ^ 2) :
    |tbt5Pot x| ≤ 9 * R := by
  have hc : ∀ i, |x i| ≤ 2 * R := by
    intro i
    have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (f := fun j => x j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    apply abs_le_of_sq_le_sq _ (by linarith)
    nlinarith
  have := tbt5_abs_Pot_le x
  linarith [hc 0, hc 1, hc 2]

/-- `|E_R|² ≤ C₂ / R²` with `C₂ = 24 (8G/3 + 9H)²`, for `R ≥ 1`. -/
theorem tbt6_frobSq_ER_le {G H R : ℝ} (hG : 0 ≤ G) (hGb : ∀ y, ‖fderiv ℝ tbt4Chi y‖ ≤ G)
    (hH : 0 ≤ H) (hHb : ∀ y i j, |hessian tbt4Chi y i j| ≤ H) (hR : 1 ≤ R) (x : Fin 3 → ℝ) :
    frobSq (tbt6ER R x) ≤ 24 * (8 * G / 3 + 9 * H) ^ 2 / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  set Q := 8 * G / 3 + 9 * H
  have hQ : 0 ≤ Q := by positivity
  by_cases hx : ∑ i, x i ^ 2 ≤ 2 * R ^ 2
  · -- `|M i j| ≤ Q / R`
    have hM : ∀ i j, |tbt6M R x i j| ≤ Q / R := by
      intro i j
      have hDi := tbt6_abs_D_chi_le hG hGb i (R⁻¹ • x)
      have hDj := tbt6_abs_D_chi_le hG hGb j (R⁻¹ • x)
      have hpi := tbt5_abs_fderiv_Pot_le x i
      have hpj := tbt5_abs_fderiv_Pot_le x j
      have hP := tbt6_abs_Pot_le hR hx
      have hh := hHb (R⁻¹ • x) i j
      simp only [tbt6M, Matrix.of_apply, tbt6_D_chiR, tbt6_hessian_chiR]
      have hRi : 0 < R⁻¹ := inv_pos.mpr hR0
      have e1 : |R⁻¹ * tbt5D tbt4Chi i (R⁻¹ • x) * tbt5D tbt5Pot j x| ≤ R⁻¹ * G * (4 / 3) := by
        rw [abs_mul, abs_mul, abs_of_pos hRi]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hDi hRi.le) hpj (abs_nonneg _) (by positivity)
      have e2 : |R⁻¹ * tbt5D tbt4Chi j (R⁻¹ • x) * tbt5D tbt5Pot i x| ≤ R⁻¹ * G * (4 / 3) := by
        rw [abs_mul, abs_mul, abs_of_pos hRi]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hDj hRi.le) hpi (abs_nonneg _) (by positivity)
      have e3 : |tbt5Pot x * (R⁻¹ ^ 2 * hessian tbt4Chi (R⁻¹ • x) i j)| ≤ 9 * R * (R⁻¹ ^ 2 * H) := by
        rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < R⁻¹ ^ 2 by positivity)]
        exact mul_le_mul hP (mul_le_mul_of_nonneg_left hh (by positivity)) (by positivity)
          (by positivity)
      have e4 : R⁻¹ * G * (4 / 3) + R⁻¹ * G * (4 / 3) + 9 * R * (R⁻¹ ^ 2 * H) = Q / R := by
        simp only [Q]; field_simp; ring
      calc _ ≤ |R⁻¹ * tbt5D tbt4Chi i (R⁻¹ • x) * tbt5D tbt5Pot j x| +
            |R⁻¹ * tbt5D tbt4Chi j (R⁻¹ • x) * tbt5D tbt5Pot i x| +
            |tbt5Pot x * (R⁻¹ ^ 2 * hessian tbt4Chi (R⁻¹ • x) i j)| := abs_add_three _ _ _
        _ ≤ _ := by linarith
    have hE : ∀ i j, (tbt6ER R x i j) ^ 2 ≤ 4 * Q ^ 2 / R ^ 2 := by
      have hQR : 0 ≤ Q / R := by positivity
      intro i j
      have e : tbt6ER R x i j = if i = 0 then tbt6M R x 0 j + tbt6M R x 2 j else tbt6M R x 1 j := by
        fin_cases i <;> simp [tbt6ER, hessB, Matrix.mul_apply, Fin.sum_univ_three]
      rw [e]
      have h4 : 4 * Q ^ 2 / R ^ 2 = (2 * (Q / R)) ^ 2 := by field_simp; ring
      rw [h4]
      split_ifs
      · rw [← sq_abs]
        apply pow_le_pow_left₀ (abs_nonneg _)
        calc _ ≤ |tbt6M R x 0 j| + |tbt6M R x 2 j| := abs_add_le _ _
          _ ≤ 2 * (Q / R) := by linarith [hM 0 j, hM 2 j]
      · rw [← sq_abs]
        apply pow_le_pow_left₀ (abs_nonneg _)
        linarith [hM 1 j]
    simp only [frobSq, Fin.sum_univ_two, Fin.sum_univ_three]
    have := hE 0 0; have := hE 0 1; have := hE 0 2; have := hE 1 0; have := hE 1 1
    have := hE 1 2
    have e : 24 * Q ^ 2 / R ^ 2 = 6 * (4 * Q ^ 2 / R ^ 2) := by ring
    rw [e]; linarith
  · rw [tbt6_ER_zero hR0 (not_le.mp hx)]
    have : frobSq (0 : Matrix (Fin 2) (Fin 3) ℝ) = 0 := by simp [frobSq]
    rw [this]; positivity

theorem tbt6_continuous_D {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 3) :
    Continuous (tbt5D f j) := (tbt5_D_contDiff hf j).continuous

theorem tbt6_continuous_ER (R : ℝ) : Continuous (tbt6ER R) := by
  have hχ : ContDiff ℝ 2 (tbt6ChiR R) := (tbt6_contDiff_chiR R).of_le (by simp)
  have hP : ContDiff ℝ 2 tbt5Pot := tbt5_Pot_contDiff
  have hH := tbt6_continuous_hessian hχ
  have hM : Continuous (tbt6M R) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [tbt6M, Matrix.of_apply]
    exact (((tbt6_continuous_D hχ i).mul (tbt6_continuous_D hP j)).add
      ((tbt6_continuous_D hχ j).mul (tbt6_continuous_D hP i))).add
      ((tbt5_Pot_contDiff (n := 0)).continuous.mul
        ((continuous_apply j).comp ((continuous_apply i).comp hH)))
  exact continuous_const.matrix_mul hM

/-- `|q₃ (B D²φ)| ≤ 16 |q₃ (∇u)|`, so `q₃ (B D²φ)` is integrable. -/
theorem tbt6_integrable_q3_V : Integrable fun x => q3 (hessB * hessian tbt5Pot x) := by
  refine (tbt_integrable_q3.norm.const_mul 16).mono'
    (tbt_continuous_q3.comp tbt5_continuous_V).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, tbt5_hessB_hessian, tbt5_q3_M, tbt_q3_jac]
  have hz := (tbt_norm_Zeta_lt_one x).le
  have hz0 := norm_nonneg (tbtZeta x)
  have hρ : 0 ≤ (1 - ‖tbtZeta x‖ ^ 2) ^ 6 := by
    have : 0 ≤ 1 - ‖tbtZeta x‖ ^ 2 := by nlinarith
    positivity
  have h1 : ‖1 + tbtZeta x‖ ≤ 2 := by
    calc ‖1 + tbtZeta x‖ ≤ ‖(1 : ℂ)‖ + ‖tbtZeta x‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have h4 : ‖1 + tbtZeta x‖ ^ 4 ≤ 16 := by
    calc ‖1 + tbtZeta x‖ ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1 4
      _ = 16 := by norm_num
  rw [abs_mul, abs_mul, abs_neg, abs_neg, abs_of_nonneg hρ,
    abs_of_nonneg (show (0 : ℝ) ≤ (‖(1 + tbtZeta x) * tbtK x‖ ^ 2) ^ 2 by positivity),
    abs_of_nonneg (show (0 : ℝ) ≤ (‖tbtK x‖ ^ 2) ^ 2 by positivity), norm_mul]
  have e : ((‖1 + tbtZeta x‖ * ‖tbtK x‖) ^ 2) ^ 2 = ‖1 + tbtZeta x‖ ^ 4 * (‖tbtK x‖ ^ 2) ^ 2 := by
    ring
  rw [e]
  have : 0 ≤ (‖tbtK x‖ ^ 2) ^ 2 * (1 - ‖tbtZeta x‖ ^ 2) ^ 6 := by positivity
  nlinarith

/-- `∫_{|x|² ≤ 2R²} |B D²φ|⁴ ≤ 16 · 576 π² log (2 + 2R)`. -/
theorem tbt6_log_bound {R : ℝ} (hR : 0 < R) :
    ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2}, frobSq (hessB * hessian tbt5Pot x) ^ 2 ≤
      16 * (576 * Real.pi ^ 2 * Real.log (2 + 2 * R)) := by
  have hc : Continuous fun x => frobSq (hessB * hessian tbt5Pot x) ^ 2 :=
    (tbt_continuous_frobSq.comp tbt5_continuous_V).pow 2
  have hi : IntegrableOn (fun x => frobSq (hessB * hessian tbt5Pot x) ^ 2)
      {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < (2 * R) ^ 2} :=
    (hc.continuousOn.integrableOn_compact (tbt4_isCompact_sum_sq_le ((2 * R) ^ 2))).mono_set
      fun x hx => le_of_lt (show ∑ i, x i ^ 2 < (2 * R) ^ 2 from hx)
  refine (setIntegral_mono_set hi (Filter.Eventually.of_forall fun x => by positivity)
    (Filter.Eventually.of_forall fun x hx => ?_)).trans
      (tbt5_V_log_bound (by positivity : 0 ≤ 2 * R))
  have h : ∑ i, x i ^ 2 ≤ 2 * R ^ 2 := hx
  show ∑ i, x i ^ 2 < (2 * R) ^ 2
  nlinarith

/-- `I₁ = ∫_{B₁} q₃ (B D²φ) < 0`. -/
theorem tbt6_I1_neg :
    ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < 1}, q3 (hessB * hessian tbt5Pot x) < 0 := by
  set B := {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < 1}
  have hsq : Continuous fun x : Fin 3 → ℝ => ∑ i, x i ^ 2 := (tbt4_contDiff_sumSq (n := 0)).continuous
  have hBo : IsOpen B := isOpen_lt hsq continuous_const
  have hpos : 0 < ∫ x in B, -q3 (hessB * hessian tbt5Pot x) := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => (neg_pos.mpr (tbt5_q3_V_neg x)).le)
      tbt6_integrable_q3_V.neg.integrableOn]
    have hs : Function.support (fun x => -q3 (hessB * hessian tbt5Pot x)) = Set.univ :=
      Set.eq_univ_of_forall fun x => (neg_pos.mpr (tbt5_q3_V_neg x)).ne'
    rw [hs, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hBo.measure_pos volume ⟨0, by simp [B]⟩
  rw [integral_neg] at hpos
  linarith

/-- A smooth potential `f : ℝ³ → ℝ` vanishing on `|x|² > 2R²` with `∫ q (B D²f) < 0` shows that
`A ↦ q (B A)` is not Hessian quasiconvex at `0`: rescaled as `x ↦ λ² f ((x − c)/λ)`,
`c = (1/2, 1/2, 1/2)`, `λ = 1/(8R)`, it has compact support in the open unit cube, the same
Hessians, and energy `λ³ ∫ q (B D²f) < 0`. -/
theorem tbt6_not_hessianQuasiconvexAt_of_witness {q : Matrix (Fin 2) (Fin 3) ℝ → ℝ}
    (hq : Continuous q) (hq0 : q 0 = 0) {R : ℝ} (hR : 0 < R) {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ tbt3Top f) (hfz : ∀ z, 2 * R ^ 2 < ∑ i, z i ^ 2 → f z = 0)
    (hneg : ∫ x, q (hessB * hessian f x) < 0) :
    ¬ HessianQuasiconvexAt (fun A : Matrix (Fin 3) (Fin 3) ℝ => q (hessB * A)) 0 := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  set c : Fin 3 → ℝ := fun _ => 1 / 2
  set l : ℝ := 1 / (8 * R)
  have hl : 0 < l := by positivity
  set φ : (Fin 3 → ℝ) → ℝ := fun x => l ^ 2 * f (l⁻¹ • (x - c))
  have hφ : ContDiff ℝ tbt3Top φ :=
    contDiff_const.mul (hf.comp ((contDiff_const_smul _).comp (contDiff_id.sub contDiff_const)))
  have hhess : ∀ x, hessian φ x = hessian f (l⁻¹ • (x - c)) := fun x =>
    tbt5_hessian_rescale hf2 hl.ne' c x
  have hφz : ∀ x, x ∉ Metric.closedBall c (1 / 4) → φ x = 0 := by
    intro x hx
    simp only [Metric.mem_closedBall, not_le] at hx
    have hn : 2 * R < ‖l⁻¹ • (x - c)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), ← dist_eq_norm]
      simp only [l]
      rw [one_div, inv_inv]
      nlinarith
    have := tbt4_lt_sum_sq (by positivity) hn
    simp only [φ, hfz _ (by nlinarith), mul_zero]
  have hball : Metric.closedBall c (1 / 4) ⊆ unitCube 3 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)] at hx
    intro i _
    have := hx i
    rw [Real.dist_eq, abs_le] at this
    simp only [c] at this
    exact ⟨by linarith, by linarith⟩
  have hts : tsupport φ ⊆ Metric.closedBall c (1 / 4) :=
    closure_minimal (fun x hx => by_contra fun h => hx (hφz x h)) Metric.isClosed_closedBall
  have hc : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall c (1 / 4)) hφz
  have hcont : Continuous fun x => q (hessB * (0 + hessian φ x)) := by
    simp_rw [zero_add]
    exact hq.comp (continuous_const.matrix_mul (tbt6_continuous_hessian (hφ.of_le (by simp))))
  intro h
  have key := h φ hφ hc (hts.trans hball) (Sverak.gen_integrableOn_unitCube hcont)
  have hout : ∀ x, x ∉ unitCube 3 → q (hessB * (0 + hessian φ x)) = 0 := by
    intro x hx
    have : x ∉ tsupport φ := fun h => hx (hball (hts h))
    rw [tbt6_hessian_eq_zero this, add_zero, Matrix.mul_zero, hq0]
  simp only at key
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout, Matrix.mul_zero, hq0] at key
  simp_rw [zero_add, hhess] at key
  rw [integral_sub_right_eq_self (fun x => q (hessB * hessian f (l⁻¹ • x))) c,
    Measure.integral_comp_inv_smul (μ := volume) (fun y => q (hessB * hessian f y)) l,
    Module.finrank_fin_fun, smul_eq_mul] at key
  have : 0 < |l ^ 3| := abs_pos.mpr (by positivity)
  nlinarith

/-- **The cutoff argument for Corollary 5.4**: for every `K` there is `δ₀ ∈ (0, 1]` such that for
`0 < δ < δ₀`, `A ↦ q_{δ,K/δ} (B A)` is not Hessian quasiconvex at `0`. -/
theorem tbt6_not_hessianQuasiconvexAt (K : ℝ) :
    ∃ δ₀ > 0, δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ¬ HessianQuasiconvexAt
        (fun A : Matrix (Fin 3) (Fin 3) ℝ => qDeltaLambda δ (K / δ) (hessB * A)) 0 := by
  obtain ⟨L, M, hL, hM, hpert⟩ := tbt4_q3_perturb
  obtain ⟨G, hG, hGb⟩ := tbt4_fderiv_chi_bound
  obtain ⟨H, hH, hHb⟩ := tbt6_hessian_chi_bound
  set I₁ := ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < 1}, q3 (hessB * hessian tbt5Pot x)
  have hI : I₁ < 0 := tbt6_I1_neg
  set C₂ := 24 * (8 * G / 3 + 9 * H) ^ 2
  set A := (L + 16) * (16 * (576 * Real.pi ^ 2)) * (Real.log 4 + 8)
  set B := 64 * C₂ ^ 2 * (L + M + 16 + 2 * K ^ 4)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  set Ct := A + B + 1
  have hCt : 0 < Ct := by positivity
  refine ⟨min 1 ((I₁ / (2 * Ct)) ^ 2), lt_min one_pos (by
    have : I₁ / (2 * Ct) ≠ 0 := div_ne_zero hI.ne (by positivity)
    positivity), min_le_left _ _, fun δ hδ hδ₀ => ?_⟩
  have hδ1 : δ ≤ 1 := (lt_of_lt_of_le hδ₀ (min_le_left _ _)).le
  have hδs : √δ < -I₁ / (2 * Ct) := by
    have h := lt_of_lt_of_le hδ₀ (min_le_right _ _)
    have h' : √δ < √((I₁ / (2 * Ct)) ^ 2) := Real.sqrt_lt_sqrt hδ.le h
    rwa [Real.sqrt_sq_eq_abs, abs_of_neg (div_neg_of_neg_of_pos hI (by positivity)), ← neg_div]
      at h'
  set R := (δ ^ 4)⁻¹
  have hR : 0 < R := by positivity
  have hR1 : 1 ≤ R := one_le_inv_iff₀.mpr ⟨by positivity, pow_le_one₀ hδ.le hδ1⟩
  -- the energy of `φ_R`
  have hE := tbt4_energy (Gf := fun x => hessB * hessian tbt5Pot x) (Ef := tbt6ER R)
    (χf := tbt6ChiR R) (C₁ := 16 * (576 * Real.pi ^ 2 * Real.log (2 + 2 * R))) (C₂ := C₂)
    (η := δ) (Λ := K / δ)
    hL hM hpert hR hδ.le hδ tbt5_continuous_V (tbt6_continuous_ER R)
    (tbt6_contDiff_chiR R).continuous tbt5_V_mem_L3
    (fun x => (tbt5_q3_V_neg x).le) tbt6_integrable_q3_V
    (fun x => Real.smoothTransition.nonneg _) (fun x => Real.smoothTransition.le_one _)
    (fun x hx => tbt4_chi_one (by
      rw [tbt4_sumSq_smul, inv_pow]
      have : (R ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hR1)
      have h0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith))
    (fun x hx => ⟨tbt4_chiR_zero hR hx, tbt6_ER_zero hR hx⟩) (tbt6_log_bound hR)
    (fun x => tbt6_frobSq_ER_le hG hGb hH hHb hR1 x)
  have heq : ∫ x, qDeltaLambda δ (K / δ) (hessB * hessian (tbt6PhiR R) x) =
      ∫ x, qDeltaLambda δ (K / δ) (tbt6ChiR R x • (hessB * hessian tbt5Pot x) + tbt6ER R x) := by
    simp_rw [tbt6_hessB_hessian_PhiR]
  have hT1 : (L * δ + 16 * δ) * (16 * (576 * Real.pi ^ 2 * Real.log (2 + 2 * R))) ≤ A * √δ := by
    have := tbt4_delta_log hδ hδ1
    calc (L * δ + 16 * δ) * (16 * (576 * Real.pi ^ 2 * Real.log (2 + 2 * R)))
        = (L + 16) * (16 * (576 * Real.pi ^ 2)) * (δ * Real.log (2 + 2 * (δ ^ 4)⁻¹)) := by ring
      _ ≤ (L + 16) * (16 * (576 * Real.pi ^ 2)) * ((Real.log 4 + 8) * √δ) := by gcongr
      _ = A * √δ := by ring
  have hT2 : (L * δ⁻¹ ^ 3 + M + 16 * δ + 2 * δ * (K / δ) ^ 4) * (64 * (C₂ / R ^ 2) ^ 2 * R ^ 3)
      ≤ B * √δ := by
    have e : (L * δ⁻¹ ^ 3 + M + 16 * δ + 2 * δ * (K / δ) ^ 4) * (64 * (C₂ / R ^ 2) ^ 2 * R ^ 3) =
        64 * C₂ ^ 2 * (L * δ + M * δ ^ 4 + 16 * δ ^ 5 + 2 * K ^ 4 * δ) := by
      simp only [R]; field_simp
    have h4 : δ ^ 4 ≤ δ := by
      calc δ ^ 4 = δ * δ ^ 3 := by ring
        _ ≤ δ * 1 := by gcongr; exact pow_le_one₀ hδ.le hδ1
        _ = δ := mul_one δ
    have h5 : δ ^ 5 ≤ δ := by
      calc δ ^ 5 = δ * δ ^ 4 := by ring
        _ ≤ δ * 1 := by gcongr; exact pow_le_one₀ hδ.le hδ1
        _ = δ := mul_one δ
    have hsd : δ ≤ √δ := (Real.le_sqrt hδ.le hδ.le).mpr (by nlinarith)
    rw [e]
    calc 64 * C₂ ^ 2 * (L * δ + M * δ ^ 4 + 16 * δ ^ 5 + 2 * K ^ 4 * δ)
        ≤ 64 * C₂ ^ 2 * (L * δ + M * δ + 16 * δ + 2 * K ^ 4 * δ) := by gcongr
      _ = B * δ := by ring
      _ ≤ B * √δ := by gcongr
  have hneg : ∫ x, qDeltaLambda δ (K / δ) (hessB * hessian (tbt6PhiR R) x) < 0 := by
    rw [heq]
    have hs0 : 0 ≤ √δ := Real.sqrt_nonneg δ
    have h1 : (A + B) * √δ ≤ Ct * √δ := by gcongr; linarith
    have h2 : Ct * √δ < Ct * (-I₁ / (2 * Ct)) := mul_lt_mul_of_pos_left hδs hCt
    have h3 : Ct * (-I₁ / (2 * Ct)) = -I₁ / 2 := by field_simp
    linarith
  exact tbt6_not_hessianQuasiconvexAt_of_witness (tbt4_continuous_qDeltaLambda δ (K / δ))
    (tbt4_qDeltaLambda_zero δ (K / δ)) hR (tbt6_contDiff_PhiR R)
    (fun z hz => by simp [tbt6PhiR, tbt6ChiR, tbt4_chiR_zero hR hz]) hneg

/-- **Corollary 5.4** (`cor:hessian-quartic`): for `K` sufficiently large and `δ > 0` sufficiently
small, with `Λ = K/δ`, `h (A) = q_{δ,Λ} (B A)` on `ℝ^{3×3}` is rank-one convex but not Hessian
quasiconvex at `0`. Burkholder's inequality (Theorem 2.3) enters through Lemma 5.1 (2).

Proof, as in the paper (TeX 2159–2191: "the proof of Theorem 1.3 now applies unchanged, with
`Λ = K/δ` and `R = δ⁻⁴`"). Rank-one convexity: `q_{δ,K/δ}` is rank-one convex for `K ≥ K₀`,
`0 < δ ≤ 1` (`qDeltaLambda_rankOneConvex`, from Lemma 5.1 (2)) and `B` maps rank-one matrices to
matrices of rank at most one (`tbt5_rankOneConvex_hessB`). Failure of Hessian quasiconvexity at
`0`: the potential `φ` with `∇φ = Re Ψ (ζ)`, `Ψ = (z + z³/3, i (z − z³/3), z²)` (`F' = 1 + z`,
`G' = z (1 + z)`), has `V = B D²φ ∈ 𝓛₃`, `q₃ (V) < 0` and `∫_{B_R} |V|⁴ ≲ log (2 + R)`
(`Morrey/Cassese/TwoByThree/Hessian.lean`); it is cut off as `φ_R = χ (·/R) φ`, so that
`B D²φ_R = χ_R V + E_R` with `E_R = B (∇χ_R ⊗ ∇φ + ∇φ ⊗ ∇χ_R + φ D²χ_R)` (Leibniz, scaling),
and `|E_R|² ≲ R⁻²` because `∇φ` is bounded and `φ` grows linearly (`tbt6_frobSq_ER_le`). The
energy estimate of the proof of Theorem 1.3 (`tbt4_energy`, Morrey/Cassese/TwoByThree/
WitnessCutoff.lean) gives `∫ q_{δ,Λ} (B D²φ_R) ≤ I₁ + O (√δ)` with `I₁ = ∫_{B₁} q₃ (V) < 0`
(`tbt6_not_hessianQuasiconvexAt`); rescaled into the unit cube as `λ² φ_R ((x − c)/λ)`, which keeps
the Hessians, the witness refutes Hessian quasiconvexity at `0`
(`tbt6_not_hessianQuasiconvexAt_of_witness`).

Mechanical choices, as in `twoByThree_not_quasiconvexAt_qDeltaLambda`: the pointwise Young bound
replaces Hölder's inequality, `I₁ = ∫_{B₁} q₃ (V)` replaces `∫_{ℝ³} q₃ (V)` (using `q₃ (V) < 0`),
and the cut-off is `χ (y) = σ (2 − |y|²)`. The potential is the explicit
`φ = Re (x Ψ₁ (ζ) + y Ψ₂ (ζ) + t Ψ₃ (ζ) + i ζ²)` (`tbt5Pot`), where the paper only describes `∇φ`
and says "the integration constants can be chosen so that `B ∇φ = u`". -/
theorem corollary5_4 :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      RankOneConvex (fun A : Matrix (Fin 3) (Fin 3) ℝ => qDeltaLambda δ (K / δ) (hessB * A)) ∧
        ¬ HessianQuasiconvexAt
          (fun A : Matrix (Fin 3) (Fin 3) ℝ => qDeltaLambda δ (K / δ) (hessB * A)) 0 := by
  obtain ⟨K₀, -, hK₀⟩ := qDeltaLambda_rankOneConvex
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨δ₀, hδ₀, hδ₀1, hnq⟩ := tbt6_not_hessianQuasiconvexAt K
  exact ⟨δ₀, hδ₀, fun δ hδ hδ' =>
    ⟨tbt5_rankOneConvex_hessB (hK₀ K hK δ hδ (by linarith)).2, hnq δ hδ hδ'⟩⟩

end Cassese
