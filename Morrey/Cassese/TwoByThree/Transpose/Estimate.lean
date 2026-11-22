module

public import Morrey.Cassese.TwoByThree.Transpose.Cutoff
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Corollary 5.3: the energy of the cut-off witness

`∫ q̂_{δ,Λ} (∇v_R) ≤ M₁ + M₃ − (75/32) log (R/4)` for `v_R = 𝒱φ_R` and `0 < δ ≤ δ₀`
(`tbt3_integral_le`), with `M₁`, `M₃` the fixed contributions of the inner region `|x|² ≤ 2` and of
the outer region `|x|² ≥ R²` (rescaled to `|y|² ≥ 1`).

Helpers are prefixed `tbt3_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace Cassese

theorem tbt3_projL3_of_mem {B : Matrix (Fin 2) (Fin 3) ℝ} (hB : B ∈ L3) : projL3 B = B := by
  rw [mem_L3_iff] at hB
  ext i j
  fin_cases i <;> fin_cases j <;> simp [projL3, hB.1, hB.2]

/-- On `𝓛₃` the penalty vanishes: `q_{δ,Λ} (T) = q₃ (T) + δ |T|⁴`. -/
theorem tbt3_qDeltaLambda_of_mem (δ Λ : ℝ) {T : Matrix (Fin 2) (Fin 3) ℝ} (hT : T ∈ L3) :
    qDeltaLambda δ Λ T = q3 T + δ * frobSq T ^ 2 := by
  have h0 : frobSq (0 : Matrix (Fin 2) (Fin 3) ℝ) = 0 := by simp [frobSq]
  simp [qDeltaLambda, tbt3_projL3_of_mem hT, h0]

/-- `q̂_{δ,Λ} (∇𝒱ψ) = q₃ (T) + δ |T|⁴` with `T = (∇𝒱ψ)ᵀ`. -/
theorem tbt3_qHat_jac (δ Λ : ℝ) {ψ : (Fin 2 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ)
    (x : Fin 2 → ℝ) :
    qHat δ Λ (jac (tbt3V ψ) x) = q3 (jac (tbt3V ψ) x)ᵀ + δ * frobSq (jac (tbt3V ψ) x)ᵀ ^ 2 := by
  have hT : (jac (tbt3V ψ) x)ᵀ ∈ L3 := by rw [tbt3_jac_V_transpose h]; exact tbt3_T_mem_L3 _ _ _ _
  exact tbt3_qDeltaLambda_of_mem δ Λ hT

theorem tbt3_projL3_smul (r : ℝ) (B : Matrix (Fin 2) (Fin 3) ℝ) :
    projL3 (r • B) = r • projL3 B := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [projL3] <;> ring

/-- `q̂_{δ,Λ}` is homogeneous of degree `4`. -/
theorem tbt3_qHat_smul (δ Λ r : ℝ) (M : Matrix (Fin 3) (Fin 2) ℝ) :
    qHat δ Λ (r • M) = r ^ 4 * qHat δ Λ M := by
  simp only [qHat, qDeltaLambda, Matrix.transpose_smul, tbt3_projL3_smul, tbt_q3_smul,
    tbt_frobSq_smul, ← smul_sub]
  ring

theorem tbt3_continuous_qHat (δ Λ : ℝ) : Continuous (qHat δ Λ) :=
  (tbt_ihp_qHat δ Λ).continuous

theorem tbt3_contDiff_V {ψ : (Fin 2 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ) :
    ContDiff ℝ tbt3Top (tbt3V ψ) := by
  have d : ∀ i j : Fin 2, ContDiff ℝ tbt3Top (tbt3D1 (tbt3D1 ψ j) i) := fun i j =>
    tbt3_contDiff_D1 (tbt3_contDiff_D1 h j) i
  rw [contDiff_pi]
  intro n
  fin_cases n
  · exact (d 0 0).sub (d 1 1)
  · exact contDiff_const.mul (d 0 1)
  · exact (d 0 0).add (d 1 1)

theorem tbt3_continuous_jac {n : ℕ} {V : (Fin 2 → ℝ) → Fin n → ℝ} (hV : ContDiff ℝ tbt3Top V) :
    Continuous fun x => jac V x := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have hi : ContDiff ℝ tbt3Top fun y => V y i := (contDiff_pi.1 hV) i
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

theorem tbt3_continuous_qHat_jac (δ Λ : ℝ) {ψ : (Fin 2 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ) :
    Continuous fun x => qHat δ Λ (jac (tbt3V ψ) x) :=
  (tbt3_continuous_qHat δ Λ).comp (tbt3_continuous_jac (tbt3_contDiff_V h))

/-- `jac` vanishes off the topological support. -/
theorem tbt3_jac_eq_zero {n : ℕ} {V : (Fin 2 → ℝ) → Fin n → ℝ} {x : Fin 2 → ℝ}
    (hx : x ∉ tsupport V) : jac V x = 0 := by
  have hU : IsOpen (tsupport V)ᶜ := (isClosed_tsupport V).isOpen_compl
  have h : Set.EqOn V (fun _ => 0) (tsupport V)ᶜ := fun y hy =>
    image_eq_zero_of_notMem_tsupport hy
  rw [tbt3_jac_eqOn hU h hx]
  ext i k; simp [jac]

theorem tbt3_tsupport_V_subset (ψ : (Fin 2 → ℝ) → ℝ) : tsupport (tbt3V ψ) ⊆ tsupport ψ := by
  have hU : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
  have h0 : Set.EqOn ψ (fun _ => 0) (tsupport ψ)ᶜ := fun y hy =>
    image_eq_zero_of_notMem_tsupport hy
  have hV := tbt3_V_eqOn hU h0
  have hz : tbt3V (fun _ : Fin 2 → ℝ => (0 : ℝ)) = 0 := by
    funext x
    have : ∀ j, tbt3D1 (fun _ : Fin 2 → ℝ => (0 : ℝ)) j = fun _ => 0 := fun j => by
      funext y; simp [tbt3D1]
    simp [tbt3V, this]
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport ψ)
  by_contra hc
  exact hx (by rw [hV hc, hz]; rfl)

/-! ### The three regions -/

theorem tbt3_jac_in {R : ℝ} (hR : 0 < R) {x : Fin 2 → ℝ} (hx : tbt3Sq x < R ^ 2) :
    jac (tbt3V (tbt3PhiR R)) x = jac (tbt3V tbt3PhiIn) x :=
  tbt3_jac_eqOn (tbt3_isOpen_Sq_lt _) (tbt3_V_eqOn (tbt3_isOpen_Sq_lt _) (tbt3_PhiR_eq_in hR)) hx

theorem tbt3_jac_out {R : ℝ} (hR : 0 < R) (hR4 : 4 < R ^ 2) {x : Fin 2 → ℝ}
    (hx : R ^ 2 / 2 < tbt3Sq x) :
    jac (tbt3V (tbt3PhiR R)) x =
      (R ^ (5 / 2 : ℝ) * R⁻¹ * R⁻¹ * R⁻¹) • jac (tbt3V tbt3PhiOut) (R⁻¹ • x) := by
  rw [tbt3_jac_eqOn (tbt3_isOpen_lt_Sq _)
    (tbt3_V_eqOn (tbt3_isOpen_lt_Sq _) (tbt3_PhiR_eq_out hR hR4)) hx,
    tbt3_V_scale tbt3_contDiff_PhiOut,
    tbt3_jac_scale ((tbt3_contDiff_V tbt3_contDiff_PhiOut).differentiable (by simp))]

theorem tbt3_isOpen_bulk (R : ℝ) : IsOpen {z : Fin 2 → ℝ | 2 < tbt3Sq z ∧ tbt3Sq z < R ^ 2} :=
  (tbt3_isOpen_lt_Sq 2).inter (tbt3_isOpen_Sq_lt _)

theorem tbt3_jac_bulk {R : ℝ} (hR : 0 < R) {x : Fin 2 → ℝ}
    (hx : 2 < tbt3Sq x ∧ tbt3Sq x < R ^ 2) :
    (jac (tbt3V (tbt3PhiR R)) x)ᵀ =
      tbt3T (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 0) 0) 0 x) (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 0) 0 x)
        (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 1) 0 x) (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 1) 1 x) := by
  have U := tbt3_isOpen_bulk R
  have e := tbt3_PhiR_eq_bulk hR
  have e3 : ∀ i j k : Fin 2, tbt3D1 (tbt3D1 (tbt3D1 (tbt3PhiR R) j) i) k x =
      tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi j) i) k x := fun i j k =>
    tbt3_D1_eqOn U (tbt3_D1_eqOn U (tbt3_D1_eqOn U e j) i) k hx
  rw [tbt3_jac_V_transpose (tbt3_contDiff_PhiR R), e3, e3, e3, e3]

/-- The bulk: `q̂_{δ,Λ} (∇v_R) ≤ −(75/16) / |x|²` on `2 < |x|² < R²` for `0 ≤ δ ≤ δ₀`. -/
theorem tbt3_bulk_le {R δ : ℝ} (hR : 0 < R) (hδ : 0 ≤ δ) (hδ₀ : δ ≤ 75 / 64000000) (Λ : ℝ)
    {x : Fin 2 → ℝ} (hx : 2 < tbt3Sq x ∧ tbt3Sq x < R ^ 2) :
    qHat δ Λ (jac (tbt3V (tbt3PhiR R)) x) ≤ -(75 / 16) / tbt3Sq x := by
  rw [tbt3_qHat_jac δ Λ (tbt3_contDiff_PhiR R), tbt3_jac_bulk hR hx]
  have hs : 0 < MvPolynomial.eval x tbt3S := by rw [tbt3_eval_S]; exact lt_trans two_pos hx.1
  obtain ⟨h1, h2⟩ := tbt3_bulk_bounds hs
  rw [tbt3_eval_S] at h1 h2
  have hS : tbt3Sq x = x 0 ^ 2 + x 1 ^ 2 := rfl
  rw [hS] at hx ⊢
  have hp : 0 < x 0 ^ 2 + x 1 ^ 2 := lt_trans two_pos hx.1
  have h3 : δ * frobSq (tbt3T _ _ _ _) ^ 2 ≤ δ * (4000000 / (x 0 ^ 2 + x 1 ^ 2)) :=
    mul_le_mul_of_nonneg_left h2 hδ
  have h4 : δ * (4000000 / (x 0 ^ 2 + x 1 ^ 2)) ≤ 75 / 16 / (x 0 ^ 2 + x 1 ^ 2) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hp]; linarith
  have h5 : -(75 / 8) / (x 0 ^ 2 + x 1 ^ 2) + 75 / 16 / (x 0 ^ 2 + x 1 ^ 2) =
      -(75 / 16) / (x 0 ^ 2 + x 1 ^ 2) := by ring
  linarith

/-- `∫_{2 < a < R/2} ∫_{0 < b < a} 1 / (2 a²) = ½ log (R/4)`. -/
theorem tbt3_integral_triangle {R : ℝ} (hR : 4 < R) :
    ∫ x in {x : Fin 2 → ℝ | 2 < x 0 ∧ x 0 < R / 2 ∧ 0 < x 1 ∧ x 1 < x 0}, 1 / (2 * x 0 ^ 2) =
      1 / 2 * Real.log (R / 4) := by
  set S := {x : Fin 2 → ℝ | 2 < x 0 ∧ x 0 < R / 2 ∧ 0 < x 1 ∧ x 1 < x 0}
  have hSm : MeasurableSet S := by
    refine (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
      ((measurableSet_lt (measurable_pi_apply 0) measurable_const).inter
      ((measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
      (measurableSet_lt (measurable_pi_apply 1) (measurable_pi_apply 0))))
  have hg : Measurable fun x : Fin 2 → ℝ => 1 / (2 * x 0 ^ 2) := by fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    hg.aestronglyMeasurable]
  rw [← lintegral_indicator hSm]
  set f := MeasurableEquiv.finTwoArrow (α := ℝ)
  have hf : MeasurePreserving f.symm volume volume := (volume_preserving_finTwoArrow ℝ).symm
  have hF : Measurable (S.indicator fun x : Fin 2 → ℝ => ENNReal.ofReal (1 / (2 * x 0 ^ 2))) :=
    (hg.ennreal_ofReal).indicator hSm
  rw [← hf.lintegral_comp_emb f.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (fun p => S.indicator (fun x : Fin 2 → ℝ => ENNReal.ofReal (1 / (2 * x 0 ^ 2)))
      (f.symm p)) (hF.comp f.symm.measurable).aemeasurable]
  have inner : ∀ a : ℝ, ∫⁻ b : ℝ, S.indicator (fun x : Fin 2 → ℝ =>
      ENNReal.ofReal (1 / (2 * x 0 ^ 2))) (f.symm (a, b)) =
      (Set.Ioo 2 (R / 2)).indicator (fun a => ENNReal.ofReal (1 / (2 * a))) a := by
    intro a
    by_cases ha : a ∈ Set.Ioo 2 (R / 2)
    · rw [Set.indicator_of_mem ha]
      have : ∀ b, S.indicator (fun x : Fin 2 → ℝ => ENNReal.ofReal (1 / (2 * x 0 ^ 2)))
          (f.symm (a, b)) = (Set.Ioo 0 a).indicator (fun _ => ENNReal.ofReal (1 / (2 * a ^ 2))) b := by
        intro b
        by_cases hb : b ∈ Set.Ioo 0 a
        · rw [Set.indicator_of_mem hb, Set.indicator_of_mem]
          · rfl
          · exact ⟨ha.1, ha.2, hb.1, hb.2⟩
        · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem]
          exact fun h => hb ⟨h.2.2.1, h.2.2.2⟩
      simp_rw [this]
      rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, ←
        ENNReal.ofReal_mul (by have := ha.1; positivity)]
      congr 1
      have : a ≠ 0 := by have := ha.1; positivity
      rw [sub_zero]; field_simp
    · rw [Set.indicator_of_notMem ha]
      have : ∀ b, S.indicator (fun x : Fin 2 → ℝ => ENNReal.ofReal (1 / (2 * x 0 ^ 2)))
          (f.symm (a, b)) = 0 := fun b =>
        Set.indicator_of_notMem (fun h : f.symm (a, b) ∈ S => ha ⟨h.1, h.2.1⟩) _
      simp only [this, lintegral_zero]
  simp_rw [inner]
  rw [lintegral_indicator measurableSet_Ioo]
  have hi : IntegrableOn (fun a : ℝ => 1 / (2 * a)) (Set.Ioo 2 (R / 2)) := by
    refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Set.Ioo_subset_Icc_self
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun a ha => ?_
    have := ha.1; positivity
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo 2 (R / 2))] fun a : ℝ => 1 / (2 * a) :=
    (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun a ha => by
      have := ha.1; show (0 : ℝ) ≤ 1 / (2 * a); positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]
  have e : (fun a : ℝ => 1 / (2 * a)) = fun a => 1 / 2 * a⁻¹ := by funext a; field_simp
  rw [e, intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num) (by linarith)]
  congr 2; ring

/-- `J (R) = ∫_{2 < |x|² < R²} |x|⁻² ≥ ½ log (R/4)`: the triangle `2 < x₀ < R/2`, `0 < x₁ < x₀`
lies in the annulus, where `|x|² ≤ 2 x₀²`. -/
theorem tbt3_J_lower {R : ℝ} (hR : 4 < R) :
    1 / 2 * Real.log (R / 4) ≤
      ∫ x in {z : Fin 2 → ℝ | 2 < tbt3Sq z ∧ tbt3Sq z < R ^ 2}, 1 / tbt3Sq x := by
  set A := {z : Fin 2 → ℝ | 2 < tbt3Sq z ∧ tbt3Sq z < R ^ 2}
  set S := {x : Fin 2 → ℝ | 2 < x 0 ∧ x 0 < R / 2 ∧ 0 < x 1 ∧ x 1 < x 0}
  have hSm : MeasurableSet S := by
    refine (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
      ((measurableSet_lt (measurable_pi_apply 0) measurable_const).inter
      ((measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
      (measurableSet_lt (measurable_pi_apply 1) (measurable_pi_apply 0))))
  have hSA : S ⊆ A := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hx
    refine ⟨?_, ?_⟩ <;> simp only [tbt3Sq] <;> nlinarith
  -- `A ⊆ {2 ≤ |x|² ≤ R²}`, compact, where `1/|x|²` is continuous
  set K := {z : Fin 2 → ℝ | 2 ≤ tbt3Sq z ∧ tbt3Sq z ≤ R ^ 2}
  have hK : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin 2 → ℝ) R)
      ((isClosed_le continuous_const tbt3_continuous_Sq).inter
        (isClosed_le tbt3_continuous_Sq continuous_const)) fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    have h := hz.2
    have hRpos : 0 ≤ R := by linarith
    apply abs_le_of_sq_le_sq _ hRpos
    simp only [tbt3Sq] at h
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  have hc : ContinuousOn (fun x => 1 / tbt3Sq x) K :=
    continuousOn_const.div tbt3_continuous_Sq.continuousOn fun x hx => by
      have := hx.1; positivity
  have hiA : IntegrableOn (fun x => 1 / tbt3Sq x) A :=
    (hc.integrableOn_compact hK).mono_set fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hiS : IntegrableOn (fun x : Fin 2 → ℝ => 1 / (2 * x 0 ^ 2)) S := by
    refine (ContinuousOn.integrableOn_compact (K := {x : Fin 2 → ℝ | 2 ≤ x 0 ∧ x 0 ≤ R ∧
      0 ≤ x 1 ∧ x 1 ≤ R}) ?_ ?_).mono_set ?_
    · refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin 2 → ℝ) R) ?_ ?_
      · exact (isClosed_le continuous_const (continuous_apply 0)).inter
          ((isClosed_le (continuous_apply 0) continuous_const).inter
          ((isClosed_le continuous_const (continuous_apply 1)).inter
          (isClosed_le (continuous_apply 1) continuous_const)))
      · intro z hz
        rw [Metric.mem_closedBall, dist_zero_right]
        refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
        rw [Real.norm_eq_abs]
        obtain ⟨h1, h2, h3, h4⟩ := hz
        fin_cases i <;> simp <;> rw [abs_le] <;> constructor <;> linarith
    · refine continuousOn_const.div (by fun_prop) fun x hx => ?_
      have := hx.1; positivity
    · intro x hx
      obtain ⟨h1, h2, h3, h4⟩ := hx
      exact ⟨h1.le, by linarith, h3.le, by linarith⟩
  calc 1 / 2 * Real.log (R / 4)
      = ∫ x in S, 1 / (2 * x 0 ^ 2) := (tbt3_integral_triangle hR).symm
    _ ≤ ∫ x in S, 1 / tbt3Sq x := by
        refine setIntegral_mono_on hiS (hiA.mono_set hSA) hSm fun x hx => ?_
        obtain ⟨h1, h2, h3, h4⟩ := hx
        have hp : 0 < tbt3Sq x := by simp only [tbt3Sq]; nlinarith
        rw [div_le_div_iff₀ (by positivity) hp]
        simp only [tbt3Sq]; nlinarith
    _ ≤ ∫ x in A, 1 / tbt3Sq x :=
        setIntegral_mono_set hiA ((ae_restrict_iff' ((measurableSet_lt measurable_const
          tbt3_continuous_Sq.measurable).inter (measurableSet_lt tbt3_continuous_Sq.measurable
          measurable_const))).mpr (Filter.Eventually.of_forall fun x hx => by
            have : 2 < tbt3Sq x := hx.1; show (0 : ℝ) ≤ 1 / tbt3Sq x; exact div_nonneg zero_le_one (by linarith)))
          (Filter.Eventually.of_forall hSA)

/-! ### The fixed inner and outer contributions -/

/-- `(∇𝒱φ_in)ᵀ`, the inner field. -/
noncomputable def tbt3TIn (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  (jac (tbt3V tbt3PhiIn) x)ᵀ

/-- `(∇𝒱φ_out)ᵀ`, the outer field. -/
noncomputable def tbt3TOut (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  (jac (tbt3V tbt3PhiOut) x)ᵀ

/-- The inner contribution bound `M₁ = |∫_{|x|² ≤ 2} q₃ (T_in)| + ∫_{|x|² ≤ 2} |T_in|⁴`. -/
noncomputable def tbt3M1 : ℝ :=
  |∫ x in {z : Fin 2 → ℝ | tbt3Sq z ≤ 2}, q3 (tbt3TIn x)| +
    ∫ x in {z : Fin 2 → ℝ | tbt3Sq z ≤ 2}, frobSq (tbt3TIn x) ^ 2

/-- The outer contribution bound `M₃ = |∫_{|y|² ≥ 1} q₃ (T_out)| + ∫_{|y|² ≥ 1} |T_out|⁴`. -/
noncomputable def tbt3M3 : ℝ :=
  |∫ x in {z : Fin 2 → ℝ | 1 ≤ tbt3Sq z}, q3 (tbt3TOut x)| +
    ∫ x in {z : Fin 2 → ℝ | 1 ≤ tbt3Sq z}, frobSq (tbt3TOut x) ^ 2

theorem tbt3_continuous_TIn : Continuous tbt3TIn :=
  (continuous_id.matrix_transpose).comp (tbt3_continuous_jac (tbt3_contDiff_V tbt3_contDiff_PhiIn))

theorem tbt3_continuous_TOut : Continuous tbt3TOut :=
  (continuous_id.matrix_transpose).comp (tbt3_continuous_jac (tbt3_contDiff_V tbt3_contDiff_PhiOut))

theorem tbt3_isCompact_A1 : IsCompact {z : Fin 2 → ℝ | tbt3Sq z ≤ 2} := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin 2 → ℝ) 2)
    (isClosed_le tbt3_continuous_Sq continuous_const) fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  have h : z 0 ^ 2 + z 1 ^ 2 ≤ 2 := hz
  apply abs_le_of_sq_le_sq _ (by norm_num)
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]

theorem tbt3_hasCompactSupport_TOut : HasCompactSupport tbt3TOut := by
  have h1 : HasCompactSupport tbt3PhiOut := tbt3_hasCompactSupport_of_Sq (ρ := 2)
    fun z hz => tbt3_PhiOut_zero hz
  refine h1.mono' fun x hx => ?_
  by_contra hc
  apply hx
  have : x ∉ tsupport (tbt3V tbt3PhiOut) := fun h => hc (tbt3_tsupport_V_subset _ h)
  simp [tbt3TOut, tbt3_jac_eq_zero this]

/-- The inner region: `∫_{|x|² ≤ 2} q̂ (∇v_in) ≤ M₁` for `δ ≤ 1`. -/
theorem tbt3_inner_le {δ : ℝ} (hδ1 : δ ≤ 1) (Λ : ℝ) :
    ∫ x in {z : Fin 2 → ℝ | tbt3Sq z ≤ 2}, qHat δ Λ (jac (tbt3V tbt3PhiIn) x) ≤ tbt3M1 := by
  have hK := tbt3_isCompact_A1
  have h1 : IntegrableOn (fun x => q3 (tbt3TIn x)) {z : Fin 2 → ℝ | tbt3Sq z ≤ 2} :=
    (tbt_continuous_q3.comp tbt3_continuous_TIn).continuousOn.integrableOn_compact hK
  have h2 : IntegrableOn (fun x => frobSq (tbt3TIn x) ^ 2) {z : Fin 2 → ℝ | tbt3Sq z ≤ 2} :=
    ((tbt_continuous_frobSq.comp tbt3_continuous_TIn).pow 2).continuousOn.integrableOn_compact hK
  have e : ∀ x, qHat δ Λ (jac (tbt3V tbt3PhiIn) x) = q3 (tbt3TIn x) + δ * frobSq (tbt3TIn x) ^ 2 :=
    fun x => tbt3_qHat_jac δ Λ tbt3_contDiff_PhiIn x
  simp_rw [e]
  rw [integral_add h1 (h2.const_mul δ), integral_const_mul]
  have hnn : 0 ≤ ∫ x in {z : Fin 2 → ℝ | tbt3Sq z ≤ 2}, frobSq (tbt3TIn x) ^ 2 :=
    setIntegral_nonneg (measurableSet_le tbt3_continuous_Sq.measurable measurable_const)
      fun x _ => sq_nonneg _
  have := le_abs_self (∫ x in {z : Fin 2 → ℝ | tbt3Sq z ≤ 2}, q3 (tbt3TIn x))
  unfold tbt3M1
  nlinarith

/-- The outer region, rescaled: `∫_{|y|² ≥ 1} q̂ (∇v_out) ≤ M₃` for `δ ≤ 1`. -/
theorem tbt3_outer_le {δ : ℝ} (hδ1 : δ ≤ 1) (Λ : ℝ) :
    ∫ x in {z : Fin 2 → ℝ | 1 ≤ tbt3Sq z}, qHat δ Λ (jac (tbt3V tbt3PhiOut) x) ≤ tbt3M3 := by
  have hc := tbt3_hasCompactSupport_TOut
  have h1 : Integrable fun x => q3 (tbt3TOut x) :=
    (tbt_continuous_q3.comp tbt3_continuous_TOut).integrable_of_hasCompactSupport
      (hc.comp_left (g := q3) (by simp [tbt_q3_eq]))
  have h2 : Integrable fun x => frobSq (tbt3TOut x) ^ 2 := by
    have hcs : HasCompactSupport fun x => frobSq (tbt3TOut x) ^ 2 :=
      hc.comp_left (g := fun A => frobSq A ^ 2) (by simp [frobSq])
    exact ((tbt_continuous_frobSq.comp tbt3_continuous_TOut).pow 2).integrable_of_hasCompactSupport
      hcs
  have e : ∀ x, qHat δ Λ (jac (tbt3V tbt3PhiOut) x) = q3 (tbt3TOut x) + δ * frobSq (tbt3TOut x) ^ 2 :=
    fun x => tbt3_qHat_jac δ Λ tbt3_contDiff_PhiOut x
  simp_rw [e]
  rw [integral_add h1.integrableOn (h2.integrableOn.const_mul δ), integral_const_mul]
  have hnn : 0 ≤ ∫ x in {z : Fin 2 → ℝ | 1 ≤ tbt3Sq z}, frobSq (tbt3TOut x) ^ 2 :=
    setIntegral_nonneg (measurableSet_le measurable_const tbt3_continuous_Sq.measurable)
      fun x _ => sq_nonneg _
  have := le_abs_self (∫ x in {z : Fin 2 → ℝ | 1 ≤ tbt3Sq z}, q3 (tbt3TOut x))
  unfold tbt3M3
  nlinarith

/-! ### The energy of `v_R` -/

theorem tbt3_integrableOn_inv_Sq (R : ℝ) :
    IntegrableOn (fun x => 1 / tbt3Sq x) {z : Fin 2 → ℝ | 2 < tbt3Sq z ∧ tbt3Sq z < R ^ 2} := by
  set K := {z : Fin 2 → ℝ | 2 ≤ tbt3Sq z ∧ tbt3Sq z ≤ |R| ^ 2}
  have hK : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin 2 → ℝ) |R|)
      ((isClosed_le continuous_const tbt3_continuous_Sq).inter
        (isClosed_le tbt3_continuous_Sq continuous_const)) fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    have h : z 0 ^ 2 + z 1 ^ 2 ≤ |R| ^ 2 := hz.2
    rw [sq_abs] at h
    apply abs_le_of_sq_le_sq _ (abs_nonneg R)
    rw [sq_abs]
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  have hc : ContinuousOn (fun x => 1 / tbt3Sq x) K :=
    continuousOn_const.div tbt3_continuous_Sq.continuousOn fun x hx => by
      have : 2 ≤ tbt3Sq x := hx.1; linarith
  exact (hc.integrableOn_compact hK).mono_set fun x hx => ⟨hx.1.le, by rw [sq_abs]; exact hx.2.le⟩

theorem tbt3_qHat_zero (δ Λ : ℝ) : qHat δ Λ 0 = 0 := by
  have := tbt3_qHat_smul δ Λ 0 0
  simpa using this

theorem tbt3_hasCompactSupport_PhiR {R : ℝ} (hR : 0 < R) : HasCompactSupport (tbt3PhiR R) :=
  tbt3_hasCompactSupport_of_Sq (ρ := 2 * R ^ 2) fun _ hz => tbt3_PhiR_zero hR hz

theorem tbt3_integrable_energy {R : ℝ} (hR : 0 < R) (δ Λ : ℝ) :
    Integrable fun x => qHat δ Λ (jac (tbt3V (tbt3PhiR R)) x) := by
  refine (tbt3_continuous_qHat_jac δ Λ (tbt3_contDiff_PhiR R)).integrable_of_hasCompactSupport
    ((tbt3_hasCompactSupport_PhiR hR).mono' fun x hx => ?_)
  by_contra hc
  apply hx
  have : x ∉ tsupport (tbt3V (tbt3PhiR R)) := fun h => hc (tbt3_tsupport_V_subset _ h)
  simp [tbt3_jac_eq_zero this, tbt3_qHat_zero]

/-- **The energy estimate** (TeX 2131–2134):
`∫ q̂_{δ,Λ} (∇v_R) ≤ M₁ + M₃ − (75/16) · ½ log (R/4)` for `R > 4` and `0 ≤ δ ≤ δ₀`. -/
theorem tbt3_integral_le {R δ : ℝ} (hR : 4 < R) (hδ : 0 ≤ δ) (hδ₀ : δ ≤ 75 / 64000000) (Λ : ℝ) :
    ∫ x, qHat δ Λ (jac (tbt3V (tbt3PhiR R)) x) ≤
      tbt3M1 + tbt3M3 - 75 / 16 * (1 / 2 * Real.log (R / 4)) := by
  have hR0 : 0 < R := by linarith
  have hR4 : 4 < R ^ 2 := by nlinarith
  set f := fun x => qHat δ Λ (jac (tbt3V (tbt3PhiR R)) x) with hf_def
  have hf : Integrable f := tbt3_integrable_energy hR0 δ Λ
  set A1 := {z : Fin 2 → ℝ | tbt3Sq z ≤ 2}
  set A2 := {z : Fin 2 → ℝ | 2 < tbt3Sq z ∧ tbt3Sq z < R ^ 2}
  set A3 := {z : Fin 2 → ℝ | R ^ 2 ≤ tbt3Sq z}
  have hm : Measurable tbt3Sq := tbt3_continuous_Sq.measurable
  have hA1 : MeasurableSet A1 := measurableSet_le hm measurable_const
  have hA2 : MeasurableSet A2 := (measurableSet_lt measurable_const hm).inter
    (measurableSet_lt hm measurable_const)
  have hA3 : MeasurableSet A3 := measurableSet_le measurable_const hm
  have hcompl : A1ᶜ = A2 ∪ A3 := by
    ext x
    simp only [A1, A2, A3, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_le]
    constructor
    · intro h; by_cases h' : tbt3Sq x < R ^ 2
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr (not_lt.mp h')
    · rintro (h | h)
      · exact h.1
      · linarith
  have hdisj : Disjoint A2 A3 :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx' (not_le.mpr hx.2)
  have hsplit : ∫ x, f x = (∫ x in A1, f x) + ((∫ x in A2, f x) + (∫ x in A3, f x)) := by
    rw [← integral_add_compl hA1 hf, hcompl,
      setIntegral_union hdisj hA3 hf.integrableOn hf.integrableOn]
  -- the inner region
  have h1 : (∫ x in A1, f x) ≤ tbt3M1 := by
    have : ∫ x in A1, f x = ∫ x in A1, qHat δ Λ (jac (tbt3V tbt3PhiIn) x) :=
      setIntegral_congr_fun hA1 fun x hx => by
        simp only [hf_def]
        rw [tbt3_jac_in hR0 (lt_of_le_of_lt hx (by linarith))]
    rw [this]
    exact tbt3_inner_le (by linarith) Λ
  -- the outer region, rescaled
  have h3 : (∫ x in A3, f x) ≤ tbt3M3 := by
    set B3 := {z : Fin 2 → ℝ | 1 ≤ tbt3Sq z}
    set κ := R ^ (5 / 2 : ℝ) * R⁻¹ * R⁻¹ * R⁻¹
    have hκ : κ ^ 4 = (R ^ 2)⁻¹ := by
      have : (R ^ (5 / 2 : ℝ)) ^ 4 = R ^ 10 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
        norm_num
      simp only [κ, mul_pow, this]
      field_simp
    have hpt : ∀ x, A3.indicator f x =
        (R ^ 2)⁻¹ * B3.indicator (fun y => qHat δ Λ (jac (tbt3V tbt3PhiOut) y)) (R⁻¹ • x) := by
      intro x
      by_cases hx : x ∈ A3
      · have hy : R⁻¹ • x ∈ B3 := by
          show 1 ≤ tbt3Sq (R⁻¹ • x)
          rw [tbt3_Sq_smul, inv_pow, le_inv_mul_iff₀ (by positivity)]
          have : R ^ 2 ≤ tbt3Sq x := hx
          linarith
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
        simp only [hf_def]
        have hx' : R ^ 2 / 2 < tbt3Sq x := lt_of_lt_of_le (by linarith) hx
        rw [tbt3_jac_out hR0 hR4 hx', tbt3_qHat_smul, hκ]
      · have hy : R⁻¹ • x ∉ B3 := by
          intro hy
          apply hx
          show R ^ 2 ≤ tbt3Sq x
          have : 1 ≤ tbt3Sq (R⁻¹ • x) := hy
          rw [tbt3_Sq_smul, inv_pow, le_inv_mul_iff₀ (by positivity)] at this
          linarith
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy, mul_zero]
    rw [← integral_indicator hA3]
    simp_rw [hpt]
    rw [integral_const_mul, Measure.integral_comp_inv_smul, Module.finrank_fin_fun,
      integral_indicator (measurableSet_le measurable_const hm), abs_of_pos (by positivity),
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    exact tbt3_outer_le (by linarith) Λ
  -- the bulk
  have h2 : (∫ x in A2, f x) ≤ -(75 / 16) * (1 / 2 * Real.log (R / 4)) := by
    have hi := tbt3_integrableOn_inv_Sq R
    calc ∫ x in A2, f x ≤ ∫ x in A2, -(75 / 16) * (1 / tbt3Sq x) :=
          setIntegral_mono_on hf.integrableOn (hi.const_mul _) hA2 fun x hx => by
            have := tbt3_bulk_le hR0 hδ hδ₀ Λ hx
            simp only [hf_def]
            rw [mul_one_div]; exact this
      _ = -(75 / 16) * ∫ x in A2, 1 / tbt3Sq x := integral_const_mul _ _
      _ ≤ -(75 / 16) * (1 / 2 * Real.log (R / 4)) := by
          have := tbt3_J_lower hR
          nlinarith
  rw [hsplit]
  linarith

end Cassese
