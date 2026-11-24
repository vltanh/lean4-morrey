module

public import Morrey.Cassese.TwoByThree.Transpose.Cutoff
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Corollary 5.3: the energy of the cut-off witness

The energy estimate of the proof sketch (TeX 2121–2134) for `v_R = 𝒱φ_R`, `R > 2`, `0 ≤ δ ≤ 1`:
`∫ q̂_{δ,Λ} (∇v_R) ≤ 2π (−c + C δ) log R + O(1)` with `c = 75/8`, `C = 4·10⁶` and
`O(1) = M₁ + M₃ + π (c − C δ) log 2` (`tbt3_integral_le`). The plane splits into the inner region
`|x|² ≤ 2`, the bulk `2 < |x|² < R²` and the outer region `|x|² ≥ R²`. In the bulk
`q̂_{δ,Λ} (∇v_R) ≤ (−c + C δ) / |x|²` (`tbt3_bulk_le`), and
`∫_{2 < |x|² < R²} |x|⁻² dx = 2π log (R/√2)` in polar coordinates (`tbt3_integral_inv_Sq_bulk`).
The inner region and the outer region (rescaled to `|y|² ≥ 1`) contribute at most the constants
`M₁`, `M₃`, which do not depend on `R` (`tbt3_inner_le`, `tbt3_outer_le`).

Helpers are prefixed `tbt3_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal Real

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

/-- The bulk (TeX 2121–2123): on `2 < |x|² < R²`, where `φ_R = φ`, the bounds
`q₃ ((∇v)ᵀ) ≤ −c / |x|²` and `|∇v|⁴ ≤ C / |x|²` with `c = 75/8`, `C = 4·10⁶` (`tbt3_bulk_bounds`)
give `q̂_{δ,Λ} (∇v_R) = q₃ ((∇v)ᵀ) + δ |∇v|⁴ ≤ (−c + C δ) / |x|²` for `δ ≥ 0`. -/
theorem tbt3_bulk_le {R δ : ℝ} (hR : 0 < R) (hδ : 0 ≤ δ) (Λ : ℝ)
    {x : Fin 2 → ℝ} (hx : 2 < tbt3Sq x ∧ tbt3Sq x < R ^ 2) :
    qHat δ Λ (jac (tbt3V (tbt3PhiR R)) x) ≤ (-(75 / 8) + 4000000 * δ) / tbt3Sq x := by
  rw [tbt3_qHat_jac δ Λ (tbt3_contDiff_PhiR R), tbt3_jac_bulk hR hx]
  have hs : 0 < MvPolynomial.eval x tbt3S := by rw [tbt3_eval_S]; exact lt_trans two_pos hx.1
  obtain ⟨h1, h2⟩ := tbt3_bulk_bounds hs
  rw [tbt3_eval_S] at h1 h2
  have hS : tbt3Sq x = x 0 ^ 2 + x 1 ^ 2 := rfl
  rw [hS]
  have h3 : δ * frobSq (tbt3T _ _ _ _) ^ 2 ≤ δ * (4000000 / (x 0 ^ 2 + x 1 ^ 2)) :=
    mul_le_mul_of_nonneg_left h2 hδ
  have h4 : (-(75 / 8) + 4000000 * δ) / (x 0 ^ 2 + x 1 ^ 2) =
      -(75 / 8) / (x 0 ^ 2 + x 1 ^ 2) + δ * (4000000 / (x 0 ^ 2 + x 1 ^ 2)) := by ring
  linarith

/-! ### The bulk integral in polar coordinates -/

/-- The bulk integral in polar coordinates (TeX 2131–2134):
`∫_{2 < |x|² < R²} |x|⁻² dx = ∫_{−π}^{π} ∫_{√2}^{R} r⁻¹ dr dθ = 2π log (R/√2)` for `R > √2`.
The plane `Fin 2 → ℝ` is carried to `ℝ × ℝ` (`volume_preserving_finTwoArrow`) and then to polar
coordinates `(r, θ) ∈ (0, ∞) × (−π, π)` (`integral_comp_polarCoord_symm`, Jacobian `r`), where the
integrand is `1_{√2 < r < R} r⁻¹ · 1`, a product (`setIntegral_prod_mul`). -/
theorem tbt3_integral_inv_Sq_bulk {R : ℝ} (hR : √2 < R) :
    ∫ x in {z : Fin 2 → ℝ | 2 < tbt3Sq z ∧ tbt3Sq z < R ^ 2}, 1 / tbt3Sq x =
      2 * π * Real.log (R / √2) := by
  have hR0 : 0 < R := lt_of_le_of_lt (Real.sqrt_nonneg 2) hR
  set A := {z : Fin 2 → ℝ | 2 < tbt3Sq z ∧ tbt3Sq z < R ^ 2}
  have hm : Measurable tbt3Sq := tbt3_continuous_Sq.measurable
  have hA : MeasurableSet A := (measurableSet_lt measurable_const hm).inter
    (measurableSet_lt hm measurable_const)
  set e := MeasurableEquiv.finTwoArrow (α := ℝ)
  have he : MeasurePreserving e.symm volume volume := (volume_preserving_finTwoArrow ℝ).symm
  rw [← integral_indicator hA, ← he.integral_comp' (A.indicator fun x => 1 / tbt3Sq x),
    ← integral_comp_polarCoord_symm]
  -- the integrand in polar coordinates: `r · 1_{2 < r² < R²} r⁻² = 1_{√2 < r < R} r⁻¹`
  have hpt : ∀ p ∈ polarCoord.target,
      p.1 • A.indicator (fun x => 1 / tbt3Sq x) (e.symm (polarCoord.symm p)) =
        (Set.Ioo (√2) R).indicator (fun r => r⁻¹) p.1 * (fun _ => (1 : ℝ)) p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr : 0 < r := hr
    have hS : tbt3Sq (e.symm (polarCoord.symm (r, θ))) = r ^ 2 := by
      simp [e, tbt3Sq, polarCoord_symm_apply]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hiff : e.symm (polarCoord.symm (r, θ)) ∈ A ↔ r ∈ Set.Ioo (√2) R := by
      simp only [A, Set.mem_ofPred_eq, hS, Set.mem_Ioo]
      rw [Real.sqrt_lt' hr, pow_lt_pow_iff_left₀ hr.le hR0.le two_ne_zero]
    by_cases h : r ∈ Set.Ioo (√2) R
    · rw [Set.indicator_of_mem (hiff.mpr h), Set.indicator_of_mem h, hS, smul_eq_mul]
      field_simp
    · rw [Set.indicator_of_notMem (mt hiff.mp h), Set.indicator_of_notMem h, smul_zero, zero_mul]
  -- Fubini on `(0, ∞) × (−π, π)`: `∫_{√2}^{R} r⁻¹ dr = log (R/√2)` and `∫_{−π}^{π} dθ = 2π`
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hpt, polarCoord_target,
    Measure.volume_eq_prod,
    setIntegral_prod_mul ((Set.Ioo (√2) R).indicator fun r => r⁻¹) (fun _ => (1 : ℝ)),
    setIntegral_indicator measurableSet_Ioo,
    Set.inter_eq_right.mpr
      (Set.Ioo_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (Real.sqrt_nonneg 2))),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    integral_inv_of_pos (Real.sqrt_pos.2 two_pos) hR0, setIntegral_const,
    Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_eq_mul]
  ring

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

/-- **The energy estimate** (TeX 2131–2134): for `R > 2` and `0 ≤ δ ≤ 1`,
`∫ q̂_{δ,Λ} (∇v_R) ≤ 2π (−c + C δ) log R + O(1)` with `c = 75/8`, `C = 4·10⁶` and
`O(1) = M₁ + M₃ + π (c − C δ) log 2`. The plane splits into the inner region `|x|² ≤ 2`, where
`v_R = 𝒱φ_in` and the energy is at most `M₁` (`tbt3_inner_le`); the bulk `2 < |x|² < R²`, where
`q̂_{δ,Λ} (∇v_R) ≤ (−c + C δ) / |x|²` (`tbt3_bulk_le`) and `∫ |x|⁻² = 2π log (R/√2)` in polar
coordinates (`tbt3_integral_inv_Sq_bulk`); and the outer region `|x|² ≥ R²`, where
`∇v_R (x) = R^{−1/2} ∇v_out (x/R)`, so that its energy is that of `v_out` on `|y|² ≥ 1`, at most
`M₃` (`tbt3_outer_le`). -/
theorem tbt3_integral_le {R δ : ℝ} (hR : 2 < R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (Λ : ℝ) :
    ∫ x, qHat δ Λ (jac (tbt3V (tbt3PhiR R)) x) ≤
      2 * π * (-(75 / 8) + 4000000 * δ) * Real.log R +
        (tbt3M1 + tbt3M3 + π * (75 / 8 - 4000000 * δ) * Real.log 2) := by
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
    exact tbt3_inner_le hδ1 Λ
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
    exact tbt3_outer_le hδ1 Λ
  -- the bulk, in polar coordinates
  have h2 : (∫ x in A2, f x) ≤ (-(75 / 8) + 4000000 * δ) * (2 * π * Real.log (R / √2)) := by
    have hi := tbt3_integrableOn_inv_Sq R
    have hR2 : √2 < R := lt_trans ((Real.sqrt_lt' two_pos).mpr (by norm_num)) hR
    calc ∫ x in A2, f x ≤ ∫ x in A2, (-(75 / 8) + 4000000 * δ) * (1 / tbt3Sq x) :=
          setIntegral_mono_on hf.integrableOn (hi.const_mul _) hA2 fun x hx => by
            have := tbt3_bulk_le hR0 hδ Λ hx
            simp only [hf_def]
            rw [mul_one_div]; exact this
      _ = (-(75 / 8) + 4000000 * δ) * ∫ x in A2, 1 / tbt3Sq x := integral_const_mul _ _
      _ = (-(75 / 8) + 4000000 * δ) * (2 * π * Real.log (R / √2)) := by
          rw [tbt3_integral_inv_Sq_bulk hR2]
  -- `2π log (R/√2) = 2π log R − π log 2`
  have hlog : Real.log (R / √2) = Real.log R - Real.log 2 / 2 := by
    rw [Real.log_div hR0.ne' (Real.sqrt_pos.2 two_pos).ne', Real.log_sqrt zero_le_two]
  rw [hlog] at h2
  rw [hsplit]
  linarith

end Cassese
