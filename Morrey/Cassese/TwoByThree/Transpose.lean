module

public import Morrey.Cassese.TwoByThree.Transpose.Estimate
public import Morrey.Cassese.TwoByThree.Extension
public import Morrey.Cassese.Bridges

/-!
# Corollary 5.3: the transposed quartic on `ℝ^{3×2}`

The witness of the proof sketch (TeX 2102–2136): `v_R = 𝒱φ_R = (φ_xx − φ_yy, 2 φ_xy, Δφ)` for the
cut-off profile `φ_R` of `φ = r^{5/2} cos 3θ` (`Morrey/Cassese/TwoByThree/Transpose/*.lean`), has
`(∇v_R)ᵀ ∈ 𝓛₃`, so the normal penalty vanishes and `∫ q̂_{δ,Λ} (∇v_R) < 0` for `δ` small and `R`
large; rescaled into the unit square it refutes quasiconvexity at `0`, and homogeneity gives
"nowhere".

Helpers are prefixed `tbt3_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace Cassese

/-- For `0 ≤ δ ≤ δ₀ = 75 / (64·10⁶)` there is `R > 4` with `∫ q̂_{δ,Λ} (∇v_R) < 0`. -/
theorem tbt3_exists_R {δ : ℝ} (hδ : 0 ≤ δ) (hδ₀ : δ ≤ 75 / 64000000) (Λ : ℝ) :
    ∃ R : ℝ, 4 < R ∧ ∫ x, qHat δ Λ (jac (tbt3V (tbt3PhiR R)) x) < 0 := by
  set L := |32 / 75 * (tbt3M1 + tbt3M3)| + 1
  refine ⟨4 * Real.exp L, ?_, ?_⟩
  · have : 1 < Real.exp L := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  · have hR : 4 < 4 * Real.exp L := by
      have : 1 < Real.exp L := Real.one_lt_exp_iff.mpr (by positivity)
      linarith
    have h := tbt3_integral_le hR hδ hδ₀ Λ
    have hl : Real.log (4 * Real.exp L / 4) = L := by
      rw [mul_div_cancel_left₀ _ (by norm_num), Real.log_exp]
    rw [hl] at h
    have : 32 / 75 * (tbt3M1 + tbt3M3) ≤ |32 / 75 * (tbt3M1 + tbt3M3)| := le_abs_self _
    linarith

/-- The translation of `jac`. -/
theorem tbt3_jac_sub {n : ℕ} {W : (Fin 2 → ℝ) → Fin n → ℝ} (hW : Differentiable ℝ W)
    (c x : Fin 2 → ℝ) : jac (fun x => W (x - c)) x = jac W (x - c) := by
  ext i k
  have hi : DifferentiableAt ℝ (fun y => W y i) (x - c) := (differentiableAt_pi.mp (hW _)) i
  have h := hi.hasFDerivAt.comp x (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) c)
  simp only [jac, Matrix.of_apply]
  rw [show (fun y => W (y - c) i) = (fun y => W y i) ∘ fun y => y - c from rfl, h.fderiv]
  rfl

theorem tbt3_tsupport_PhiR {R : ℝ} (hR : 0 < R) :
    tsupport (tbt3PhiR R) ⊆ {z | tbt3Sq z ≤ 2 * R ^ 2} := by
  refine closure_minimal (fun z hz => ?_) (isClosed_le tbt3_continuous_Sq continuous_const)
  by_contra h
  exact hz (tbt3_PhiR_zero hR (not_le.mp h).le)

/-- `q̂_{δ,Λ}` is not quasiconvex at `0` for `0 < δ ≤ δ₀`: the rescaled witness
`x ↦ λ v_R ((x − c) / λ)`, `c = (1/2, 1/2)`, `λ = 1/(8R)`, has compact support in the open unit
square, the same gradients, and energy `λ² ∫ q̂ (∇v_R) < 0`. -/
theorem tbt3_not_quasiconvexAt {δ : ℝ} (hδ : 0 ≤ δ) (hδ₀ : δ ≤ 75 / 64000000) (Λ : ℝ) :
    ¬ QuasiconvexAt (qHat δ Λ) 0 := by
  obtain ⟨R, hR, hneg⟩ := tbt3_exists_R hδ hδ₀ Λ
  have hR0 : 0 < R := by linarith
  set v := tbt3V (tbt3PhiR R)
  have hv : ContDiff ℝ tbt3Top v := tbt3_contDiff_V (tbt3_contDiff_PhiR R)
  have hvd : Differentiable ℝ v := hv.differentiable (by simp)
  set c : Fin 2 → ℝ := fun _ => 1 / 2
  set l : ℝ := 1 / (8 * R)
  have hl : 0 < l := by positivity
  set W : (Fin 2 → ℝ) → Fin 3 → ℝ := fun z => l • v (l⁻¹ • z)
  have hWd : Differentiable ℝ W := (hvd.comp (differentiable_id.const_smul l⁻¹)).const_smul l
  set φ : (Fin 2 → ℝ) → Fin 3 → ℝ := fun x => W (x - c)
  have hφ : ContDiff ℝ tbt3Top φ :=
    ((hv.comp (contDiff_const_smul _)).const_smul l).comp (contDiff_id.sub contDiff_const)
  have hjac : ∀ x, jac φ x = jac v (l⁻¹ • (x - c)) := by
    intro x
    rw [tbt3_jac_sub hWd, tbt3_jac_scale hvd, mul_inv_cancel₀ hl.ne', one_smul]
  -- `v` vanishes outside `|z|² ≤ 2R²`, so `φ` vanishes outside the ball of radius `1/4` about `c`
  have hvz : ∀ z, 2 * R ^ 2 < tbt3Sq z → v z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h =>
      absurd ((tbt3_tsupport_PhiR hR0) (tbt3_tsupport_V_subset _ h)) (not_le.mpr hz)
  have hφz : ∀ x, x ∉ Metric.closedBall c (1 / 4) → φ x = 0 := by
    intro x hx
    simp only [Metric.mem_closedBall, not_le] at hx
    obtain ⟨i, hi⟩ : ∃ i, 1 / 4 < |x i - c i| := by
      by_contra hcon
      push Not at hcon
      have : dist x c ≤ 1 / 4 := (dist_pi_le_iff (by norm_num)).mpr fun i => by
        rw [Real.dist_eq]; exact hcon i
      linarith
    have hS : 2 * R ^ 2 < tbt3Sq (l⁻¹ • (x - c)) := by
      have h1 : 2 * R < |(l⁻¹ • (x - c)) i| := by
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, l]
        rw [abs_of_pos (by positivity)]
        field_simp
        nlinarith
      have h2 : (2 * R) ^ 2 < ((l⁻¹ • (x - c)) i) ^ 2 := by
        rw [← sq_abs ((l⁻¹ • (x - c)) i)]
        exact pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
      have h3 : ∀ (y : Fin 2 → ℝ) (j : Fin 2), (y j) ^ 2 ≤ tbt3Sq y := by
        intro y j
        fin_cases j <;> simp [tbt3Sq] <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
      have := h3 (l⁻¹ • (x - c)) i
      nlinarith
    simp only [φ, W, hvz _ hS, smul_zero]
  have hball : Metric.closedBall c (1 / 4) ⊆ unitCube 2 := by
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
  refine not_quasiconvexAt_of_smooth (tbt3_continuous_qHat δ Λ) hφ hc (hts.trans hball) ?_
  -- the energy of the rescaled witness
  have hout : ∀ x, x ∉ unitCube 2 → qHat δ Λ (0 + jac φ x) = 0 := by
    intro x hx
    have : x ∉ tsupport φ := fun h => hx (hball (hts h))
    rw [tbt3_jac_eq_zero this, add_zero, tbt3_qHat_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout, tbt3_qHat_zero]
  simp_rw [zero_add, hjac]
  rw [integral_sub_right_eq_self (fun x => qHat δ Λ (jac v (l⁻¹ • x))) c,
    Measure.integral_comp_inv_smul (μ := volume) (fun y => qHat δ Λ (jac v y)) l,
    Module.finrank_fin_fun,
    smul_eq_mul]
  exact mul_neg_of_pos_of_neg (abs_pos.mpr (by positivity)) hneg

/-- `q̂_{δ,Λ}` is `4`-homogeneous. -/
theorem tbt3_isPHomogeneous_qHat (δ Λ : ℝ) : IsPHomogeneous 4 (qHat δ Λ) := by
  intro t A
  rw [tbt3_qHat_smul, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs,
    abs_of_nonneg (by positivity)]

/-- Rank-one convexity passes to the transposes. -/
theorem tbt3_rankOneConvex_qHat {δ Λ : ℝ} (h : RankOneConvex (qDeltaLambda δ Λ)) :
    RankOneConvex (qHat δ Λ) := by
  intro A B hAB
  have h' := h Aᵀ Bᵀ (by rw [← Matrix.transpose_sub, Matrix.rank_transpose]; exact hAB)
  simpa only [qHat, Matrix.transpose_add, Matrix.transpose_smul] using h'

/-- **Corollary 5.3** (`cor:transp`): for `K` sufficiently large and `δ > 0` sufficiently small,
with `Λ = K/δ`, `q̂_{δ,Λ} (A) = q_{δ,Λ} (Aᵀ)` on `ℝ^{3×2}` is a homogeneous quartic polynomial
which is globally rank-one convex and nowhere quasiconvex.

Proof, after the paper's sketch (TeX 2102–2136). The rank-one convexity of `q_{δ,K/δ}` for `K ≥ K₀`,
`0 < δ ≤ 1` (`qDeltaLambda_rankOneConvex`, from Lemma 5.1 (2)) passes to the transposes
(`tbt3_rankOneConvex_qHat`), and `q̂_{δ,Λ}` is a homogeneous quartic (`tbt_ihp_qHat`). For the
failure of quasiconvexity, the witness is `v_R = (φ_xx − φ_yy, 2 φ_xy, Δφ)` built from the cut-off
`φ_R` of `φ = r^{5/2} cos 3θ` (`tbt3V`, `tbt3PhiR`): `(∇v_R)ᵀ ∈ 𝓛₃` (symmetry of the third
derivatives, `tbt3_jac_V_transpose`), so the normal penalty vanishes and
`q̂_{δ,Λ} (∇v_R) = q₃ ((∇v_R)ᵀ) + δ |∇v_R|⁴` whatever `Λ`. In the bulk `2 < |x|² < R²`,
`q₃ ≤ −c / |x|²` and `|∇v|⁴ ≤ C / |x|²` with `c = 75/8`, `C = 4·10⁶` (`tbt3_bulk_bounds`; the
paper's numerical values are `c ≈ 1029.8`, `C ≈ 62938`, inventory E17, and any `c > 0`, `C < ∞`
suffice); the inner region `|x|² ≤ 2` and the outer region `|x|² ≥ R²` (where `∇v_R (x) =
R^{−1/2} ∇v_out (x/R)`, so its energy does not depend on `R`) contribute a bounded amount
`M₁ + M₃`; hence for `0 < δ ≤ δ₀ = 75/(64·10⁶)`,
`∫ q̂_{δ,Λ} (∇v_R) ≤ M₁ + M₃ − (75/32) log (R/4) < 0` for `R` large (`tbt3_integral_le`,
`tbt3_exists_R`), the paper's `2π (−c + Cδ) log R + O(1) < 0`. Rescaled into the open unit square
the witness refutes quasiconvexity at `0` (`tbt3_not_quasiconvexAt`), and `4`-homogeneity gives
"nowhere" (Toolkit's `nowhereQuasiconvex_of_not_quasiconvexAt_zero`, the consequence of
Proposition 2.3 that the route `cs-envelope-cons` names).

Details that the sketch leaves open, filled in (not departures of argument): the cut-offs are
`σ (|x|² − 1)` and `σ (2 − |x|²/R²)` with `σ = Real.smoothTransition` (the paper: "cutting off
`φ` smoothly at radii `1` and `R`"), and the outer profile `φ_out = σ (4|y|² − 1) σ (2 − |y|²) φ`
carries an extra inner cut-off so that it is smooth (it is used only on `|y|² ≥ 1/2`); the
logarithmic divergence `∫_{2 < |x|² < R²} |x|⁻² dx` is bounded below by `½ log (R/4)`, its integral
over the triangle `2 < x₀ < R/2`, `0 < x₁ < x₀` (Tonelli, `tbt3_J_lower`), instead of being
computed as `2π log (R/√2)` in polar coordinates; only its divergence is used. -/
theorem corollary5_3 :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      IsHomogeneousPolynomial 4 (qHat δ (K / δ)) ∧ RankOneConvex (qHat δ (K / δ)) ∧
        NowhereQuasiconvex (qHat δ (K / δ)) := by
  obtain ⟨K₀, -, hK₀⟩ := qDeltaLambda_rankOneConvex
  refine ⟨K₀, fun K hK => ⟨75 / 64000000, by norm_num, fun δ hδ hδ₀ => ?_⟩⟩
  refine ⟨tbt_ihp_qHat δ (K / δ),
    tbt3_rankOneConvex_qHat (hK₀ K hK δ hδ (by linarith)).2, ?_⟩
  exact nowhereQuasiconvex_of_not_quasiconvexAt_zero (p := 4) (by norm_num)
    (tbt3_continuous_qHat δ (K / δ)) (Or.inl (tbt3_isPHomogeneous_qHat δ (K / δ)))
    (tbt3_not_quasiconvexAt hδ.le hδ₀.le (K / δ))

end Cassese
