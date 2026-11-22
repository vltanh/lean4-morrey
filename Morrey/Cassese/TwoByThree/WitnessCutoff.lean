module

public import Morrey.Cassese.TwoByThree.Witness
public import Morrey.Cassese.TwoByThree.Polynomial
public import Morrey.Cassese.Bridges
public import Morrey.Cassese.TwoByThree.Transpose.Estimate
public import Morrey.Cassese.TwoByThree.Extension

/-!
# Section 5: the cutoff of the witness of Proposition 5.2 (proof of Theorem 1.3 (a))

The proof of Theorem 1.3 (a) (TeX lines 1977–2029) cuts off the witness `u` of Proposition 5.2,
`u_R = χ (·/R) u`, and estimates `∫ q_{δ,Λ} (∇u_R)` with `Λ = K/δ`, `R = δ⁻⁴`.

The intermediate claims of the paper are stated abstractly in the bulk field `G ∈ 𝓛₃` and the
cut-off error `E_R`, so that Corollary 5.4 uses them unchanged: `∫ |E_R|⁴ ≲ R⁻¹`
(`tbt4_integral_E4_le`); the Hölder step
`∫ q₃ (π ∇u_R) = ∫ χ (·/R)⁴ q₃ (G) + O (R^{−1/4} (log R)^{3/4})` (`tbt4_holder`, from the
two-sided quartic bound `tbt4_q3_perturb`); `∫ χ (·/R)⁴ q₃ (G) → I = ∫ q₃ (G)`
(`tbt4_tendsto_integral_chi`), so `∫ q₃ (π ∇u_R) = I + o_R (1)` (`tbt4_tendsto_q3_proj`);
`∫ |π ∇u_R|⁴ ≲ 1 + log R` and `∫ |π^⊥ ∇u_R|⁴ ≲ R⁻¹` (`tbt4_proj4_le`, `tbt4_perp4_le`); the
penalty bound and the resulting `∫ q_{δ,Λ} (∇u_R) ≤ I + o_R (1) + C₀ δ (1 + log R + Λ⁴/R)`
(`tbt4_energy`, `tbt4_energy_le`); the limit `δ ↓ 0` with `R = δ⁻⁴` (`tbt4_tendsto_rhs`); and the
whole chain `tbt4_cutoff_neg`. The rescaling into the unit cube is
`tbt4_not_quasiconvexAt_of_witness`.

Helpers are prefixed `tbt4_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace Cassese


theorem tbt4_contDiff_q3 : ContDiff ℝ 1 fun V : Fin 2 → Fin 3 → ℝ => q3 (Matrix.of V) := by
  have he : ∀ (i : Fin 2) (j : Fin 3), ContDiff ℝ 1 fun X : Fin 2 → Fin 3 → ℝ => X i j :=
    fun i j => contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) i j
  simp only [tbt_q3_eq, Matrix.of_apply]
  have h00 := he 0 0; have h01 := he 0 1; have h02 := he 0 2
  have h10 := he 1 0; have h11 := he 1 1; have h12 := he 1 2
  fun_prop

theorem tbt4_norm_le_sqrt_frobSq (V : Fin 2 → Fin 3 → ℝ) : ‖V‖ ≤ √(frobSq (Matrix.of V)) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have h1 : V i j ^ 2 ≤ ∑ j', V i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => V i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', V i j' ^ 2 ≤ ∑ i', ∑ j', V i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', V i' j' ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  simp only [frobSq, Matrix.of_apply]
  linarith

/-- The two-sided perturbation bound for the quartic `q₃`:
`|q₃ (X + Y) − q₃ (X)| ≤ L |X|³ |Y| + M |Y|⁴` (Frobenius norms). -/
theorem tbt4_q3_perturb : ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧ ∀ X Y : Matrix (Fin 2) (Fin 3) ℝ,
    |q3 (X + Y) - q3 X| ≤ L * √(frobSq X) ^ 3 * √(frobSq Y) + M * √(frobSq Y) ^ 4 := by
  set g : (Fin 2 → Fin 3 → ℝ) → ℝ := fun V => q3 (Matrix.of V)
  have hg := tbt4_contDiff_q3
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgc : Continuous g := hg.continuous
  have hfc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hsm : ∀ (t : ℝ) (V : Fin 2 → Fin 3 → ℝ), g (t • V) = t ^ 4 * g V := fun t V =>
    tbt_q3_smul t (Matrix.of V)
  obtain ⟨L₀, hL₀⟩ := (isCompact_closedBall (0 : Fin 2 → Fin 3 → ℝ) 2).exists_bound_of_continuousOn
    hfc.continuousOn
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : Fin 2 → Fin 3 → ℝ) 1).exists_bound_of_continuousOn
    hgc.continuousOn
  have hL₀' : 0 ≤ L₀ := (norm_nonneg _).trans (hL₀ 0 (Metric.mem_closedBall_self (by norm_num)))
  have hM₀' : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0 (Metric.mem_closedBall_self (by norm_num)))
  -- the mean value inequality on the ball of radius `2`
  have hlip : ∀ V ∈ Metric.closedBall (0 : Fin 2 → Fin 3 → ℝ) 2,
      ∀ W ∈ Metric.closedBall (0 : Fin 2 → Fin 3 → ℝ) 2, ‖g V - g W‖ ≤ L₀ * ‖V - W‖ :=
    fun V hV W hW => (convex_closedBall 0 2).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hgd x) (fun x hx => hL₀ x hx) hW hV
  -- `|g (Z)| ≤ M₀ ‖Z‖⁴`
  have hbd : ∀ Z, |g Z| ≤ M₀ * ‖Z‖ ^ 4 := by
    intro Z
    rcases eq_or_ne Z 0 with rfl | hZ
    · have : g 0 = 0 := by simpa using hsm 0 0
      simp [this]
    · have hn : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
      have hZ' : Z = ‖Z‖ • (‖Z‖⁻¹ • Z) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have hu : ‖Z‖⁻¹ • Z ∈ Metric.closedBall (0 : Fin 2 → Fin 3 → ℝ) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hn.ne']
      have := hM₀ _ hu
      rw [hZ', hsm, abs_mul, abs_of_nonneg (by positivity)]
      rw [Real.norm_eq_abs] at this
      calc ‖Z‖ ^ 4 * |g (‖Z‖⁻¹ • Z)| ≤ ‖Z‖ ^ 4 * M₀ := by gcongr
        _ = M₀ * ‖‖Z‖ • (‖Z‖⁻¹ • Z)‖ ^ 4 := by rw [← hZ']; ring
  -- the bound in the sup norm
  have key : ∀ V W : Fin 2 → Fin 3 → ℝ,
      |g (V + W) - g V| ≤ L₀ * ‖V‖ ^ 3 * ‖W‖ + 17 * M₀ * ‖W‖ ^ 4 := by
    intro V W
    by_cases hc : ‖W‖ ≤ ‖V‖ ∧ V ≠ 0
    · obtain ⟨hWV, hV⟩ := hc
      have hn : 0 < ‖V‖ := norm_pos_iff.mpr hV
      set μ := ‖V‖⁻¹
      have hμ : 0 < μ := inv_pos.mpr hn
      have h1 : μ • V ∈ Metric.closedBall (0 : Fin 2 → Fin 3 → ℝ) 2 := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hμ.le,
          inv_mul_cancel₀ hn.ne']; norm_num
      have h2 : μ • (V + W) ∈ Metric.closedBall (0 : Fin 2 → Fin 3 → ℝ) 2 := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hμ.le]
        calc μ * ‖V + W‖ ≤ μ * (‖V‖ + ‖W‖) := by gcongr; exact norm_add_le _ _
          _ ≤ μ * (‖V‖ + ‖V‖) := by gcongr
          _ = 2 := by rw [mul_add, inv_mul_cancel₀ hn.ne']; norm_num
      have h3 := hlip _ h2 _ h1
      rw [hsm, hsm, ← mul_sub, smul_add, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hμ.le, norm_mul, Real.norm_of_nonneg (by positivity)] at h3
      have hμ4 : μ ^ 4 * ‖V‖ ^ 4 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hn.ne', one_pow]
      have : |g (V + W) - g V| = ‖g (V + W) - g V‖ := (Real.norm_eq_abs _).symm
      have h4 : ‖g (V + W) - g V‖ = ‖V‖ ^ 4 * (μ ^ 4 * ‖g (V + W) - g V‖) := by
        rw [← mul_assoc, mul_comm (‖V‖ ^ 4), hμ4, one_mul]
      have h5 : ‖V‖ ^ 4 * (μ ^ 4 * ‖g (V + W) - g V‖) ≤ ‖V‖ ^ 4 * (L₀ * (μ * ‖W‖)) := by
        gcongr
      have h6 : ‖V‖ ^ 4 * (L₀ * (μ * ‖W‖)) = L₀ * ‖V‖ ^ 3 * ‖W‖ := by
        simp only [μ]; field_simp
      have : 0 ≤ 17 * M₀ * ‖W‖ ^ 4 := by positivity
      linarith
    · have hVW : ‖V‖ ≤ ‖W‖ := by
        by_contra h
        push Not at h
        exact hc ⟨h.le, fun hV => by rw [hV, norm_zero] at h; exact absurd h (not_lt.mpr (norm_nonneg _))⟩
      have h1 := hbd (V + W)
      have h2 := hbd V
      have h3 : ‖V + W‖ ≤ 2 * ‖W‖ := by
        calc ‖V + W‖ ≤ ‖V‖ + ‖W‖ := norm_add_le _ _
          _ ≤ 2 * ‖W‖ := by linarith
      have h4 : ‖V + W‖ ^ 4 ≤ 16 * ‖W‖ ^ 4 := by
        calc ‖V + W‖ ^ 4 ≤ (2 * ‖W‖) ^ 4 := by gcongr
          _ = 16 * ‖W‖ ^ 4 := by ring
      have h5 : ‖V‖ ^ 4 ≤ ‖W‖ ^ 4 := by gcongr
      have : 0 ≤ L₀ * ‖V‖ ^ 3 * ‖W‖ := by positivity
      have := le_abs_self (g (V + W))
      have := neg_abs_le (g (V + W))
      have := le_abs_self (g V)
      have := neg_abs_le (g V)
      rw [abs_sub_le_iff]
      constructor <;>
        nlinarith [mul_le_mul_of_nonneg_left h4 hM₀', mul_le_mul_of_nonneg_left h5 hM₀']
  refine ⟨L₀, 17 * M₀, hL₀', by positivity, fun X Y => ?_⟩
  set V : Fin 2 → Fin 3 → ℝ := fun i j => X i j
  set W : Fin 2 → Fin 3 → ℝ := fun i j => Y i j
  have h := key V W
  have hX : ‖V‖ ≤ √(frobSq X) := tbt4_norm_le_sqrt_frobSq V
  have hY : ‖W‖ ≤ √(frobSq Y) := tbt4_norm_le_sqrt_frobSq W
  have hX0 := norm_nonneg V
  have hY0 := norm_nonneg W
  have e1 : L₀ * ‖V‖ ^ 3 * ‖W‖ ≤ L₀ * √(frobSq X) ^ 3 * √(frobSq Y) := by gcongr
  have e2 : 17 * M₀ * ‖W‖ ^ 4 ≤ 17 * M₀ * √(frobSq Y) ^ 4 := by gcongr
  have e3 : g (V + W) = q3 (X + Y) := rfl
  have e4 : g V = q3 X := rfl
  rw [e3, e4] at h
  linarith

theorem tbt4_frobSq_add_le {d m : ℕ} (A B : Matrix (Fin d) (Fin m) ℝ) :
    frobSq (A + B) ≤ 2 * frobSq A + 2 * frobSq B := by
  simp only [frobSq, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
    nlinarith [sq_nonneg (A i j - B i j)]

/-- Pythagoras for `π`: `|E|² = |π E|² + |π^⊥ E|²`. -/
theorem tbt4_frobSq_pythagoras (E : Matrix (Fin 2) (Fin 3) ℝ) :
    frobSq E = frobSq (projL3 E) + frobSq (E - projL3 E) := by
  simp [frobSq, projL3, Fin.sum_univ_two, Fin.sum_univ_three]; ring

/-- For `G ∈ 𝓛₃`: `π (χ G + E) = χ G + π E`. -/
theorem tbt4_proj_add {G : Matrix (Fin 2) (Fin 3) ℝ} (hG : G ∈ L3) (χ : ℝ)
    (E : Matrix (Fin 2) (Fin 3) ℝ) : projL3 (χ • G + E) = χ • G + projL3 E := by
  rw [add_comm, tbt_projL3_add_smul, tbt3_projL3_of_mem hG, add_comm]

/-- For `G ∈ 𝓛₃`: `π^⊥ (χ G + E) = π^⊥ E`. -/
theorem tbt4_perp_add {G : Matrix (Fin 2) (Fin 3) ℝ} (hG : G ∈ L3) (χ : ℝ)
    (E : Matrix (Fin 2) (Fin 3) ℝ) : χ • G + E - projL3 (χ • G + E) = E - projL3 E := by
  rw [tbt4_proj_add hG]; abel

theorem tbt4_continuous_projL3 : Continuous projL3 := tbt1_continuous_proj isFrobProj_projL3

theorem tbt4_projL3_zero : projL3 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [projL3]

theorem tbt4_q3_zero : q3 0 = 0 := by simpa using tbt_q3_smul 0 0

/-- The pointwise form of the paper's first display (TeX 2005–2014): for `G ∈ 𝓛₃` and
`χ ∈ [0, 1]`, `π (χ G + E) = χ G + π E`, so the two-sided bound `tbt4_q3_perturb` at `X = χ G`,
`Y = π E` gives `|q₃ (π (χ G + E)) − χ⁴ q₃ (G)| ≤ L |G|³ |E| + M |E|⁴`. -/
theorem tbt4_q3_proj_sub_le {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hpert : ∀ X Y : Matrix (Fin 2) (Fin 3) ℝ,
      |q3 (X + Y) - q3 X| ≤ L * √(frobSq X) ^ 3 * √(frobSq Y) + M * √(frobSq Y) ^ 4)
    {G E : Matrix (Fin 2) (Fin 3) ℝ} (hG : G ∈ L3) {χ : ℝ} (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) :
    |q3 (projL3 (χ • G + E)) - χ ^ 4 * q3 G| ≤
      L * (√(frobSq G) ^ 3 * √(frobSq E)) + M * frobSq E ^ 2 := by
  have hpy := tbt4_frobSq_pythagoras E
  have hP0 := tbt_frobSq_nonneg (projL3 E)
  have hN0 := tbt_frobSq_nonneg (E - projL3 E)
  have hPE : frobSq (projL3 E) ≤ frobSq E := by linarith
  have hχG : frobSq (χ • G) ≤ frobSq G := by
    rw [tbt_frobSq_smul]
    have : χ ^ 2 ≤ 1 := by nlinarith
    nlinarith [tbt_frobSq_nonneg G]
  have h1 : √(frobSq (χ • G)) ≤ √(frobSq G) := Real.sqrt_le_sqrt hχG
  have h2 : √(frobSq (projL3 E)) ≤ √(frobSq E) := Real.sqrt_le_sqrt hPE
  have h3 : √(frobSq (projL3 E)) ^ 4 ≤ frobSq E ^ 2 := by
    rw [show √(frobSq (projL3 E)) ^ 4 = (√(frobSq (projL3 E)) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hP0]
    exact pow_le_pow_left₀ hP0 hPE 2
  have h := hpert (χ • G) (projL3 E)
  rw [tbt_q3_smul] at h
  rw [tbt4_proj_add hG]
  have e1 : L * √(frobSq (χ • G)) ^ 3 * √(frobSq (projL3 E)) ≤
      L * (√(frobSq G) ^ 3 * √(frobSq E)) := by
    rw [mul_assoc]; gcongr
  have e2 := mul_le_mul_of_nonneg_left h3 hM
  linarith

theorem tbt4_qDeltaLambda_zero (δ Λ : ℝ) : qDeltaLambda δ Λ 0 = 0 := by
  have h0 : (0 : Matrix (Fin 2) (Fin 3) ℝ) ∈ L3 := by rw [mem_L3_iff]; simp
  rw [tbt3_qDeltaLambda_of_mem δ Λ h0, tbt4_q3_zero]
  simp [frobSq]

theorem tbt4_lt_sum_sq {x : Fin 3 → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : r < ‖x‖) :
    r ^ 2 < ∑ i, x i ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, r < |x i| := by
    by_contra hc
    push Not at hc
    have : ‖x‖ ≤ r := (pi_norm_le_iff_of_nonneg hr).mpr fun i => by
      rw [Real.norm_eq_abs]; exact hc i
    linarith
  have h1 : r ^ 2 < x i ^ 2 := by
    rw [← sq_abs (x i)]; exact pow_lt_pow_left₀ hi hr (by norm_num)
  have h2 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

theorem tbt4_continuous_qDeltaLambda (δ Λ : ℝ) : Continuous (qDeltaLambda δ Λ) :=
  (tbt_ihp_qDeltaLambda δ Λ).continuous

theorem tbt4_isCompact_sum_sq_le (ρ : ℝ) :
    IsCompact {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ ρ} := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin 3 → ℝ) (√|ρ|))
    (isClosed_le (by fun_prop) continuous_const) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  push Not at h
  have := tbt4_lt_sum_sq (Real.sqrt_nonneg _) h
  rw [Real.sq_sqrt (abs_nonneg _)] at this
  have hx' : ∑ i, x i ^ 2 ≤ ρ := hx
  linarith [le_abs_self ρ]

theorem tbt4_sumSq_gt {R : ℝ} (hR : 0 < R) {x : Fin 3 → ℝ}
    (hx : x ∉ Metric.closedBall (0 : Fin 3 → ℝ) (2 * R)) : 2 * R ^ 2 < ∑ i, x i ^ 2 := by
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  have := tbt4_lt_sum_sq (by positivity) hx
  nlinarith

/-- A function vanishing on `|x|² > 2R²` has compact support. -/
theorem tbt4_hasCompactSupport {β : Type*} [Zero β] {f : (Fin 3 → ℝ) → β} {R : ℝ} (hR : 0 < R)
    (h : ∀ x, 2 * R ^ 2 < ∑ i, x i ^ 2 → f x = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall 0 (2 * R)) fun x hx => h x (tbt4_sumSq_gt hR hx)

/-- **`∫ |E_R|⁴ ≲ R⁻¹`** (TeX 2004, "boundedness of `u` gives `∫ |E_R|⁴ ≲ R⁻¹`"): for `E`
supported in `|x|² ≤ 2R²` with `|E|² ≤ C₂ / R²`, `∫ |E|⁴ ≤ 64 C₂² / R`. -/
theorem tbt4_integral_E4_le {Ef : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ} {R C₂ : ℝ} (hR : 0 < R)
    (hEc : Continuous Ef) (hsupp : ∀ x, 2 * R ^ 2 < ∑ i, x i ^ 2 → Ef x = 0)
    (hE : ∀ x, frobSq (Ef x) ≤ C₂ / R ^ 2) :
    ∫ x, frobSq (Ef x) ^ 2 ≤ 64 * C₂ ^ 2 / R := by
  have hcE : Continuous fun x => frobSq (Ef x) ^ 2 := (tbt_continuous_frobSq.comp hEc).pow 2
  have hEbd : ∀ x, frobSq (Ef x) ^ 2 ≤
      (Metric.closedBall (0 : Fin 3 → ℝ) (2 * R)).indicator (fun _ => (C₂ / R ^ 2) ^ 2) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Fin 3 → ℝ) (2 * R)
    · rw [Set.indicator_of_mem hx]
      exact pow_le_pow_left₀ (tbt_frobSq_nonneg _) (hE x) 2
    · rw [Set.indicator_of_notMem hx, hsupp x (tbt4_sumSq_gt hR hx)]
      simp [frobSq]
  have hiB : Integrable ((Metric.closedBall (0 : Fin 3 → ℝ) (2 * R)).indicator
      fun _ => (C₂ / R ^ 2) ^ 2) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (measure_closedBall_lt_top).ne)
  have hi : Integrable fun x => frobSq (Ef x) ^ 2 :=
    hcE.integrable_of_hasCompactSupport (tbt4_hasCompactSupport hR fun x hx => by
      simp [hsupp x hx, frobSq])
  refine (integral_mono hi hiB hEbd).trans (le_of_eq ?_)
  rw [integral_indicator_const _ measurableSet_closedBall, Measure.real,
    Real.volume_pi_closedBall _ (by positivity), Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  field_simp
  ring

/-- **The Hölder step** (TeX 2005–2014): for `G ∈ 𝓛₃` with `q₃ (G) ∈ L¹`, a cut-off `χ ∈ [0, 1]`
and an error `E` (both vanishing off `S = {|x|² ≤ 2R²}`, `|E|² ≤ C₂ / R²`) and
`∫_S |G|⁴ ≤ C₁`,
`|∫ q₃ (π (χ G + E)) − ∫ χ⁴ q₃ (G)| ≤ L C₁^{3/4} (64 C₂² / R)^{1/4} + M · 64 C₂² / R`.
The pointwise bound `tbt4_q3_proj_sub_le` leaves `L ∫ |G|³ |E| + M ∫ |E|⁴`; Hölder's inequality
with exponents `4/3` and `4` on `S` (`integral_mul_le_Lp_mul_Lq_of_nonneg`) gives
`∫ |G|³ |E| ≤ (∫_S |G|⁴)^{3/4} (∫ |E|⁴)^{1/4}`, and `∫ |E|⁴ ≤ 64 C₂² / R`
(`tbt4_integral_E4_le`). -/
theorem tbt4_holder {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hpert : ∀ X Y : Matrix (Fin 2) (Fin 3) ℝ,
      |q3 (X + Y) - q3 X| ≤ L * √(frobSq X) ^ 3 * √(frobSq Y) + M * √(frobSq Y) ^ 4)
    {Gf Ef : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ} {χf : (Fin 3 → ℝ) → ℝ}
    {R C₁ C₂ : ℝ} (hR : 0 < R)
    (hGc : Continuous Gf) (hEc : Continuous Ef) (hχc : Continuous χf)
    (hGL : ∀ x, Gf x ∈ L3) (hGi : Integrable fun x => q3 (Gf x))
    (hχ0 : ∀ x, 0 ≤ χf x) (hχ1 : ∀ x, χf x ≤ 1)
    (hsupp : ∀ x, 2 * R ^ 2 < ∑ i, x i ^ 2 → χf x = 0 ∧ Ef x = 0)
    (hlog : ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2}, frobSq (Gf x) ^ 2 ≤ C₁)
    (hE : ∀ x, frobSq (Ef x) ≤ C₂ / R ^ 2) :
    |(∫ x, q3 (projL3 (χf x • Gf x + Ef x))) - ∫ x, χf x ^ 4 * q3 (Gf x)| ≤
      L * (C₁ ^ (3 / 4 : ℝ) * (64 * C₂ ^ 2 / R) ^ (1 / 4 : ℝ)) + M * (64 * C₂ ^ 2 / R) := by
  set S := {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2}
  have hsq : Continuous fun x : Fin 3 → ℝ => ∑ i, x i ^ 2 := by fun_prop
  have hSm : MeasurableSet S := measurableSet_le hsq.measurable measurable_const
  have hSc : IsCompact S := tbt4_isCompact_sum_sq_le _
  set f : (Fin 3 → ℝ) → ℝ := fun x => √(frobSq (Gf x)) ^ 3
  set g : (Fin 3 → ℝ) → ℝ := fun x => √(frobSq (Ef x))
  have hfc : Continuous f := ((tbt_continuous_frobSq.comp hGc).sqrt).pow 3
  have hgc : Continuous g := (tbt_continuous_frobSq.comp hEc).sqrt
  have hec : Continuous fun x => frobSq (Ef x) ^ 2 := (tbt_continuous_frobSq.comp hEc).pow 2
  have hac : Continuous fun x => q3 (projL3 (χf x • Gf x + Ef x)) :=
    tbt_continuous_q3.comp (tbt4_continuous_projL3.comp ((hχc.smul hGc).add hEc))
  -- integrability
  have ha : Integrable fun x => q3 (projL3 (χf x • Gf x + Ef x)) :=
    hac.integrable_of_hasCompactSupport (tbt4_hasCompactSupport hR fun x hx => by
      obtain ⟨h1, h2⟩ := hsupp x hx
      simp [h1, h2, tbt4_projL3_zero, tbt4_q3_zero])
  have hb : Integrable fun x => χf x ^ 4 * q3 (Gf x) := by
    refine hGi.norm.mono' ((hχc.pow 4).mul (tbt_continuous_q3.comp hGc)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (hχ0 x) 4)]
    have : χf x ^ 4 ≤ 1 := pow_le_one₀ (hχ0 x) (hχ1 x)
    nlinarith [abs_nonneg (q3 (Gf x))]
  have hfg : Integrable fun x => f x * g x :=
    (hfc.mul hgc).integrable_of_hasCompactSupport (tbt4_hasCompactSupport hR fun x hx => by
      simp [g, (hsupp x hx).2, frobSq])
  have he : Integrable fun x => frobSq (Ef x) ^ 2 :=
    hec.integrable_of_hasCompactSupport (tbt4_hasCompactSupport hR fun x hx => by
      simp [(hsupp x hx).2, frobSq])
  have hE4 := tbt4_integral_E4_le hR hEc (fun x hx => (hsupp x hx).2) hE
  -- the pointwise bound, integrated
  have h1 : |(∫ x, q3 (projL3 (χf x • Gf x + Ef x))) - ∫ x, χf x ^ 4 * q3 (Gf x)| ≤
      L * (∫ x, f x * g x) + M * ∫ x, frobSq (Ef x) ^ 2 := by
    rw [← integral_sub ha hb, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hfg.const_mul L) (he.const_mul M)]
    refine abs_integral_le_integral_abs.trans
      (integral_mono (ha.sub hb).abs ((hfg.const_mul L).add (he.const_mul M)) fun x => ?_)
    exact tbt4_q3_proj_sub_le hL hM hpert (hGL x) (hχ0 x) (hχ1 x)
  -- Hölder's inequality on `S` with exponents `4/3` and `4`
  have hS0 : ∀ x ∉ S, f x * g x = 0 := fun x hx => by
    simp [g, (hsupp x (not_le.mp hx)).2, frobSq]
  have h2 : ∫ x, f x * g x ≤ C₁ ^ (3 / 4 : ℝ) * (64 * C₂ ^ 2 / R) ^ (1 / 4 : ℝ) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hS0]
    have : IsFiniteMeasure (volume.restrict S) :=
      isFiniteMeasure_restrict.mpr hSc.measure_lt_top.ne
    have hpq : Real.HolderConjugate (4 / 3) 4 := ⟨by norm_num, by norm_num, by norm_num⟩
    obtain ⟨Cf, hCf⟩ := hSc.exists_bound_of_continuousOn hfc.continuousOn
    obtain ⟨Cg, hCg⟩ := hSc.exists_bound_of_continuousOn hgc.continuousOn
    have hfm : MemLp f (ENNReal.ofReal (4 / 3)) (volume.restrict S) :=
      MemLp.of_bound hfc.aestronglyMeasurable Cf ((ae_restrict_iff' hSm).mpr
        (Filter.Eventually.of_forall hCf))
    have hgm : MemLp g (ENNReal.ofReal 4) (volume.restrict S) :=
      MemLp.of_bound hgc.aestronglyMeasurable Cg ((ae_restrict_iff' hSm).mpr
        (Filter.Eventually.of_forall hCg))
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      (Filter.Eventually.of_forall fun x => by positivity)
      (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _) hfm hgm
    have ef : ∀ x, f x ^ (4 / 3 : ℝ) = frobSq (Gf x) ^ 2 := fun x => by
      show (√(frobSq (Gf x)) ^ 3) ^ (4 / 3 : ℝ) = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.sqrt_nonneg _),
        show ((3 : ℕ) : ℝ) * (4 / 3) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        show √(frobSq (Gf x)) ^ 4 = (√(frobSq (Gf x)) ^ 2) ^ 2 by ring,
        Real.sq_sqrt (tbt_frobSq_nonneg _)]
    have eg : ∀ x, √(frobSq (Ef x)) ^ (4 : ℝ) = frobSq (Ef x) ^ 2 := fun x => by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        show √(frobSq (Ef x)) ^ 4 = (√(frobSq (Ef x)) ^ 2) ^ 2 by ring,
        Real.sq_sqrt (tbt_frobSq_nonneg _)]
    simp_rw [ef, eg] at hH
    rw [show (1 : ℝ) / (4 / 3) = 3 / 4 by norm_num] at hH
    have hC₁ : 0 ≤ C₁ := (setIntegral_nonneg hSm fun x _ => by positivity).trans hlog
    refine hH.trans (mul_le_mul ?_ ?_ (by positivity) (Real.rpow_nonneg hC₁ _))
    · exact Real.rpow_le_rpow (setIntegral_nonneg hSm fun x _ => by positivity) hlog
        (by norm_num)
    · refine Real.rpow_le_rpow (setIntegral_nonneg hSm fun x _ => by positivity) ?_
        (by norm_num)
      exact (setIntegral_le_integral he (Filter.Eventually.of_forall fun x => by positivity)).trans
        hE4
  refine h1.trans ?_
  have := mul_le_mul_of_nonneg_left h2 hL
  have := mul_le_mul_of_nonneg_left hE4 hM
  linarith

/-- The penalty in the step "consequently" (TeX 2022–2027):
`δ (|π A|² + Λ² |π^⊥ A|²)² ≤ 2 δ |π A|⁴ + 2 δ Λ⁴ |π^⊥ A|⁴`, so
`∫ q_{δ,Λ} (A) ≤ ∫ q₃ (π A) + 2 δ ∫ |π A|⁴ + 2 δ Λ⁴ ∫ |π^⊥ A|⁴` for continuous compactly
supported `A`. -/
theorem tbt4_energy {Af : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ} (hAc : Continuous Af)
    (hAs : HasCompactSupport Af) {δ Λ : ℝ} (hδ : 0 ≤ δ) :
    ∫ x, qDeltaLambda δ Λ (Af x) ≤ (∫ x, q3 (projL3 (Af x))) +
      2 * δ * (∫ x, frobSq (projL3 (Af x)) ^ 2) +
        2 * δ * Λ ^ 4 * ∫ x, frobSq (Af x - projL3 (Af x)) ^ 2 := by
  have hπc : Continuous fun x => projL3 (Af x) := tbt4_continuous_projL3.comp hAc
  have hi0 : Integrable fun x => qDeltaLambda δ Λ (Af x) :=
    ((tbt4_continuous_qDeltaLambda δ Λ).comp hAc).integrable_of_hasCompactSupport
      (hAs.comp_left (tbt4_qDeltaLambda_zero δ Λ))
  have hi1 : Integrable fun x => q3 (projL3 (Af x)) :=
    (tbt_continuous_q3.comp hπc).integrable_of_hasCompactSupport
      (hAs.comp_left (g := fun A => q3 (projL3 A)) (by simp [tbt4_projL3_zero, tbt4_q3_zero]))
  have hi2 : Integrable fun x => frobSq (projL3 (Af x)) ^ 2 := by
    have hc : Continuous fun x => frobSq (projL3 (Af x)) ^ 2 :=
      (tbt_continuous_frobSq.comp hπc).pow 2
    have hs : HasCompactSupport fun x => frobSq (projL3 (Af x)) ^ 2 :=
      hAs.comp_left (g := fun A => frobSq (projL3 A) ^ 2) (by simp [tbt4_projL3_zero, frobSq])
    exact hc.integrable_of_hasCompactSupport hs
  have hi3 : Integrable fun x => frobSq (Af x - projL3 (Af x)) ^ 2 := by
    have hc : Continuous fun x => frobSq (Af x - projL3 (Af x)) ^ 2 :=
      (tbt_continuous_frobSq.comp (hAc.sub hπc)).pow 2
    have hs : HasCompactSupport fun x => frobSq (Af x - projL3 (Af x)) ^ 2 :=
      hAs.comp_left (g := fun A => frobSq (A - projL3 A) ^ 2)
        (by simp [tbt4_projL3_zero, frobSq])
    exact hc.integrable_of_hasCompactSupport hs
  have hi12 : Integrable fun x => q3 (projL3 (Af x)) + 2 * δ * frobSq (projL3 (Af x)) ^ 2 :=
    hi1.add (hi2.const_mul _)
  have hi123 : Integrable fun x => q3 (projL3 (Af x)) + 2 * δ * frobSq (projL3 (Af x)) ^ 2 +
      2 * δ * Λ ^ 4 * frobSq (Af x - projL3 (Af x)) ^ 2 :=
    hi12.add (hi3.const_mul _)
  have hmono := integral_mono hi0 hi123 fun x => by
    simp only [qDeltaLambda]
    nlinarith [mul_nonneg hδ (sq_nonneg (frobSq (projL3 (Af x)) -
      Λ ^ 2 * frobSq (Af x - projL3 (Af x))))]
  rw [integral_add hi12 (hi3.const_mul _), integral_add hi1 (hi2.const_mul _),
    integral_const_mul, integral_const_mul] at hmono
  exact hmono

/-- **`∫ |π ∇u_R|⁴ ≲ 1 + log R`** (TeX 2015–2021): for `G ∈ 𝓛₃`, `χ ∈ [0, 1]`, `E` as in
`tbt4_holder`, `R ≥ 1` and `∫_S |G|⁴ ≤ C log (2 + 2R)`,
`∫ |π (χ G + E)|⁴ ≤ (24 C + 512 C₂²) (1 + log R)`: `π (χ G + E) = χ G + π E`,
`|χ G + π E|⁴ ≤ 8 |G|⁴ + 8 |E|⁴` on `S`, and `∫ |E|⁴ ≤ 64 C₂² / R` (`tbt4_integral_E4_le`). -/
theorem tbt4_proj4_le {Gf Ef : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ} {χf : (Fin 3 → ℝ) → ℝ}
    {R C C₂ : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hGc : Continuous Gf) (hEc : Continuous Ef) (hχc : Continuous χf)
    (hGL : ∀ x, Gf x ∈ L3) (hχ0 : ∀ x, 0 ≤ χf x) (hχ1 : ∀ x, χf x ≤ 1)
    (hsupp : ∀ x, 2 * R ^ 2 < ∑ i, x i ^ 2 → χf x = 0 ∧ Ef x = 0)
    (hlog : ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2}, frobSq (Gf x) ^ 2 ≤
      C * Real.log (2 + 2 * R))
    (hE : ∀ x, frobSq (Ef x) ≤ C₂ / R ^ 2) :
    ∫ x, frobSq (projL3 (χf x • Gf x + Ef x)) ^ 2 ≤
      (24 * C + 512 * C₂ ^ 2) * (1 + Real.log R) := by
  have hR0 : 0 < R := by linarith
  set S := {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2}
  have hsq : Continuous fun x : Fin 3 → ℝ => ∑ i, x i ^ 2 := by fun_prop
  have hSm : MeasurableSet S := measurableSet_le hsq.measurable measurable_const
  have hSc : IsCompact S := tbt4_isCompact_sum_sq_le _
  have hcG : Continuous fun x => frobSq (Gf x) ^ 2 := (tbt_continuous_frobSq.comp hGc).pow 2
  have hiG : Integrable (S.indicator fun x => frobSq (Gf x) ^ 2) :=
    (integrable_indicator_iff hSm).mpr (hcG.continuousOn.integrableOn_compact hSc)
  have he : Integrable fun x => frobSq (Ef x) ^ 2 :=
    ((tbt_continuous_frobSq.comp hEc).pow 2).integrable_of_hasCompactSupport
      (tbt4_hasCompactSupport hR0 fun x hx => by simp [(hsupp x hx).2, frobSq])
  have hπ : Continuous fun x => frobSq (projL3 (χf x • Gf x + Ef x)) ^ 2 :=
    (tbt_continuous_frobSq.comp (tbt4_continuous_projL3.comp ((hχc.smul hGc).add hEc))).pow 2
  have hi : Integrable fun x => frobSq (projL3 (χf x • Gf x + Ef x)) ^ 2 :=
    hπ.integrable_of_hasCompactSupport (tbt4_hasCompactSupport hR0 fun x hx => by
      obtain ⟨h1, h2⟩ := hsupp x hx
      simp [h1, h2, tbt4_projL3_zero, frobSq])
  have hpt : ∀ x, frobSq (projL3 (χf x • Gf x + Ef x)) ^ 2 ≤
      8 * S.indicator (fun x => frobSq (Gf x) ^ 2) x + 8 * frobSq (Ef x) ^ 2 := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, tbt4_proj_add (hGL x)]
      have hpy := tbt4_frobSq_pythagoras (Ef x)
      have hN0 := tbt_frobSq_nonneg (Ef x - projL3 (Ef x))
      have hP0 := tbt_frobSq_nonneg (projL3 (Ef x))
      have hG0 := tbt_frobSq_nonneg (Gf x)
      have hχG : frobSq (χf x • Gf x) ≤ frobSq (Gf x) := by
        rw [tbt_frobSq_smul]
        have : χf x ^ 2 ≤ 1 := by nlinarith [hχ0 x, hχ1 x]
        nlinarith
      have hS := tbt4_frobSq_add_le (χf x • Gf x) (projL3 (Ef x))
      have hS' : frobSq (χf x • Gf x + projL3 (Ef x)) ≤
          2 * frobSq (Gf x) + 2 * frobSq (Ef x) := by
        linarith
      have h2 := pow_le_pow_left₀ (tbt_frobSq_nonneg _) hS' 2
      nlinarith [sq_nonneg (frobSq (Gf x) - frobSq (Ef x))]
    · obtain ⟨h1, h2⟩ := hsupp x (not_le.mp hx)
      rw [Set.indicator_of_notMem hx]
      simp [h1, h2, tbt4_projL3_zero, frobSq]
  have hE4 := tbt4_integral_E4_le hR0 hEc (fun x hx => (hsupp x hx).2) hE
  have hint : Integrable fun x => 8 * S.indicator (fun x => frobSq (Gf x) ^ 2) x +
      8 * frobSq (Ef x) ^ 2 := (hiG.const_mul 8).add (he.const_mul 8)
  have h1 := integral_mono hi hint hpt
  rw [integral_add (hiG.const_mul 8) (he.const_mul 8), integral_const_mul, integral_const_mul,
    integral_indicator hSm] at h1
  -- `log (2 + 2R) ≤ 3 (1 + log R)` and `1/R ≤ 1 ≤ 1 + log R` for `R ≥ 1`
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hl : Real.log (2 + 2 * R) ≤ 3 * (1 + Real.log R) := by
    have h4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
    have : Real.log (2 + 2 * R) ≤ Real.log (4 * R) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) hR0.ne'] at this
    linarith
  have hRi : 64 * C₂ ^ 2 / R ≤ 64 * C₂ ^ 2 * (1 + Real.log R) := by
    rw [div_le_iff₀ hR0]
    nlinarith [sq_nonneg C₂, mul_nonneg (sq_nonneg C₂) hlR]
  have := mul_le_mul_of_nonneg_left hl hC
  linarith

/-- **`∫ |π^⊥ ∇u_R|⁴ ≲ R⁻¹`** (TeX 2015–2021): `π^⊥ (χ G + E) = π^⊥ E` for `G ∈ 𝓛₃`, so
`∫ |π^⊥ (χ G + E)|⁴ ≤ ∫ |E|⁴ ≤ 64 C₂² / R` (`tbt4_integral_E4_le`). -/
theorem tbt4_perp4_le {Gf Ef : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ} {χf : (Fin 3 → ℝ) → ℝ}
    {R C₂ : ℝ} (hR : 0 < R) (hEc : Continuous Ef) (hGL : ∀ x, Gf x ∈ L3)
    (hsupp : ∀ x, 2 * R ^ 2 < ∑ i, x i ^ 2 → Ef x = 0)
    (hE : ∀ x, frobSq (Ef x) ≤ C₂ / R ^ 2) :
    ∫ x, frobSq (χf x • Gf x + Ef x - projL3 (χf x • Gf x + Ef x)) ^ 2 ≤ 64 * C₂ ^ 2 / R := by
  have e : ∀ x, χf x • Gf x + Ef x - projL3 (χf x • Gf x + Ef x) = Ef x - projL3 (Ef x) :=
    fun x => tbt4_perp_add (hGL x) _ _
  simp_rw [e]
  have he : Integrable fun x => frobSq (Ef x) ^ 2 :=
    ((tbt_continuous_frobSq.comp hEc).pow 2).integrable_of_hasCompactSupport
      (tbt4_hasCompactSupport hR fun x hx => by simp [hsupp x hx, frobSq])
  have hc : Continuous fun x => frobSq (Ef x - projL3 (Ef x)) ^ 2 :=
    (tbt_continuous_frobSq.comp (hEc.sub (tbt4_continuous_projL3.comp hEc))).pow 2
  have hi : Integrable fun x => frobSq (Ef x - projL3 (Ef x)) ^ 2 :=
    hc.integrable_of_hasCompactSupport (tbt4_hasCompactSupport hR fun x hx => by
      simp [hsupp x hx, tbt4_projL3_zero, frobSq])
  refine (integral_mono hi he fun x => ?_).trans (tbt4_integral_E4_le hR hEc hsupp hE)
  have hpy := tbt4_frobSq_pythagoras (Ef x)
  have hP0 := tbt_frobSq_nonneg (projL3 (Ef x))
  have hN0 := tbt_frobSq_nonneg (Ef x - projL3 (Ef x))
  exact pow_le_pow_left₀ hN0 (by linarith) 2

/-! ### The cutoff of the witness -/

theorem tbt4_differentiable {ψ : (Fin 3 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ) :
    Differentiable ℝ ψ := h.differentiable (by simp)

/-- `χ (y) = σ (2 − |y|²)`: `1` on `|y|² ≤ 1`, `0` on `|y|² ≥ 2`. -/
noncomputable def tbt4Chi (y : Fin 3 → ℝ) : ℝ := Real.smoothTransition (2 - ∑ i, y i ^ 2)

/-- `u_R = χ (·/R) u`. -/
noncomputable def tbt4uR (u : (Fin 3 → ℝ) → Fin 2 → ℝ) (R : ℝ) (x : Fin 3 → ℝ) : Fin 2 → ℝ :=
  tbt4Chi (R⁻¹ • x) • u x

/-- The cutoff error `E_R = u ⊗ ∇[χ (·/R)]`. -/
noncomputable def tbt4ER (u : (Fin 3 → ℝ) → Fin 2 → ℝ) (R : ℝ) (x : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of fun i k => u x i * (R⁻¹ * fderiv ℝ tbt4Chi (R⁻¹ • x) (Pi.single k 1))

theorem tbt4_contDiff_sumSq {n : WithTop ℕ∞} : ContDiff ℝ n fun y : Fin 3 → ℝ => ∑ i, y i ^ 2 :=
  ContDiff.sum fun i _ => (contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) i).pow 2

theorem tbt4_contDiff_chi : ContDiff ℝ tbt3Top tbt4Chi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub tbt4_contDiff_sumSq)

theorem tbt4_sumSq_smul (a : ℝ) (x : Fin 3 → ℝ) :
    ∑ i, (a • x) i ^ 2 = a ^ 2 * ∑ i, x i ^ 2 := by
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem tbt4_chi_zero {y : Fin 3 → ℝ} (h : 2 ≤ ∑ i, y i ^ 2) : tbt4Chi y = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem tbt4_chi_one {y : Fin 3 → ℝ} (h : ∑ i, y i ^ 2 ≤ 1) : tbt4Chi y = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- `∇χ` vanishes on `|y|² > 2`. -/
theorem tbt4_fderiv_chi_zero {y : Fin 3 → ℝ} (h : 2 < ∑ i, y i ^ 2) : fderiv ℝ tbt4Chi y = 0 := by
  have hU : IsOpen {z : Fin 3 → ℝ | 2 < ∑ i, z i ^ 2} :=
    isOpen_lt continuous_const (tbt4_contDiff_sumSq (n := 0)).continuous
  have : tbt4Chi =ᶠ[nhds y] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds h) fun z hz => tbt4_chi_zero (le_of_lt hz)
  rw [this.fderiv_eq]; exact fderiv_const_apply 0

/-- `∇χ` is bounded. -/
theorem tbt4_fderiv_chi_bound : ∃ G : ℝ, 0 ≤ G ∧ ∀ y, ‖fderiv ℝ tbt4Chi y‖ ≤ G := by
  have hc : HasCompactSupport tbt4Chi :=
    HasCompactSupport.intro (tbt4_isCompact_sum_sq_le 2) fun y hy =>
      tbt4_chi_zero (le_of_lt (not_le.mp hy))
  have hcf : Continuous (fderiv ℝ tbt4Chi) := tbt4_contDiff_chi.continuous_fderiv (by simp)
  obtain ⟨G, hG⟩ := hcf.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  exact ⟨max G 0, le_max_right _ _, fun y => (hG y).trans (le_max_left _ _)⟩

/-- `∇u_R = χ (·/R) ∇u + E_R`. -/
theorem tbt4_jac_uR {u : (Fin 3 → ℝ) → Fin 2 → ℝ} (hu : ContDiff ℝ tbt3Top u) (R : ℝ)
    (x : Fin 3 → ℝ) : jac (tbt4uR u R) x = tbt4Chi (R⁻¹ • x) • jac u x + tbt4ER u R x := by
  ext i k
  have hχ : HasFDerivAt (fun y => tbt4Chi (R⁻¹ • y))
      ((fderiv ℝ tbt4Chi (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ _)) x :=
    ((tbt4_differentiable tbt4_contDiff_chi) (R⁻¹ • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul R⁻¹)
  have hui : HasFDerivAt (fun y => u y i) (fderiv ℝ (fun y => u y i) x) x :=
    (((contDiff_pi.1 hu) i).differentiable (by simp) x).hasFDerivAt
  have h := hχ.mul hui
  simp only [jac, Matrix.of_apply, tbt4uR, tbt4ER, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [show (fun y => (tbt4Chi (R⁻¹ • y) • u y) i) =
    ((fun y => tbt4Chi (R⁻¹ • y)) * fun y => u y i) from rfl, h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_id', id_eq, map_smul]

theorem tbt4_continuous_ER {u : (Fin 3 → ℝ) → Fin 2 → ℝ} (hu : Continuous u) (R : ℝ) :
    Continuous (tbt4ER u R) := by
  have hf : Continuous (fderiv ℝ tbt4Chi) := tbt4_contDiff_chi.continuous_fderiv (by simp)
  refine continuous_pi fun i => continuous_pi fun k => ?_
  exact ((continuous_apply i).comp hu).mul (continuous_const.mul
    ((hf.comp (continuous_const_smul R⁻¹)).clm_apply continuous_const))

/-- `|E_R|² ≤ 6 M² G² / R²`, `M` a bound of `|u|` and `G` a bound of `‖∇χ‖`. -/
theorem tbt4_frobSq_ER_le {u : (Fin 3 → ℝ) → Fin 2 → ℝ} {M G R : ℝ} (hM : ∀ x, ‖u x‖ ≤ M)
    (hG : 0 ≤ G) (hGb : ∀ y, ‖fderiv ℝ tbt4Chi y‖ ≤ G)
    (hR : 0 < R) (x : Fin 3 → ℝ) : frobSq (tbt4ER u R x) ≤ 6 * M ^ 2 * G ^ 2 / R ^ 2 := by
  have hu : ∀ i, |u x i| ≤ M := fun i => (norm_le_pi_norm (u x) i).trans (hM x)
  have hd : ∀ k : Fin 3, |fderiv ℝ tbt4Chi (R⁻¹ • x) (Pi.single k 1)| ≤ G := by
    intro k
    have h1 := (fderiv ℝ tbt4Chi (R⁻¹ • x)).le_opNorm (Pi.single k 1)
    have h2 : ‖(Pi.single k (1 : ℝ) : Fin 3 → ℝ)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by
        by_cases hj : j = k
        · subst hj; simp
        · simp [hj]
    rw [← Real.norm_eq_abs]
    calc _ ≤ ‖fderiv ℝ tbt4Chi (R⁻¹ • x)‖ * ‖(Pi.single k (1 : ℝ) : Fin 3 → ℝ)‖ := h1
      _ ≤ G * 1 := mul_le_mul (hGb _) h2 (norm_nonneg _) hG
      _ = G := mul_one G
  have he : ∀ i k, (tbt4ER u R x i k) ^ 2 ≤ M ^ 2 * G ^ 2 / R ^ 2 := by
    intro i k
    simp only [tbt4ER, Matrix.of_apply]
    rw [mul_pow, mul_pow, inv_pow, ← sq_abs (u x i),
      ← sq_abs (fderiv ℝ tbt4Chi (R⁻¹ • x) (Pi.single k 1))]
    have h1 : |u x i| ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hu i) 2
    have h2 : |fderiv ℝ tbt4Chi (R⁻¹ • x) (Pi.single k 1)| ^ 2 ≤ G ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hd k) 2
    rw [div_eq_mul_inv]
    have : 0 ≤ (R ^ 2)⁻¹ := by positivity
    calc |u x i| ^ 2 * ((R ^ 2)⁻¹ * |fderiv ℝ tbt4Chi (R⁻¹ • x) (Pi.single k 1)| ^ 2)
        ≤ M ^ 2 * ((R ^ 2)⁻¹ * G ^ 2) := by gcongr
      _ = M ^ 2 * G ^ 2 * (R ^ 2)⁻¹ := by ring
  simp only [frobSq, Fin.sum_univ_two, Fin.sum_univ_three]
  have := he 0 0; have := he 0 1; have := he 0 2; have := he 1 0; have := he 1 1; have := he 1 2
  have e : 6 * M ^ 2 * G ^ 2 / R ^ 2 = 6 * (M ^ 2 * G ^ 2 / R ^ 2) := by ring
  rw [e]; linarith

theorem tbt4_chiR_zero {R : ℝ} (hR : 0 < R) {x : Fin 3 → ℝ} (hx : 2 * R ^ 2 < ∑ i, x i ^ 2) :
    tbt4Chi (R⁻¹ • x) = 0 := by
  have h : 2 < ∑ i, (R⁻¹ • x) i ^ 2 := by
    rw [tbt4_sumSq_smul, inv_pow, lt_inv_mul_iff₀ (by positivity)]; linarith
  exact tbt4_chi_zero h.le

theorem tbt4_supp (u : (Fin 3 → ℝ) → Fin 2 → ℝ) {R : ℝ} (hR : 0 < R) {x : Fin 3 → ℝ}
    (hx : 2 * R ^ 2 < ∑ i, x i ^ 2) : tbt4Chi (R⁻¹ • x) = 0 ∧ tbt4ER u R x = 0 := by
  have h : 2 < ∑ i, (R⁻¹ • x) i ^ 2 := by
    rw [tbt4_sumSq_smul, inv_pow, lt_inv_mul_iff₀ (by positivity)]; linarith
  refine ⟨tbt4_chi_zero h.le, ?_⟩
  ext i k
  simp [tbt4ER, tbt4_fderiv_chi_zero h]

/-- `∫_{|x|² ≤ 2R²} |∇u|⁴ ≤ C log (2 + 2R)`, from the logarithmic bound
`∫_{B_R} |∇u|⁴ ≤ C log (2 + R)` on the open balls. -/
theorem tbt4_log_bound {u : (Fin 3 → ℝ) → Fin 2 → ℝ} (hu : ContDiff ℝ tbt3Top u) {C : ℝ}
    (hC : ∀ R : ℝ, 0 ≤ R →
      ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}, frobSq (jac u x) ^ 2 ≤ C * Real.log (2 + R))
    {R : ℝ} (hR : 0 < R) :
    ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2}, frobSq (jac u x) ^ 2 ≤
      C * Real.log (2 + 2 * R) := by
  have hc : Continuous fun x => frobSq (jac u x) ^ 2 :=
    (tbt_continuous_frobSq.comp (tbt_continuous_jac hu)).pow 2
  have hi : IntegrableOn (fun x => frobSq (jac u x) ^ 2)
      {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < (2 * R) ^ 2} :=
    (hc.continuousOn.integrableOn_compact (tbt4_isCompact_sum_sq_le ((2 * R) ^ 2))).mono_set
      fun x hx => le_of_lt (show ∑ i, x i ^ 2 < (2 * R) ^ 2 from hx)
  refine (setIntegral_mono_set hi (Filter.Eventually.of_forall fun x => by positivity)
    (Filter.Eventually.of_forall fun x hx => ?_)).trans (hC (2 * R) (by positivity))
  have h : ∑ i, x i ^ 2 ≤ 2 * R ^ 2 := hx
  show ∑ i, x i ^ 2 < (2 * R) ^ 2
  nlinarith

theorem tbt4_chi_nonneg (y : Fin 3 → ℝ) : 0 ≤ tbt4Chi y := Real.smoothTransition.nonneg _

theorem tbt4_chi_le_one (y : Fin 3 → ℝ) : tbt4Chi y ≤ 1 := Real.smoothTransition.le_one _

theorem tbt4_continuous_chiR (R : ℝ) : Continuous fun x : Fin 3 → ℝ => tbt4Chi (R⁻¹ • x) :=
  tbt4_contDiff_chi.continuous.comp (continuous_const_smul R⁻¹)

/-- `χ (x/R) = 1` for `|x|² ≤ R²`. -/
theorem tbt4_chiR_one {R : ℝ} (hR : 0 < R) {x : Fin 3 → ℝ} (hx : ∑ i, x i ^ 2 ≤ R ^ 2) :
    tbt4Chi (R⁻¹ • x) = 1 := by
  refine tbt4_chi_one ?_
  rw [tbt4_sumSq_smul, inv_pow, inv_mul_le_iff₀ (by positivity)]
  linarith

/-- `I = ∫ f < 0` for `f < 0` integrable (TeX 1995, `I := ∫_{ℝ³} q₃ (∇u) < 0`). -/
theorem tbt4_integral_neg {f : (Fin 3 → ℝ) → ℝ} (hneg : ∀ x, f x < 0) (hint : Integrable f) :
    ∫ x, f x < 0 := by
  have hpos : 0 < ∫ x, -f x := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => (neg_pos.mpr (hneg x)).le) hint.neg]
    have hs : Function.support (fun x => -f x) = Set.univ :=
      Set.eq_univ_of_forall fun x => (neg_pos.mpr (hneg x)).ne'
    rw [hs]
    exact isOpen_univ.measure_pos volume Set.univ_nonempty
  rw [integral_neg] at hpos
  linarith

/-- **`∫ χ (·/R)⁴ q₃ (∇u) → I`** (TeX 2010–2013): for integrable `f`,
`∫ χ (x/R)⁴ f (x) dx → ∫ f` as `R → ∞`, by dominated convergence (`|χ (x/R)⁴ f| ≤ |f|`, and
`χ (x/R) = 1` once `|x|² ≤ R²`). -/
theorem tbt4_tendsto_integral_chi {f : (Fin 3 → ℝ) → ℝ} (hf : Integrable f) :
    Filter.Tendsto (fun R : ℝ => ∫ x, tbt4Chi (R⁻¹ • x) ^ 4 * f x) Filter.atTop
      (nhds (∫ x, f x)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => |f x|)
    (Filter.Eventually.of_forall fun R =>
      ((tbt4_continuous_chiR R).pow 4).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => ?_) hf.abs
    (Filter.Eventually.of_forall fun x => ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (tbt4_chi_nonneg _) 4)]
    have : tbt4Chi (R⁻¹ • x) ^ 4 ≤ 1 := pow_le_one₀ (tbt4_chi_nonneg _) (tbt4_chi_le_one _)
    nlinarith [abs_nonneg (f x)]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (∑ i, x i ^ 2 + 1)] with R hR
    have h0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [tbt4_chiR_one (by linarith) (by nlinarith), one_pow, one_mul]

/-- `log (2 + 2R)ⁿ / R → 0` as `R → ∞`. -/
theorem tbt4_tendsto_log_pow_div (n : ℕ) :
    Filter.Tendsto (fun R : ℝ => Real.log (2 + 2 * R) ^ n / R) Filter.atTop (nhds 0) := by
  have h2 : Filter.Tendsto (fun R : ℝ => 2 + 2 * R) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ 2 (Filter.tendsto_id.const_mul_atTop two_pos)
  refine ((Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) (-1) n (by norm_num)).comp h2).congr
    fun R => ?_
  simp only [Function.comp]
  congr 1
  ring

/-- **`∫ q₃ (π ∇u_R) = I + o_R (1)`** (TeX 2005–2014), abstract in the bulk field `G` (values in
`𝓛₃`, `q₃ (G) ∈ L¹`) and the cut-off errors `E_R` (vanishing off `|x|² ≤ 2R²`,
`|E_R|² ≤ C₂ / R²`), with `∫_{|x|² ≤ 2R²} |G|⁴ ≤ C log (2 + 2R)`: the Hölder step
`tbt4_holder` gives `∫ q₃ (π ∇u_R) = ∫ χ (·/R)⁴ q₃ (G) + O (R^{−1/4} (log R)^{3/4})`, and
`∫ χ (·/R)⁴ q₃ (G) → I = ∫ q₃ (G)` (`tbt4_tendsto_integral_chi`). -/
theorem tbt4_tendsto_q3_proj {Gf : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ}
    {Ef : ℝ → (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ} {C C₂ : ℝ} (hC : 0 ≤ C)
    (hGc : Continuous Gf) (hEc : ∀ R, Continuous (Ef R)) (hGL : ∀ x, Gf x ∈ L3)
    (hGi : Integrable fun x => q3 (Gf x))
    (hsupp : ∀ R, 1 ≤ R → ∀ x, 2 * R ^ 2 < ∑ i, x i ^ 2 → Ef R x = 0)
    (hlog : ∀ R, 1 ≤ R → ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2},
      frobSq (Gf x) ^ 2 ≤ C * Real.log (2 + 2 * R))
    (hE : ∀ R, 1 ≤ R → ∀ x, frobSq (Ef R x) ≤ C₂ / R ^ 2) :
    Filter.Tendsto (fun R : ℝ => ∫ x, q3 (projL3 (tbt4Chi (R⁻¹ • x) • Gf x + Ef R x)))
      Filter.atTop (nhds (∫ x, q3 (Gf x))) := by
  obtain ⟨L, M, hL, hM, hpert⟩ := tbt4_q3_perturb
  set β : ℝ → ℝ := fun R => L * ((C ^ 3 * (64 * C₂ ^ 2)) * (Real.log (2 + 2 * R) ^ 3 / R))
    ^ (1 / 4 : ℝ) + M * (64 * C₂ ^ 2 * R⁻¹)
  -- the error term `O (R^{−1/4} (log R)^{3/4})` tends to `0`
  have hβ : Filter.Tendsto β Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun R : ℝ => ((C ^ 3 * (64 * C₂ ^ 2)) *
        (Real.log (2 + 2 * R) ^ 3 / R)) ^ (1 / 4 : ℝ)) Filter.atTop (nhds 0) := by
      have := (tbt4_tendsto_log_pow_div 3).const_mul (C ^ 3 * (64 * C₂ ^ 2))
      rw [mul_zero] at this
      exact this.rpow_const_nhds_zero (by norm_num)
    have h2 : Filter.Tendsto (fun R : ℝ => 64 * C₂ ^ 2 * R⁻¹) Filter.atTop (nhds 0) := by
      have := tendsto_inv_atTop_zero.const_mul (64 * C₂ ^ 2)
      rw [mul_zero] at this
      exact this
    have := (h1.const_mul L).add (h2.const_mul M)
    rw [mul_zero, mul_zero, add_zero] at this
    exact this
  -- `|∫ q₃ (π ∇u_R) − ∫ χ_R⁴ q₃ (G)| ≤ β (R)` for `R ≥ 1`
  have hab : ∀ᶠ R in Filter.atTop, ‖(∫ x, q3 (projL3 (tbt4Chi (R⁻¹ • x) • Gf x + Ef R x))) -
      ∫ x, tbt4Chi (R⁻¹ • x) ^ 4 * q3 (Gf x)‖ ≤ β R := by
    filter_upwards [Filter.eventually_ge_atTop 1] with R hR
    have hR0 : 0 < R := by linarith
    have hl0 : 0 ≤ Real.log (2 + 2 * R) := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs]
    refine (tbt4_holder hL hM hpert hR0 hGc (hEc R) (tbt4_continuous_chiR R) hGL hGi
      (fun _ => tbt4_chi_nonneg _) (fun _ => tbt4_chi_le_one _) (fun x hx =>
        ⟨tbt4_chiR_zero hR0 hx, hsupp R hR x hx⟩) (hlog R hR) (hE R hR)).trans (le_of_eq ?_)
    simp only [β]
    have hx : 0 ≤ C * Real.log (2 + 2 * R) := mul_nonneg hC hl0
    have hy : 0 ≤ 64 * C₂ ^ 2 / R := by positivity
    rw [show C ^ 3 * (64 * C₂ ^ 2) * (Real.log (2 + 2 * R) ^ 3 / R) =
        (C * Real.log (2 + 2 * R)) ^ 3 * (64 * C₂ ^ 2 / R) by ring,
      Real.mul_rpow (pow_nonneg hx 3) hy, ← Real.rpow_natCast (C * Real.log (2 + 2 * R)) 3,
      ← Real.rpow_mul hx,
      div_eq_mul_inv (64 * C₂ ^ 2) R]
    norm_num
  have hd : Filter.Tendsto (fun R : ℝ => (∫ x, q3 (projL3 (tbt4Chi (R⁻¹ • x) • Gf x + Ef R x))) -
      ∫ x, tbt4Chi (R⁻¹ • x) ^ 4 * q3 (Gf x)) Filter.atTop (nhds 0) :=
    squeeze_zero_norm' hab hβ
  simpa using (tbt4_tendsto_integral_chi hGi).add hd

/-- **The energy bound** (TeX 2022–2027, "consequently"): with `G`, `E_R` as in
`tbt4_tendsto_q3_proj`, there is `C₀` such that for `R ≥ 1`, `δ ≥ 0` and all `Λ`,
`∫ q_{δ,Λ} (∇u_R) ≤ ∫ q₃ (π ∇u_R) + C₀ δ (1 + log R + Λ⁴ / R)`; together with
`∫ q₃ (π ∇u_R) = I + o_R (1)` this is the paper's `∫ q_{δ,Λ} (∇u_R) ≤ I + o_R (1) +
C₀ δ (1 + log R + Λ⁴/R)`. It combines the penalty bound `tbt4_energy` with
`∫ |π ∇u_R|⁴ ≲ 1 + log R` (`tbt4_proj4_le`) and `∫ |π^⊥ ∇u_R|⁴ ≲ R⁻¹` (`tbt4_perp4_le`). -/
theorem tbt4_energy_le {Gf : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ}
    {Ef : ℝ → (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ} {C C₂ : ℝ} (hC : 0 ≤ C)
    (hGc : Continuous Gf) (hEc : ∀ R, Continuous (Ef R)) (hGL : ∀ x, Gf x ∈ L3)
    (hsupp : ∀ R, 1 ≤ R → ∀ x, 2 * R ^ 2 < ∑ i, x i ^ 2 → Ef R x = 0)
    (hlog : ∀ R, 1 ≤ R → ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2},
      frobSq (Gf x) ^ 2 ≤ C * Real.log (2 + 2 * R))
    (hE : ∀ R, 1 ≤ R → ∀ x, frobSq (Ef R x) ≤ C₂ / R ^ 2) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ R : ℝ, 1 ≤ R → ∀ δ Λ : ℝ, 0 ≤ δ →
      ∫ x, qDeltaLambda δ Λ (tbt4Chi (R⁻¹ • x) • Gf x + Ef R x) ≤
        (∫ x, q3 (projL3 (tbt4Chi (R⁻¹ • x) • Gf x + Ef R x))) +
          C₀ * δ * (1 + Real.log R + Λ ^ 4 / R) := by
  set A := 24 * C + 512 * C₂ ^ 2
  have hA : 0 ≤ A := by positivity
  refine ⟨2 * A + 128 * C₂ ^ 2, by positivity, fun R hR δ Λ hδ => ?_⟩
  have hR0 : 0 < R := by linarith
  have hsupp' : ∀ x, 2 * R ^ 2 < ∑ i, x i ^ 2 → tbt4Chi (R⁻¹ • x) = 0 ∧ Ef R x = 0 :=
    fun x hx => ⟨tbt4_chiR_zero hR0 hx, hsupp R hR x hx⟩
  have hAc : Continuous fun x => tbt4Chi (R⁻¹ • x) • Gf x + Ef R x :=
    ((tbt4_continuous_chiR R).smul hGc).add (hEc R)
  have hAs : HasCompactSupport fun x => tbt4Chi (R⁻¹ • x) • Gf x + Ef R x :=
    tbt4_hasCompactSupport hR0 fun x hx => by simp [hsupp' x hx]
  have h1 := tbt4_energy hAc hAs (Λ := Λ) hδ
  have h2 := tbt4_proj4_le hR hC hGc (hEc R) (tbt4_continuous_chiR R) hGL
    (fun _ => tbt4_chi_nonneg _) (fun _ => tbt4_chi_le_one _) hsupp' (hlog R hR) (hE R hR)
  have h3 := tbt4_perp4_le (χf := fun x => tbt4Chi (R⁻¹ • x)) hR0 (hEc R) hGL (hsupp R hR)
    (hE R hR)
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hw : 0 ≤ Λ ^ 4 / R := by positivity
  have e2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * δ)
  have e3 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * δ * Λ ^ 4)
  have e3' : 2 * δ * Λ ^ 4 * (64 * C₂ ^ 2 / R) = 128 * C₂ ^ 2 * δ * (Λ ^ 4 / R) := by ring
  have hc1 : 0 ≤ 2 * A * δ * (Λ ^ 4 / R) := by positivity
  have hc2 : 0 ≤ 128 * C₂ ^ 2 * δ * (1 + Real.log R) := by positivity
  nlinarith

/-- **`R = δ⁻⁴`** (TeX 2028–2029, "taking `R = δ⁻⁴` makes the right-hand side tend to `I`"): if
`a (R) → I` as `R → ∞` (here `a (R) = ∫ q₃ (π ∇u_R) = I + o_R (1)`), then with `Λ = K/δ` and
`R = δ⁻⁴` the right-hand side `a (R) + C₀ δ (1 + log R + Λ⁴ / R)` tends to `I` as `δ ↓ 0`:
`Λ⁴ / R = K⁴` and `δ log δ⁻⁴ = −4 δ log δ → 0`. -/
theorem tbt4_tendsto_rhs {a : ℝ → ℝ} {I : ℝ} (ha : Filter.Tendsto a Filter.atTop (nhds I))
    (C₀ K : ℝ) :
    Filter.Tendsto (fun δ : ℝ => a (δ ^ 4)⁻¹ +
      C₀ * δ * (1 + Real.log (δ ^ 4)⁻¹ + (K / δ) ^ 4 / (δ ^ 4)⁻¹)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds I) := by
  have hR : Filter.Tendsto (fun δ : ℝ => (δ ^ 4)⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    refine ((Filter.tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
      tendsto_inv_nhdsGT_zero).congr fun δ => ?_
    simp [inv_pow]
  have h0 : Filter.Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id
  -- `δ log δ⁻¹ = log δ⁻¹ / δ⁻¹ → 0`
  have hl : Filter.Tendsto (fun δ : ℝ => Real.log δ⁻¹ ^ 1 / (1 * δ⁻¹ + 0))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_inv_nhdsGT_zero
  have hc : Filter.Tendsto (fun δ : ℝ => C₀ * ((1 + K ^ 4) * δ +
      4 * (Real.log δ⁻¹ ^ 1 / (1 * δ⁻¹ + 0)))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := ((h0.const_mul (1 + K ^ 4)).add (hl.const_mul 4)).const_mul C₀
    rw [mul_zero, mul_zero, add_zero, mul_zero] at this
    exact this
  have h2 : Filter.Tendsto (fun δ : ℝ => C₀ * δ * (1 + Real.log (δ ^ 4)⁻¹ + (K / δ) ^ 4 /
      (δ ^ 4)⁻¹)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    rw [← inv_pow, Real.log_pow]
    field_simp
    ring
  have := (ha.comp hR).add h2
  rw [add_zero] at this
  exact this

/-- **The cutoff argument** of the proof of Theorem 1.3 (TeX 1993–2029), abstract in the bulk
field `G` (values in `𝓛₃`, `q₃ (G) ∈ L¹`, `I = ∫ q₃ (G) < 0`,
`∫_{|x|² ≤ 2R²} |G|⁴ ≤ C log (2 + 2R)`) and the cut-off errors `E_R` (vanishing off
`|x|² ≤ 2R²`, `|E_R|² ≤ C₂ / R²`), so that Corollary 5.4 uses it unchanged: there is
`δ₀ ∈ (0, 1]` such that for `0 < δ < δ₀`, `Λ = K/δ` and `R = δ⁻⁴`,
`∫ q_{δ,Λ} (χ (·/R) G + E_R) < 0`. The right-hand side of `tbt4_energy_le` tends to `I < 0`
as `δ ↓ 0` (`tbt4_tendsto_q3_proj`, `tbt4_tendsto_rhs`), so it is negative for small `δ`. -/
theorem tbt4_cutoff_neg {Gf : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ}
    {Ef : ℝ → (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ} {C C₂ : ℝ} (hC : 0 ≤ C)
    (hGc : Continuous Gf) (hEc : ∀ R, Continuous (Ef R)) (hGL : ∀ x, Gf x ∈ L3)
    (hGi : Integrable fun x => q3 (Gf x)) (hI : ∫ x, q3 (Gf x) < 0)
    (hsupp : ∀ R, 1 ≤ R → ∀ x, 2 * R ^ 2 < ∑ i, x i ^ 2 → Ef R x = 0)
    (hlog : ∀ R, 1 ≤ R → ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2},
      frobSq (Gf x) ^ 2 ≤ C * Real.log (2 + 2 * R))
    (hE : ∀ R, 1 ≤ R → ∀ x, frobSq (Ef R x) ≤ C₂ / R ^ 2) (K : ℝ) :
    ∃ δ₀ > 0, δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ R : ℝ, R = (δ ^ 4)⁻¹ →
      ∫ x, qDeltaLambda δ (K / δ) (tbt4Chi (R⁻¹ • x) • Gf x + Ef R x) < 0 := by
  obtain ⟨C₀, -, hen⟩ := tbt4_energy_le hC hGc hEc hGL hsupp hlog hE
  have hT := tbt4_tendsto_rhs (tbt4_tendsto_q3_proj hC hGc hEc hGL hGi hsupp hlog hE) C₀ K
  obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hT.eventually (gt_mem_nhds hI))
  refine ⟨min δ₁ 1, lt_min hδ₁ one_pos, min_le_right _ _, fun δ hδ hδ' R hR => ?_⟩
  have hδ1 : δ ≤ 1 := (hδ'.trans_le (min_le_right _ _)).le
  have hR1 : 1 ≤ R := hR ▸ one_le_inv_iff₀.mpr ⟨by positivity, pow_le_one₀ hδ.le hδ1⟩
  have h1 := hen R hR1 δ (K / δ) hδ.le
  have h2 := hsub ⟨hδ, hδ'.trans_le (min_le_left _ _)⟩
  simp only [Set.mem_ofPred_eq] at h2
  subst hR
  linarith

/-! ### Rescaling into the unit cube -/

theorem tbt4_jac_eqOn {n p : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {v₁ v₂ : (Fin n → ℝ) → Fin p → ℝ} (h : Set.EqOn v₁ v₂ U) {x : Fin n → ℝ} (hx : x ∈ U) :
    jac v₁ x = jac v₂ x := by
  ext i k
  simp only [jac, Matrix.of_apply]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx)
    (fun y hy => congrFun (h hy) i))]

theorem tbt4_jac_eq_zero {n p : ℕ} {V : (Fin n → ℝ) → Fin p → ℝ} {x : Fin n → ℝ}
    (hx : x ∉ tsupport V) : jac V x = 0 := by
  have hU : IsOpen (tsupport V)ᶜ := (isClosed_tsupport V).isOpen_compl
  have h : Set.EqOn V (fun _ => 0) (tsupport V)ᶜ := fun y hy =>
    image_eq_zero_of_notMem_tsupport hy
  rw [tbt4_jac_eqOn hU h hx]
  ext i k; simp [jac]

theorem tbt4_jac_scale {n p : ℕ} {V : (Fin n → ℝ) → Fin p → ℝ} (hV : Differentiable ℝ V)
    (K a : ℝ) (x : Fin n → ℝ) : jac (fun z => K • V (a • z)) x = (K * a) • jac V (a • x) := by
  ext i k
  have hi : DifferentiableAt ℝ (fun y => V y i) (a • x) := (differentiableAt_pi.mp (hV _)) i
  have h1 : HasFDerivAt (fun z : Fin n → ℝ => a • z) (a • ContinuousLinearMap.id ℝ _) x :=
    (hasFDerivAt_id x).const_smul a
  have h2 := (hi.hasFDerivAt.comp x h1).const_mul K
  simp only [jac, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (fun z => K * V (a • z) i) = fun z => K * ((fun y => V y i) ∘ fun z => a • z) z from rfl,
    h2.fderiv]
  simp [mul_assoc]

theorem tbt4_jac_sub {n p : ℕ} {W : (Fin n → ℝ) → Fin p → ℝ} (hW : Differentiable ℝ W)
    (c x : Fin n → ℝ) : jac (fun x => W (x - c)) x = jac W (x - c) := by
  ext i k
  have hi : DifferentiableAt ℝ (fun y => W y i) (x - c) := (differentiableAt_pi.mp (hW _)) i
  have h := hi.hasFDerivAt.comp x (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) c)
  simp only [jac, Matrix.of_apply]
  rw [show (fun y => W (y - c) i) = (fun y => W y i) ∘ fun y => y - c from rfl, h.fderiv]
  rfl

theorem tbt4_contDiff_uR {u : (Fin 3 → ℝ) → Fin 2 → ℝ} (hu : ContDiff ℝ tbt3Top u) (R : ℝ) :
    ContDiff ℝ tbt3Top (tbt4uR u R) :=
  (tbt4_contDiff_chi.comp (contDiff_const_smul _)).smul hu

theorem tbt4_uR_zero (u : (Fin 3 → ℝ) → Fin 2 → ℝ) {R : ℝ} (hR : 0 < R) {x : Fin 3 → ℝ}
    (hx : 2 * R ^ 2 < ∑ i, x i ^ 2) : tbt4uR u R x = 0 := by
  simp [tbt4uR, tbt4_chiR_zero hR hx]

/-- A smooth `u : ℝ³ → ℝ²` vanishing on `|x|² > 2R²` with `∫ q (∇u) < 0` refutes
quasiconvexity of `q` at `0`: rescaled as `x ↦ λ u ((x − c)/λ)`, `c = (1/2, 1/2, 1/2)`,
`λ = 1/(8R)`, it has compact support in the open unit cube, the same gradients, and energy
`λ³ ∫ q (∇u) < 0`. -/
theorem tbt4_not_quasiconvexAt_of_witness {q : Matrix (Fin 2) (Fin 3) ℝ → ℝ} (hq : Continuous q)
    (hq0 : q 0 = 0) {R : ℝ} (hR : 0 < R) {v : (Fin 3 → ℝ) → Fin 2 → ℝ}
    (hv : ContDiff ℝ tbt3Top v) (hvz : ∀ z, 2 * R ^ 2 < ∑ i, z i ^ 2 → v z = 0)
    (hneg : ∫ x, q (jac v x) < 0) : ¬ QuasiconvexAt q 0 := by
  have hvd : Differentiable ℝ v := hv.differentiable (by simp)
  set c : Fin 3 → ℝ := fun _ => 1 / 2
  set l : ℝ := 1 / (8 * R)
  have hl : 0 < l := by positivity
  set W : (Fin 3 → ℝ) → Fin 2 → ℝ := fun z => l • v (l⁻¹ • z)
  have hWd : Differentiable ℝ W := (hvd.comp (differentiable_id.const_smul l⁻¹)).const_smul l
  set φ : (Fin 3 → ℝ) → Fin 2 → ℝ := fun x => W (x - c)
  have hφ : ContDiff ℝ tbt3Top φ :=
    ((hv.comp (contDiff_const_smul _)).const_smul l).comp (contDiff_id.sub contDiff_const)
  have hjac : ∀ x, jac φ x = jac v (l⁻¹ • (x - c)) := by
    intro x
    rw [tbt4_jac_sub hWd, tbt4_jac_scale hvd, mul_inv_cancel₀ hl.ne', one_smul]
  have hφz : ∀ x, x ∉ Metric.closedBall c (1 / 4) → φ x = 0 := by
    intro x hx
    simp only [Metric.mem_closedBall, not_le] at hx
    have hn : 2 * R < ‖l⁻¹ • (x - c)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), ← dist_eq_norm]
      simp only [l]
      rw [one_div, inv_inv]
      nlinarith
    have := tbt4_lt_sum_sq (by positivity) hn
    simp only [φ, W, hvz _ (by nlinarith), smul_zero]
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
  refine not_quasiconvexAt_of_smooth hq hφ hc (hts.trans hball) ?_
  have hout : ∀ x, x ∉ unitCube 3 → q (0 + jac φ x) = 0 := by
    intro x hx
    have : x ∉ tsupport φ := fun h => hx (hball (hts h))
    rw [tbt4_jac_eq_zero this, add_zero, hq0]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout, hq0]
  simp_rw [zero_add, hjac]
  rw [integral_sub_right_eq_self (fun x => q (jac v (l⁻¹ • x))) c,
    Measure.integral_comp_inv_smul (μ := volume) (fun y => q (jac v y)) l,
    Module.finrank_fin_fun, smul_eq_mul]
  exact mul_neg_of_pos_of_neg (abs_pos.mpr (by positivity)) hneg

/-- **Proof of Theorem 1.3 (a)** (`cs-thm1.3a-witness`, TeX lines 1977–2029): for every `K` there
is `δ₀ > 0` such that for `0 < δ < δ₀`, `q_{δ, K/δ}` is not quasiconvex at `0`.

Proof, as in the paper. Let `u` be given by Proposition 5.2 (`proposition5_2`: `u` smooth and
bounded, `∇u ∈ 𝓛₃`, `q₃ (∇u) < 0`, `q₃ (∇u) ∈ L¹`, `∫_{B_R} |∇u|⁴ ≤ C log (2 + R)`), and
`I = ∫_{ℝ³} q₃ (∇u) < 0` (`tbt4_integral_neg`, TeX 1995). Put `u_R = χ (·/R) u`
(`tbt4uR`), where the cut-off `χ (y) = σ (2 − |y|²)` (`tbt4Chi`, `σ = Real.smoothTransition`)
is smooth, `0 ≤ χ ≤ 1`, equal to one on `B₁` and supported in `|y|² ≤ 2`. Then
`∇u_R = χ (·/R) ∇u + E_R` with `E_R = u ⊗ ∇[χ (·/R)]` (`tbt4_jac_uR`), and
`|E_R|² ≤ 6 M² G² / R²`, `E_R = 0` off `|x|² ≤ 2R²` (`|u| ≤ M`, `|∇χ| ≤ G`;
`tbt4_frobSq_ER_le`, `tbt4_supp`). The chain of the paper is `tbt4_cutoff_neg`, applied with
`G = ∇u` and the logarithmic bound on `|x|² ≤ 2R²` (`tbt4_log_bound`):
* `∫ |E_R|⁴ ≤ 64 C₂² / R` (`tbt4_integral_E4_le`, TeX 2004);
* the Hölder step: `|∫ q₃ (π ∇u_R) − ∫ χ (·/R)⁴ q₃ (∇u)| ≤ L (C log (2 + 2R))^{3/4}
  (64 C₂² / R)^{1/4} + M · 64 C₂² / R` (`tbt4_holder`, from the two-sided quartic bound
  `tbt4_q3_perturb`, `π ∇u_R = χ_R ∇u + π E_R` and Hölder's inequality with exponents `4/3`, `4`),
  and `∫ χ (·/R)⁴ q₃ (∇u) → I` by dominated convergence (`tbt4_tendsto_integral_chi`), so
  `∫ q₃ (π ∇u_R) = I + o_R (1)` (`tbt4_tendsto_q3_proj`, TeX 2005–2014);
* `∫ |π ∇u_R|⁴ ≤ (24 C + 512 C₂²) (1 + log R)` and, by `π^⊥ ∇u_R = π^⊥ E_R`,
  `∫ |π^⊥ ∇u_R|⁴ ≤ 64 C₂² / R` (`tbt4_proj4_le`, `tbt4_perp4_le`, TeX 2015–2021);
* consequently, with the penalty bound `tbt4_energy`,
  `∫ q_{δ,Λ} (∇u_R) ≤ ∫ q₃ (π ∇u_R) + C₀ δ (1 + log R + Λ⁴ / R)`, that is
  `≤ I + o_R (1) + C₀ δ (1 + log R + Λ⁴ / R)` (`tbt4_energy_le`, TeX 2022–2027);
* with `R = δ⁻⁴` and `Λ = K/δ` the right-hand side tends to `I < 0` as `δ ↓ 0`
  (`tbt4_tendsto_rhs`, TeX 2028–2029), so it is negative for `0 < δ < δ₀`.
Rescaled into the unit cube (`tbt4_not_quasiconvexAt_of_witness`), `u_R` refutes
quasiconvexity at `0`. -/

theorem twoByThree_not_quasiconvexAt_qDeltaLambda (K : ℝ) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ¬ QuasiconvexAt (qDeltaLambda δ (K / δ)) 0 := by
  -- "Let `u` be given by Proposition 5.2"
  obtain ⟨u, hsm, ⟨Mu, hMu⟩, hL3, hneg, hint, ⟨C, hC⟩⟩ := proposition5_2
  obtain ⟨G, hG, hGb⟩ := tbt4_fderiv_chi_bound
  set Mu' := max Mu 0
  have hMu' : ∀ x, ‖u x‖ ≤ Mu' := fun x => (hMu x).trans (le_max_left _ _)
  -- `I = ∫ q₃ (∇u) < 0`
  have hI : ∫ x, q3 (jac u x) < 0 := tbt4_integral_neg hneg hint
  -- the logarithmic bound of Proposition 5.2 on `|x|² ≤ 2R²`
  have hlog : ∀ R : ℝ, 1 ≤ R → ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2},
      frobSq (jac u x) ^ 2 ≤ max C 0 * Real.log (2 + 2 * R) := fun R hR => by
    refine (tbt4_log_bound hsm hC (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith))
  obtain ⟨δ₀, hδ₀, -, hcut⟩ := tbt4_cutoff_neg (Gf := jac u) (Ef := tbt4ER u)
    (C₂ := 6 * Mu' ^ 2 * G ^ 2) (le_max_right _ _) (tbt_continuous_jac hsm)
    (fun R => tbt4_continuous_ER hsm.continuous R) hL3 hint hI
    (fun R hR x hx => (tbt4_supp u (by linarith) hx).2) hlog
    (fun R hR x => tbt4_frobSq_ER_le hMu' hG hGb (by linarith) x) K
  refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' => ?_⟩
  set R := (δ ^ 4)⁻¹
  have hR : 0 < R := by positivity
  have hneg' : ∫ x, qDeltaLambda δ (K / δ) (jac (tbt4uR u R) x) < 0 := by
    simp_rw [tbt4_jac_uR hsm]
    exact hcut δ hδ hδ₀' R rfl
  exact tbt4_not_quasiconvexAt_of_witness (tbt4_continuous_qDeltaLambda δ (K / δ))
    (tbt4_qDeltaLambda_zero δ (K / δ)) hR (tbt4_contDiff_uR hsm R) (fun z hz => tbt4_uR_zero u hR hz)
    hneg'

end Cassese
