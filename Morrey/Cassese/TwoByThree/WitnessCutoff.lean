module

public import Morrey.Cassese.TwoByThree.Witness
public import Morrey.Cassese.TwoByThree.Polynomial
public import Morrey.Cassese.Bridges
public import Morrey.Cassese.TwoByThree.Transpose.Estimate
public import Morrey.Cassese.TwoByThree.Extension

/-!
# Section 5: the cutoff of the witness of Proposition 5.2 (proof of Theorem 1.3 (a))

The proof of Theorem 1.3 (a) (TeX lines 1993–2029) cuts off the witness `u` of Proposition 5.2,
`u_R = χ (·/R) u`, and estimates `∫ q_{δ,Λ} (∇u_R)` with `Λ = K/δ`, `R = δ⁻⁴`.

Reusable estimates (for Corollary 5.4 too): the quartic perturbation bound `tbt4_q3_perturb`, the
pointwise estimate `tbt4_pointwise` and its integrated form `tbt4_energy` (abstract in the bulk
field `G ∈ 𝓛₃` and the cut-off error `E`), and the rescaling `tbt4_not_quasiconvexAt_of_witness`.

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

/-- The perturbation bound for the quartic `q₃`:
`q₃ (X + Y) ≤ q₃ (X) + L |X|³ |Y| + M |Y|⁴` (Frobenius norms). -/
theorem tbt4_q3_perturb : ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧ ∀ X Y : Matrix (Fin 2) (Fin 3) ℝ,
    q3 (X + Y) ≤ q3 X + L * √(frobSq X) ^ 3 * √(frobSq Y) + M * √(frobSq Y) ^ 4 := by
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
      g (V + W) - g V ≤ L₀ * ‖V‖ ^ 3 * ‖W‖ + 17 * M₀ * ‖W‖ ^ 4 := by
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
      have : g (V + W) - g V ≤ ‖g (V + W) - g V‖ := Real.le_norm_self _
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
      have := neg_abs_le (g V)
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

/-- Young's inequality in the form used: `a³ b ≤ η a⁴ + η⁻³ b⁴`. -/
theorem tbt4_young {a b η : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 < η) :
    a ^ 3 * b ≤ η * a ^ 4 + η⁻¹ ^ 3 * b ^ 4 := by
  have h1 : 0 ≤ η * a ^ 4 := by positivity
  have h2 : 0 ≤ η⁻¹ ^ 3 * b ^ 4 := by positivity
  rcases le_or_gt b (η * a) with h | h
  · have : a ^ 3 * b ≤ a ^ 3 * (η * a) := mul_le_mul_of_nonneg_left h (by positivity)
    nlinarith
  · have ha' : a ≤ η⁻¹ * b := by
      rw [← div_eq_inv_mul, le_div_iff₀ hη]; linarith
    have : a ^ 3 * b ≤ (η⁻¹ * b) ^ 3 * b := by gcongr
    nlinarith

theorem tbt4_frobSq_add_le {d m : ℕ} (A B : Matrix (Fin d) (Fin m) ℝ) :
    frobSq (A + B) ≤ 2 * frobSq A + 2 * frobSq B := by
  simp only [frobSq, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
    nlinarith [sq_nonneg (A i j - B i j)]

/-- Pythagoras for `π`: `|E|² = |π E|² + |π^⊥ E|²`. -/
theorem tbt4_frobSq_pythagoras (E : Matrix (Fin 2) (Fin 3) ℝ) :
    frobSq E = frobSq (projL3 E) + frobSq (E - projL3 E) := by
  simp [frobSq, projL3, Fin.sum_univ_two, Fin.sum_univ_three]; ring

/-- **The pointwise estimate** behind the cutoff argument of Theorem 1.3 (a): for `G ∈ 𝓛₃`,
`χ ∈ [0, 1]` and any error `E`,
`q_{δ,Λ} (χ G + E) ≤ χ⁴ q₃ (G) + (L η + 16 δ) |G|⁴ + (L η⁻³ + M + 16 δ + 2 δ Λ⁴) |E|⁴`
(with `L`, `M` from `tbt4_q3_perturb`). -/
theorem tbt4_pointwise {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hpert : ∀ X Y : Matrix (Fin 2) (Fin 3) ℝ,
      q3 (X + Y) ≤ q3 X + L * √(frobSq X) ^ 3 * √(frobSq Y) + M * √(frobSq Y) ^ 4)
    {G E : Matrix (Fin 2) (Fin 3) ℝ} (hG : G ∈ L3) {χ δ η Λ : ℝ} (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hδ : 0 ≤ δ) (hη : 0 < η) :
    qDeltaLambda δ Λ (χ • G + E) ≤ χ ^ 4 * q3 G + (L * η + 16 * δ) * frobSq G ^ 2 +
      (L * η⁻¹ ^ 3 + M + 16 * δ + 2 * δ * Λ ^ 4) * frobSq E ^ 2 := by
  set P := projL3 E
  have hπ : projL3 (χ • G + E) = χ • G + P := by
    rw [add_comm, tbt_projL3_add_smul, tbt3_projL3_of_mem hG, add_comm]
  have hperp : χ • G + E - projL3 (χ • G + E) = E - P := by rw [hπ]; abel
  have hpy := tbt4_frobSq_pythagoras E
  have hP0 := tbt_frobSq_nonneg P
  have hN0 := tbt_frobSq_nonneg (E - P)
  have hG0 := tbt_frobSq_nonneg G
  have hE0 := tbt_frobSq_nonneg E
  have hPE : frobSq P ≤ frobSq E := by linarith
  have hNE : frobSq (E - P) ≤ frobSq E := by linarith
  have hχG : frobSq (χ • G) = χ ^ 2 * frobSq G := tbt3_frobSq_smul χ G
  -- the quartic
  set a := √(frobSq (χ • G))
  set b := √(frobSq P)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha4 : a ^ 4 = (χ ^ 2 * frobSq G) ^ 2 := by
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, Real.sq_sqrt (tbt_frobSq_nonneg _), hχG]
  have hb4 : b ^ 4 = frobSq P ^ 2 := by
    rw [show b ^ 4 = (b ^ 2) ^ 2 by ring, Real.sq_sqrt hP0]
  have hχ4 : (χ ^ 2 * frobSq G) ^ 2 ≤ frobSq G ^ 2 := by
    have : χ ^ 2 ≤ 1 := by nlinarith
    have : χ ^ 2 * frobSq G ≤ frobSq G := by nlinarith
    exact pow_le_pow_left₀ (by positivity) this 2
  have hP4 : frobSq P ^ 2 ≤ frobSq E ^ 2 := pow_le_pow_left₀ hP0 hPE 2
  have hq := hpert (χ • G) P
  have hy := tbt4_young ha0 hb0 hη
  have hq' : q3 (χ • G + P) ≤ χ ^ 4 * q3 G + L * η * frobSq G ^ 2 +
      (L * η⁻¹ ^ 3 + M) * frobSq E ^ 2 := by
    rw [tbt_q3_smul] at hq
    have e1 : L * a ^ 3 * b ≤ L * (η * a ^ 4 + η⁻¹ ^ 3 * b ^ 4) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hy hL
    rw [ha4, hb4] at e1
    have hb4' : √(frobSq P) ^ 4 = frobSq P ^ 2 := hb4
    rw [hb4'] at hq
    have hηi : 0 ≤ η⁻¹ ^ 3 := by positivity
    have f1 := mul_le_mul_of_nonneg_left hχ4 (mul_nonneg hL hη.le)
    have f2 := mul_le_mul_of_nonneg_left hP4 (mul_nonneg hL hηi)
    have f3 := mul_le_mul_of_nonneg_left hP4 hM
    have e2 : L * (η * (χ ^ 2 * frobSq G) ^ 2 + η⁻¹ ^ 3 * frobSq P ^ 2) =
        L * η * (χ ^ 2 * frobSq G) ^ 2 + L * η⁻¹ ^ 3 * frobSq P ^ 2 := by ring
    have e3 : χ ^ 4 * q3 G + L * η * frobSq G ^ 2 + (L * η⁻¹ ^ 3 + M) * frobSq E ^ 2 =
        χ ^ 4 * q3 G + L * η * frobSq G ^ 2 + L * η⁻¹ ^ 3 * frobSq E ^ 2 + M * frobSq E ^ 2 := by
      ring
    have hab : L * √(frobSq (χ • G)) ^ 3 * √(frobSq P) = L * a ^ 3 * b := rfl
    rw [e3]
    linarith
  -- the penalty
  have hS : frobSq (χ • G + P) ≤ 2 * frobSq G + 2 * frobSq E := by
    have := tbt4_frobSq_add_le (χ • G) P
    have : χ ^ 2 * frobSq G ≤ frobSq G := by
      have : χ ^ 2 ≤ 1 := by nlinarith
      nlinarith
    linarith
  have hpen : (frobSq (χ • G + P) + Λ ^ 2 * frobSq (E - P)) ^ 2 ≤
      16 * frobSq G ^ 2 + (16 + 2 * Λ ^ 4) * frobSq E ^ 2 := by
    have h1 : (frobSq (χ • G + P) + Λ ^ 2 * frobSq (E - P)) ^ 2 ≤
        2 * frobSq (χ • G + P) ^ 2 + 2 * (Λ ^ 2 * frobSq (E - P)) ^ 2 := by
      nlinarith [sq_nonneg (frobSq (χ • G + P) - Λ ^ 2 * frobSq (E - P))]
    have h2 : frobSq (χ • G + P) ^ 2 ≤ (2 * frobSq G + 2 * frobSq E) ^ 2 :=
      pow_le_pow_left₀ (tbt_frobSq_nonneg _) hS 2
    have h3 : (Λ ^ 2 * frobSq (E - P)) ^ 2 ≤ Λ ^ 4 * frobSq E ^ 2 := by
      rw [mul_pow, show (Λ ^ 2) ^ 2 = Λ ^ 4 by ring]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN0 hNE 2) (by positivity)
    nlinarith [sq_nonneg (frobSq G - frobSq E)]
  rw [qDeltaLambda, hperp, hπ]
  have h := mul_le_mul_of_nonneg_left hpen hδ
  have e : χ ^ 4 * q3 G + (L * η + 16 * δ) * frobSq G ^ 2 +
      (L * η⁻¹ ^ 3 + M + 16 * δ + 2 * δ * Λ ^ 4) * frobSq E ^ 2 =
      (χ ^ 4 * q3 G + L * η * frobSq G ^ 2 + (L * η⁻¹ ^ 3 + M) * frobSq E ^ 2) +
        δ * (16 * frobSq G ^ 2 + (16 + 2 * Λ ^ 4) * frobSq E ^ 2) := by ring
  rw [e]
  linarith

theorem tbt4_qDeltaLambda_zero (δ Λ : ℝ) : qDeltaLambda δ Λ 0 = 0 := by
  have h0 : (0 : Matrix (Fin 2) (Fin 3) ℝ) ∈ L3 := by rw [mem_L3_iff]; simp
  have hq : q3 0 = 0 := by simpa using tbt_q3_smul 0 0
  rw [tbt3_qDeltaLambda_of_mem δ Λ h0, hq]
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
  tbt3_continuous_of_ihp (tbt_ihp_qDeltaLambda δ Λ)

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

/-- **The energy estimate** of the cutoff argument (TeX 1993–2029), abstract in the bulk field
`G` (with values in `𝓛₃`, `q₃ (G) ≤ 0`) and the cutoff error `E` (supported in `|x|² ≤ 2R²`,
`|E|² ≤ C₂ / R²`), for a cutoff `χ ∈ [0, 1]` equal to `1` on the unit ball and `0` off
`|x|² ≤ 2R²`:
`∫ q_{δ,Λ} (χ G + E) ≤ ∫_{B₁} q₃ (G) + (L η + 16 δ) C₁ + (L η⁻³ + M + 16 δ + 2 δ Λ⁴) · 64 C₂² / R`
where `C₁` bounds `∫_{|x|² ≤ 2R²} |G|⁴`. -/
theorem tbt4_energy {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hpert : ∀ X Y : Matrix (Fin 2) (Fin 3) ℝ,
      q3 (X + Y) ≤ q3 X + L * √(frobSq X) ^ 3 * √(frobSq Y) + M * √(frobSq Y) ^ 4)
    {Gf Ef : (Fin 3 → ℝ) → Matrix (Fin 2) (Fin 3) ℝ} {χf : (Fin 3 → ℝ) → ℝ}
    {R C₁ C₂ δ η Λ : ℝ} (hR : 0 < R) (hδ : 0 ≤ δ) (hη : 0 < η)
    (hGc : Continuous Gf) (hEc : Continuous Ef) (hχc : Continuous χf)
    (hGL : ∀ x, Gf x ∈ L3) (hGq : ∀ x, q3 (Gf x) ≤ 0) (hGi : Integrable fun x => q3 (Gf x))
    (hχ0 : ∀ x, 0 ≤ χf x) (hχ1 : ∀ x, χf x ≤ 1) (hχB : ∀ x, ∑ i, x i ^ 2 < 1 → χf x = 1)
    (hsupp : ∀ x, 2 * R ^ 2 < ∑ i, x i ^ 2 → χf x = 0 ∧ Ef x = 0)
    (hlog : ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2}, frobSq (Gf x) ^ 2 ≤ C₁)
    (hE : ∀ x, frobSq (Ef x) ≤ C₂ / R ^ 2) :
    ∫ x, qDeltaLambda δ Λ (χf x • Gf x + Ef x) ≤
      (∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < 1}, q3 (Gf x)) + (L * η + 16 * δ) * C₁ +
        (L * η⁻¹ ^ 3 + M + 16 * δ + 2 * δ * Λ ^ 4) * (64 * (C₂ / R ^ 2) ^ 2 * R ^ 3) := by
  set S := {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2}
  set B1 := {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < 1}
  set c₁ := L * η + 16 * δ
  set c₂ := L * η⁻¹ ^ 3 + M + 16 * δ + 2 * δ * Λ ^ 4
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  have hsq : Continuous fun x : Fin 3 → ℝ => ∑ i, x i ^ 2 := by fun_prop
  have hSm : MeasurableSet S := measurableSet_le hsq.measurable measurable_const
  have hB1m : MeasurableSet B1 := measurableSet_lt hsq.measurable measurable_const
  have hSc : IsCompact S := tbt4_isCompact_sum_sq_le _
  have hout : ∀ x, x ∉ Metric.closedBall (0 : Fin 3 → ℝ) (2 * R) →
      2 * R ^ 2 < ∑ i, x i ^ 2 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    have := tbt4_lt_sum_sq (by positivity) hx
    nlinarith
  -- the integrand: continuous, compactly supported
  set f := fun x => qDeltaLambda δ Λ (χf x • Gf x + Ef x)
  have hfc : Continuous f :=
    (tbt4_continuous_qDeltaLambda δ Λ).comp ((hχc.smul hGc).add hEc)
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall 0 (2 * R)) fun x hx => by
      obtain ⟨h1, h2⟩ := hsupp x (hout x hx)
      simp only [f, h1, h2, zero_smul, add_zero, tbt4_qDeltaLambda_zero])
  -- the three terms of the bound
  have hi1 : Integrable fun x => χf x ^ 4 * q3 (Gf x) := by
    refine hGi.norm.mono' ((hχc.pow 4).mul (tbt3_continuous_q3'.comp hGc)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (hχ0 x) 4)]
    have : χf x ^ 4 ≤ 1 := pow_le_one₀ (hχ0 x) (hχ1 x)
    nlinarith [abs_nonneg (q3 (Gf x))]
  have hcG : Continuous fun x => frobSq (Gf x) ^ 2 := (tbt3_continuous_frobSq'.comp hGc).pow 2
  have hi2 : Integrable (S.indicator fun x => frobSq (Gf x) ^ 2) :=
    (integrable_indicator_iff hSm).mpr (hcG.continuousOn.integrableOn_compact hSc)
  have hcE : Continuous fun x => frobSq (Ef x) ^ 2 := (tbt3_continuous_frobSq'.comp hEc).pow 2
  have hEbd : ∀ x, frobSq (Ef x) ^ 2 ≤
      (Metric.closedBall (0 : Fin 3 → ℝ) (2 * R)).indicator (fun _ => (C₂ / R ^ 2) ^ 2) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Fin 3 → ℝ) (2 * R)
    · rw [Set.indicator_of_mem hx]
      exact pow_le_pow_left₀ (tbt_frobSq_nonneg _) (hE x) 2
    · rw [Set.indicator_of_notMem hx, (hsupp x (hout x hx)).2]
      simp [frobSq]
  have hiB : Integrable ((Metric.closedBall (0 : Fin 3 → ℝ) (2 * R)).indicator
      fun _ => (C₂ / R ^ 2) ^ 2) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (measure_closedBall_lt_top).ne)
  have hi3 : Integrable fun x => frobSq (Ef x) ^ 2 :=
    hiB.mono' hcE.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hEbd x)
  -- the pointwise bound
  have hpt : ∀ x, f x ≤ χf x ^ 4 * q3 (Gf x) + c₁ * S.indicator (fun x => frobSq (Gf x) ^ 2) x +
      c₂ * frobSq (Ef x) ^ 2 := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      exact tbt4_pointwise hL hM hpert (hGL x) (hχ0 x) (hχ1 x) hδ hη
    · rw [Set.indicator_of_notMem hx]
      have hx' : 2 * R ^ 2 < ∑ i, x i ^ 2 := not_le.mp hx
      obtain ⟨h1, h2⟩ := hsupp x hx'
      simp [f, h1, h2, tbt4_qDeltaLambda_zero, frobSq]
  have hint12 : Integrable fun x => χf x ^ 4 * q3 (Gf x) +
      c₁ * S.indicator (fun x => frobSq (Gf x) ^ 2) x := hi1.add (hi2.const_mul c₁)
  have hint : Integrable fun x => χf x ^ 4 * q3 (Gf x) +
      c₁ * S.indicator (fun x => frobSq (Gf x) ^ 2) x + c₂ * frobSq (Ef x) ^ 2 :=
    hint12.add (hi3.const_mul c₂)
  have hmono := integral_mono hfi hint hpt
  have e1 : ∫ x, (χf x ^ 4 * q3 (Gf x) + c₁ * S.indicator (fun x => frobSq (Gf x) ^ 2) x +
      c₂ * frobSq (Ef x) ^ 2) = (∫ x, (χf x ^ 4 * q3 (Gf x) +
        c₁ * S.indicator (fun x => frobSq (Gf x) ^ 2) x)) + ∫ x, c₂ * frobSq (Ef x) ^ 2 :=
    integral_add hint12 (hi3.const_mul c₂)
  have e2 : ∫ x, (χf x ^ 4 * q3 (Gf x) + c₁ * S.indicator (fun x => frobSq (Gf x) ^ 2) x) =
      (∫ x, χf x ^ 4 * q3 (Gf x)) + ∫ x, c₁ * S.indicator (fun x => frobSq (Gf x) ^ 2) x :=
    integral_add hi1 (hi2.const_mul c₁)
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_indicator hSm] at hmono
  -- `∫ χ⁴ q₃ (G) ≤ ∫_{B₁} q₃ (G)`
  have h1 : (∫ x, χf x ^ 4 * q3 (Gf x)) ≤ ∫ x in B1, q3 (Gf x) := by
    rw [← integral_indicator hB1m]
    refine integral_mono hi1 ((integrable_indicator_iff hB1m).mpr hGi.integrableOn) fun x => ?_
    by_cases hx : x ∈ B1
    · rw [Set.indicator_of_mem hx, hχB x hx]; simp
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (hχ0 x) 4) (hGq x)
  -- `∫ |E|⁴ ≤ 64 (C₂/R²)² R³`
  have h3 : (∫ x, frobSq (Ef x) ^ 2) ≤ 64 * (C₂ / R ^ 2) ^ 2 * R ^ 3 := by
    refine (integral_mono hi3 hiB hEbd).trans (le_of_eq ?_)
    rw [integral_indicator_const _ measurableSet_closedBall, Measure.real,
      Real.volume_pi_closedBall _ (by positivity), Fintype.card_fin,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    ring
  have h2 := mul_le_mul_of_nonneg_left hlog hc₁
  have h3' := mul_le_mul_of_nonneg_left h3 hc₂
  linarith

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
    (tbt3_continuous_frobSq'.comp (tbt_continuous_jac hu)).pow 2
  have hi : IntegrableOn (fun x => frobSq (jac u x) ^ 2)
      {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < (2 * R) ^ 2} :=
    (hc.continuousOn.integrableOn_compact (tbt4_isCompact_sum_sq_le ((2 * R) ^ 2))).mono_set
      fun x hx => le_of_lt (show ∑ i, x i ^ 2 < (2 * R) ^ 2 from hx)
  refine (setIntegral_mono_set hi (Filter.Eventually.of_forall fun x => by positivity)
    (Filter.Eventually.of_forall fun x hx => ?_)).trans (hC (2 * R) (by positivity))
  have h : ∑ i, x i ^ 2 ≤ 2 * R ^ 2 := hx
  show ∑ i, x i ^ 2 < (2 * R) ^ 2
  nlinarith

/-- `I₁ = ∫_{B₁} q₃ (∇u) < 0` when `q₃ (∇u) < 0` everywhere and `q₃ (∇u)` is integrable. -/
theorem tbt4_I1_neg {u : (Fin 3 → ℝ) → Fin 2 → ℝ} (hneg : ∀ x, q3 (jac u x) < 0)
    (hint : Integrable fun x => q3 (jac u x)) :
    ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < 1}, q3 (jac u x) < 0 := by
  set B := {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < 1}
  have hsq : Continuous fun x : Fin 3 → ℝ => ∑ i, x i ^ 2 := (tbt4_contDiff_sumSq (n := 0)).continuous
  have hBo : IsOpen B := isOpen_lt hsq continuous_const
  have hpos : 0 < ∫ x in B, -q3 (jac u x) := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => (neg_pos.mpr (hneg x)).le) hint.neg.integrableOn]
    have hs : Function.support (fun x => -q3 (jac u x)) = Set.univ :=
      Set.eq_univ_of_forall fun x => (neg_pos.mpr (hneg x)).ne'
    rw [hs, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hBo.measure_pos volume ⟨0, by simp [B]⟩
  rw [integral_neg] at hpos
  linarith

/-- `δ log (2 + 2 δ⁻⁴) ≤ (log 4 + 8) √δ` for `0 < δ ≤ 1`. -/
theorem tbt4_delta_log {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ * Real.log (2 + 2 * (δ ^ 4)⁻¹) ≤ (Real.log 4 + 8) * √δ := by
  have hs : 0 < √δ := Real.sqrt_pos.mpr hδ
  have hss : √δ ^ 2 = δ := Real.sq_sqrt hδ.le
  have h1 : 1 ≤ (δ ^ 4)⁻¹ := one_le_inv_iff₀.mpr ⟨by positivity, pow_le_one₀ hδ.le hδ1⟩
  have h2 : Real.log (2 + 2 * (δ ^ 4)⁻¹) ≤ Real.log 4 + 4 * Real.log δ⁻¹ := by
    have e : 4 * Real.log δ⁻¹ = Real.log (δ⁻¹ ^ 4) := by rw [Real.log_pow]; norm_num
    rw [e, ← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [inv_pow]; linarith
  -- `log δ⁻¹ ≤ 2 / √δ`
  have h3 : Real.log δ⁻¹ ≤ 2 * (√δ)⁻¹ := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
    have e : Real.log δ⁻¹ = 2 * Real.log (√δ)⁻¹ := by
      have : 2 * Real.log (√δ)⁻¹ = Real.log ((√δ)⁻¹ ^ 2) := by rw [Real.log_pow]; norm_num
      rw [this, inv_pow, hss]
    rw [e]; linarith
  have h4 : δ * (√δ)⁻¹ = √δ := by
    have := Real.mul_self_sqrt hδ.le
    field_simp; linarith
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hδs : δ ≤ √δ := (Real.le_sqrt hδ.le hδ.le).mpr (by nlinarith)
  calc δ * Real.log (2 + 2 * (δ ^ 4)⁻¹) ≤ δ * (Real.log 4 + 4 * Real.log δ⁻¹) :=
        mul_le_mul_of_nonneg_left h2 hδ.le
    _ ≤ δ * (Real.log 4 + 4 * (2 * (√δ)⁻¹)) := by gcongr
    _ = δ * Real.log 4 + 8 * (δ * (√δ)⁻¹) := by ring
    _ = δ * Real.log 4 + 8 * √δ := by rw [h4]
    _ ≤ √δ * Real.log 4 + 8 * √δ := by gcongr
    _ = (Real.log 4 + 8) * √δ := by ring

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

/-- **Proof of Theorem 1.3 (a)** (`cs-thm1.3a-witness`, TeX lines 1993–2029): for every `K` there
is `δ₀ > 0` such that for `0 < δ < δ₀`, `q_{δ, K/δ}` is not quasiconvex at `0`. The witness is the
cutoff `u_R = χ (·/R) u` of Proposition 5.2's `u` with `R = δ⁻⁴`, rescaled into the unit cube:
`∫ q_{δ,Λ} (∇u_R) ≤ I + o_R (1) + C₀ δ (1 + log R + Λ⁴ / R)`.

Proof, as in the paper ("let `u` be given by Proposition 5.2": `u` is obtained from the statement
of `proposition5_2`). `∇u_R = χ_R ∇u + E_R` with `E_R = u ⊗ ∇[χ (·/R)]` (`tbt4_jac_uR`),
`|E_R|² ≤ 6 M² G² / R²` (`|u| ≤ M`) and `E_R = 0` off `|x|² ≤ 2R²` (`tbt4_frobSq_ER_le`,
`tbt4_supp`). Since
`∇u ∈ 𝓛₃`, `π ∇u_R = χ_R ∇u + π E_R` and `π^⊥ ∇u_R = π^⊥ E_R`; the quartic perturbation bound
`q₃ (X + Y) ≤ q₃ (X) + L |X|³ |Y| + M |Y|⁴` (`tbt4_q3_perturb`) and the penalty give the pointwise
estimate `tbt4_pointwise`, which integrates to `tbt4_energy`:
`∫ q_{δ,Λ} (∇u_R) ≤ ∫_{B₁} q₃ (∇u) + (L η + 16 δ) ∫_{|x|² ≤ 2R²} |∇u|⁴ +
(L η⁻³ + M + 16 δ + 2 δ Λ⁴) · 64 C₂² / R`, with `∫_{|x|² ≤ 2R²} |∇u|⁴ ≤ C log (2 + 2R)`
(`tbt4_log_bound`, from the logarithmic bound of Proposition 5.2) and `∫ |E_R|⁴ ≲ R⁻¹`. With
`R = δ⁻⁴`, `Λ = K/δ`, `η = δ` this is `I₁ + O(√δ)` (`tbt4_delta_log`), negative for small `δ`; rescaled into the unit cube
(`tbt4_not_quasiconvexAt_of_witness`) the witness refutes quasiconvexity at `0`.

Mechanical choices (not departures of argument): Hölder's inequality in the paper's
`∫ q₃ (π ∇u_R) = ∫ χ_R⁴ q₃ (∇u) + O (R^{−1/4} (log R)^{3/4})` is replaced by the pointwise Young
bound `|X|³ |Y| ≤ η |X|⁴ + η⁻³ |Y|⁴` with `η = R^{−1/4} = δ`; the paper's `I = ∫_{ℝ³} q₃ (∇u)` is
replaced by `I₁ = ∫_{B₁} q₃ (∇u) < 0`, using `q₃ (∇u) < 0` and `χ_R = 1` on `B₁`, so that
`∫ χ_R⁴ q₃ (∇u) ≤ I₁` (inventory E20: the integrability of `q₃ (∇u)` is not needed for this
step); the cut-off is `χ (y) = σ (2 − |y|²)` with `σ = Real.smoothTransition`. -/

theorem twoByThree_not_quasiconvexAt_qDeltaLambda (K : ℝ) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ¬ QuasiconvexAt (qDeltaLambda δ (K / δ)) 0 := by
  -- "Let `u` be given by Proposition 5.2"
  obtain ⟨u, hsm, ⟨Mu, hMu⟩, hL3, hneg, hint, ⟨C, hC⟩⟩ := proposition5_2
  obtain ⟨L, M, hL, hM, hpert⟩ := tbt4_q3_perturb
  obtain ⟨G, hG, hGb⟩ := tbt4_fderiv_chi_bound
  set Mu' := max Mu 0
  have hMu' : ∀ x, ‖u x‖ ≤ Mu' := fun x => (hMu x).trans (le_max_left _ _)
  set C' := max C 0
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set I₁ := ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < 1}, q3 (jac u x)
  have hI : I₁ < 0 := tbt4_I1_neg hneg hint
  set C₂ := 6 * Mu' ^ 2 * G ^ 2
  set A := (L + 16) * C' * (Real.log 4 + 8)
  set B := 64 * C₂ ^ 2 * (L + M + 16 + 2 * K ^ 4)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  set Ct := A + B + 1
  have hCt : 0 < Ct := by positivity
  refine ⟨min 1 ((I₁ / (2 * Ct)) ^ 2), lt_min one_pos (by
    have : I₁ / (2 * Ct) ≠ 0 := div_ne_zero hI.ne (by positivity)
    positivity), fun δ hδ hδ₀ => ?_⟩
  have hδ1 : δ ≤ 1 := (lt_of_lt_of_le hδ₀ (min_le_left _ _)).le
  have hδs : √δ < -I₁ / (2 * Ct) := by
    have h := lt_of_lt_of_le hδ₀ (min_le_right _ _)
    have h' : √δ < √((I₁ / (2 * Ct)) ^ 2) := Real.sqrt_lt_sqrt hδ.le h
    rwa [Real.sqrt_sq_eq_abs, abs_of_neg (div_neg_of_neg_of_pos hI (by positivity)), ← neg_div]
      at h'
  set R := (δ ^ 4)⁻¹
  have hR : 0 < R := by positivity
  have hR1 : 1 ≤ R := one_le_inv_iff₀.mpr ⟨by positivity, pow_le_one₀ hδ.le hδ1⟩
  -- the logarithmic bound of Proposition 5.2 on `|x|² ≤ 2R²`
  have hlog : ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 ≤ 2 * R ^ 2}, frobSq (jac u x) ^ 2 ≤
      C' * Real.log (2 + 2 * R) := by
    refine (tbt4_log_bound hsm hC hR).trans ?_
    have : 0 ≤ Real.log (2 + 2 * R) := Real.log_nonneg (by linarith)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  -- the energy of `u_R`
  have hE := tbt4_energy (Gf := jac u) (Ef := tbt4ER u R) (χf := fun x => tbt4Chi (R⁻¹ • x))
    (C₁ := C' * Real.log (2 + 2 * R)) (C₂ := C₂) (η := δ) (Λ := K / δ)
    hL hM hpert hR hδ.le hδ (tbt_continuous_jac hsm) (tbt4_continuous_ER hsm.continuous R)
    ((tbt4_contDiff_chi.continuous).comp (continuous_const_smul R⁻¹)) hL3
    (fun x => (hneg x).le) hint
    (fun x => Real.smoothTransition.nonneg _) (fun x => Real.smoothTransition.le_one _)
    (fun x hx => tbt4_chi_one (by
      rw [tbt4_sumSq_smul, inv_pow]
      have : (R ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hR1)
      have h0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith))
    (fun x hx => tbt4_supp u hR hx) hlog (fun x => tbt4_frobSq_ER_le hMu' hG hGb hR x)
  have heq : ∫ x, qDeltaLambda δ (K / δ) (jac (tbt4uR u R) x) =
      ∫ x, qDeltaLambda δ (K / δ) (tbt4Chi (R⁻¹ • x) • jac u x + tbt4ER u R x) := by
    simp_rw [tbt4_jac_uR hsm]
  -- the bound tends to `I₁ < 0`
  have hT1 : (L * δ + 16 * δ) * (C' * Real.log (2 + 2 * R)) ≤ A * √δ := by
    have := tbt4_delta_log hδ hδ1
    calc (L * δ + 16 * δ) * (C' * Real.log (2 + 2 * R))
        = (L + 16) * C' * (δ * Real.log (2 + 2 * (δ ^ 4)⁻¹)) := by ring
      _ ≤ (L + 16) * C' * ((Real.log 4 + 8) * √δ) := by gcongr
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
  have hneg' : ∫ x, qDeltaLambda δ (K / δ) (jac (tbt4uR u R) x) < 0 := by
    rw [heq]
    have hs0 : 0 ≤ √δ := Real.sqrt_nonneg δ
    have h1 : (A + B) * √δ ≤ Ct * √δ := by gcongr; linarith
    have h2 : Ct * √δ < Ct * (-I₁ / (2 * Ct)) := mul_lt_mul_of_pos_left hδs hCt
    have h3 : Ct * (-I₁ / (2 * Ct)) = -I₁ / 2 := by field_simp
    linarith
  exact tbt4_not_quasiconvexAt_of_witness (tbt4_continuous_qDeltaLambda δ (K / δ))
    (tbt4_qDeltaLambda_zero δ (K / δ)) hR (tbt4_contDiff_uR hsm R) (fun z hz => tbt4_uR_zero u hR hz)
    hneg'

end Cassese
