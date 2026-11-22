module

public import Morrey.Cassese.Defs
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.UniformOn

/-!
# Rademacher martingales on the canonical space are martingales

The Rademacher (Paley–Walsh) martingales `k ↦ Σ_{j<k} ε_j ξ_j` of `Defs` (`mart`, predictable `ξ`)
live on the space `Fin n → Bool` of `n` signs with the uniform probability
(`ProbabilityTheory.uniformOn Set.univ`). With the natural filtration `ℱ_k = σ (ε₀, …, ε_{k−1})`
(`rad_filtration`) they are martingales in Mathlib's sense (`rad_martingale`), so that results on
Mathlib's martingales, Burkholder's inequalities among them, apply to them; and on this finite
space `L^p` norms are averages (`rad_eLpNorm_uniform`).

Used by Section 7 (`FourByTwo.lean`, Burkholder's inequality for Proposition 7.1) and by Section 6
(`Square/Korn.lean`, Burkholder's square function inequality in `S_2^{d×d}`). The sign-space
helpers that the other sections share are here too: averages over the signs (`rad_avg_add`, …),
the flip of one sign (`rad_flip`), and `M_0 = 0`, `M_N = Σ_k ε_k ξ_k`, and the dependence of `M_k`
on the first `k` signs only (`rad_mart_zero`, `rad_mart_top`, `rad_mart_congr`). Helpers are
prefixed `rad_`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Cassese

/-- The truncation `ε ↦ (ε₀, …, ε_{k−1}, false, …, false)`. -/
def rad_trunc {n : ℕ} (k : ℕ) (ε : Fin n → Bool) : Fin n → Bool :=
  fun j => if j.val < k then ε j else false

theorem rad_trunc_trunc {n : ℕ} {k k' : ℕ} (h : k ≤ k') (ε : Fin n → Bool) :
    rad_trunc k (rad_trunc k' ε) = rad_trunc k ε := by
  funext j
  simp only [rad_trunc]
  split_ifs <;> first | rfl | omega

/-- The natural filtration of the signs: `ℱ_k = σ (ε₀, …, ε_{k−1})`. -/
noncomputable def rad_filtration (n : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → Bool)) where
  seq k := MeasurableSpace.comap (rad_trunc k) inferInstance
  mono' k k' h := by
    show MeasurableSpace.comap (rad_trunc k) _ ≤ MeasurableSpace.comap (rad_trunc k') _
    rw [show (rad_trunc k : (Fin n → Bool) → (Fin n → Bool)) =
        rad_trunc k ∘ rad_trunc k' from
        funext fun ε => (rad_trunc_trunc h ε).symm, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono fun s _ => MeasurableSet.of_discrete
  le' _ := fun _ _ => MeasurableSet.of_discrete

theorem rad_mart_trunc {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin n → (Fin n → Bool) → E) (hξ : IsPredictable ξ) (k : ℕ) (ε : Fin n → Bool) :
    mart ξ k (rad_trunc k ε) = mart ξ k ε := by
  unfold mart
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rw [hξ j (rad_trunc k ε) ε fun i hi => by
    have : i.val < k := lt_trans (Fin.lt_def.mp hi) hj
    simp [rad_trunc, this]]
  simp [rad_trunc, hj]

theorem rad_mart_succ {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin n → (Fin n → Bool) → E) (k : ℕ) (ε : Fin n → Bool) :
    mart ξ (k + 1) ε = mart ξ k ε + if h : k < n then coin (ε ⟨k, h⟩) • ξ ⟨k, h⟩ ε else 0 := by
  unfold mart
  split_ifs with h
  · rw [show Finset.univ.filter (fun j : Fin n => j.val < k + 1) =
        insert ⟨k, h⟩ (Finset.univ.filter (fun j : Fin n => j.val < k)) from ?_,
      Finset.sum_insert (by simp)]
    · abel
    · ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
  · rw [add_zero]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem rad_mart_zero {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin n → (Fin n → Bool) → E) (ε : Fin n → Bool) : mart ξ 0 ε = 0 := by
  simp [mart]

theorem rad_mart_top {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin n → (Fin n → Bool) → E) (ε : Fin n → Bool) :
    mart ξ n ε = ∑ k, coin (ε k) • ξ k ε := by
  simp only [mart]
  rw [Finset.filter_true_of_mem fun k _ => k.isLt]

/-- `M_k = Σ_{j<k} ε_j ξ_j` depends only on the first `k` signs. -/
theorem rad_mart_congr {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ξ : Fin n → (Fin n → Bool) → E} (hξ : IsPredictable ξ) (k : ℕ) {ε ε' : Fin n → Bool}
    (h : ∀ j : Fin n, j.val < k → ε j = ε' j) : mart ξ k ε = mart ξ k ε' := by
  unfold mart
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j.val < k := (Finset.mem_filter.mp hj).2
  rw [h j hj', hξ j ε ε' fun i hi => h i (lt_trans (Fin.lt_def.mp hi) hj')]

/-! ### Averages over the signs, and the flip of one sign -/

theorem rad_avg_add {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    avg (fun ε => f ε + g ε) = avg f + avg g := by
  simp only [avg, Finset.sum_add_distrib, add_div]

theorem rad_avg_sub {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    avg (fun ε => f ε - g ε) = avg f - avg g := by
  simp only [avg, Finset.sum_sub_distrib, sub_div]

theorem rad_avg_mul_left {n : ℕ} (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    avg (fun ε => c * f ε) = c * avg f := by
  simp only [avg, ← Finset.mul_sum, mul_div_assoc]

theorem rad_avg_mono {n : ℕ} {f g : (Fin n → Bool) → ℝ} (h : ∀ ε, f ε ≤ g ε) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun ε _ => h ε) (by positivity)

theorem rad_avg_nonneg {n : ℕ} {f : (Fin n → Bool) → ℝ} (h : ∀ ε, 0 ≤ f ε) : 0 ≤ avg f :=
  div_nonneg (Finset.sum_nonneg fun ε _ => h ε) (by positivity)

/-- Flipping the sign `ε_k`. -/
def rad_flip {n : ℕ} (k : Fin n) (ε : Fin n → Bool) : Fin n → Bool :=
  Function.update ε k (!ε k)

theorem rad_flip_involutive {n : ℕ} (k : Fin n) : Function.Involutive (rad_flip k) := by
  intro ε
  funext j
  by_cases h : j = k
  · subst h; simp [rad_flip]
  · simp [rad_flip, Function.update_of_ne h]

theorem rad_flip_apply_self {n : ℕ} (k : Fin n) (ε : Fin n → Bool) : rad_flip k ε k = !ε k := by
  simp [rad_flip]

theorem rad_flip_apply_ne {n : ℕ} {k j : Fin n} (h : j ≠ k) (ε : Fin n → Bool) :
    rad_flip k ε j = ε j :=
  Function.update_of_ne h _ _

theorem rad_coin_not (b : Bool) : coin (!b) = -coin b := by
  cases b <;> simp [coin]

theorem rad_uniformOn_singleton {n : ℕ} (ε : Fin n → Bool) :
    (ProbabilityTheory.uniformOn (Set.univ : Set (Fin n → Bool))).real {ε} = 1 / 2 ^ n := by
  rw [Measure.real, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
  simp [Fintype.card_bool]

/-- A Rademacher (Paley–Walsh) martingale `k ↦ Σ_{j<k} ε_j ξ_j` with predictable `ξ` is a
martingale for the natural filtration of the signs and the uniform probability. -/
theorem rad_martingale {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ξ : Fin n → (Fin n → Bool) → E) (hξ : IsPredictable ξ) :
    Martingale (fun k => mart ξ k) (rad_filtration n)
      (ProbabilityTheory.uniformOn Set.univ) := by
  refine martingale_of_setIntegral_eq_succ (fun k => ?_) (fun k => Integrable.of_finite)
    (fun k s hs => ?_)
  · have : (mart ξ k) = (mart ξ k) ∘ rad_trunc k :=
      funext fun ε => (rad_mart_trunc ξ hξ k ε).symm
    show StronglyMeasurable[MeasurableSpace.comap (rad_trunc k) inferInstance] (mart ξ k)
    rw [this]
    exact StronglyMeasurable.of_discrete.comp_measurable (comap_measurable _)
  · obtain ⟨t, -, rfl⟩ := hs
    simp_rw [rad_mart_succ ξ k]
    rw [integral_add Integrable.of_finite.integrableOn Integrable.of_finite.integrableOn,
      left_eq_add]
    split_ifs with h
    swap
    · simp
    rw [← integral_indicator MeasurableSet.of_discrete, integral_fintype Integrable.of_finite]
    simp_rw [rad_uniformOn_singleton]
    rw [← Finset.smul_sum]
    -- the flip of the `k`-th sign
    set σ : (Fin n → Bool) ≃ (Fin n → Bool) :=
      { toFun := fun ε => Function.update ε ⟨k, h⟩ (!ε ⟨k, h⟩)
        invFun := fun ε => Function.update ε ⟨k, h⟩ (!ε ⟨k, h⟩)
        left_inv := fun ε => by funext j; by_cases hj : j = ⟨k, h⟩ <;> simp [hj]
        right_inv := fun ε => by funext j; by_cases hj : j = ⟨k, h⟩ <;> simp [hj] } with hσ
    set g := (rad_trunc k ⁻¹' t).indicator
      (fun ε => coin (ε ⟨k, h⟩) • ξ ⟨k, h⟩ ε) with hg
    have hflip : ∀ ε, g (σ ε) = -g ε := by
      intro ε
      have htr : rad_trunc k (σ ε) = rad_trunc k ε := by
        funext j
        simp only [rad_trunc, hσ, Equiv.coe_fn_mk]
        split_ifs with hj
        · rw [Function.update_of_ne]
          intro hjk
          rw [hjk] at hj
          exact lt_irrefl _ hj
        · rfl
      have hξσ : ξ ⟨k, h⟩ (σ ε) = ξ ⟨k, h⟩ ε := hξ _ _ _ fun i hi => by
        simp only [hσ, Equiv.coe_fn_mk]
        exact Function.update_of_ne (ne_of_lt hi) _ _
      have hmem : σ ε ∈ rad_trunc k ⁻¹' t ↔ ε ∈ rad_trunc k ⁻¹' t := by
        simp only [Set.mem_preimage, htr]
      by_cases hε : ε ∈ rad_trunc k ⁻¹' t
      · rw [hg, Set.indicator_of_mem (hmem.mpr hε), Set.indicator_of_mem hε, hξσ]
        simp [hσ, rad_coin_not, neg_smul]
      · rw [hg, Set.indicator_of_notMem (fun h' => hε (hmem.mp h')),
          Set.indicator_of_notMem hε, neg_zero]
    have hsum : ∑ ε, g ε = -∑ ε, g ε := by
      conv_lhs => rw [← Equiv.sum_comp σ g]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun ε _ => hflip ε
    have h2 : (2 : ℝ) • ∑ ε, g ε = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hsum]
      exact add_neg_cancel _
    rw [smul_eq_zero.mp h2 |>.resolve_left two_ne_zero, smul_zero]

/-- On the signs with the uniform probability,
`‖f‖_{L^p} = (2^{−n} Σ_ε ‖f (ε)‖^p)^{1/p}`. -/
theorem rad_eLpNorm_uniform {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : (Fin n → Bool) → E) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) =
      ENNReal.ofReal (((∑ ε, ‖f ε‖ ^ p) / 2 ^ n) ^ (1 / p)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    AEStronglyMeasurable.of_discrete, ENNReal.toReal_ofReal hp.le, lintegral_fintype]
  have hμ : ∀ ε : Fin n → Bool,
      (ProbabilityTheory.uniformOn (Set.univ : Set (Fin n → Bool))) {ε} =
        ENNReal.ofReal (1 / 2 ^ n) := fun ε => by
    rw [← rad_uniformOn_singleton ε, ofReal_measureReal]
  have hsum : 0 ≤ (∑ ε, ‖f ε‖ ^ p) / 2 ^ n :=
    div_nonneg (Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  rw [← ENNReal.ofReal_rpow_of_nonneg hsum (by positivity)]
  congr 1
  have hterm : ∀ ε, ‖f ε‖ₑ ^ p * (ProbabilityTheory.uniformOn Set.univ) {ε} =
      ENNReal.ofReal (‖f ε‖ ^ p * (1 / 2 ^ n)) := by
    intro ε
    rw [hμ, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [Finset.sum_congr rfl fun ε _ => hterm ε, ← ENNReal.ofReal_sum_of_nonneg fun ε _ =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by positivity), ← Finset.sum_mul]
  congr 1
  ring

end Cassese
