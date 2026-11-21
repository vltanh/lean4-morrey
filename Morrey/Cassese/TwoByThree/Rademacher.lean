module

public import Morrey.Cassese.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Probability.Martingale.Basic

/-!
# Rademacher martingales on the canonical space and Burkholder's inequality

The Rademacher martingales `n ↦ Σ_{k<n} ε_k ξ_k` of `Defs` (`mart`, predictable `ξ`) live on the
canonical space `{±1}^N = Fin N → Bool` with the uniform probability `tbt1Mu N`
(`(2^N)⁻¹ • count`). With the filtration `tbt1Filt N` of the sets determined by the first `k`
signs, they are martingales in Mathlib's sense (`tbt1_martingale_mart`), so Burkholder's
inequality (Theorem 2.3, the hypothesis `BurkholderInequality`) applies to them; on this finite
space `L^p` norms are averages (`tbt1_eLpNorm_eq`). The consequence used in Lemma 5.1 (1),
inequality (27), is `tbt1_burkholder_avg`: if `‖ξ_k‖ ≤ ‖ζ_k‖` pointwise then
`E ‖Σ ε_k ξ_k‖^p ≤ (p* − 1)^p E ‖Σ ε_k ζ_k‖^p`.

Helpers are prefixed `tbt1`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Cassese

/-- The σ-algebra of the sets of sign sequences determined by the first `k` signs. -/
@[instance_reducible] def tbt1Sigma (N k : ℕ) : MeasurableSpace (Fin N → Bool) where
  MeasurableSet' s := ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) →
    (ε ∈ s ↔ ε' ∈ s)
  measurableSet_empty := by simp
  measurableSet_compl s hs ε ε' h := by
    simp only [Set.mem_compl_iff]; exact not_congr (hs ε ε' h)
  measurableSet_iUnion f hf ε ε' h := by
    simp only [Set.mem_iUnion]; exact exists_congr fun i => hf i ε ε' h

theorem tbt1_measurableSet_pi {N : ℕ} (s : Set (Fin N → Bool)) : MeasurableSet s :=
  s.toFinite.measurableSet

/-- The filtration of the first `k` signs. -/
def tbt1Filt (N : ℕ) : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (Fin N → Bool)) where
  seq k := tbt1Sigma N k
  mono' _ _ hkk' _ hs ε ε' h := hs ε ε' fun j hj => h j (lt_of_lt_of_le hj hkk')
  le' _ s _ := tbt1_measurableSet_pi s

/-- The uniform probability on `{±1}^N`. -/
noncomputable def tbt1Mu (N : ℕ) : Measure (Fin N → Bool) :=
  ((2 : ℝ≥0∞) ^ N)⁻¹ • Measure.count

theorem tbt1Mu_singleton (N : ℕ) (ε : Fin N → Bool) :
    tbt1Mu N {ε} = ((2 : ℝ≥0∞) ^ N)⁻¹ := by
  simp [tbt1Mu]

instance tbt1Mu_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (tbt1Mu N) := by
  constructor
  simp only [tbt1Mu, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  rw [ENat.card_eq_coe_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  push_cast
  exact ENNReal.inv_mul_cancel (by positivity) (by simp)

section Mart

variable {N : ℕ}

section Module

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The increment `ε_n ξ_n` (`0` for `n ≥ N`). -/
noncomputable def tbt1D (ξ : Fin N → (Fin N → Bool) → H) (n : ℕ) (ε : Fin N → Bool) : H :=
  if h : n < N then coin (ε ⟨n, h⟩) • ξ ⟨n, h⟩ ε else 0

theorem tbt1_mart_succ (ξ : Fin N → (Fin N → Bool) → H) (n : ℕ) (ε : Fin N → Bool) :
    mart ξ (n + 1) ε = mart ξ n ε + tbt1D ξ n ε := by
  simp only [mart, Finset.sum_filter, tbt1D]
  have : ∀ k : Fin N, (if k.val < n + 1 then coin (ε k) • ξ k ε else 0) =
      (if k.val < n then coin (ε k) • ξ k ε else 0) +
        (if k.val = n then coin (ε k) • ξ k ε else 0) := by
    intro k
    by_cases h1 : k.val < n
    · simp [h1, show k.val < n + 1 by omega, show k.val ≠ n by omega]
    · by_cases h2 : k.val = n
      · simp [h2]
      · simp [h1, h2, show ¬ k.val < n + 1 by omega]
  rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb
      rw [ite_eq_right_iff]
      intro hb'
      exact absurd (Fin.ext hb') hb
    · simp
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [ite_eq_right_iff]
    intro hk
    exact absurd (hk ▸ k.isLt) h

/-- `Σ_{k<n} ε_k ξ_k` depends only on the first `n` signs. -/
theorem tbt1_mart_congr {ξ : Fin N → (Fin N → Bool) → H} (hξ : IsPredictable ξ) (n : ℕ)
    {ε ε' : Fin N → Bool} (h : ∀ j : Fin N, j.val < n → ε j = ε' j) : mart ξ n ε = mart ξ n ε' := by
  unfold mart
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k.val < n := (Finset.mem_filter.mp hk).2
  rw [h k hk', hξ k ε ε' fun j hj => h j (lt_trans (Fin.lt_def.mp hj) hk')]

end Module

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem tbt1_norm_D (ξ : Fin N → (Fin N → Bool) → H) (n : ℕ) (ε : Fin N → Bool) :
    ‖tbt1D ξ n ε‖ = if h : n < N then ‖ξ ⟨n, h⟩ ε‖ else 0 := by
  unfold tbt1D
  split_ifs with h
  · rw [norm_smul]
    unfold coin
    split_ifs <;> simp
  · simp

/-- On `{±1}^N`, `∫_s f = 2^{-N} Σ_{ε ∈ s} f ε`. -/
theorem tbt1_setIntegral_eq [CompleteSpace H] (f : (Fin N → Bool) → H) (s : Set (Fin N → Bool)) :
    ∫ ε in s, f ε ∂tbt1Mu N = ((2 : ℝ) ^ N)⁻¹ • ∑ ε, s.indicator f ε := by
  rw [← integral_indicator (tbt1_measurableSet_pi s), integral_fintype Integrable.of_finite,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 1
  simp [Measure.real, tbt1Mu_singleton]

/-- The increments of a Rademacher martingale have mean zero on every set determined by the
earlier signs: flipping the sign `ε_n` is a measure-preserving involution that fixes the set and
`ξ_n`, and changes the sign of `ε_n ξ_n`. -/
theorem tbt1_setIntegral_D [CompleteSpace H] {ξ : Fin N → (Fin N → Bool) → H} (hξ : IsPredictable ξ)
    (n : ℕ) {s : Set (Fin N → Bool)} (hs : MeasurableSet[tbt1Sigma N n] s) :
    ∫ ε in s, tbt1D ξ n ε ∂tbt1Mu N = 0 := by
  rw [tbt1_setIntegral_eq]
  by_cases hn : n < N
  · set i : Fin N := ⟨n, hn⟩
    set fl : (Fin N → Bool) → (Fin N → Bool) := fun ε => Function.update ε i (!ε i)
    have hfl : Function.Involutive fl := by
      intro ε
      funext j
      by_cases hj : j = i
      · subst hj; simp [fl]
      · simp [fl, Function.update_of_ne hj]
    have hagree : ∀ ε (j : Fin N), j.val < n → fl ε j = ε j := by
      intro ε j hj
      have : j ≠ i := fun h => by rw [h] at hj; exact lt_irrefl _ hj
      simp [fl, Function.update_of_ne this]
    have hF : ∀ ε, s.indicator (tbt1D ξ n) (fl ε) = -s.indicator (tbt1D ξ n) ε := by
      intro ε
      have hmem : fl ε ∈ s ↔ ε ∈ s := (hs ε (fl ε) fun j hj => (hagree ε j hj).symm).symm
      by_cases he : ε ∈ s
      · rw [Set.indicator_of_mem (hmem.mpr he), Set.indicator_of_mem he]
        simp only [tbt1D, hn, dite_true]
        have hξe : ξ i (fl ε) = ξ i ε := hξ i (fl ε) ε fun j hj => hagree ε j hj
        have hc : coin (fl ε i) = -coin (ε i) := by
          simp only [fl, Function.update_self]
          cases ε i <;> simp [coin]
        rw [hξe, hc, neg_smul]
      · rw [Set.indicator_of_notMem (fun h => he (hmem.mp h)), Set.indicator_of_notMem he, neg_zero]
    have hsum : ∑ ε, s.indicator (tbt1D ξ n) ε = -∑ ε, s.indicator (tbt1D ξ n) ε := by
      rw [← Finset.sum_neg_distrib]
      conv_lhs => rw [← Equiv.sum_comp hfl.toPerm]
      exact Finset.sum_congr rfl fun ε _ => hF ε
    have h2 : (2 : ℝ) • ∑ ε, s.indicator (tbt1D ξ n) ε = 0 := by
      rw [two_smul]; nth_rewrite 2 [hsum]; exact add_neg_cancel _
    rw [smul_eq_zero.mp h2 |>.resolve_left two_ne_zero, smul_zero]
  · have : tbt1D ξ n = fun _ => 0 := funext fun ε => by simp [tbt1D, hn]
    simp [this]

omit [NormedSpace ℝ H] in
/-- On `{±1}^N`, `‖f‖_{L^p} = (E ‖f‖^p)^{1/p}`. -/
theorem tbt1_eLpNorm_eq (f : (Fin N → Bool) → H) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) (tbt1Mu N) =
      ENNReal.ofReal ((avg fun ε => ‖f ε‖ ^ p) ^ (1 / p)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    Integrable.of_finite.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le, lintegral_fintype]
  have hN : (0 : ℝ) < 2 ^ N := by positivity
  have h : ∑ x, ‖f x‖ₑ ^ p * tbt1Mu N {x} = ENNReal.ofReal (avg fun ε => ‖f ε‖ ^ p) := by
    simp only [tbt1Mu_singleton, avg, div_eq_mul_inv]
    rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun _ _ => by positivity),
      ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ENNReal.ofReal_inv_of_pos hN]
    congr
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  rw [h, ENNReal.ofReal_rpow_of_nonneg (by
    unfold avg; exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) hN.le)
    (by positivity)]

variable [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- A Rademacher martingale with predictable `ξ` is a martingale for the filtration of the signs
and the uniform probability. -/
theorem tbt1_martingale_mart {ξ : Fin N → (Fin N → Bool) → H} (hξ : IsPredictable ξ) :
    Martingale (fun n => mart ξ n) (tbt1Filt N) (tbt1Mu N) := by
  refine martingale_of_setIntegral_eq_succ (fun n => ?_) (fun n => Integrable.of_finite)
    (fun n s hs => ?_)
  · have hm : Measurable[tbt1Sigma N n] (mart ξ n) := fun t _ ε ε' h => by
      simp only [Set.mem_preimage, tbt1_mart_congr hξ n h]
    exact hm.stronglyMeasurable
  · have : (fun ε => mart ξ (n + 1) ε) = fun ε => mart ξ n ε + tbt1D ξ n ε :=
      funext fun ε => tbt1_mart_succ ξ n ε
    rw [this, integral_add Integrable.of_finite.integrableOn Integrable.of_finite.integrableOn,
      tbt1_setIntegral_D hξ n hs, add_zero]

/-- **Burkholder's inequality (27) on `{±1}^N`**: if `‖ξ_k‖ ≤ ‖ζ_k‖` pointwise, for predictable
`ξ`, `ζ` with values in a separable Hilbert space, then
`E ‖Σ_{k<N} ε_k ξ_k‖^p ≤ (p* − 1)^p E ‖Σ_{k<N} ε_k ζ_k‖^p`. From `BurkholderInequality`
(differential subordination `‖dX_n‖ ≤ ‖dY_n‖`) on the canonical space. -/
theorem tbt1_burkholder_avg (hB : BurkholderInequality) {N : ℕ} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {ξ ζ : Fin N → (Fin N → Bool) → E} (hξ : IsPredictable ξ)
    (hζ : IsPredictable ζ) (hle : ∀ k ε, ‖ξ k ε‖ ≤ ‖ζ k ε‖) {p : ℝ} (hp : 1 < p) :
    avg (fun ε => ‖mart ξ N ε‖ ^ p) ≤ (pStar p - 1) ^ p * avg (fun ε => ‖mart ζ N ε‖ ^ p) := by
  have key := hB (Fin N → Bool) MeasurableSpace.pi (tbt1Mu N) (tbt1Filt N)
    E (fun n => mart ξ n) (fun n => mart ζ n) p hp
    (tbt1_martingale_mart hξ) (tbt1_martingale_mart hζ) (fun ε => by simp [mart])
    (fun ε => by simp [mart])
    (fun n => Filter.Eventually.of_forall fun ε => by
      simp only [tbt1_mart_succ, add_sub_cancel_left, tbt1_norm_D]
      split_ifs <;> simp [hle]) N
  have hp0 : 0 < p := by linarith
  rw [tbt1_eLpNorm_eq _ hp0, tbt1_eLpNorm_eq _ hp0] at key
  have hpstar : 0 ≤ pStar p - 1 := by
    have : p ≤ pStar p := le_max_left _ _
    linarith
  have ha : 0 ≤ avg (fun ε => ‖mart ξ N ε‖ ^ p) := by
    unfold avg; exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  have hb : 0 ≤ avg (fun ε => ‖mart ζ N ε‖ ^ p) := by
    unfold avg; exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  rw [← ENNReal.ofReal_mul hpstar, ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  have := Real.rpow_le_rpow (by positivity) key hp0.le
  rw [Real.mul_rpow hpstar (by positivity), ← Real.rpow_mul ha, ← Real.rpow_mul hb,
    one_div_mul_cancel hp0.ne', Real.rpow_one, Real.rpow_one] at this
  exact this

end Mart

end Cassese
