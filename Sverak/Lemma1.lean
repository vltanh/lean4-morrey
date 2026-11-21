module

public import Sverak.Cube
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Šverák 1992, Lemma 1: quasiconvexity tested with periodic maps

V. Šverák, *Rank-one convexity does not imply quasiconvexity*, Proc. Roy. Soc. Edinburgh 120A
(1992), 185–189, Section 2, Lemma 1. Quasiconvexity is taken on the unit cube `Ω = (0, 1)^n`, the
domain of the paper's proof ("Since `u_ε` is smooth and compactly supported in `(0, 1)^n`"). The
paper's class does not depend on `Ω`, by [3] and [10] of the paper, which is not formalized here.

* `lemma1_limit`: the limit in the proof: for a continuous `f`, a smooth periodic `u` and every
  `A`, the maps `u_ε (x) = ε² η_ε (x) u (x / ε²)`, smooth with compact support in `(0, 1)^n`,
  have `∫_{(0,1)^n} f (A + ∇u_ε) → ∫_{(0,1)^n} f (A + ∇u)` as `ε → 0⁺`.
* `lemma1`: the equivalence. The "only if" part is the paper's: quasiconvexity gives (2),
  `f (A) ≤ ∫ f (A + ∇u_ε)` for `0 < ε < 1/2`, and the limit gives `f (A) ≤ ∫ f (A + ∇u)`.
* `lemma1_witness`: the "only if" part in contrapositive form, from the same limit: a periodic
  map with `∫ f (A + ∇u) < f (A)` gives a compactly supported one, one of the `u_ε`.

Helpers (prefix `l1_`):

* the cutoff `η_ε` (`l1_eta`, for `ε = 1/K`): a product of one-dimensional profiles built from
  `Real.smoothTransition`, equal to `1` on `[ε, 1 - ε]^n`, vanishing off `(ε/2, 1 - ε/2)^n`, with
  `|D η_ε| ≤ 4 n B / ε` (`l1_eta_fderiv_bound`), where the paper asks `|D η_ε| ≤ 2 / ε`; the
  paper's constant 2 is not used, any bound `C / ε` serves;
* the periodic average identity `∫_{(0,1)^n} G (N x) dx = ∫_{(0,1)^n} G` for an integer `N ≥ 1`
  (`l1_setIntegral_comp_nsmul`), and the averaging limit `∫_{(0,1)^n} G (N x) dx → ∫_{(0,1)^n} G`
  as `N → ∞` through the reals (`l1_tendsto_setIntegral_comp_smul`);
* the test maps `u_ε` (`l1_testMap`) and their gradients;
* the periodic extension `x ↦ φ (fract x)` (`l1_perExt`) for the "if" part.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Pointwise

namespace Sverak

/-- `u : ℝ^n → ℝ^m` is periodic with respect to `ℤ^n`. -/
def IsPeriodic {m n : ℕ} (u : (Fin n → ℝ) → Fin m → ℝ) : Prop :=
  ∀ (x : Fin n → ℝ) (z : Fin n → ℤ), u (x + fun i => (z i : ℝ)) = u x

/-! ### The cutoff `η_ε` -/

/-- The derivative of `Real.smoothTransition` is bounded (it is continuous and vanishes off
`[0, 1]`). -/
theorem l1_deriv_smoothTransition_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv Real.smoothTransition t| ≤ B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1)) fun t ht => ?_
    rcases not_and_or.1 ht with h | h
    · push Not at h
      have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h] with s hs
        exact Real.smoothTransition.zero_of_nonpos hs.le
      rw [this.deriv_eq]; simp
    · push Not at h
      have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds h] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [this.deriv_eq]; simp
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

/-- The one-dimensional profile of the cutoff, for `ε = 1/K`. -/
noncomputable def l1_chi (K t : ℝ) : ℝ :=
  Real.smoothTransition (2 * K * t - 1) * Real.smoothTransition (2 * K * (1 - t) - 1)

theorem l1_chi_nonneg (K t : ℝ) : 0 ≤ l1_chi K t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem l1_chi_le_one (K t : ℝ) : l1_chi K t ≤ 1 := by
  unfold l1_chi
  nlinarith [Real.smoothTransition.le_one (2 * K * t - 1),
    Real.smoothTransition.nonneg (2 * K * t - 1),
    Real.smoothTransition.le_one (2 * K * (1 - t) - 1),
    Real.smoothTransition.nonneg (2 * K * (1 - t) - 1)]

theorem l1_chi_contDiff (K : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (l1_chi K) := by
  unfold l1_chi
  have h := Real.smoothTransition.contDiff (n := ⊤)
  exact (h.comp (by fun_prop)).mul (h.comp (by fun_prop))

/-- `χ = 1` on `[1/K, 1 - 1/K]`. -/
theorem l1_chi_eq_one {K t : ℝ} (hK : 0 < K) (h1 : 1 / K ≤ t) (h2 : t ≤ 1 - 1 / K) :
    l1_chi K t = 1 := by
  unfold l1_chi
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, one_mul]
  · have : 1 ≤ K * (1 - t) := by
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hK] at h2
      nlinarith
    linarith
  · have : 1 ≤ K * t := by rwa [div_le_iff₀ hK, mul_comm] at h1
    linarith

/-- `χ = 0` off `(1/(2K), 1 - 1/(2K))`. -/
theorem l1_chi_eq_zero {K t : ℝ} (hK : 0 < K) (h : t ≤ 1 / (2 * K) ∨ 1 - 1 / (2 * K) ≤ t) :
    l1_chi K t = 0 := by
  unfold l1_chi
  rcases h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  · rw [Real.smoothTransition.zero_of_nonpos (x := 2 * K * (1 - t) - 1), mul_zero]
    have : 1 - t ≤ 1 / (2 * K) := by linarith
    rw [le_div_iff₀ (by positivity)] at this
    linarith

theorem l1_chi_hasDerivAt (K t : ℝ) :
    HasDerivAt (l1_chi K)
      (deriv Real.smoothTransition (2 * K * t - 1) * (2 * K) *
          Real.smoothTransition (2 * K * (1 - t) - 1) +
        Real.smoothTransition (2 * K * t - 1) *
          (deriv Real.smoothTransition (2 * K * (1 - t) - 1) * (-(2 * K)))) t := by
  have hd : ∀ s, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition s) s := fun s =>
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero s).hasDerivAt
  have h1 : HasDerivAt (fun t => 2 * K * t - 1) (2 * K) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * K)).sub_const 1
  have h2 : HasDerivAt (fun t => 2 * K * (1 - t) - 1) (-(2 * K)) t := by
    simpa using (((hasDerivAt_id t).const_sub 1).const_mul (2 * K)).sub_const 1
  exact ((hd _).comp t h1).mul ((hd _).comp t h2)

/-- `|χ'| ≤ 4 K B = 4 B / ε`, where `B` bounds the derivative of the smooth transition. -/
theorem l1_chi_deriv_bound {K B : ℝ} (hK : 0 < K)
    (hB : ∀ s, |deriv Real.smoothTransition s| ≤ B) (t : ℝ) :
    |deriv (l1_chi K) t| ≤ 4 * K * B := by
  rw [(l1_chi_hasDerivAt K t).deriv]
  set p := deriv Real.smoothTransition (2 * K * t - 1)
  set q := deriv Real.smoothTransition (2 * K * (1 - t) - 1)
  set b := Real.smoothTransition (2 * K * (1 - t) - 1)
  set c := Real.smoothTransition (2 * K * t - 1)
  have hb0 : 0 ≤ b := Real.smoothTransition.nonneg _
  have hb1 : b ≤ 1 := Real.smoothTransition.le_one _
  have hc0 : 0 ≤ c := Real.smoothTransition.nonneg _
  have hc1 : c ≤ 1 := Real.smoothTransition.le_one _
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have e1 : |p * b| ≤ B := by
    rw [abs_mul, abs_of_nonneg hb0]
    calc |p| * b ≤ B * 1 := mul_le_mul (hB _) hb1 hb0 hB0
      _ = B := mul_one B
  have e2 : |c * q| ≤ B := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |q| ≤ 1 * B := mul_le_mul hc1 (hB _) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  rw [show p * (2 * K) * b + c * (q * -(2 * K)) = 2 * K * (p * b) - 2 * K * (c * q) by ring]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul (2 * K) (p * b), abs_mul (2 * K) (c * q), abs_of_pos (by positivity : (0:ℝ) < 2 * K)]
  nlinarith

/-- The cutoff `η_ε` for `ε = 1/K`: `η_ε (x) = ∏ᵢ χ (xᵢ)`. It is smooth, takes values in `[0, 1]`,
equals `1` on `[ε, 1 - ε]^n` and vanishes off `(ε/2, 1 - ε/2)^n`, as the paper asks. A note on the
construction: its gradient satisfies `|D η_ε| ≤ 4 n B / ε` (`l1_eta_fderiv_bound`), with
`B = sup |smoothTransition'|`, where the paper asks `|D η_ε| ≤ 2 / ε`. The paper's constant 2 is
not used; any bound `C / ε` serves, since the proof only needs `ε² |D η_ε|` to be bounded. -/
noncomputable def l1_eta (n : ℕ) (K : ℝ) (x : Fin n → ℝ) : ℝ := ∏ i, l1_chi K (x i)

theorem l1_eta_contDiff (n : ℕ) (K : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (l1_eta n K) := by
  unfold l1_eta
  exact contDiff_prod fun i _ => (l1_chi_contDiff K).comp (contDiff_apply ℝ (fun _ : Fin n => ℝ) i)

theorem l1_eta_nonneg (n : ℕ) (K : ℝ) (x : Fin n → ℝ) : 0 ≤ l1_eta n K x :=
  Finset.prod_nonneg fun i _ => l1_chi_nonneg K (x i)

theorem l1_eta_le_one (n : ℕ) (K : ℝ) (x : Fin n → ℝ) : l1_eta n K x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => l1_chi_nonneg K (x i)) fun i _ => l1_chi_le_one K (x i)

/-- `η_ε = 1` on `[ε, 1 - ε]^n`. -/
theorem l1_eta_eq_one {n : ℕ} {K : ℝ} (hK : 0 < K) {x : Fin n → ℝ}
    (hx : ∀ i, 1 / K ≤ x i ∧ x i ≤ 1 - 1 / K) : l1_eta n K x = 1 :=
  Finset.prod_eq_one fun i _ => l1_chi_eq_one hK (hx i).1 (hx i).2

/-- `η_ε` vanishes off `(ε/2, 1 - ε/2)^n`, a neighbourhood of the boundary of `[0, 1]^n`. -/
theorem l1_eta_eq_zero {n : ℕ} {K : ℝ} (hK : 0 < K) {x : Fin n → ℝ}
    (hx : ¬ ∀ i, 1 / (2 * K) < x i ∧ x i < 1 - 1 / (2 * K)) : l1_eta n K x = 0 := by
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  refine Finset.prod_eq_zero (Finset.mem_univ i) (l1_chi_eq_zero hK ?_)
  by_cases h : 1 / (2 * K) < x i
  · exact Or.inr (hi h)
  · exact Or.inl (not_lt.1 h)

/-- The gradient bound `|D η_ε| ≤ 4 n B / ε` for `ε = 1/K`, with `B` a bound for the derivative of
`Real.smoothTransition`. The paper asks `|D η_ε| ≤ 2 / ε`; the paper's constant 2 is not used, any
bound `C / ε` serves (only the boundedness of `ε² |D η_ε|` enters, in
`l1_fderiv_testMap_bound`). -/
theorem l1_eta_fderiv_bound {n : ℕ} {K B : ℝ} (hK : 0 < K)
    (hB : ∀ s, |deriv Real.smoothTransition s| ≤ B) (x : Fin n → ℝ) :
    ‖fderiv ℝ (l1_eta n K) x‖ ≤ n * (4 * K * B) := by
  classical
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasFDerivAt (fun y : Fin n → ℝ => l1_chi K (y i))
      (deriv (l1_chi K) (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) x :=
    fun i _ => by
      have h1 : HasDerivAt (l1_chi K) (deriv (l1_chi K) (x i)) ((fun y : Fin n → ℝ => y i) x) :=
        (l1_chi_hasDerivAt K (x i)).differentiableAt.hasDerivAt
      have h2 : HasFDerivAt (fun y : Fin n → ℝ => y i)
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) x :=
        hasFDerivAt_apply i x
      exact h1.comp_hasFDerivAt x h2
  have hd := HasFDerivAt.finsetProd hg
  rw [show l1_eta n K = (∏ i ∈ Finset.univ, (fun y : Fin n → ℝ => l1_chi K (y i)) ·) from rfl,
    hd.fderiv]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖(∏ j ∈ Finset.univ.erase i, l1_chi K (x j)) •
        (deriv (l1_chi K) (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)‖
      ≤ ∑ _i : Fin n, 4 * K * B := Finset.sum_le_sum fun i _ => ?_
    _ = n * (4 * K * B) := by simp
  have hproj : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    simpa using norm_le_pi_norm y i
  have hc : ‖∏ j ∈ Finset.univ.erase i, l1_chi K (x j)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun j _ => l1_chi_nonneg K (x j))]
    exact Finset.prod_le_one₀ (fun j _ => l1_chi_nonneg K (x j)) fun j _ => l1_chi_le_one K (x j)
  have hd : ‖deriv (l1_chi K) (x i)‖ ≤ 4 * K * B := l1_chi_deriv_bound hK hB (x i)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [norm_smul, norm_smul]
  calc _ ≤ 1 * (4 * K * B * 1) := by gcongr
    _ = 4 * K * B := by ring

/-! ### Periodic functions -/

/-- A continuous `ℤ^n`-periodic map is bounded: it takes all its values on `[0, 1]^n`. -/
theorem l1_periodic_bounded {n : ℕ} {E : Type*} [NormedAddCommGroup E] {F : (Fin n → ℝ) → E}
    (hF : Continuous F) (hper : ∀ x (z : Fin n → ℤ), F (x + fun i => (z i : ℝ)) = F x) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖F x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ =>
    isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : (x + fun i => ((-⌊x i⌋ : ℤ) : ℝ)) ∈ Set.pi Set.univ fun _ => Set.Icc (0:ℝ) 1 := by
    intro i _
    simp only [Pi.add_apply, Int.cast_neg]
    constructor
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  rw [← hper x (fun i => -⌊x i⌋)]
  exact (hC _ hx).trans (le_max_left _ _)

/-- The open unit cube and the half-open one `[0, 1)^n` differ by a null set. -/
theorem l1_setIntegral_unitCube_eq_Ico {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    ∫ x in unitCube n, g x = ∫ x in Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1), g x := by
  apply setIntegral_congr_set
  have h1 := Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin n => (volume : Measure ℝ))
    (f := fun _ => (0:ℝ)) (g := fun _ => 1)
  have h2 := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin n => (volume : Measure ℝ))
    (f := fun _ => (0:ℝ)) (g := fun _ => 1)
  exact h1.trans h2.symm

/-- The unit cell `z + [0, 1)^n`. -/
def l1_cell {n : ℕ} (z : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun i => Set.Ico (z i) (z i + 1)

/-- By periodicity and translation invariance, all integer cells give the same integral. -/
theorem l1_setIntegral_cell {n : ℕ} {G : (Fin n → ℝ) → ℝ}
    (hper : ∀ x (z : Fin n → ℤ), G (x + fun i => (z i : ℝ)) = G x) (z : Fin n → ℤ) :
    ∫ x in l1_cell (fun i => (z i : ℝ)), G x = ∫ x in l1_cell 0, G x := by
  have h := (measurePreserving_add_right (volume : Measure (Fin n → ℝ))
    (fun i => (z i : ℝ))).setIntegral_preimage_emb (measurableEmbedding_addRight _) G
    (l1_cell (fun i => (z i : ℝ)))
  have hpre : (fun x => x + fun i => (z i : ℝ)) ⁻¹' l1_cell (fun i => (z i : ℝ)) = l1_cell 0 := by
    ext x
    simp only [l1_cell, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
      Pi.add_apply, Pi.zero_apply, zero_add]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [← h, hpre]
  exact setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    fun x _ => hper x z

/-- The periodic average identity: for a continuous `ℤ^n`-periodic `G` and an integer `N ≥ 1`,
`∫_{(0,1)^n} G (N x) dx = ∫_{(0,1)^n} G`. Change variables `y = N x`, then cut `[0, N)^n` into
`N^n` unit cells. -/
theorem l1_setIntegral_comp_nsmul {n : ℕ} {G : (Fin n → ℝ) → ℝ} (hG : Continuous G)
    (hper : ∀ x (z : Fin n → ℤ), G (x + fun i => (z i : ℝ)) = G x) {N : ℕ} (hN : 0 < N) :
    ∫ x in unitCube n, G ((N : ℝ) • x) = ∫ x in unitCube n, G x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [l1_setIntegral_unitCube_eq_Ico, l1_setIntegral_unitCube_eq_Ico,
    Measure.setIntegral_comp_smul_of_pos volume G _ hN']
  have hQ : Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1) = l1_cell (0 : Fin n → ℝ) := by
    simp [l1_cell]
  have hcells : (N : ℝ) • Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1) =
      ⋃ z : Fin n → Fin N, l1_cell (fun i => (((z i : ℕ) : ℤ) : ℝ)) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hN'.ne', Set.mem_iUnion]
    simp only [l1_cell, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico, Pi.smul_apply,
      smul_eq_mul, Int.cast_natCast]
    constructor
    · intro h
      have h0 : ∀ i, 0 ≤ y i := fun i => by
        have := mul_nonneg hN'.le (h i).1
        rwa [mul_inv_cancel_left₀ hN'.ne'] at this
      have h1 : ∀ i, y i < N := fun i => by
        simpa using (inv_mul_lt_iff₀ hN').1 (h i).2
      refine ⟨fun i => ⟨⌊y i⌋₊, (Nat.floor_lt (h0 i)).2 (h1 i)⟩, fun i => ?_⟩
      exact ⟨Nat.floor_le (h0 i), Nat.lt_floor_add_one (y i)⟩
    · rintro ⟨z, hz⟩ i
      have hzN : ((z i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast (z i).isLt
      have h0 : 0 ≤ y i := le_trans (Nat.cast_nonneg _) (hz i).1
      refine ⟨mul_nonneg (inv_nonneg.2 hN'.le) h0, ?_⟩
      rw [inv_mul_lt_iff₀ hN', mul_one]
      linarith [(hz i).2]
  have hint : ∀ z : Fin n → Fin N, IntegrableOn G (l1_cell (fun i => (((z i : ℕ) : ℤ) : ℝ))) :=
    fun z => (hG.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
        (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self)
  have hdisj : Pairwise (Function.onFun Disjoint fun z : Fin n → Fin N =>
      l1_cell (fun i => (((z i : ℕ) : ℤ) : ℝ))) := by
    intro z z' hzz'
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hzz'
    refine Set.disjoint_left.2 fun y hy hy' => hi ?_
    have a := hy i (Set.mem_univ _)
    have b := hy' i (Set.mem_univ _)
    simp only [Set.mem_Ico, Int.cast_natCast] at a b
    have c1 : ((z i : ℕ) : ℝ) < (z' i : ℕ) + 1 := by linarith [a.1, b.2]
    have c2 : ((z' i : ℕ) : ℝ) < (z i : ℕ) + 1 := by linarith [a.2, b.1]
    have d1 : (z i : ℕ) < (z' i : ℕ) + 1 := by exact_mod_cast c1
    have d2 : (z' i : ℕ) < (z i : ℕ) + 1 := by exact_mod_cast c2
    exact Fin.ext (by omega)
  have hmeas : ∀ z : Fin n → Fin N, MeasurableSet (l1_cell (fun i => (((z i : ℕ) : ℤ) : ℝ))) :=
    fun z => MeasurableSet.univ_pi fun _ => measurableSet_Ico
  rw [hcells, integral_iUnion_fintype hmeas hdisj hint]
  simp_rw [l1_setIntegral_cell hper, hQ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, ← mul_assoc]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_mul]

/-- The averaging limit, for the limit in the proof of Lemma 1: for a continuous `ℤ^n`-periodic `G`,
`∫_{(0,1)^n} G (N x) dx → ∫_{(0,1)^n} G` as `N → ∞` through the reals. Rescaled,
`∫_{(0,1)^n} G (N x) dx = N^{-n} ∫_{(0,N)^n} G`. With `M = ⌊N⌋`, the cube `(0, N)^n` holds the
`M^n` whole cells of `(0, M)^n`, which contribute `M^n ∫_{(0,1)^n} G` (`l1_setIntegral_comp_nsmul`),
and a boundary layer of measure `N^n - M^n`. So the difference between `∫_{(0,1)^n} G (N x) dx`
and `(M/N)^n ∫_{(0,1)^n} G` is at most `sup |G| (1 - (M/N)^n)`, and `M / N → 1`. -/
theorem l1_tendsto_setIntegral_comp_smul {n : ℕ} {G : (Fin n → ℝ) → ℝ} (hG : Continuous G)
    (hper : ∀ x (z : Fin n → ℤ), G (x + fun i => (z i : ℝ)) = G x) :
    Tendsto (fun N : ℝ => ∫ x in unitCube n, G (N • x)) atTop (𝓝 (∫ x in unitCube n, G x)) := by
  obtain ⟨C, -, hC⟩ := l1_periodic_bounded hG hper
  set I := ∫ x in unitCube n, G x
  -- the cubes `(0, r)^n`
  let Q : ℝ → Set (Fin n → ℝ) := fun r => Set.pi Set.univ fun _ => Set.Ioo 0 r
  have hQmeas : ∀ r, MeasurableSet (Q r) := fun r =>
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hQvol : ∀ r : ℝ, 0 ≤ r → volume.real (Q r) = r ^ n := fun r hr => by
    simp only [Measure.real, Q]
    rw [Real.volume_pi_Ioo_toReal fun _ => hr]
    simp
  have hQfin : ∀ r, volume (Q r) ≠ ⊤ := fun r => by
    simp [Q, Real.volume_pi_Ioo]
  have hQint : ∀ r, IntegrableOn G (Q r) := fun r =>
    (hG.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc (a := (0:ℝ)) (b := r))).mono_set
        (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self)
  -- rescaling: `∫_{(0,1)^n} G (r x) dx = r^{-n} ∫_{(0,r)^n} G`
  have hscale : ∀ r : ℝ, 0 < r →
      ∫ x in unitCube n, G (r • x) = (r ^ n)⁻¹ * ∫ y in Q r, G y := by
    intro r hr
    rw [Measure.setIntegral_comp_smul_of_pos volume G _ hr, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, smul_eq_mul]
    congr 3
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
    simp only [unitCube, Q, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.smul_apply,
      smul_eq_mul]
    refine forall_congr' fun i => ?_
    rw [mul_pos_iff_of_pos_left (inv_pos.2 hr), inv_mul_lt_iff₀ hr, mul_one]
  -- the whole cells: `∫_{(0,M)^n} G = M^n ∫_{(0,1)^n} G`
  have hcells : ∀ M : ℕ, 0 < M → ∫ y in Q M, G y = (M : ℝ) ^ n * I := by
    intro M hM
    have hM' : (0:ℝ) < M := by exact_mod_cast hM
    have h := (hscale M hM').symm.trans (l1_setIntegral_comp_nsmul hG hper hM)
    exact (mul_inv_cancel_left₀ (by positivity) _).symm.trans (congrArg _ h)
  -- the estimate, for `N ≥ 1`
  have hest : ∀ N : ℝ, 1 ≤ N →
      ‖(∫ x in unitCube n, G (N • x)) - ((⌊N⌋₊ : ℝ) / N) ^ n * I‖ ≤
        C * (1 - ((⌊N⌋₊ : ℝ) / N) ^ n) := by
    intro N hN
    set M := ⌊N⌋₊
    have hN0 : 0 < N := by linarith
    have hM1 : 0 < M := Nat.floor_pos.2 hN
    have hM0 : (0:ℝ) < M := by exact_mod_cast hM1
    have hMN : (M : ℝ) ≤ N := Nat.floor_le hN0.le
    have hsub : Q M ⊆ Q N := Set.pi_mono fun _ _ => Set.Ioo_subset_Ioo_right hMN
    have hsplit : ∫ y in Q N, G y = (M : ℝ) ^ n * I + ∫ y in Q N \ Q M, G y := by
      conv_lhs => rw [← Set.union_sdiff_cancel hsub]
      rw [setIntegral_union Set.disjoint_sdiff_right ((hQmeas N).diff (hQmeas M)) (hQint M)
        ((hQint N).mono_set Set.sdiff_subset), hcells M hM1]
    have hE : ‖∫ y in Q N \ Q M, G y‖ ≤ C * (N ^ n - (M : ℝ) ^ n) := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Q N \ Q M) (f := G)
        ((measure_mono Set.sdiff_subset).trans_lt (hQfin N).lt_top) fun x _ => hC x
      rwa [measureReal_sdiff hsub (hQmeas M) (hQfin N), hQvol N hN0.le, hQvol M hM0.le] at h
    have hNn : (0:ℝ) < N ^ n := by positivity
    rw [hscale N hN0, hsplit, div_pow]
    calc ‖(N ^ n)⁻¹ * ((M : ℝ) ^ n * I + ∫ y in Q N \ Q M, G y) - (M : ℝ) ^ n / N ^ n * I‖
        = (N ^ n)⁻¹ * ‖∫ y in Q N \ Q M, G y‖ := by
          rw [show (N ^ n)⁻¹ * ((M : ℝ) ^ n * I + ∫ y in Q N \ Q M, G y) -
              (M : ℝ) ^ n / N ^ n * I = (N ^ n)⁻¹ * ∫ y in Q N \ Q M, G y by
            field_simp; ring, norm_mul, Real.norm_of_nonneg (inv_nonneg.2 hNn.le)]
      _ ≤ (N ^ n)⁻¹ * (C * (N ^ n - (M : ℝ) ^ n)) := by gcongr
      _ = C * (1 - (M : ℝ) ^ n / N ^ n) := by field_simp
  -- `M / N → 1`
  have hr : Tendsto (fun N : ℝ => ((⌊N⌋₊ : ℝ) / N) ^ n) atTop (𝓝 1) := by
    simpa using (tendsto_nat_floor_div_atTop (R := ℝ)).pow n
  have he : Tendsto (fun N : ℝ => (∫ x in unitCube n, G (N • x)) - ((⌊N⌋₊ : ℝ) / N) ^ n * I)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun N : ℝ => C * (1 - ((⌊N⌋₊ : ℝ) / N) ^ n)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN using hest N hN
    · simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hr).const_mul C
  simpa using he.add (hr.mul_const I)

/-! ### Jacobians and periodicity -/

/-- `jac` only depends on the germ of the map. -/
theorem l1_jac_congr {m n : ℕ} {φ ψ : (Fin n → ℝ) → Fin m → ℝ} {x : Fin n → ℝ}
    (h : φ =ᶠ[𝓝 x] ψ) : jac φ x = jac ψ x := by
  ext i k
  simp only [jac, Matrix.of_apply]
  rw [Filter.EventuallyEq.fderiv_eq (h.mono fun y hy => congrFun hy i)]

/-- An entry of `jac φ x` is bounded by the norm of the derivative of the row. -/
theorem l1_abs_jac_le {m n : ℕ} (φ : (Fin n → ℝ) → Fin m → ℝ) (x : Fin n → ℝ) (i : Fin m)
    (k : Fin n) : |jac φ x i k| ≤ ‖fderiv ℝ (fun y => φ y i) x‖ := by
  simp only [jac, Matrix.of_apply]
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ (fun y => φ y i) x).le_opNorm _).trans ?_
  have : ‖(Pi.single k (1:ℝ) : Fin n → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  calc _ ≤ ‖fderiv ℝ (fun y => φ y i) x‖ * 1 := by gcongr
    _ = _ := mul_one _

/-- The derivative of a periodic map is periodic. -/
theorem l1_fderiv_periodic {m n : ℕ} {u : (Fin n → ℝ) → Fin m → ℝ} (hper : IsPeriodic u)
    (i : Fin m) (x : Fin n → ℝ) (z : Fin n → ℤ) :
    fderiv ℝ (fun y => u y i) (x + fun j => (z j : ℝ)) = fderiv ℝ (fun y => u y i) x := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext y
  rw [hper]

theorem l1_jac_periodic {m n : ℕ} {u : (Fin n → ℝ) → Fin m → ℝ} (hper : IsPeriodic u)
    (x : Fin n → ℝ) (z : Fin n → ℤ) : jac u (x + fun j => (z j : ℝ)) = jac u x := by
  ext i k
  simp only [jac, Matrix.of_apply, l1_fderiv_periodic hper]

/-! ### The test maps `u_ε` -/

/-- The paper's `u_ε (x) = ε² η_ε (x) u (x / ε²)`, for `ε = 1/K`. -/
noncomputable def l1_testMap {m n : ℕ} (u : (Fin n → ℝ) → Fin m → ℝ) (K : ℝ) :
    (Fin n → ℝ) → Fin m → ℝ :=
  fun x => (K ^ 2)⁻¹ • (l1_eta n K x • u ((K ^ 2) • x))

theorem l1_testMap_contDiff {m n : ℕ} {u : (Fin n → ℝ) → Fin m → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (K : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (l1_testMap u K) := by
  unfold l1_testMap
  exact ((l1_eta_contDiff n K).smul (hu.comp (contDiff_const_smul (K ^ 2)))).const_smul ((K ^ 2)⁻¹)

/-- `u_ε` has compact support in `(0, 1)^n`. -/
theorem l1_testMap_support {m n : ℕ} (u : (Fin n → ℝ) → Fin m → ℝ) {K : ℝ} (hK : 1 ≤ K) :
    HasCompactSupport (l1_testMap u K) ∧ tsupport (l1_testMap u K) ⊆ unitCube n := by
  have hK0 : 0 < K := by linarith
  set S := Set.pi Set.univ fun _ : Fin n => Set.Icc (1 / (2 * K)) (1 - 1 / (2 * K))
  have h0 : ∀ x, x ∉ S → l1_testMap u K x = 0 := fun x hx => by
    have : l1_eta n K x = 0 := l1_eta_eq_zero hK0 fun h => hx fun i _ => ⟨(h i).1.le, (h i).2.le⟩
    simp [l1_testMap, this]
  refine ⟨HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_Icc) h0, ?_⟩
  refine (closure_minimal (Function.support_subset_iff'.2 h0)
    (isClosed_set_pi fun _ _ => isClosed_Icc)).trans ?_
  intro x hx i _
  have := hx i (Set.mem_univ _)
  have hp : 0 < 1 / (2 * K) := by positivity
  exact ⟨hp.trans_le this.1, by linarith [this.2]⟩

/-- On `(ε, 1 - ε)^n`, `D u_ε (x) = D u (x / ε²)`. -/
theorem l1_jac_testMap_inner {m n : ℕ} {u : (Fin n → ℝ) → Fin m → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) {K : ℝ} (hK : 0 < K) {x : Fin n → ℝ}
    (hx : ∀ i, 1 / K < x i ∧ x i < 1 - 1 / K) :
    jac (l1_testMap u K) x = jac u ((K ^ 2) • x) := by
  have hev : l1_testMap u K =ᶠ[𝓝 x] fun y => (K ^ 2)⁻¹ • u ((K ^ 2) • y) := by
    have hO : IsOpen (Set.pi Set.univ fun _ : Fin n => Set.Ioo (1 / K) (1 - 1 / K)) :=
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
    filter_upwards [hO.mem_nhds fun i _ => hx i] with y hy
    have : l1_eta n K y = 1 :=
      l1_eta_eq_one hK fun i => ⟨(hy i (Set.mem_univ _)).1.le, (hy i (Set.mem_univ _)).2.le⟩
    simp only [l1_testMap, this, one_smul]
  rw [l1_jac_congr hev]
  ext i k
  simp only [jac, Matrix.of_apply]
  have hui : DifferentiableAt ℝ (fun y => u y i) ((K ^ 2) • x) :=
    ((contDiff_pi.1 hu i).differentiable (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun y : Fin n → ℝ => (K ^ 2) • y)
      ((K ^ 2) • ContinuousLinearMap.id ℝ (Fin n → ℝ)) x :=
    (hasFDerivAt_id x).const_smul (K ^ 2)
  have h2 := (hui.hasFDerivAt.comp x h1).const_mul ((K ^ 2)⁻¹)
  rw [show (fun y => ((K ^ 2)⁻¹ • u ((K ^ 2) • y)) i) =
    fun y => (K ^ 2)⁻¹ * ((fun y => u y i) ∘ fun y => (K ^ 2) • y) y from rfl, h2.fderiv]
  have hK2 : K ^ 2 ≠ 0 := by positivity
  simp [hK2]

/-- `D u_ε = ε² u (x/ε²) ⊗ D η_ε + η_ε D u (x/ε²)` is bounded uniformly in `ε = 1/K ≤ 1`: each row
satisfies `|D (u_ε)ᵢ| ≤ D + 4 n B U ε ≤ D + 4 n B U`, where `U` bounds `|u|`, `D` bounds the rows of
`D u`, and `B` bounds the derivative of `Real.smoothTransition` (so `|D η_ε| ≤ 4 n B / ε`). -/
theorem l1_fderiv_testMap_bound {m n : ℕ} {u : (Fin n → ℝ) → Fin m → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) {K : ℝ} (hK : 1 ≤ K) {B U D : ℝ}
    (hB : ∀ s, |deriv Real.smoothTransition s| ≤ B) (hU : ∀ y, ‖u y‖ ≤ U)
    (hD : ∀ i y, ‖fderiv ℝ (fun y => u y i) y‖ ≤ D) (x : Fin n → ℝ) (i : Fin m) :
    ‖fderiv ℝ (fun y => l1_testMap u K y i) x‖ ≤ D + n * (4 * B) * U := by
  have hK0 : 0 < K := by linarith
  have hη : HasFDerivAt (l1_eta n K) (fderiv ℝ (l1_eta n K) x) x :=
    ((l1_eta_contDiff n K).differentiable (by simp) x).hasFDerivAt
  have hui : DifferentiableAt ℝ (fun y => u y i) ((K ^ 2) • x) :=
    ((contDiff_pi.1 hu i).differentiable (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun y : Fin n → ℝ => (K ^ 2) • y)
      ((K ^ 2) • ContinuousLinearMap.id ℝ (Fin n → ℝ)) x :=
    (hasFDerivAt_id x).const_smul (K ^ 2)
  have hv := hui.hasFDerivAt.comp x h1
  have h := (hη.mul hv).const_mul ((K ^ 2)⁻¹)
  have hφ := (show HasFDerivAt (fun y => l1_testMap u K y i) _ x from h)
  rw [hφ.fderiv]
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD i 0)
  have hL : ‖(fderiv ℝ (fun y => u y i) ((K ^ 2) • x)).comp
      ((K ^ 2) • ContinuousLinearMap.id ℝ (Fin n → ℝ))‖ ≤ D * K ^ 2 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    gcongr
    · exact hD i _
    · refine (norm_smul_le _ _).trans ?_
      rw [Real.norm_of_nonneg (by positivity)]
      calc K ^ 2 * ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤ K ^ 2 * 1 := by
            gcongr; exact ContinuousLinearMap.norm_id_le
        _ = K ^ 2 := mul_one _
  have hη1 : ‖l1_eta n K x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (l1_eta_nonneg n K x)]; exact l1_eta_le_one n K x
  have hv1 : ‖((fun y => u y i) ∘ fun y => (K ^ 2) • y) x‖ ≤ U :=
    (norm_le_pi_norm (u ((K ^ 2) • x)) i).trans (hU _)
  have hη' : ‖fderiv ℝ (l1_eta n K) x‖ ≤ n * (4 * K * B) := l1_eta_fderiv_bound hK0 hB x
  calc _ ≤ (K ^ 2)⁻¹ * (1 * (D * K ^ 2) + U * (n * (4 * K * B))) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
        exact add_le_add (mul_le_mul hη1 hL (norm_nonneg _) zero_le_one)
          (mul_le_mul hv1 hη' (norm_nonneg _) hU0)
    _ = D + n * (4 * B) * U / K := by field_simp
    _ ≤ D + n * (4 * B) * U := by gcongr; exact div_le_self (by positivity) hK

/-- The limit in the proof of **Lemma 1** (`sv-lemma1`): for a continuous `f`, a smooth
`ℤ^n`-periodic `u` and every matrix `A`, the paper's maps `u_ε = ε² η_ε u (· / ε²)`
(`l1_testMap u ε⁻¹`: the formalization's parameter is `K = 1/ε`) satisfy
`∫_{(0,1)^n} f (A + D u_ε) → ∫_{(0,1)^n} f (A + D u)` as `ε → 0⁺`. The paper states this limit
("it is easily seen") without proof.

Proof: the integrands are bounded uniformly in `ε ≤ 1` (`l1_fderiv_testMap_bound`), and
`D u_ε (x) = D u (x / ε²)` on `(ε, 1 - ε)^n` (`l1_jac_testMap_inner`), so by dominated convergence
`∫ f (A + D u_ε) - ∫ f (A + D u (x / ε²)) → 0`; and `∫ f (A + D u (x / ε²)) → ∫ f (A + D u)` by
periodicity (`l1_tendsto_setIntegral_comp_smul`, with `N = 1/ε²`, not an integer in general). A
note on the construction: the cutoff `η_ε` (`l1_eta`) has `|D η_ε| ≤ 4 n B / ε`
(`l1_eta_fderiv_bound`), with `B = sup |smoothTransition'|`, where the paper asks
`|D η_ε| ≤ 2 / ε`; the paper's constant 2 is not used, any bound `C / ε` serves, since only the
boundedness of `ε² |D η_ε|` enters. -/
theorem lemma1_limit {m n : ℕ} {f : Matrix (Fin m) (Fin n) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin m) (Fin n) ℝ) {u : (Fin n → ℝ) → Fin m → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (hper : IsPeriodic u) :
    Tendsto (fun ε : ℝ => ∫ x in unitCube n, f (A + jac (l1_testMap u ε⁻¹) x)) (𝓝[>] 0)
      (𝓝 (∫ x in unitCube n, f (A + jac u x))) := by
  -- uniform bounds: `|Dη_ε| ≤ 4 n B / ε`, `|u| ≤ U`, `|Du| ≤ D'`
  obtain ⟨B, hB0, hB⟩ := l1_deriv_smoothTransition_bound
  obtain ⟨U, hU0, hU⟩ := l1_periodic_bounded hu.continuous hper
  have hDi : ∀ i, ∃ D, 0 ≤ D ∧ ∀ y, ‖fderiv ℝ (fun y => u y i) y‖ ≤ D := fun i =>
    l1_periodic_bounded (((contDiff_pi.1 hu) i).continuous_fderiv (by simp))
      (fun x z => l1_fderiv_periodic hper i x z)
  choose D hD0 hD using hDi
  set D' := ∑ i, D i
  have hD' : ∀ i y, ‖fderiv ℝ (fun y => u y i) y‖ ≤ D' := fun i y =>
    (hD i y).trans (Finset.single_le_sum (fun j _ => hD0 j) (Finset.mem_univ i))
  set R := D' + n * (4 * B) * U
  have hD'R : D' ≤ R := le_add_of_nonneg_right (by positivity)
  -- the integrand is bounded on the matrices with entries in `[-R, R]`
  set S : Set (Matrix (Fin m) (Fin n) ℝ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-R) R
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    (hf.comp (continuous_const.add continuous_id)).continuousOn
  have hmemS : ∀ (ψ : (Fin n → ℝ) → Fin m → ℝ) x,
      (∀ i, ‖fderiv ℝ (fun y => ψ y i) x‖ ≤ R) → jac ψ x ∈ S := by
    intro ψ x h i _ k _
    exact abs_le.1 ((l1_abs_jac_le ψ x i k).trans (h i))
  -- in terms of `K = 1/ε → ∞`
  let G : (Fin n → ℝ) → ℝ := fun y => f (A + jac u y)
  have hGc : Continuous G := gen_continuous_comp_jac hf A hu
  have hGper : ∀ x (z : Fin n → ℤ), G (x + fun i => (z i : ℝ)) = G x := fun x z => by
    simp only [G, l1_jac_periodic hper]
  let H : ℝ → (Fin n → ℝ) → ℝ := fun K x =>
    f (A + jac (l1_testMap u K) x) - G ((K ^ 2) • x)
  have hHc : ∀ K, Continuous (H K) := fun K =>
    (gen_continuous_comp_jac hf A (l1_testMap_contDiff hu K)).sub
      (hGc.comp (continuous_const_smul _))
  have : IsFiniteMeasure (volume.restrict (unitCube n)) :=
    isFiniteMeasure_restrict.2 (by rw [volume_unitCube]; simp)
  have hcube : MeasurableSet (unitCube n) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  -- dominated convergence: `∫ f (A + D u_ε) - ∫ f (A + D u (x / ε²)) → 0`
  have hlim : Tendsto (fun K => ∫ x in unitCube n, H K x) atTop
      (𝓝 (∫ x in unitCube n, (0:ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * M)
      (Eventually.of_forall fun K => (hHc K).aestronglyMeasurable) ?_ (integrable_const _) ?_
    · filter_upwards [eventually_ge_atTop 1] with K hK
      refine Eventually.of_forall fun x => ?_
      have h1 : ‖f (A + jac (l1_testMap u K) x)‖ ≤ M :=
        hM _ (hmemS _ x fun i => l1_fderiv_testMap_bound hu hK hB hU hD' x i)
      have h2 : ‖G ((K ^ 2) • x)‖ ≤ M := hM _ (hmemS u _ fun i => (hD' i _).trans hD'R)
      calc ‖H K x‖ ≤ ‖f (A + jac (l1_testMap u K) x)‖ + ‖G ((K ^ 2) • x)‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith
    · rw [ae_restrict_iff' hcube]
      refine Eventually.of_forall fun x hx => ?_
      refine tendsto_const_nhds.congr' ?_
      have ht : Tendsto (fun K : ℝ => 1 / K) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hev : ∀ᶠ K in atTop, ∀ i, 1 / K < x i ∧ x i < 1 - 1 / K := by
        rw [eventually_all]
        intro i
        have hxi := hx i (Set.mem_univ _)
        filter_upwards [ht.eventually (Iio_mem_nhds hxi.1),
          ht.eventually (Iio_mem_nhds (sub_pos.2 hxi.2))] with K h1 h2
        exact ⟨h1, by linarith⟩
      filter_upwards [hev, eventually_gt_atTop 0] with K hK hK0
      show (0:ℝ) = f (A + jac (l1_testMap u K) x) - f (A + jac u ((K ^ 2) • x))
      rw [l1_jac_testMap_inner hu hK0 hK, sub_self]
  rw [integral_zero] at hlim
  -- by periodicity, `∫ f (A + D u (x / ε²)) → ∫ f (A + D u)`
  have havg : Tendsto (fun K : ℝ => ∫ x in unitCube n, G ((K ^ 2) • x)) atTop
      (𝓝 (∫ x in unitCube n, G x)) :=
    (l1_tendsto_setIntegral_comp_smul hGc hGper).comp (tendsto_pow_atTop two_ne_zero)
  have hK : Tendsto (fun K => ∫ x in unitCube n, f (A + jac (l1_testMap u K) x)) atTop
      (𝓝 (∫ x in unitCube n, G x)) := by
    have h := hlim.add havg
    rw [zero_add] at h
    refine h.congr fun K => ?_
    rw [← integral_add (gen_integrableOn_unitCube (hHc K))
      (gen_integrableOn_unitCube (g := fun x => G ((K ^ 2) • x))
        (hGc.comp (continuous_const_smul _)))]
    congr 1
    funext x
    simp only [H]
    ring
  exact hK.comp tendsto_inv_nhdsGT_zero

/-- **Lemma 1** (`sv-lemma1`), "only if" part, in contrapositive form: for a continuous `f`, a
smooth `ℤ^n`-periodic `u` with `∫_{[0,1]^n} f (A + ∇u) < f (A)` yields a smooth map `φ` with
compact support in `(0, 1)^n` and `∫ f (A + ∇φ) < f (A)`, one of the paper's `u_ε` with
`0 < ε < 1/2`.

Proof (the paper's): by the limit in the proof of Lemma 1 (`lemma1_limit`), the integrals
`∫ f (A + D u_ε)` tend to `∫ f (A + D u) < f (A)` as `ε → 0⁺`, so one of them is `< f (A)`. A
note on the construction: the cutoff `η_ε` (`l1_eta`) has `|D η_ε| ≤ 4 n B / ε` where the paper
asks `|D η_ε| ≤ 2 / ε`; the paper's constant 2 is not used, any bound `C / ε` serves. -/
theorem lemma1_witness {m n : ℕ} {f : Matrix (Fin m) (Fin n) ℝ → ℝ} (hf : Continuous f)
    {A : Matrix (Fin m) (Fin n) ℝ} {u : (Fin n → ℝ) → Fin m → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (hper : IsPeriodic u)
    (hlt : ∫ x in unitCube n, f (A + jac u x) < f A) :
    ∃ φ : (Fin n → ℝ) → Fin m → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ unitCube n ∧ ∫ x in unitCube n, f (A + jac φ x) < f A := by
  obtain ⟨ε, hlt', hε⟩ := (((lemma1_limit hf A hu hper).eventually_lt_const hlt).and
    (Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 2 by norm_num))).exists
  obtain ⟨hcs, hts⟩ := l1_testMap_support u ((one_le_inv₀ hε.1).2 (by linarith [hε.2]))
  exact ⟨l1_testMap u ε⁻¹, l1_testMap_contDiff hu _, hcs, hts, hlt'⟩

/-! ### The "if" part: periodic extension -/

/-- The `ℤ^n`-periodic extension `x ↦ φ (fract x)` of a map `φ` supported in the cube. -/
noncomputable def l1_perExt {m n : ℕ} (φ : (Fin n → ℝ) → Fin m → ℝ) : (Fin n → ℝ) → Fin m → ℝ :=
  fun x => φ fun i => Int.fract (x i)

theorem l1_perExt_periodic {m n : ℕ} (φ : (Fin n → ℝ) → Fin m → ℝ) : IsPeriodic (l1_perExt φ) := by
  intro x z
  simp only [l1_perExt, Pi.add_apply, Int.fract_add_intCast]

/-- Near any point, the periodic extension is a finite sum of translates of `φ`. -/
theorem l1_perExt_contDiff {m n : ℕ} {φ : (Fin n → ℝ) → Fin m → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hs : tsupport φ ⊆ unitCube n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (l1_perExt φ) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  set W : Finset (Fin n → ℤ) := Fintype.piFinset fun i => Finset.Icc (⌊x i⌋ - 1) (⌊x i⌋ + 1)
  have hsum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun y => ∑ w ∈ W, φ (y - fun i => (w i : ℝ)) :=
    ContDiff.sum fun w _ => hφ.comp (contDiff_id.sub contDiff_const)
  refine hsum.contDiffAt.congr_of_eventuallyEq ?_
  have hO : IsOpen (Set.pi Set.univ fun i => Set.Ioo (x i - 1) (x i + 1)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  filter_upwards [hO.mem_nhds fun i _ => ⟨by linarith, by linarith⟩] with y hy
  have hw0 : (fun i => ⌊y i⌋) ∈ W := by
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨?_, ?_⟩
    · refine Int.le_floor.2 ?_
      have := (hy i (Set.mem_univ _)).1
      push_cast
      linarith [Int.floor_le (x i)]
    · have h1 : ⌊y i⌋ < ⌊x i⌋ + 2 := by
        refine Int.floor_lt.2 ?_
        have := (hy i (Set.mem_univ _)).2
        push_cast
        linarith [Int.lt_floor_add_one (x i)]
      omega
  rw [Finset.sum_eq_single_of_mem _ hw0]
  · simp only [l1_perExt]
    congr 1
  · intro w _ hw
    by_contra hne
    apply hw
    have hmem := hs (subset_tsupport φ (Function.mem_support.2 hne))
    funext i
    have := hmem i (Set.mem_univ _)
    simp only [Pi.sub_apply, Set.mem_Ioo] at this
    exact (Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩).symm

/-- On the open cube the periodic extension has the same gradient as `φ`. -/
theorem l1_jac_perExt {m n : ℕ} (φ : (Fin n → ℝ) → Fin m → ℝ) {x : Fin n → ℝ}
    (hx : x ∈ unitCube n) : jac (l1_perExt φ) x = jac φ x := by
  have hO : IsOpen (unitCube n) := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  refine l1_jac_congr ?_
  filter_upwards [hO.mem_nhds hx] with y hy
  simp only [l1_perExt]
  congr 1
  funext i
  have := hy i (Set.mem_univ _)
  exact Int.fract_eq_self.2 ⟨this.1.le, this.2⟩

/-- **Lemma 1** (`sv-lemma1`). A continuous function `f : M^{m×n} → ℝ` is quasiconvex if and only
if `∫_{[0,1]^n} f (A + D u (x)) dx ≥ f (A)` for each `A ∈ M^{m×n}` and each smooth `u : ℝ^n → ℝ^m`
which is periodic with respect to `ℤ^n`. Quasiconvex is meant on the unit cube
(`QuasiconvexOn (unitCube n)`); the paper's class does not depend on `Ω`, by [3] and [10] of the
paper, which is not formalized here.

Proof (the paper's). "Only if": for `0 < ε < 1/2` the map `u_ε = ε² η_ε u (· / ε²)` is smooth and
compactly supported in `(0, 1)^n`, so quasiconvexity gives (2), `f (A) ≤ ∫ f (A + D u_ε)`; as
`ε → 0⁺` the right side tends to `∫ f (A + D u)` (`lemma1_limit`). "If" (the paper: "trivial"):
test with the periodic extension `x ↦ φ (fract x)` of `φ` (`l1_perExt`), smooth because near each
point it is a finite sum of integer translates of `φ`. -/
theorem lemma1 {m n : ℕ} {f : Matrix (Fin m) (Fin n) ℝ → ℝ} (hf : Continuous f) :
    QuasiconvexOn (unitCube n) f ↔
      ∀ (A : Matrix (Fin m) (Fin n) ℝ) (u : (Fin n → ℝ) → Fin m → ℝ),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u → IsPeriodic u →
          f A ≤ ∫ x in unitCube n, f (A + jac u x) := by
  have hconst : ∀ A : Matrix (Fin m) (Fin n) ℝ, ∫ _ in unitCube n, f A = f A := fun A => by
    simp [Measure.real, volume_unitCube]
  have hcube : MeasurableSet (unitCube n) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  constructor
  · intro hq A u hu hper
    -- (2): `f (A) ≤ ∫ f (A + D u_ε)` for each `0 < ε < 1/2`
    have h2 : ∀ᶠ ε in 𝓝[>] (0:ℝ),
        f A ≤ ∫ x in unitCube n, f (A + jac (l1_testMap u ε⁻¹) x) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 2 by norm_num)] with ε hε
      obtain ⟨hcs, hts⟩ := l1_testMap_support u ((one_le_inv₀ hε.1).2 (by linarith [hε.2]))
      have := hq A _ (l1_testMap_contDiff hu _) hcs hts
        (gen_integrableOn_unitCube (gen_continuous_comp_jac hf A (l1_testMap_contDiff hu _)))
      rwa [hconst] at this
    -- and the right-hand sides tend to `∫ f (A + D u)`
    exact ge_of_tendsto (lemma1_limit hf A hu hper) h2
  · intro h A φ hφ _ hs _
    rw [hconst]
    calc f A ≤ ∫ x in unitCube n, f (A + jac (l1_perExt φ) x) :=
          h A _ (l1_perExt_contDiff hφ hs) (l1_perExt_periodic φ)
      _ = ∫ x in unitCube n, f (A + jac φ x) :=
          setIntegral_congr_fun hcube fun x hx => by simp only [l1_jac_perExt φ hx]

end Sverak
