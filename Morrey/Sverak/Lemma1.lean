module

public import Morrey.Sverak.Cube
public import Morrey.Common.Basic.Analysis.Calculus.BumpFunction.Mollify
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

* the paper's cutoff `η_ε` (`l1_eta`, for `ε = 1/K`): smooth, equal to `1` on `[ε, 1 - ε]^n`,
  vanishing in a neighbourhood of the boundary of `[0, 1]^n` (off `(ε/16, 1 - ε/16)^n`), with
  `|D η_ε| ≤ 2 / ε` (`l1_eta_fderiv_bound`). It is the mollification, by a normed bump of radius
  `ε/16` (`l1_bump`), of the Lipschitz profile `p = min (1, max (0, (d - ε/8) · 8/(5ε)))`
  (`l1_profile`) of the distance `d` to the boundary of the cube (`l1_dist`), so that `D η_ε` is
  bounded by the Lipschitz constant `8/(5ε)` of `p`;
* the periodic average identity `∫_{(0,1)^n} G (N x) dx = ∫_{(0,1)^n} G` for an integer `N ≥ 1`
  (`l1_setIntegral_comp_nsmul`), and the averaging limit `∫_{(0,1)^n} G (N x) dx → ∫_{(0,1)^n} G`
  as `N → ∞` through the reals (`l1_tendsto_setIntegral_comp_smul`);
* the test maps `u_ε` (`l1_testMap`) and their gradients;
* the periodic extension `x ↦ φ (fract x)` (`l1_perExt`) for the "if" part.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Pointwise Convolution

namespace Sverak

/-- `u : ℝ^n → ℝ^m` is periodic with respect to `ℤ^n`. -/
def IsPeriodic {m n : ℕ} (u : (Fin n → ℝ) → Fin m → ℝ) : Prop :=
  ∀ (x : Fin n → ℝ) (z : Fin n → ℤ), u (x + fun i => (z i : ℝ)) = u x

/-! ### The cutoff `η_ε` -/

/-- The distance from `x ∈ [0, 1]^n` to the boundary of the cube, for the sup norm:
`d (x) = min (1, minᵢ min (xᵢ, 1 - xᵢ))`. The `1` only matters for `n = 0`, where the cube is a
point and `d = 1`. -/
noncomputable def l1_dist (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Finset.univ.fold min 1 fun i => min (x i) (1 - x i)

theorem l1_le_dist_iff {n : ℕ} {x : Fin n → ℝ} {t : ℝ} :
    t ≤ l1_dist n x ↔ t ≤ 1 ∧ ∀ i, t ≤ x i ∧ t ≤ 1 - x i := by
  simp [l1_dist, Finset.le_fold_min]

theorem l1_dist_le {n : ℕ} {x : Fin n → ℝ} {t : ℝ} (i : Fin n) (h : x i ≤ t ∨ 1 - x i ≤ t) :
    l1_dist n x ≤ t := by
  refine (Finset.fold_min_le _).2 (Or.inr ⟨i, Finset.mem_univ i, ?_⟩)
  rcases h with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans h

/-- `d` is `1`-Lipschitz for the sup norm: `d (y) ≥ d (x) - ‖x - y‖`, since each `yᵢ` and
`1 - yᵢ` is within `‖x - y‖` of `xᵢ` and `1 - xᵢ`. -/
theorem l1_dist_lipschitzWith (n : ℕ) : LipschitzWith 1 (l1_dist n) := by
  refine LipschitzWith.of_le_add fun x y => ?_
  have h := (l1_le_dist_iff (x := x) (t := l1_dist n x)).1 le_rfl
  have h' : l1_dist n x - dist x y ≤ l1_dist n y := by
    refine l1_le_dist_iff.2 ⟨by linarith [h.1, dist_nonneg (x := x) (y := y)], fun i => ?_⟩
    have hi := abs_le.1 ((Real.dist_eq _ _).symm.trans_le (dist_le_pi_dist x y i))
    exact ⟨by linarith [(h.2 i).1], by linarith [(h.2 i).2]⟩
  linarith

/-- The Lipschitz profile of the cutoff, for `ε = 1/K`:
`p (x) = min (1, max (0, (d (x) - ε/8) · 8/(5ε)))`, which is `0` where `d ≤ ε/8` and `1` where
`d ≥ 3ε/4`. -/
noncomputable def l1_profile (n : ℕ) (K : ℝ) (x : Fin n → ℝ) : ℝ :=
  min 1 (max 0 ((l1_dist n x - 1 / (8 * K)) * (8 * K / 5)))

theorem l1_profile_mem_Icc (n : ℕ) (K : ℝ) (x : Fin n → ℝ) : l1_profile n K x ∈ Set.Icc 0 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem l1_continuous_profile (n : ℕ) (K : ℝ) : Continuous (l1_profile n K) :=
  continuous_const.min (continuous_const.max
    (((l1_dist_lipschitzWith n).continuous.sub continuous_const).mul continuous_const))

/-- `p` is `8/(5ε)`-Lipschitz: `d` is `1`-Lipschitz, and the truncations `min 1`, `max 0` are
`1`-Lipschitz. -/
theorem l1_profile_lipschitzWith (n : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    LipschitzWith (Real.toNNReal (8 * K / 5)) (l1_profile n K) := by
  have h : LipschitzWith (Real.toNNReal (8 * K / 5))
      fun x => (l1_dist n x - 1 / (8 * K)) * (8 * K / 5) := by
    refine LipschitzWith.of_dist_le' fun x y => ?_
    rw [Real.dist_eq, ← sub_mul, sub_sub_sub_cancel_right, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 8 * K / 5), mul_comm]
    gcongr
    simpa [Real.dist_eq] using (l1_dist_lipschitzWith n).dist_le_mul x y
  exact (h.const_max 0).const_min 1

/-- `p = 0` where `d ≤ ε/8`. -/
theorem l1_profile_eq_zero {n : ℕ} {K : ℝ} (hK : 0 < K) {x : Fin n → ℝ}
    (h : l1_dist n x ≤ 1 / (8 * K)) : l1_profile n K x = 0 := by
  have : (l1_dist n x - 1 / (8 * K)) * (8 * K / 5) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [l1_profile, max_eq_left this, min_eq_right zero_le_one]

/-- `p = 1` where `d ≥ 3ε/4`. -/
theorem l1_profile_eq_one {n : ℕ} {K : ℝ} (hK : 0 < K) {x : Fin n → ℝ}
    (h : 3 / (4 * K) ≤ l1_dist n x) : l1_profile n K x = 1 := by
  have : 1 ≤ (l1_dist n x - 1 / (8 * K)) * (8 * K / 5) := by
    have e : (3 / (4 * K) - 1 / (8 * K)) * (8 * K / 5) = 1 := by field_simp; ring
    calc (1:ℝ) = _ := e.symm
      _ ≤ _ := by gcongr
  rw [l1_profile, max_eq_right (zero_le_one.trans this), min_eq_left this]

/-- The mollifier for `ε = 1/K > 0`: the normed bump of radius `ε/16` (`l1_bump_rOut`). -/
noncomputable def l1_bump (n : ℕ) (K : ℝ) : ContDiffBump (0 : Fin n → ℝ) :=
  if hK : 0 < K then ContDiffBump.ofRadius (r := 1 / (16 * K)) (by positivity)
  else ContDiffBump.ofRadius one_pos

theorem l1_bump_rOut {n : ℕ} {K : ℝ} (hK : 0 < K) : (l1_bump n K).rOut = 1 / (16 * K) := by
  simp [l1_bump, hK]

/-- The paper's cutoff `η_ε` for `ε = 1/K`: the mollification `ρ ⋆ p` of the Lipschitz profile
`p` (`l1_profile`) by the normed bump `ρ` of radius `ε/16` (`l1_bump`). It is smooth
(`l1_eta_contDiff`), takes values in `[0, 1]`, equals `1` on `[ε, 1 - ε]^n` (`l1_eta_eq_one`),
vanishes in a neighbourhood of the boundary of `[0, 1]^n`, namely off `(ε/16, 1 - ε/16)^n`
(`l1_eta_eq_zero`), and satisfies `|D η_ε| ≤ 2 / ε` (`l1_eta_fderiv_bound`). -/
noncomputable def l1_eta (n : ℕ) (K : ℝ) : (Fin n → ℝ) → ℝ :=
  (l1_bump n K).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] l1_profile n K

/-- `η_ε` is smooth: the mollification of a continuous function. -/
theorem l1_eta_contDiff (n : ℕ) (K : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (l1_eta n K) :=
  (l1_bump n K).contDiff_normed_convolution (l1_continuous_profile n K).locallyIntegrable

theorem l1_eta_mem_Icc (n : ℕ) (K : ℝ) (x : Fin n → ℝ) : l1_eta n K x ∈ Set.Icc 0 1 :=
  (l1_bump n K).normed_convolution_mem_Icc (l1_continuous_profile n K).locallyIntegrable
    (l1_profile_mem_Icc n K) x

theorem l1_eta_nonneg (n : ℕ) (K : ℝ) (x : Fin n → ℝ) : 0 ≤ l1_eta n K x :=
  (l1_eta_mem_Icc n K x).1

theorem l1_eta_le_one (n : ℕ) (K : ℝ) (x : Fin n → ℝ) : l1_eta n K x ≤ 1 :=
  (l1_eta_mem_Icc n K x).2

/-- `η_ε = 1` on `[ε, 1 - ε]^n` (for `ε ≤ 1`): on the ball of radius `ε/16` about such an `x`,
`d ≥ 15ε/16 ≥ 3ε/4`, so `p = 1` there. -/
theorem l1_eta_eq_one {n : ℕ} {K : ℝ} (hK : 1 ≤ K) {x : Fin n → ℝ}
    (hx : ∀ i, 1 / K ≤ x i ∧ x i ≤ 1 - 1 / K) : l1_eta n K x = 1 := by
  have hK0 : 0 < K := by linarith
  unfold l1_eta
  refine (l1_bump n K).normed_convolution_eq_of_forall_ball fun y hy => l1_profile_eq_one hK0 ?_
  rw [l1_bump_rOut hK0, Metric.mem_ball, dist_pi_lt_iff (by positivity)] at hy
  have e1 : 1 / (16 * K) = 1 / K / 16 := by ring
  have e2 : 3 / (4 * K) = 3 / 4 * (1 / K) := by ring
  have hK1 : 1 / K ≤ 1 := (div_le_one hK0).2 hK
  have hKp : 0 < 1 / K := by positivity
  refine l1_le_dist_iff.2 ⟨by linarith, fun i => ?_⟩
  have h1 := abs_lt.1 ((Real.dist_eq _ _).symm.trans_lt (hy i))
  have h2 := hx i
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `η_ε` vanishes off `(ε/16, 1 - ε/16)^n`, a neighbourhood of the boundary of `[0, 1]^n`: on the
ball of radius `ε/16` about such an `x`, `d < ε/8`, so `p = 0` there. -/
theorem l1_eta_eq_zero {n : ℕ} {K : ℝ} (hK : 0 < K) {x : Fin n → ℝ}
    (hx : ¬ ∀ i, 1 / (16 * K) < x i ∧ x i < 1 - 1 / (16 * K)) : l1_eta n K x = 0 := by
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  unfold l1_eta
  refine (l1_bump n K).normed_convolution_eq_of_forall_ball fun y hy => l1_profile_eq_zero hK ?_
  rw [l1_bump_rOut hK, Metric.mem_ball, dist_pi_lt_iff (by positivity)] at hy
  have h1 := abs_lt.1 ((Real.dist_eq _ _).symm.trans_lt (hy i))
  have e : 1 / (8 * K) = 2 * (1 / (16 * K)) := by ring
  refine l1_dist_le i ?_
  by_cases h : 1 / (16 * K) < x i
  · exact Or.inr (by linarith [hi h, h1.1, h1.2])
  · exact Or.inl (by linarith [h1.1, h1.2])

/-- The paper's gradient bound `|D η_ε| ≤ 2 / ε` for `ε = 1/K`: the mollification keeps the
Lipschitz constant `8/(5ε)` of `p` (`ContDiffBump.norm_fderiv_normed_convolution_le`). The norm is
the operator norm for the sup norm on `ℝ^n`, the `ℓ¹` norm of the gradient, which dominates its
Euclidean norm. -/
theorem l1_eta_fderiv_bound {n : ℕ} {K : ℝ} (hK : 0 < K) (x : Fin n → ℝ) :
    ‖fderiv ℝ (l1_eta n K) x‖ ≤ 2 * K := by
  refine ((l1_bump n K).norm_fderiv_normed_convolution_le
    (l1_profile_lipschitzWith n hK.le) x).trans ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  linarith

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
  set S := Set.pi Set.univ fun _ : Fin n => Set.Icc (1 / (16 * K)) (1 - 1 / (16 * K))
  have h0 : ∀ x, x ∉ S → l1_testMap u K x = 0 := fun x hx => by
    have : l1_eta n K x = 0 := l1_eta_eq_zero hK0 fun h => hx fun i _ => ⟨(h i).1.le, (h i).2.le⟩
    simp [l1_testMap, this]
  refine ⟨HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_Icc) h0, ?_⟩
  refine (closure_minimal (Function.support_subset_iff'.2 h0)
    (isClosed_set_pi fun _ _ => isClosed_Icc)).trans ?_
  intro x hx i _
  have := hx i (Set.mem_univ _)
  have hp : 0 < 1 / (16 * K) := by positivity
  exact ⟨hp.trans_le this.1, by linarith [this.2]⟩

/-- On `(ε, 1 - ε)^n`, `D u_ε (x) = D u (x / ε²)`. -/
theorem l1_jac_testMap_inner {m n : ℕ} {u : (Fin n → ℝ) → Fin m → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) {K : ℝ} (hK : 1 ≤ K) {x : Fin n → ℝ}
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

/-- `D u_ε = ε² u (x/ε²) ⊗ D η_ε + η_ε D u (x/ε²)` is bounded uniformly in `ε = 1/K ≤ 1`: with
`|D η_ε| ≤ 2 / ε` (`l1_eta_fderiv_bound`), each row satisfies `|D (u_ε)ᵢ| ≤ D + 2 U ε ≤ D + 2 U`,
where `U` bounds `|u|` and `D` bounds the rows of `D u`. -/
theorem l1_fderiv_testMap_bound {m n : ℕ} {u : (Fin n → ℝ) → Fin m → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) {K : ℝ} (hK : 1 ≤ K) {U D : ℝ}
    (hU : ∀ y, ‖u y‖ ≤ U) (hD : ∀ i y, ‖fderiv ℝ (fun y => u y i) y‖ ≤ D) (x : Fin n → ℝ)
    (i : Fin m) :
    ‖fderiv ℝ (fun y => l1_testMap u K y i) x‖ ≤ D + 2 * U := by
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
  have hη' : ‖fderiv ℝ (l1_eta n K) x‖ ≤ 2 * K := l1_eta_fderiv_bound hK0 x
  calc _ ≤ (K ^ 2)⁻¹ * (1 * (D * K ^ 2) + U * (2 * K)) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
        exact add_le_add (mul_le_mul hη1 hL (norm_nonneg _) zero_le_one)
          (mul_le_mul hv1 hη' (norm_nonneg _) hU0)
    _ = D + 2 * U / K := by field_simp
    _ ≤ D + 2 * U := by gcongr; exact div_le_self (by positivity) hK

/-- The limit in the proof of **Lemma 1** (`sv-lemma1`): for a continuous `f`, a smooth
`ℤ^n`-periodic `u` and every matrix `A`, the paper's maps `u_ε = ε² η_ε u (· / ε²)`
(`l1_testMap u ε⁻¹`: the formalization's parameter is `K = 1/ε`) satisfy
`∫_{(0,1)^n} f (A + D u_ε) → ∫_{(0,1)^n} f (A + D u)` as `ε → 0⁺`. The paper states this limit
("it is easily seen") without proof.

Proof: the integrands are bounded uniformly in `ε ≤ 1` (`l1_fderiv_testMap_bound`), and
`D u_ε (x) = D u (x / ε²)` on `(ε, 1 - ε)^n` (`l1_jac_testMap_inner`), so by dominated convergence
`∫ f (A + D u_ε) - ∫ f (A + D u (x / ε²)) → 0`; and `∫ f (A + D u (x / ε²)) → ∫ f (A + D u)` by
periodicity (`l1_tendsto_setIntegral_comp_smul`, with `N = 1/ε²`, not an integer in general). The
cutoff `η_ε` (`l1_eta`) is the paper's: smooth, equal to `1` on `[ε, 1 - ε]^n`, vanishing in a
neighbourhood of the boundary of `[0, 1]^n` (off `(ε/16, 1 - ε/16)^n`), with `|D η_ε| ≤ 2 / ε`
(`l1_eta_fderiv_bound`). -/
theorem lemma1_limit {m n : ℕ} {f : Matrix (Fin m) (Fin n) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin m) (Fin n) ℝ) {u : (Fin n → ℝ) → Fin m → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (hper : IsPeriodic u) :
    Tendsto (fun ε : ℝ => ∫ x in unitCube n, f (A + jac (l1_testMap u ε⁻¹) x)) (𝓝[>] 0)
      (𝓝 (∫ x in unitCube n, f (A + jac u x))) := by
  -- uniform bounds: `|u| ≤ U`, `|Du| ≤ D'` (and `|Dη_ε| ≤ 2 / ε`)
  obtain ⟨U, hU0, hU⟩ := l1_periodic_bounded hu.continuous hper
  have hDi : ∀ i, ∃ D, 0 ≤ D ∧ ∀ y, ‖fderiv ℝ (fun y => u y i) y‖ ≤ D := fun i =>
    l1_periodic_bounded (((contDiff_pi.1 hu) i).continuous_fderiv (by simp))
      (fun x z => l1_fderiv_periodic hper i x z)
  choose D hD0 hD using hDi
  set D' := ∑ i, D i
  have hD' : ∀ i y, ‖fderiv ℝ (fun y => u y i) y‖ ≤ D' := fun i y =>
    (hD i y).trans (Finset.single_le_sum (fun j _ => hD0 j) (Finset.mem_univ i))
  set R := D' + 2 * U
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
        hM _ (hmemS _ x fun i => l1_fderiv_testMap_bound hu hK hU hD' x i)
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
      filter_upwards [hev, eventually_ge_atTop 1] with K hK hK1
      show (0:ℝ) = f (A + jac (l1_testMap u K) x) - f (A + jac u ((K ^ 2) • x))
      rw [l1_jac_testMap_inner hu hK1 hK, sub_self]
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
`∫ f (A + D u_ε)` tend to `∫ f (A + D u) < f (A)` as `ε → 0⁺`, so one of them is `< f (A)`. The
cutoff `η_ε` (`l1_eta`) is the paper's: equal to `1` on `[ε, 1 - ε]^n`, vanishing in a
neighbourhood of the boundary of `[0, 1]^n` (off `(ε/16, 1 - ε/16)^n`), with `|D η_ε| ≤ 2 / ε`
(`l1_eta_fderiv_bound`). -/
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
