module

public import Morrey.Cassese.TwoByThree.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Lemma 5.1 (2): the analytic tools

The tools behind the proof of Lemma 5.1 (2) (`lemma5_1_part2`, in
`Morrey/Cassese/TwoByThree/Extension.lean`):

* the orthogonal projection `π` of `IsFrobProj` is linear (`tbt2_proj_add`, `tbt2_proj_smul`);
* for `f` `p`-homogeneous on `L` and `C²` away from the origin, the function
  `g = f ∘ π` on `V = Fin d → Fin m → ℝ` is differentiable everywhere and its derivative has the
  Lipschitz-type bound `‖Dg (Y) − Dg (Y')‖ ≤ C max (‖Y‖, ‖Y'‖)^{p−2} ‖Y − Y'‖` on `L`
  (`tbt2_lipschitz`);
* the comparison (28) for one step (`tbt2_comparison`), with the first-order cancellation;
* the uniform convexity (29) for one step (`tbt2_gain`), an elementary inequality;
* the absorption of (28) by (29) (`tbt2_absorb`);
* a continuous midpoint-convex function of one variable is convex (`tbt2_convexOn_of_midpoint`).

Helpers are prefixed `tbt2_`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-! ### The projection -/

variable {L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ)}
  {π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ}

theorem tbt2_proj_mem (hπ : IsFrobProj L π) (A : Matrix (Fin d) (Fin m) ℝ) : π A ∈ L :=
  (hπ A).1

theorem tbt2_proj_of_mem (hπ : IsFrobProj L π) {X : Matrix (Fin d) (Fin m) ℝ} (hX : X ∈ L) :
    π X = X :=
  tbt_proj_unique hπ X X hX fun Z _ => by simp [frobInner]

theorem tbt2_proj_add (hπ : IsFrobProj L π) (A B : Matrix (Fin d) (Fin m) ℝ) :
    π (A + B) = π A + π B :=
  tbt_proj_unique hπ _ _ (L.add_mem (hπ A).1 (hπ B).1) fun Z hZ => by
    rw [show A + B - (π A + π B) = (A - π A) + (B - π B) by abel, tbt_frobInner_add_left,
      (hπ A).2 Z hZ, (hπ B).2 Z hZ, add_zero]

theorem tbt2_proj_smul (hπ : IsFrobProj L π) (c : ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    π (c • A) = c • π A :=
  tbt_proj_unique hπ _ _ (L.smul_mem c (hπ A).1) fun Z hZ => by
    rw [show c • A - c • π A = c • (A - π A) by rw [smul_sub], tbt_frobInner_smul_left,
      (hπ A).2 Z hZ, mul_zero]

theorem tbt2_proj_sub (hπ : IsFrobProj L π) (A B : Matrix (Fin d) (Fin m) ℝ) :
    π (A - B) = π A - π B := by
  rw [sub_eq_add_neg, tbt2_proj_add hπ, show -B = (-1 : ℝ) • B by simp, tbt2_proj_smul hπ]
  simp [sub_eq_add_neg]

theorem tbt2_proj_zero (hπ : IsFrobProj L π) : π 0 = 0 := by
  simpa using tbt2_proj_smul hπ 0 0

/-! ### The ambient space `V = Fin d → Fin m → ℝ` -/

/-- `π` on `V`, as a continuous linear map. -/
noncomputable def tbt2_piV (hπ : IsFrobProj L π) : (Fin d → Fin m → ℝ) →L[ℝ] (Fin d → Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => Matrix.of.symm (π (Matrix.of Y))
      map_add' := fun Y Y' => by
        show Matrix.of.symm (π (Matrix.of Y + Matrix.of Y')) = _
        rw [tbt2_proj_add hπ]; rfl
      map_smul' := fun c Y => by
        show Matrix.of.symm (π (c • Matrix.of Y)) = _
        rw [tbt2_proj_smul hπ]; rfl }

theorem tbt2_piV_apply (hπ : IsFrobProj L π) (Y : Fin d → Fin m → ℝ) :
    tbt2_piV hπ Y = Matrix.of.symm (π (Matrix.of Y)) := rfl

/-- The sup norm of the entries is at most the Frobenius norm. -/
theorem tbt2_norm_le_frobNorm (A : Matrix (Fin d) (Fin m) ℝ) :
    ‖(Matrix.of.symm A : Fin d → Fin m → ℝ)‖ ≤ frobNorm A := by
  have h0 : 0 ≤ frobNorm A := Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg h0).mpr fun i => (pi_norm_le_iff_of_nonneg h0).mpr fun j => ?_
  rw [Real.norm_eq_abs, frobNorm, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have hi := Finset.single_le_sum (f := fun i => ∑ j, A i j ^ 2)
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)
  have hj := Finset.single_le_sum (f := fun j => A i j ^ 2) (fun j _ => sq_nonneg (A i j))
    (Finset.mem_univ j)
  exact hj.trans hi

theorem tbt2_of_piV (hπ : IsFrobProj L π) (Y : Fin d → Fin m → ℝ) :
    Matrix.of (tbt2_piV hπ Y) = π (Matrix.of Y) := by
  rw [tbt2_piV_apply, Equiv.apply_symm_apply]

theorem tbt2_piV_piV (hπ : IsFrobProj L π) (Y : Fin d → Fin m → ℝ) :
    tbt2_piV hπ (tbt2_piV hπ Y) = tbt2_piV hπ Y := by
  rw [tbt2_piV_apply, tbt2_of_piV, tbt2_proj_of_mem hπ (hπ _).1, tbt2_piV_apply]

theorem tbt2_piV_eq_iff (hπ : IsFrobProj L π) (Y : Fin d → Fin m → ℝ) :
    tbt2_piV hπ Y = Y ↔ Matrix.of Y ∈ L := by
  constructor
  · intro h; rw [← h, tbt2_of_piV]; exact (hπ _).1
  · intro h; rw [tbt2_piV_apply, tbt2_proj_of_mem hπ h]; rfl

theorem tbt2_piV_ne_zero_iff (hπ : IsFrobProj L π) (Y : Fin d → Fin m → ℝ) :
    π (Matrix.of Y) ≠ 0 ↔ tbt2_piV hπ Y ≠ 0 := by
  rw [tbt2_piV_apply, Ne, Ne, Equiv.symm_apply_eq]; rfl

theorem tbt2_isOpen (hπ : IsFrobProj L π) : IsOpen {X : Fin d → Fin m → ℝ | π (Matrix.of X) ≠ 0} := by
  have : {X : Fin d → Fin m → ℝ | π (Matrix.of X) ≠ 0} = {X | tbt2_piV hπ X ≠ 0} := by
    ext X; exact tbt2_piV_ne_zero_iff hπ X
  rw [this]
  exact isOpen_ne_fun (tbt2_piV hπ).continuous continuous_const

/-! ### `f ∘ π`: homogeneity, bounds and differentiability -/

section Smooth

variable (hπ : IsFrobProj L π) {p : ℝ} (hp : 2 ≤ p) {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
  (hhom : ∀ (t : ℝ), ∀ X ∈ L, f (t • X) = |t| ^ p * f X)
  (hC2 : ContDiffOn ℝ 2 (fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X)))
    {X | π (Matrix.of X) ≠ 0})
include hπ hp hhom

omit hπ in
theorem tbt2_f_zero : f 0 = 0 := by
  have := hhom 0 0 L.zero_mem
  rw [zero_smul, abs_zero, Real.zero_rpow (by linarith), zero_mul] at this
  exact this

omit hp in
theorem tbt2_g_smul (s : ℝ) (Y : Fin d → Fin m → ℝ) :
    f (π (Matrix.of (s • Y))) = |s| ^ p * f (π (Matrix.of Y)) := by
  rw [← Matrix.smul_of, tbt2_proj_smul hπ, hhom s _ (hπ _).1]

omit hp hhom in
theorem tbt2_g_eq_of_piV (Y : Fin d → Fin m → ℝ) :
    f (π (Matrix.of Y)) = f (π (Matrix.of (tbt2_piV hπ Y))) := by
  rw [tbt2_of_piV, tbt2_proj_of_mem hπ (hπ _).1]

include hC2

/-- `|f (π Y)| ≤ M₀ ‖π Y‖^p`. -/
theorem tbt2_bound_g : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ Y : Fin d → Fin m → ℝ,
    |f (π (Matrix.of Y))| ≤ M₀ * ‖tbt2_piV hπ Y‖ ^ p := by
  set S := {Y : Fin d → Fin m → ℝ | tbt2_piV hπ Y = Y} ∩ Metric.sphere 0 1
  have hS : IsCompact S :=
    (isCompact_sphere 0 1).inter_left (isClosed_eq (tbt2_piV hπ).continuous continuous_id)
  have hSU : S ⊆ {X | π (Matrix.of X) ≠ 0} := by
    intro Y ⟨h1, h2⟩
    rw [Set.mem_ofPred_eq, tbt2_piV_ne_zero_iff hπ, h1]
    intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at h2; exact zero_ne_one h2
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (hC2.continuousOn.mono hSU)
  refine ⟨max M 0, le_max_right _ _, fun Y => ?_⟩
  rw [tbt2_g_eq_of_piV hπ (f := f)]
  set Z := tbt2_piV hπ Y
  have hZ : tbt2_piV hπ Z = Z := tbt2_piV_piV hπ Y
  rcases eq_or_ne Z 0 with h0 | h0
  · rw [h0, show Matrix.of (0 : Fin d → Fin m → ℝ) = 0 from rfl, tbt2_proj_zero hπ,
      tbt2_f_zero hp hhom, abs_zero]
    exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hn : 0 < ‖Z‖ := norm_pos_iff.mpr h0
    set Zh := ‖Z‖⁻¹ • Z
    have hZh : Zh ∈ S := by
      refine ⟨?_, ?_⟩
      · show tbt2_piV hπ (‖Z‖⁻¹ • Z) = ‖Z‖⁻¹ • Z
        rw [map_smul, hZ]
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have e : Z = ‖Z‖ • Zh := by simp only [Zh, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [e, tbt2_g_smul hπ hhom, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_pos hn, mul_comm]
    have := hM Zh hZh
    rw [Real.norm_eq_abs] at this
    have hZhn : ‖‖Z‖ • Zh‖ = ‖Z‖ := by rw [← e]
    rw [hZhn]
    exact mul_le_mul_of_nonneg_right (this.trans (le_max_left _ _))
      (Real.rpow_nonneg hn.le _)

/-- Where `π Y = 0`, `f ∘ π` is differentiable with derivative `0` (`p > 1`). -/
theorem tbt2_hasFDerivAt_zero (Y : Fin d → Fin m → ℝ) (hY : tbt2_piV hπ Y = 0) :
    HasFDerivAt (fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X)))
      (0 : (Fin d → Fin m → ℝ) →L[ℝ] ℝ) Y := by
  obtain ⟨M₀, hM₀, hM⟩ := tbt2_bound_g hπ hp hhom hC2
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set B := M₀ * ‖tbt2_piV hπ‖ ^ p + 1
  have hB : 0 < B := by positivity
  have hr : 0 < min 1 (c / B) := lt_min one_pos (div_pos hc hB)
  filter_upwards [Metric.ball_mem_nhds (0 : Fin d → Fin m → ℝ) hr] with H hH
  rw [mem_ball_zero_iff, lt_min_iff] at hH
  have hgY : f (π (Matrix.of Y)) = 0 := by
    rw [tbt2_g_eq_of_piV hπ (f := f), hY, show Matrix.of (0 : Fin d → Fin m → ℝ) = 0 from rfl,
      tbt2_proj_zero hπ, tbt2_f_zero hp hhom]
  have hgYH : f (π (Matrix.of (Y + H))) = f (π (Matrix.of H)) := by
    rw [tbt2_g_eq_of_piV hπ (f := f), map_add, hY, zero_add, ← tbt2_g_eq_of_piV hπ (f := f)]
  simp only [zero_apply, sub_zero, hgY, hgYH, Real.norm_eq_abs]
  have hH0 := norm_nonneg H
  have h1 : |f (π (Matrix.of H))| ≤ M₀ * ‖tbt2_piV hπ‖ ^ p * ‖H‖ ^ p := by
    refine (hM H).trans ?_
    rw [mul_assoc, ← Real.mul_rpow (norm_nonneg _) hH0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
      ((tbt2_piV hπ).le_opNorm H) (by linarith)) hM₀
  have h2 : ‖H‖ ^ p ≤ ‖H‖ * ‖H‖ := by
    have := Real.rpow_le_rpow_of_exponent_ge' hH0 hH.1.le (by norm_num) hp
    rwa [Real.rpow_two, pow_two] at this
  have h3 : ‖H‖ * ‖H‖ ≤ c / B * ‖H‖ := mul_le_mul_of_nonneg_right hH.2.le hH0
  calc |f (π (Matrix.of H))| ≤ M₀ * ‖tbt2_piV hπ‖ ^ p * ‖H‖ ^ p := h1
    _ ≤ B * (c / B * ‖H‖) := by
        apply mul_le_mul (by linarith) (h2.trans h3) (Real.rpow_nonneg hH0 _) hB.le
    _ = c * ‖H‖ := by field_simp

theorem tbt2_differentiable :
    Differentiable ℝ fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X)) := by
  intro Y
  by_cases hY : π (Matrix.of Y) ≠ 0
  · exact (hC2.differentiableOn (by norm_num) Y hY).differentiableAt
      ((tbt2_isOpen hπ).mem_nhds hY)
  · push Not at hY
    exact (tbt2_hasFDerivAt_zero hπ hp hhom hC2 Y (by
      rw [tbt2_piV_apply, hY]; rfl)).differentiableAt

/-- `D g (s Y) = s^{p−1} D g (Y)` for `s > 0`. -/
theorem tbt2_fderiv_smul {s : ℝ} (hs : 0 < s) (Y : Fin d → Fin m → ℝ) :
    fderiv ℝ (fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X))) (s • Y) =
      s ^ (p - 1) • fderiv ℝ (fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X))) Y := by
  set g := fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X))
  have hg := tbt2_differentiable hπ hp hhom hC2
  have h1 : HasFDerivAt (fun Z => g (s • Z))
      ((fderiv ℝ g (s • Y)).comp (s • ContinuousLinearMap.id ℝ _)) Y :=
    (hg (s • Y)).hasFDerivAt.comp Y ((hasFDerivAt_id Y).const_smul s)
  have h2 : HasFDerivAt (fun Z => g (s • Z)) (s ^ p • fderiv ℝ g Y) Y := by
    have e : (fun Z => g (s • Z)) = fun Z => s ^ p * g Z := by
      funext Z; simp only [g, tbt2_g_smul hπ hhom, abs_of_pos hs]
    rw [e]
    exact (hg Y).hasFDerivAt.const_mul (s ^ p)
  have h := h1.unique h2
  ext v
  have hv := congrArg (fun L => L v) h
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, map_smul] at hv
  rw [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Real.rpow_sub_one hs.ne']
  field_simp
  linarith [hv]

theorem tbt2_fderiv_zero_of (Y : Fin d → Fin m → ℝ) (hY : tbt2_piV hπ Y = 0) :
    fderiv ℝ (fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X))) Y = 0 :=
  (tbt2_hasFDerivAt_zero hπ hp hhom hC2 Y hY).fderiv

/-- The Lipschitz-type bound on `D (f ∘ π)` along `L`:
`‖Dg (Y) − Dg (Y')‖ ≤ C max (‖Y‖, ‖Y'‖)^{p−2} ‖Y − Y'‖` (`C²` and homogeneity). -/
theorem tbt2_lipschitz : ∃ C : ℝ, 1 ≤ C ∧ ∀ Y Y' : Fin d → Fin m → ℝ,
    tbt2_piV hπ Y = Y → tbt2_piV hπ Y' = Y' →
    ‖fderiv ℝ (fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X))) Y -
      fderiv ℝ (fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X))) Y'‖ ≤
      C * max ‖Y‖ ‖Y'‖ ^ (p - 2) * ‖Y - Y'‖ := by
  set g := fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X)) with hg_def
  set U := {X : Fin d → Fin m → ℝ | π (Matrix.of X) ≠ 0}
  have hU : IsOpen U := tbt2_isOpen hπ
  have hmemU : ∀ Y, tbt2_piV hπ Y = Y → Y ≠ 0 → Y ∈ U := by
    intro Y h1 h2
    show π (Matrix.of Y) ≠ 0
    rw [tbt2_piV_ne_zero_iff hπ, h1]; exact h2
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ g) U := hC2.fderiv_of_isOpen hU (by norm_num)
  -- `M₁`: a bound for `Dg` on the unit sphere of `L`
  set S := {Y : Fin d → Fin m → ℝ | tbt2_piV hπ Y = Y} ∩ Metric.sphere 0 1
  have hS : IsCompact S :=
    (isCompact_sphere 0 1).inter_left (isClosed_eq (tbt2_piV hπ).continuous continuous_id)
  have hSU : S ⊆ U := fun Y ⟨h1, h2⟩ => hmemU Y h1 (by
    intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at h2; exact zero_ne_one h2)
  obtain ⟨M₁, hM₁⟩ := hS.exists_bound_of_continuousOn
    ((hC2.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hSU)
  set M₁' := max M₁ 0
  have hball : ∀ Z, tbt2_piV hπ Z = Z → ‖Z‖ ≤ 1 → ‖fderiv ℝ g Z‖ ≤ M₁' := by
    intro Z hZ hZ1
    rcases eq_or_ne Z 0 with h0 | h0
    · rw [tbt2_fderiv_zero_of hπ hp hhom hC2 Z (by rw [hZ, h0]), norm_zero]
      exact le_max_right _ _
    · have hn : 0 < ‖Z‖ := norm_pos_iff.mpr h0
      set Zh := ‖Z‖⁻¹ • Z
      have hZh : Zh ∈ S := by
        refine ⟨?_, ?_⟩
        · show tbt2_piV hπ (‖Z‖⁻¹ • Z) = ‖Z‖⁻¹ • Z
          rw [map_smul, hZ]
        · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have e : Z = ‖Z‖ • Zh := by simp only [Zh, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [e, tbt2_fderiv_smul hπ hp hhom hC2 hn, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hn.le _)]
      calc ‖Z‖ ^ (p - 1) * ‖fderiv ℝ g Zh‖ ≤ 1 * M₁' := by
            apply mul_le_mul (Real.rpow_le_one hn.le hZ1 (by linarith))
              ((hM₁ Zh hZh).trans (le_max_left _ _)) (norm_nonneg _) zero_le_one
        _ = M₁' := one_mul _
  -- `M₂`: a bound for `D²g` on the annulus `1/2 ≤ ‖Y‖ ≤ 1` of `L`
  set K := {Y : Fin d → Fin m → ℝ | tbt2_piV hπ Y = Y} ∩
    (Metric.closedBall 0 1 ∩ {Y | 1 / 2 ≤ ‖Y‖})
  have hK : IsCompact K := by
    refine IsCompact.inter_left ?_ (isClosed_eq (tbt2_piV hπ).continuous continuous_id)
    exact (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const continuous_norm)
  have hKU : K ⊆ U := fun Y ⟨h1, _, h3⟩ => hmemU Y h1 (by
    intro h; rw [h, Set.mem_ofPred_eq, norm_zero] at h3; norm_num at h3)
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn
    ((hD1.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  set M₂' := max M₂ 0
  set C₀ := max (4 * M₁') M₂'
  have hC₀ : 0 ≤ C₀ := le_max_of_le_right (le_max_right _ _)
  -- the bound at scale one
  have core1 : ∀ Y Y', tbt2_piV hπ Y = Y → tbt2_piV hπ Y' = Y' → ‖Y‖ = 1 → ‖Y'‖ ≤ 1 →
      ‖fderiv ℝ g Y - fderiv ℝ g Y'‖ ≤ C₀ * ‖Y - Y'‖ := by
    intro Y Y' hY hY' h1 h1'
    by_cases hfar : 1 / 2 ≤ ‖Y - Y'‖
    · calc ‖fderiv ℝ g Y - fderiv ℝ g Y'‖ ≤ ‖fderiv ℝ g Y‖ + ‖fderiv ℝ g Y'‖ := norm_sub_le _ _
        _ ≤ M₁' + M₁' := add_le_add (hball Y hY h1.le) (hball Y' hY' h1')
        _ ≤ 4 * M₁' * ‖Y - Y'‖ := by nlinarith [le_max_right M₁ 0]
        _ ≤ C₀ * ‖Y - Y'‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · push Not at hfar
      have hseg : segment ℝ Y Y' ⊆ K := by
        intro z hz
        obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
        refine ⟨?_, ?_, ?_⟩
        · show tbt2_piV hπ (a • Y + b • Y') = a • Y + b • Y'
          rw [map_add, map_smul, map_smul, hY, hY']
        · rw [mem_closedBall_zero_iff]
          calc ‖a • Y + b • Y'‖ ≤ a * ‖Y‖ + b * ‖Y'‖ := by
                refine (norm_add_le _ _).trans ?_
                rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
            _ ≤ a * 1 + b * 1 := by nlinarith
            _ = 1 := by linarith
        · show 1 / 2 ≤ ‖a • Y + b • Y'‖
          have e : a • Y + b • Y' = Y - b • (Y - Y') := by
            rw [show a = 1 - b by linarith]; module
          rw [e]
          have := norm_sub_norm_le Y (b • (Y - Y'))
          rw [norm_smul, Real.norm_of_nonneg hb] at this
          have hb1 : b ≤ 1 := by linarith
          nlinarith [norm_nonneg (Y - Y')]
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ g) (C := M₂')
        (fun z hz => (hD1.differentiableOn one_ne_zero z (hKU (hseg hz))).differentiableAt
          (hU.mem_nhds (hKU (hseg hz))))
        (fun z hz => (hM₂ z (hseg hz)).trans (le_max_left _ _)) (convex_segment Y Y')
        (left_mem_segment ℝ Y Y') (right_mem_segment ℝ Y Y')
      rw [norm_sub_rev, norm_sub_rev Y' Y] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have core : ∀ Y Y', tbt2_piV hπ Y = Y → tbt2_piV hπ Y' = Y' → max ‖Y‖ ‖Y'‖ = 1 →
      ‖fderiv ℝ g Y - fderiv ℝ g Y'‖ ≤ C₀ * ‖Y - Y'‖ := by
    intro Y Y' hY hY' hmax
    rcases le_total ‖Y'‖ ‖Y‖ with h | h
    · rw [max_eq_left h] at hmax
      exact core1 Y Y' hY hY' hmax (hmax ▸ h)
    · rw [max_eq_right h] at hmax
      rw [norm_sub_rev, norm_sub_rev Y Y']
      exact core1 Y' Y hY' hY hmax (hmax ▸ h)
  refine ⟨max C₀ 1, le_max_right _ _, fun Y Y' hY hY' => ?_⟩
  set μ := max ‖Y‖ ‖Y'‖
  have hμ0 : 0 ≤ μ := le_max_of_le_left (norm_nonneg _)
  rcases hμ0.lt_or_eq with hμ | hμ
  · set Yh := μ⁻¹ • Y
    set Yh' := μ⁻¹ • Y'
    have eY : Y = μ • Yh := by simp only [Yh, smul_smul, mul_inv_cancel₀ hμ.ne', one_smul]
    have eY' : Y' = μ • Yh' := by simp only [Yh', smul_smul, mul_inv_cancel₀ hμ.ne', one_smul]
    have hYh : tbt2_piV hπ Yh = Yh := by simp only [Yh, map_smul, hY]
    have hYh' : tbt2_piV hπ Yh' = Yh' := by simp only [Yh', map_smul, hY']
    have hmax : max ‖Yh‖ ‖Yh'‖ = 1 := by
      simp only [Yh, Yh', norm_smul, norm_inv, Real.norm_of_nonneg hμ0]
      rw [← mul_max_of_nonneg _ _ (inv_nonneg.mpr hμ0), inv_mul_cancel₀ hμ.ne']
    have hc := core Yh Yh' hYh hYh' hmax
    have hsub : ‖Y - Y'‖ = μ * ‖Yh - Yh'‖ := by
      rw [eY, eY', ← smul_sub, norm_smul, Real.norm_of_nonneg hμ0]
    rw [eY, eY', tbt2_fderiv_smul hπ hp hhom hC2 hμ, tbt2_fderiv_smul hπ hp hhom hC2 hμ,
      ← smul_sub, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hμ0 _), ← eY, ← eY', hsub]
    have e2 : μ ^ (p - 1) = μ ^ (p - 2) * μ := by
      rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one hμ.ne']
    rw [e2]
    have hp2 : 0 ≤ μ ^ (p - 2) := Real.rpow_nonneg hμ0 _
    calc μ ^ (p - 2) * μ * ‖fderiv ℝ g Yh - fderiv ℝ g Yh'‖
        ≤ μ ^ (p - 2) * μ * (C₀ * ‖Yh - Yh'‖) := by gcongr
      _ ≤ max C₀ 1 * μ ^ (p - 2) * (μ * ‖Yh - Yh'‖) := by
        have : C₀ ≤ max C₀ 1 := le_max_left _ _
        have h3 : 0 ≤ μ * ‖Yh - Yh'‖ := mul_nonneg hμ0 (norm_nonneg _)
        nlinarith [mul_nonneg hp2 h3]
  · have h0 : Y = 0 := norm_eq_zero.mp (le_antisymm (hμ ▸ le_max_left _ _) (norm_nonneg _))
    have h0' : Y' = 0 := norm_eq_zero.mp (le_antisymm (hμ ▸ le_max_right _ _) (norm_nonneg _))
    rw [h0, h0', sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (le_max_of_le_left
      (norm_nonneg _)) _)) (norm_nonneg _)

/-- (28) for one step, with the first-order cancellation (inventory E3): for `X, W, R_L ∈ L` and
`𝓔 = W − R_L`, `|f (X + W) + f (X − W) − f (X + R_L) − f (X − R_L)|
≤ 2 C (|X| + |W| + 2 |𝓔|)^{p−2} (|W| + 2 |𝓔|) |𝓔|`. The first-order terms `Dg (X) (±𝓔)` cancel
because the two points `X ± R_L` are symmetric about `X`. -/
theorem tbt2_comparison : ∃ C : ℝ, 1 ≤ C ∧ ∀ X W RL : Matrix (Fin d) (Fin m) ℝ, X ∈ L → W ∈ L →
    RL ∈ L →
    |(f (X + W) + f (X - W)) - (f (X + RL) + f (X - RL))| ≤
      2 * C * (frobNorm X + frobNorm W + 2 * frobNorm (W - RL)) ^ (p - 2) *
        (frobNorm W + 2 * frobNorm (W - RL)) * frobNorm (W - RL) := by
  obtain ⟨C, hC1, hC⟩ := tbt2_lipschitz hπ hp hhom hC2
  refine ⟨C, hC1, fun X W RL hX hW hRL => ?_⟩
  set g := fun Y : Fin d → Fin m → ℝ => f (π (Matrix.of Y)) with hg_def
  have hg := tbt2_differentiable hπ hp hhom hC2
  have hgZ : ∀ M ∈ L, g (Matrix.of.symm M) = f M := by
    intro M hM; simp only [g, Equiv.apply_symm_apply]; rw [tbt2_proj_of_mem hπ hM]
  set E := W - RL with hE
  have hEL : E ∈ L := L.sub_mem hW hRL
  set a := frobNorm X
  set w := frobNorm W
  set e := frobNorm E
  have hRLe : RL = W - E := by rw [hE]; abel
  -- `P s = X + R_L + s 𝓔`, `Q s = X − R_L − s 𝓔`
  set P : ℝ → Fin d → Fin m → ℝ := fun s => Matrix.of.symm (X + RL) + s • Matrix.of.symm E
  set Q : ℝ → Fin d → Fin m → ℝ := fun s => Matrix.of.symm (X - RL) - s • Matrix.of.symm E
  have hPm : ∀ s : ℝ, P s = Matrix.of.symm (X + RL + s • E) := fun s => rfl
  have hQm : ∀ s : ℝ, Q s = Matrix.of.symm (X - RL - s • E) := fun s => rfl
  have hPL : ∀ s : ℝ, tbt2_piV hπ (P s) = P s := fun s => by
    rw [tbt2_piV_eq_iff, hPm, Equiv.apply_symm_apply]
    exact L.add_mem (L.add_mem hX hRL) (L.smul_mem s hEL)
  have hQL : ∀ s : ℝ, tbt2_piV hπ (Q s) = Q s := fun s => by
    rw [tbt2_piV_eq_iff, hQm, Equiv.apply_symm_apply]
    exact L.sub_mem (L.sub_mem hX hRL) (L.smul_mem s hEL)
  set ψ : ℝ → ℝ := fun s => g (P s) + g (Q s)
  have hψ1 : ψ 1 = f (X + W) + f (X - W) := by
    simp only [ψ, hPm, hQm, one_smul]
    rw [show X + RL + E = X + W by rw [hRLe]; abel, show X - RL - E = X - W by rw [hRLe]; abel,
      hgZ _ (L.add_mem hX hW), hgZ _ (L.sub_mem hX hW)]
  have hψ0 : ψ 0 = f (X + RL) + f (X - RL) := by
    simp only [ψ, hPm, hQm, zero_smul, add_zero, sub_zero]
    rw [hgZ _ (L.add_mem hX hRL), hgZ _ (L.sub_mem hX hRL)]
  set ψ' : ℝ → ℝ := fun s =>
    fderiv ℝ g (P s) (Matrix.of.symm E) - fderiv ℝ g (Q s) (Matrix.of.symm E)
  have hder : ∀ s : ℝ, HasDerivAt ψ (ψ' s) s := by
    intro s
    have hP : HasDerivAt P (Matrix.of.symm E) s :=
      (((hasDerivAt_id s).smul_const (Matrix.of.symm E)).const_add
        (Matrix.of.symm (X + RL))).congr_deriv (by simp)
    have hQ : HasDerivAt Q (-Matrix.of.symm E) s :=
      (((hasDerivAt_id s).smul_const (Matrix.of.symm E)).const_sub
        (Matrix.of.symm (X - RL))).congr_deriv (by simp)
    have h1 := (hg (P s)).hasFDerivAt.comp_hasDerivAt s hP
    have h2 := (hg (Q s)).hasFDerivAt.comp_hasDerivAt s hQ
    have h3 := h1.add h2
    exact h3.congr_deriv (by simp [ψ', g, sub_eq_add_neg])
  have hnE : ‖Matrix.of.symm E‖ ≤ e := tbt2_norm_le_frobNorm E
  have hnX : ‖Matrix.of.symm X‖ ≤ a := tbt2_norm_le_frobNorm X
  have hnW : ‖Matrix.of.symm W‖ ≤ w := tbt2_norm_le_frobNorm W
  have hnRL : ‖Matrix.of.symm RL‖ ≤ w + e := by
    have : Matrix.of.symm RL = Matrix.of.symm W - Matrix.of.symm E := by rw [hRLe]; rfl
    rw [this]; exact (norm_sub_le _ _).trans (add_le_add hnW hnE)
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖ψ' s‖ ≤
      2 * C * (a + w + 2 * e) ^ (p - 2) * (w + 2 * e) * e := by
    intro s ⟨hs0, hs1⟩
    have hnP : ‖P s‖ ≤ a + w + 2 * e := by
      calc ‖P s‖ ≤ ‖Matrix.of.symm X‖ + ‖Matrix.of.symm RL‖ + s * ‖Matrix.of.symm E‖ := by
            have : P s = Matrix.of.symm X + Matrix.of.symm RL + s • Matrix.of.symm E := rfl
            rw [this]
            refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
            rw [norm_smul, Real.norm_of_nonneg hs0]
        _ ≤ a + (w + e) + 1 * e := by gcongr
        _ = a + w + 2 * e := by ring
    have hnQ : ‖Q s‖ ≤ a + w + 2 * e := by
      calc ‖Q s‖ ≤ ‖Matrix.of.symm X‖ + ‖Matrix.of.symm RL‖ + s * ‖Matrix.of.symm E‖ := by
            have : Q s = Matrix.of.symm X - Matrix.of.symm RL - s • Matrix.of.symm E := rfl
            rw [this]
            refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
            rw [norm_smul, Real.norm_of_nonneg hs0]
        _ ≤ a + (w + e) + 1 * e := by gcongr
        _ = a + w + 2 * e := by ring
    have hPQ : ‖P s - Q s‖ ≤ 2 * (w + 2 * e) := by
      have : P s - Q s = (2 : ℝ) • (Matrix.of.symm RL + s • Matrix.of.symm E) := by
        show Matrix.of.symm (X + RL) + s • Matrix.of.symm E -
          (Matrix.of.symm (X - RL) - s • Matrix.of.symm E) = _
        ext i j; simp only [Matrix.of_symm_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, Matrix.add_apply, Matrix.sub_apply]; ring
      rw [this, norm_smul, Real.norm_two]
      gcongr
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hs0]
      nlinarith [norm_nonneg (Matrix.of.symm E)]
    have hmax : max ‖P s‖ ‖Q s‖ ^ (p - 2) ≤ (a + w + 2 * e) ^ (p - 2) :=
      Real.rpow_le_rpow (le_max_of_le_left (norm_nonneg _)) (max_le hnP hnQ) (by linarith)
    have hL := hC (P s) (Q s) (hPL s) (hQL s)
    calc ‖ψ' s‖ = ‖(fderiv ℝ g (P s) - fderiv ℝ g (Q s)) (Matrix.of.symm E)‖ := rfl
      _ ≤ ‖fderiv ℝ g (P s) - fderiv ℝ g (Q s)‖ * ‖Matrix.of.symm E‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C * max ‖P s‖ ‖Q s‖ ^ (p - 2) * ‖P s - Q s‖) * e :=
        mul_le_mul hL hnE (norm_nonneg _) (by positivity)
      _ ≤ (C * (a + w + 2 * e) ^ (p - 2) * (2 * (w + 2 * e))) * e :=
        mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hmax (by linarith)) hPQ
          (norm_nonneg _) (mul_nonneg (by linarith) (Real.rpow_nonneg (by
            have : 0 ≤ a := Real.sqrt_nonneg _
            have : 0 ≤ w := Real.sqrt_nonneg _
            linarith) _))) he0
      _ = 2 * C * (a + w + 2 * e) ^ (p - 2) * (w + 2 * e) * e := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _ => (hder s).hasDerivWithinAt) hbound 1 (Set.right_mem_Icc.mpr zero_le_one)
  rw [hψ1, hψ0, Real.norm_eq_abs, sub_zero, mul_one] at key
  exact key

end Smooth

/-! ### (29) for one step: the elementary uniform convexity -/

/-- Bernoulli: `x^q + q x^{q−1} y ≤ (x + y)^q` for `x, y ≥ 0`, `q ≥ 1`. -/
theorem tbt2_bernoulli {q x y : ℝ} (hq : 1 ≤ q) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ q + q * x ^ (q - 1) * y ≤ (x + y) ^ q := by
  rcases hx.lt_or_eq with hx | rfl
  · have h := one_add_mul_self_le_rpow_one_add (s := y / x) (by
      have : 0 ≤ y / x := div_nonneg hy hx.le
      linarith) hq
    have e : x + y = x * (1 + y / x) := by field_simp
    rw [e, Real.mul_rpow hx.le (by positivity)]
    have e2 : x ^ (q - 1) = x ^ q / x := Real.rpow_sub_one hx.ne' q
    rw [e2]
    have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx q
    calc x ^ q + q * (x ^ q / x) * y = x ^ q * (1 + q * (y / x)) := by field_simp
      _ ≤ x ^ q * (1 + y / x) ^ q := mul_le_mul_of_nonneg_left h hxq.le
  · rcases hq.lt_or_eq with hq1 | rfl
    · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith), zero_add, zero_add,
        mul_zero, zero_mul]
      exact Real.rpow_nonneg hy q
    · simp

/-- (29) for one step: if `u + v = 2 (x + y)` (parallelogram), then
`u^q + v^q − 2 x^q ≥ x^{q−1} y + y^q` for `q ≥ 1`. -/
theorem tbt2_gain {q x y u v : ℝ} (hq : 1 ≤ q) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (huv : u + v = 2 * (x + y)) :
    x ^ (q - 1) * y + y ^ q ≤ u ^ q + v ^ q - 2 * x ^ q := by
  have hc := (convexOn_rpow hq).2 (Set.mem_Ici.mpr hu) (Set.mem_Ici.mpr hv)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [show 1 / 2 * u + 1 / 2 * v = x + y by linarith] at hc
  have hb := tbt2_bernoulli hq hx hy
  have hs := Real.add_rpow_le_rpow_add hx hy hq
  have h1 : x ^ (q - 1) * y ≤ q * x ^ (q - 1) * y := by
    have : 0 ≤ x ^ (q - 1) * y := mul_nonneg (Real.rpow_nonneg hx _) hy
    nlinarith
  linarith

/-! ### The absorption -/

theorem tbt2_aux_sq {B : ℝ} (hB : 1 ≤ B) : B ^ 2 + 8 * B ≤ B ^ 2 * (B + 2) ^ 2 := by
  have h1 : 8 * B ≤ 8 * B ^ 2 := by nlinarith
  have h2 : 9 ≤ (B + 2) ^ 2 := by nlinarith
  have h3 : 0 ≤ B ^ 2 := sq_nonneg B
  nlinarith

/-- The constant of Lemma 5.1 (2) from the Lipschitz constant `C` of `D (f ∘ π)` and `κ`. -/
noncomputable def tbt2_c0 (p C K : ℝ) : ℝ :=
  max (max 1 (2 * K)) (max (2 ^ (p - 1) * C * (2 ^ (p - 1) * C + 2) * K)
    (2 ^ (p - 1) * C * 2 ^ (p - 1) * K))

/-- The absorption of the error (28) by the gain (29), with `Λ ≥ c₀ / δ`. -/
theorem tbt2_absorb {p C K δ Λ a w e n x : ℝ} (hp : 2 ≤ p) (hC : 1 ≤ C) (hK : 0 ≤ K)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hΛ : tbt2_c0 p C K / δ ≤ Λ) (ha : 0 ≤ a) (hw : 0 ≤ w)
    (he : 0 ≤ e) (hn : 0 ≤ n) (hen : e ≤ K * n) (hx : a ^ 2 ≤ x) :
    2 * C * (a + w + 2 * e) ^ (p - 2) * (w + 2 * e) * e ≤
      δ * (x ^ (p / 2 - 1) * (w ^ 2 + Λ ^ 2 * n ^ 2) + (w ^ 2 + Λ ^ 2 * n ^ 2) ^ (p / 2)) := by
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ, B = 2 ^ (p - 1) * C := ⟨_, rfl⟩
  have h2p : (1 : ℝ) ≤ 2 ^ (p - 1) := Real.one_le_rpow (by norm_num) (by linarith)
  have hB1 : 1 ≤ B := by nlinarith
  obtain ⟨c₀, hc₀_def⟩ : ∃ c₀ : ℝ, c₀ = tbt2_c0 p C K := ⟨_, rfl⟩
  rw [← hc₀_def] at hΛ
  have hc1 : 1 ≤ c₀ := hc₀_def ▸ le_max_of_le_left (le_max_left _ _)
  have hc2 : 2 * K ≤ c₀ := hc₀_def ▸ le_max_of_le_left (le_max_right _ _)
  have hc3 : B * (B + 2) * K ≤ c₀ := hc₀_def ▸ hB_def ▸ le_max_of_le_right (le_max_left _ _)
  have hc4 : B * 2 ^ (p - 1) * K ≤ c₀ := hc₀_def ▸ hB_def ▸ le_max_of_le_right (le_max_right _ _)
  have hΛc : c₀ ≤ Λ := by
    calc c₀ ≤ c₀ / δ := by rw [le_div_iff₀ hδ]; nlinarith
      _ ≤ Λ := hΛ
  have hΛ0 : 0 < Λ := by linarith
  have hδΛ : c₀ ≤ δ * Λ := by rwa [div_le_iff₀ hδ, mul_comm] at hΛ
  obtain ⟨y, hy_def⟩ : ∃ y : ℝ, y = w ^ 2 + Λ ^ 2 * n ^ 2 := ⟨_, rfl⟩
  rw [← hy_def]
  have hy0 : 0 ≤ y := by rw [hy_def]; positivity
  have hRHS : 0 ≤ δ * (x ^ (p / 2 - 1) * y + y ^ (p / 2)) := by
    have hx0 : 0 ≤ x := (sq_nonneg a).trans hx
    have := Real.rpow_nonneg hx0 (p / 2 - 1)
    have := Real.rpow_nonneg hy0 (p / 2)
    positivity
  rcases he.lt_or_eq with he' | rfl
  swap
  · simpa using hRHS
  have hx0 : 0 ≤ x := (sq_nonneg a).trans hx
  have hp2 : 0 ≤ p - 2 := by linarith
  have h2pm : (2 : ℝ) ^ (p - 1) = 2 ^ (p - 2) * 2 := by
    rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one (by norm_num)]
  by_cases hcase : w + 2 * e ≤ a
  · -- Case 1: use the term `x^{p/2-1} (w² + Λ² n²)` with `x^{p/2-1} ≥ a^{p-2}`
    have hapow : (a + w + 2 * e) ^ (p - 2) ≤ 2 ^ (p - 2) * a ^ (p - 2) := by
      rw [← Real.mul_rpow (by norm_num) ha]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hp2
    have hxpow : a ^ (p - 2) ≤ x ^ (p / 2 - 1) := by
      have : a ^ (p - 2) = (a ^ 2) ^ (p / 2 - 1) := by
        rw [← Real.rpow_two, ← Real.rpow_mul ha]; congr 1; ring
      rw [this]
      exact Real.rpow_le_rpow (sq_nonneg a) hx (by linarith)
    have hap : 0 ≤ a ^ (p - 2) := Real.rpow_nonneg ha _
    -- `B (w + 2e) e ≤ δ y`
    have he2 : e ^ 2 ≤ K ^ 2 * n ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ he hen 2
    have hΛ2 : (B * (B + 2) * K) ^ 2 ≤ (δ * Λ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hc3.trans hδΛ) 2
    have key : B * (w + 2 * e) * e ≤ δ * y := by
      have t1 : 4 * δ * (B * w * e) ≤ 4 * δ ^ 2 * w ^ 2 + B ^ 2 * e ^ 2 := by
        linear_combination sq_nonneg (2 * δ * w - B * e)
      have hBe : 0 ≤ B * e ^ 2 := by positivity
      have t2 : δ * (B * e ^ 2) ≤ B * e ^ 2 := mul_le_of_le_one_left hBe hδ1.le
      have t3 : (B ^ 2 + 8 * B) * e ^ 2 ≤ (B ^ 2 + 8 * B) * (K ^ 2 * n ^ 2) :=
        mul_le_mul_of_nonneg_left he2 (by positivity)
      have t4 : (B ^ 2 + 8 * B) * K ^ 2 ≤ (δ * Λ) ^ 2 := by
        have h1 : B ^ 2 + 8 * B ≤ B ^ 2 * (B + 2) ^ 2 := tbt2_aux_sq hB1
        have h2 : (B ^ 2 + 8 * B) * K ^ 2 ≤ B ^ 2 * (B + 2) ^ 2 * K ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg K)
        have h3 : B ^ 2 * (B + 2) ^ 2 * K ^ 2 = (B * (B + 2) * K) ^ 2 := by ring
        linarith
      have t5 : (B ^ 2 + 8 * B) * (K ^ 2 * n ^ 2) ≤ 4 * δ ^ 2 * (Λ ^ 2 * n ^ 2) := by
        have : (B ^ 2 + 8 * B) * (K ^ 2 * n ^ 2) = (B ^ 2 + 8 * B) * K ^ 2 * n ^ 2 := by ring
        rw [this]
        have h6 : (δ * Λ) ^ 2 * n ^ 2 ≤ 4 * δ ^ 2 * (Λ ^ 2 * n ^ 2) := by
          have : (δ * Λ) ^ 2 * n ^ 2 = δ ^ 2 * (Λ ^ 2 * n ^ 2) := by ring
          rw [this]
          have : 0 ≤ δ ^ 2 * (Λ ^ 2 * n ^ 2) := by positivity
          linarith
        exact (mul_le_mul_of_nonneg_right t4 (sq_nonneg n)).trans h6
      have t6 : 4 * δ * (B * (w + 2 * e) * e) ≤ 4 * δ * (δ * y) := by
        have e1 : 4 * δ * (B * (w + 2 * e) * e) = 4 * δ * (B * w * e) + 8 * (δ * (B * e ^ 2)) := by
          ring
        have e2 : 4 * δ * (δ * y) = 4 * δ ^ 2 * w ^ 2 + 4 * δ ^ 2 * (Λ ^ 2 * n ^ 2) := by
          rw [hy_def]; ring
        rw [e1, e2]
        linear_combination t1 + 8 * t2 + t3 + t5
      exact le_of_mul_le_mul_left t6 (by positivity)
    calc 2 * C * (a + w + 2 * e) ^ (p - 2) * (w + 2 * e) * e
        ≤ 2 * C * (2 ^ (p - 2) * a ^ (p - 2)) * (w + 2 * e) * e := by gcongr
      _ = a ^ (p - 2) * (B * (w + 2 * e) * e) := by rw [hB_def, h2pm]; ring
      _ ≤ a ^ (p - 2) * (δ * y) := mul_le_mul_of_nonneg_left key hap
      _ ≤ x ^ (p / 2 - 1) * (δ * y) := mul_le_mul_of_nonneg_right hxpow (by positivity)
      _ ≤ δ * (x ^ (p / 2 - 1) * y + y ^ (p / 2)) := by
        have : 0 ≤ δ * y ^ (p / 2) := mul_nonneg hδ.le (Real.rpow_nonneg hy0 _)
        rw [mul_add]; linarith
  · -- Case 2: use the term `(w² + Λ² n²)^{p/2}`
    push Not at hcase
    obtain ⟨S, hS_def⟩ : ∃ S : ℝ, S = √y := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := hS_def ▸ Real.sqrt_nonneg _
    have hSy : S ^ 2 = y := hS_def ▸ Real.sq_sqrt hy0
    have hwS : w ≤ S := by
      rw [show w = √(w ^ 2) from (Real.sqrt_sq hw).symm, hS_def]
      exact Real.sqrt_le_sqrt (by rw [hy_def]; exact le_add_of_nonneg_right (by positivity))
    have hnS : Λ * n ≤ S := by
      rw [show Λ * n = √((Λ * n) ^ 2) from (Real.sqrt_sq (by positivity)).symm, hS_def]
      exact Real.sqrt_le_sqrt (by rw [hy_def, mul_pow]; exact le_add_of_nonneg_left (sq_nonneg w))
    have h2e : 2 * e ≤ S := by
      calc 2 * e ≤ 2 * K * n := by linarith
        _ ≤ Λ * n := mul_le_mul_of_nonneg_right (hc2.trans hΛc) hn
        _ ≤ S := hnS
    have hpow1 : (a + w + 2 * e) ^ (p - 2) ≤ 2 ^ (p - 2) * (w + 2 * e) ^ (p - 2) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hp2
    have hwe : 0 < w + 2 * e := by linarith
    have hpow2 : (w + 2 * e) ^ (p - 2) * (w + 2 * e) ≤ 2 ^ (p - 1) * S ^ (p - 1) := by
      rw [← Real.rpow_add_one hwe.ne', show p - 2 + 1 = p - 1 by ring,
        ← Real.mul_rpow (by norm_num) hS0]
      exact Real.rpow_le_rpow hwe.le (by linarith) (by linarith)
    have heS : e * Λ ≤ K * S := by
      calc e * Λ ≤ K * n * Λ := mul_le_mul_of_nonneg_right hen hΛ0.le
        _ = K * (Λ * n) := by ring
        _ ≤ K * S := mul_le_mul_of_nonneg_left hnS hK
    have hSpos : 0 < S := by linarith
    have hSp : S ^ (p - 1) * S = y ^ (p / 2) := by
      rw [← Real.rpow_add_one hSpos.ne', show p - 1 + 1 = p by ring, ← hSy, ← Real.rpow_two,
        ← Real.rpow_mul hS0]
      congr 1; ring
    have hSp1 : 0 ≤ S ^ (p - 1) := Real.rpow_nonneg hS0 _
    calc 2 * C * (a + w + 2 * e) ^ (p - 2) * (w + 2 * e) * e
        ≤ 2 * C * (2 ^ (p - 2) * (w + 2 * e) ^ (p - 2)) * (w + 2 * e) * e := by gcongr
      _ = B * ((w + 2 * e) ^ (p - 2) * (w + 2 * e)) * e := by rw [hB_def, h2pm]; ring
      _ ≤ B * (2 ^ (p - 1) * S ^ (p - 1)) * e := by gcongr
      _ = B * 2 ^ (p - 1) * S ^ (p - 1) * (e * Λ) / Λ := by field_simp
      _ ≤ B * 2 ^ (p - 1) * S ^ (p - 1) * (K * S) / Λ := by
        apply div_le_div_of_nonneg_right _ hΛ0.le
        exact mul_le_mul_of_nonneg_left heS (by positivity)
      _ = (B * 2 ^ (p - 1) * K) * (S ^ (p - 1) * S) / Λ := by ring
      _ ≤ (δ * Λ) * (S ^ (p - 1) * S) / Λ := by
        apply div_le_div_of_nonneg_right _ hΛ0.le
        exact mul_le_mul_of_nonneg_right (hc4.trans hδΛ) (by positivity)
      _ = δ * y ^ (p / 2) := by rw [hSp]; field_simp
      _ ≤ δ * (x ^ (p / 2 - 1) * y + y ^ (p / 2)) := by
        have : 0 ≤ δ * (x ^ (p / 2 - 1) * y) :=
          mul_nonneg hδ.le (mul_nonneg (Real.rpow_nonneg hx0 _) hy0)
        rw [mul_add]; linarith

/-! ### Midpoint convexity -/

/-- A continuous midpoint-convex function of one variable is convex. -/
theorem tbt2_convexOn_of_midpoint {φ : ℝ → ℝ} (hc : Continuous φ)
    (hmid : ∀ x h : ℝ, 2 * φ x ≤ φ (x + h) + φ (x - h)) : ConvexOn ℝ Set.univ φ := by
  -- below the chord on `[x, y]`
  have core : ∀ x y : ℝ, x < y → ∀ z ∈ Set.Icc x y,
      φ z ≤ φ x + (z - x) / (y - x) * (φ y - φ x) := by
    intro x y hxy z hz
    set ψ : ℝ → ℝ := fun t => φ t - (φ x + (t - x) / (y - x) * (φ y - φ x)) with hψ
    have hψc : Continuous ψ := by
      have : y - x ≠ 0 := by linarith
      fun_prop
    have hψx : ψ x = 0 := by simp [ψ]
    have hψy : ψ y = 0 := by
      simp only [ψ]; field_simp [show y - x ≠ 0 by linarith]; ring
    have hψmid : ∀ t h : ℝ, 2 * ψ t ≤ ψ (t + h) + ψ (t - h) := by
      intro t h
      have := hmid t h
      simp only [ψ]
      have e : (t + h - x) / (y - x) * (φ y - φ x) + (t - h - x) / (y - x) * (φ y - φ x) =
          2 * ((t - x) / (y - x) * (φ y - φ x)) := by
        field_simp [show y - x ≠ 0 by linarith]; ring
      linarith
    by_contra hlt
    push Not at hlt
    have hz0 : 0 < ψ z := by simp only [ψ]; linarith
    obtain ⟨z₀, hz₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hxy.le)
      hψc.continuousOn
    set M := ψ z₀
    have hM : 0 < M := lt_of_lt_of_le hz0 (hmax hz)
    set T := Set.Icc x y ∩ ψ ⁻¹' {M}
    have hT : IsCompact T := isCompact_Icc.inter_right (isClosed_singleton.preimage hψc)
    obtain ⟨t₀, ht₀, hmin⟩ := hT.exists_isMinOn ⟨z₀, hz₀, rfl⟩ continuous_id.continuousOn
    have hψt₀ : ψ t₀ = M := ht₀.2
    have hx₀ : x < t₀ := by
      rcases ht₀.1.1.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h, hψx] at hψt₀; linarith
    have hy₀ : t₀ < y := by
      rcases ht₀.1.2.lt_or_eq with h | h
      · exact h
      · exfalso; rw [h, hψy] at hψt₀; linarith
    set h := min (t₀ - x) (y - t₀)
    have hh : 0 < h := lt_min (by linarith) (by linarith)
    have h1 : t₀ + h ∈ Set.Icc x y := ⟨by linarith, by linarith [min_le_right (t₀ - x) (y - t₀)]⟩
    have h2 : t₀ - h ∈ Set.Icc x y := ⟨by linarith [min_le_left (t₀ - x) (y - t₀)], by linarith⟩
    have hle1 : ψ (t₀ + h) ≤ M := hmax h1
    have hlt2 : ψ (t₀ - h) < M := by
      rcases (hmax h2 : ψ (t₀ - h) ≤ M).lt_or_eq with hl | he
      · exact hl
      · exfalso
        have h3 : t₀ ≤ t₀ - h := hmin ⟨h2, he⟩
        linarith
    have := hψmid t₀ h
    linarith
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  obtain rfl : a = 1 - b := by linarith
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have hz : (1 - b) * x + b * y ∈ Set.Icc x y := by
      have h1 := mul_nonneg hb (sub_nonneg.2 hxy.le)
      have h2 := mul_nonneg ha (sub_nonneg.2 hxy.le)
      constructor <;> linarith
    have := core x y hxy _ hz
    have e : ((1 - b) * x + b * y - x) / (y - x) = b := by
      field_simp [show y - x ≠ 0 by linarith]; ring
    rw [e] at this
    linarith
  · ring_nf; rfl
  · have hz : (1 - b) * x + b * y ∈ Set.Icc y x := by
      have h1 := mul_nonneg hb (sub_nonneg.2 hxy.le)
      have h2 := mul_nonneg ha (sub_nonneg.2 hxy.le)
      constructor <;> linarith
    have := core y x hxy _ hz
    have e : ((1 - b) * x + b * y - y) / (x - y) = 1 - b := by
      field_simp [show x - y ≠ 0 by linarith]; ring
    rw [e] at this
    linarith

/-! ### One step of the argument: the midpoint inequality for (26) -/

theorem tbt2_parallelogram (P V : Matrix (Fin d) (Fin m) ℝ) :
    frobSq (P + V) + frobSq (P - V) = 2 * frobSq P + 2 * frobSq V := by
  simp only [frobSq, Matrix.add_apply, Matrix.sub_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tbt2_frobNorm_sq (A : Matrix (Fin d) (Fin m) ℝ) : frobNorm A ^ 2 = frobSq A :=
  Real.sq_sqrt (tbt_frobSq_nonneg A)

/-- The midpoint inequality `2 F (A) ≤ F (A + R) + F (A − R)` for the map (26) and a rank-one
`R`: the argument of the paper for a one-step rank-one martingale `M₁ = A ± R`. -/
theorem tbt2_midpoint (hπ : IsFrobProj L π) (κ : ℝ) (hκ : HasRankOneCorrection L π κ) {p : ℝ}
    (hp : 2 ≤ p) {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hrc : ∀ X ∈ L, ∀ R ∈ L, R.rank = 1 → ConvexOn ℝ Set.univ fun t : ℝ => f (X + t • R))
    {C : ℝ} (hC1 : 1 ≤ C)
    (hcmp : ∀ X W RL : Matrix (Fin d) (Fin m) ℝ, X ∈ L → W ∈ L → RL ∈ L →
      |(f (X + W) + f (X - W)) - (f (X + RL) + f (X - RL))| ≤
        2 * C * (frobNorm X + frobNorm W + 2 * frobNorm (W - RL)) ^ (p - 2) *
          (frobNorm W + 2 * frobNorm (W - RL)) * frobNorm (W - RL))
    {δ Λ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hΛ : tbt2_c0 p C |κ| / δ ≤ Λ)
    (A R : Matrix (Fin d) (Fin m) ℝ) (hR : R.rank = 1) :
    2 * (f (π A) + δ * (frobSq (π A) + Λ ^ 2 * frobSq (A - π A)) ^ (p / 2)) ≤
      (f (π (A + R)) + δ * (frobSq (π (A + R)) + Λ ^ 2 * frobSq (A + R - π (A + R))) ^ (p / 2)) +
      (f (π (A - R)) + δ * (frobSq (π (A - R)) + Λ ^ 2 * frobSq (A - R - π (A - R))) ^ (p / 2)) := by
  obtain ⟨RL, hRL, hRL1, hRLb⟩ := hκ R hR
  set X := π A with hX_def
  set W := π R with hW_def
  have hXL : X ∈ L := (hπ A).1
  have hWL : W ∈ L := (hπ R).1
  rw [tbt2_proj_add hπ, tbt2_proj_sub hπ, ← hX_def, ← hW_def]
  set N := R - W
  set NA := A - X
  rw [show A + R - (X + W) = NA + N by simp only [NA, N]; abel,
    show A - R - (X - W) = NA - N by simp only [NA, N]; abel]
  -- (a): rank-one convexity on `L`, `f (X + R_L) + f (X − R_L) ≥ 2 f (X)`
  have ha : 2 * f X ≤ f (X + RL) + f (X - RL) := by
    have := (hrc X hXL RL hRL hRL1).2 (Set.mem_univ (1 : ℝ)) (Set.mem_univ (-1 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul, one_smul, neg_smul, ← sub_eq_add_neg] at this
    norm_num at this
    linarith
  -- (28)
  have hc := hcmp X W RL hXL hWL hRL
  -- (29)
  set x := frobSq X + Λ ^ 2 * frobSq NA
  set y := frobSq W + Λ ^ 2 * frobSq N
  have hgain := tbt2_gain (q := p / 2) (x := x) (y := y)
    (u := frobSq (X + W) + Λ ^ 2 * frobSq (NA + N)) (v := frobSq (X - W) + Λ ^ 2 * frobSq (NA - N))
    (by linarith)
    (add_nonneg (tbt_frobSq_nonneg _) (mul_nonneg (sq_nonneg _) (tbt_frobSq_nonneg _)))
    (add_nonneg (tbt_frobSq_nonneg _) (mul_nonneg (sq_nonneg _) (tbt_frobSq_nonneg _)))
    (add_nonneg (tbt_frobSq_nonneg _) (mul_nonneg (sq_nonneg _) (tbt_frobSq_nonneg _)))
    (add_nonneg (tbt_frobSq_nonneg _) (mul_nonneg (sq_nonneg _) (tbt_frobSq_nonneg _)))
    (by
      have h1 := tbt2_parallelogram X W
      have h2 := tbt2_parallelogram NA N
      simp only [x, y]
      linear_combination h1 + Λ ^ 2 * h2)
  -- the absorption
  have hen : frobNorm (W - RL) ≤ |κ| * frobNorm N :=
    hRLb.trans (mul_le_mul_of_nonneg_right (le_abs_self κ) (Real.sqrt_nonneg _))
  have hab := tbt2_absorb (a := frobNorm X) (w := frobNorm W) (e := frobNorm (W - RL))
    (n := frobNorm N) (x := x) hp hC1 (abs_nonneg κ) hδ hδ1 hΛ (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hen (by
      rw [tbt2_frobNorm_sq]
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (tbt_frobSq_nonneg _)))
  rw [tbt2_frobNorm_sq, tbt2_frobNorm_sq] at hab
  have habs := neg_abs_le ((f (X + W) + f (X - W)) - (f (X + RL) + f (X - RL)))
  have hδg := mul_le_mul_of_nonneg_left hgain hδ.le
  nlinarith

end Cassese
