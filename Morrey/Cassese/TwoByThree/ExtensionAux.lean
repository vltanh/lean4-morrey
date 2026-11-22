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
  (`tbt2_lipschitz`), across the origin too;
* the second-order remainder of (28), `|f (X + W) − f (X + W − 𝓔) − Df (X) 𝓔|`, with the
  first-order term taken at the starting point `X` (`tbt2_taylor`), and its splitting "for every
  `0 < ε ≤ 1`" (`tbt2_young`);
* the uniform convexity of `|·|^p` behind (29), pointwise with its first-order term
  (`tbt2_gain`);
* a continuous midpoint-convex function of one variable is convex (`tbt2_convexOn_of_midpoint`,
  used by `Morrey/Cassese/TwoByThree/Folklore.lean`).

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

/-- The second-order remainder in (28), with the first-order term taken at the starting point
`X`: for `X, W, 𝓔 ∈ L`, `|f (X + W) − f (X + W − 𝓔) − Df (X) 𝓔|
≤ C (|X| + |W| + |𝓔|)^{p−2} (|W| + |𝓔|) |𝓔|`. Along the segment from `X + W − 𝓔` to `X + W`,
`Df (·) − Df (X)` is controlled by the Lipschitz-type bound `tbt2_lipschitz`. -/
theorem tbt2_taylor : ∃ C : ℝ, 1 ≤ C ∧ ∀ X W E : Matrix (Fin d) (Fin m) ℝ, X ∈ L → W ∈ L →
    E ∈ L →
    |f (X + W) - f (X + W - E) -
        fderiv ℝ (fun Y : Fin d → Fin m → ℝ => f (π (Matrix.of Y))) (Matrix.of.symm X)
          (Matrix.of.symm E)| ≤
      C * (frobNorm X + frobNorm W + frobNorm E) ^ (p - 2) * (frobNorm W + frobNorm E) *
        frobNorm E := by
  obtain ⟨C, hC1, hC⟩ := tbt2_lipschitz hπ hp hhom hC2
  refine ⟨C, hC1, fun X W E hX hW hE => ?_⟩
  set g := fun Y : Fin d → Fin m → ℝ => f (π (Matrix.of Y)) with hg_def
  have hg := tbt2_differentiable hπ hp hhom hC2
  have hgZ : ∀ M ∈ L, g (Matrix.of.symm M) = f M := by
    intro M hM; simp only [g, Equiv.apply_symm_apply]; rw [tbt2_proj_of_mem hπ hM]
  set ℓ := fderiv ℝ g (Matrix.of.symm X)
  set a := frobNorm X
  set w := frobNorm W
  set e := frobNorm E
  -- `P s = X + W − 𝓔 + s 𝓔`
  set P : ℝ → Fin d → Fin m → ℝ := fun s => Matrix.of.symm (X + W - E) + s • Matrix.of.symm E
  have hPm : ∀ s : ℝ, P s = Matrix.of.symm (X + W - E + s • E) := fun s => rfl
  have hPL : ∀ s : ℝ, tbt2_piV hπ (P s) = P s := fun s => by
    rw [tbt2_piV_eq_iff, hPm, Equiv.apply_symm_apply]
    exact L.add_mem (L.sub_mem (L.add_mem hX hW) hE) (L.smul_mem s hE)
  have hXL : tbt2_piV hπ (Matrix.of.symm X) = Matrix.of.symm X := by
    rw [tbt2_piV_eq_iff, Equiv.apply_symm_apply]; exact hX
  set ψ : ℝ → ℝ := fun s => g (P s) - s * ℓ (Matrix.of.symm E)
  have hψ1 : ψ 1 = f (X + W) - ℓ (Matrix.of.symm E) := by
    simp only [ψ, hPm, one_smul, one_mul, sub_add_cancel]
    rw [hgZ _ (L.add_mem hX hW)]
  have hψ0 : ψ 0 = f (X + W - E) := by
    simp only [ψ, hPm, zero_smul, add_zero, zero_mul, sub_zero]
    rw [hgZ _ (L.sub_mem (L.add_mem hX hW) hE)]
  set ψ' : ℝ → ℝ := fun s => fderiv ℝ g (P s) (Matrix.of.symm E) - ℓ (Matrix.of.symm E)
  have hder : ∀ s : ℝ, HasDerivAt ψ (ψ' s) s := by
    intro s
    have hP : HasDerivAt P (Matrix.of.symm E) s :=
      (((hasDerivAt_id s).smul_const (Matrix.of.symm E)).const_add
        (Matrix.of.symm (X + W - E))).congr_deriv (by simp)
    have h1 := (hg (P s)).hasFDerivAt.comp_hasDerivAt s hP
    have h2 := h1.sub ((hasDerivAt_id s).mul_const (ℓ (Matrix.of.symm E)))
    exact h2.congr_deriv (by simp only [one_mul, ψ']; rfl)
  have hnE : ‖(Matrix.of.symm E : Fin d → Fin m → ℝ)‖ ≤ e := tbt2_norm_le_frobNorm E
  have hnX : ‖(Matrix.of.symm X : Fin d → Fin m → ℝ)‖ ≤ a := tbt2_norm_le_frobNorm X
  have hnW : ‖(Matrix.of.symm W : Fin d → Fin m → ℝ)‖ ≤ w := tbt2_norm_le_frobNorm W
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖ψ' s‖ ≤
      C * (a + w + e) ^ (p - 2) * (w + e) * e := by
    intro s ⟨hs0, hs1⟩
    have hPs : P s - Matrix.of.symm X = Matrix.of.symm W - (1 - s) • Matrix.of.symm E := by
      ext i j
      simp only [P, Matrix.of_symm_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.add_apply, Matrix.sub_apply]
      ring
    have hsub : ‖P s - Matrix.of.symm X‖ ≤ w + e := by
      rw [hPs]
      refine (norm_sub_le _ _).trans (add_le_add hnW ?_)
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      nlinarith [norm_nonneg (Matrix.of.symm E : Fin d → Fin m → ℝ)]
    have hnP : ‖P s‖ ≤ a + w + e := by
      have : P s = Matrix.of.symm X + (P s - Matrix.of.symm X) := by abel
      rw [this]
      refine (norm_add_le _ _).trans ?_
      linarith
    have hmax : max ‖P s‖ ‖(Matrix.of.symm X : Fin d → Fin m → ℝ)‖ ^ (p - 2) ≤
        (a + w + e) ^ (p - 2) :=
      Real.rpow_le_rpow (le_max_of_le_left (norm_nonneg _)) (max_le hnP (by linarith))
        (by linarith)
    have hL := hC (P s) (Matrix.of.symm X) (hPL s) hXL
    calc ‖ψ' s‖ = ‖(fderiv ℝ g (P s) - ℓ) (Matrix.of.symm E)‖ := rfl
      _ ≤ ‖fderiv ℝ g (P s) - ℓ‖ * ‖(Matrix.of.symm E : Fin d → Fin m → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C * max ‖P s‖ ‖(Matrix.of.symm X : Fin d → Fin m → ℝ)‖ ^ (p - 2) *
            ‖P s - Matrix.of.symm X‖) * e :=
        mul_le_mul hL hnE (norm_nonneg _) (by positivity)
      _ ≤ (C * (a + w + e) ^ (p - 2) * (w + e)) * e :=
        mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hmax (by linarith))
          hsub (norm_nonneg _) (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _))) he0
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _ => (hder s).hasDerivWithinAt) hbound 1 (Set.right_mem_Icc.mpr zero_le_one)
  rw [hψ1, hψ0, Real.norm_eq_abs, sub_zero, mul_one] at key
  rw [show f (X + W) - f (X + W - E) - ℓ (Matrix.of.symm E) =
    f (X + W) - ℓ (Matrix.of.symm E) - f (X + W - E) by ring]
  exact key

end Smooth

/-! ### Real inequalities: the splitting of (28) and the uniform convexity (29) -/

/-- Bernoulli: `x^q + q x^{q−1} y ≤ (x + y)^q` for `x ≥ 0`, `x + y ≥ 0`, `q ≥ 1` (the tangent
line of the convex `t ↦ t^q` at `x`). -/
theorem tbt2_bernoulli {q x y : ℝ} (hq : 1 ≤ q) (hx : 0 ≤ x) (hxy : 0 ≤ x + y) :
    x ^ q + q * x ^ (q - 1) * y ≤ (x + y) ^ q := by
  rcases hx.lt_or_eq with hx | rfl
  · have h := one_add_mul_self_le_rpow_one_add (s := y / x) (by
      rw [le_div_iff₀ hx]; linarith) hq
    have e : x + y = x * (1 + y / x) := by field_simp
    have h1 : 0 ≤ 1 + y / x := by
      have : 0 ≤ (x + y) / x := div_nonneg hxy hx.le
      rwa [add_div, div_self hx.ne'] at this
    rw [e, Real.mul_rpow hx.le h1]
    have e2 : x ^ (q - 1) = x ^ q / x := Real.rpow_sub_one hx.ne' q
    rw [e2]
    have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx q
    calc x ^ q + q * (x ^ q / x) * y = x ^ q * (1 + q * (y / x)) := by field_simp
      _ ≤ x ^ q * (1 + y / x) ^ q := mul_le_mul_of_nonneg_left h hxq.le
  · rw [zero_add] at hxy ⊢
    rcases hq.lt_or_eq with hq1 | rfl
    · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith), zero_add,
        mul_zero, zero_mul]
      exact Real.rpow_nonneg hxy q
    · simp

/-- `t^q = t^{q−1} t` for `t ≥ 0`, `q ≥ 1`. -/
theorem tbt2_rpow_eq_mul {q t : ℝ} (hq : 1 ≤ q) (ht : 0 ≤ t) : t ^ q = t ^ (q - 1) * t := by
  conv_lhs => rw [show q = (q - 1) + 1 by ring]
  rw [Real.rpow_add' ht (by linarith), Real.rpow_one]

/-- The uniform convexity of `|·|^p` behind (29), pointwise (`p = 2q ≥ 2`): with `x = |α|²`,
`y = |β|²` and `σ = 2 ⟨α, β⟩` (so `σ² ≤ 4 x y`),
`|α + β|^p − |α|^p − p |α|^{p−2} ⟨α, β⟩ ≥ c (|α|^{p−2} |β|² + |β|^p)` for some `c = c_p > 0`.
The paper invokes "uniform convexity of `|·|^p`" without proof or reference (a gap, filled here):
if `|β| ≤ K |α|` (`K = 8q`), the tangent line of the convex `t ↦ t^q` at `x` (`tbt2_bernoulli`)
gives the lower bound `q x^{q−1} y`, which controls both terms; otherwise
`|α + β| ≥ (1 − 2/K) |β|` and the term `|β|^p` dominates. -/
theorem tbt2_gain {q : ℝ} (hq : 1 ≤ q) : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ x y σ : ℝ, 0 ≤ x → 0 ≤ y →
    σ ^ 2 ≤ 4 * x * y →
      c * (x ^ (q - 1) * y + y ^ q) ≤ (x + σ + y) ^ q - x ^ q - q * x ^ (q - 1) * σ := by
  set K : ℝ := 8 * q with hK
  have hK8 : 8 ≤ K := by rw [hK]; linarith
  set D : ℝ := (K ^ 2) ^ (q - 1)
  have hD : 0 ≤ D := Real.rpow_nonneg (sq_nonneg _) _
  refine ⟨1 / (8 * (1 + D)), by positivity, by
    rw [div_le_one (by positivity)]; linarith, fun x y σ hx hy hσ => ?_⟩
  have hc8 : 1 / (8 * (1 + D)) * (1 + D) = 1 / 8 := by field_simp
  have hc0 : 0 < 1 / (8 * (1 + D)) := by positivity
  have hcD : 1 / (8 * (1 + D)) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hT : 0 ≤ x ^ (q - 1) := Real.rpow_nonneg hx _
  have hY : 0 ≤ y ^ q := Real.rpow_nonneg hy _
  -- `|σ| ≤ x + y`
  have hσxy := abs_le_of_sq_le_sq' (show σ ^ 2 ≤ (x + y) ^ 2 by nlinarith [sq_nonneg (x - y)])
    (by linarith)
  rcases le_or_gt y (K ^ 2 * x) with hA | hB
  · -- `|β| ≤ K |α|`: the tangent line gives `q |α|^{p−2} |β|²`
    have hb := tbt2_bernoulli hq hx (show 0 ≤ x + (σ + y) by linarith)
    have hyq : y ^ q ≤ D * (x ^ (q - 1) * y) := by
      rw [tbt2_rpow_eq_mul hq hy]
      calc y ^ (q - 1) * y ≤ (K ^ 2 * x) ^ (q - 1) * y :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hy hA (by linarith)) hy
        _ = D * (x ^ (q - 1) * y) := by
            rw [Real.mul_rpow (sq_nonneg _) hx]; ring
    have hTy : 0 ≤ x ^ (q - 1) * y := mul_nonneg hT hy
    have h1 : x ^ (q - 1) * y ≤ q * x ^ (q - 1) * y := by nlinarith
    calc 1 / (8 * (1 + D)) * (x ^ (q - 1) * y + y ^ q)
        ≤ 1 / (8 * (1 + D)) * ((1 + D) * (x ^ (q - 1) * y)) := by
          apply mul_le_mul_of_nonneg_left _ hc0.le; nlinarith
      _ = 1 / 8 * (x ^ (q - 1) * y) := by rw [← hc8]; ring
      _ ≤ (x + σ + y) ^ q - x ^ q - q * x ^ (q - 1) * σ := by
          rw [show x + σ + y = x + (σ + y) by ring]; nlinarith
  · -- `|β| > K |α|`: the term `|β|^p`
    have hy0 : 0 < y := lt_of_le_of_lt (by positivity) hB
    have hxy : x ≤ y / K ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    have hxy' : x ≤ y := hxy.trans (div_le_self hy (by nlinarith))
    have hσ : |σ| ≤ 2 * y / K := by
      apply abs_le_of_sq_le_sq _ (by positivity)
      calc σ ^ 2 ≤ 4 * x * y := hσ
        _ ≤ 4 * (y / K ^ 2) * y := by gcongr
        _ = (2 * y / K) ^ 2 := by field_simp; ring
    have hσ' := abs_le.mp hσ
    have hK0 : 0 < K := by linarith
    have hlow : y * (1 - 2 / K) ≤ x + σ + y := by
      have : y * (1 - 2 / K) = y - 2 * y / K := by field_simp
      linarith
    have hpos : 0 ≤ y * (1 - 2 / K) := mul_nonneg hy (by
      rw [sub_nonneg, div_le_one hK0]; linarith)
    -- `(x + σ + y)^q ≥ y^q (1 − 2q/K)`
    have h1 : y ^ q * (1 - 2 * q / K) ≤ (x + σ + y) ^ q := by
      have hb := one_add_mul_self_le_rpow_one_add (s := -(2 / K)) (by
        rw [neg_le_neg_iff, div_le_one hK0]; linarith) hq
      calc y ^ q * (1 - 2 * q / K) = y ^ q * (1 + q * -(2 / K)) := by ring
        _ ≤ y ^ q * (1 + -(2 / K)) ^ q := mul_le_mul_of_nonneg_left hb hY
        _ = (y * (1 - 2 / K)) ^ q := by
            rw [Real.mul_rpow hy (by rw [← sub_eq_add_neg] at *; nlinarith)]; ring_nf
        _ ≤ (x + σ + y) ^ q := Real.rpow_le_rpow hpos hlow (by linarith)
    have hTy : x ^ (q - 1) ≤ y ^ (q - 1) := Real.rpow_le_rpow hx hxy' (by linarith)
    have hT' : 0 ≤ y ^ (q - 1) := Real.rpow_nonneg hy _
    have hYe : y ^ q = y ^ (q - 1) * y := tbt2_rpow_eq_mul hq hy
    -- `x^q ≤ y^q / K²`
    have h2 : x ^ q ≤ y ^ q / K ^ 2 := by
      rw [tbt2_rpow_eq_mul hq hx, hYe]
      calc x ^ (q - 1) * x ≤ y ^ (q - 1) * (y / K ^ 2) := mul_le_mul hTy hxy hx hT'
        _ = y ^ (q - 1) * y / K ^ 2 := by ring
    -- `q x^{q−1} σ ≤ 2 q y^q / K`
    have h3 : q * x ^ (q - 1) * σ ≤ 2 * q * y ^ q / K := by
      rw [hYe]
      have : x ^ (q - 1) * σ ≤ y ^ (q - 1) * (2 * y / K) := by
        calc x ^ (q - 1) * σ ≤ x ^ (q - 1) * |σ| := mul_le_mul_of_nonneg_left (le_abs_self σ) hT
          _ ≤ y ^ (q - 1) * (2 * y / K) := mul_le_mul hTy hσ (abs_nonneg _) hT'
      calc q * x ^ (q - 1) * σ = q * (x ^ (q - 1) * σ) := by ring
        _ ≤ q * (y ^ (q - 1) * (2 * y / K)) := mul_le_mul_of_nonneg_left this (by linarith)
        _ = 2 * q * (y ^ (q - 1) * y) / K := by ring
    have hk1 : 2 * q / K = 1 / 4 := by rw [hK]; field_simp; ring
    have hk2 : 1 / K ^ 2 ≤ 1 / 64 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h4 : x ^ (q - 1) * y ≤ y ^ q := by
      rw [hYe]; exact mul_le_mul_of_nonneg_right hTy hy
    have e1 : y ^ q * (1 - 2 * q / K) = y ^ q - y ^ q * (2 * q / K) := by ring
    have e2 : 2 * q * y ^ q / K = y ^ q * (2 * q / K) := by ring
    have e3 : y ^ q / K ^ 2 = y ^ q * (1 / K ^ 2) := by ring
    rw [hk1] at e1 e2 h1
    have h5 : y ^ q * (1 / K ^ 2) ≤ y ^ q * (1 / 64) := mul_le_mul_of_nonneg_left hk2 hY
    calc 1 / (8 * (1 + D)) * (x ^ (q - 1) * y + y ^ q) ≤ 1 / 8 * (y ^ q + y ^ q) :=
          mul_le_mul hcD (by linarith) (by positivity) (by norm_num)
      _ ≤ (x + σ + y) ^ q - x ^ q - q * x ^ (q - 1) * σ := by linarith

/-- `(t²)^{p/2} = t^p` for `t ≥ 0`. -/
theorem tbt2_sq_rpow {p t : ℝ} (ht : 0 ≤ t) : (t ^ 2) ^ (p / 2) = t ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  congr 1; push_cast; ring

theorem tbt2_frobNorm_sq (A : Matrix (Fin d) (Fin m) ℝ) : frobNorm A ^ 2 = frobSq A :=
  Real.sq_sqrt (tbt_frobSq_nonneg A)

/-- The splitting of the error in (28), "for every `0 < ε ≤ 1`": pointwise,
`C (|X| + |W| + |𝓔|)^{p−2} (|W| + |𝓔|) |𝓔|
≤ ε (|X|^{p−2} |W|² + |W|^p) + C' (ε^{−1} |X|^{p−2} |𝓔|² + ε^{1−p} |𝓔|^p)`, with `C'` depending
only on `C` and `p` (Young's inequality, in the elementary form of a case split on the sizes of
`|X|`, `|W|`, `|𝓔|`). -/
theorem tbt2_young {p C : ℝ} (hp : 2 ≤ p) (hC : 1 ≤ C) : ∃ C' : ℝ, 0 ≤ C' ∧
    ∀ ε a w e : ℝ, 0 < ε → ε ≤ 1 → 0 ≤ a → 0 ≤ w → 0 ≤ e →
      C * (a + w + e) ^ (p - 2) * (w + e) * e ≤
        ε * (a ^ (p - 2) * w ^ 2 + w ^ p) +
          C' * (ε⁻¹ * a ^ (p - 2) * e ^ 2 + ε ^ (1 - p) * e ^ p) := by
  set B : ℝ := C * 2 ^ (p - 2)
  set B' : ℝ := B * 2 ^ (p - 1)
  have h2a : (1 : ℝ) ≤ 2 ^ (p - 2) := Real.one_le_rpow (by norm_num) (by linarith)
  have h2b : (1 : ℝ) ≤ 2 ^ (p - 1) := Real.one_le_rpow (by norm_num) (by linarith)
  have hB : 1 ≤ B := by nlinarith
  have hB' : 1 ≤ B' := by nlinarith
  have hB'p : B' ≤ B' ^ p := Real.self_le_rpow_of_one_le hB' (by linarith)
  refine ⟨B ^ 2 + B + B' ^ p, by positivity, fun ε a w e hε hε1 ha hw he => ?_⟩
  have hp2 : 0 ≤ p - 2 := by linarith
  have hAp : 0 ≤ a ^ (p - 2) := Real.rpow_nonneg ha _
  have hwp : 0 ≤ w ^ p := Real.rpow_nonneg hw _
  have hep : 0 ≤ e ^ p := Real.rpow_nonneg he _
  have hεp : 1 ≤ ε ^ (1 - p) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have hεi : 1 ≤ ε⁻¹ := by rw [le_inv_comm₀ one_pos hε, inv_one]; exact hε1
  have hB'p0 : 0 ≤ B' ^ p := by positivity
  -- the terms that are not used are nonnegative
  have t1 : 0 ≤ ε * (a ^ (p - 2) * w ^ 2) := by positivity
  have t2 : 0 ≤ ε * w ^ p := by positivity
  have t3 : 0 ≤ ε⁻¹ * a ^ (p - 2) * e ^ 2 := by positivity
  have t4 : 0 ≤ ε ^ (1 - p) * e ^ p := by positivity
  have hsplit : ε * (a ^ (p - 2) * w ^ 2 + w ^ p) +
      (B ^ 2 + B + B' ^ p) * (ε⁻¹ * a ^ (p - 2) * e ^ 2 + ε ^ (1 - p) * e ^ p) =
      ε * (a ^ (p - 2) * w ^ 2) + ε * w ^ p + (B ^ 2 + B) * (ε⁻¹ * a ^ (p - 2) * e ^ 2) +
        B' ^ p * (ε⁻¹ * a ^ (p - 2) * e ^ 2) + (B ^ 2 + B) * (ε ^ (1 - p) * e ^ p) +
        B' ^ p * (ε ^ (1 - p) * e ^ p) := by ring
  rw [hsplit]
  have u1 : 0 ≤ B' ^ p * (ε⁻¹ * a ^ (p - 2) * e ^ 2) := by positivity
  have u2 : 0 ≤ (B ^ 2 + B) * (ε ^ (1 - p) * e ^ p) := by positivity
  have u3 : 0 ≤ (B ^ 2 + B) * (ε⁻¹ * a ^ (p - 2) * e ^ 2) := by positivity
  have u4 : 0 ≤ B' ^ p * (ε ^ (1 - p) * e ^ p) := by positivity
  rcases le_or_gt (w + e) a with h1 | h1
  · -- `|W| + |𝓔| ≤ |X|`
    have hpow : (a + w + e) ^ (p - 2) ≤ 2 ^ (p - 2) * a ^ (p - 2) := by
      rw [← Real.mul_rpow (by norm_num) ha]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hp2
    -- `B w e ≤ ε w² + B² e² / ε`
    have hwe : B * w * e ≤ ε * w ^ 2 + B ^ 2 * ε⁻¹ * e ^ 2 := by
      have hm : ε * (B * w * e) ≤ ε * (ε * w ^ 2 + B ^ 2 * ε⁻¹ * e ^ 2) := by
        have : ε * (ε * w ^ 2 + B ^ 2 * ε⁻¹ * e ^ 2) = ε ^ 2 * w ^ 2 + B ^ 2 * e ^ 2 := by
          field_simp
        rw [this]
        nlinarith [sq_nonneg (ε * w - B * e), mul_nonneg (mul_nonneg hε.le
          (by linarith : (0 : ℝ) ≤ B)) (mul_nonneg hw he)]
      exact le_of_mul_le_mul_left hm hε
    have hee : B * e ^ 2 ≤ B * ε⁻¹ * e ^ 2 := by
      have : B * e ^ 2 = B * 1 * e ^ 2 := by ring
      rw [this]; gcongr
    calc C * (a + w + e) ^ (p - 2) * (w + e) * e
        ≤ C * (2 ^ (p - 2) * a ^ (p - 2)) * (w + e) * e := by gcongr
      _ = a ^ (p - 2) * (B * w * e + B * e ^ 2) := by ring
      _ ≤ a ^ (p - 2) * (ε * w ^ 2 + B ^ 2 * ε⁻¹ * e ^ 2 + B * ε⁻¹ * e ^ 2) := by gcongr
      _ = ε * (a ^ (p - 2) * w ^ 2) + (B ^ 2 + B) * (ε⁻¹ * a ^ (p - 2) * e ^ 2) := by ring
      _ ≤ _ := by linarith
  · -- `|X| < |W| + |𝓔|`
    have hwe0 : 0 < w + e := lt_of_le_of_lt ha h1
    have hpow : (a + w + e) ^ (p - 2) ≤ 2 ^ (p - 2) * (w + e) ^ (p - 2) := by
      rw [← Real.mul_rpow (by norm_num) hwe0.le]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hp2
    have hstep : C * (a + w + e) ^ (p - 2) * (w + e) * e ≤ B * (w + e) ^ (p - 1) * e := by
      calc C * (a + w + e) ^ (p - 2) * (w + e) * e
          ≤ C * (2 ^ (p - 2) * (w + e) ^ (p - 2)) * (w + e) * e := by gcongr
        _ = B * ((w + e) ^ (p - 2) * (w + e)) * e := by ring
        _ = B * (w + e) ^ (p - 1) * e := by
            rw [← Real.rpow_add_one hwe0.ne', show p - 2 + 1 = p - 1 by ring]
    rcases le_or_gt e w with h2 | h2
    · have hw0 : 0 < w := by linarith
      have hpw : (w + e) ^ (p - 1) ≤ 2 ^ (p - 1) * w ^ (p - 1) := by
        rw [← Real.mul_rpow (by norm_num) hw]
        exact Real.rpow_le_rpow hwe0.le (by linarith) (by linarith)
      have hstep2 : C * (a + w + e) ^ (p - 2) * (w + e) * e ≤ B' * w ^ (p - 1) * e := by
        refine hstep.trans ?_
        calc B * (w + e) ^ (p - 1) * e ≤ B * (2 ^ (p - 1) * w ^ (p - 1)) * e := by gcongr
          _ = B' * w ^ (p - 1) * e := by ring
      have hwp1 : 0 ≤ w ^ (p - 1) := Real.rpow_nonneg hw _
      rcases le_or_gt (B' * e) (ε * w) with h3 | h3
      · -- `B' |𝓔| ≤ ε |W|`
        calc C * (a + w + e) ^ (p - 2) * (w + e) * e ≤ B' * w ^ (p - 1) * e := hstep2
          _ = w ^ (p - 1) * (B' * e) := by ring
          _ ≤ w ^ (p - 1) * (ε * w) := mul_le_mul_of_nonneg_left h3 hwp1
          _ = ε * w ^ p := by rw [tbt2_rpow_eq_mul (q := p) (by linarith) hw]; ring
          _ ≤ _ := by linarith
      · -- `ε |W| < B' |𝓔|`
        have hwle : w ≤ B' * ε⁻¹ * e := by
          rw [mul_comm B', mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hε]; linarith
        have hpw2 : w ^ (p - 1) ≤ B' ^ (p - 1) * ε ^ (1 - p) * e ^ (p - 1) := by
          calc w ^ (p - 1) ≤ (B' * ε⁻¹ * e) ^ (p - 1) :=
                Real.rpow_le_rpow hw hwle (by linarith)
            _ = B' ^ (p - 1) * ε ^ (1 - p) * e ^ (p - 1) := by
                rw [Real.mul_rpow (by positivity) he, Real.mul_rpow (by positivity)
                  (by positivity), Real.inv_rpow hε.le, ← Real.rpow_neg hε.le, neg_sub]
        calc C * (a + w + e) ^ (p - 2) * (w + e) * e ≤ B' * w ^ (p - 1) * e := hstep2
          _ ≤ B' * (B' ^ (p - 1) * ε ^ (1 - p) * e ^ (p - 1)) * e := by gcongr
          _ = (B' * B' ^ (p - 1)) * ε ^ (1 - p) * (e ^ (p - 1) * e) := by ring
          _ = B' ^ p * (ε ^ (1 - p) * e ^ p) := by
              rw [← tbt2_rpow_eq_mul (q := p) (by linarith) he, mul_comm B',
                ← tbt2_rpow_eq_mul (q := p) (by linarith) (by linarith)]; ring
          _ ≤ _ := by linarith
    · -- `|W| < |𝓔|`
      have he0 : 0 < e := by linarith
      have hpe : (w + e) ^ (p - 1) ≤ 2 ^ (p - 1) * e ^ (p - 1) := by
        rw [← Real.mul_rpow (by norm_num) he]
        exact Real.rpow_le_rpow hwe0.le (by linarith) (by linarith)
      calc C * (a + w + e) ^ (p - 2) * (w + e) * e ≤ B * (w + e) ^ (p - 1) * e := hstep
        _ ≤ B * (2 ^ (p - 1) * e ^ (p - 1)) * e := by gcongr
        _ = B' * e ^ p := by rw [tbt2_rpow_eq_mul (q := p) (by linarith) he]; ring
        _ ≤ B' ^ p * (1 * e ^ p) := by rw [one_mul]; exact mul_le_mul_of_nonneg_right hB'p hep
        _ ≤ B' ^ p * (ε ^ (1 - p) * e ^ p) := by gcongr
        _ ≤ _ := by linarith

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

end Cassese
