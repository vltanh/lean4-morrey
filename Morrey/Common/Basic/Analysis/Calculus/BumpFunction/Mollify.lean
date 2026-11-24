module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Mollification by normed bump functions

For a normed bump function `ρ : ContDiffBump (0 : E)` on a finite-dimensional real normed space `E`
with an additive Haar measure `μ`, the mollification of `g : E → ℝ` is the convolution
`ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g`, `x ↦ ∫ ρ_μ (t) g (x − t) dμ (t)`. This file collects the properties
of it that a proof by mollification uses: it is smooth, linear, monotone, preserves constants,
bounds, convexity and concavity, Lipschitz constants and periods; it depends only on the values
of `g` on the ball of radius `ρ.rOut`; for a Lipschitz `g` its derivative is the mollification of
the (almost everywhere defined) derivative of `g`; it converges to `g` pointwise for continuous `g`
and its derivatives converge almost everywhere for Lipschitz `g` as `ρ.rOut → 0`.

Mathlib has the convolution and the bump functions
(`Mathlib/Analysis/Convolution.lean`, `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`);
the lemmas here are thin consequences, filed as Mathlib would file them (namespace
`ContDiffBump`), with the names `normed_convolution_*`. The kernel `ρ.normed μ` is continuous,
nonnegative, compactly supported, of integral `1` and supported in the ball of radius `ρ.rOut`;
most proofs use only these facts and the formula `normed_convolution_apply`.

API (every statement uses `ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g`):

* `normed_convolution_apply`: the formula `∫ ρ_μ (t) * g (x − t) dμ (t)`;
* `contDiff_normed_convolution`: smooth for locally integrable `g`;
* `normed_convolution_add`, `normed_convolution_sub`, `normed_convolution_const_mul`,
  `normed_convolution_const`: linearity, and constants are fixed;
* `normed_convolution_mono`: monotone in `g`;
* `abs_normed_convolution_le`, `normed_convolution_mem_Icc`: bounds pass to the mollification;
* `normed_convolution_concaveOn`, `normed_convolution_convexOn`: concavity and convexity on `E`;
* `normed_convolution_lipschitzWith`: the Lipschitz constant is kept;
* `normed_convolution_add_right`: periods are kept;
* `normed_convolution_eq_of_forall_ball`: if `g = c` on the ball of radius `ρ.rOut` about `x`, the
  mollification is `c` at `x`;
* `normed_convolution_pos`: positive at `x` for continuous `g ≥ 0` positive somewhere on the ball
  of radius `ρ.rOut` about `x`;
* `fderiv_normed_convolution_of_lipschitzWith`: for Lipschitz `g`,
  `D (ρ ⋆ g) (x) v = (ρ ⋆ ∂_v g) (x)`;
* `norm_fderiv_normed_convolution_le`: for `K`-Lipschitz `g`, `‖D (ρ ⋆ g) (x)‖ ≤ K`;
* `tendsto_normed_convolution`: pointwise convergence for continuous `g` as `rOut → 0`;
* `ae_tendsto_fderiv_normed_convolution`: almost everywhere convergence of the derivatives for
  Lipschitz `g`, as `rOut → 0` with `rOut ≤ C rIn`;
* `ContDiffBump.ofRadius`: the bump with radii `r / 2 < r`.
-/

@[expose] public section

open MeasureTheory Filter Topology ContinuousLinearMap Metric
open scoped Convolution ContDiff

namespace ContDiffBump

section ofRadius

variable {E : Type*} [NormedAddCommGroup E]

/-- The bump function with radii `r / 2 < r`. -/
noncomputable def ofRadius {r : ℝ} (hr : 0 < r) : ContDiffBump (0 : E) where
  rIn := r / 2
  rOut := r
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

@[simp] theorem ofRadius_rOut {r : ℝ} (hr : 0 < r) : (ofRadius (E := E) hr).rOut = r := rfl

@[simp] theorem ofRadius_rIn {r : ℝ} (hr : 0 < r) : (ofRadius (E := E) hr).rIn = r / 2 := rfl

end ofRadius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  (ρ : ContDiffBump (0 : E))

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The mollification as an integral. -/
theorem normed_convolution_apply (g : E → ℝ) (x : E) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x = ∫ t, ρ.normed μ t * g (x - t) ∂μ :=
  convolution_lsmul

/-- The convolution of the normed bump with a locally integrable function exists everywhere. -/
private theorem convolutionExists_normed {g : E → ℝ} (hg : LocallyIntegrable g μ) :
    ConvolutionExists (ρ.normed μ) g (lsmul ℝ ℝ) μ :=
  ρ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ) ρ.continuous_normed hg

/-- The integrand `t ↦ ρ_μ (t) * h (t)` is integrable for continuous `h`. -/
private theorem integrable_normed_mul {h : E → ℝ} (hh : Continuous h) :
    Integrable (fun t => ρ.normed μ t * h t) μ :=
  (ρ.continuous_normed.mul hh).integrable_of_hasCompactSupport ρ.hasCompactSupport_normed.mul_right

/-- The integrand `t ↦ ρ_μ (t) * g (x - t)` of the mollification is integrable for continuous `g`.
-/
private theorem integrable_normed_mul_comp_sub {g : E → ℝ} (hg : Continuous g) (x : E) :
    Integrable (fun t => ρ.normed μ t * g (x - t)) μ :=
  ρ.integrable_normed_mul (hg.comp (continuous_const.sub continuous_id))

/-- The mollification of a locally integrable function is smooth: `ρ_μ` is smooth with compact
support (`HasCompactSupport.contDiff_convolution_left`). -/
theorem contDiff_normed_convolution {g : E → ℝ} (hg : LocallyIntegrable g μ) :
    ContDiff ℝ ∞ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_left (n := ⊤) _ ρ.contDiff_normed hg

/-- The mollification is additive on locally integrable functions. -/
theorem normed_convolution_add {g g' : E → ℝ} (hg : LocallyIntegrable g μ)
    (hg' : LocallyIntegrable g' μ) :
    ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (g + g') =
      ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g + ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g' :=
  (ρ.convolutionExists_normed hg).distrib_add (ρ.convolutionExists_normed hg')

/-- The mollification commutes with differences of locally integrable functions. -/
theorem normed_convolution_sub {g g' : E → ℝ} (hg : LocallyIntegrable g μ)
    (hg' : LocallyIntegrable g' μ) :
    ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (g - g') =
      ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g - ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g' := by
  ext x
  simp only [convolution_def, Pi.sub_apply, map_sub]
  exact integral_sub (ρ.convolutionExists_normed hg x) (ρ.convolutionExists_normed hg' x)

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The mollification commutes with multiplication by a constant. -/
theorem normed_convolution_const_mul (c : ℝ) (g : E → ℝ) :
    ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (fun x => c * g x) =
      fun x => c * (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x := by
  ext x
  simp only [normed_convolution_apply, ← integral_const_mul]
  congr 1
  ext t
  ring

/-- Constants are fixed. -/
theorem normed_convolution_const (c : ℝ) (x : E) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun _ => c) x = c :=
  normed_convolution_eq_right (μ := μ) (φ := ρ) (g := fun _ => c) fun _ _ => rfl

/-- The mollification is monotone. -/
theorem normed_convolution_mono {g g' : E → ℝ} (hg : LocallyIntegrable g μ)
    (hg' : LocallyIntegrable g' μ) (h : ∀ y, g y ≤ g' y) (x : E) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x ≤ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g') x :=
  convolution_mono_right (ρ.convolutionExists_normed hg x) (ρ.convolutionExists_normed hg' x)
    ρ.nonneg_normed h

/-- A bound `|g| ≤ C` passes to the mollification: `ρ_μ ≥ 0` has integral `1`. -/
theorem abs_normed_convolution_le {g : E → ℝ} {C : ℝ} (hg : ∀ y, |g y| ≤ C) (x : E) :
    |(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x| ≤ C := by
  rw [normed_convolution_apply]
  have hi : Integrable (fun t => ρ.normed μ t * C) μ :=
    (ρ.continuous_normed.integrable_of_hasCompactSupport ρ.hasCompactSupport_normed).mul_const C
  have := norm_integral_le_of_norm_le hi (μ := μ) (f := fun t => ρ.normed μ t * g (x - t))
    (Eventually.of_forall fun t => by
      rw [norm_mul, Real.norm_of_nonneg (ρ.nonneg_normed t), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hg _) (ρ.nonneg_normed t))
  rw [integral_mul_const, ρ.integral_normed, one_mul] at this
  simpa [Real.norm_eq_abs] using this

/-- Bounds `a ≤ g ≤ b` pass to the mollification (`normed_convolution_mono` against the
constants `a` and `b`, which are fixed). -/
theorem normed_convolution_mem_Icc {g : E → ℝ} (hg : LocallyIntegrable g μ) {a b : ℝ}
    (h : ∀ y, g y ∈ Set.Icc a b) (x : E) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  · calc a = (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun _ => a) x := (ρ.normed_convolution_const a x).symm
      _ ≤ _ := ρ.normed_convolution_mono (locallyIntegrable_const a) hg (fun y => (h y).1) x
  · calc _ ≤ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun _ => b) x :=
          ρ.normed_convolution_mono hg (locallyIntegrable_const b) (fun y => (h y).2) x
      _ = b := ρ.normed_convolution_const b x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For `a + b = 1`, `a • x + b • y - t = a • (x - t) + b • (y - t)`. -/
private theorem combo_sub_eq {a b : ℝ} (hab : a + b = 1) (x y t : E) :
    a • x + b • y - t = a • (x - t) + b • (y - t) := by
  rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]

/-- The two sides of the concavity and convexity inequalities for the mollification of a
continuous `g`, as integrals against `ρ_μ`. -/
private theorem normed_convolution_combo {g : E → ℝ} (hg : Continuous g) {a b : ℝ}
    (hab : a + b = 1) (x y : E) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) (a • x + b • y) =
        ∫ t, ρ.normed μ t * g (a • (x - t) + b • (y - t)) ∂μ ∧
      a • (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x + b • (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) y =
        ∫ t, ρ.normed μ t * (a • g (x - t) + b • g (y - t)) ∂μ := by
  refine ⟨?_, ?_⟩
  · simp only [normed_convolution_apply, combo_sub_eq hab]
  · simp only [normed_convolution_apply, smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((ρ.integrable_normed_mul_comp_sub hg x).const_mul a)
        ((ρ.integrable_normed_mul_comp_sub hg y).const_mul b)]
    congr 1
    ext t
    ring

/-- The integrands of `normed_convolution_combo` are integrable. -/
private theorem integrable_combo {g : E → ℝ} (hg : Continuous g) (a b : ℝ) (x y : E) :
    Integrable (fun t => ρ.normed μ t * g (a • (x - t) + b • (y - t))) μ ∧
      Integrable (fun t => ρ.normed μ t * (a • g (x - t) + b • g (y - t))) μ := by
  have hx : Continuous fun t : E => x - t := continuous_const.sub continuous_id
  have hy : Continuous fun t : E => y - t := continuous_const.sub continuous_id
  exact ⟨ρ.integrable_normed_mul (hg.comp ((hx.const_smul a).add (hy.const_smul b))),
    ρ.integrable_normed_mul (((hg.comp hx).const_smul a).add ((hg.comp hy).const_smul b))⟩

/-- The mollification of a concave function is concave: for `a + b = 1`,
`(ρ ⋆ g) (a • x + b • y) = ∫ ρ_μ (t) g (a • (x - t) + b • (y - t)) dμ (t)
  ≥ ∫ ρ_μ (t) (a g (x - t) + b g (y - t)) dμ (t) = a (ρ ⋆ g) (x) + b (ρ ⋆ g) (y)`. -/
theorem normed_convolution_concaveOn {g : E → ℝ} (hg : Continuous g)
    (hcv : ConcaveOn ℝ Set.univ g) : ConcaveOn ℝ Set.univ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨h1, h2⟩ := ρ.normed_convolution_combo (μ := μ) hg hab x y
  obtain ⟨i1, i2⟩ := ρ.integrable_combo (μ := μ) hg a b x y
  rw [h1, h2]
  exact integral_mono i2 i1 fun t => mul_le_mul_of_nonneg_left
    (hcv.2 (Set.mem_univ (x - t)) (Set.mem_univ (y - t)) ha hb hab) (ρ.nonneg_normed t)

/-- The mollification of a convex function is convex (as `normed_convolution_concaveOn`, with the
inequality reversed). -/
theorem normed_convolution_convexOn {g : E → ℝ} (hg : Continuous g)
    (hcv : ConvexOn ℝ Set.univ g) : ConvexOn ℝ Set.univ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨h1, h2⟩ := ρ.normed_convolution_combo (μ := μ) hg hab x y
  obtain ⟨i1, i2⟩ := ρ.integrable_combo (μ := μ) hg a b x y
  rw [h1, h2]
  exact integral_mono i1 i2 fun t => mul_le_mul_of_nonneg_left
    (hcv.2 (Set.mem_univ (x - t)) (Set.mem_univ (y - t)) ha hb hab) (ρ.nonneg_normed t)

/-- The mollification keeps the Lipschitz constant:
`|(ρ ⋆ g) (x) - (ρ ⋆ g) (y)| ≤ ∫ ρ_μ (t) |g (x - t) - g (y - t)| dμ (t) ≤ K ‖x - y‖`. -/
theorem normed_convolution_lipschitzWith {g : E → ℝ} {K : NNReal} (hg : LipschitzWith K g) :
    LipschitzWith K (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, normed_convolution_apply, normed_convolution_apply,
    ← integral_sub (ρ.integrable_normed_mul_comp_sub hg.continuous x)
      (ρ.integrable_normed_mul_comp_sub hg.continuous y)]
  have hi : Integrable (fun t => ρ.normed μ t * (K * dist x y)) μ :=
    (ρ.continuous_normed.integrable_of_hasCompactSupport ρ.hasCompactSupport_normed).mul_const _
  have hb : ∀ t, ‖ρ.normed μ t * g (x - t) - ρ.normed μ t * g (y - t)‖ ≤
      ρ.normed μ t * (K * dist x y) := by
    intro t
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (ρ.nonneg_normed t)]
    refine mul_le_mul_of_nonneg_left ?_ (ρ.nonneg_normed t)
    have := hg.dist_le_mul (x - t) (y - t)
    rwa [dist_sub_right, Real.dist_eq, ← Real.norm_eq_abs] at this
  have := norm_integral_le_of_norm_le hi (Eventually.of_forall hb)
  rw [integral_mul_const, ρ.integral_normed, one_mul] at this
  simpa [Real.norm_eq_abs] using this

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The mollification keeps periods: `g (x + v - t) = g (x - t)`. -/
theorem normed_convolution_add_right {g : E → ℝ} {v : E} (hg : ∀ y, g (y + v) = g y) (x : E) :
    (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) (x + v) = (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x := by
  simp only [normed_convolution_apply]
  congr 1
  ext t
  rw [show x + v - t = x - t + v by abel, hg]

/-- The mollification at `x` depends only on `g` on the ball of radius `ρ.rOut` about `x`
(`normed_convolution_eq_right`). -/
theorem normed_convolution_eq_of_forall_ball {g : E → ℝ} {c : ℝ} {x : E}
    (hg : ∀ y ∈ ball x ρ.rOut, g y = c) : (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x = c := by
  have hx : g x = c := hg x (mem_ball_self ρ.rOut_pos)
  rw [normed_convolution_eq_right (μ := μ) (φ := ρ) fun y hy => (hg y hy).trans hx.symm, hx]

/-- The mollification of a continuous `g ≥ 0` is positive at `x` when `g` is positive somewhere on
the ball of radius `ρ.rOut` about `x`: the integrand `t ↦ ρ_μ (t) g (x - t)` is continuous,
nonnegative, compactly supported and positive at `t = x - y`. -/
theorem normed_convolution_pos {g : E → ℝ} (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y) {x y : E}
    (hy : y ∈ ball x ρ.rOut) (hgy : 0 < g y) : 0 < (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x := by
  rw [normed_convolution_apply]
  have hxy : ρ.normed μ (x - y) ≠ 0 := by
    rw [← Function.mem_support, ρ.support_normed_eq, mem_ball_zero_iff, ← dist_eq_norm,
      dist_comm]
    exact hy
  have hc : Continuous fun t => ρ.normed μ t * g (x - t) :=
    ρ.continuous_normed.mul (hg.comp (continuous_const.sub continuous_id))
  refine hc.integral_pos_of_hasCompactSupport_nonneg_ne_zero ρ.hasCompactSupport_normed.mul_right
    (fun t => mul_nonneg (ρ.nonneg_normed t) (hg0 _)) (x := x - y) ?_
  rw [sub_sub_cancel]
  exact mul_ne_zero hxy hgy.ne'

/-- The derivative of the mollification of a Lipschitz function is the mollification of its
(almost everywhere defined) line derivative: the difference quotients
`t⁻¹ ((ρ ⋆ g) (x + t v) - (ρ ⋆ g) (x)) = ∫ t⁻¹ (g (z + t v) - g z) ρ_μ (x - z) dμ (z)` tend to
`D (ρ ⋆ g) (x) v` and, by dominated convergence
(`LipschitzWith.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul`), to
`∫ ∂_v g (z) ρ_μ (x - z) dμ (z) = (ρ ⋆ ∂_v g) (x)`. -/
theorem fderiv_normed_convolution_of_lipschitzWith {g : E → ℝ} {K : NNReal}
    (hg : LipschitzWith K g) (x v : E) :
    fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x v =
      (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun y => lineDeriv ℝ g y v) x := by
  set ρn := ρ.normed μ
  have hdiff : DifferentiableAt ℝ (ρn ⋆[lsmul ℝ ℝ, μ] g) x :=
    ((ρ.contDiff_normed_convolution hg.continuous.locallyIntegrable).differentiable (by simp)) x
  have lim1 := (hdiff.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right
  have hgi : Integrable (fun z => ρn (x - z)) μ :=
    (ρ.continuous_normed.integrable_of_hasCompactSupport ρ.hasCompactSupport_normed).comp_sub_left x
  have lim2 := hg.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul hgi v
  have hcs : HasCompactSupport (fun z => ρn (x - z)) :=
    ρ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
  have hcont : Continuous (fun z => ρn (x - z)) :=
    ρ.continuous_normed.comp (continuous_const.sub continuous_id)
  have heq : ∀ t : ℝ, t⁻¹ • ((ρn ⋆[lsmul ℝ ℝ, μ] g) (x + t • v) - (ρn ⋆[lsmul ℝ ℝ, μ] g) x) =
      ∫ z, (t⁻¹ • (g (z + t • v) - g z)) * ρn (x - z) ∂μ := by
    intro t
    have i1 : Integrable (fun z => ρn (x - z) * g (z + t • v)) μ :=
      Continuous.integrable_of_hasCompactSupport
        (hcont.mul (hg.continuous.comp (continuous_id.add continuous_const))) hcs.mul_right
    have i2 : Integrable (fun z => ρn (x - z) * g z) μ :=
      (hcont.mul hg.continuous).integrable_of_hasCompactSupport hcs.mul_right
    have e1 : (ρn ⋆[lsmul ℝ ℝ, μ] g) (x + t • v) = ∫ z, ρn (x - z) * g (z + t • v) ∂μ := by
      rw [convolution_lsmul_swap, ← integral_add_right_eq_self _ (t • v)]
      congr 1
      ext z
      simp only [smul_eq_mul]
      congr 2
      abel
    have e2 : (ρn ⋆[lsmul ℝ ℝ, μ] g) x = ∫ z, ρn (x - z) * g z ∂μ := by
      rw [convolution_lsmul_swap]
      rfl
    rw [e1, e2, ← integral_sub i1 i2, ← integral_smul]
    congr 1
    ext z
    simp only [smul_eq_mul]
    ring
  simp only [heq] at lim1
  rw [tendsto_nhds_unique lim1 lim2, convolution_lsmul_swap]
  congr 1
  ext z
  simp only [smul_eq_mul]
  ring

/-- The derivative of the mollification of a `K`-Lipschitz function has norm at most `K`
(`normed_convolution_lipschitzWith` and `norm_fderiv_le_of_lipschitz`). -/
theorem norm_fderiv_normed_convolution_le {g : E → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    (x : E) : ‖fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x‖ ≤ K :=
  norm_fderiv_le_of_lipschitz ℝ (ρ.normed_convolution_lipschitzWith hg)

/-- Pointwise convergence for continuous `g` as the outer radius tends to `0`
(`ContDiffBump.convolution_tendsto_right_of_continuous`). -/
theorem tendsto_normed_convolution {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) {g : E → ℝ} (hg : Continuous g) (x : E) :
    Tendsto (fun i => ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x) l (𝓝 (g x)) :=
  convolution_tendsto_right_of_continuous hφ hg x

/-- For Lipschitz `g`, the derivatives of the mollifications converge to the derivative of `g`
almost everywhere, as the outer radius tends to `0` with a bounded ratio of the radii: by
`fderiv_normed_convolution_of_lipschitzWith` they are the mollifications of the locally
integrable `∂_v g`, which converge to `∂_v g` almost everywhere
(`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`), and `∂_v g = D g (·) v` almost
everywhere (Rademacher, `LipschitzWith.ae_differentiableAt`). -/
theorem ae_tendsto_fderiv_normed_convolution {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} {C : ℝ} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hφC : ∀ᶠ i in l, (φ i).rOut ≤ C * (φ i).rIn) {g : E → ℝ} {K : NNReal}
    (hg : LipschitzWith K g) (v : E) :
    ∀ᵐ x ∂μ, Tendsto (fun i => fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x v) l
      (𝓝 (fderiv ℝ g x v)) := by
  have h1 := ae_convolution_tendsto_right_of_locallyIntegrable (μ := μ) hφ hφC
    (hg.locallyIntegrable_lineDeriv v)
  filter_upwards [h1, hg.ae_differentiableAt (μ := μ)] with x hx hd
  simp only [fderiv_normed_convolution_of_lipschitzWith _ hg]
  rw [← hd.lineDeriv_eq_fderiv]
  exact hx

end ContDiffBump
