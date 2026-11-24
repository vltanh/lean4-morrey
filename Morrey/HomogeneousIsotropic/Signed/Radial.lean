module

public import Morrey.HomogeneousIsotropic.Signed.Defs
public import Morrey.HomogeneousIsotropic.Burkholder
public import Morrey.Common.Basic.Analysis.Convex.Hinge
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial integration of the truncated determinant

For `N : ℝ → ℝ` and a sign `e`, let
`radial e N (X) = (σ + e δ) N (σ) − 2 ∫₀^σ N`, where `σ = |z| + |w|` and `δ = |z| − |w|` for the
conformal part `z` and the anticonformal part `w` of `X`: it is `2 |z| N (σ) − 2 ∫₀^σ N` for
`e = 1` and `2 |w| N (σ) − 2 ∫₀^σ N` for `e = −1`.

* `quasiconvex_radial`: if `N` is convex on `[0, ∞)`, continuous, and `N 0 ≤ 0`, then
  `radial e N` is quasiconvex. For an affine `N = n₀ + n₁ r` it is `−2 n₀ r' + e n₁ det X`
  (`r' = |w|` for `e = 1`, `|z|` for `e = −1`): a convex function plus a null Lagrangian
  (`radial_affine`, `quasiconvex_norm_add_norm_add_det`). For `N = max (r − ρ) 0` it is
  `ρ² K (X/ρ)` (`radial_hinge`), where `K = (σ − 1)₊ (1 + e δ)` (`radialKernel`) is the truncated
  determinant `L` of arXiv:2609.28311 (`Agazzi.integrandL`) composed with the reflection, plus the
  determinant (for `e = 1`, `radialKernel_one`), or `L` minus the determinant (for `e = −1`,
  `radialKernel_neg_one`). A general `N` is a uniform limit on bounded sets of nonnegative
  combinations of these (`ConvexOn.exists_hinge_approx`, `abs_radial_sub_le`), and Jensen's
  inequality for a Lipschitz test map sees a bounded set of matrices only
  (`norm_add_norm_add_grad_le`).
* `quasiconvex_comp_smul`, `quasiconvex_const_add`, `quasiconvex_finset_sum`: quasiconvexity is
  invariant under `X ↦ c X` and under adding a constant, and finite nonnegative combinations of
  continuous quasiconvex functions are quasiconvex.
-/

@[expose] public section

open Set CalculusOfVariations MeasureTheory

namespace HomogeneousIsotropic

/-- The radial function of a continuous `N` is continuous. -/
theorem continuous_radial (e : ℝ) {N : ℝ → ℝ} (hN : Continuous N) : Continuous (radial e N) := by
  have h1 := continuous_norm_conformalPart
  have h2 := continuous_norm_anticonformalPart
  have hP : Continuous fun s : ℝ => ∫ r in (0 : ℝ)..s, N r :=
    intervalIntegral.continuous_primitive (fun a b => hN.intervalIntegrable a b) 0
  unfold radial radialProfile
  exact (((h1.add h2).add (continuous_const.mul (h1.sub h2))).mul (hN.comp (h1.add h2))).sub
    (continuous_const.mul (hP.comp (h1.add h2)))

/-! ### Operations that preserve quasiconvexity -/

/-- The gradient of `c φ` is `c ∇φ`. -/
theorem grad_const_smul (c : ℝ) (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    grad (fun y => c • φ y) x = c • grad φ x := by
  ext i k
  simp only [grad, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  have h : (fun y => c * φ y i) = c • fun y => φ y i := by
    ext y
    simp
  rw [h, fderiv_const_smul_field]
  rfl

/-- Quasiconvexity is invariant under `X ↦ c X`. -/
theorem quasiconvex_comp_smul {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hf : Quasiconvex f) (c : ℝ) :
    Quasiconvex fun X => f (c • X) := by
  intro A φ K hφ h0 hI
  have hψ : LipschitzWith (‖c‖₊ * K) fun y => c • φ y := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_smul₀, NNReal.coe_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hφ.dist_le_mul x y) (norm_nonneg c)
  have h0ψ : ∀ x ∉ unitCube 2, (fun y => c • φ y) x = 0 := fun x hx => by
    simp [h0 x hx]
  have e : ∀ x, f (c • A + grad (fun y => c • φ y) x) = f (c • (A + grad φ x)) := fun x => by
    rw [grad_const_smul, smul_add]
  have := hf (c • A) _ _ hψ h0ψ (by simpa only [e] using hI)
  simpa only [e] using this

/-- Adding a constant preserves quasiconvexity. -/
theorem quasiconvex_const_add {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hf : Quasiconvex f) (c : ℝ) :
    Quasiconvex fun X => c + f X := by
  intro A φ K hφ h0 hI
  have hc : IntegrableOn (fun _ : Fin 2 → ℝ => c) (unitCube 2) :=
    integrableOn_const volume_unitCube_two_ne_top enorm_ne_top
  have hfI : IntegrableOn (fun x => f (A + grad φ x)) (unitCube 2) := by
    have h : IntegrableOn (fun x => c + f (A + grad φ x) - c) (unitCube 2) := hI.sub hc
    simpa using h
  have h := hf A φ K hφ h0 hfI
  rw [integral_add hc hfI, setIntegral_const, smul_eq_mul, Measure.real, mul_add]
  linarith

/-- The zero function is quasiconvex. -/
theorem quasiconvex_zero : Quasiconvex fun _ : Matrix (Fin 2) (Fin 2) ℝ => (0 : ℝ) :=
  quasiconvex_of_hasPolyaffineSupportAt fun _ =>
    ⟨0, 0, 0, fun _ => by simp [polyaffine], by simp [polyaffine]⟩

/-- Finite nonnegative combinations of continuous quasiconvex functions are quasiconvex. -/
theorem quasiconvex_finset_sum {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    {f : ι → Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hf : ∀ i ∈ s, Quasiconvex (f i)) (hfc : ∀ i ∈ s, Continuous (f i)) :
    Quasiconvex fun X => ∑ i ∈ s, w i * f i X := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using quasiconvex_zero
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfc i (Finset.mem_insert_of_mem hi))
    have hc : Continuous fun X => ∑ i ∈ s, w i * f i X :=
      continuous_finsetSum _ fun i hi =>
        continuous_const.mul (hfc i (Finset.mem_insert_of_mem hi))
    have h := quasiconvex_add_mul (hw a (Finset.mem_insert_self a s)) zero_le_one
      (hf a (Finset.mem_insert_self a s)) (hfc a (Finset.mem_insert_self a s)) ih' hc
    simpa [Finset.sum_insert ha] using h

/-- For `b, g ≥ 0`, the function `X ↦ b |z| + g |w| + c det X` is quasiconvex: a convex function
plus a null Lagrangian. -/
theorem quasiconvex_norm_add_norm_add_det {b g : ℝ} (hb : 0 ≤ b) (hg : 0 ≤ g) (c : ℝ) :
    Quasiconvex fun X : Matrix (Fin 2) (Fin 2) ℝ =>
      b * ‖conformalPart X‖ + g * ‖anticonformalPart X‖ + c * X.det := by
  set F : Matrix (Fin 2) (Fin 2) ℝ → ℝ := fun X =>
    b * ‖conformalPart X‖ + g * ‖anticonformalPart X‖ + c * X.det with hF
  have hiso : IsIsotropic F :=
    isIsotropic_of_eq (Φ := fun x y => b * x + g * y + c * (x ^ 2 - y ^ 2)) fun A => by
      simp only [hF]
      rw [det_eq_norm_sq_sub]
  have hprof : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      profile F x y = b * x + g * y + c * (x ^ 2 - y ^ 2) := by
    intro x y hx hy
    simp only [profile, hF]
    rw [conformalPart_ofComplex, anticonformalPart_ofComplex, det_ofComplex, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hx, Real.norm_of_nonneg hy]
  refine quasiconvex_of_hasPolyaffineSupportAt fun A₀ =>
    hasPolyaffineSupportAt_of_profile hiso A₀ (k := 0) (c := c) hb hg (fun x y hx hy => ?_) ?_
  · rw [hprof x y hx hy]
    simp
  · rw [hprof _ _ (norm_nonneg _) (norm_nonneg _)]
    ring

/-! ### The radial function of an affine function and of a hinge function -/

/-- For an affine `N = n₀ + n₁ r`, the radial function is
`−n₀ (1 − e) |z| − n₀ (1 + e) |w| + e n₁ det X`. -/
theorem radial_affine (e n₀ n₁ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    radial e (fun r => n₀ + n₁ * r) X =
      -n₀ * (1 - e) * ‖conformalPart X‖ + -n₀ * (1 + e) * ‖anticonformalPart X‖ +
        e * n₁ * X.det := by
  rw [det_eq_norm_sq_sub]
  unfold radial radialProfile
  have h : ∫ r in (0 : ℝ)..(‖conformalPart X‖ + ‖anticonformalPart X‖), (n₀ + n₁ * r) =
      n₀ * (‖conformalPart X‖ + ‖anticonformalPart X‖) +
        n₁ * ((‖conformalPart X‖ + ‖anticonformalPart X‖) ^ 2 / 2) := by
    have hi1 : IntervalIntegrable (fun _ : ℝ => n₀) volume 0
        (‖conformalPart X‖ + ‖anticonformalPart X‖) := continuous_const.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun r : ℝ => n₁ * r) volume 0
        (‖conformalPart X‖ + ‖anticonformalPart X‖) :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id]
    simp
    ring
  rw [h]
  ring

/-- The integral of the hinge function `max (r − ρ) 0` from `0` to `s`. -/
theorem integral_hinge {ρ s : ℝ} (hρ : 0 ≤ ρ) (hs : 0 ≤ s) :
    ∫ r in (0 : ℝ)..s, max (r - ρ) 0 = max (s - ρ) 0 ^ 2 / 2 := by
  rcases le_total s ρ with h | h
  · have h1 : ∫ r in (0 : ℝ)..s, max (r - ρ) 0 = ∫ _ in (0 : ℝ)..s, (0 : ℝ) :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hs] at hr
        exact max_eq_right (by linarith [hr.2])
    rw [h1, max_eq_right (by linarith)]
    simp
  · have hcont : Continuous fun r : ℝ => max (r - ρ) 0 := by fun_prop
    have h1 : ∫ r in (0 : ℝ)..ρ, max (r - ρ) 0 = ∫ _ in (0 : ℝ)..ρ, (0 : ℝ) :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hρ] at hr
        exact max_eq_right (by linarith [hr.2])
    have h2 : ∫ r in ρ..s, max (r - ρ) 0 = ∫ r in ρ..s, (r - ρ) :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le h] at hr
        exact max_eq_left (by linarith [hr.1])
    have hi1 : IntervalIntegrable (fun r : ℝ => r) volume ρ s :=
      continuous_id.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun _ : ℝ => ρ) volume ρ s :=
      continuous_const.intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 ρ)
      (hcont.intervalIntegrable ρ s), h1, h2, max_eq_left (by linarith),
      intervalIntegral.integral_sub hi1 hi2, integral_id, intervalIntegral.integral_const,
      intervalIntegral.integral_const]
    simp
    ring

/-- The kernel `K (X) = (σ − 1)₊ (1 + e δ)`, `σ = |z| + |w|`, `δ = |z| − |w|`: the radial function
of the hinge function `max (r − 1) 0`. -/
noncomputable def radialKernel (e : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  max (‖conformalPart X‖ + ‖anticonformalPart X‖ - 1) 0 *
    (1 + e * (‖conformalPart X‖ - ‖anticonformalPart X‖))

/-- The kernel is continuous. -/
theorem continuous_radialKernel (e : ℝ) : Continuous (radialKernel e) := by
  have h1 := continuous_norm_conformalPart
  have h2 := continuous_norm_anticonformalPart
  unfold radialKernel
  exact (((h1.add h2).sub continuous_const).max continuous_const).mul
    (continuous_const.add (continuous_const.mul (h1.sub h2)))

/-- For `e = 1` the kernel is the truncated determinant `L` at `J X`, plus the determinant. -/
theorem radialKernel_one (X : Matrix (Fin 2) (Fin 2) ℝ) :
    radialKernel 1 X = Agazzi.integrandL (reflection * X) + X.det := by
  have h1 : ‖Agazzi.conformalPart (reflection * X)‖ = ‖anticonformalPart X‖ := by
    change ‖conformalPart (reflection * X)‖ = _
    rw [conformalPart_reflection_mul, RCLike.norm_conj]
  have h2 : ‖Agazzi.anticonformalPart (reflection * X)‖ = ‖conformalPart X‖ := by
    change ‖anticonformalPart (reflection * X)‖ = _
    rw [anticonformalPart_reflection_mul, RCLike.norm_conj]
  rw [Agazzi.integrandL, h1, h2, det_eq_norm_sq_sub, radialKernel]
  split_ifs with h
  · rw [max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (by linarith)]
    ring

/-- For `e = −1` the kernel is the truncated determinant `L`, minus the determinant. -/
theorem radialKernel_neg_one (X : Matrix (Fin 2) (Fin 2) ℝ) :
    radialKernel (-1) X = Agazzi.integrandL X - X.det := by
  have h1 : ‖Agazzi.conformalPart X‖ = ‖conformalPart X‖ := rfl
  have h2 : ‖Agazzi.anticonformalPart X‖ = ‖anticonformalPart X‖ := rfl
  rw [Agazzi.integrandL, h1, h2, det_eq_norm_sq_sub, radialKernel]
  split_ifs with h
  · rw [max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (by linarith)]
    ring

/-- A multiple of the determinant is quasiconvex: it is a null Lagrangian. -/
theorem quasiconvex_const_mul_det (c : ℝ) :
    Quasiconvex fun X : Matrix (Fin 2) (Fin 2) ℝ => c * X.det :=
  quasiconvex_of_hasPolyaffineSupportAt fun _ =>
    ⟨0, 0, c, fun _ => by simp [polyaffine], by simp [polyaffine]⟩

/-- The kernel is quasiconvex: the truncated determinant is (arXiv:2609.28311, Theorem 1), the
reflection preserves quasiconvexity, and the determinant is a null Lagrangian. -/
theorem quasiconvex_radialKernel {e : ℝ} (he : e = 1 ∨ e = -1) :
    Quasiconvex (radialKernel e) := by
  have hL : Quasiconvex Agazzi.integrandL := Agazzi.quasiconvex_integrandL
  have hLc : Continuous Agazzi.integrandL := Agazzi.continuous_integrandL
  have hdc : ∀ c : ℝ, Continuous fun X : Matrix (Fin 2) (Fin 2) ℝ => c * X.det := fun c =>
    continuous_const.mul continuous_id.matrix_det
  rcases he with rfl | rfl
  · have h := quasiconvex_add_mul zero_le_one zero_le_one (quasiconvex_comp_reflection_mul hL)
      (hLc.comp (continuous_const.mul continuous_id)) (quasiconvex_const_mul_det 1) (hdc 1)
    have e : radialKernel 1 = fun X =>
        1 * Agazzi.integrandL (reflection * X) + 1 * (1 * X.det) := by
      funext X
      rw [radialKernel_one]
      ring
    rw [e]
    exact h
  · have h := quasiconvex_add_mul zero_le_one zero_le_one hL hLc (quasiconvex_const_mul_det (-1))
      (hdc (-1))
    have e : radialKernel (-1) = fun X => 1 * Agazzi.integrandL X + 1 * (-1 * X.det) := by
      funext X
      rw [radialKernel_neg_one]
      ring
    rw [e]
    exact h

/-- For the hinge function `N = max (r − ρ) 0`, `ρ > 0`, the radial function is
`ρ² K (X/ρ)`. -/
theorem radial_hinge (e : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    radial e (fun r => max (r - ρ) 0) X = ρ ^ 2 * radialKernel e (ρ⁻¹ • X) := by
  have hx := norm_nonneg (conformalPart X)
  have hy := norm_nonneg (anticonformalPart X)
  have hz : ‖conformalPart (ρ⁻¹ • X)‖ = ρ⁻¹ * ‖conformalPart X‖ := by
    rw [conformalPart_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hρ.le)]
  have hw : ‖anticonformalPart (ρ⁻¹ • X)‖ = ρ⁻¹ * ‖anticonformalPart X‖ := by
    rw [anticonformalPart_smul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 hρ.le)]
  unfold radial radialProfile
  beta_reduce
  rw [integral_hinge hρ.le (add_nonneg hx hy), radialKernel, hz, hw]
  rcases le_or_gt (‖conformalPart X‖ + ‖anticonformalPart X‖) ρ with h | h
  · have h1 : ρ⁻¹ * ‖conformalPart X‖ + ρ⁻¹ * ‖anticonformalPart X‖ - 1 ≤ 0 := by
      rw [← mul_add, sub_nonpos, inv_mul_le_iff₀ hρ]
      linarith
    rw [max_eq_right (by linarith), max_eq_right h1]
    ring
  · have h1 : 0 ≤ ρ⁻¹ * ‖conformalPart X‖ + ρ⁻¹ * ‖anticonformalPart X‖ - 1 := by
      rw [← mul_add, sub_nonneg, le_inv_mul_iff₀ hρ]
      linarith
    rw [max_eq_left (by linarith), max_eq_left h1]
    field_simp
    ring

/-! ### Linearity and the approximation -/

/-- The radial function is linear in `N`. -/
theorem radial_add_sum (e : ℝ) {ι : Type*} (s : Finset ι) {N₀ : ℝ → ℝ} (hN₀ : Continuous N₀)
    (w : ι → ℝ) {M : ι → ℝ → ℝ} (hM : ∀ i, Continuous (M i))
    (X : Matrix (Fin 2) (Fin 2) ℝ) :
    radial e (fun r => N₀ r + ∑ i ∈ s, w i * M i r) X =
      radial e N₀ X + ∑ i ∈ s, w i * radial e (M i) X := by
  unfold radial radialProfile
  have hsumc : Continuous fun r => ∑ i ∈ s, w i * M i r :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hM i)
  beta_reduce
  rw [intervalIntegral.integral_add (hN₀.intervalIntegrable _ _) (hsumc.intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (f := fun i r => w i * M i r) fun i _ =>
      (continuous_const.mul (hM i)).intervalIntegrable _ _]
  simp only [intervalIntegral.integral_const_mul]
  have hsum : ∀ a : ℝ, ∑ i ∈ s, w i * (a * M i (‖conformalPart X‖ + ‖anticonformalPart X‖) -
      2 * ∫ r in (0 : ℝ)..(‖conformalPart X‖ + ‖anticonformalPart X‖), M i r) =
      a * ∑ i ∈ s, w i * M i (‖conformalPart X‖ + ‖anticonformalPart X‖) -
        2 * ∑ i ∈ s, w i * ∫ r in (0 : ℝ)..(‖conformalPart X‖ + ‖anticonformalPart X‖),
          M i r := by
    intro a
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  ring

/-- If `N` and `N'` differ by at most `ε` on `[0, R]`, their radial functions differ by at most
`4 R ε` at the matrices with `|z| + |w| ≤ R`. -/
theorem abs_radial_sub_le {e : ℝ} (he : e = 1 ∨ e = -1) {N N' : ℝ → ℝ} (hN : Continuous N)
    (hN' : Continuous N') {R ε : ℝ} (h : ∀ r ∈ Icc 0 R, |N r - N' r| ≤ ε)
    {X : Matrix (Fin 2) (Fin 2) ℝ} (hX : ‖conformalPart X‖ + ‖anticonformalPart X‖ ≤ R) :
    |radial e N X - radial e N' X| ≤ 4 * R * ε := by
  have hx := norm_nonneg (conformalPart X)
  have hy := norm_nonneg (anticonformalPart X)
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = ‖conformalPart X‖ + ‖anticonformalPart X‖ := ⟨_, rfl⟩
  have hσ0 : 0 ≤ σ := by rw [hσ]; exact add_nonneg hx hy
  have hσR : σ ≤ R := by rw [hσ]; exact hX
  have hε : 0 ≤ ε := (abs_nonneg _).trans (h 0 ⟨le_rfl, hσ0.trans hσR⟩)
  have h1 : |N σ - N' σ| ≤ ε := h σ ⟨hσ0, hσR⟩
  have h2 : |∫ r in (0 : ℝ)..σ, (N r - N' r)| ≤ ε * σ := by
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := σ) (C := ε)
      (f := fun r => N r - N' r) fun r hr => by
        rw [uIoc_of_le hσ0] at hr
        exact h r ⟨hr.1.le, hr.2.trans hσR⟩
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hσ0] at h3
  have h4 : |σ + e * (‖conformalPart X‖ - ‖anticonformalPart X‖)| ≤ 2 * σ := by
    rcases he with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith
  have hid : radial e N X - radial e N' X =
      (σ + e * (‖conformalPart X‖ - ‖anticonformalPart X‖)) * (N σ - N' σ) -
        2 * ∫ r in (0 : ℝ)..σ, (N r - N' r) := by
    unfold radial radialProfile
    rw [intervalIntegral.integral_sub (hN.intervalIntegrable _ _) (hN'.intervalIntegrable _ _),
      hσ]
    ring
  rw [hid]
  have h5 : |(σ + e * (‖conformalPart X‖ - ‖anticonformalPart X‖)) * (N σ - N' σ)| ≤
      2 * σ * ε := by
    rw [abs_mul]
    exact mul_le_mul h4 h1 (abs_nonneg _) (by linarith)
  have h6 : |2 * ∫ r in (0 : ℝ)..σ, (N r - N' r)| ≤ 2 * (ε * σ) := by
    rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left h2 zero_le_two
  have h7 : 4 * σ * ε ≤ 4 * R * ε :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσR (by norm_num)) hε
  calc |(σ + e * (‖conformalPart X‖ - ‖anticonformalPart X‖)) * (N σ - N' σ) -
        2 * ∫ r in (0 : ℝ)..σ, (N r - N' r)|
      ≤ |(σ + e * (‖conformalPart X‖ - ‖anticonformalPart X‖)) * (N σ - N' σ)| +
        |2 * ∫ r in (0 : ℝ)..σ, (N r - N' r)| := abs_sub _ _
    _ ≤ 4 * R * ε := by linarith

/-- The moduli of the coordinates of a matrix with entries bounded by `K` add up to at most
`4 K`. -/
theorem norm_add_norm_le_of_abs_le {G : Matrix (Fin 2) (Fin 2) ℝ} {K : ℝ}
    (hG : ∀ i k, |G i k| ≤ K) : ‖conformalPart G‖ + ‖anticonformalPart G‖ ≤ 4 * K := by
  have h00 := abs_le.1 (hG 0 0)
  have h01 := abs_le.1 (hG 0 1)
  have h10 := abs_le.1 (hG 1 0)
  have h11 := abs_le.1 (hG 1 1)
  have hz := Complex.norm_le_abs_re_add_abs_im (conformalPart G)
  have hw := Complex.norm_le_abs_re_add_abs_im (anticonformalPart G)
  have e1 : (conformalPart G).re = (G 0 0 + G 1 1) / 2 := rfl
  have e2 : (conformalPart G).im = (G 1 0 - G 0 1) / 2 := rfl
  have e3 : (anticonformalPart G).re = (G 0 0 - G 1 1) / 2 := rfl
  have e4 : (anticonformalPart G).im = (G 1 0 + G 0 1) / 2 := rfl
  have a1 : |(conformalPart G).re| ≤ K := by
    rw [e1, abs_le]
    constructor <;> linarith
  have a2 : |(conformalPart G).im| ≤ K := by
    rw [e2, abs_le]
    constructor <;> linarith
  have a3 : |(anticonformalPart G).re| ≤ K := by
    rw [e3, abs_le]
    constructor <;> linarith
  have a4 : |(anticonformalPart G).im| ≤ K := by
    rw [e4, abs_le]
    constructor <;> linarith
  linarith

/-- For a `K`-Lipschitz test map `φ`, the matrices `A + ∇φ` have `|z| + |w| ≤ |z_A| + |w_A| + 4 K`:
Jensen's inequality at `A` sees a bounded set of matrices only. -/
theorem norm_add_norm_add_grad_le {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    ‖conformalPart (A + grad φ x)‖ + ‖anticonformalPart (A + grad φ x)‖ ≤
      ‖conformalPart A‖ + ‖anticonformalPart A‖ + 4 * K := by
  have h := norm_add_norm_le_of_abs_le (G := grad φ x) (K := K) fun i k => rd_grad_abs_le hφ x i k
  have hz : ‖conformalPart (A + grad φ x)‖ ≤ ‖conformalPart A‖ + ‖conformalPart (grad φ x)‖ := by
    rw [conformalPart_add]
    exact norm_add_le _ _
  have hw : ‖anticonformalPart (A + grad φ x)‖ ≤
      ‖anticonformalPart A‖ + ‖anticonformalPart (grad φ x)‖ := by
    rw [anticonformalPart_add]
    exact norm_add_le _ _
  linarith

/-! ### Quasiconvexity -/

/-- The radial function of `N = n₀ + n₁ r + ∑ wᵢ max (r − ρᵢ) 0`, with `n₀ ≤ 0`, `wᵢ ≥ 0` and
`ρᵢ > 0`, is quasiconvex: a nonnegative combination of a convex function plus a null Lagrangian
and of scaled kernels. -/
theorem quasiconvex_radial_hinge_sum {e : ℝ} (he : e = 1 ∨ e = -1) {n₀ : ℝ} (hn₀ : n₀ ≤ 0)
    (n₁ : ℝ) {ι : Type*} (s : Finset ι) {w ρ : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hρ : ∀ i, 0 < ρ i) :
    Quasiconvex (radial e fun r => n₀ + n₁ * r + ∑ i ∈ s, w i * max (r - ρ i) 0) := by
  have haffc : Continuous fun r : ℝ => n₀ + n₁ * r := by fun_prop
  have hhc : ∀ i, Continuous fun r : ℝ => max (r - ρ i) 0 := fun i => by fun_prop
  have hb : 0 ≤ -n₀ * (1 - e) := by
    rcases he with rfl | rfl <;> nlinarith
  have hg : 0 ≤ -n₀ * (1 + e) := by
    rcases he with rfl | rfl <;> nlinarith
  have haff : Quasiconvex (radial e fun r => n₀ + n₁ * r) := by
    have e1 : (radial e fun r => n₀ + n₁ * r) = fun X =>
        -n₀ * (1 - e) * ‖conformalPart X‖ + -n₀ * (1 + e) * ‖anticonformalPart X‖ +
          e * n₁ * X.det := funext fun X => radial_affine e n₀ n₁ X
    rw [e1]
    exact quasiconvex_norm_add_norm_add_det hb hg (e * n₁)
  have hh : ∀ i, Quasiconvex (radial e fun r => max (r - ρ i) 0) := by
    intro i
    have e1 : (radial e fun r => max (r - ρ i) 0) = fun X =>
        ρ i ^ 2 * radialKernel e ((ρ i)⁻¹ • X) := funext fun X => radial_hinge e (hρ i) X
    rw [e1]
    exact Agazzi.quasiconvex_const_mul
      (quasiconvex_comp_smul (quasiconvex_radialKernel he) (ρ i)⁻¹) (pow_pos (hρ i) 2)
  have hsum := quasiconvex_finset_sum s (w := w) (f := fun i => radial e fun r => max (r - ρ i) 0)
    (fun i _ => hw i) (fun i _ => hh i) (fun i _ => continuous_radial e (hhc i))
  have hsumc : Continuous fun X => ∑ i ∈ s, w i * radial e (fun r => max (r - ρ i) 0) X :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_radial e (hhc i))
  have h := quasiconvex_add_mul zero_le_one zero_le_one haff (continuous_radial e haffc) hsum
    hsumc
  have e2 : (radial e fun r => n₀ + n₁ * r + ∑ i ∈ s, w i * max (r - ρ i) 0) = fun X =>
      1 * radial e (fun r => n₀ + n₁ * r) X +
        1 * ∑ i ∈ s, w i * radial e (fun r => max (r - ρ i) 0) X := by
    funext X
    rw [radial_add_sum e s haffc w hhc X]
    ring
  rw [e2]
  exact h

/-- **Proposition 6.8, radial integration of the truncated determinant.** If `N` is convex on
`[0, ∞)`, continuous, and `N 0 ≤ 0`, then `X ↦ (σ + e δ) N (σ) − 2 ∫₀^σ N` is quasiconvex, for
`e = 1` and for `e = −1`. -/
theorem quasiconvex_radial {e : ℝ} (he : e = 1 ∨ e = -1) {N : ℝ → ℝ}
    (hN : ConvexOn ℝ (Ici 0) N) (hNc : Continuous N) (hN0 : N 0 ≤ 0) :
    Quasiconvex (radial e N) := by
  intro A φ K hφ h0 hI
  rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul]
  have hfin := volume_unitCube_two_ne_top
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖conformalPart A‖ + ‖anticonformalPart A‖ + 4 * K + 1 := ⟨_, rfl⟩
  have hRpos : 0 < R := by
    rw [hR]
    positivity
  have hRA : ‖conformalPart A‖ + ‖anticonformalPart A‖ ≤ R := by
    rw [hR]
    have : (0 : ℝ) ≤ 4 * K := by positivity
    linarith
  have hRx : ∀ x, ‖conformalPart (A + grad φ x)‖ + ‖anticonformalPart (A + grad φ x)‖ ≤ R := by
    intro x
    have := norm_add_norm_add_grad_le hφ A x
    linarith
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = η / (8 * R) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hε]
    positivity
  have h8 : 8 * R * ε = η := by
    rw [hε]
    field_simp
  obtain ⟨n, n₁, w, ρ, hw, hρ, happ⟩ :=
    (hN.subset Icc_subset_Ici_self (convex_Icc 0 R)).exists_hinge_approx hRpos hNc.continuousOn
      hεpos
  obtain ⟨N', hN'⟩ : ∃ N' : ℝ → ℝ,
      N' = fun r => N 0 + n₁ * r + ∑ i, w i * max (r - ρ i) 0 := ⟨_, rfl⟩
  have hN'c : Continuous N' := by
    rw [hN']
    exact (continuous_const.add (continuous_const.mul continuous_id)).add
      (continuous_finsetSum _ fun i _ => continuous_const.mul
        ((continuous_id.sub continuous_const).max continuous_const))
  have hqc : Quasiconvex (radial e N') := by
    rw [hN']
    exact quasiconvex_radial_hinge_sum he hN0 n₁ Finset.univ hw hρ
  have happ' : ∀ r ∈ Icc 0 R, |N r - N' r| ≤ ε := by
    rw [hN']
    exact happ
  have hI' := nl_integrableOn_cube hφ (continuous_radial e hN'c) A (unitCube 2) hfin
  have hJ := hqc A φ K hφ h0 hI'
  rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul] at hJ
  have hA := abs_le.1 (abs_radial_sub_le he hNc hN'c happ' hRA)
  have hc : IntegrableOn (fun _ : Fin 2 → ℝ => 4 * R * ε) (unitCube 2) :=
    integrableOn_const hfin enorm_ne_top
  have hmono : ∫ x in unitCube 2, radial e N' (A + grad φ x) ≤
      ∫ x in unitCube 2, (radial e N (A + grad φ x) + 4 * R * ε) :=
    setIntegral_mono hI' (hI.add hc) fun x => by
      have := abs_le.1 (abs_radial_sub_le he hNc hN'c happ' (hRx x))
      linarith
  rw [integral_add hI hc, setIntegral_const, smul_eq_mul, Measure.real, rd_volume_unitCube,
    ENNReal.toReal_one, one_mul] at hmono
  linarith

end HomogeneousIsotropic
