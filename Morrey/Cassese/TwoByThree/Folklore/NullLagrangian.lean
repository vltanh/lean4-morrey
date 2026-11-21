module

public import Morrey.Cassese.TwoByThree.Basic
public import Morrey.Common.External.Dacorogna.Plancherel
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Proposition 5.1: minors of order at most `3` are null Lagrangians

For Lipschitz maps vanishing outside a compact set, the integrals of the `1 × 1`, `2 × 2` and
`3 × 3` minors of the gradient vanish: for smooth compactly supported maps by the divergence
identities (`∂_a u ∂_b v − ∂_b u ∂_a v = ∂_a (u ∂_b v) − ∂_b (u ∂_a v)`, and the cofactor (Piola)
identity for `3 × 3`), and for Lipschitz maps by mollification (the tools of
`Morrey.Common.External.Dacorogna.Plancherel`) and dominated convergence. This is the direction
"minors ⇒ quasiaffine" of Dacorogna, Theorem 5.20 (Ball's null Lagrangians).

Helpers are prefixed `tbt6_`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ContDiff Pointwise

namespace Cassese

variable {m : ℕ}

/-- The partial derivative `∂_a g`. -/
noncomputable def tbt6D (a : Fin m) (g : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) : ℝ :=
  fderiv ℝ g x (Pi.single a 1)

theorem tbt6_D_contDiff {g : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (a : Fin m) :
    ContDiff ℝ ∞ (tbt6D a g) :=
  (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem tbt6_D_mul {g h : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (a : Fin m) : tbt6D a (fun x => g x * h x) = fun x => tbt6D a g x * h x + g x * tbt6D a h x := by
  funext x
  simp only [tbt6D]
  rw [fderiv_fun_mul ((hg.differentiable (by simp)) x) ((hh.differentiable (by simp)) x)]
  simp [smul_eq_mul]
  ring

theorem tbt6_D_sub {g h : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (a : Fin m) : tbt6D a (fun x => g x - h x) = fun x => tbt6D a g x - tbt6D a h x := by
  funext x
  simp only [tbt6D]
  rw [fderiv_fun_sub ((hg.differentiable (by simp)) x) ((hh.differentiable (by simp)) x)]
  rfl

theorem tbt6_D_add {g h : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (a : Fin m) : tbt6D a (fun x => g x + h x) = fun x => tbt6D a g x + tbt6D a h x := by
  funext x
  simp only [tbt6D]
  rw [fderiv_fun_add ((hg.differentiable (by simp)) x) ((hh.differentiable (by simp)) x)]
  rfl

/-- Symmetry of second derivatives: `∂_a ∂_b g = ∂_b ∂_a g`. -/
theorem tbt6_D_comm {g : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (a b : Fin m) :
    tbt6D a (tbt6D b g) = tbt6D b (tbt6D a g) := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have hsymm := (hg.contDiffAt (x := x)).isSymmSndFDerivAt (n := ∞) (by simp)
  show fderiv ℝ (fun y => fderiv ℝ g y (Pi.single b 1)) x (Pi.single a 1) =
    fderiv ℝ (fun y => fderiv ℝ g y (Pi.single a 1)) x (Pi.single b 1)
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hsymm _ _

/-- `∫ ∂_a w = 0` for smooth compactly supported `w`. -/
theorem tbt6_integral_D_eq_zero {w : (Fin m → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w)
    (hwc : HasCompactSupport w) (a : Fin m) : ∫ x, tbt6D a w x = 0 := by
  obtain ⟨K, hK⟩ := hw.lipschitzWith_of_hasCompactSupport hwc (by simp) (𝕂 := ℝ)
  exact External.Dacorogna.plancherel_integral_fderiv_eq_zero hK hwc _

theorem tbt6_hasCompactSupport_D {g : (Fin m → ℝ) → ℝ} (hgc : HasCompactSupport g) (a : Fin m) :
    HasCompactSupport (tbt6D a g) :=
  (hgc.fderiv ℝ).comp_left (g := fun L : (Fin m → ℝ) →L[ℝ] ℝ => L (Pi.single a 1)) rfl

theorem tbt6_integrable_of_smooth {g : (Fin m → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) : Integrable g :=
  hg.continuous.integrable_of_hasCompactSupport hgc

/-- **`2 × 2` minors, smooth case**: `∫ (∂_a u ∂_b v − ∂_b u ∂_a v) = 0`. -/
theorem tbt6_null2_smooth {u v : (Fin m → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (huc : HasCompactSupport u) (a b : Fin m) :
    ∫ x, (tbt6D a u x * tbt6D b v x - tbt6D b u x * tbt6D a v x) = 0 := by
  have hDv := fun c => tbt6_D_contDiff hv c
  have e : (fun x => tbt6D a u x * tbt6D b v x - tbt6D b u x * tbt6D a v x) =
      fun x => tbt6D a (fun y => u y * tbt6D b v y) x - tbt6D b (fun y => u y * tbt6D a v y) x := by
    rw [tbt6_D_mul hu (hDv b), tbt6_D_mul hu (hDv a), tbt6_D_comm hv a b]
    funext x; ring
  rw [e]
  have hw1 : ContDiff ℝ ∞ fun y => u y * tbt6D b v y := hu.mul (hDv b)
  have hw2 : ContDiff ℝ ∞ fun y => u y * tbt6D a v y := hu.mul (hDv a)
  have hc1 : HasCompactSupport fun y => u y * tbt6D b v y := huc.mul_right
  have hc2 : HasCompactSupport fun y => u y * tbt6D a v y := huc.mul_right
  rw [integral_sub (tbt6_integrable_of_smooth (tbt6_D_contDiff hw1 a) (tbt6_hasCompactSupport_D hc1 a))
    (tbt6_integrable_of_smooth (tbt6_D_contDiff hw2 b) (tbt6_hasCompactSupport_D hc2 b)),
    tbt6_integral_D_eq_zero hw1 hc1, tbt6_integral_D_eq_zero hw2 hc2, sub_zero]

/-- The `3 × 3` minor `det [∂_{a_j} u_i]`. -/
noncomputable def tbt6Det3 (u₀ u₁ u₂ : (Fin m → ℝ) → ℝ) (a₀ a₁ a₂ : Fin m) (x : Fin m → ℝ) : ℝ :=
  tbt6D a₀ u₀ x * (tbt6D a₁ u₁ x * tbt6D a₂ u₂ x - tbt6D a₂ u₁ x * tbt6D a₁ u₂ x) -
    tbt6D a₁ u₀ x * (tbt6D a₀ u₁ x * tbt6D a₂ u₂ x - tbt6D a₂ u₁ x * tbt6D a₀ u₂ x) +
    tbt6D a₂ u₀ x * (tbt6D a₀ u₁ x * tbt6D a₁ u₂ x - tbt6D a₁ u₁ x * tbt6D a₀ u₂ x)

/-- **`3 × 3` minors, smooth case**: `∫ det [∂_{a_j} u_i] = 0`, by
`det = Σ_j ∂_{a_j} (u₀ C_j)` with the cofactors `C_j` of the first row, whose divergence
`Σ_j ∂_{a_j} C_j` vanishes (Piola). -/
theorem tbt6_null3_smooth {u₀ u₁ u₂ : (Fin m → ℝ) → ℝ} (h₀ : ContDiff ℝ ∞ u₀)
    (h₁ : ContDiff ℝ ∞ u₁) (h₂ : ContDiff ℝ ∞ u₂) (hc : HasCompactSupport u₀)
    (a₀ a₁ a₂ : Fin m) : ∫ x, tbt6Det3 u₀ u₁ u₂ a₀ a₁ a₂ x = 0 := by
  have D1 := fun c => tbt6_D_contDiff h₁ c
  have D2 := fun c => tbt6_D_contDiff h₂ c
  -- the cofactors of the first row
  set C₀ : (Fin m → ℝ) → ℝ := fun x => tbt6D a₁ u₁ x * tbt6D a₂ u₂ x - tbt6D a₂ u₁ x * tbt6D a₁ u₂ x
  set C₁ : (Fin m → ℝ) → ℝ := fun x => tbt6D a₀ u₁ x * tbt6D a₂ u₂ x - tbt6D a₂ u₁ x * tbt6D a₀ u₂ x
  set C₂ : (Fin m → ℝ) → ℝ := fun x => tbt6D a₀ u₁ x * tbt6D a₁ u₂ x - tbt6D a₁ u₁ x * tbt6D a₀ u₂ x
  have hC₀ : ContDiff ℝ ∞ C₀ := ((D1 a₁).mul (D2 a₂)).sub ((D1 a₂).mul (D2 a₁))
  have hC₁ : ContDiff ℝ ∞ C₁ := ((D1 a₀).mul (D2 a₂)).sub ((D1 a₂).mul (D2 a₀))
  have hC₂ : ContDiff ℝ ∞ C₂ := ((D1 a₀).mul (D2 a₁)).sub ((D1 a₁).mul (D2 a₀))
  -- the Piola identity
  have hP : ∀ x, tbt6D a₀ C₀ x - tbt6D a₁ C₁ x + tbt6D a₂ C₂ x = 0 := by
    intro x
    simp only [C₀, C₁, C₂]
    rw [tbt6_D_sub ((D1 a₁).mul (D2 a₂)) ((D1 a₂).mul (D2 a₁)),
      tbt6_D_sub ((D1 a₀).mul (D2 a₂)) ((D1 a₂).mul (D2 a₀)),
      tbt6_D_sub ((D1 a₀).mul (D2 a₁)) ((D1 a₁).mul (D2 a₀))]
    simp only
    rw [tbt6_D_mul (D1 a₁) (D2 a₂), tbt6_D_mul (D1 a₂) (D2 a₁), tbt6_D_mul (D1 a₀) (D2 a₂),
      tbt6_D_mul (D1 a₂) (D2 a₀), tbt6_D_mul (D1 a₀) (D2 a₁), tbt6_D_mul (D1 a₁) (D2 a₀)]
    simp only
    rw [tbt6_D_comm h₁ a₀ a₁, tbt6_D_comm h₁ a₀ a₂, tbt6_D_comm h₁ a₁ a₂,
      tbt6_D_comm h₂ a₀ a₁, tbt6_D_comm h₂ a₀ a₂, tbt6_D_comm h₂ a₁ a₂]
    ring
  have e : tbt6Det3 u₀ u₁ u₂ a₀ a₁ a₂ = fun x =>
      tbt6D a₀ (fun y => u₀ y * C₀ y) x - tbt6D a₁ (fun y => u₀ y * C₁ y) x +
        tbt6D a₂ (fun y => u₀ y * C₂ y) x := by
    rw [tbt6_D_mul h₀ hC₀, tbt6_D_mul h₀ hC₁, tbt6_D_mul h₀ hC₂]
    funext x
    have := hP x
    simp only [tbt6Det3]
    linear_combination (-(u₀ x)) * this
  rw [e]
  have w0 : ContDiff ℝ ∞ fun y => u₀ y * C₀ y := h₀.mul hC₀
  have w1 : ContDiff ℝ ∞ fun y => u₀ y * C₁ y := h₀.mul hC₁
  have w2 : ContDiff ℝ ∞ fun y => u₀ y * C₂ y := h₀.mul hC₂
  have c0 : HasCompactSupport fun y => u₀ y * C₀ y := hc.mul_right
  have c1 : HasCompactSupport fun y => u₀ y * C₁ y := hc.mul_right
  have c2 : HasCompactSupport fun y => u₀ y * C₂ y := hc.mul_right
  have i0 := tbt6_integrable_of_smooth (tbt6_D_contDiff w0 a₀) (tbt6_hasCompactSupport_D c0 a₀)
  have i1 := tbt6_integrable_of_smooth (tbt6_D_contDiff w1 a₁) (tbt6_hasCompactSupport_D c1 a₁)
  have i2 := tbt6_integrable_of_smooth (tbt6_D_contDiff w2 a₂) (tbt6_hasCompactSupport_D c2 a₂)
  beta_reduce
  rw [integral_add (f := fun x => tbt6D a₀ (fun y => u₀ y * C₀ y) x -
      tbt6D a₁ (fun y => u₀ y * C₁ y) x) (i0.sub i1) i2,
    integral_sub i0 i1, tbt6_integral_D_eq_zero w0 c0,
    tbt6_integral_D_eq_zero w1 c1, tbt6_integral_D_eq_zero w2 c2]
  ring

/-- **Mollification**: an identity `∫ Φ (∇ψ) = 0`, valid for smooth compactly supported `ψ`,
passes to compactly supported Lipschitz maps, for continuous `Φ` with `Φ (0) = 0` (the
mollifications `ρ_n ⋆ u_i` are smooth with compact support, and their derivatives are bounded,
supported in a fixed compact set and converge almost everywhere). -/
theorem tbt6_lipschitz_limit {k : ℕ} (u : Fin k → (Fin m → ℝ) → ℝ) (K : Fin k → NNReal)
    (hu : ∀ i, LipschitzWith (K i) (u i)) (huc : ∀ i, HasCompactSupport (u i))
    (Φ : (Fin k → Fin m → ℝ) → ℝ) (hΦ : Continuous Φ) (hΦ0 : Φ 0 = 0)
    (hsmooth : ∀ ψ : Fin k → (Fin m → ℝ) → ℝ, (∀ i, ContDiff ℝ ∞ (ψ i)) →
      (∀ i, HasCompactSupport (ψ i)) → ∫ x, Φ (fun i a => tbt6D a (ψ i) x) = 0) :
    ∫ x, Φ (fun i a => fderiv ℝ (u i) x (Pi.single a 1)) = 0 := by
  set ψ : ℕ → Fin k → (Fin m → ℝ) → ℝ :=
    fun n i => External.Dacorogna.plancherelMollify volume (External.Dacorogna.plancherelBump m n)
      (u i) with hψ
  have hψs : ∀ n i, ContDiff ℝ ∞ (ψ n i) := fun n i =>
    External.Dacorogna.plancherelMollify_contDiff _ (hu i).continuous
  have hψc : ∀ n i, HasCompactSupport (ψ n i) := fun n i =>
    External.Dacorogna.plancherelMollify_hasCompactSupport _ (huc i)
  have hn : ∀ n, ∫ x, Φ (fun i a => tbt6D a (ψ n i) x) = 0 := fun n => hsmooth _ (hψs n) (hψc n)
  have hbd : ∀ n i (v : Fin m → ℝ) x, |fderiv ℝ (ψ n i) x v| ≤ K i * ‖v‖ := by
    intro n i v x
    rw [External.Dacorogna.plancherelMollify_fderiv _ (hu i)]
    exact External.Dacorogna.plancherelMollify_abs_le _ (fun y => by
      simpa [Real.norm_eq_abs] using norm_lineDeriv_le_of_lipschitz ℝ (hu i) (x₀ := y) (v := v)) x
  set S := ⋃ i, Metric.closedBall (0 : Fin m → ℝ) 1 + tsupport (u i) with hS
  have hSc : IsCompact S := isCompact_iUnion fun i => (isCompact_closedBall _ _).add (huc i)
  have hsupp : ∀ n i (v : Fin m → ℝ) x, x ∉ S → fderiv ℝ (ψ n i) x v = 0 := by
    intro n i v x hx
    rw [External.Dacorogna.plancherelMollify_fderiv _ (hu i)]
    exact External.Dacorogna.plancherelMollify_eq_zero _
      (External.Dacorogna.plancherelBump_rOut_le m n)
      (fun y hy => External.Dacorogna.plancherel_lineDeriv_eq_zero_of_notMem hy v)
      (fun h => hx (Set.mem_iUnion.mpr ⟨i, h⟩))
  -- a bound for `Φ` on the box of admissible gradients
  set B : Set (Fin k → Fin m → ℝ) :=
    Set.pi Set.univ fun i => Set.pi Set.univ fun a =>
      Set.Icc (-(K i * ‖(Pi.single a 1 : Fin m → ℝ)‖)) (K i * ‖(Pi.single a 1 : Fin m → ℝ)‖)
  have hBc : IsCompact B := isCompact_univ_pi fun i => isCompact_univ_pi fun a => isCompact_Icc
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hΦ.continuousOn
  have hmem : ∀ n x, (fun i a => tbt6D a (ψ n i) x) ∈ B := by
    intro n x i _ a _
    exact abs_le.mp (hbd n i _ x)
  have hlim : Tendsto (fun n => ∫ x, Φ (fun i a => tbt6D a (ψ n i) x)) atTop
      (𝓝 (∫ x, Φ (fun i a => fderiv ℝ (u i) x (Pi.single a 1)))) := by
    refine tendsto_integral_of_dominated_convergence (S.indicator fun _ => M) (fun n => ?_) ?_
      (fun n => ?_) ?_
    · have : Continuous fun x => (fun i a => tbt6D a (ψ n i) x) :=
        continuous_pi fun i => continuous_pi fun a => (tbt6_D_contDiff (hψs n i) a).continuous
      exact (hΦ.comp this).aestronglyMeasurable
    · exact (integrable_indicator_iff hSc.measurableSet).2
        (integrableOn_const hSc.measure_lt_top.ne)
    · filter_upwards with x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        exact hM _ (hmem n x)
      · rw [Set.indicator_of_notMem hx]
        have : (fun i a => tbt6D a (ψ n i) x) = 0 := by
          funext i a; exact hsupp n i _ x hx
        rw [this, hΦ0, norm_zero]
    · have hae : ∀ᵐ x, ∀ i : Fin k, ∀ a : Fin m, Tendsto
          (fun n => fderiv ℝ (ψ n i) x (Pi.single a 1)) atTop
          (𝓝 (fderiv ℝ (u i) x (Pi.single a 1))) := by
        rw [ae_all_iff]; intro i
        rw [ae_all_iff]; intro a
        exact External.Dacorogna.plancherel_ae_tendsto (hu i) _
      filter_upwards [hae] with x hx
      exact (hΦ.tendsto _).comp (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun a => hx i a)
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun n => (hn n).symm) hlim |>.symm

/-- **`2 × 2` minors are null Lagrangians** (Lipschitz, compact support). -/
theorem tbt6_null2 {u v : (Fin m → ℝ) → ℝ} {Ku Kv : NNReal} (hu : LipschitzWith Ku u)
    (hv : LipschitzWith Kv v) (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (a b : Fin m) :
    ∫ x, (fderiv ℝ u x (Pi.single a 1) * fderiv ℝ v x (Pi.single b 1) -
      fderiv ℝ u x (Pi.single b 1) * fderiv ℝ v x (Pi.single a 1)) = 0 := by
  have := tbt6_lipschitz_limit ![u, v] ![Ku, Kv]
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
    (fun G => G 0 a * G 1 b - G 0 b * G 1 a) (by fun_prop) (by simp)
    (fun ψ hψ hψc => tbt6_null2_smooth (hψ 0) (hψ 1) (hψc 0) a b)
  simpa using this

/-- **`3 × 3` minors are null Lagrangians** (Lipschitz, compact support). -/
theorem tbt6_null3 {u₀ u₁ u₂ : (Fin m → ℝ) → ℝ} {K₀ K₁ K₂ : NNReal} (h₀ : LipschitzWith K₀ u₀)
    (h₁ : LipschitzWith K₁ u₁) (h₂ : LipschitzWith K₂ u₂) (c₀ : HasCompactSupport u₀)
    (c₁ : HasCompactSupport u₁) (c₂ : HasCompactSupport u₂) (a₀ a₁ a₂ : Fin m) :
    ∫ x, (fderiv ℝ u₀ x (Pi.single a₀ 1) * (fderiv ℝ u₁ x (Pi.single a₁ 1) *
        fderiv ℝ u₂ x (Pi.single a₂ 1) - fderiv ℝ u₁ x (Pi.single a₂ 1) *
        fderiv ℝ u₂ x (Pi.single a₁ 1)) -
      fderiv ℝ u₀ x (Pi.single a₁ 1) * (fderiv ℝ u₁ x (Pi.single a₀ 1) *
        fderiv ℝ u₂ x (Pi.single a₂ 1) - fderiv ℝ u₁ x (Pi.single a₂ 1) *
        fderiv ℝ u₂ x (Pi.single a₀ 1)) +
      fderiv ℝ u₀ x (Pi.single a₂ 1) * (fderiv ℝ u₁ x (Pi.single a₀ 1) *
        fderiv ℝ u₂ x (Pi.single a₁ 1) - fderiv ℝ u₁ x (Pi.single a₁ 1) *
        fderiv ℝ u₂ x (Pi.single a₀ 1))) = 0 := by
  have := tbt6_lipschitz_limit ![u₀, u₁, u₂] ![K₀, K₁, K₂]
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
    (fun G => G 0 a₀ * (G 1 a₁ * G 2 a₂ - G 1 a₂ * G 2 a₁) -
      G 0 a₁ * (G 1 a₀ * G 2 a₂ - G 1 a₂ * G 2 a₀) +
      G 0 a₂ * (G 1 a₀ * G 2 a₁ - G 1 a₁ * G 2 a₀)) (by fun_prop) (by simp)
    (fun ψ hψ hψc => tbt6_null3_smooth (hψ 0) (hψ 1) (hψ 2) (hψc 0) a₀ a₁ a₂)
  simpa using this

end Cassese
