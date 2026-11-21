module

public import Morrey.Cassese.TwoByThree.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Corollary 5.3: fields of the form `v = (φ_xx − φ_yy, 2 φ_xy, Δφ)`

For a scalar potential `ψ : ℝ² → ℝ` the map `𝒱ψ = (∂₀₀ψ − ∂₁₁ψ, 2 ∂₀₁ψ, ∂₀₀ψ + ∂₁₁ψ)`
(`tbt3V`, the partial derivatives `∂ⱼ` being `tbt3D1`) has `(∇𝒱ψ)ᵀ ∈ 𝓛₃` whenever `ψ` is smooth
(symmetry of the second derivative, `tbt3_jac_V_transpose`). The partial derivatives are local
(`tbt3_D1_eqOn`) and covariant under scaling (`tbt3_D1_scale`, `tbt3_jac_V_scale`).

Helpers are prefixed `tbt3_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace Cassese

/-- The partial derivative `∂ⱼψ (x)`. -/
noncomputable def tbt3D1 (ψ : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (x : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ ψ x (Pi.single j 1)

/-- `𝒱ψ = (∂₀₀ψ − ∂₁₁ψ, 2 ∂₀₁ψ, ∂₀₀ψ + ∂₁₁ψ)`, i.e. `(φ_xx − φ_yy, 2 φ_xy, Δφ)`. -/
noncomputable def tbt3V (ψ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![tbt3D1 (tbt3D1 ψ 0) 0 x - tbt3D1 (tbt3D1 ψ 1) 1 x, 2 * tbt3D1 (tbt3D1 ψ 1) 0 x,
    tbt3D1 (tbt3D1 ψ 0) 0 x + tbt3D1 (tbt3D1 ψ 1) 1 x]

/-- The matrix `[[a − c, 2b, a + c], [b − e, 2c, b + e]]` of `𝓛₃` built from the third
derivatives `a, b, c, e = φ_xxx, φ_xxy, φ_xyy, φ_yyy`. -/
def tbt3T (a b c e : ℝ) : Matrix (Fin 2) (Fin 3) ℝ := !![a - c, 2 * b, a + c; b - e, 2 * c, b + e]

theorem tbt3_T_mem_L3 (a b c e : ℝ) : tbt3T a b c e ∈ L3 := by
  rw [mem_L3_iff]; simp [tbt3T]; constructor <;> ring

/-- The smoothness class used throughout. -/
abbrev tbt3Top : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem tbt3_contDiff_D1 {ψ : (Fin 2 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ) (j : Fin 2) :
    ContDiff ℝ tbt3Top (tbt3D1 ψ j) :=
  (h.fderiv_right (m := tbt3Top) (by simp)).clm_apply contDiff_const

theorem tbt3_differentiable {ψ : (Fin 2 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ) :
    Differentiable ℝ ψ := h.differentiable (by simp)

/-- `∂ᵢ∂ⱼψ (x) = D²ψ (x) eᵢ eⱼ`. -/
theorem tbt3_D1_D1_eq {ψ : (Fin 2 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ) (i j : Fin 2)
    (x : Fin 2 → ℝ) :
    tbt3D1 (tbt3D1 ψ j) i x = fderiv ℝ (fderiv ℝ ψ) x (Pi.single i 1) (Pi.single j 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    ((h.fderiv_right (m := tbt3Top) (by simp)).differentiable (by simp)) x
  show fderiv ℝ (fun y => fderiv ℝ ψ y (Pi.single j 1)) x (Pi.single i 1) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- Symmetry of the second derivative: `∂ᵢ∂ⱼψ = ∂ⱼ∂ᵢψ`. -/
theorem tbt3_D1_comm {ψ : (Fin 2 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ) (i j : Fin 2) :
    tbt3D1 (tbt3D1 ψ j) i = tbt3D1 (tbt3D1 ψ i) j := by
  funext x
  rw [tbt3_D1_D1_eq h, tbt3_D1_D1_eq h]
  exact (h.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- Locality of the partial derivatives on open sets. -/
theorem tbt3_D1_eqOn {U : Set (Fin 2 → ℝ)} (hU : IsOpen U) {ψ₁ ψ₂ : (Fin 2 → ℝ) → ℝ}
    (h : Set.EqOn ψ₁ ψ₂ U) (j : Fin 2) : Set.EqOn (tbt3D1 ψ₁ j) (tbt3D1 ψ₂ j) U := by
  intro x hx
  simp only [tbt3D1]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]

theorem tbt3_V_eqOn {U : Set (Fin 2 → ℝ)} (hU : IsOpen U) {ψ₁ ψ₂ : (Fin 2 → ℝ) → ℝ}
    (h : Set.EqOn ψ₁ ψ₂ U) : Set.EqOn (tbt3V ψ₁) (tbt3V ψ₂) U := by
  intro x hx
  have h0 := tbt3_D1_eqOn hU (tbt3_D1_eqOn hU h 0) 0 hx
  have h1 := tbt3_D1_eqOn hU (tbt3_D1_eqOn hU h 1) 1 hx
  have h2 := tbt3_D1_eqOn hU (tbt3_D1_eqOn hU h 1) 0 hx
  simp only [tbt3V, h0, h1, h2]

/-- Locality of `jac`. -/
theorem tbt3_jac_eqOn {n : ℕ} {U : Set (Fin 2 → ℝ)} (hU : IsOpen U) {v₁ v₂ : (Fin 2 → ℝ) → Fin n → ℝ}
    (h : Set.EqOn v₁ v₂ U) {x : Fin 2 → ℝ} (hx : x ∈ U) : jac v₁ x = jac v₂ x := by
  ext i k
  simp only [jac, Matrix.of_apply]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx)
    (fun y hy => congrFun (h hy) i))]

/-- `jac (𝒱ψ)` in terms of the third partial derivatives. -/
theorem tbt3_jac_V {ψ : (Fin 2 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ) (x : Fin 2 → ℝ) (k : Fin 2) :
    jac (tbt3V ψ) x 0 k = tbt3D1 (tbt3D1 (tbt3D1 ψ 0) 0) k x -
        tbt3D1 (tbt3D1 (tbt3D1 ψ 1) 1) k x ∧
      jac (tbt3V ψ) x 1 k = 2 * tbt3D1 (tbt3D1 (tbt3D1 ψ 1) 0) k x ∧
      jac (tbt3V ψ) x 2 k = tbt3D1 (tbt3D1 (tbt3D1 ψ 0) 0) k x +
        tbt3D1 (tbt3D1 (tbt3D1 ψ 1) 1) k x := by
  have d : ∀ i j : Fin 2, DifferentiableAt ℝ (tbt3D1 (tbt3D1 ψ j) i) x := fun i j =>
    tbt3_differentiable (tbt3_contDiff_D1 (tbt3_contDiff_D1 h j) i) x
  refine ⟨?_, ?_, ?_⟩
  · show fderiv ℝ (fun y => tbt3D1 (tbt3D1 ψ 0) 0 y - tbt3D1 (tbt3D1 ψ 1) 1 y) x _ = _
    rw [fderiv_fun_sub (d 0 0) (d 1 1)]; rfl
  · show fderiv ℝ (fun y => 2 * tbt3D1 (tbt3D1 ψ 1) 0 y) x _ = _
    rw [fderiv_const_mul (d 0 1)]; rfl
  · show fderiv ℝ (fun y => tbt3D1 (tbt3D1 ψ 0) 0 y + tbt3D1 (tbt3D1 ψ 1) 1 y) x _ = _
    rw [fderiv_fun_add (d 0 0) (d 1 1)]; rfl

/-- `(∇𝒱ψ)ᵀ = T (a, b, c, e)` with `a, b, c, e` the third derivatives `∂₀₀₀ψ, ∂₀₀₁ψ, ∂₀₁₁ψ,
∂₁₁₁ψ`; in particular `(∇𝒱ψ)ᵀ ∈ 𝓛₃`. -/
theorem tbt3_jac_V_transpose {ψ : (Fin 2 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ) (x : Fin 2 → ℝ) :
    (jac (tbt3V ψ) x)ᵀ = tbt3T (tbt3D1 (tbt3D1 (tbt3D1 ψ 0) 0) 0 x)
      (tbt3D1 (tbt3D1 (tbt3D1 ψ 1) 0) 0 x) (tbt3D1 (tbt3D1 (tbt3D1 ψ 1) 1) 0 x)
      (tbt3D1 (tbt3D1 (tbt3D1 ψ 1) 1) 1 x) := by
  -- symmetries of the third derivatives
  have s1 : tbt3D1 (tbt3D1 ψ 0) 1 = tbt3D1 (tbt3D1 ψ 1) 0 := tbt3_D1_comm h 1 0
  have s2 : tbt3D1 (tbt3D1 (tbt3D1 ψ 0) 0) 1 = tbt3D1 (tbt3D1 (tbt3D1 ψ 0) 1) 0 :=
    tbt3_D1_comm (tbt3_contDiff_D1 h 0) 1 0
  have s3 : tbt3D1 (tbt3D1 (tbt3D1 ψ 1) 0) 1 = tbt3D1 (tbt3D1 (tbt3D1 ψ 1) 1) 0 :=
    tbt3_D1_comm (tbt3_contDiff_D1 h 1) 1 0
  obtain ⟨a0, b0, c0⟩ := tbt3_jac_V h x 0
  obtain ⟨a1, b1, c1⟩ := tbt3_jac_V h x 1
  ext k n
  fin_cases k <;> fin_cases n <;>
    simp [Matrix.transpose_apply, tbt3T, a0, b0, c0, a1, b1, c1, s1, s2, s3]

/-- Scaling: `∂ⱼ (c ψ (a ·)) (x) = c a ∂ⱼψ (a x)`. -/
theorem tbt3_D1_scale {ψ : (Fin 2 → ℝ) → ℝ} (hψ : Differentiable ℝ ψ) (c a : ℝ) (j : Fin 2) :
    tbt3D1 (fun z => c * ψ (a • z)) j = fun x => c * a * tbt3D1 ψ j (a • x) := by
  funext x
  have h1 : HasFDerivAt (fun z : Fin 2 → ℝ => a • z) (a • ContinuousLinearMap.id ℝ _) x :=
    (hasFDerivAt_id x).const_smul a
  have h2 := ((hψ (a • x)).hasFDerivAt.comp x h1).const_mul c
  simp only [tbt3D1]
  rw [show (fun z => c * ψ (a • z)) = fun z => c * (ψ ∘ fun z => a • z) z from rfl, h2.fderiv]
  simp [mul_assoc]

theorem tbt3_V_scale {ψ : (Fin 2 → ℝ) → ℝ} (h : ContDiff ℝ tbt3Top ψ) (c a : ℝ) :
    tbt3V (fun z => c * ψ (a • z)) = fun x => (c * a * a) • tbt3V ψ (a • x) := by
  have e : ∀ j i : Fin 2, tbt3D1 (tbt3D1 (fun z => c * ψ (a • z)) j) i =
      fun x => c * a * a * tbt3D1 (tbt3D1 ψ j) i (a • x) := by
    intro j i
    rw [tbt3_D1_scale (tbt3_differentiable h), tbt3_D1_scale
      (tbt3_differentiable (tbt3_contDiff_D1 h j))]
  funext x
  simp only [tbt3V, e]
  ext n; fin_cases n <;> simp [Pi.smul_apply] <;> ring

theorem tbt3_jac_scale {n : ℕ} {V : (Fin 2 → ℝ) → Fin n → ℝ} (hV : Differentiable ℝ V) (K a : ℝ)
    (x : Fin 2 → ℝ) : jac (fun z => K • V (a • z)) x = (K * a) • jac V (a • x) := by
  ext i k
  have hi : Differentiable ℝ fun y => V y i := fun y =>
    (differentiableAt_pi.mp (hV y)) i
  have := congrFun (tbt3_D1_scale hi K a k) x
  simp only [tbt3D1] at this
  simp only [jac, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  exact this

end Cassese
