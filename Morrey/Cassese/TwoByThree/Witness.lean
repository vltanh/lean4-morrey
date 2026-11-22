module

public import Morrey.Cassese.TwoByThree.Basic
public import Morrey.Cassese.TwoByThree.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Section 5.2: the quasiconvexity witness (Proposition 5.2)

The construction of the proof of Proposition 5.2 (TeX lines 1717–1796). Identify `ℝ³` with
`ℂ × ℝ`, `X = (x, y, t) ↦ (w, t)` with `w = x + i y`. With the principal square root
`s = √((1 − i t)² + |w|²)` (`tbtS`, written `exp (log z / 2)`), the root in the unit disc of
`w̄ ζ² + 2 (t + i) ζ + w = 0` is `ζ = i w / (1 − i t + s)` (`tbtZeta`), and the witness is
`u = ζ̄ + ζ² / 2` (`tbtU`, the profile `F (z) = z`, `G (z) = z² / 2`), as a map into `ℝ²`
(`tbtWitness`). The integrals are evaluated, as in the paper, in the coordinates
`(ζ, τ) ∈ 𝔻 × ℝ`, `τ = −Im s`, through the change of variables `(ζ, τ) ↦ (w, t)` (`tbtInv`).

Helpers are prefixed `tbt_`.
-/

@[expose] public section

open MeasureTheory Complex
open scoped Matrix ENNReal ComplexConjugate

namespace Cassese

/-- `w = x + i y`. -/
noncomputable def tbtW (X : Fin 3 → ℝ) : ℂ := (X 0 : ℂ) + (X 1 : ℂ) * I

/-- `z = (1 − i t)² + |w|²`, whose principal square root is `s`. -/
noncomputable def tbtZ (X : Fin 3 → ℝ) : ℂ := (1 - (X 2 : ℂ) * I) ^ 2 + ((X 0 ^ 2 + X 1 ^ 2 : ℝ) : ℂ)

/-- `s = √((1 − i t)² + |w|²)`, the principal square root. -/
noncomputable def tbtS (X : Fin 3 → ℝ) : ℂ := exp (log (tbtZ X) / 2)

/-- The denominator `1 − i t + s`. -/
noncomputable def tbtDen (X : Fin 3 → ℝ) : ℂ := 1 - (X 2 : ℂ) * I + tbtS X

/-- `ζ = i w / (1 − i t + s)`, the root in the unit disc of `w̄ ζ² + 2 (t + i) ζ + w = 0`. -/
noncomputable def tbtZeta (X : Fin 3 → ℝ) : ℂ := I * tbtW X / tbtDen X

/-- `u = ζ̄ + ζ² / 2` (`F (z) = z`, `G (z) = z² / 2`). -/
noncomputable def tbtU (X : Fin 3 → ℝ) : ℂ := conj (tbtZeta X) + tbtZeta X ^ 2 / 2

/-- The witness of Proposition 5.2, `u` as a map into `ℝ²`. -/
noncomputable def tbtWitness (X : Fin 3 → ℝ) : Fin 2 → ℝ := ![(tbtU X).re, (tbtU X).im]

theorem tbt_Z_re (X : Fin 3 → ℝ) : (tbtZ X).re = 1 - X 2 ^ 2 + (X 0 ^ 2 + X 1 ^ 2) := by
  simp [tbtZ, pow_two]

theorem tbt_Z_im (X : Fin 3 → ℝ) : (tbtZ X).im = -2 * X 2 := by
  simp [tbtZ, pow_two]; ring

/-- `z` lies in the slit plane: off the real axis when `t ≠ 0`, and `z = 1 + |w|² > 0` when
`t = 0`. -/
theorem tbt_Z_mem_slitPlane (X : Fin 3 → ℝ) : tbtZ X ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : X 2 = 0
  · left; rw [tbt_Z_re, h]; positivity
  · right; rw [tbt_Z_im]; exact mul_ne_zero (by norm_num) h

theorem tbt_Z_ne_zero (X : Fin 3 → ℝ) : tbtZ X ≠ 0 := slitPlane_ne_zero (tbt_Z_mem_slitPlane X)

/-- `s² = (1 − i t)² + |w|²`. -/
theorem tbt_S_sq (X : Fin 3 → ℝ) : tbtS X ^ 2 = tbtZ X := by
  rw [tbtS, ← exp_nat_mul, show ((2 : ℕ) : ℂ) * (log (tbtZ X) / 2) = log (tbtZ X) by
    push_cast; ring, exp_log (tbt_Z_ne_zero X)]

/-- `Re s > 0`: the principal square root of a point of the slit plane. -/
theorem tbt_S_re_pos (X : Fin 3 → ℝ) : 0 < (tbtS X).re := by
  rw [tbtS, exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have := neg_pi_lt_arg (tbtZ X)
    have h2 : (log (tbtZ X) / 2).im = (tbtZ X).arg / 2 := by
      simp [Complex.div_ofNat_im, log_im]
    rw [h2]; linarith
  · have h1 := arg_le_pi (tbtZ X)
    have h1' := slitPlane_arg_ne_pi (tbt_Z_mem_slitPlane X)
    have h2 : (log (tbtZ X) / 2).im = (tbtZ X).arg / 2 := by
      simp [Complex.div_ofNat_im, log_im]
    rw [h2]; have := lt_of_le_of_ne h1 h1'; linarith

theorem tbt_S_ne_zero (X : Fin 3 → ℝ) : tbtS X ≠ 0 := by
  intro h; have := tbt_S_re_pos X; rw [h, zero_re] at this; exact lt_irrefl _ this

theorem tbt_Den_re (X : Fin 3 → ℝ) : (tbtDen X).re = 1 + (tbtS X).re := by
  simp [tbtDen]

theorem tbt_Den_ne_zero (X : Fin 3 → ℝ) : tbtDen X ≠ 0 := by
  intro h
  have := tbt_Den_re X
  rw [h, zero_re] at this
  linarith [tbt_S_re_pos X]

theorem tbt_conj_W_mul (X : Fin 3 → ℝ) :
    conj (tbtW X) * tbtW X = ((X 0 ^ 2 + X 1 ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [tbtW, pow_two]; ring

/-- The defining equation `w̄ ζ² + 2 (t + i) ζ + w = 0` (`h (ξ) = −2 i ξ`). -/
theorem tbt_Zeta_eq (X : Fin 3 → ℝ) :
    conj (tbtW X) * tbtZeta X ^ 2 + 2 * ((X 2 : ℂ) + I) * tbtZeta X + tbtW X = 0 := by
  have hD := tbt_Den_ne_zero X
  have hS := tbt_S_sq X
  have hw := tbt_conj_W_mul X
  have hZ : tbtZ X = (1 - (X 2 : ℂ) * I) ^ 2 + ((X 0 ^ 2 + X 1 ^ 2 : ℝ) : ℂ) := rfl
  have key : conj (tbtW X) * (I * tbtW X) ^ 2 + 2 * ((X 2 : ℂ) + I) * (I * tbtW X) * tbtDen X +
      tbtW X * tbtDen X ^ 2 = 0 := by
    rw [tbtDen]
    linear_combination (tbtW X) * hS +
      (-2 * I * (X 2 : ℂ) * tbtW X + 2 * tbtS X * tbtW X + tbtW X ^ 2 * conj (tbtW X) +
        2 * tbtW X) * I_sq - tbtW X * hw + tbtW X * hZ
  rw [tbtZeta]
  field_simp
  linear_combination key

/-- `s = −i (t + i + w̄ ζ)`. -/
theorem tbt_S_eq (X : Fin 3 → ℝ) :
    tbtS X + I * ((X 2 : ℂ) + I + conj (tbtW X) * tbtZeta X) = 0 := by
  have hD := tbt_Den_ne_zero X
  have hS := tbt_S_sq X
  have hw := tbt_conj_W_mul X
  have hZ : tbtZ X = (1 - (X 2 : ℂ) * I) ^ 2 + ((X 0 ^ 2 + X 1 ^ 2 : ℝ) : ℂ) := rfl
  rw [tbtZeta]
  field_simp
  rw [tbtDen]
  linear_combination hS + (-I * (X 2 : ℂ) + tbtS X + tbtW X * conj (tbtW X) + 1) * I_sq - hw + hZ

/-- `σ (1 − |ζ|²) = 1 + |ζ|²` for `σ = Re s` (so `σ = (1 + |ζ|²) / (1 − |ζ|²)`). -/
theorem tbt_sigma_eq (X : Fin 3 → ℝ) :
    (tbtS X).re * (1 - ‖tbtZeta X‖ ^ 2) = 1 + ‖tbtZeta X‖ ^ 2 := by
  have h4 := congrArg re (tbt_Zeta_eq X)
  have h4' := congrArg im (tbt_Zeta_eq X)
  have h5 := congrArg re (tbt_S_eq X)
  simp only [tbtW, add_re, add_im, mul_re, mul_im, conj_re, conj_im, ofReal_re, ofReal_im, I_re,
    I_im, pow_two, zero_re, zero_im, re_ofNat, im_ofNat] at h4 h4' h5
  rw [Complex.sq_norm, Complex.normSq_apply]
  linear_combination (1 - (tbtZeta X).re ^ 2 - (tbtZeta X).im ^ 2) * h5 + (tbtZeta X).im * h4 -
    (tbtZeta X).re * h4'

/-- `|ζ| < 1`: `ζ` takes values in the unit disc. -/
theorem tbt_norm_Zeta_lt_one (X : Fin 3 → ℝ) : ‖tbtZeta X‖ < 1 := by
  have h := tbt_sigma_eq X
  have hs := tbt_S_re_pos X
  have h1 : 0 < 1 - ‖tbtZeta X‖ ^ 2 := by
    by_contra hle
    push Not at hle
    nlinarith [sq_nonneg ‖tbtZeta X‖]
  nlinarith [norm_nonneg (tbtZeta X)]

theorem tbt_W_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n tbtW := by
  unfold tbtW
  have h0 : ContDiff ℝ n fun X : Fin 3 → ℝ => (X 0 : ℂ) :=
    ofRealCLM.contDiff.comp (contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) (0 : Fin 3))
  have h1 : ContDiff ℝ n fun X : Fin 3 → ℝ => (X 1 : ℂ) :=
    ofRealCLM.contDiff.comp (contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) (1 : Fin 3))
  exact h0.add (h1.mul contDiff_const)

theorem tbt_Z_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n tbtZ := by
  unfold tbtZ
  have h2 : ContDiff ℝ n fun X : Fin 3 → ℝ => (X 2 : ℂ) :=
    ofRealCLM.contDiff.comp (contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) (2 : Fin 3))
  have hr : ContDiff ℝ n fun X : Fin 3 → ℝ => X 0 ^ 2 + X 1 ^ 2 :=
    ((contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) (0 : Fin 3)).pow 2).add ((contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) (1 : Fin 3)).pow 2)
  exact ((contDiff_const.sub (h2.mul contDiff_const)).pow 2).add (ofRealCLM.contDiff.comp hr)

theorem tbt_S_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n tbtS := by
  rw [contDiff_iff_contDiffAt]
  intro X
  have hlog : ContDiffAt ℝ n (fun X => log (tbtZ X)) X :=
    ((contDiffAt_log (tbt_Z_mem_slitPlane X)).restrict_scalars ℝ).comp X
      tbt_Z_contDiff.contDiffAt
  exact (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp X (hlog.div_const 2)

/-- `ζ` is smooth. The paper argues that `ζ` is the unique, simple root in the unit disc of
`w̄ ζ² + 2 (t + i) ζ + w = 0` and hence smooth (TeX 1745–1752); here smoothness is read off the
closed form `ζ = i w / (1 − i t + s)`, `s` the principal square root of a point of the slit plane
(`tbt_S_contDiff`) and `Re (1 − i t + s) > 0`. This is a mechanical difference: the closed form
is that root (`tbt_Zeta_eq`, `tbt_norm_Zeta_lt_one`). -/
theorem tbt_Zeta_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n tbtZeta := by
  rw [contDiff_iff_contDiffAt]
  intro X
  have h2 : ContDiff ℝ n fun X : Fin 3 → ℝ => (X 2 : ℂ) :=
    ofRealCLM.contDiff.comp (contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) (2 : Fin 3))
  have hD : ContDiff ℝ n tbtDen := (contDiff_const.sub (h2.mul contDiff_const)).add tbt_S_contDiff
  have hinv : ContDiffAt ℝ n (fun X => (tbtDen X)⁻¹) X :=
    hD.contDiffAt.inv (tbt_Den_ne_zero X)
  have : ContDiffAt ℝ n (fun X => I * tbtW X * (tbtDen X)⁻¹) X :=
    (contDiff_const.mul tbt_W_contDiff).contDiffAt.mul hinv
  have he : tbtZeta = fun X => I * tbtW X * (tbtDen X)⁻¹ := by
    funext X; rw [tbtZeta, div_eq_mul_inv]
  rw [he]; exact this

theorem tbt_U_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n tbtU :=
  (conjCLE.contDiff.comp tbt_Zeta_contDiff).add ((tbt_Zeta_contDiff.pow 2).div_const 2)

theorem tbt_witness_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n tbtWitness := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact reCLM.contDiff.comp tbt_U_contDiff
  · exact imCLM.contDiff.comp tbt_U_contDiff

/-- Implicit differentiation of `w̄ ζ² + 2 (t + i) ζ + w = 0` along a line on which `w`, `t` are
affine (`w = W + τ c`, `t = T + τ d`): the derivative `f'` of `ζ` satisfies
`c̄ ζ² + 2 (w̄ ζ + t + i) f' + 2 d ζ + c = 0`. -/
theorem tbt_implicit {f : ℝ → ℂ} {f' : ℂ} (hf : HasDerivAt f f' 0) (W c : ℂ) (T d : ℝ)
    (hG : ∀ τ : ℝ, (conj W + (τ : ℂ) * conj c) * f τ ^ 2 +
      2 * ((T : ℂ) + (τ : ℂ) * d + I) * f τ + (W + (τ : ℂ) * c) = 0) :
    conj c * f 0 ^ 2 + 2 * (conj W * f 0 + T + I) * f' + 2 * d * f 0 + c = 0 := by
  have hτ : HasDerivAt (fun τ : ℝ => (τ : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h1 : HasDerivAt (fun τ : ℝ => conj W + (τ : ℂ) * conj c) (1 * conj c) 0 :=
    (hτ.mul_const (conj c)).const_add (conj W)
  have h2 : HasDerivAt (fun τ => f τ ^ 2) ((2 : ℕ) * f 0 ^ (2 - 1) * f') 0 := hf.fun_pow 2
  have h3 : HasDerivAt (fun τ : ℝ => 2 * ((T : ℂ) + (τ : ℂ) * d + I)) (2 * (1 * d)) 0 :=
    (((hτ.mul_const (d : ℂ)).const_add (T : ℂ)).add_const I).const_mul 2
  have h4 : HasDerivAt (fun τ : ℝ => W + (τ : ℂ) * c) (1 * c) 0 :=
    (hτ.mul_const c).const_add W
  have hG' := ((h1.mul h2).add (h3.mul hf)).add h4
  have hz : (((fun τ : ℝ => conj W + (τ : ℂ) * conj c) * fun τ => f τ ^ 2) +
      (fun τ : ℝ => 2 * ((T : ℂ) + (τ : ℂ) * d + I)) * f + fun τ : ℝ => W + (τ : ℂ) * c) =
      fun _ => 0 := by
    funext τ; simp only [Pi.add_apply, Pi.mul_apply]; exact hG τ
  rw [hz] at hG'
  have := hG'.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  simp only [ofReal_zero, zero_mul, add_zero] at this
  push_cast at this
  linear_combination this

/-- The line `τ ↦ X + τ e_k`. -/
theorem tbt_hasDerivAt_line (X v : Fin 3 → ℝ) :
    HasDerivAt (fun τ : ℝ => X + τ • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add X

/-- The directional derivative of a differentiable map along a line. -/
theorem tbt_hasDerivAt_comp_line {F : (Fin 3 → ℝ) → ℂ} {X : Fin 3 → ℝ}
    (hF : DifferentiableAt ℝ F X) (v : Fin 3 → ℝ) :
    HasDerivAt (fun τ : ℝ => F (X + τ • v)) (fderiv ℝ F X v) 0 :=
  hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (tbt_hasDerivAt_line X v) (by simp)

/-- `ζ_k`, the partial derivatives of `ζ`. -/
noncomputable def tbtZetaD (X : Fin 3 → ℝ) (k : Fin 3) : ℂ :=
  fderiv ℝ tbtZeta X (Pi.single k 1)

/-- `∂ζ = i / (2 s)`. -/
noncomputable def tbtK (X : Fin 3 → ℝ) : ℂ := I / (2 * tbtS X)

/-- The partial derivatives of `ζ` by implicit differentiation: `ζ_x = ∂ζ (1 + ζ²)`,
`ζ_y = i ∂ζ (1 − ζ²)`, `ζ_t = 2 ζ ∂ζ`, with `∂ζ = i / (2 s)`; equivalently `∂̄ζ = ζ² ∂ζ` and
`ζ_t = 2 ζ ∂ζ`. -/
theorem tbt_ZetaD_eq (X : Fin 3 → ℝ) :
    tbtZetaD X 0 = tbtK X * (1 + tbtZeta X ^ 2) ∧
      tbtZetaD X 1 = I * tbtK X * (1 - tbtZeta X ^ 2) ∧
      tbtZetaD X 2 = 2 * tbtZeta X * tbtK X := by
  have hdiff : DifferentiableAt ℝ tbtZeta X :=
    (tbt_Zeta_contDiff (n := 1)).differentiable one_ne_zero X
  -- `w̄ ζ + t + i = i s`
  have hIS : conj (tbtW X) * tbtZeta X + (X 2 : ℂ) + I = I * tbtS X := by
    linear_combination (-I) * tbt_S_eq X + (conj (tbtW X) * tbtZeta X + (X 2 : ℂ) + I) * I_sq
  have hS := tbt_S_ne_zero X
  have key : ∀ k : Fin 3, ∀ c : ℂ, ∀ d : ℝ,
      (∀ τ : ℝ, tbtW (X + τ • Pi.single k 1) = tbtW X + τ * c) →
      (∀ τ : ℝ, (X + τ • Pi.single k 1 : Fin 3 → ℝ) 2 = X 2 + τ * d) →
      conj c * tbtZeta X ^ 2 + 2 * (I * tbtS X) * tbtZetaD X k + 2 * d * tbtZeta X + c = 0 := by
    intro k c d hw ht
    have h := tbt_implicit (tbt_hasDerivAt_comp_line hdiff (Pi.single k 1)) (tbtW X) c (X 2) d
      (fun τ => by
        have := tbt_Zeta_eq (X + τ • Pi.single k 1)
        rw [hw τ, ht τ] at this
        simpa [map_add, map_mul, conj_ofReal] using this)
    simp only [zero_smul, add_zero] at h
    rw [← hIS, tbtZetaD]
    linear_combination h
  refine ⟨?_, ?_, ?_⟩
  · have h := key 0 1 0 (fun τ => by simp [tbtW]; ring) (fun τ => by simp)
    rw [tbtK]; field_simp
    simp only [map_one, ofReal_zero, mul_zero, zero_mul, add_zero] at h
    linear_combination (-I) * h + (tbtZetaD X 0 * 2 * tbtS X) * I_sq
  · have h := key 1 I 0 (fun τ => by simp [tbtW]; ring) (fun τ => by simp)
    rw [tbtK]; field_simp
    simp only [conj_I, ofReal_zero, mul_zero, zero_mul, add_zero] at h
    linear_combination (-I) * h + (tbtZetaD X 1 * 2 * tbtS X) * I_sq
  · have h := key 2 0 1 (fun τ => by simp [tbtW]) (fun τ => by simp)
    rw [tbtK]; field_simp
    simp only [map_zero, zero_mul, zero_add, add_zero, ofReal_one, mul_one] at h
    linear_combination (-I / 2) * h + (tbtZetaD X 2 * tbtS X) * I_sq

/-- The partial derivatives `u_k = ζ̄_k + ζ ζ_k` of `u = ζ̄ + ζ² / 2`. -/
noncomputable def tbtUD (X : Fin 3 → ℝ) (k : Fin 3) : ℂ :=
  conj (tbtZetaD X k) + tbtZeta X * tbtZetaD X k

theorem tbt_fderiv_U (X : Fin 3 → ℝ) (k : Fin 3) :
    fderiv ℝ tbtU X (Pi.single k 1) = tbtUD X k := by
  have hζ : DifferentiableAt ℝ tbtZeta X := (tbt_Zeta_contDiff (n := 1)).differentiable one_ne_zero X
  have hU : DifferentiableAt ℝ tbtU X := (tbt_U_contDiff (n := 1)).differentiable one_ne_zero X
  have h1 := tbt_hasDerivAt_comp_line hU (Pi.single k 1)
  have hf := tbt_hasDerivAt_comp_line hζ (Pi.single k 1)
  have h2 : HasDerivAt (fun τ : ℝ => tbtU (X + τ • Pi.single k 1))
      (star (tbtZetaD X k) + (2 : ℕ) * tbtZeta (X + (0 : ℝ) • Pi.single k 1) ^ (2 - 1) *
        tbtZetaD X k / 2) 0 :=
    (HasDerivAt.star hf).add ((hf.fun_pow 2).div_const 2)
  rw [h1.unique h2, tbtUD]
  simp only [zero_smul, add_zero, Complex.star_def]
  push_cast
  ring

theorem tbt_jac_zero (X : Fin 3 → ℝ) (k : Fin 3) : jac tbtWitness X 0 k = (tbtUD X k).re := by
  have hU : DifferentiableAt ℝ tbtU X := (tbt_U_contDiff (n := 1)).differentiable one_ne_zero X
  have h : HasFDerivAt (fun y => (tbtU y).re) (reCLM.comp (fderiv ℝ tbtU X)) X :=
    reCLM.hasFDerivAt.comp X hU.hasFDerivAt
  show fderiv ℝ (fun y => (tbtU y).re) X (Pi.single k 1) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, tbt_fderiv_U, reCLM_apply]

theorem tbt_jac_one (X : Fin 3 → ℝ) (k : Fin 3) : jac tbtWitness X 1 k = (tbtUD X k).im := by
  have hU : DifferentiableAt ℝ tbtU X := (tbt_U_contDiff (n := 1)).differentiable one_ne_zero X
  have h : HasFDerivAt (fun y => (tbtU y).im) (imCLM.comp (fderiv ℝ tbtU X)) X :=
    imCLM.hasFDerivAt.comp X hU.hasFDerivAt
  show fderiv ℝ (fun y => (tbtU y).im) X (Pi.single k 1) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply, tbt_fderiv_U, imCLM_apply]

/-- The entries of `∇u` as polynomials in `ζ = a + i b` and `∂ζ = c + i e`. -/
theorem tbt_jac_eq (X : Fin 3 → ℝ) :
    let a := (tbtZeta X).re
    let b := (tbtZeta X).im
    let c := (tbtK X).re
    let e := (tbtK X).im
    jac tbtWitness X = !![a ^ 3 * c - 3 * a ^ 2 * b * e + a ^ 2 * c - 3 * a * b ^ 2 * c -
        2 * a * b * e + a * c + b ^ 3 * e - b ^ 2 * c - b * e + c,
      a ^ 3 * e + 3 * a ^ 2 * b * c + a ^ 2 * e - 3 * a * b ^ 2 * e + 2 * a * b * c - a * e -
        b ^ 3 * c - b ^ 2 * e - b * c - e,
      2 * a ^ 2 * c - 4 * a * b * e + 2 * a * c - 2 * b ^ 2 * c - 2 * b * e;
      a ^ 3 * e + 3 * a ^ 2 * b * c - a ^ 2 * e - 3 * a * b ^ 2 * e - 2 * a * b * c + a * e -
        b ^ 3 * c + b ^ 2 * e + b * c - e,
      -a ^ 3 * c + 3 * a ^ 2 * b * e + a ^ 2 * c + 3 * a * b ^ 2 * c - 2 * a * b * e + a * c -
        b ^ 3 * e - b ^ 2 * c - b * e - c,
      2 * a ^ 2 * e + 4 * a * b * c - 2 * a * e - 2 * b ^ 2 * e - 2 * b * c] := by
  intro a b c e
  obtain ⟨h0, h1, h2⟩ := tbt_ZetaD_eq X
  ext i k
  fin_cases i <;> fin_cases k <;>
  simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, tbt_jac_zero, tbt_jac_one, tbtUD, h0, h1,
    h2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, add_re, add_im, mul_re, mul_im, sub_re, sub_im, conj_re, conj_im, one_re,
    one_im, I_re, I_im, pow_two, re_ofNat, im_ofNat] <;>
  ring

/-- `∇u ∈ 𝓛₃`: the constraint `u_t = 2 \overline{∂u}`. -/
theorem tbt_jac_mem_L3 (X : Fin 3 → ℝ) : jac tbtWitness X ∈ L3 := by
  rw [mem_L3_iff, tbt_jac_eq]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons]
  constructor <;> ring

/-- `q₃ (∇u) = −|∂ζ|⁴ (1 − |ζ|²)⁶`, by (24). -/
theorem tbt_q3_jac (X : Fin 3 → ℝ) :
    q3 (jac tbtWitness X) = -(‖tbtK X‖ ^ 2) ^ 2 * (1 - ‖tbtZeta X‖ ^ 2) ^ 6 := by
  rw [equation24 _ (tbt_jac_mem_L3 X), tbt_jac_eq]
  simp only [Complex.sq_norm, Complex.normSq_apply, Matrix.det_fin_two, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons]
  norm_num
  ring

theorem tbt_norm_K (X : Fin 3 → ℝ) : ‖tbtK X‖ ^ 2 = 1 / (4 * ‖tbtS X‖ ^ 2) := by
  have hS : ‖tbtS X‖ ≠ 0 := norm_ne_zero_iff.mpr (tbt_S_ne_zero X)
  rw [tbtK, norm_div, norm_I, norm_mul, Complex.norm_two]
  field_simp
  norm_num

/-- `q₃ (∇u) < 0` everywhere. -/
theorem tbt_q3_jac_neg (X : Fin 3 → ℝ) : q3 (jac tbtWitness X) < 0 := by
  rw [tbt_q3_jac]
  have hK : 0 < ‖tbtK X‖ ^ 2 := by
    rw [tbt_norm_K]
    have := norm_pos_iff.mpr (tbt_S_ne_zero X)
    positivity
  have hz : 0 < 1 - ‖tbtZeta X‖ ^ 2 := by
    have := tbt_norm_Zeta_lt_one X
    nlinarith [norm_nonneg (tbtZeta X)]
  have : 0 < (‖tbtK X‖ ^ 2) ^ 2 * (1 - ‖tbtZeta X‖ ^ 2) ^ 6 := by positivity
  linarith

/-- The real and imaginary parts `σ`, `τ` of `s`: `σ² − τ² = 1 − t² + |w|²`, `σ τ = −t`. -/
theorem tbt_S_parts (X : Fin 3 → ℝ) :
    (tbtS X).re ^ 2 - (tbtS X).im ^ 2 = 1 - X 2 ^ 2 + (X 0 ^ 2 + X 1 ^ 2) ∧
      (tbtS X).re * (tbtS X).im = -X 2 := by
  have h := tbt_S_sq X
  have h1 := congrArg re h
  have h2 := congrArg im h
  rw [tbt_Z_re] at h1
  rw [tbt_Z_im] at h2
  simp only [pow_two, mul_re, mul_im] at h1 h2
  constructor <;> nlinarith

/-- `σ ≥ 1`: `(σ² − 1) (σ² + t²) = |w|² σ²`. -/
theorem tbt_one_le_sigma_sq (X : Fin 3 → ℝ) : 1 ≤ (tbtS X).re ^ 2 := by
  obtain ⟨h1, h2⟩ := tbt_S_parts X
  have hσ := tbt_S_re_pos X
  have key : ((tbtS X).re ^ 2 - 1) * ((tbtS X).re ^ 2 + X 2 ^ 2) =
      (X 0 ^ 2 + X 1 ^ 2) * (tbtS X).re ^ 2 := by
    have h3 : (tbtS X).re ^ 2 * (tbtS X).im ^ 2 = X 2 ^ 2 := by
      rw [← mul_pow, h2]; ring
    linear_combination (tbtS X).re ^ 2 * h1 + h3
  by_contra hlt
  push Not at hlt
  have : ((tbtS X).re ^ 2 - 1) * ((tbtS X).re ^ 2 + X 2 ^ 2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by positivity)
  nlinarith [sq_nonneg (X 0), sq_nonneg (X 1), sq_nonneg (tbtS X).re]

theorem tbt_frobSq_jac (X : Fin 3 → ℝ) :
    frobSq (jac tbtWitness X) = ∑ k, ‖tbtUD X k‖ ^ 2 := by
  simp only [frobSq, Fin.sum_univ_two, Fin.sum_univ_three, tbt_jac_zero, tbt_jac_one,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem tbt_norm_UD_le (X : Fin 3 → ℝ) (k : Fin 3) : ‖tbtUD X k‖ ≤ 4 * ‖tbtK X‖ := by
  obtain ⟨h0, h1, h2⟩ := tbt_ZetaD_eq X
  have hz := (tbt_norm_Zeta_lt_one X).le
  have hz0 := norm_nonneg (tbtZeta X)
  have hK := norm_nonneg (tbtK X)
  have hD : ‖tbtZetaD X k‖ ≤ 2 * ‖tbtK X‖ := by
    fin_cases k
    · show ‖tbtZetaD X 0‖ ≤ _
      rw [h0, norm_mul]
      have : ‖1 + tbtZeta X ^ 2‖ ≤ 2 := by
        calc ‖1 + tbtZeta X ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖tbtZeta X ^ 2‖ := norm_add_le _ _
          _ ≤ 2 := by rw [norm_one, norm_pow]; nlinarith
      nlinarith
    · show ‖tbtZetaD X 1‖ ≤ _
      rw [h1, norm_mul, norm_mul, norm_I, one_mul]
      have : ‖1 - tbtZeta X ^ 2‖ ≤ 2 := by
        calc ‖1 - tbtZeta X ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖tbtZeta X ^ 2‖ := norm_sub_le _ _
          _ ≤ 2 := by rw [norm_one, norm_pow]; nlinarith
      nlinarith
    · show ‖tbtZetaD X 2‖ ≤ _
      rw [h2, norm_mul, norm_mul, Complex.norm_two]
      nlinarith
  calc ‖tbtUD X k‖ ≤ ‖conj (tbtZetaD X k)‖ + ‖tbtZeta X * tbtZetaD X k‖ := norm_add_le _ _
    _ = ‖tbtZetaD X k‖ + ‖tbtZeta X‖ * ‖tbtZetaD X k‖ := by rw [Complex.norm_conj, norm_mul]
    _ ≤ 4 * ‖tbtK X‖ := by nlinarith [norm_nonneg (tbtZetaD X k)]

/-- `|∇u| ≲ |∂ζ| = 1 / (2 |s|)`, in the form `|∇u|⁴ ≤ 144 / |s|⁴` (TeX 1785: "`|∇u| ≲ M |s|⁻¹`",
`M = ‖F'‖_∞ = 1`). -/
theorem tbt_frobSq_sq_le_inv_S4 (X : Fin 3 → ℝ) :
    frobSq (jac tbtWitness X) ^ 2 ≤ 144 / ‖tbtS X‖ ^ 4 := by
  have hF : frobSq (jac tbtWitness X) ≤ 48 * ‖tbtK X‖ ^ 2 := by
    rw [tbt_frobSq_jac, Fin.sum_univ_three]
    have := fun k => pow_le_pow_left₀ (norm_nonneg _) (tbt_norm_UD_le X k) 2
    nlinarith [this 0, this 1, this 2]
  have hF0 : 0 ≤ frobSq (jac tbtWitness X) := tbt_frobSq_nonneg _
  have hSpos : 0 < ‖tbtS X‖ := norm_pos_iff.mpr (tbt_S_ne_zero X)
  calc frobSq (jac tbtWitness X) ^ 2 ≤ (48 * ‖tbtK X‖ ^ 2) ^ 2 := pow_le_pow_left₀ hF0 hF 2
    _ = 144 / ‖tbtS X‖ ^ 4 := by rw [tbt_norm_K]; field_simp; ring

theorem tbt_lintegral_fin_three_le (F : (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ X, F X ≤ ∫⁻ x, ∫⁻ y, ∫⁻ z, F ![x, y, z] := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have he : MeasurePreserving e.symm volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  rw [← he.lintegral_comp_emb e.symm.measurableEmbedding F]
  refine (lintegral_prod_le _).trans (lintegral_mono fun x => ?_)
  set f := MeasurableEquiv.finTwoArrow (α := ℝ)
  have hf : MeasurePreserving f.symm volume volume := (volume_preserving_finTwoArrow ℝ).symm
  rw [← hf.lintegral_comp_emb f.symm.measurableEmbedding]
  refine (lintegral_prod_le _).trans (le_of_eq (lintegral_congr fun y => lintegral_congr fun z => ?_))
  congr 1
  funext i
  fin_cases i <;> rfl



/-- `∫ (a² + y²)⁻¹ dy = π / a` for `a > 0`. -/
theorem tbt_integral_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    ∫ y : ℝ, 1 / (a ^ 2 + y ^ 2) = Real.pi / a := by
  have h : (fun y : ℝ => 1 / (a ^ 2 + y ^ 2)) = fun y => a⁻¹ ^ 2 * (1 + (a⁻¹ * y) ^ 2)⁻¹ := by
    funext y; field_simp
  rw [h, integral_const_mul, Measure.integral_comp_inv_mul_left (fun y => (1 + y ^ 2)⁻¹) a,
    integral_univ_inv_one_add_sq, abs_of_pos ha, smul_eq_mul]
  field_simp

theorem tbt_lintegral_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    ∫⁻ y : ℝ, ENNReal.ofReal (1 / (a ^ 2 + y ^ 2)) = ENNReal.ofReal (Real.pi / a) := by
  have hi : Integrable fun y : ℝ => 1 / (a ^ 2 + y ^ 2) := by
    have h : (fun y : ℝ => 1 / (a ^ 2 + y ^ 2)) = fun y => a⁻¹ ^ 2 * (1 + (a⁻¹ * y) ^ 2)⁻¹ := by
      funext y; field_simp
    rw [h]
    exact (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero ha.ne')).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun z => by positivity),
    tbt_integral_inv_sq_add_sq ha]

theorem tbt_continuous_jac {φ : (Fin 3 → ℝ) → Fin 2 → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : Continuous fun x => jac φ x := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have hi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => φ y i := (contDiff_pi.1 hφ) i
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

/-! ### The coordinates `(ζ, τ)` and the integrals

The paper evaluates the integrals in the coordinates `(ζ, τ) ∈ 𝔻 × ℝ`, `τ = −Im s`
(TeX 1768–1790). Here `p : Fin 3 → ℝ` stands for `(ζ, τ)` with `ζ = p 0 + i p 1`, `τ = p 2`. The
inverse coordinates `w = −2 ζ (τ + i) / (1 − |ζ|²)`, `t = σ τ` (`tbtInv`) map `𝔻 × ℝ` bijectively
onto `ℝ³` (`tbt_Inv_image`, `tbt_Inv_injOn`, with the left inverse `X ↦ (ζ (X), −Im s (X))`,
`tbtCoord`), with Jacobian `4 |s|² / (1 − |ζ|²)²` (`tbt_Inv_det`), and Mathlib's change of variables
formula (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) gives
`dx dy dt = 4 |s|² (1 − |ζ|²)⁻² dA (ζ) dτ` (`tbt_lintegral_eq_coord`).
-/

/-- The domain `𝔻 × ℝ` of the coordinates `(ζ, τ)`, with `ζ = p 0 + i p 1` and `τ = p 2`. -/
def tbtDom : Set (Fin 3 → ℝ) := {p | p 0 ^ 2 + p 1 ^ 2 < 1}

/-- `1 − |ζ|²` in the coordinates `(ζ, τ)`. -/
noncomputable def tbtRho (p : Fin 3 → ℝ) : ℝ := 1 - (p 0 ^ 2 + p 1 ^ 2)

/-- `σ = (1 + |ζ|²) / (1 − |ζ|²)` in the coordinates `(ζ, τ)`. -/
noncomputable def tbtSig (p : Fin 3 → ℝ) : ℝ := (1 + (p 0 ^ 2 + p 1 ^ 2)) / tbtRho p

/-- The inverse coordinates `w = −2 ζ (τ + i) / (1 − |ζ|²)`, `t = σ τ`, as a map `ℝ³ → ℝ³`. -/
noncomputable def tbtInv (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-2 * (p 0 * p 2 - p 1) / tbtRho p, -2 * (p 0 + p 1 * p 2) / tbtRho p, tbtSig p * p 2]

/-- The coordinates `(ζ, τ)` of `X`: `ζ` and `τ = −Im s`. -/
noncomputable def tbtCoord (X : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(tbtZeta X).re, (tbtZeta X).im, -(tbtS X).im]

theorem tbt_Dom_measurableSet : MeasurableSet tbtDom :=
  measurableSet_lt (by fun_prop) measurable_const

theorem tbt_Rho_pos {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) : 0 < tbtRho p := by
  have : p 0 ^ 2 + p 1 ^ 2 < 1 := hp
  unfold tbtRho; linarith

/-- `(1 + σ) (1 − |ζ|²) = 2`. -/
theorem tbt_one_add_Sig_mul_Rho {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) :
    (1 + tbtSig p) * tbtRho p = 2 := by
  have h := (tbt_Rho_pos hp).ne'
  unfold tbtSig; field_simp; unfold tbtRho; ring

theorem tbt_Sig_pos {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) : 0 < tbtSig p := by
  have := tbt_Rho_pos hp
  unfold tbtSig; positivity

theorem tbt_normSq_Zeta (X : Fin 3 → ℝ) :
    ‖tbtZeta X‖ ^ 2 = (tbtZeta X).re ^ 2 + (tbtZeta X).im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- `(ζ, τ) ∈ 𝔻 × ℝ`. -/
theorem tbt_Coord_mem (X : Fin 3 → ℝ) : tbtCoord X ∈ tbtDom := by
  show (tbtCoord X) 0 ^ 2 + (tbtCoord X) 1 ^ 2 < 1
  have h := tbt_norm_Zeta_lt_one X
  have h' : ‖tbtZeta X‖ ^ 2 < 1 := by nlinarith [norm_nonneg (tbtZeta X)]
  simpa [tbtCoord, tbt_normSq_Zeta] using h'

/-- `(w, t)` is recovered from its coordinates `(ζ, τ)` by `w = −2 ζ (τ + i) / (1 − |ζ|²)` and
`t = σ τ` (TeX 1771–1774). -/
theorem tbt_Inv_Coord (X : Fin 3 → ℝ) : tbtInv (tbtCoord X) = X := by
  set ζ := tbtZeta X
  set σ := (tbtS X).re
  set c := -(tbtS X).im
  have hmem := tbt_Coord_mem X
  have hρ : tbtRho (tbtCoord X) = 1 - ‖ζ‖ ^ 2 := by
    simp [tbtRho, tbtCoord, tbt_normSq_Zeta, ζ]
  have hρ0 := tbt_Rho_pos hmem
  have hsig := tbt_sigma_eq X
  have hSig : tbtSig (tbtCoord X) = σ := by
    rw [tbtSig, hρ]
    have h0 : (0 : ℝ) < 1 - ‖ζ‖ ^ 2 := by rw [← hρ]; exact hρ0
    rw [div_eq_iff h0.ne']
    have : 1 + ((tbtCoord X) 0 ^ 2 + (tbtCoord X) 1 ^ 2) = 1 + ‖ζ‖ ^ 2 := by
      simp [tbtCoord, tbt_normSq_Zeta, ζ]
    rw [this]; linarith
  obtain ⟨-, hst⟩ := tbt_S_parts X
  -- `t = σ c`
  have ht : X 2 = σ * c := by simp only [σ, c]; linarith
  -- `(1 + σ) ρ = 2`
  have hσρ : (1 + σ) * (1 - ‖ζ‖ ^ 2) = 2 := by linarith
  -- `w ρ = −2 ζ (c + i)`
  have hw : tbtW X * ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) = -2 * ζ * ((c : ℂ) + I) := by
    have hD := tbt_Den_ne_zero X
    have hζ : ζ * tbtDen X = I * tbtW X := by
      simp only [ζ, tbtZeta]; field_simp
    have hs : tbtS X = (σ : ℂ) - (c : ℂ) * I := by
      apply Complex.ext <;> simp [σ, c]
    have hden : tbtDen X = (1 + (σ : ℂ)) * (1 - (c : ℂ) * I) := by
      rw [tbtDen, hs, ht]; push_cast; ring
    have hσρ' : (1 + (σ : ℂ)) * ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) = 2 := by exact_mod_cast hσρ
    rw [hden] at hζ
    linear_combination (I * ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ)) * hζ + (-I * ζ * (1 - (c : ℂ) * I)) * hσρ' +
      (tbtW X * ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) + 2 * ζ * c) * I_sq
  have hre := congrArg Complex.re hw
  have him := congrArg Complex.im hw
  simp only [tbtW, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, neg_re,
    neg_im, re_ofNat, im_ofNat] at hre him
  have h0 : (0 : ℝ) < 1 - ‖ζ‖ ^ 2 := by rw [← hρ]; exact hρ0
  ext i
  fin_cases i
  · simp only [tbtInv, Fin.zero_eta, Matrix.cons_val_zero, hρ]
    rw [div_eq_iff h0.ne']
    simp only [tbtCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination -hre
  · simp only [tbtInv, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hρ]
    rw [div_eq_iff h0.ne']
    simp only [tbtCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination -him
  · simp only [tbtInv, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      hSig]
    simp only [tbtCoord, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [ht]

/-- A square root with positive real part is the principal one. -/
theorem tbt_S_eq_of_sq {X : Fin 3 → ℝ} {r : ℂ} (hr : r ^ 2 = tbtZ X) (hre : 0 < r.re) :
    tbtS X = r := by
  have h : (tbtS X - r) * (tbtS X + r) = 0 := by
    linear_combination tbt_S_sq X - hr
  rcases mul_eq_zero.mp h with h | h
  · linear_combination h
  · have := congrArg Complex.re h
    rw [add_re, zero_re] at this
    linarith [tbt_S_re_pos X]

/-- At `X = (w, t)` given by the inverse coordinates, `s = σ − i τ`. -/
theorem tbt_S_Inv {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) :
    tbtS (tbtInv p) = (tbtSig p : ℂ) - (p 2 : ℂ) * I := by
  have hρ := (tbt_Rho_pos hp).ne'
  apply tbt_S_eq_of_sq
  · apply Complex.ext
    · rw [tbt_Z_re]
      simp only [tbtInv, tbtSig, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, pow_two, mul_re, sub_re, sub_im, ofReal_re, ofReal_im,
        mul_im, I_re, I_im]
      field_simp
      unfold tbtRho
      ring
    · rw [tbt_Z_im]
      simp only [tbtInv, tbtSig, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, pow_two, mul_re, sub_re, sub_im, ofReal_re, ofReal_im,
        mul_im, I_re, I_im]
      ring
  · simpa using tbt_Sig_pos hp

/-- At `X = (w, t)` given by the inverse coordinates, `ζ (X) = ζ`. -/
theorem tbt_Zeta_Inv {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) :
    tbtZeta (tbtInv p) = (p 0 : ℂ) + (p 1 : ℂ) * I := by
  have hρ := (tbt_Rho_pos hp).ne'
  have h2 := tbt_one_add_Sig_mul_Rho hp
  rw [tbtZeta, div_eq_iff (tbt_Den_ne_zero _), tbtDen, tbt_S_Inv hp]
  apply Complex.ext
  · simp only [tbtW, tbtInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_re, mul_im, add_re, add_im, sub_re, sub_im,
      ofReal_re, ofReal_im, I_re, I_im, one_re, one_im]
    field_simp
    linear_combination (-(p 0) - p 1 * p 2) * h2
  · simp only [tbtW, tbtInv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_re, mul_im, add_re, add_im, sub_re, sub_im,
      ofReal_re, ofReal_im, I_re, I_im, one_re, one_im]
    field_simp
    linear_combination (p 0 * p 2 - p 1) * h2

/-- The coordinates `(ζ, τ)` invert the inverse coordinates on `𝔻 × ℝ`. -/
theorem tbt_Coord_Inv {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) : tbtCoord (tbtInv p) = p := by
  ext i
  fin_cases i
  · simp [tbtCoord, tbt_Zeta_Inv hp]
  · simp [tbtCoord, tbt_Zeta_Inv hp]
  · simp [tbtCoord, tbt_S_Inv hp]

theorem tbt_Inv_injOn : Set.InjOn tbtInv tbtDom := fun p hp q hq h => by
  rw [← tbt_Coord_Inv hp, ← tbt_Coord_Inv hq, h]

theorem tbt_Inv_image : tbtInv '' tbtDom = Set.univ :=
  Set.eq_univ_of_forall fun X => ⟨tbtCoord X, tbt_Coord_mem X, tbt_Inv_Coord X⟩

theorem tbt_Rho_differentiable : Differentiable ℝ tbtRho := by
  unfold tbtRho; fun_prop

theorem tbt_Inv_differentiableAt {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) :
    DifferentiableAt ℝ tbtInv p := by
  have hρ : 1 - (p 0 ^ 2 + p 1 ^ 2) ≠ 0 := (tbt_Rho_pos hp).ne'
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    simp only [tbtInv, tbtSig, tbtRho, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] <;>
    fun_prop (disch := exact hρ)

/-- The directional derivatives of the inverse coordinates. -/
theorem tbt_Inv_fderiv {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) (v : Fin 3 → ℝ) :
    fderiv ℝ tbtInv p v = ![
      -2 * ((v 0 * p 2 + p 0 * v 2 - v 1) * tbtRho p +
        (p 0 * p 2 - p 1) * (2 * (p 0 * v 0 + p 1 * v 1))) / tbtRho p ^ 2,
      -2 * ((v 0 + v 1 * p 2 + p 1 * v 2) * tbtRho p +
        (p 0 + p 1 * p 2) * (2 * (p 0 * v 0 + p 1 * v 1))) / tbtRho p ^ 2,
      4 * (p 0 * v 0 + p 1 * v 1) / tbtRho p ^ 2 * p 2 + tbtSig p * v 2] := by
  have hρ := (tbt_Rho_pos hp).ne'
  have hline : HasDerivAt (fun τ : ℝ => tbtInv (p + τ • v)) (fderiv ℝ tbtInv p v) 0 :=
    (tbt_Inv_differentiableAt hp).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (tbt_hasDerivAt_line p v) (by simp)
  have hq : ∀ k, HasDerivAt (fun τ : ℝ => (p + τ • v) k) (v k) 0 := fun k => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v k)).const_add (p k)
  have hR : HasDerivAt (fun τ : ℝ => tbtRho (p + τ • v)) (-(2 * (p 0 * v 0 + p 1 * v 1))) 0 := by
    refine ((((hq 0).fun_pow 2).add ((hq 1).fun_pow 2)).const_sub 1).congr_deriv ?_
    simp; ring
  have hR0 : tbtRho (p + (0 : ℝ) • v) ≠ 0 := by simpa using hρ
  ext i
  fin_cases i
  · have h := ((((hq 0).mul (hq 2)).sub (hq 1)).const_mul (-2)).div hR hR0
    have h' := (hasDerivAt_pi.1 hline) 0
    simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [h'.unique h]
    simp only [zero_smul, add_zero, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    field_simp
    ring
  · have h := (((hq 0).add ((hq 1).mul (hq 2))).const_mul (-2)).div hR hR0
    have h' := (hasDerivAt_pi.1 hline) 1
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [h'.unique h]
    simp only [zero_smul, add_zero, Pi.mul_apply, Pi.add_apply, Pi.zero_apply]
    field_simp
    ring
  · have h := (((((hq 0).fun_pow 2).add ((hq 1).fun_pow 2)).const_add 1).div hR hR0).mul (hq 2)
    have h' := (hasDerivAt_pi.1 hline) 2
    simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [h'.unique h]
    simp only [zero_smul, add_zero, Pi.add_apply, Pi.zero_apply, Pi.div_apply, tbtSig,
      Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
    unfold tbtRho
    ring

/-- The volume element: `det D (w, t) / D (ζ, τ) = 4 |s|² / (1 − |ζ|²)²`, `|s|² = σ² + τ²`. -/
theorem tbt_Inv_det {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) :
    (fderiv ℝ tbtInv p).det = 4 * (tbtSig p ^ 2 + p 2 ^ 2) / tbtRho p ^ 2 := by
  have hρ := (tbt_Rho_pos hp).ne'
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', Matrix.det_fin_three]
  simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, tbt_Inv_fderiv hp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Pi.single_apply]
  norm_num
  simp only [tbtSig]
  field_simp
  unfold tbtRho
  ring

/-- The change of variables `(ζ, τ) ↦ (w, t)` (TeX 1768–1777):
`dx dy dt = 4 |s|² (1 − |ζ|²)⁻² dA (ζ) dτ` on `𝔻 × ℝ`. -/
theorem tbt_lintegral_eq_coord (g : (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ X, g X = ∫⁻ p in tbtDom,
      ENNReal.ofReal (4 * (tbtSig p ^ 2 + p 2 ^ 2) / tbtRho p ^ 2) * g (tbtInv p) := by
  rw [← setLIntegral_univ, ← tbt_Inv_image,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume tbt_Dom_measurableSet
      (fun p hp => (tbt_Inv_differentiableAt hp).hasFDerivAt.hasFDerivWithinAt) tbt_Inv_injOn g]
  refine setLIntegral_congr_fun tbt_Dom_measurableSet (fun p hp => ?_)
  have := tbt_Rho_pos hp
  rw [tbt_Inv_det hp, abs_of_nonneg (by positivity)]

/-- `|s|² = σ² + τ²` in the coordinates. -/
theorem tbt_normSq_S_Inv {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) :
    ‖tbtS (tbtInv p)‖ ^ 2 = tbtSig p ^ 2 + p 2 ^ 2 := by
  rw [tbt_S_Inv hp, Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- `Re s = σ` in the coordinates. -/
theorem tbt_re_S_Inv {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) : (tbtS (tbtInv p)).re = tbtSig p := by
  rw [tbt_S_Inv hp]; simp

theorem tbt_Rho_Inv {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) :
    1 - ‖tbtZeta (tbtInv p)‖ ^ 2 = tbtRho p := by
  rw [tbt_Zeta_Inv hp, Complex.sq_norm, Complex.normSq_apply]; simp [tbtRho]; ring

/-- `|q₃ (∇u)| = |∂ζ|⁴ (1 − |ζ|²)⁶ = (1 − |ζ|²)⁶ / (16 |s|⁴)` in the coordinates. -/
theorem tbt_abs_q3_Inv {p : Fin 3 → ℝ} (hp : p ∈ tbtDom) :
    |q3 (jac tbtWitness (tbtInv p))| =
      tbtRho p ^ 6 / (16 * (tbtSig p ^ 2 + p 2 ^ 2) ^ 2) := by
  have h0 : 0 < tbtSig p ^ 2 + p 2 ^ 2 := by have := tbt_Sig_pos hp; positivity
  rw [tbt_q3_jac, tbt_norm_K, tbt_normSq_S_Inv hp, tbt_Rho_Inv hp,
    neg_mul, abs_neg, abs_of_nonneg (by positivity)]
  field_simp
  ring

theorem tbt_lintegral_fin_three_eq {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ X, F X = ∫⁻ x, ∫⁻ y, ∫⁻ z, F ![x, y, z] := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have he : MeasurePreserving e.symm volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  rw [← he.lintegral_comp_emb e.symm.measurableEmbedding F]
  rw [Measure.volume_eq_prod, lintegral_prod (fun z => F (e.symm z))
    (hF.comp e.symm.measurable).aemeasurable]
  refine lintegral_congr fun x => ?_
  set f := MeasurableEquiv.finTwoArrow (α := ℝ)
  have hf : MeasurePreserving f.symm volume volume := (volume_preserving_finTwoArrow ℝ).symm
  rw [← hf.lintegral_comp_emb f.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (fun z => F (e.symm (x, f.symm z))) ((hF.comp e.symm.measurable).comp
      (measurable_const.prodMk f.symm.measurable)).aemeasurable]
  refine lintegral_congr fun y => lintegral_congr fun z => ?_
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `∫ A / (σ² + τ²) dτ = π A / σ`. -/
theorem tbt_lintegral_tau {A σ : ℝ} (hA : 0 ≤ A) (hσ : 0 < σ) :
    ∫⁻ c : ℝ, ENNReal.ofReal (A / (σ ^ 2 + c ^ 2)) = ENNReal.ofReal (A * Real.pi / σ) := by
  have h : ∀ c : ℝ, ENNReal.ofReal (A / (σ ^ 2 + c ^ 2)) =
      ENNReal.ofReal A * ENNReal.ofReal (1 / (σ ^ 2 + c ^ 2)) := fun c => by
    rw [← ENNReal.ofReal_mul hA, mul_one_div]
  simp_rw [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, tbt_lintegral_inv_sq_add_sq hσ,
    ← ENNReal.ofReal_mul hA, mul_div_assoc]

/-- "Integrating gives `∫_{ℝ³} q₃ (∇u) = −(π/4) ∫_𝔻 (1 − |ζ|²)⁵ / (1 + |ζ|²) dA (ζ)`" (TeX
1779–1783, `F' = 1`), for `|q₃ (∇u)| = −q₃ (∇u)`: in the coordinates `(ζ, τ)` the integrand is
`(1 − |ζ|²)⁶ / (16 |s|⁴) · 4 |s|² / (1 − |ζ|²)² = (1 − |ζ|²)⁴ / (4 (σ² + τ²))`, and
`∫ dτ / (σ² + τ²) = π / σ`. -/
theorem tbt_lintegral_abs_q3 :
    ∫⁻ X, ENNReal.ofReal |q3 (jac tbtWitness X)| =
      ∫⁻ q : ℝ × ℝ, if q.1 ^ 2 + q.2 ^ 2 < 1 then
        ENNReal.ofReal (Real.pi / 4 * (1 - (q.1 ^ 2 + q.2 ^ 2)) ^ 5 / (1 + (q.1 ^ 2 + q.2 ^ 2)))
      else 0 := by
  set G : (Fin 3 → ℝ) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (tbtRho p ^ 4 / 4 / (tbtSig p ^ 2 + p 2 ^ 2)) with hGdef
  have hG : Measurable G := by simp only [G, tbtRho, tbtSig]; fun_prop
  have hif : Measurable fun q : ℝ × ℝ => if q.1 ^ 2 + q.2 ^ 2 < 1 then
      ENNReal.ofReal (Real.pi / 4 * (1 - (q.1 ^ 2 + q.2 ^ 2)) ^ 5 / (1 + (q.1 ^ 2 + q.2 ^ 2)))
      else 0 :=
    Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop)
      measurable_const
  rw [tbt_lintegral_eq_coord, setLIntegral_congr_fun tbt_Dom_measurableSet (g := G)
      (fun p hp => ?_), ← lintegral_indicator tbt_Dom_measurableSet,
    tbt_lintegral_fin_three_eq (hG.indicator tbt_Dom_measurableSet), Measure.volume_eq_prod,
    lintegral_prod _ hif.aemeasurable]
  · refine lintegral_congr fun a => lintegral_congr fun b => ?_
    split_ifs with h
    · have hmem : ∀ c, (![a, b, c] : Fin 3 → ℝ) ∈ tbtDom := fun c => by simpa [tbtDom] using h
      simp_rw [Set.indicator_of_mem (hmem _)]
      have hρ : 0 < 1 - (a ^ 2 + b ^ 2) := by linarith
      simp only [G, tbtRho, tbtSig, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [tbt_lintegral_tau (by positivity) (by positivity)]
      congr 1
      field_simp
    · have hmem : ∀ c, (![a, b, c] : Fin 3 → ℝ) ∉ tbtDom := fun c => by simpa [tbtDom] using h
      simp_rw [Set.indicator_of_notMem (hmem _)]
      simp
  · have h0 := tbt_Rho_pos hp
    have h1 : 0 < tbtSig p ^ 2 + p 2 ^ 2 := by have := tbt_Sig_pos hp; positivity
    simp only [G]
    rw [tbt_abs_q3_Inv hp, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring

/-- `q₃ (∇u) ∈ L¹ (ℝ³)`: the integral of TeX 1779–1783 (`tbt_lintegral_abs_q3`) is finite, since
`(1 − |ζ|²)⁵ / (1 + |ζ|²) ≤ 1` on the disc. -/
theorem tbt_integrable_q3 : Integrable fun x => q3 (jac tbtWitness x) := by
  have hc : Continuous fun x => q3 (jac tbtWitness x) :=
    tbt_continuous_q3.comp (tbt_continuous_jac tbt_witness_contDiff)
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  show ∫⁻ x, ‖q3 (jac tbtWitness x)‖ₑ < ⊤
  simp_rw [Real.enorm_eq_ofReal_abs]
  rw [tbt_lintegral_abs_q3]
  refine lt_of_le_of_lt (lintegral_mono fun q => ?_ : _ ≤ ∫⁻ q : ℝ × ℝ,
    (Metric.ball (0 : ℝ × ℝ) 1).indicator (fun _ => ENNReal.ofReal (Real.pi / 4)) q) ?_
  · split_ifs with h
    · have hq : q ∈ Metric.ball (0 : ℝ × ℝ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff, Real.norm_eq_abs,
          Real.norm_eq_abs]
        exact ⟨abs_lt.mpr (abs_lt_of_sq_lt_sq' (by nlinarith [sq_nonneg q.2]) (by norm_num)),
          abs_lt.mpr (abs_lt_of_sq_lt_sq' (by nlinarith [sq_nonneg q.1]) (by norm_num))⟩
      rw [Set.indicator_of_mem hq]
      apply ENNReal.ofReal_le_ofReal
      have hρ0 : 0 ≤ 1 - (q.1 ^ 2 + q.2 ^ 2) := by linarith
      have hρ1 : 1 - (q.1 ^ 2 + q.2 ^ 2) ≤ 1 := by nlinarith [sq_nonneg q.1, sq_nonneg q.2]
      have h5 : (1 - (q.1 ^ 2 + q.2 ^ 2)) ^ 5 ≤ 1 := pow_le_one₀ hρ0 hρ1
      rw [mul_div_assoc]
      have : (1 - (q.1 ^ 2 + q.2 ^ 2)) ^ 5 / (1 + (q.1 ^ 2 + q.2 ^ 2)) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [sq_nonneg q.1, sq_nonneg q.2]
      have hpi := Real.pi_pos
      nlinarith
    · exact bot_le
  · rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- `σ ≤ √(1 + R²)` on `B_R` (TeX 1787): `σ² = 1 + |w|² − t² + (Im s)²` and
`(Im s)² = t² / σ² ≤ t²`. -/
theorem tbt_re_S_le_sqrt {R : ℝ} {X : Fin 3 → ℝ} (hX : ∑ i, X i ^ 2 < R ^ 2) :
    (tbtS X).re ≤ √(1 + R ^ 2) := by
  obtain ⟨h1, h2⟩ := tbt_S_parts X
  have hσ1 := tbt_one_le_sigma_sq X
  have him : (tbtS X).im ^ 2 ≤ X 2 ^ 2 := by
    have : (tbtS X).re ^ 2 * (tbtS X).im ^ 2 = X 2 ^ 2 := by rw [← mul_pow, h2]; ring
    nlinarith [sq_nonneg (tbtS X).im]
  have hX' : X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 < R ^ 2 := by simpa [Fin.sum_univ_three] using hX
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith))

/-- The radial integral, by the substitution `σ = (1 + r²) / (1 − r²)`, `dσ = 4 r dr / (1 − r²)²`:
`∫_0^{r_S} r dr / ((1 − r²) (1 + r²)) = ¼ ∫_1^S dσ / σ = ¼ log S`, `r_S² = (S − 1) / (S + 1)`. -/
theorem tbt_integral_radial {S : ℝ} (hS : 1 ≤ S) :
    ∫ r in (0 : ℝ)..√((S - 1) / (S + 1)), r / ((1 - r ^ 2) * (1 + r ^ 2)) =
      1 / 4 * Real.log S := by
  set k := (S - 1) / (S + 1) with hk
  have hk0 : 0 ≤ k := div_nonneg (by linarith) (by linarith)
  have hk1 : k < 1 := by rw [hk, div_lt_one (by linarith)]; linarith
  have hsq : √k ^ 2 = k := Real.sq_sqrt hk0
  have hI : ∀ x ∈ Set.uIcc 0 √k, 0 < 1 - x ^ 2 := fun x hx => by
    rw [Set.uIcc_of_le (Real.sqrt_nonneg _)] at hx
    have : x ^ 2 ≤ √k ^ 2 := pow_le_pow_left₀ hx.1 hx.2 2
    linarith
  set f : ℝ → ℝ := fun r => (1 + r ^ 2) / (1 - r ^ 2)
  set f' : ℝ → ℝ := fun r => 4 * r / (1 - r ^ 2) ^ 2
  have hf : ∀ x ∈ Set.uIcc 0 √k, HasDerivAt f (f' x) x := fun x hx => by
    have h := ((hasDerivAt_pow 2 x).const_add 1).div ((hasDerivAt_pow 2 x).const_sub 1)
      (hI x hx).ne'
    refine h.congr_deriv ?_
    have := (hI x hx).ne'
    simp only [f']
    field_simp
    ring
  have hf' : ContinuousOn f' (Set.uIcc 0 √k) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => by have := hI x hx; positivity
  have hg : ContinuousOn (fun u : ℝ => 1 / u) (f '' Set.uIcc 0 √k) :=
    ContinuousOn.div continuousOn_const continuousOn_id fun u hu => by
      obtain ⟨x, hx, rfl⟩ := hu
      have := hI x hx
      simp only [f]; positivity
  have hsub := intervalIntegral.integral_comp_mul_deriv' hf hf' hg
  have hf0 : f 0 = 1 := by simp [f]
  have hfk : f √k = S := by
    simp only [f]
    rw [hsq, hk]
    have : S + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hf0, hfk, integral_one_div_of_pos one_pos (by linarith), div_one] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x hx => ?_
  have := (hI x hx).ne'
  have h2 : 1 + x ^ 2 ≠ 0 := by positivity
  simp only [Function.comp, f, f']
  field_simp

/-- `∫_{B_R} |s|⁻⁴ ≲ ∫_1^{√(1+R²)} dσ / σ` (TeX 1785–1790). In the coordinates `(ζ, τ)` the
integrand is `|s|⁻⁴ · 4 |s|² / (1 − |ζ|²)² = 4 / ((1 − |ζ|²)² (σ² + τ²))`, over `σ ≤ √(1 + R²)`;
integrate in `τ` (`π / σ`), then over the disc in polar coordinates, `dA = r dr dθ`, and substitute
`σ = (1 + r²) / (1 − r²)` (`tbt_integral_radial`). -/
theorem tbt_lintegral_inv_S4_le (R : ℝ) :
    ∫⁻ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}, ENNReal.ofReal (144 / ‖tbtS x‖ ^ 4) ≤
      ENNReal.ofReal (288 * Real.pi ^ 2 * Real.log √(1 + R ^ 2)) := by
  set S := √(1 + R ^ 2) with hSdef
  have hS1 : 1 ≤ S := by rw [hSdef, Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  set k := (S - 1) / (S + 1) with hk
  have hk0 : 0 ≤ k := div_nonneg (by linarith) (by linarith)
  have hk1 : k < 1 := by rw [hk, div_lt_one (by linarith)]; linarith
  set B := {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}
  set E := {X : Fin 3 → ℝ | (tbtS X).re ≤ S}
  have hE : MeasurableSet E :=
    measurableSet_le (Complex.continuous_re.comp (tbt_S_contDiff (n := 0)).continuous).measurable
      measurable_const
  set Φ : ℝ → ℝ≥0∞ := fun u => if u ≤ k then
    ENNReal.ofReal (576 * Real.pi / ((1 - u) * (1 + u))) else 0 with hΦ
  have hΦm : Measurable Φ := Measurable.ite measurableSet_Iic (by fun_prop) measurable_const
  set G : (Fin 3 → ℝ) → ℝ≥0∞ := fun p => if tbtSig p ≤ S then
    ENNReal.ofReal (576 / tbtRho p ^ 2 / (tbtSig p ^ 2 + p 2 ^ 2)) else 0
  -- on the disc, `σ ≤ S ↔ |ζ|² ≤ k`
  have hiff : ∀ u : ℝ, u < 1 → ((1 + u) / (1 - u) ≤ S ↔ u ≤ k) := fun u hu => by
    rw [div_le_iff₀ (by linarith), hk, le_div_iff₀ (by linarith)]
    constructor <;> intro h <;> linarith
  have hlog : 0 ≤ Real.log S := Real.log_nonneg hS1
  calc ∫⁻ x in B, ENNReal.ofReal (144 / ‖tbtS x‖ ^ 4)
      ≤ ∫⁻ x in E, ENNReal.ofReal (144 / ‖tbtS x‖ ^ 4) :=
        lintegral_mono_set fun X hX => tbt_re_S_le_sqrt hX
    _ = ∫⁻ X, E.indicator (fun X => ENNReal.ofReal (144 / ‖tbtS X‖ ^ 4)) X :=
        (lintegral_indicator hE _).symm
    _ = ∫⁻ p in tbtDom, G p := by
        rw [tbt_lintegral_eq_coord]
        refine setLIntegral_congr_fun tbt_Dom_measurableSet fun p hp => ?_
        have h0 := tbt_Rho_pos hp
        have h1 : 0 < tbtSig p ^ 2 + p 2 ^ 2 := by have := tbt_Sig_pos hp; positivity
        simp only [G, E, Set.indicator, Set.mem_ofPred_eq, tbt_re_S_Inv hp]
        split_ifs
        · rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show ‖tbtS (tbtInv p)‖ ^ 4 = (‖tbtS (tbtInv p)‖ ^ 2) ^ 2 by ring,
            tbt_normSq_S_Inv hp]
          field_simp
          ring
        · simp
    _ = ∫⁻ p, tbtDom.indicator G p := (lintegral_indicator tbt_Dom_measurableSet _).symm
    _ ≤ ∫⁻ a, ∫⁻ b, ∫⁻ c, tbtDom.indicator G ![a, b, c] := tbt_lintegral_fin_three_le _
    _ = ∫⁻ a, ∫⁻ b, Φ (a ^ 2 + b ^ 2) := by
        refine lintegral_congr fun a => lintegral_congr fun b => ?_
        by_cases h : a ^ 2 + b ^ 2 < 1
        · have hmem : ∀ c, (![a, b, c] : Fin 3 → ℝ) ∈ tbtDom := fun c => by
            simpa [tbtDom] using h
          simp_rw [Set.indicator_of_mem (hmem _)]
          have hρ : 0 < 1 - (a ^ 2 + b ^ 2) := by linarith
          simp only [G, Φ, tbtRho, tbtSig, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hiff _ h]
          split_ifs
          · rw [tbt_lintegral_tau (by positivity) (by positivity)]
            congr 1
            field_simp
          · simp
        · have hmem : ∀ c, (![a, b, c] : Fin 3 → ℝ) ∉ tbtDom := fun c => by
            simpa [tbtDom] using h
          simp_rw [Set.indicator_of_notMem (hmem _)]
          have hk' : ¬ a ^ 2 + b ^ 2 ≤ k := by linarith
          simp only [lintegral_const, zero_mul, Φ, hk', ite_false]
    _ = ∫⁻ q : ℝ × ℝ, Φ (q.1 ^ 2 + q.2 ^ 2) := by
        rw [Measure.volume_eq_prod, lintegral_prod (fun q : ℝ × ℝ => Φ (q.1 ^ 2 + q.2 ^ 2))
          (hΦm.comp (by fun_prop)).aemeasurable]
    _ = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * Φ (p.1 ^ 2) := by
        rw [← lintegral_comp_polarCoord_symm, polarCoord_target]
        refine lintegral_congr fun p => ?_
        rw [polarCoord_symm_apply, smul_eq_mul, mul_pow, mul_pow, ← mul_add,
          Real.cos_sq_add_sin_sq, mul_one]
    _ ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r * Φ (r ^ 2) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_le _
    _ = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r * Φ (r ^ 2)) *
          ENNReal.ofReal (2 * Real.pi) := by
        simp_rw [setLIntegral_const, Real.volume_Ioo]
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        congr 2; ring
    _ = ENNReal.ofReal (∫ r in (0 : ℝ)..√k, 576 * Real.pi * (r / ((1 - r ^ 2) * (1 + r ^ 2)))) *
          ENNReal.ofReal (2 * Real.pi) := by
        congr 1
        have hI : ∀ x ∈ Set.Icc 0 √k, 0 < 1 - x ^ 2 := fun x hx => by
          have : x ^ 2 ≤ √k ^ 2 := pow_le_pow_left₀ hx.1 hx.2 2
          rw [Real.sq_sqrt hk0] at this
          linarith
        have hcont : ContinuousOn (fun r : ℝ => 576 * Real.pi * (r / ((1 - r ^ 2) * (1 + r ^ 2))))
            (Set.Icc 0 √k) :=
          continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => by
            have := hI x hx; positivity)
        rw [intervalIntegral.integral_of_le (Real.sqrt_nonneg _),
          ofReal_integral_eq_lintegral_ofReal
            ((hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
            ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun x hx => by
              have := hI x (Set.Ioc_subset_Icc_self hx)
              have := hx.1.le
              simp only [Pi.zero_apply]; positivity))]
        rw [← Set.Ioi_inter_Iic, Set.inter_comm, ← Measure.restrict_restrict measurableSet_Iic,
          ← lintegral_indicator measurableSet_Iic]
        refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
        simp only [Φ, Set.indicator, Set.mem_Iic]
        have hiff' := Real.le_sqrt hr.le hk0
        split_ifs with h1 h2 h2
        · have : 0 < 1 - r ^ 2 := by linarith
          rw [← ENNReal.ofReal_mul hr.le]
          congr 1
          field_simp
        · exact absurd (hiff'.mpr h1) h2
        · exact absurd (hiff'.mp h2) h1
        · simp
    _ = ENNReal.ofReal (288 * Real.pi ^ 2 * Real.log S) := by
        rw [intervalIntegral.integral_const_mul, tbt_integral_radial hS1,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring


/-- `∫_{B_R} F ≲ log (2 + R)` for every continuous `F ≥ 0` with `F ≤ c · 144 / |s|⁴`, from the
computation in the coordinates `(ζ, τ)` (`tbt_lintegral_inv_S4_le`) and
`log √(1 + R²) ≤ log (2 + R)`. -/
theorem tbt_log_bound_of_le {F : (Fin 3 → ℝ) → ℝ} (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x)
    {c : ℝ} (hc : 0 ≤ c) (hle : ∀ x, F x ≤ c * (144 / ‖tbtS x‖ ^ 4)) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}, F x ≤
      c * (576 * Real.pi ^ 2 * Real.log (2 + R)) := by
  have hlog : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have hS1 : 1 ≤ √(1 + R ^ 2) := by rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  have hS : Real.log √(1 + R ^ 2) ≤ Real.log (2 + R) := by
    apply Real.log_le_log (by linarith)
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0)
    hF.aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  calc ∫⁻ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}, ENNReal.ofReal (F x)
      ≤ ∫⁻ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2},
          ENNReal.ofReal c * ENNReal.ofReal (144 / ‖tbtS x‖ ^ 4) :=
        lintegral_mono fun x => by
          rw [← ENNReal.ofReal_mul hc]; exact ENNReal.ofReal_le_ofReal (hle x)
    _ = ENNReal.ofReal c * ∫⁻ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2},
          ENNReal.ofReal (144 / ‖tbtS x‖ ^ 4) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (288 * Real.pi ^ 2 * Real.log √(1 + R ^ 2)) :=
        mul_le_mul_right (tbt_lintegral_inv_S4_le R) _
    _ ≤ ENNReal.ofReal (c * (576 * Real.pi ^ 2 * Real.log (2 + R))) := by
        rw [← ENNReal.ofReal_mul hc]
        apply ENNReal.ofReal_le_ofReal
        have hpi := Real.pi_pos
        have hl := Real.log_nonneg hS1
        have : 288 * Real.pi ^ 2 * Real.log √(1 + R ^ 2) ≤
            576 * Real.pi ^ 2 * Real.log (2 + R) := by nlinarith [sq_nonneg Real.pi]
        exact mul_le_mul_of_nonneg_left this hc

/-- The logarithmic bound: `∫_{B_R} |∇u|⁴ ≤ 576 π² log (2 + R)`. -/
theorem tbt_log_bound {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}, frobSq (jac tbtWitness x) ^ 2 ≤
      576 * Real.pi ^ 2 * Real.log (2 + R) := by
  have h := tbt_log_bound_of_le
    ((tbt_continuous_frobSq.comp (tbt_continuous_jac tbt_witness_contDiff)).pow 2)
    (fun x => sq_nonneg _) zero_le_one
    (fun x => by rw [one_mul]; exact tbt_frobSq_sq_le_inv_S4 x) hR
  rwa [one_mul] at h

theorem tbt_continuous_zCoord (k : Fin 3) :
    Continuous fun A : Matrix (Fin 2) (Fin 4) ℝ => zCoord A k := by
  have hα : ∀ k l : Fin 4, Continuous fun A : Matrix (Fin 2) (Fin 4) ℝ => wirtAlpha A k l := by
    intro k l
    unfold wirtAlpha
    have := tbt_continuous_entry (d := 2) (m := 4)
    fun_prop
  have hβ : ∀ k l : Fin 4, Continuous fun A : Matrix (Fin 2) (Fin 4) ℝ => wirtBeta A k l := by
    intro k l
    unfold wirtBeta
    have := tbt_continuous_entry (d := 2) (m := 4)
    fun_prop
  fin_cases k
  · exact Complex.continuous_conj.comp (hα 2 3)
  · exact Complex.continuous_conj.comp (hα 0 1)
  · exact hβ 0 1

theorem tbt_continuous_embedJ : Continuous embedJ := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [embedJ, Matrix.of_apply]
  split_ifs
  · exact tbt_continuous_entry _ _
  · exact continuous_const

/-- `|u| ≤ 3/2`. -/
theorem tbt_norm_witness_le (x : Fin 3 → ℝ) : ‖tbtWitness x‖ ≤ 3 / 2 := by
  have hU : ‖tbtU x‖ ≤ 3 / 2 := by
    have hz := (tbt_norm_Zeta_lt_one x).le
    have hz0 := norm_nonneg (tbtZeta x)
    calc ‖tbtU x‖ ≤ ‖conj (tbtZeta x)‖ + ‖tbtZeta x ^ 2 / 2‖ := norm_add_le _ _
      _ = ‖tbtZeta x‖ + ‖tbtZeta x‖ ^ 2 / 2 := by
        rw [Complex.norm_conj, norm_div, norm_pow, Complex.norm_two]
      _ ≤ 3 / 2 := by nlinarith
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
  fin_cases i
  · exact (Complex.abs_re_le_norm _).trans hU
  · exact (Complex.abs_im_le_norm _).trans hU


/-- **Proposition 5.2** (`prop:qc-witness`, an (almost) quasiconvexity witness): there is a smooth
bounded `u : ℝ³ → ℝ²` with `∇u (x) ∈ 𝓛₃` and `q₃ (∇u (x)) < 0` for every `x`,
`q₃ (∇u) ∈ L¹ (ℝ³)`, and `∫_{B_R} |∇u|⁴ ≲ log (2 + R)` (Euclidean balls `B_R`, `R ≥ 0`).

Proof, as in the paper (TeX lines 1717–1796): `u = ζ̄ + ζ² / 2` with `ζ` the root in the unit disc
of `w̄ ζ² + 2 t ζ + w = h (ζ)`, `h (ξ) = −2 i ξ`, explicitly `ζ = i w / (1 − i t + s)` with
`s = √((1 − i t)² + |w|²)` (`tbtZeta`; `|ζ| < 1` from `σ = Re s = (1 + |ζ|²) / (1 − |ζ|²)`,
`tbt_sigma_eq`). Implicit differentiation gives `∂ζ = i / (2 s)`, `∂̄ζ = ζ² ∂ζ`, `ζ_t = 2 ζ ∂ζ`
(`tbt_ZetaD_eq`), hence `∇u ∈ 𝓛₃` (`tbt_jac_mem_L3`) and, by (24),
`q₃ (∇u) = −|∂ζ|⁴ (1 − |ζ|²)⁶ < 0` (`tbt_q3_jac`, `F' = 1`). The integrals are evaluated in the
coordinates `(ζ, τ)`, `τ = −Im s`: the inverse coordinates `w = −2 ζ (τ + i) / (1 − |ζ|²)`,
`t = σ τ` map `𝔻 × ℝ` bijectively onto `ℝ³` with
`dx dy dt = 4 |s|² (1 − |ζ|²)⁻² dA (ζ) dτ` (`tbt_lintegral_eq_coord`, by Mathlib's change of
variables formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, with the Jacobian
`tbt_Inv_det`). Integrating in `τ` (`∫ dτ / (σ² + τ²) = π / σ`) gives
`∫ |q₃ (∇u)| = (π/4) ∫_𝔻 (1 − |ζ|²)⁵ / (1 + |ζ|²) dA (ζ) < ∞` (`tbt_lintegral_abs_q3`,
`tbt_integrable_q3`). For the energy, `|∇u| ≲ |∂ζ| = 1 / (2 |s|)` (`tbt_frobSq_sq_le_inv_S4`),
`σ ≤ √(1 + R²)` on `B_R` (`tbt_re_S_le_sqrt`), and integrating in `τ`, then over the disc in polar
coordinates with the substitution `σ = (1 + |ζ|²) / (1 − |ζ|²)`, gives
`∫_{B_R} |∇u|⁴ ≤ 288 π² ∫_1^{√(1+R²)} dσ / σ ≤ 576 π² log (2 + R)` (`tbt_lintegral_inv_S4_le`,
`tbt_integral_radial`, `tbt_log_bound`).

Mechanical differences: smoothness of `ζ` is read off the closed form rather than from "unique
simple root, hence smooth" (`tbt_Zeta_contDiff`); `q₃ (∇u) ∈ L¹` is concluded from the formula for
`∫ |q₃ (∇u)|` (the paper writes the integral of `q₃`, which is `−∫ |q₃|` since `q₃ < 0`); and the
radial integral `∫ r dr / ((1 − r²) (1 + r²))` is turned into `¼ ∫ dσ / σ` by the substitution
theorem. -/
theorem proposition5_2 :
    ∃ u : (Fin 3 → ℝ) → Fin 2 → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧
      (∃ M : ℝ, ∀ x, ‖u x‖ ≤ M) ∧ (∀ x, jac u x ∈ L3) ∧ (∀ x, q3 (jac u x) < 0) ∧
      Integrable (fun x => q3 (jac u x)) ∧
      ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
        ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}, frobSq (jac u x) ^ 2 ≤
          C * Real.log (2 + R) :=
  ⟨tbtWitness, tbt_witness_contDiff, ⟨3 / 2, tbt_norm_witness_le⟩, tbt_jac_mem_L3,
    tbt_q3_jac_neg, tbt_integrable_q3, ⟨576 * Real.pi ^ 2, fun _ hR => tbt_log_bound hR⟩⟩

end Cassese
