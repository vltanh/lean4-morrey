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

/-!
# Section 5.2: the quasiconvexity witness (Proposition 5.2)

The construction of the proof of Proposition 5.2 (TeX lines 1717–1796). Identify `ℝ³` with
`ℂ × ℝ`, `X = (x, y, t) ↦ (w, t)` with `w = x + i y`. With the principal square root
`s = √((1 − i t)² + |w|²)` (`tbtS`, written `exp (log z / 2)`), the root in the unit disc of
`w̄ ζ² + 2 (t + i) ζ + w = 0` is `ζ = i w / (1 − i t + s)` (`tbtZeta`), and the witness is
`u = ζ̄ + ζ² / 2` (`tbtU`, the profile `F (z) = z`, `G (z) = z² / 2`), as a map into `ℝ²`
(`tbtWitness`).

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

/-- The decay of `q₃ (∇u)`: `|q₃ (∇u)| ≤ 4 / (1 + |X|²)²`. -/
theorem tbt_abs_q3_le (X : Fin 3 → ℝ) :
    |q3 (jac tbtWitness X)| ≤ 4 / (1 + (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2)) ^ 2 := by
  rw [tbt_q3_jac]
  obtain ⟨h1, h2⟩ := tbt_S_parts X
  have hσ := tbt_S_re_pos X
  have hσ1 := tbt_one_le_sigma_sq X
  have hsig := tbt_sigma_eq X
  set σ := (tbtS X).re with hσ_def
  set τ := (tbtS X).im with hτ_def
  set ρ := 1 - ‖tbtZeta X‖ ^ 2 with hρ_def
  have hρ0 : 0 < ρ := by
    have := tbt_norm_Zeta_lt_one X
    nlinarith [norm_nonneg (tbtZeta X)]
  have hρ1 : ρ ≤ 1 := by nlinarith [norm_nonneg (tbtZeta X)]
  -- `ρ (1 + σ) = 2`
  have hρσ : ρ * (1 + σ) = 2 := by
    have : ‖tbtZeta X‖ ^ 2 = 1 - ρ := by rw [hρ_def]; ring
    rw [this] at hsig; linarith
  have hK : ‖tbtK X‖ ^ 2 = 1 / (4 * (σ ^ 2 + τ ^ 2)) := by
    rw [tbt_norm_K, Complex.sq_norm, Complex.normSq_apply, hσ_def, hτ_def]; ring
  rw [hK]
  -- `σ² (σ² + τ²) = σ⁴ + t² ≥ (1 + |X|²) / 2`
  have hτσ : σ ^ 2 * τ ^ 2 = X 2 ^ 2 := by rw [← mul_pow, h2]; ring
  have hlow : 1 + (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2) ≤ 2 * (σ ^ 2 * (σ ^ 2 + τ ^ 2)) := by
    nlinarith [sq_nonneg τ]
  have hpos : 0 < σ ^ 2 + τ ^ 2 := by positivity
  have hρσ' : ρ * σ ≤ 2 := by nlinarith
  have hρ4 : ρ ^ 4 * σ ^ 4 ≤ 16 := by
    have : (ρ * σ) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by positivity) hρσ' 4
    nlinarith
  have hρ6 : ρ ^ 6 ≤ ρ ^ 4 := pow_le_pow_of_le_one hρ0.le hρ1 (by norm_num)
  have hA : 0 < 1 + (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2) := by positivity
  rw [abs_of_nonpos (by
    have : 0 ≤ (1 / (4 * (σ ^ 2 + τ ^ 2))) ^ 2 * ρ ^ 6 := by positivity
    linarith), neg_mul, neg_neg]
  rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  -- `ρ⁶ (1 + |X|²)² ≤ 4 · 16 (σ² + τ²)²`
  have h3 : ρ ^ 6 * (1 + (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2)) ^ 2 ≤
      ρ ^ 4 * (2 * (σ ^ 2 * (σ ^ 2 + τ ^ 2))) ^ 2 := by
    calc ρ ^ 6 * (1 + (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2)) ^ 2
        ≤ ρ ^ 4 * (1 + (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2)) ^ 2 := by gcongr
      _ ≤ ρ ^ 4 * (2 * (σ ^ 2 * (σ ^ 2 + τ ^ 2))) ^ 2 := by gcongr
  have h4 : ρ ^ 4 * (2 * (σ ^ 2 * (σ ^ 2 + τ ^ 2))) ^ 2 =
      4 * (ρ ^ 4 * σ ^ 4) * (σ ^ 2 + τ ^ 2) ^ 2 := by ring
  nlinarith [mul_le_mul_of_nonneg_right hρ4 (sq_nonneg (σ ^ 2 + τ ^ 2))]

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

/-- `|∇u|⁴ ≲ |s|⁻⁴`, in the form used for the logarithmic bound:
`|∇u|⁴ ≤ 72 / (1 + |w|²) · (1 / (1 + (t − |w|)²) + 1 / (1 + (t + |w|)²))`, from
`|s|⁴ = |(1 − i t)² + |w|²|² = (1 + (t − |w|)²) (1 + (t + |w|)²)`. -/
theorem tbt_frobSq_sq_le (X : Fin 3 → ℝ) :
    frobSq (jac tbtWitness X) ^ 2 ≤ 72 / (1 + (X 0 ^ 2 + X 1 ^ 2)) *
      (1 / (1 + (X 2 - √(X 0 ^ 2 + X 1 ^ 2)) ^ 2) + 1 / (1 + (X 2 + √(X 0 ^ 2 + X 1 ^ 2)) ^ 2)) := by
  have hF : frobSq (jac tbtWitness X) ≤ 48 * ‖tbtK X‖ ^ 2 := by
    rw [tbt_frobSq_jac, Fin.sum_univ_three]
    have := fun k => pow_le_pow_left₀ (norm_nonneg _) (tbt_norm_UD_le X k) 2
    nlinarith [this 0, this 1, this 2]
  have hF0 : 0 ≤ frobSq (jac tbtWitness X) := tbt_frobSq_nonneg _
  -- `|s|⁴ = |z|²`
  have hS4 : ‖tbtS X‖ ^ 4 = (1 - X 2 ^ 2 + (X 0 ^ 2 + X 1 ^ 2)) ^ 2 + (-2 * X 2) ^ 2 := by
    have : ‖tbtS X‖ ^ 4 = ‖tbtZ X‖ ^ 2 := by
      rw [← tbt_S_sq, norm_pow]; ring
    rw [this, Complex.sq_norm, Complex.normSq_apply, tbt_Z_re, tbt_Z_im]; ring
  have hSpos : 0 < ‖tbtS X‖ := norm_pos_iff.mpr (tbt_S_ne_zero X)
  have hK := tbt_norm_K X
  set r := √(X 0 ^ 2 + X 1 ^ 2) with hr
  have hr2 : r ^ 2 = X 0 ^ 2 + X 1 ^ 2 := Real.sq_sqrt (by positivity)
  set t := X 2
  -- `|s|⁴ = (1 + (t − r)²) (1 + (t + r)²)`
  have hprod : ‖tbtS X‖ ^ 4 = (1 + (t - r) ^ 2) * (1 + (t + r) ^ 2) := by
    rw [hS4, ← hr2]; ring
  have hp : 0 < 1 + (t - r) ^ 2 := by positivity
  have hq : 0 < 1 + (t + r) ^ 2 := by positivity
  calc frobSq (jac tbtWitness X) ^ 2 ≤ (48 * ‖tbtK X‖ ^ 2) ^ 2 := pow_le_pow_left₀ hF0 hF 2
    _ = 144 / ‖tbtS X‖ ^ 4 := by rw [hK]; field_simp; ring
    _ = 144 / ((1 + (t - r) ^ 2) * (1 + (t + r) ^ 2)) := by rw [hprod]
    _ = 144 / (2 + 2 * t ^ 2 + 2 * r ^ 2) * (1 / (1 + (t - r) ^ 2) + 1 / (1 + (t + r) ^ 2)) := by
      field_simp; ring
    _ ≤ 72 / (1 + (X 0 ^ 2 + X 1 ^ 2)) * (1 / (1 + (t - r) ^ 2) + 1 / (1 + (t + r) ^ 2)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity), ← hr2]
      nlinarith [sq_nonneg t, sq_nonneg r]


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



/-- `∫ (1 + (z + c)²)⁻¹ dz = π`. -/
theorem tbt_lintegral_cauchy (c : ℝ) :
    ∫⁻ z : ℝ, ENNReal.ofReal (1 / (1 + (z + c) ^ 2)) = ENNReal.ofReal Real.pi := by
  have hi : Integrable fun z : ℝ => 1 / (1 + (z + c) ^ 2) := by
    simpa [one_div] using integrable_inv_one_add_sq.comp_add_right c
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun z => by positivity)]
  congr 1
  rw [integral_add_right_eq_self (fun z : ℝ => 1 / (1 + z ^ 2)) c]
  simp [one_div]

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

/-- `∫_{−R}^{R} (1 + x²)^{−1/2} dx = 2 arsinh R`. -/
theorem tbt_lintegral_Icc_inv_sqrt {R : ℝ} (hR : 0 ≤ R) :
    ∫⁻ x in Set.Icc (-R) R, ENNReal.ofReal (1 / √(1 + x ^ 2)) =
      ENNReal.ofReal (2 * Real.arsinh R) := by
  have hc : Continuous fun x : ℝ => 1 / √(1 + x ^ 2) := by
    refine continuous_const.div (by fun_prop) fun x => ?_
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hi : IntegrableOn (fun x : ℝ => 1 / √(1 + x ^ 2)) (Set.Icc (-R) R) :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun z => by positivity)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => by
      simpa [one_div] using Real.hasDerivAt_arsinh x)
      (hc.intervalIntegrable _ _), Real.arsinh_neg]
  ring

/-- `arsinh R ≤ 2 log (2 + R)` for `R ≥ 0`. -/
theorem tbt_arsinh_le_log {R : ℝ} (hR : 0 ≤ R) : Real.arsinh R ≤ 2 * Real.log (2 + R) := by
  rw [Real.arsinh, ← Real.log_rpow (by linarith)]
  apply Real.log_le_log (by positivity)
  have : √(1 + R ^ 2) ≤ 1 + R := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  rw [show ((2 : ℝ) + R) ^ (2 : ℝ) = (2 + R) ^ 2 by norm_cast]
  nlinarith



theorem tbt_continuous_jac {φ : (Fin 3 → ℝ) → Fin 2 → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : Continuous fun x => jac φ x := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have hi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => φ y i := (contDiff_pi.1 hφ) i
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The inner integral over `t`: `∫ (1 / (1 + (t − r)²) + 1 / (1 + (t + r)²)) dt = 2π`. -/
theorem tbt_lintegral_two_cauchy (a r : ℝ) (ha : 0 ≤ a) :
    ∫⁻ z : ℝ, ENNReal.ofReal (a * (1 / (1 + (z - r) ^ 2) + 1 / (1 + (z + r) ^ 2))) =
      ENNReal.ofReal a * ENNReal.ofReal (2 * Real.pi) := by
  have hm1 : Measurable fun z : ℝ => ENNReal.ofReal (1 / (1 + (z + -r) ^ 2)) := by fun_prop
  have hm2 : Measurable fun z : ℝ => ENNReal.ofReal (1 / (1 + (z + r) ^ 2)) := by fun_prop
  have h : ∀ z : ℝ, ENNReal.ofReal (a * (1 / (1 + (z - r) ^ 2) + 1 / (1 + (z + r) ^ 2))) =
      ENNReal.ofReal a * (ENNReal.ofReal (1 / (1 + (z + -r) ^ 2)) +
        ENNReal.ofReal (1 / (1 + (z + r) ^ 2))) := by
    intro z
    rw [ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add (by positivity) (by positivity), sub_eq_add_neg]
  simp_rw [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm1, tbt_lintegral_cauchy,
    tbt_lintegral_cauchy, ← ENNReal.ofReal_add Real.pi_pos.le Real.pi_pos.le, two_mul]

/-- The logarithmic bound: `∫_{B_R} |∇u|⁴ ≤ 576 π² log (2 + R)`. -/
theorem tbt_log_bound {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}, frobSq (jac tbtWitness x) ^ 2 ≤
      576 * Real.pi ^ 2 * Real.log (2 + R) := by
  set B := {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}
  set Φ : (Fin 3 → ℝ) → ℝ := fun X => 72 / (1 + (X 0 ^ 2 + X 1 ^ 2)) *
      (1 / (1 + (X 2 - √(X 0 ^ 2 + X 1 ^ 2)) ^ 2) + 1 / (1 + (X 2 + √(X 0 ^ 2 + X 1 ^ 2)) ^ 2))
  set Q := {X : Fin 3 → ℝ | |X 0| ≤ R ∧ |X 1| ≤ R}
  have hcont : Continuous fun x => frobSq (jac tbtWitness x) ^ 2 :=
    (tbt_continuous_frobSq.comp (tbt_continuous_jac tbt_witness_contDiff)).pow 2
  have hlog : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    hcont.aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  have hBQ : B ⊆ Q := by
    intro X hX
    have hX' : X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 < R ^ 2 := by
      simpa [B, Fin.sum_univ_three] using hX
    have h0 : X 0 ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (X 1), sq_nonneg (X 2)]
    have h1 : X 1 ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (X 0), sq_nonneg (X 2)]
    exact ⟨(abs_lt_of_sq_lt_sq h0 hR).le, (abs_lt_of_sq_lt_sq h1 hR).le⟩
  have hQm : MeasurableSet Q := by
    have : Q = {X : Fin 3 → ℝ | |X 0| ≤ R} ∩ {X | |X 1| ≤ R} := rfl
    rw [this]
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)
  calc ∫⁻ x in B, ENNReal.ofReal (frobSq (jac tbtWitness x) ^ 2)
      ≤ ∫⁻ x in B, ENNReal.ofReal (Φ x) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (tbt_frobSq_sq_le x)
    _ ≤ ∫⁻ x in Q, ENNReal.ofReal (Φ x) := lintegral_mono_set hBQ
    _ = ∫⁻ x, Q.indicator (fun X => ENNReal.ofReal (Φ X)) x := (lintegral_indicator hQm _).symm
    _ ≤ ∫⁻ x, ∫⁻ y, ∫⁻ z, Q.indicator (fun X => ENNReal.ofReal (Φ X)) ![x, y, z] :=
        tbt_lintegral_fin_three_le _
    _ ≤ ∫⁻ x, (Set.Icc (-R) R).indicator (fun x => ∫⁻ y,
          ENNReal.ofReal (2 * Real.pi * 72) * ENNReal.ofReal (1 / (√(1 + x ^ 2) ^ 2 + y ^ 2))) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : |x| ≤ R
        · rw [Set.indicator_of_mem (abs_le.mp hx)]
          refine lintegral_mono fun y => ?_
          by_cases hy : |y| ≤ R
          · have hQ : ∀ z, (![x, y, z] : Fin 3 → ℝ) ∈ Q := fun z => ⟨hx, hy⟩
            simp_rw [Set.indicator_of_mem (hQ _)]
            simp only [Φ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
              Matrix.head_cons, Matrix.tail_cons]
            rw [tbt_lintegral_two_cauchy _ _ (by positivity), mul_comm, ← ENNReal.ofReal_mul
              (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            rw [Real.sq_sqrt (by positivity)]
            apply le_of_eq; field_simp; ring
          · have hQ : ∀ z, (![x, y, z] : Fin 3 → ℝ) ∉ Q := fun z h => hy h.2
            simp_rw [Set.indicator_of_notMem (hQ _)]
            simp
        · have hQ : ∀ y z, (![x, y, z] : Fin 3 → ℝ) ∉ Q := fun y z h => hx h.1
          simp_rw [Set.indicator_of_notMem (hQ _ _)]
          simp
    _ = ∫⁻ x in Set.Icc (-R) R, ENNReal.ofReal (2 * Real.pi * 72 * Real.pi) *
          ENNReal.ofReal (1 / √(1 + x ^ 2)) := by
        rw [← lintegral_indicator measurableSet_Icc]
        congr 1; funext x
        by_cases hx : x ∈ Set.Icc (-R) R
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, lintegral_const_mul' _ _
            ENNReal.ofReal_ne_top, tbt_lintegral_inv_sq_add_sq (Real.sqrt_pos.mpr (by positivity)),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    _ = ENNReal.ofReal (2 * Real.pi * 72 * Real.pi) * ENNReal.ofReal (2 * Real.arsinh R) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, tbt_lintegral_Icc_inv_sqrt hR]
    _ ≤ ENNReal.ofReal (576 * Real.pi ^ 2 * Real.log (2 + R)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := tbt_arsinh_le_log hR
        have hpi := Real.pi_pos
        nlinarith [mul_pos hpi hpi]



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

theorem tbt_norm_le_sqrt (x : Fin 3 → ℝ) : ‖x‖ ≤ √(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

/-- `q₃ (∇u) ∈ L¹ (ℝ³)`. -/
theorem tbt_integrable_q3 : Integrable fun x => q3 (jac tbtWitness x) := by
  have hc : Continuous fun x => q3 (jac tbtWitness x) :=
    tbt_continuous_q3.comp (tbt_continuous_jac tbt_witness_contDiff)
  have hi : Integrable fun x : Fin 3 → ℝ => (1 + ‖x‖) ^ (-(4 : ℝ)) :=
    integrable_one_add_norm (by norm_num [Module.finrank_fin_fun])
  refine (hi.const_mul 16).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  refine (tbt_abs_q3_le x).trans ?_
  set S := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2
  have hS : 0 ≤ S := by positivity
  have hn := tbt_norm_le_sqrt x
  have hn0 := norm_nonneg x
  have hn2 : ‖x‖ ^ 2 ≤ S := by
    calc ‖x‖ ^ 2 ≤ √S ^ 2 := pow_le_pow_left₀ hn0 hn 2
      _ = S := Real.sq_sqrt hS
  have h1 : (1 + ‖x‖) ^ 4 ≤ 4 * (1 + S) ^ 2 := by
    have : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + S) := by nlinarith [sq_nonneg (1 - ‖x‖)]
    nlinarith [pow_le_pow_left₀ (by positivity) this 2]
  rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

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
`q₃ (∇u) = −|∂ζ|⁴ (1 − |ζ|²)⁶ < 0` (`tbt_q3_jac`, `F' = 1`). For the integrability and the
logarithmic bound we use `|∇u| ≲ |∂ζ| = 1 / (2 |s|)` as the paper does.

Departure from the paper (reason 2, the change of variables): the paper evaluates the integrals in
the coordinates `(ζ, τ)`, `dx dy dt = 4 |s|² (1 − |ζ|²)⁻² dA (ζ) dτ`; that change of variables needs
the inverse map and its Jacobian, which Lean does not have and which would be long to build. Instead
the same quantities are bounded in the coordinates `(x, y, t)`:
`|q₃ (∇u)| = (1 − |ζ|²)⁶ / (16 |s|⁴) ≤ 4 / (1 + |X|²)²` (from `σ ≥ 1`, `(1 + σ) (1 − |ζ|²) = 2` and
`σ² |s|² = σ⁴ + t²`; `tbt_abs_q3_le`), which is integrable on `ℝ³`; and
`|s|⁴ = (1 + (t − |w|)²) (1 + (t + |w|)²)`, so that `|∇u|⁴ ≲ |s|⁻⁴` integrates first in `t` (two
Cauchy kernels, `2π / (1 + |w|²)`), then over the square `[−R, R]²` (`∫ dy / (1 + x² + y²) =
π / √(1 + x²)`, `∫_{−R}^{R} dx / √(1 + x²) = 2 arsinh R`), giving
`∫_{B_R} |∇u|⁴ ≤ 576 π² log (2 + R)` (`tbt_log_bound`). -/
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
