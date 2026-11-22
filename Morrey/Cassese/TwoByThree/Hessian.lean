module

public import Morrey.Cassese.TwoByThree.Witness

/-!
# Corollary 5.4: the Hessian witness

The proof of Corollary 5.4 (TeX lines 2159–2191) seeks `u = B ∇φ` for the ansatz
`u = \overline{F (ζ)} + G (ζ)` of Proposition 5.2, with `F' (z) = 1 + z`, `G' (z) = z (1 + z)`:
`∇φ = Re Ψ (ζ)` with `Ψ' (z) = F' (z) (1 + z)⁻¹ (1 + z², i (1 − z²), 2 z) = (1 + z², i (1 − z²), 2 z)`,
`Ψ (z) = (z + z³/3, i (z − z³/3), z²)`. A potential is
`Φ = x Ψ₁ (ζ) + y Ψ₂ (ζ) + t Ψ₃ (ζ) + i ζ²` (its gradient is `Ψ (ζ)` because
`Σ x_j Ψ_j' (ζ) + 2 i ζ = w + w̄ ζ² + 2 (t + i) ζ = 0`), `φ = Re Φ` (`tbt5Pot`).

The matrix `tbtM z k` collects the entries of `∇ (\overline{F (ζ)} + G (ζ))` when `F' (ζ) ∂ζ = k`;
it lies in `𝓛₃`, `q₃ (tbtM z k) = −|k|⁴ (1 − |z|²)⁶` and `|tbtM z k|² ≤ 48 |k|²` for `|z| ≤ 1`.

Helpers are prefixed `tbt5_`.
-/

@[expose] public section

open MeasureTheory Complex
open scoped Matrix ENNReal ComplexConjugate

namespace Cassese

/-- The matrix `B = (1 0 1; 0 1 0)` of Corollary 5.4. -/
def hessB : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, 1; 0, 1, 0]

/-- The vector `c (z) = (1 + z², i (1 − z²), 2 z)`, so that `∇ζ = ∂ζ · c (ζ)`. -/
noncomputable def tbt5c (z : ℂ) : Fin 3 → ℂ := ![1 + z ^ 2, I * (1 - z ^ 2), 2 * z]

/-- `conj (k c_j) + z k c_j`: the `j`-th partial derivative of `\overline{F (ζ)} + G (ζ)` (with
`G' = z F'`) when `F' (ζ) ∂ζ = k`. -/
noncomputable def tbt5UD (z k : ℂ) (j : Fin 3) : ℂ := conj (k * tbt5c z j) + z * (k * tbt5c z j)

/-- The real `2 × 3` matrix with columns `tbt5UD z k j`. -/
noncomputable def tbtM (z k : ℂ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![(tbt5UD z k 0).re, (tbt5UD z k 1).re, (tbt5UD z k 2).re;
    (tbt5UD z k 0).im, (tbt5UD z k 1).im, (tbt5UD z k 2).im]

/-- The entries of `tbtM z k` as polynomials in `z = a + i b`, `k = c + i e`. -/
theorem tbt5_M_eq (z k : ℂ) :
    let a := z.re
    let b := z.im
    let c := k.re
    let e := k.im
    tbtM z k = !![a ^ 3 * c - 3 * a ^ 2 * b * e + a ^ 2 * c - 3 * a * b ^ 2 * c -
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
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp only [tbtM, tbt5UD, tbt5c, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, add_re, add_im,
    mul_re, mul_im, sub_re, sub_im, conj_re, conj_im, one_re, one_im, I_re, I_im, pow_two, re_ofNat,
    im_ofNat] <;>
  ring

theorem tbt5_M_mem_L3 (z k : ℂ) : tbtM z k ∈ L3 := by
  rw [mem_L3_iff, tbt5_M_eq]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons]
  constructor <;> ring

/-- `q₃ (tbtM z k) = −|k|⁴ (1 − |z|²)⁶`, by (24). -/
theorem tbt5_q3_M (z k : ℂ) : q3 (tbtM z k) = -(‖k‖ ^ 2) ^ 2 * (1 - ‖z‖ ^ 2) ^ 6 := by
  rw [equation24 _ (tbt5_M_mem_L3 z k), tbt5_M_eq]
  simp only [Complex.sq_norm, Complex.normSq_apply, Matrix.det_fin_two, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons]
  norm_num
  ring

theorem tbt5_frobSq_M (z k : ℂ) : frobSq (tbtM z k) = ∑ j, ‖tbt5UD z k j‖ ^ 2 := by
  simp only [frobSq, tbtM, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem tbt5_norm_c_le {z : ℂ} (hz : ‖z‖ ≤ 1) (j : Fin 3) : ‖tbt5c z j‖ ≤ 2 := by
  have hz0 := norm_nonneg z
  fin_cases j
  · show ‖1 + z ^ 2‖ ≤ 2
    calc ‖1 + z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one, norm_pow]; nlinarith
  · show ‖I * (1 - z ^ 2)‖ ≤ 2
    rw [norm_mul, norm_I, one_mul]
    calc ‖1 - z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one, norm_pow]; nlinarith
  · show ‖2 * z‖ ≤ 2
    rw [norm_mul, Complex.norm_two]; nlinarith

theorem tbt5_frobSq_M_le {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℂ) : frobSq (tbtM z k) ≤ 48 * ‖k‖ ^ 2 := by
  have hUD : ∀ j, ‖tbt5UD z k j‖ ≤ 4 * ‖k‖ := by
    intro j
    have hc := tbt5_norm_c_le hz j
    have hk := norm_nonneg k
    calc ‖tbt5UD z k j‖ ≤ ‖conj (k * tbt5c z j)‖ + ‖z * (k * tbt5c z j)‖ := norm_add_le _ _
      _ = ‖k‖ * ‖tbt5c z j‖ + ‖z‖ * (‖k‖ * ‖tbt5c z j‖) := by
        rw [Complex.norm_conj, norm_mul, norm_mul, norm_mul]
      _ ≤ 4 * ‖k‖ := by
        have h1 : ‖k‖ * ‖tbt5c z j‖ ≤ ‖k‖ * 2 := mul_le_mul_of_nonneg_left hc hk
        have h2 : ‖z‖ * (‖k‖ * ‖tbt5c z j‖) ≤ 1 * (‖k‖ * 2) :=
          mul_le_mul hz h1 (by positivity) zero_le_one
        linarith
  rw [tbt5_frobSq_M, Fin.sum_univ_three]
  have := fun j => pow_le_pow_left₀ (norm_nonneg _) (hUD j) 2
  nlinarith [this 0, this 1, this 2]

/-- The witness of Proposition 5.2 in this notation: `∇u = tbtM ζ ∂ζ` (`F (z) = z`). -/
theorem tbt5_jac_witness (X : Fin 3 → ℝ) : jac tbtWitness X = tbtM (tbtZeta X) (tbtK X) := by
  rw [tbt_jac_eq, tbt5_M_eq]

/-- `Ψ (z) = (z + z³/3, i (z − z³/3), z²)`, with `Ψ' = c`. -/
noncomputable def tbt5Psi (z : ℂ) : Fin 3 → ℂ := ![z + z ^ 3 / 3, I * (z - z ^ 3 / 3), z ^ 2]

/-- The complex potential `Φ = x Ψ₁ (ζ) + y Ψ₂ (ζ) + t Ψ₃ (ζ) + i ζ²`. -/
noncomputable def tbt5Phi (X : Fin 3 → ℝ) : ℂ :=
  (X 0 : ℂ) * tbt5Psi (tbtZeta X) 0 + (X 1 : ℂ) * tbt5Psi (tbtZeta X) 1 +
    (X 2 : ℂ) * tbt5Psi (tbtZeta X) 2 + I * tbtZeta X ^ 2

/-- The potential `φ = Re Φ` of Corollary 5.4. -/
noncomputable def tbt5Pot (X : Fin 3 → ℝ) : ℝ := (tbt5Phi X).re

theorem tbt5_Phi_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n tbt5Phi := by
  have hζ : ContDiff ℝ n tbtZeta := tbt_Zeta_contDiff
  have hX : ∀ i : Fin 3, ContDiff ℝ n fun X : Fin 3 → ℝ => (X i : ℂ) := fun i =>
    ofRealCLM.contDiff.comp (contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) i)
  unfold tbt5Phi tbt5Psi
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have h0 := hX 0; have h1 := hX 1; have h2 := hX 2
  fun_prop

theorem tbt5_Pot_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n tbt5Pot :=
  reCLM.contDiff.comp tbt5_Phi_contDiff

/-- The chain rule for `Ψ_j (ζ)` along a line. -/
theorem tbt5_hasDerivAt_Psi {f : ℝ → ℂ} {f' : ℂ} (hf : HasDerivAt f f' 0) (j : Fin 3) :
    HasDerivAt (fun τ => tbt5Psi (f τ) j) (tbt5c (f 0) j * f') 0 := by
  match j with
  | 0 =>
    have := hf.fun_add ((hf.fun_pow 3).div_const 3)
    convert this using 1
    · funext τ; simp [tbt5Psi]
    · simp [tbt5c]; ring
  | 1 =>
    have := (hf.fun_sub ((hf.fun_pow 3).div_const 3)).const_mul I
    convert this using 1
    · funext τ; simp [tbt5Psi]
    · simp [tbt5c]; ring
  | 2 =>
    have := hf.fun_pow 2
    convert this using 1
    · funext τ; simp [tbt5Psi]
    · simp [tbt5c]

/-- `∇Φ = Ψ (ζ)`: the first-order terms cancel by the defining equation of `ζ`,
`Σ_i x_i Ψ_i' (ζ) + 2 i ζ = w + w̄ ζ² + 2 (t + i) ζ = 0`. -/
theorem tbt5_fderiv_Phi (X : Fin 3 → ℝ) (j : Fin 3) :
    fderiv ℝ tbt5Phi X (Pi.single j 1) = tbt5Psi (tbtZeta X) j := by
  have hζ : DifferentiableAt ℝ tbtZeta X :=
    (tbt_Zeta_contDiff (n := 1)).differentiable one_ne_zero X
  have hΦ : DifferentiableAt ℝ tbt5Phi X :=
    (tbt5_Phi_contDiff (n := 1)).differentiable one_ne_zero X
  have h1 := tbt_hasDerivAt_comp_line hΦ (Pi.single j 1)
  have hf := tbt_hasDerivAt_comp_line hζ (Pi.single j 1)
  have hc : ∀ i : Fin 3, HasDerivAt
      (fun τ : ℝ => (((X + τ • (Pi.single j 1 : Fin 3 → ℝ) : Fin 3 → ℝ) i : ℝ) : ℂ))
      (((Pi.single j 1 : Fin 3 → ℝ) i : ℝ) : ℂ) 0 := by
    intro i
    have := (((hasDerivAt_id (0 : ℝ)).mul_const ((Pi.single j 1 : Fin 3 → ℝ) i)).const_add
      (X i)).ofReal_comp
    simpa [mul_comm] using this
  have hP := fun i => tbt5_hasDerivAt_Psi hf i
  have h2 := ((((hc 0).fun_mul (hP 0)).fun_add ((hc 1).fun_mul (hP 1))).fun_add
    ((hc 2).fun_mul (hP 2))).fun_add ((hf.fun_pow 2).const_mul I)
  rw [h1.unique h2]
  simp only [zero_smul, add_zero]
  have hE := tbt_Zeta_eq X
  have hw : conj (tbtW X) = (X 0 : ℂ) - (X 1 : ℂ) * I := by
    simp [tbtW, map_add, map_mul, conj_ofReal]; ring
  rw [hw] at hE
  simp only [tbtW] at hE
  match j with
  | 0 =>
    simp [tbt5c, tbt5Psi]
    linear_combination (fderiv ℝ tbtZeta X (Pi.single 0 1)) * hE
  | 1 =>
    simp [tbt5c, tbt5Psi]
    linear_combination (fderiv ℝ tbtZeta X (Pi.single 1 1)) * hE
  | 2 =>
    simp [tbt5c, tbt5Psi]
    linear_combination (fderiv ℝ tbtZeta X (Pi.single 2 1)) * hE

/-- `∇φ = Re Ψ (ζ)`. -/
theorem tbt5_fderiv_Pot (X : Fin 3 → ℝ) (j : Fin 3) :
    fderiv ℝ tbt5Pot X (Pi.single j 1) = (tbt5Psi (tbtZeta X) j).re := by
  have hΦ : DifferentiableAt ℝ tbt5Phi X :=
    (tbt5_Phi_contDiff (n := 1)).differentiable one_ne_zero X
  have h : HasFDerivAt tbt5Pot (reCLM.comp (fderiv ℝ tbt5Phi X)) X :=
    reCLM.hasFDerivAt.comp X hΦ.hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply, tbt5_fderiv_Phi, reCLM_apply]

/-- `D²φ = Re (∂ζ c_i (ζ) c_j (ζ))`. -/
theorem tbt5_hessian_Pot (X : Fin 3 → ℝ) (i j : Fin 3) :
    hessian tbt5Pot X i j = (tbtK X * tbt5c (tbtZeta X) i * tbt5c (tbtZeta X) j).re := by
  have hζ : DifferentiableAt ℝ tbtZeta X :=
    (tbt_Zeta_contDiff (n := 1)).differentiable one_ne_zero X
  have he : (fun y => fderiv ℝ tbt5Pot y (Pi.single j 1)) =
      fun y => (tbt5Psi (tbtZeta y) j).re := funext fun y => tbt5_fderiv_Pot y j
  have hP : DifferentiableAt ℝ (fun y => tbt5Psi (tbtZeta y) j) X := by
    have hc : ContDiff ℝ 1 (fun y => tbt5Psi (tbtZeta y) j) := by
      have hζ' : ContDiff ℝ 1 tbtZeta := tbt_Zeta_contDiff
      match j with
      | 0 => simp only [tbt5Psi, Matrix.cons_val_zero]; fun_prop
      | 1 => simp [tbt5Psi]; fun_prop
      | 2 => simp [tbt5Psi]; fun_prop
    exact hc.differentiable one_ne_zero X
  have h1 := tbt_hasDerivAt_comp_line hP (Pi.single i 1)
  have h2 := tbt5_hasDerivAt_Psi (tbt_hasDerivAt_comp_line hζ (Pi.single i 1)) j
  have hfd : fderiv ℝ (fun y => tbt5Psi (tbtZeta y) j) X (Pi.single i 1) =
      tbt5c (tbtZeta X) j * tbtZetaD X i := by
    rw [h1.unique h2]; simp [tbtZetaD]
  have hre : HasFDerivAt (fun y => (tbt5Psi (tbtZeta y) j).re)
      (reCLM.comp (fderiv ℝ (fun y => tbt5Psi (tbtZeta y) j) X)) X :=
    reCLM.hasFDerivAt.comp X hP.hasFDerivAt
  simp only [hessian, Matrix.of_apply]
  rw [he, hre.fderiv, ContinuousLinearMap.comp_apply, hfd, reCLM_apply]
  obtain ⟨h0, h1', h2'⟩ := tbt_ZetaD_eq X
  congr 1
  match i with
  | 0 => rw [h0]; simp [tbt5c]; ring
  | 1 => rw [h1']; simp [tbt5c]; ring
  | 2 => rw [h2']; simp [tbt5c]; ring

/-- `B D²φ = ∇ (\overline{F (ζ)} + G (ζ))` with `F' (z) = 1 + z`, `G' = z F'`: the matrix
`tbtM ζ ((1 + ζ) ∂ζ)`. -/
theorem tbt5_hessB_hessian (X : Fin 3 → ℝ) :
    hessB * hessian tbt5Pot X = tbtM (tbtZeta X) ((1 + tbtZeta X) * tbtK X) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, tbt5_hessian_Pot]
  fin_cases i <;> fin_cases j <;>
  simp [hessB, tbtM, tbt5UD, tbt5c, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The bulk field of Corollary 5.4, `V = B D²φ`. -/
theorem tbt5_V_mem_L3 (X : Fin 3 → ℝ) : hessB * hessian tbt5Pot X ∈ L3 := by
  rw [tbt5_hessB_hessian]; exact tbt5_M_mem_L3 _ _

/-- `q₃ (B D²φ) = −|F' (ζ)|⁴ |∂ζ|⁴ (1 − |ζ|²)⁶ < 0` (`F' (ζ) = 1 + ζ ≠ 0` in the disc). -/
theorem tbt5_q3_V_neg (X : Fin 3 → ℝ) : q3 (hessB * hessian tbt5Pot X) < 0 := by
  rw [tbt5_hessB_hessian, tbt5_q3_M]
  have hz := tbt_norm_Zeta_lt_one X
  have h1 : 1 + tbtZeta X ≠ 0 := by
    intro h
    have : tbtZeta X = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hz
    exact lt_irrefl _ hz
  have hK : tbtK X ≠ 0 := by
    rw [tbtK]; exact div_ne_zero I_ne_zero (mul_ne_zero two_ne_zero (tbt_S_ne_zero X))
  have hk : 0 < ‖(1 + tbtZeta X) * tbtK X‖ := norm_pos_iff.mpr (mul_ne_zero h1 hK)
  have hρ : 0 < 1 - ‖tbtZeta X‖ ^ 2 := by nlinarith [norm_nonneg (tbtZeta X)]
  have : 0 < (‖(1 + tbtZeta X) * tbtK X‖ ^ 2) ^ 2 * (1 - ‖tbtZeta X‖ ^ 2) ^ 6 := by positivity
  linarith

/-- `|B D²φ| ≲ |s|⁻¹`, the bound `|∇u| ≲ M |s|⁻¹` of the proof of Proposition 5.2 with
`M = ‖F'‖_∞ ≤ 2` (`F' (z) = 1 + z`): `|B D²φ|⁴ ≤ 16 · 144 / |s|⁴`. -/
theorem tbt5_frobSq_V_sq_le (X : Fin 3 → ℝ) :
    frobSq (hessB * hessian tbt5Pot X) ^ 2 ≤ 16 * (144 / ‖tbtS X‖ ^ 4) := by
  rw [tbt5_hessB_hessian]
  have hz := (tbt_norm_Zeta_lt_one X).le
  have h1 : ‖1 + tbtZeta X‖ ≤ 2 := by
    calc ‖1 + tbtZeta X‖ ≤ ‖(1 : ℂ)‖ + ‖tbtZeta X‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hF := tbt5_frobSq_M_le hz ((1 + tbtZeta X) * tbtK X)
  have hF0 := tbt_frobSq_nonneg (tbtM (tbtZeta X) ((1 + tbtZeta X) * tbtK X))
  have hk2 : ‖(1 + tbtZeta X) * tbtK X‖ ^ 2 ≤ 4 * ‖tbtK X‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    have : ‖1 + tbtZeta X‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (1 + tbtZeta X)]
    nlinarith [sq_nonneg ‖tbtK X‖]
  have hSpos : 0 < ‖tbtS X‖ := norm_pos_iff.mpr (tbt_S_ne_zero X)
  have hK := tbt_norm_K X
  have hmain : frobSq (tbtM (tbtZeta X) ((1 + tbtZeta X) * tbtK X)) ^ 2 ≤
      (192 * ‖tbtK X‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ hF0 (by linarith) 2
  have he : (192 * ‖tbtK X‖ ^ 2) ^ 2 = 16 * (144 / ‖tbtS X‖ ^ 4) := by
    rw [hK]; field_simp; ring
  linarith

theorem tbt5_continuous_V : Continuous fun X => hessB * hessian tbt5Pot X := by
  have hc : Continuous fun X => hessian tbt5Pot X := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have h1 : ContDiff ℝ 1 fun y => fderiv ℝ tbt5Pot y (Pi.single j 1) :=
      ((tbt5_Pot_contDiff (n := 2)).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact (h1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact continuous_const.matrix_mul hc

/-- `∫_{B_R} |B D²φ|⁴ ≲ log (2 + R)`: the energy estimate of the proof of Proposition 5.2, in the
coordinates `(ζ, τ)` (`tbt_log_bound_of_le`, Morrey/Cassese/TwoByThree/Witness.lean). -/
theorem tbt5_V_log_bound {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}, frobSq (hessB * hessian tbt5Pot x) ^ 2 ≤
      16 * (576 * Real.pi ^ 2 * Real.log (2 + R)) :=
  tbt_log_bound_of_le ((tbt_continuous_frobSq.comp tbt5_continuous_V).pow 2)
    (fun x => sq_nonneg _)
    (by norm_num) tbt5_frobSq_V_sq_le hR

/-- `|∂_j φ| ≤ 4/3`: `∇φ = Re Ψ (ζ)` is bounded. -/
theorem tbt5_abs_fderiv_Pot_le (X : Fin 3 → ℝ) (j : Fin 3) :
    |fderiv ℝ tbt5Pot X (Pi.single j 1)| ≤ 4 / 3 := by
  rw [tbt5_fderiv_Pot]
  refine (Complex.abs_re_le_norm _).trans ?_
  have hz := (tbt_norm_Zeta_lt_one X).le
  have hz0 := norm_nonneg (tbtZeta X)
  have h3 : ‖tbtZeta X‖ ^ 3 ≤ 1 := pow_le_one₀ hz0 hz
  have h2 : ‖tbtZeta X‖ ^ 2 ≤ 1 := pow_le_one₀ hz0 hz
  match j with
  | 0 =>
    simp only [tbt5Psi, Matrix.cons_val_zero]
    calc ‖tbtZeta X + tbtZeta X ^ 3 / 3‖ ≤ ‖tbtZeta X‖ + ‖tbtZeta X ^ 3 / 3‖ := norm_add_le _ _
      _ ≤ 4 / 3 := by
        rw [norm_div, norm_pow]; simp only [RCLike.norm_ofNat]; linarith
  | 1 =>
    show ‖I * (tbtZeta X - tbtZeta X ^ 3 / 3)‖ ≤ 4 / 3
    rw [norm_mul, norm_I, one_mul]
    calc ‖tbtZeta X - tbtZeta X ^ 3 / 3‖ ≤ ‖tbtZeta X‖ + ‖tbtZeta X ^ 3 / 3‖ := norm_sub_le _ _
      _ ≤ 4 / 3 := by
        rw [norm_div, norm_pow]; simp only [RCLike.norm_ofNat]; linarith
  | 2 =>
    show ‖tbtZeta X ^ 2‖ ≤ 4 / 3
    rw [norm_pow]; linarith

/-- `|φ (X)| ≤ (4/3) (|x| + |y| + |t|) + 1`: linear growth. -/
theorem tbt5_abs_Pot_le (X : Fin 3 → ℝ) :
    |tbt5Pot X| ≤ 4 / 3 * (|X 0| + |X 1| + |X 2|) + 1 := by
  have hz := (tbt_norm_Zeta_lt_one X).le
  have hz0 := norm_nonneg (tbtZeta X)
  have hP : ∀ j, ‖tbt5Psi (tbtZeta X) j‖ ≤ 4 / 3 := by
    have h3 : ‖tbtZeta X‖ ^ 3 ≤ 1 := pow_le_one₀ hz0 hz
    have h2 : ‖tbtZeta X‖ ^ 2 ≤ 1 := pow_le_one₀ hz0 hz
    intro j
    match j with
    | 0 =>
      simp only [tbt5Psi, Matrix.cons_val_zero]
      calc ‖tbtZeta X + tbtZeta X ^ 3 / 3‖ ≤ ‖tbtZeta X‖ + ‖tbtZeta X ^ 3 / 3‖ :=
            norm_add_le _ _
        _ ≤ 4 / 3 := by rw [norm_div, norm_pow]; simp only [RCLike.norm_ofNat]; linarith
    | 1 =>
      show ‖I * (tbtZeta X - tbtZeta X ^ 3 / 3)‖ ≤ 4 / 3
      rw [norm_mul, norm_I, one_mul]
      calc ‖tbtZeta X - tbtZeta X ^ 3 / 3‖ ≤ ‖tbtZeta X‖ + ‖tbtZeta X ^ 3 / 3‖ :=
            norm_sub_le _ _
        _ ≤ 4 / 3 := by rw [norm_div, norm_pow]; simp only [RCLike.norm_ofNat]; linarith
    | 2 =>
      show ‖tbtZeta X ^ 2‖ ≤ 4 / 3
      rw [norm_pow]; linarith
  unfold tbt5Pot tbt5Phi
  refine (Complex.abs_re_le_norm _).trans ?_
  have h4 : ‖I * tbtZeta X ^ 2‖ ≤ 1 := by
    rw [norm_mul, norm_I, one_mul, norm_pow]; exact pow_le_one₀ hz0 hz
  have ht : ∀ j : Fin 3, ‖(X j : ℂ) * tbt5Psi (tbtZeta X) j‖ ≤ 4 / 3 * |X j| := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hP j) (abs_nonneg _)
  calc _ ≤ ‖(X 0 : ℂ) * tbt5Psi (tbtZeta X) 0‖ + ‖(X 1 : ℂ) * tbt5Psi (tbtZeta X) 1‖ +
        ‖(X 2 : ℂ) * tbt5Psi (tbtZeta X) 2‖ + ‖I * tbtZeta X ^ 2‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by linarith [ht 0, ht 1, ht 2]

/-- The partial derivative `∂_j f`. -/
noncomputable def tbt5D (f : (Fin 3 → ℝ) → ℝ) (j : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ f y (Pi.single j 1)

theorem tbt5_D_contDiff {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 3) :
    ContDiff ℝ 1 (tbt5D f j) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem tbt5_D_mul {a b : (Fin 3 → ℝ) → ℝ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (j : Fin 3) (y : Fin 3 → ℝ) :
    tbt5D (fun x => a x * b x) j y = a y * tbt5D b j y + b y * tbt5D a j y := by
  simp only [tbt5D]
  rw [fderiv_fun_mul (ha y) (hb y)]
  simp [smul_eq_mul]

theorem tbt5_D_add {u v : (Fin 3 → ℝ) → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (j : Fin 3) (y : Fin 3 → ℝ) :
    tbt5D (fun x => u x + v x) j y = tbt5D u j y + tbt5D v j y := by
  simp only [tbt5D]
  rw [fderiv_fun_add (hu y) (hv y)]
  rfl

theorem tbt5_D_const_mul {u : (Fin 3 → ℝ) → ℝ} (hu : Differentiable ℝ u) (c : ℝ)
    (j : Fin 3) (y : Fin 3 → ℝ) :
    tbt5D (fun x => c * u x) j y = c * tbt5D u j y := by
  simp only [tbt5D]
  rw [fderiv_const_mul (hu y)]
  rfl

/-- The Hessian is `∂_i ∂_j`. -/
theorem tbt5_hessian_eq (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) (i j : Fin 3) :
    hessian f x i j = tbt5D (tbt5D f j) i x := rfl

/-- Leibniz's rule for the Hessian:
`∂_i ∂_j (a b) = a ∂_i ∂_j b + ∂_i a ∂_j b + ∂_j a ∂_i b + b ∂_i ∂_j a`. -/
theorem tbt5_hessian_mul {a b : (Fin 3 → ℝ) → ℝ} (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (x : Fin 3 → ℝ) (i j : Fin 3) :
    hessian (fun y => a y * b y) x i j =
      a x * hessian b x i j + tbt5D a i x * tbt5D b j x + tbt5D a j x * tbt5D b i x +
        b x * hessian a x i j := by
  have ha1 : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hb1 : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hDa : Differentiable ℝ (tbt5D a j) := (tbt5_D_contDiff ha j).differentiable (by norm_num)
  have hDb : Differentiable ℝ (tbt5D b j) := (tbt5_D_contDiff hb j).differentiable (by norm_num)
  rw [tbt5_hessian_eq]
  have : tbt5D (fun y => a y * b y) j = fun y => a y * tbt5D b j y + b y * tbt5D a j y :=
    funext fun y => tbt5_D_mul ha1 hb1 j y
  rw [this, tbt5_D_add (u := fun y => a y * tbt5D b j y) (v := fun y => b y * tbt5D a j y)
    (ha1.fun_mul hDb) (hb1.fun_mul hDa), tbt5_D_mul ha1 hDb, tbt5_D_mul hb1 hDa,
    tbt5_hessian_eq, tbt5_hessian_eq]
  ring

/-- Scaling: `∂_j (f (c • ·)) (x) = c ∂_j f (c x)`. -/
theorem tbt5_D_comp_smul {f : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (j : Fin 3)
    (x : Fin 3 → ℝ) : tbt5D (fun y => f (c • y)) j x = c * tbt5D f j (c • x) := by
  simp only [tbt5D]
  have h : HasFDerivAt (fun y => f (c • y))
      ((fderiv ℝ f (c • x)).comp (c • ContinuousLinearMap.id ℝ _)) x :=
    (hf (c • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)
  rw [h.fderiv]
  simp

theorem tbt5_hessian_comp_smul {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ)
    (x : Fin 3 → ℝ) (i j : Fin 3) :
    hessian (fun y => f (c • y)) x i j = c ^ 2 * hessian f (c • x) i j := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hD : Differentiable ℝ (tbt5D f j) := (tbt5_D_contDiff hf j).differentiable (by norm_num)
  rw [tbt5_hessian_eq]
  have : tbt5D (fun y => f (c • y)) j = fun y => c * tbt5D f j (c • y) :=
    funext fun y => tbt5_D_comp_smul hf1 c j y
  have hDc : Differentiable ℝ fun y => tbt5D f j (c • y) :=
    hD.comp (differentiable_id.const_smul c)
  rw [this, tbt5_D_const_mul (u := fun y => tbt5D f j (c • y)) hDc,
    tbt5_D_comp_smul hD, tbt5_hessian_eq]
  ring

/-- Translation: `∂_j (f (· − c)) (x) = ∂_j f (x − c)`. -/
theorem tbt5_D_comp_sub {f : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f) (c : Fin 3 → ℝ)
    (j : Fin 3) (x : Fin 3 → ℝ) : tbt5D (fun y => f (y - c)) j x = tbt5D f j (x - c) := by
  simp only [tbt5D]
  have h := (hf (x - c)).hasFDerivAt.comp x (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x) c)
  rw [show (fun y => f (y - c)) = f ∘ fun y => y - c from rfl, h.fderiv]
  rfl

theorem tbt5_hessian_comp_sub {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (c : Fin 3 → ℝ)
    (x : Fin 3 → ℝ) (i j : Fin 3) :
    hessian (fun y => f (y - c)) x i j = hessian f (x - c) i j := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hD : Differentiable ℝ (tbt5D f j) := (tbt5_D_contDiff hf j).differentiable (by norm_num)
  rw [tbt5_hessian_eq]
  have : tbt5D (fun y => f (y - c)) j = fun y => tbt5D f j (y - c) :=
    funext fun y => tbt5_D_comp_sub hf1 c j y
  rw [this, tbt5_D_comp_sub hD, tbt5_hessian_eq]

/-- The rescaled potential `λ² f ((x − c)/λ)` has Hessian `D²f ((x − c)/λ)`. -/
theorem tbt5_hessian_rescale {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {l : ℝ} (hl : l ≠ 0)
    (c x : Fin 3 → ℝ) :
    hessian (fun y => l ^ 2 * f (l⁻¹ • (y - c))) x = hessian f (l⁻¹ • (x - c)) := by
  ext i j
  have hg : ContDiff ℝ 2 fun y => f (l⁻¹ • y) := hf.comp (contDiff_const_smul _)
  have h1 : hessian (fun y => l ^ 2 * f (l⁻¹ • (y - c))) x i j =
      l ^ 2 * hessian (fun y => f (l⁻¹ • (y - c))) x i j := by
    have hg' : ContDiff ℝ 2 fun y => f (l⁻¹ • (y - c)) :=
      hg.comp (contDiff_id.sub contDiff_const)
    rw [tbt5_hessian_eq, tbt5_hessian_eq]
    have hD : Differentiable ℝ (tbt5D (fun y => f (l⁻¹ • (y - c))) j) :=
      (tbt5_D_contDiff hg' j).differentiable (by norm_num)
    have : tbt5D (fun y => l ^ 2 * f (l⁻¹ • (y - c))) j =
        fun y => l ^ 2 * tbt5D (fun y => f (l⁻¹ • (y - c))) j y :=
      funext fun y => tbt5_D_const_mul (u := fun y => f (l⁻¹ • (y - c)))
        (hg'.differentiable (by norm_num)) _ j y
    rw [this, tbt5_D_const_mul hD]
  rw [h1, tbt5_hessian_comp_sub (f := fun y => f (l⁻¹ • y)) hg c x i j,
    tbt5_hessian_comp_smul hf]
  field_simp

/-- `A ↦ q (B A)` is rank-one convex when `q` is: `B` maps rank-one matrices to matrices of rank
at most one. -/
theorem tbt5_rankOneConvex_hessB {q : Matrix (Fin 2) (Fin 3) ℝ → ℝ} (hq : RankOneConvex q) :
    RankOneConvex fun A : Matrix (Fin 3) (Fin 3) ℝ => q (hessB * A) := by
  intro A A' hAA'
  have hlin : ∀ t : ℝ, hessB * (t • A + (1 - t) • A') = t • (hessB * A) + (1 - t) • (hessB * A') :=
    fun t => by rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
  have hr : (hessB * A - hessB * A').rank ≤ 1 := by
    rw [← Matrix.mul_sub]
    exact (Matrix.rank_mul_le_right _ _).trans hAA'.le
  rcases Nat.lt_or_ge (hessB * A - hessB * A').rank 1 with h0 | h1
  · have h0' : hessB * A - hessB * A' = 0 :=
      eq_zero_of_rank_eq_zero (by omega)
    have hAeq : hessB * A = hessB * A' := sub_eq_zero.mp h0'
    simp_rw [hlin, hAeq, ← add_smul, add_sub_cancel, one_smul]
    exact convexOn_const _ (convex_Icc 0 1)
  · simp_rw [hlin]
    exact hq _ _ (le_antisymm hr h1)

end Cassese
