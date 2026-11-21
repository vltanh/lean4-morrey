module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Burkholder's inequality and square function inequality for Hilbert-space-valued martingales

D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*,
Ann. Probab. 12 (1984); A. Osękowski, *Sharp martingale and semimartingale inequalities* (2012),
Theorems 3.5 and 8.6. Cassese (arXiv:2608.03488v3) quotes both as Theorem 2.3 (`cs-thm2.3`);
they are proved here by Burkholder's method, the source's standard argument.

## Main results

* `inequality` (Theorem 2.3 (1)): for martingales `X`, `Y` with values in a separable real Hilbert
  space `H`, started at `0`, with `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost surely, and `p > 1`,
  `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}` with `p* = max (p, p / (p − 1))`. The proof does not use
  the separability of `H`: `inequality_of_subordinate` is the same statement without it.
* `squareFunction` (Theorem 2.3 (2)): `‖𝒮_n X‖_{L^p} ≤ (p* − 1) ‖X_n‖_{L^p}` and
  `‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`, `𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`
  (`squareFunction_of_martingale` without separability).
* `burkholderU`: Burkholder's function
  `U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}`, written as a function of
  `s = |x|`, `r = |y|`; here `x` is the position of the subordinate martingale `X` and `y` that of
  the dominating one `Y`. `burkholderU_ge`: `U ≥ V`, `V (x, y) = |x|^p − (p* − 1)^p |y|^p`.

## The proof

1. `U ≥ V` (`burkholderU_ge`): for `r > 0`, `s ↦ U (s, r) − V (s, r)` vanishes at `s = (p* − 1) r`
   and its derivative is `≤ 0` before and `≥ 0` after that point (`sign_A`, `sign_B`); at `r = 0`,
   `U − V = (α − 1) s^p ≥ 0`.
2. The concavity property: for `|h| ≤ |k|`,
   `U (x + h, y + k) ≤ U (x, y) + ⟨U_x (x, y), h⟩ + ⟨U_y (x, y), k⟩` with
   `U_x (x, y) = (∂_s U (|x|, |y|) / |x|) x` (`0` if `x = 0`) and similarly `U_y`, because
   `t ↦ U (x + t h, y + t k)` is concave. For `p ≥ 2`, `U = α ψ (|x|, |y|)` with
   `ψ (s, r) = (s − (p − 1) r)(s + r)^{p−1}`; for `p ≤ 2`, `U = −α (p − 1)⁻¹ ψ (|y|, |x|)`. Along
   a curve, `(ψ (S, R))'' = p (S + R)^{p−3} (−(p − 1)(p − 2) R (S' + R')² − (p − 2)(S + R)² S'' −
   (p − 1)(S + R)(K − H))`, `H = S'² + S S''`, `K = R'² + R R''` (`psi_hasDerivAt_two`), which is
   `≤ 0` if `p ≥ 2`, `H ≤ K` and `≥ 0` if `p ≤ 2`, `K ≤ H` (`psi_line`); along a line,
   `H = |h|²`, `K = |k|²` (`psi_zigzag`).
3. `E U (X_{k+1}, Y_{k+1}) ≤ E U (X_k, Y_k)` (`method_step`): integrate the concavity property at
   `(X_k, Y_k)` with increments `(dX_{k+1}, dY_{k+1})`; the linear terms
   `E ⟨U_x (X_k, Y_k), dX_{k+1}⟩` vanish by the pull-out property of `E [· | ℱ_k]`
   (`integral_inner_increment`). Hence `E V (X_n, Y_n) ≤ E U (X_n, Y_n) ≤ U (0, 0) = 0`
   (`method`, `integral_burkholderU_nonpos`).
4. Integrability: if `‖Y_n‖_p = ∞` there is nothing to prove; otherwise `Y_k = E [Y_n | ℱ_k]` and
   `X_k = Σ_{j < k} dX_{j+1}` are in `L^p` for `k ≤ n`, and every term in step 3 is dominated by
   `C (|X_k| + |Y_k| + |dX_{k+1}| + |dY_{k+1}|)^p`.
5. The square function inequality, by the standard derivation from (1) (the `ℓ²(H)`-valued
   martingale `Σ_k dX_k e_k` and `X` are differentially subordinate to each other): in `H^{n+1}`
   with the `ℓ²` norm, `Z_m = Σ_{k < n} (X_{(k+1) ∧ m} − X_{k ∧ m}) e_k` and
   `A_m = X_{n ∧ m} e_n` are martingales started at `0` with
   `‖dZ_m‖ = ‖dA_m‖ = 1_{m < n} ‖dX_{m+1}‖`, `‖Z_n‖ = 𝒮_n X` and `‖A_n‖ = ‖X_n‖`; apply (1) to
   `(Z, A)` and to `(A, Z)`.

Departures from the source's proof. The source is quoted from memory (its text was not available
offline); these are the points where the proof here may differ from it, all in the mechanics of a
step whose claim is the source's:
* the non-smooth points of `t ↦ U (x + t h, y + t k)` (where `x + t h = 0` or `y + t k = 0`): the
  norms `|z|` are replaced by `√(|z|² + ε²)`, for which the second derivative has the required
  sign everywhere, and `ε → 0` in the tangent inequality (`psi_zigzag_eps`, `psi_zigzag`). Reason:
  gluing concave pieces at the kinks through the one-sided derivatives would need a lemma that
  Mathlib does not have (reason 2 of the skill's list); the smoothing avoids it;
* the square function: the finite-dimensional `H^{n+1}` replaces `ℓ²(H)` (`n` is fixed), the same
  argument.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal InnerProductSpace RealInnerProductSpace

namespace External.Burkholder

/-! ### The function `ψ (s, r) = (s − (p − 1) r) (s + r)^{p−1}` and its derivatives -/

/-- `ψ (s, r) = (s − (p − 1) r) (s + r)^{p−1}`; Burkholder's function is `α ψ (|x|, |y|)` for
`p ≥ 2` and `−α (p − 1)⁻¹ ψ (|y|, |x|)` for `p ≤ 2`. -/
private noncomputable def psi (p s r : ℝ) : ℝ := (s - (p - 1) * r) * (s + r) ^ (p - 1)

/-- `∂ψ/∂s = p (s + r)^{p−2} (s − (p − 2) r)`. -/
private noncomputable def psiS (p s r : ℝ) : ℝ := p * (s + r) ^ (p - 2) * (s - (p - 2) * r)

/-- `∂ψ/∂r = −p (p − 1) r (s + r)^{p−2}`. -/
private noncomputable def psiR (p s r : ℝ) : ℝ := -(p * (p - 1)) * r * (s + r) ^ (p - 2)

private theorem psi_hasDerivAt {p : ℝ} {S R : ℝ → ℝ} {S1 R1 t : ℝ}
    (hS : HasDerivAt S S1 t) (hR : HasDerivAt R R1 t) (hpos : 0 < S t + R t) :
    HasDerivAt (fun u => psi p (S u) (R u))
      (psiS p (S t) (R t) * S1 + psiR p (S t) (R t) * R1) t := by
  have h := (hS.sub (hR.const_mul (p - 1))).mul
    ((hS.add hR).rpow_const (p := p - 1) (Or.inl hpos.ne'))
  have e : (S t + R t) ^ (p - 1) = (S t + R t) ^ (p - 2) * (S t + R t) := by
    rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hpos.ne']
  have e2 : p - 1 - 1 = p - 2 := by ring
  unfold psi psiS psiR
  convert h using 1
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [e2, e]; ring

/-- The second derivative of `ψ` along a curve `(S, R)`:
`p (S + R)^{p−3} (−(p − 1)(p − 2) R (S' + R')² − (p − 2)(S + R)² S'' − (p − 1)(S + R)(K − H))`
with `H = S'² + S S''`, `K = R'² + R R''`. -/
private theorem psi_hasDerivAt_two {p : ℝ} {S R S1 R1 : ℝ → ℝ} {S2 R2 t : ℝ}
    (hS : HasDerivAt S (S1 t) t) (hR : HasDerivAt R (R1 t) t)
    (hS1 : HasDerivAt S1 S2 t) (hR1 : HasDerivAt R1 R2 t) (hpos : 0 < S t + R t) :
    HasDerivAt (fun u => psiS p (S u) (R u) * S1 u + psiR p (S u) (R u) * R1 u)
      (p * (S t + R t) ^ (p - 3) * (-(p - 1) * (p - 2) * R t * (S1 t + R1 t) ^ 2
        - (p - 2) * (S t + R t) ^ 2 * S2
        - (p - 1) * (S t + R t) * ((R1 t ^ 2 + R t * R2) - (S1 t ^ 2 + S t * S2)))) t := by
  have hP := (hS.add hR).rpow_const (p := p - 2) (Or.inl hpos.ne')
  have h1 := ((hP.const_mul p).mul (hS.sub (hR.const_mul (p - 2)))).mul hS1
  have h2 := (((hR.const_mul (-(p * (p - 1)))).mul hP)).mul hR1
  have h := h1.add h2
  have e : (S t + R t) ^ (p - 2) = (S t + R t) ^ (p - 3) * (S t + R t) := by
    rw [show p - 2 = p - 3 + 1 by ring, Real.rpow_add_one hpos.ne']
  have e2 : p - 2 - 1 = p - 3 := by ring
  unfold psiS psiR
  convert h using 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  rw [e2, e]; ring

/-- Along a curve `(S, R)` with `S, R > 0`, `S'' ≥ 0`: if `p ≥ 2` and `S'² + S S'' ≤ R'² + R R''`,
then `t ↦ ψ (S t, R t)` is concave, so it lies below its tangent at `0`; if `p ≤ 2` and the
reverse inequality holds, it is convex and lies above its tangent. -/
private theorem psi_line {p : ℝ} (hp : 1 < p) {S R S1 R1 S2 R2 : ℝ → ℝ}
    (hSpos : ∀ t, 0 < S t) (hRpos : ∀ t, 0 < R t)
    (dS : ∀ t, HasDerivAt S (S1 t) t) (dR : ∀ t, HasDerivAt R (R1 t) t)
    (dS1 : ∀ t, HasDerivAt S1 (S2 t) t) (dR1 : ∀ t, HasDerivAt R1 (R2 t) t)
    (hS2 : ∀ t, 0 ≤ S2 t) :
    ((2 ≤ p ∧ ∀ t, S1 t ^ 2 + S t * S2 t ≤ R1 t ^ 2 + R t * R2 t) →
      psi p (S 1) (R 1) ≤
        psi p (S 0) (R 0) + (psiS p (S 0) (R 0) * S1 0 + psiR p (S 0) (R 0) * R1 0)) ∧
    ((p ≤ 2 ∧ ∀ t, R1 t ^ 2 + R t * R2 t ≤ S1 t ^ 2 + S t * S2 t) →
      psi p (S 0) (R 0) + (psiS p (S 0) (R 0) * S1 0 + psiR p (S 0) (R 0) * R1 0) ≤
        psi p (S 1) (R 1)) := by
  set G1 : ℝ → ℝ := fun u => psiS p (S u) (R u) * S1 u + psiR p (S u) (R u) * R1 u with hG1
  set G2 : ℝ → ℝ := fun t => p * (S t + R t) ^ (p - 3) * (-(p - 1) * (p - 2) * R t *
      (S1 t + R1 t) ^ 2 - (p - 2) * (S t + R t) ^ 2 * S2 t
        - (p - 1) * (S t + R t) * ((R1 t ^ 2 + R t * R2 t) - (S1 t ^ 2 + S t * S2 t))) with hG2
  have hpos : ∀ t, 0 < S t + R t := fun t => add_pos (hSpos t) (hRpos t)
  have dG : ∀ t, HasDerivAt (fun u => psi p (S u) (R u)) (G1 t) t :=
    fun t => psi_hasDerivAt (dS t) (dR t) (hpos t)
  have dG1 : ∀ t, HasDerivAt G1 (G2 t) t :=
    fun t => psi_hasDerivAt_two (dS t) (dR t) (dS1 t) (dR1 t) (hpos t)
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun u => psi p (S u) (R u)) G1
    zero_lt_one (fun t _ => (dG t).continuousAt.continuousWithinAt) (fun t _ => dG t)
  simp only [sub_zero, div_one] at hceq
  have hp1 : 0 ≤ p - 1 := by linarith
  have hpow : ∀ t, 0 ≤ p * (S t + R t) ^ (p - 3) :=
    fun t => mul_nonneg (by linarith) (Real.rpow_nonneg (hpos t).le _)
  refine ⟨fun ⟨hp2, hHK⟩ => ?_, fun ⟨hp2, hHK⟩ => ?_⟩
  · have hanti : Antitone G1 := antitone_of_hasDerivAt_nonpos dG1 fun t => by
      have h2 : 0 ≤ p - 2 := by linarith
      have hb : -(p - 1) * (p - 2) * R t * (S1 t + R1 t) ^ 2 - (p - 2) * (S t + R t) ^ 2 * S2 t
          - (p - 1) * (S t + R t) * ((R1 t ^ 2 + R t * R2 t) - (S1 t ^ 2 + S t * S2 t)) ≤ 0 := by
        have := mul_nonneg (mul_nonneg (mul_nonneg hp1 h2) (hRpos t).le) (sq_nonneg (S1 t + R1 t))
        have := mul_nonneg (mul_nonneg h2 (sq_nonneg (S t + R t))) (hS2 t)
        have := mul_nonneg (mul_nonneg hp1 (hpos t).le) (sub_nonneg.2 (hHK t))
        nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos (hpow t) hb
    have := hanti hc.1.le
    linarith
  · have hmono : Monotone G1 := monotone_of_hasDerivAt_nonneg dG1 fun t => by
      have h2 : 0 ≤ 2 - p := by linarith
      have hb : 0 ≤ -(p - 1) * (p - 2) * R t * (S1 t + R1 t) ^ 2
          - (p - 2) * (S t + R t) ^ 2 * S2 t
          - (p - 1) * (S t + R t) * ((R1 t ^ 2 + R t * R2 t) - (S1 t ^ 2 + S t * S2 t)) := by
        have := mul_nonneg (mul_nonneg (mul_nonneg hp1 h2) (hRpos t).le) (sq_nonneg (S1 t + R1 t))
        have := mul_nonneg (mul_nonneg h2 (sq_nonneg (S t + R t))) (hS2 t)
        have := mul_nonneg (mul_nonneg hp1 (hpos t).le) (sub_nonneg.2 (hHK t))
        nlinarith
      exact mul_nonneg (hpow t) hb
    have := hmono hc.1.le
    linarith

/-! ### Smoothed norms along a line: `t ↦ √(a₀ + 2 a₁ t + a₂ t²)` -/

/-- `S (t) = √(a₀ + 2 a₁ t + a₂ t²)`; with `a₀ = |x|² + ε²`, `a₁ = ⟨x, h⟩`, `a₂ = |h|²` this is
`√(|x + t h|² + ε²)`. -/
private noncomputable def qS (a₀ a₁ a₂ t : ℝ) : ℝ := √(a₀ + 2 * a₁ * t + a₂ * t ^ 2)

/-- `S' = (a₁ + a₂ t) / S`. -/
private noncomputable def qS1 (a₀ a₁ a₂ t : ℝ) : ℝ := (a₁ + a₂ * t) / qS a₀ a₁ a₂ t

/-- `S'' = (a₂ − S'²) / S`. -/
private noncomputable def qS2 (a₀ a₁ a₂ t : ℝ) : ℝ := (a₂ - qS1 a₀ a₁ a₂ t ^ 2) / qS a₀ a₁ a₂ t

private theorem q_facts {a₀ a₁ a₂ : ℝ} (hpos : ∀ t, 0 < a₀ + 2 * a₁ * t + a₂ * t ^ 2)
    (hcs : a₁ ^ 2 ≤ a₀ * a₂) :
    (∀ t, 0 < qS a₀ a₁ a₂ t) ∧ (∀ t, HasDerivAt (qS a₀ a₁ a₂) (qS1 a₀ a₁ a₂ t) t) ∧
    (∀ t, HasDerivAt (qS1 a₀ a₁ a₂) (qS2 a₀ a₁ a₂ t) t) ∧ (∀ t, 0 ≤ qS2 a₀ a₁ a₂ t) ∧
    (∀ t, qS1 a₀ a₁ a₂ t ^ 2 + qS a₀ a₁ a₂ t * qS2 a₀ a₁ a₂ t = a₂) := by
  have hSpos : ∀ t, 0 < qS a₀ a₁ a₂ t := fun t => Real.sqrt_pos.2 (hpos t)
  have hSsq : ∀ t, qS a₀ a₁ a₂ t ^ 2 = a₀ + 2 * a₁ * t + a₂ * t ^ 2 :=
    fun t => Real.sq_sqrt (hpos t).le
  have dS : ∀ t, HasDerivAt (qS a₀ a₁ a₂) (qS1 a₀ a₁ a₂ t) t := by
    intro t
    have hσ := ((((hasDerivAt_id' (x := t)).const_mul (2 * a₁)).const_add a₀).add
      ((hasDerivAt_pow 2 t).const_mul a₂)).sqrt (hpos t).ne'
    convert hσ using 1
    · funext u; simp only [qS, Pi.add_apply]
    have := (hSpos t).ne'
    change (a₁ + a₂ * t) / qS a₀ a₁ a₂ t = (2 * a₁ * 1 + a₂ * (((2 : ℕ) : ℝ) * t ^ (2 - 1))) /
      (2 * qS a₀ a₁ a₂ t)
    norm_num
    field_simp
  have dS1 : ∀ t, HasDerivAt (qS1 a₀ a₁ a₂) (qS2 a₀ a₁ a₂ t) t := by
    intro t
    have h := (((hasDerivAt_id' (x := t)).const_mul a₂).const_add a₁).fun_div (dS t)
      (hSpos t).ne'
    convert h using 1
    · funext u; rfl
    have := (hSpos t).ne'
    unfold qS2 qS1
    field_simp
  have hS1le : ∀ t, qS1 a₀ a₁ a₂ t ^ 2 ≤ a₂ := by
    intro t
    unfold qS1
    rw [div_pow, hSsq, div_le_iff₀ (hpos t)]
    nlinarith
  refine ⟨hSpos, dS, dS1, fun t => div_nonneg (sub_nonneg.2 (hS1le t)) (hSpos t).le, fun t => ?_⟩
  unfold qS2
  have := (hSpos t).ne'
  field_simp
  ring

private theorem qS_zero (a₀ a₁ a₂ : ℝ) : qS a₀ a₁ a₂ 0 = √a₀ := by simp [qS]

private theorem qS1_zero (a₀ a₁ a₂ : ℝ) : qS1 a₀ a₁ a₂ 0 = a₁ / √a₀ := by simp [qS1, qS]

private theorem qS_one (a₀ a₁ a₂ : ℝ) : qS a₀ a₁ a₂ 1 = √(a₀ + 2 * a₁ + a₂) := by simp [qS]

/-! ### The concavity property of `ψ` along lines in a Hilbert space -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem quad_pos (x h : H) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 < ‖x‖ ^ 2 + ε ^ 2 + 2 * ⟪x, h⟫ * t + ‖h‖ ^ 2 * t ^ 2 := by
  have e := norm_add_sq_real x (t • h)
  rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at e
  have := sq_nonneg ‖x + t • h‖
  have := pow_pos hε 2
  nlinarith

private theorem inner_sq_le (x h : H) {ε : ℝ} :
    ⟪x, h⟫ ^ 2 ≤ (‖x‖ ^ 2 + ε ^ 2) * ‖h‖ ^ 2 := by
  have h1 := abs_real_inner_le_norm x h
  have h2 : ⟪x, h⟫ ^ 2 ≤ (‖x‖ * ‖h‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [sq_nonneg ε, sq_nonneg ‖h‖]

/-- The smoothed inequality: `ψ` evaluated at `√(|·|² + ε²)` along the segment. -/
private theorem psi_zigzag_eps {p : ℝ} (hp : 1 < p) (x y h k : H) {ε : ℝ} (hε : 0 < ε) :
    ((2 ≤ p ∧ ‖h‖ ≤ ‖k‖) →
      psi p √(‖x + h‖ ^ 2 + ε ^ 2) √(‖y + k‖ ^ 2 + ε ^ 2) ≤
        psi p √(‖x‖ ^ 2 + ε ^ 2) √(‖y‖ ^ 2 + ε ^ 2) +
          (psiS p √(‖x‖ ^ 2 + ε ^ 2) √(‖y‖ ^ 2 + ε ^ 2) * (⟪x, h⟫ / √(‖x‖ ^ 2 + ε ^ 2)) +
            psiR p √(‖x‖ ^ 2 + ε ^ 2) √(‖y‖ ^ 2 + ε ^ 2) * (⟪y, k⟫ / √(‖y‖ ^ 2 + ε ^ 2)))) ∧
    ((p ≤ 2 ∧ ‖k‖ ≤ ‖h‖) →
      psi p √(‖x‖ ^ 2 + ε ^ 2) √(‖y‖ ^ 2 + ε ^ 2) +
          (psiS p √(‖x‖ ^ 2 + ε ^ 2) √(‖y‖ ^ 2 + ε ^ 2) * (⟪x, h⟫ / √(‖x‖ ^ 2 + ε ^ 2)) +
            psiR p √(‖x‖ ^ 2 + ε ^ 2) √(‖y‖ ^ 2 + ε ^ 2) * (⟪y, k⟫ / √(‖y‖ ^ 2 + ε ^ 2))) ≤
        psi p √(‖x + h‖ ^ 2 + ε ^ 2) √(‖y + k‖ ^ 2 + ε ^ 2)) := by
  obtain ⟨hSpos, dS, dS1, hS2, hSH⟩ := q_facts (quad_pos x h hε) (inner_sq_le x h)
  obtain ⟨hRpos, dR, dR1, -, hRK⟩ := q_facts (quad_pos y k hε) (inner_sq_le y k)
  have L := psi_line hp hSpos hRpos dS dR dS1 dR1 hS2
  have ex : ‖x‖ ^ 2 + ε ^ 2 + 2 * ⟪x, h⟫ + ‖h‖ ^ 2 = ‖x + h‖ ^ 2 + ε ^ 2 := by
    rw [norm_add_sq_real]; ring
  have ey : ‖y‖ ^ 2 + ε ^ 2 + 2 * ⟪y, k⟫ + ‖k‖ ^ 2 = ‖y + k‖ ^ 2 + ε ^ 2 := by
    rw [norm_add_sq_real]; ring
  simp only [qS_zero, qS1_zero, qS_one, ex, ey] at L
  refine ⟨fun ⟨hp2, hhk⟩ => L.1 ⟨hp2, fun t => ?_⟩, fun ⟨hp2, hhk⟩ => L.2 ⟨hp2, fun t => ?_⟩⟩
  · rw [hSH, hRK]; exact pow_le_pow_left₀ (norm_nonneg _) hhk 2
  · rw [hSH, hRK]; exact pow_le_pow_left₀ (norm_nonneg _) hhk 2

omit [InnerProductSpace ℝ H] in
private theorem tendsto_sqrt_sq_add (z : H) :
    Tendsto (fun ε : ℝ => √(‖z‖ ^ 2 + ε ^ 2)) (𝓝[>] 0) (𝓝 ‖z‖) := by
  have hc : Continuous (fun ε : ℝ => √(‖z‖ ^ 2 + ε ^ 2)) := by fun_prop
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simpa [Real.sqrt_sq (norm_nonneg z)] using this

private theorem tendsto_psi {p : ℝ} (hp : 1 < p) {l : Filter ℝ} {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun ε => psi p (f ε) (g ε)) l (𝓝 (psi p a b)) := by
  unfold psi
  exact (hf.sub (hg.const_mul _)).mul ((hf.add hg).rpow_const (Or.inr (by linarith)))

private theorem tendsto_psiS_mul {p : ℝ} {l : Filter ℝ} {f g : ℝ → ℝ} {a b c : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (ha : c ≠ 0 → 0 < a) (hb : 0 ≤ b) :
    Tendsto (fun ε => psiS p (f ε) (g ε) * (c / f ε)) l (𝓝 (psiS p a b * (c / a))) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using tendsto_const_nhds
  have ha := ha hc
  unfold psiS
  exact ((tendsto_const_nhds.mul ((hf.add hg).rpow_const
    (Or.inl (add_pos_of_pos_of_nonneg ha hb).ne'))).mul (hf.sub (hg.const_mul _))).mul
    (tendsto_const_nhds.div hf ha.ne')

private theorem tendsto_psiR_mul {p : ℝ} {l : Filter ℝ} {f g : ℝ → ℝ} {a b c : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (ha : 0 ≤ a) (hb : c ≠ 0 → 0 < b) :
    Tendsto (fun ε => psiR p (f ε) (g ε) * (c / g ε)) l (𝓝 (psiR p a b * (c / b))) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using tendsto_const_nhds
  have hb := hb hc
  unfold psiR
  exact ((tendsto_const_nhds.mul hg).mul ((hf.add hg).rpow_const
    (Or.inl (add_pos_of_nonneg_of_pos ha hb).ne'))).mul (tendsto_const_nhds.div hg hb.ne')

/-- **The concavity property of Burkholder's function along lines** (for `ψ`), with the
"gradient" `(ψ_s (|x|, |y|) x / |x|, ψ_r (|x|, |y|) y / |y|)` (`0` where `x = 0`, resp. `y = 0`):
for `p ≥ 2` and `|h| ≤ |k|`, `ψ (|x + h|, |y + k|) ≤ ψ (|x|, |y|) + ⟨∇ψ, (h, k)⟩`; for `p ≤ 2` and
`|k| ≤ |h|`, the reverse inequality. The non-smooth points `x = 0`, `y = 0` are handled by
replacing `|z|` by `√(|z|² + ε²)` and letting `ε → 0`. -/
private theorem psi_zigzag {p : ℝ} (hp : 1 < p) (x y h k : H) :
    ((2 ≤ p ∧ ‖h‖ ≤ ‖k‖) → psi p ‖x + h‖ ‖y + k‖ ≤
        psi p ‖x‖ ‖y‖ + (psiS p ‖x‖ ‖y‖ * (⟪x, h⟫ / ‖x‖) + psiR p ‖x‖ ‖y‖ * (⟪y, k⟫ / ‖y‖))) ∧
    ((p ≤ 2 ∧ ‖k‖ ≤ ‖h‖) → psi p ‖x‖ ‖y‖ + (psiS p ‖x‖ ‖y‖ * (⟪x, h⟫ / ‖x‖) +
        psiR p ‖x‖ ‖y‖ * (⟪y, k⟫ / ‖y‖)) ≤ psi p ‖x + h‖ ‖y + k‖) := by
  have hx := tendsto_sqrt_sq_add x
  have hy := tendsto_sqrt_sq_add y
  have hL := tendsto_psi hp (tendsto_sqrt_sq_add (x + h)) (tendsto_sqrt_sq_add (y + k))
  have hR := (tendsto_psi hp hx hy).add
    ((tendsto_psiS_mul (p := p) (c := ⟪x, h⟫) hx hy
      (fun hc => norm_pos_iff.2 fun hx0 => hc (by simp [hx0])) (norm_nonneg y)).add
    (tendsto_psiR_mul (p := p) (c := ⟪y, k⟫) hx hy (norm_nonneg x)
      (fun hc => norm_pos_iff.2 fun hy0 => hc (by simp [hy0]))))
  refine ⟨fun hA => le_of_tendsto_of_tendsto hL hR (eventually_nhdsWithin_of_forall
    fun ε hε => (psi_zigzag_eps hp x y h k (Set.mem_Ioi.1 hε)).1 hA), fun hB =>
    le_of_tendsto_of_tendsto hR hL (eventually_nhdsWithin_of_forall
    fun ε hε => (psi_zigzag_eps hp x y h k (Set.mem_Ioi.1 hε)).2 hB)⟩

end Hilbert

/-! ### Burkholder's function and its majorization of `V (x, y) = |x|^p − (p* − 1)^p |y|^p` -/

/-- **Burkholder's function** (Osękowski 2012, (3.2)), as a function of `s = |x|`, `r = |y|`:
`U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}`, `p* = max (p, p/(p − 1))`.
Here `x` is the position of the subordinate martingale and `y` that of the dominating one. -/
noncomputable def burkholderU (p s r : ℝ) : ℝ :=
  p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * (s - (max p (p / (p - 1)) - 1) * r) *
    (s + r) ^ (p - 1)

private theorem max_eq_A {p : ℝ} (hp : 2 ≤ p) : max p (p / (p - 1)) = p :=
  max_eq_left (by rw [div_le_iff₀ (by linarith)]; nlinarith)

private theorem max_eq_B {p : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) : max p (p / (p - 1)) = p / (p - 1) :=
  max_eq_right (by rw [le_div_iff₀ (by linarith)]; nlinarith)

private theorem U_eq_A {p : ℝ} (hp : 2 ≤ p) (s r : ℝ) :
    burkholderU p s r = p * (1 - 1 / p) ^ (p - 1) * psi p s r := by
  unfold burkholderU psi; rw [max_eq_A hp]; ring

private theorem U_eq_B {p : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) (s r : ℝ) :
    burkholderU p s r = -(p * (1 / p) ^ (p - 1) / (p - 1)) * psi p r s := by
  unfold burkholderU psi; rw [max_eq_B hp1 hp]
  have hp0 : p - 1 ≠ 0 := by linarith
  have h1 : 1 - 1 / (p / (p - 1)) = 1 / p := by field_simp; ring
  rw [h1, add_comm r s]; field_simp; ring

private theorem alpha_A {p : ℝ} (hp : 2 ≤ p) : 1 ≤ p * (1 - 1 / p) ^ (p - 1) := by
  have hp0 : 0 < p := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := -(1 / p)) (by
    rw [neg_le_neg_iff, div_le_one hp0]; linarith) (p := p - 1) (by linarith)
  have e : 1 + (p - 1) * -(1 / p) = 1 / p := by field_simp; ring
  rw [e, ← sub_eq_add_neg] at h
  calc (1 : ℝ) = p * (1 / p) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hp0.le

private theorem alpha_B {p : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) : 1 ≤ p * (1 / p) ^ (p - 1) := by
  have hp0 : 0 < p := by linarith
  have h : (1 / p) ^ (1 : ℝ) ≤ (1 / p) ^ (p - 1) :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) (by rw [div_le_one hp0]; linarith)
      (by linarith)
  rw [Real.rpow_one] at h
  calc (1 : ℝ) = p * (1 / p) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hp0.le

private theorem nonneg_of_deriv_sign {g g' : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hcont : Continuous g) (hd : ∀ s, 0 < s → HasDerivAt g (g' s) s)
    (h1 : ∀ s, 0 < s → s < c → g' s ≤ 0) (h2 : ∀ s, c < s → 0 ≤ g' s) (hgc : g c = 0)
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ g s := by
  rcases le_total s c with hsc | hsc
  · have hanti : AntitoneOn g (Icc 0 c) := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 c)
      hcont.continuousOn (fun x hx => by
        rw [interior_Icc] at hx; exact (hd x hx.1).hasDerivWithinAt)
      (fun x hx => by rw [interior_Icc] at hx; exact h1 x hx.1 hx.2)
    have := hanti ⟨hs, hsc⟩ ⟨hc.le, le_rfl⟩ hsc
    linarith
  · have hmono : MonotoneOn g (Ici c) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici c)
      hcont.continuousOn (fun x hx => by
        rw [interior_Ici] at hx; exact (hd x (hc.trans hx)).hasDerivWithinAt)
      (fun x hx => by rw [interior_Ici] at hx; exact h2 x hx)
    have := hmono self_mem_Ici hsc hsc
    linarith

private theorem continuous_psi_left {p : ℝ} (hp : 1 < p) (r : ℝ) :
    Continuous fun s => psi p s r := by
  unfold psi
  exact (continuous_id.sub continuous_const).mul
    ((continuous_id.add continuous_const).rpow_const fun _ => Or.inr (by linarith))

private theorem continuous_psi_right {p : ℝ} (hp : 1 < p) (r : ℝ) :
    Continuous fun s => psi p r s := by
  unfold psi
  exact (continuous_const.sub (continuous_const.mul continuous_id)).mul
    ((continuous_const.add continuous_id).rpow_const fun _ => Or.inr (by linarith))

private theorem psi_self_zero {p r : ℝ} (hr : 0 ≤ r) (hp : 1 < p) :
    psi p 0 r = -(p - 1) * r ^ p := by
  unfold psi
  rw [zero_add, show r ^ p = r ^ ((p - 1) + 1) by ring_nf, Real.rpow_add' hr (by linarith),
    Real.rpow_one]
  ring

private theorem psi_zero_right {p s : ℝ} (hs : 0 ≤ s) (hp : 1 < p) : psi p s 0 = s ^ p := by
  unfold psi
  rw [add_zero, show s ^ p = s ^ ((p - 1) + 1) by ring_nf, Real.rpow_add' hs (by linarith),
    Real.rpow_one]
  ring

/-- The sign of `∂_s (U − V)` for `p ≥ 2`: with `W = s + r`, `v = s / W`, it is
`p W^{p−1} (α ((p − 1) v − (p − 2)) − v^{p−1})`, and the concave function
`v ↦ α ((p − 1) v − (p − 2)) − v^{p−1}` vanishes at `v = 1 − 1/p` and is `≥ 0` at `v = 1`. -/
private theorem sign_A {p s r : ℝ} (hp : 2 ≤ p) (hs : 0 < s) (hr : 0 < r) :
    (s < (p - 1) * r → p * (1 - 1 / p) ^ (p - 1) * psiS p s r - p * s ^ (p - 1) ≤ 0) ∧
    ((p - 1) * r < s → 0 ≤ p * (1 - 1 / p) ^ (p - 1) * psiS p s r - p * s ^ (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hq : 1 ≤ p - 1 := by linarith
  have hα := alpha_A hp
  set A := (1 - 1 / p) ^ (p - 1) with hA
  have hA' : A = ((p - 1) / p) ^ (p - 1) := by rw [hA]; congr 1; field_simp
  set W := s + r with hW
  have hWpos : 0 < W := by linarith
  set v := s / W with hv
  have hv0 : 0 < v := div_pos hs hWpos
  have hv1 : v < 1 := by rw [hv, div_lt_one hWpos]; linarith
  have hsv : s = v * W := by rw [hv]; field_simp
  -- `∂_s (U − V) = p W^{p−1} m (v)`
  have key : p * A * psiS p s r - p * s ^ (p - 1) =
      p * W ^ (p - 1) * (p * A * ((p - 1) * v - (p - 2)) - v ^ (p - 1)) := by
    unfold psiS
    have e1 : (s + r) ^ (p - 2) = W ^ (p - 1) / W := by
      rw [← hW, show p - 2 = p - 1 - 1 by ring, Real.rpow_sub_one hWpos.ne']
    have e2 : s ^ (p - 1) = v ^ (p - 1) * W ^ (p - 1) := by
      rw [hsv, Real.mul_rpow hv0.le hWpos.le]
    rw [e1, e2]
    have hr' : r = W - v * W := by rw [← hsv]; ring
    rw [hr', hsv]
    field_simp
    ring
  have hφ := convexOn_rpow hq
  have hv₀ : (p - 1) / p < 1 := by rw [div_lt_one hp0]; linarith
  have hv₀pos : 0 < (p - 1) / p := div_pos (by linarith) hp0
  have hpW : 0 < p * W ^ (p - 1) := mul_pos hp0 (Real.rpow_pos_of_pos hWpos _)
  have e1 : p * (1 - (p - 1) / p) = 1 := by field_simp; ring
  have e2 : p * ((p - 1) / p - v) = p - 1 - p * v := by field_simp
  have e3 : p * (v - (p - 1) / p) = p * v - (p - 1) := by field_simp
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hvv : v < (p - 1) / p := by
      rw [hv, div_lt_div_iff₀ hWpos hp0]; linarith
    have sec := hφ.secant_mono_aux1 (x := v) (y := (p - 1) / p) (z := 1) (mem_Ici.2 hv0.le)
      (mem_Ici.2 zero_le_one) hvv hv₀
    simp only [Real.one_rpow, mul_one, ← hA'] at sec
    have key' : p * (1 - v) * A ≤ v ^ (p - 1) + (p - 1 - p * v) := by
      have := mul_le_mul_of_nonneg_left sec hp0.le
      rw [mul_add, ← mul_assoc, ← mul_assoc, e1, e2, one_mul] at this
      linarith
    have h3 : 0 ≤ (p - 1 - p * v) * (p * A - 1) := by
      apply mul_nonneg
      · have := mul_lt_mul_of_pos_left hvv hp0
        rw [mul_div_cancel₀ _ hp0.ne'] at this; linarith
      · linarith
    rw [key]
    exact mul_nonpos_of_nonneg_of_nonpos hpW.le (by nlinarith)
  · have hvv : (p - 1) / p < v := by
      rw [hv, div_lt_div_iff₀ hp0 hWpos]; linarith
    have sec := hφ.secant_mono_aux1 (x := (p - 1) / p) (y := v) (z := 1) (mem_Ici.2 hv₀pos.le)
      (mem_Ici.2 zero_le_one) hvv hv1
    simp only [Real.one_rpow, mul_one, ← hA'] at sec
    have key' : v ^ (p - 1) ≤ p * (1 - v) * A + (p * v - (p - 1)) := by
      have := mul_le_mul_of_nonneg_left sec hp0.le
      rw [mul_add, ← mul_assoc, ← mul_assoc, e1, e3, one_mul] at this
      linarith
    have h3 : 0 ≤ (p * v - (p - 1)) * (p * A - 1) := by
      apply mul_nonneg
      · have := mul_lt_mul_of_pos_left hvv hp0
        rw [mul_div_cancel₀ _ hp0.ne'] at this; linarith
      · linarith
    rw [key]
    exact mul_nonneg hpW.le (by nlinarith)

/-- The sign of `∂_s (U − V)` for `p ≤ 2`: it is `p s (((r + s)/p)^{p−2} − s^{p−2})`. -/
private theorem sign_B {p s r : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) (hs : 0 < s) (hr : 0 < r) :
    (s < r / (p - 1) →
      -(p * (1 / p) ^ (p - 1) / (p - 1)) * psiR p r s - p * s ^ (p - 1) ≤ 0) ∧
    (r / (p - 1) < s →
      0 ≤ -(p * (1 / p) ^ (p - 1) / (p - 1)) * psiR p r s - p * s ^ (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p - 1 := by linarith
  have key : -(p * (1 / p) ^ (p - 1) / (p - 1)) * psiR p r s - p * s ^ (p - 1) =
      p * s * (((r + s) / p) ^ (p - 2) - s ^ (p - 2)) := by
    unfold psiR
    have e1 : (1 / p) ^ (p - 1) = (1 / p) ^ (p - 2) * (1 / p) := by
      rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one (by positivity)]
    have e2 : ((r + s) / p) ^ (p - 2) = (1 / p) ^ (p - 2) * (r + s) ^ (p - 2) := by
      rw [div_eq_mul_one_div (r + s) p, mul_comm (r + s),
        Real.mul_rpow (by positivity) (by linarith)]
    have e3 : s ^ (p - 1) = s ^ (p - 2) * s := by
      rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hs.ne']
    rw [e1, e2, e3]
    field_simp
  have hrs : 0 < (r + s) / p := by positivity
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : s ≤ (r + s) / p := by
      rw [le_div_iff₀ hp0]; rw [lt_div_iff₀ hq0] at h; linarith
    rw [key]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.2 (Real.rpow_le_rpow_of_nonpos hs h' (by linarith)))
  · have h' : (r + s) / p ≤ s := by
      rw [div_le_iff₀ hp0]; rw [div_lt_iff₀ hq0] at h; linarith
    rw [key]
    exact mul_nonneg (by positivity)
      (sub_nonneg.2 (Real.rpow_le_rpow_of_nonpos hrs h' (by linarith)))

/-- `U ≥ V` for `p ≥ 2`, in terms of `ψ`. -/
private theorem V_le_U_A {p s r : ℝ} (hp : 2 ≤ p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    s ^ p - (p - 1) ^ p * r ^ p ≤ p * (1 - 1 / p) ^ (p - 1) * psi p s r := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hα := alpha_A hp
  set A := (1 - 1 / p) ^ (p - 1) with hA
  rcases hr.eq_or_lt with rfl | hr
  · rw [psi_zero_right hs hp1, Real.zero_rpow hp0.ne']
    nlinarith [Real.rpow_nonneg hs p]
  set g : ℝ → ℝ := fun s => p * A * psi p s r - s ^ p + (p - 1) ^ p * r ^ p with hg
  suffices 0 ≤ g s by simp only [hg] at this; linarith
  have hq : 1 ≤ p - 1 := by linarith
  set c := (p - 1) * r with hc
  have hcpos : 0 < c := mul_pos (by linarith) hr
  refine nonneg_of_deriv_sign (g' := fun s => p * A * psiS p s r - p * s ^ (p - 1)) hcpos
    ?_ ?_ ?_ ?_ ?_ hs
  · exact ((continuous_const.mul (continuous_psi_left hp1 r)).sub
      (continuous_id.rpow_const fun _ => Or.inr hp0.le)).add continuous_const
  · intro s hs
    have h := (((psi_hasDerivAt (p := p) (hasDerivAt_id' (x := s)) (hasDerivAt_const s r)
      (show 0 < s + r by linarith)).const_mul (p * A)).sub
      (Real.hasDerivAt_rpow_const (p := p) (Or.inl hs.ne'))).add_const ((p - 1) ^ p * r ^ p)
    convert h using 1; ring
  · intro s hs hsc
    exact (sign_A hp hs hr).1 hsc
  · intro s hsc
    exact (sign_A hp (hcpos.trans hsc) hr).2 hsc
  · simp only [hg, hc]
    unfold psi
    rw [Real.mul_rpow (by linarith) hr.le]; ring

/-- `U ≥ V` for `p ≤ 2`, in terms of `ψ`. -/
private theorem V_le_U_B {p s r : ℝ} (hp1 : 1 < p) (hp : p ≤ 2) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    s ^ p - (1 / (p - 1)) ^ p * r ^ p ≤ -(p * (1 / p) ^ (p - 1) / (p - 1)) * psi p r s := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p - 1 := by linarith
  have hα := alpha_B hp1 hp
  set α := p * (1 / p) ^ (p - 1) with hαdef
  rcases hr.eq_or_lt with rfl | hr
  · rw [psi_self_zero hs hp1, Real.zero_rpow hp0.ne']
    have e : -(α / (p - 1)) * (-(p - 1) * s ^ p) = α * s ^ p := by field_simp
    rw [e]
    nlinarith [Real.rpow_nonneg hs p]
  set g : ℝ → ℝ := fun s => -(α / (p - 1)) * psi p r s - s ^ p + (1 / (p - 1)) ^ p * r ^ p
    with hg
  suffices 0 ≤ g s by simp only [hg] at this; linarith
  set c := r / (p - 1) with hc
  have hcpos : 0 < c := div_pos hr hq0
  refine nonneg_of_deriv_sign (g' := fun s => -(α / (p - 1)) * psiR p r s - p * s ^ (p - 1))
    hcpos ?_ ?_ ?_ ?_ ?_ hs
  · exact ((continuous_const.mul (continuous_psi_right hp1 r)).sub
      (continuous_id.rpow_const fun _ => Or.inr hp0.le)).add continuous_const
  · intro s hs
    have h := (((psi_hasDerivAt (p := p) (hasDerivAt_const s r) (hasDerivAt_id' (x := s))
      (show 0 < r + s by linarith)).const_mul (-(α / (p - 1)))).sub
      (Real.hasDerivAt_rpow_const (p := p) (Or.inl hs.ne'))).add_const ((1 / (p - 1)) ^ p * r ^ p)
    convert h using 1; ring
  · intro s hs hsc
    exact (sign_B hp1 hp hs hr).1 hsc
  · intro s hsc
    exact (sign_B hp1 hp (hcpos.trans hsc) hr).2 hsc
  · simp only [hg, hc]
    unfold psi
    rw [Real.div_rpow hr.le hq0.le, Real.div_rpow zero_le_one hq0.le, Real.one_rpow]
    field_simp
    ring

/-- **Majorization** (Burkholder; Osękowski 2012, proof of Theorem 3.5): `V ≤ U`, that is
`|x|^p − (p* − 1)^p |y|^p ≤ U (x, y)`, with `s = |x|`, `r = |y|`. -/
theorem burkholderU_ge {p s r : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    s ^ p - (max p (p / (p - 1)) - 1) ^ p * r ^ p ≤ burkholderU p s r := by
  rcases le_total 2 p with h2 | h2
  · rw [U_eq_A h2, max_eq_A h2]; exact V_le_U_A h2 hs hr
  · have hp0 : p - 1 ≠ 0 := by linarith
    rw [U_eq_B hp h2, max_eq_B hp h2, show p / (p - 1) - 1 = 1 / (p - 1) by field_simp; ring]
    exact V_le_U_B hp h2 hs hr

/-! ### Burkholder's method: `E U (X_n, Y_n) ≤ E U (X_{n−1}, Y_{n−1}) ≤ … ≤ U (0, 0) = 0` -/

section Method

variable {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `E ⟨Z, X_{k+1} − X_k⟩ = 0` for an `ℱ_k`-measurable `Z`, by the pull-out property of the
conditional expectation: `E [⟨Z, dX_{k+1}⟩ | ℱ_k] = ⟨Z, E [dX_{k+1} | ℱ_k]⟩ = 0`. -/
private theorem integral_inner_increment {X : ℕ → Ω → H} (hX : Martingale X ℱ μ) {k : ℕ}
    {Z : Ω → H} (hZ : StronglyMeasurable[ℱ k] Z)
    (hint : Integrable (fun ω => ⟪Z ω, X (k + 1) ω - X k ω⟫) μ) :
    ∫ ω, ⟪Z ω, X (k + 1) ω - X k ω⟫ ∂μ = 0 := by
  have hd : Integrable (X (k + 1) - X k) μ := (hX.integrable _).sub (hX.integrable _)
  have hB : ∀ v w : H, (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) v w = ⟪v, w⟫ :=
    fun v w => innerSL_apply_apply ℝ v w
  have hint' :
      Integrable (fun ω => (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) (Z ω) ((X (k + 1) - X k) ω)) μ := by
    simpa only [hB, Pi.sub_apply] using hint
  have h1 := condExp_bilin_of_aestronglyMeasurable_left (m := ℱ k) (innerSL ℝ)
    hZ.aestronglyMeasurable hint' hd
  simp only [hB, Pi.sub_apply] at h1
  have h2 : μ[X (k + 1) - X k | ℱ k] =ᵐ[μ] 0 := by
    filter_upwards [condExp_sub (hX.integrable (k + 1)) (hX.integrable k) (ℱ k),
      hX.condExp_ae_eq (Nat.le_succ k)] with ω h3 h4
    rw [h3, Pi.sub_apply, h4, condExp_of_stronglyMeasurable (ℱ.le k) (hX.stronglyAdapted k)
      (hX.integrable k)]
    simp
  calc ∫ ω, ⟪Z ω, X (k + 1) ω - X k ω⟫ ∂μ
      = ∫ ω, (μ[fun ω => ⟪Z ω, X (k + 1) ω - X k ω⟫ | ℱ k]) ω ∂μ :=
        (integral_condExp (ℱ.le k)).symm
    _ = ∫ ω, ⟪Z ω, μ[X (k + 1) - X k | ℱ k] ω⟫ ∂μ := integral_congr_ae h1
    _ = ∫ _ω, (0 : ℝ) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [h2] with ω hω
        rw [hω, Pi.zero_apply, inner_zero_right]
    _ = 0 := integral_zero _ _

omit [IsProbabilityMeasure μ] in
private theorem integrable_rpow_of_memLp {W : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hW : MemLp W (ENNReal.ofReal p) μ) (hWnn : ∀ ω, 0 ≤ W ω) :
    Integrable (fun ω => W ω ^ p) μ := by
  have h := hW.integrable_norm_rpow (by simpa using hp) ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp.le] at h
  refine h.congr (Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_of_nonneg (hWnn ω)]

private theorem rpow_sub_one_mul_le {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {W : ℝ} (haW : a ≤ W) (hbW : b ≤ W) : a ^ (p - 1) * b ≤ W ^ p := by
  have hW : 0 ≤ W := ha.trans haW
  calc a ^ (p - 1) * b ≤ W ^ (p - 1) * W :=
        mul_le_mul (Real.rpow_le_rpow ha haW (by linarith)) hbW hb (Real.rpow_nonneg hW _)
    _ = W ^ p := by
        rw [← Real.rpow_add_one' hW (by linarith)]; ring_nf

omit [IsProbabilityMeasure μ] [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem integrable_of_bound {F : ℝ → ℝ → ℝ} {C p : ℝ} (hp : 0 < p)
    (hF : Measurable (Function.uncurry F))
    (hFb : ∀ s r, 0 ≤ s → 0 ≤ r → |F s r| ≤ C * (s + r) ^ p) {U V : Ω → H}
    (hU : MemLp U (ENNReal.ofReal p) μ) (hV : MemLp V (ENNReal.ofReal p) μ) :
    Integrable (fun ω => F ‖U ω‖ ‖V ω‖) μ := by
  have hW := integrable_rpow_of_memLp hp (hU.norm.add hV.norm)
    (fun ω => add_nonneg (norm_nonneg (U ω)) (norm_nonneg (V ω)))
  refine (hW.const_mul C).mono' ?_ (Eventually.of_forall fun ω => ?_)
  · exact (hF.comp_aemeasurable (hU.aestronglyMeasurable.norm.aemeasurable.prodMk
      hV.aestronglyMeasurable.norm.aemeasurable)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact hFb _ _ (norm_nonneg _) (norm_nonneg _)

/-- One step of Burkholder's method: `E U (X_{k+1}, Y_{k+1}) ≤ E U (X_k, Y_k)`. -/
private theorem method_step {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ)
    {F f g : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : Measurable (Function.uncurry F)) (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g))
    (hzig : ∀ x y h k : H, ‖h‖ ≤ ‖k‖ →
      F ‖x + h‖ ‖y + k‖ ≤ F ‖x‖ ‖y‖ + f ‖x‖ ‖y‖ * ⟪x, h⟫ + g ‖x‖ ‖y‖ * ⟪y, k⟫)
    (hFb : ∀ s r, 0 ≤ s → 0 ≤ r → |F s r| ≤ C * (s + r) ^ p)
    (hfb : ∀ s r, 0 ≤ s → 0 ≤ r → |f s r| * s ≤ C * (s + r) ^ (p - 1))
    (hgb : ∀ s r, 0 ≤ s → 0 ≤ r → |g s r| * r ≤ C * (s + r) ^ (p - 1)) {k : ℕ}
    (hsub : ∀ᵐ ω ∂μ, ‖X (k + 1) ω - X k ω‖ ≤ ‖Y (k + 1) ω - Y k ω‖)
    (hXk : MemLp (X k) (ENNReal.ofReal p) μ) (hYk : MemLp (Y k) (ENNReal.ofReal p) μ)
    (hXk1 : MemLp (X (k + 1)) (ENNReal.ofReal p) μ)
    (hYk1 : MemLp (Y (k + 1)) (ENNReal.ofReal p) μ) :
    ∫ ω, F ‖X (k + 1) ω‖ ‖Y (k + 1) ω‖ ∂μ ≤ ∫ ω, F ‖X k ω‖ ‖Y k ω‖ ∂μ := by
  have hp0 : 0 < p := by linarith
  have hdX := hXk1.sub hXk
  have hdY := hYk1.sub hYk
  -- the dominating function `C W^p`, `W = |X_k| + |Y_k| + |dX| + |dY|`
  set W : Ω → ℝ := fun ω => ‖X k ω‖ + ‖Y k ω‖ + ‖X (k + 1) ω - X k ω‖ + ‖Y (k + 1) ω - Y k ω‖
    with hWdef
  have hWnn : ∀ ω, 0 ≤ W ω := fun ω => by positivity
  have hWint : Integrable (fun ω => C * W ω ^ p) μ :=
    (integrable_rpow_of_memLp hp0 (((hXk.norm.add hYk.norm).add hdX.norm).add hdY.norm)
      hWnn).const_mul C
  have hI1 := integrable_of_bound hp0 hF hFb hXk1 hYk1
  have hI0 := integrable_of_bound hp0 hF hFb hXk hYk
  -- the two linear terms
  have mXk : Measurable[ℱ k] fun ω => ‖X k ω‖ := (hX.stronglyAdapted k).norm.measurable
  have mYk : Measurable[ℱ k] fun ω => ‖Y k ω‖ := (hY.stronglyAdapted k).norm.measurable
  set ZX : Ω → H := fun ω => f ‖X k ω‖ ‖Y k ω‖ • X k ω with hZX
  set ZY : Ω → H := fun ω => g ‖X k ω‖ ‖Y k ω‖ • Y k ω with hZY
  have sZX : StronglyMeasurable[ℱ k] ZX :=
    (hf.comp (mXk.prodMk mYk)).stronglyMeasurable.smul (hX.stronglyAdapted k)
  have sZY : StronglyMeasurable[ℱ k] ZY :=
    (hg.comp (mXk.prodMk mYk)).stronglyMeasurable.smul (hY.stronglyAdapted k)
  have eZX : ∀ ω, ⟪ZX ω, X (k + 1) ω - X k ω⟫ =
      f ‖X k ω‖ ‖Y k ω‖ * ⟪X k ω, X (k + 1) ω - X k ω⟫ := fun ω => real_inner_smul_left _ _ _
  have eZY : ∀ ω, ⟪ZY ω, Y (k + 1) ω - Y k ω⟫ =
      g ‖X k ω‖ ‖Y k ω‖ * ⟪Y k ω, Y (k + 1) ω - Y k ω⟫ := fun ω => real_inner_smul_left _ _ _
  have hIX : Integrable (fun ω => ⟪ZX ω, X (k + 1) ω - X k ω⟫) μ := by
    refine hWint.mono' ((sZX.mono (ℱ.le k)).aestronglyMeasurable.inner hdX.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [eZX, Real.norm_eq_abs, abs_mul]
    calc |f ‖X k ω‖ ‖Y k ω‖| * |⟪X k ω, X (k + 1) ω - X k ω⟫|
        ≤ |f ‖X k ω‖ ‖Y k ω‖| * (‖X k ω‖ * ‖X (k + 1) ω - X k ω‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
      _ = |f ‖X k ω‖ ‖Y k ω‖| * ‖X k ω‖ * ‖X (k + 1) ω - X k ω‖ := by ring
      _ ≤ C * (‖X k ω‖ + ‖Y k ω‖) ^ (p - 1) * ‖X (k + 1) ω - X k ω‖ :=
          mul_le_mul_of_nonneg_right (hfb _ _ (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = C * ((‖X k ω‖ + ‖Y k ω‖) ^ (p - 1) * ‖X (k + 1) ω - X k ω‖) := by ring
      _ ≤ C * W ω ^ p := by
          gcongr
          refine rpow_sub_one_mul_le hp (by positivity) (norm_nonneg _) ?_ ?_
          · simp only [hWdef]
            linarith [norm_nonneg (X (k + 1) ω - X k ω), norm_nonneg (Y (k + 1) ω - Y k ω)]
          · simp only [hWdef]
            linarith [norm_nonneg (X k ω), norm_nonneg (Y k ω), norm_nonneg (Y (k + 1) ω - Y k ω)]
  have hIY : Integrable (fun ω => ⟪ZY ω, Y (k + 1) ω - Y k ω⟫) μ := by
    refine hWint.mono' ((sZY.mono (ℱ.le k)).aestronglyMeasurable.inner hdY.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [eZY, Real.norm_eq_abs, abs_mul]
    calc |g ‖X k ω‖ ‖Y k ω‖| * |⟪Y k ω, Y (k + 1) ω - Y k ω⟫|
        ≤ |g ‖X k ω‖ ‖Y k ω‖| * (‖Y k ω‖ * ‖Y (k + 1) ω - Y k ω‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
      _ = |g ‖X k ω‖ ‖Y k ω‖| * ‖Y k ω‖ * ‖Y (k + 1) ω - Y k ω‖ := by ring
      _ ≤ C * (‖X k ω‖ + ‖Y k ω‖) ^ (p - 1) * ‖Y (k + 1) ω - Y k ω‖ :=
          mul_le_mul_of_nonneg_right (hgb _ _ (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
      _ = C * ((‖X k ω‖ + ‖Y k ω‖) ^ (p - 1) * ‖Y (k + 1) ω - Y k ω‖) := by ring
      _ ≤ C * W ω ^ p := by
          gcongr
          refine rpow_sub_one_mul_le hp (by positivity) (norm_nonneg _) ?_ ?_
          · simp only [hWdef]
            linarith [norm_nonneg (X (k + 1) ω - X k ω), norm_nonneg (Y (k + 1) ω - Y k ω)]
          · simp only [hWdef]
            linarith [norm_nonneg (X k ω), norm_nonneg (Y k ω), norm_nonneg (X (k + 1) ω - X k ω)]
  have h0X := integral_inner_increment hX sZX hIX
  have h0Y := integral_inner_increment hY sZY hIY
  simp only [eZX] at hIX h0X
  simp only [eZY] at hIY h0Y
  calc ∫ ω, F ‖X (k + 1) ω‖ ‖Y (k + 1) ω‖ ∂μ
      ≤ ∫ ω, (F ‖X k ω‖ ‖Y k ω‖ + f ‖X k ω‖ ‖Y k ω‖ * ⟪X k ω, X (k + 1) ω - X k ω⟫ +
          g ‖X k ω‖ ‖Y k ω‖ * ⟪Y k ω, Y (k + 1) ω - Y k ω⟫) ∂μ := by
        refine integral_mono_ae hI1 ((hI0.add hIX).add hIY) ?_
        filter_upwards [hsub] with ω hω
        have := hzig (X k ω) (Y k ω) (X (k + 1) ω - X k ω) (Y (k + 1) ω - Y k ω) hω
        simpa only [add_sub_cancel] using this
    _ = ∫ ω, F ‖X k ω‖ ‖Y k ω‖ ∂μ := by
        have hI01 : Integrable (fun ω => F ‖X k ω‖ ‖Y k ω‖ +
            f ‖X k ω‖ ‖Y k ω‖ * ⟪X k ω, X (k + 1) ω - X k ω⟫) μ := hI0.add hIX
        rw [integral_add hI01 hIY, integral_add hI0 hIX, h0X, h0Y]; ring

/-- Burkholder's method: `E U (X_n, Y_n) ≤ U (0, 0) = 0`. -/
private theorem method {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖)
    {F f g : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : Measurable (Function.uncurry F)) (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g))
    (hzig : ∀ x y h k : H, ‖h‖ ≤ ‖k‖ →
      F ‖x + h‖ ‖y + k‖ ≤ F ‖x‖ ‖y‖ + f ‖x‖ ‖y‖ * ⟪x, h⟫ + g ‖x‖ ‖y‖ * ⟪y, k⟫)
    (hF0 : F 0 0 = 0)
    (hFb : ∀ s r, 0 ≤ s → 0 ≤ r → |F s r| ≤ C * (s + r) ^ p)
    (hfb : ∀ s r, 0 ≤ s → 0 ≤ r → |f s r| * s ≤ C * (s + r) ^ (p - 1))
    (hgb : ∀ s r, 0 ≤ s → 0 ≤ r → |g s r| * r ≤ C * (s + r) ^ (p - 1)) (n : ℕ)
    (hXn : ∀ k ≤ n, MemLp (X k) (ENNReal.ofReal p) μ)
    (hYn : ∀ k ≤ n, MemLp (Y k) (ENNReal.ofReal p) μ) :
    ∫ ω, F ‖X n ω‖ ‖Y n ω‖ ∂μ ≤ 0 := by
  suffices ∀ k ≤ n, ∫ ω, F ‖X k ω‖ ‖Y k ω‖ ∂μ ≤ 0 from this n le_rfl
  intro k
  induction k with
  | zero => intro _; simp [hX0, hY0, hF0]
  | succ k ih =>
    intro hk
    exact (method_step hp hX hY hC hF hf hg hzig hFb hfb hgb (hsub k) (hXn k (by omega))
      (hYn k (by omega)) (hXn (k + 1) hk) (hYn (k + 1) hk)).trans (ih (by omega))

end Method

/-! ### Bounds and measurability of Burkholder's function and of its gradient -/

private theorem abs_psiS_le {p s r : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) (hsr : 0 < s + r) :
    |psiS p s r| ≤ p * (1 + |p - 2|) * (s + r) ^ (p - 1) := by
  unfold psiS
  have e : (s + r) ^ (p - 1) = (s + r) ^ (p - 2) * (s + r) := by
    rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hsr.ne']
  have h1 : |s - (p - 2) * r| ≤ (1 + |p - 2|) * (s + r) := by
    have := abs_sub (s) ((p - 2) * r)
    rw [abs_mul, abs_of_nonneg hs, abs_of_nonneg hr] at this
    nlinarith [abs_nonneg (p - 2)]
  have h2 : 0 ≤ (s + r) ^ (p - 2) := Real.rpow_nonneg hsr.le _
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p), abs_of_nonneg h2, e]
  calc p * (s + r) ^ (p - 2) * |s - (p - 2) * r|
        ≤ p * (s + r) ^ (p - 2) * ((1 + |p - 2|) * (s + r)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (by linarith) h2)
    _ = _ := by ring

private theorem abs_psiR_le {p s r : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) (hsr : 0 < s + r) :
    |psiR p s r| ≤ p * (p - 1) * (s + r) ^ (p - 1) := by
  unfold psiR
  have e : (s + r) ^ (p - 1) = (s + r) ^ (p - 2) * (s + r) := by
    rw [show p - 1 = p - 2 + 1 by ring, Real.rpow_add_one hsr.ne']
  have h2 : 0 ≤ (s + r) ^ (p - 2) := Real.rpow_nonneg hsr.le _
  have hpp : 0 ≤ p * (p - 1) := mul_nonneg (by linarith) (by linarith)
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hpp, abs_of_nonneg hr, abs_of_nonneg h2, e]
  calc p * (p - 1) * r * (s + r) ^ (p - 2) ≤ p * (p - 1) * (s + r) * (s + r) ^ (p - 2) := by
        gcongr; linarith
    _ = _ := by ring

private theorem coef_bound {c a s B : ℝ} (hs : 0 ≤ s) (hB : 0 < s → |a| ≤ B) (hB0 : 0 ≤ B) :
    |c * (a / s)| * s ≤ |c| * B := by
  rcases hs.eq_or_lt with rfl | hs
  · simp only [div_zero, mul_zero, abs_zero]; exact mul_nonneg (abs_nonneg _) hB0
  · rw [abs_mul, abs_div, abs_of_pos hs, mul_assoc, div_mul_cancel₀ _ hs.ne']
    exact mul_le_mul_of_nonneg_left (hB hs) (abs_nonneg _)

private theorem abs_burkholderU_le {p s r : ℝ} (hp : 1 < p) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    |burkholderU p s r| ≤
      p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * max p (p / (p - 1)) * (s + r) ^ p := by
  set P := max p (p / (p - 1)) with hP
  have hP1 : 1 < P := lt_of_lt_of_le hp (le_max_left _ _)
  have hα : 0 ≤ p * (1 - 1 / P) ^ (p - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg (by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith) _)
  unfold burkholderU
  rw [← hP]
  have e : (s + r) ^ p = (s + r) * (s + r) ^ (p - 1) := by
    rw [show (s + r) ^ p = (s + r) ^ (1 + (p - 1)) by ring_nf, Real.rpow_add' (by linarith)
      (by linarith), Real.rpow_one]
  have h2 : 0 ≤ (s + r) ^ (p - 1) := Real.rpow_nonneg (by linarith) _
  have h1 : |s - (P - 1) * r| ≤ P * (s + r) := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg h2, e]
  calc p * (1 - 1 / P) ^ (p - 1) * |s - (P - 1) * r| * (s + r) ^ (p - 1)
      ≤ p * (1 - 1 / P) ^ (p - 1) * (P * (s + r)) * (s + r) ^ (p - 1) := by gcongr
    _ = _ := by ring

private theorem measurable_burkholderU (p : ℝ) : Measurable (Function.uncurry (burkholderU p)) := by
  change Measurable fun z : ℝ × ℝ => burkholderU p z.1 z.2
  unfold burkholderU
  fun_prop

private theorem burkholderU_zero (p : ℝ) : burkholderU p 0 0 = 0 := by
  simp [burkholderU]

/-! ### Burkholder's inequality -/

/-- `E U (X_n, Y_n) ≤ 0` for differentially subordinate martingales in `L^p`. -/
private theorem integral_burkholderU_nonpos {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ)
    (hXn : ∀ k ≤ n, MemLp (X k) (ENNReal.ofReal p) μ)
    (hYn : ∀ k ≤ n, MemLp (Y k) (ENNReal.ofReal p) μ) :
    ∫ ω, burkholderU p ‖X n ω‖ ‖Y n ω‖ ∂μ ≤ 0 := by
  set KU := p * (1 - 1 / max p (p / (p - 1))) ^ (p - 1) * max p (p / (p - 1)) with hKU
  have hP1 : 1 < max p (p / (p - 1)) := lt_of_lt_of_le hp (le_max_left _ _)
  have hKU0 : 0 ≤ KU := mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith) _)) (by linarith)
  have hS : 0 ≤ p * (1 + |p - 2|) := mul_nonneg (by linarith) (by positivity)
  have hR : 0 ≤ p * (p - 1) := mul_nonneg (by linarith) (by linarith)
  have hpow : ∀ s r : ℝ, 0 ≤ s → 0 ≤ r → 0 ≤ (s + r) ^ (p - 1) :=
    fun s r hs hr => Real.rpow_nonneg (by linarith) _
  rcases le_total 2 p with h2 | h2
  · -- `p ≥ 2`: `U = α ψ (|x|, |y|)`
    set α := p * (1 - 1 / p) ^ (p - 1) with hα
    have hα1 := alpha_A h2
    set C := KU + |α| * (p * (1 + |p - 2|)) + |α| * (p * (p - 1)) with hC
    have hCf : |α| * (p * (1 + |p - 2|)) ≤ C := by
      have := mul_nonneg (abs_nonneg α) hR; linarith
    have hCg : |α| * (p * (p - 1)) ≤ C := by
      have := mul_nonneg (abs_nonneg α) hS; linarith
    refine method hp hX hY hX0 hY0 hsub (F := burkholderU p)
      (f := fun s r => α * (psiS p s r / s)) (g := fun s r => α * (psiR p s r / r)) (C := C)
      (by have := mul_nonneg (abs_nonneg α) hS; have := mul_nonneg (abs_nonneg α) hR; linarith)
      (measurable_burkholderU p) ?_ ?_ ?_ (burkholderU_zero p) ?_ ?_ ?_ n hXn hYn
    · change Measurable fun z : ℝ × ℝ => α * (psiS p z.1 z.2 / z.1)
      unfold psiS; fun_prop
    · change Measurable fun z : ℝ × ℝ => α * (psiR p z.1 z.2 / z.2)
      unfold psiR; fun_prop
    · intro x y h k hhk
      have := (psi_zigzag hp x y h k).1 ⟨h2, hhk⟩
      rw [U_eq_A h2, U_eq_A h2]
      have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ α)
      calc α * psi p ‖x + h‖ ‖y + k‖ ≤ _ := this
        _ = _ := by ring
    · intro s r hs hr
      have := abs_burkholderU_le hp hs hr
      have h0 : 0 ≤ (s + r) ^ p := Real.rpow_nonneg (by linarith) _
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg α) hS) h0,
        mul_nonneg (mul_nonneg (abs_nonneg α) hR) h0]
    · intro s r hs hr
      calc |α * (psiS p s r / s)| * s ≤ |α| * (p * (1 + |p - 2|) * (s + r) ^ (p - 1)) :=
            coef_bound hs (fun hs' => abs_psiS_le hp hs hr (by linarith))
              (mul_nonneg hS (hpow s r hs hr))
        _ ≤ C * (s + r) ^ (p - 1) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCf (hpow s r hs hr)
    · intro s r hs hr
      calc |α * (psiR p s r / r)| * r ≤ |α| * (p * (p - 1) * (s + r) ^ (p - 1)) :=
            coef_bound hr (fun hr' => abs_psiR_le hp hs hr (by linarith))
              (mul_nonneg hR (hpow s r hs hr))
        _ ≤ C * (s + r) ^ (p - 1) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCg (hpow s r hs hr)
  · -- `p ≤ 2`: `U = −c ψ (|y|, |x|)`
    set c := p * (1 / p) ^ (p - 1) / (p - 1) with hc
    have hc0 : 0 < c := div_pos (by linarith [alpha_B hp h2]) (by linarith)
    set C := KU + |-c| * (p * (p - 1)) + |-c| * (p * (1 + |p - 2|)) with hC
    have hCf : |-c| * (p * (p - 1)) ≤ C := by
      have := mul_nonneg (abs_nonneg (-c)) hS; linarith
    have hCg : |-c| * (p * (1 + |p - 2|)) ≤ C := by
      have := mul_nonneg (abs_nonneg (-c)) hR; linarith
    refine method hp hX hY hX0 hY0 hsub (F := burkholderU p)
      (f := fun s r => -c * (psiR p r s / s)) (g := fun s r => -c * (psiS p r s / r)) (C := C)
      (by have := mul_nonneg (abs_nonneg (-c)) hS; have := mul_nonneg (abs_nonneg (-c)) hR
          linarith)
      (measurable_burkholderU p) ?_ ?_ ?_ (burkholderU_zero p) ?_ ?_ ?_ n hXn hYn
    · change Measurable fun z : ℝ × ℝ => -c * (psiR p z.2 z.1 / z.1)
      unfold psiR; fun_prop
    · change Measurable fun z : ℝ × ℝ => -c * (psiS p z.2 z.1 / z.2)
      unfold psiS; fun_prop
    · intro x y h k hhk
      have h1 := (psi_zigzag hp y x k h).2 ⟨h2, hhk⟩
      rw [U_eq_B hp h2, U_eq_B hp h2, ← hc]
      have h3 := mul_le_mul_of_nonneg_left h1 hc0.le
      have e : -c * psi p ‖y‖ ‖x‖ + -c * (psiR p ‖y‖ ‖x‖ / ‖x‖) * ⟪x, h⟫ +
          -c * (psiS p ‖y‖ ‖x‖ / ‖y‖) * ⟪y, k⟫ = -(c * (psi p ‖y‖ ‖x‖ +
            (psiS p ‖y‖ ‖x‖ * (⟪y, k⟫ / ‖y‖) + psiR p ‖y‖ ‖x‖ * (⟪x, h⟫ / ‖x‖)))) := by ring
      rw [e]; linarith
    · intro s r hs hr
      have := abs_burkholderU_le hp hs hr
      have h0 : 0 ≤ (s + r) ^ p := Real.rpow_nonneg (by linarith) _
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (-c)) hS) h0,
        mul_nonneg (mul_nonneg (abs_nonneg (-c)) hR) h0]
    · intro s r hs hr
      calc |-c * (psiR p r s / s)| * s ≤ |-c| * (p * (p - 1) * (s + r) ^ (p - 1)) :=
            coef_bound hs (fun hs' => by
              rw [add_comm s r]; exact abs_psiR_le hp hr hs (by linarith))
              (mul_nonneg hR (hpow s r hs hr))
        _ ≤ C * (s + r) ^ (p - 1) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCf (hpow s r hs hr)
    · intro s r hs hr
      calc |-c * (psiS p r s / r)| * r ≤ |-c| * (p * (1 + |p - 2|) * (s + r) ^ (p - 1)) :=
            coef_bound hr (fun hr' => by
              rw [add_comm s r]; exact abs_psiS_le hp hr hs (by linarith))
              (mul_nonneg hS (hpow s r hs hr))
        _ ≤ C * (s + r) ^ (p - 1) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCg (hpow s r hs hr)

/-- Burkholder's inequality without the separability of `H` (which the proof does not use). -/
theorem inequality_of_subordinate {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ) :
    eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (Y n) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  set q := ENNReal.ofReal p with hq
  have hq1 : 1 ≤ q := by rw [hq, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hq0 : q ≠ 0 := by rw [hq, Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : q.toReal = p := ENNReal.toReal_ofReal hp0.le
  set β := max p (p / (p - 1)) - 1 with hβdef
  have hβ : 0 < β := by have := le_max_left p (p / (p - 1)); linarith
  by_cases hYt : eLpNorm (Y n) q μ = ⊤
  · rw [hYt, ENNReal.mul_top (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hβ)]
    exact le_top
  -- if `Y_n ∈ L^p`, then `Y_k = E [Y_n | ℱ_k] ∈ L^p` and `X_k = Σ dX_j ∈ L^p` for `k ≤ n`
  have hYn : MemLp (Y n) q μ := memLp_iff.2 (lt_top_iff_ne_top.2 hYt)
  have hYk : ∀ k ≤ n, MemLp (Y k) q μ := fun k hk =>
    (hYn.condExp (m := ℱ k) hq1).ae_eq (hY.condExp_ae_eq hk)
  have hXk : ∀ k ≤ n, MemLp (X k) q μ := by
    intro k
    induction k with
    | zero => intro _; rw [show X 0 = 0 from funext hX0]; exact MemLp.zero
    | succ k ih =>
      intro hk
      have hd : MemLp (X (k + 1) - X k) q μ :=
        ((hYk (k + 1) hk).sub (hYk k (by omega))).of_le
          ((((hX.stronglyAdapted (k + 1)).mono (ℱ.le _)).aestronglyMeasurable).sub
            (((hX.stronglyAdapted k).mono (ℱ.le _)).aestronglyMeasurable))
          (by filter_upwards [hsub k] with ω hω; simpa only [Pi.sub_apply] using hω)
      have := (ih (by omega)).add hd
      rwa [add_sub_cancel] at this
  -- `E V (X_n, Y_n) ≤ E U (X_n, Y_n) ≤ 0`
  have hEU := integral_burkholderU_nonpos hp hX hY hX0 hY0 hsub n hXk hYk
  have hIX := integrable_rpow_of_memLp hp0 (hXk n le_rfl).norm (fun _ => norm_nonneg _)
  have hIY := integrable_rpow_of_memLp hp0 hYn.norm (fun _ => norm_nonneg _)
  have hIU := integrable_of_bound hp0 (measurable_burkholderU p)
    (fun s r hs hr => abs_burkholderU_le hp hs hr) (hXk n le_rfl) hYn
  have hV : ∫ ω, ‖X n ω‖ ^ p ∂μ - β ^ p * ∫ ω, ‖Y n ω‖ ^ p ∂μ ≤ 0 := by
    rw [← integral_const_mul, ← integral_sub hIX (hIY.const_mul _)]
    exact (integral_mono (hIX.sub (hIY.const_mul _)) hIU
      fun ω => burkholderU_ge hp (norm_nonneg _) (norm_nonneg _)).trans hEU
  -- back to `L^p` norms
  rw [(hXk n le_rfl).eLpNorm_eq_integral_rpow_norm hq0 hqt,
    hYn.eLpNorm_eq_integral_rpow_norm hq0 hqt, hqr, ← ENNReal.ofReal_mul hβ.le]
  apply ENNReal.ofReal_le_ofReal
  have hIXnn : 0 ≤ ∫ ω, ‖X n ω‖ ^ p ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hIYnn : 0 ≤ ∫ ω, ‖Y n ω‖ ^ p ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg _) _
  calc (∫ ω, ‖X n ω‖ ^ p ∂μ) ^ p⁻¹ ≤ (β ^ p * ∫ ω, ‖Y n ω‖ ^ p ∂μ) ^ p⁻¹ :=
        Real.rpow_le_rpow hIXnn (by linarith) (inv_nonneg.2 hp0.le)
    _ = β * (∫ ω, ‖Y n ω‖ ^ p ∂μ) ^ p⁻¹ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hβ.le _) hIYnn, Real.rpow_rpow_inv hβ.le hp0.ne']

/-- **Burkholder's inequality** (Burkholder 1984; Osękowski, *Sharp martingale and semimartingale
inequalities* (2012), Theorem 3.5; Cassese, Theorem 2.3 (1)): for martingales `X`, `Y` with values
in a separable real Hilbert space, started at `0`, with `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost
surely, and `p > 1`, `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}`, `p* = max (p, p / (p − 1))`.

Proved by Burkholder's method, as in Osękowski's proof: Burkholder's function
`U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}` (`burkholderU`) majorizes
`V (x, y) = |x|^p − (p* − 1)^p |y|^p` (`burkholderU_ge`), and satisfies
`U (x + h, y + k) ≤ U (x, y) + ⟨U_x (x, y), h⟩ + ⟨U_y (x, y), k⟩` whenever `|h| ≤ |k|`, because
`t ↦ U (x + t h, y + t k)` is concave (computed through `ψ`, at the non-smooth points `x = 0`,
`y = 0` by smoothing the norms and passing to the limit). Taking expectations and conditioning on
`ℱ_{n−1}` (pull-out property) gives `E U (X_n, Y_n) ≤ E U (X_{n−1}, Y_{n−1}) ≤ … ≤ U (0, 0) = 0`,
hence `E V (X_n, Y_n) ≤ 0`. If `‖Y_n‖_p = ∞` the right side is `∞`; otherwise every `Y_k`, `X_k`
(`k ≤ n`) is in `L^p`, which makes every term integrable.

Departure from the source's proof (mechanics of one step, reason 2): at the points where
`U (x + t h, y + t k)` is not differentiable in `t`, the concavity is obtained by smoothing the
norms (`√(|z|² + ε²)`) and letting `ε → 0`, instead of gluing concave pieces at the kinks, for
which Mathlib has no lemma. The separability of `H` is not used. -/
theorem inequality {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ) :
    eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (Y n) (ENNReal.ofReal p) μ :=
  inequality_of_subordinate hp hX hY hX0 hY0 hsub n

/-! ### Burkholder's square function inequality -/

section SquareFunction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ}

omit [IsProbabilityMeasure μ] in
/-- The image of a martingale under a continuous linear map is a martingale. -/
private theorem martingale_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {M : ℕ → Ω → E} (hM : Martingale M ℱ μ) (T : E →L[ℝ] F) :
    Martingale (fun m ω => T (M m ω)) ℱ μ := by
  refine ⟨fun m => T.continuous.comp_stronglyMeasurable (hM.stronglyAdapted m),
    fun i j hij => ?_⟩
  filter_upwards [T.comp_condExp_comm (m := ℱ i) (hM.integrable j), hM.condExp_ae_eq hij]
    with ω h1 h2
  change μ[T ∘ M j | ℱ i] ω = T (M i ω)
  rw [← h1, Function.comp_apply, h2]

/-- A martingale stopped at the deterministic time `j`. -/
private theorem martingale_stopped {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {X : ℕ → Ω → E} (hX : Martingale X ℱ μ) (j : ℕ) :
    Martingale (fun m => X (min j m)) ℱ μ := by
  refine martingale_nat (fun m => (hX.stronglyAdapted (min j m)).mono (ℱ.mono (min_le_right _ _)))
    (fun m => hX.integrable _) fun m => ?_
  rcases le_or_gt j m with h | h
  · simp only [min_eq_left h, min_eq_left (h.trans (Nat.le_succ m))]
    rw [condExp_of_stronglyMeasurable (ℱ.le m) ((hX.stronglyAdapted j).mono (ℱ.mono h))
      (hX.integrable j)]
  · simp only [min_eq_right h.le, min_eq_right (Nat.succ_le_of_lt h)]
    exact (hX.condExp_ae_eq (Nat.le_succ m)).symm

omit [IsProbabilityMeasure μ] in
private theorem martingale_finset_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (s : Finset ι) {M : ι → ℕ → Ω → E}
    (hM : ∀ i ∈ s, Martingale (M i) ℱ μ) :
    Martingale (fun m ω => ∑ i ∈ s, M i m ω) ℱ μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert martingale_zero E ℱ μ using 1
    funext m ω; simp
  | insert a s ha ih =>
    have := (hM a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hM i (Finset.mem_insert_of_mem hi))
    convert this using 1
    funext m ω; simp [Finset.sum_insert ha]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem norm_sum_single {n : ℕ} (v : Fin n → H) :
    ‖∑ i : Fin n, PiLp.single 2 (β := fun _ : Fin (n + 1) => H) (Fin.castSucc i) (v i)‖ =
      √(∑ i : Fin n, ‖v i‖ ^ 2) := by
  classical
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_castSucc]
  congr 1
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.ofLp_single, Pi.single_apply,
    Fin.castSucc_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [(Fin.castSucc_ne_last _).symm]

/-- Burkholder's square function inequality without the separability of `H`. -/
theorem squareFunction_of_martingale {X : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) :
    eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2))
            (ENNReal.ofReal p) μ := by
  classical
  -- the Hilbert space `H^{n+1}` with the `ℓ²` norm, and its coordinate embeddings
  let L : Fin (n + 1) → H →L[ℝ] PiLp 2 (fun _ : Fin (n + 1) => H) := fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => H)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => H) i)
  have hL : ∀ i x, L i x = PiLp.single 2 (β := fun _ : Fin (n + 1) => H) i x := fun _ _ => rfl
  -- `A_m = X_{n ∧ m} e_n` and `Z_m = Σ_{i < n} (X_{(i+1) ∧ m} − X_{i ∧ m}) e_i`
  set A : ℕ → Ω → PiLp 2 (fun _ : Fin (n + 1) => H) :=
    fun m ω => L (Fin.last n) (X (min n m) ω) with hAdef
  set Z : ℕ → Ω → PiLp 2 (fun _ : Fin (n + 1) => H) := fun m ω =>
    ∑ i : Fin n, L (Fin.castSucc i) (X (min ((i : ℕ) + 1) m) ω - X (min (i : ℕ) m) ω) with hZdef
  have hA : Martingale A ℱ μ := martingale_clm (martingale_stopped hX n) _
  have hZ : Martingale Z ℱ μ := martingale_finset_sum Finset.univ fun i _ =>
    martingale_clm ((martingale_stopped hX ((i : ℕ) + 1)).sub (martingale_stopped hX i)) _
  have hA0 : ∀ ω, A 0 ω = 0 := fun ω => by simp [hAdef, hX0]
  have hZ0 : ∀ ω, Z 0 ω = 0 := fun ω => by simp [hZdef]
  -- the increments: `‖dZ_m‖ = ‖dA_m‖ = 1_{m < n} ‖dX_m‖`
  have hinc : ∀ m ω, ‖Z (m + 1) ω - Z m ω‖ = ‖A (m + 1) ω - A m ω‖ := by
    intro m ω
    have hw : ∀ i : ℕ, (X (min (i + 1) (m + 1)) ω - X (min i (m + 1)) ω) -
        (X (min (i + 1) m) ω - X (min i m) ω) = if i = m then X (m + 1) ω - X m ω else 0 := by
      intro i
      rcases lt_trichotomy i m with h | rfl | h
      · rw [ite_eq_right h.ne, min_eq_left (by omega : i + 1 ≤ m + 1),
          min_eq_left (by omega : i ≤ m + 1),
          min_eq_left (by omega : i + 1 ≤ m), min_eq_left (by omega : i ≤ m)]
        simp
      · rw [ite_eq_left rfl, min_self, min_eq_left (by omega : i ≤ i + 1),
          min_eq_right (by omega : i ≤ i + 1), min_self]
        simp
      · rw [ite_eq_right h.ne', min_eq_right (by omega : m + 1 ≤ i + 1),
          min_eq_right (by omega : m + 1 ≤ i), min_eq_right (by omega : m ≤ i + 1),
          min_eq_right (by omega : m ≤ i)]
        simp
    have hZd : Z (m + 1) ω - Z m ω = ∑ i : Fin n, PiLp.single 2 (β := fun _ : Fin (n + 1) => H)
        (Fin.castSucc i) (if (i : ℕ) = m then X (m + 1) ω - X m ω else 0) := by
      simp only [hZdef, ← Finset.sum_sub_distrib, hL, ← PiLp.single_sub, hw]
    rw [hZd, norm_sum_single]
    simp only [hAdef, hL, ← PiLp.single_sub, PiLp.norm_single]
    rcases lt_or_ge m n with h | h
    · rw [min_eq_right (by omega : m + 1 ≤ n), min_eq_right h.le]
      have : ∑ i : Fin n, ‖(if (i : ℕ) = m then X (m + 1) ω - X m ω else 0)‖ ^ 2 =
          ‖X (m + 1) ω - X m ω‖ ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun i => ‖(if i = m then X (m + 1) ω - X m ω else 0)‖ ^ 2) n,
          Finset.sum_eq_single m (fun b _ hb => by simp [hb])
            (fun hm => absurd (Finset.mem_range.2 h) hm)]
        simp
      rw [this, Real.sqrt_sq (norm_nonneg _)]
    · rw [min_eq_left (by omega : n ≤ m + 1), min_eq_left h]
      have : ∑ i : Fin n, ‖(if (i : ℕ) = m then X (m + 1) ω - X m ω else 0)‖ ^ 2 = 0 :=
        Finset.sum_eq_zero fun i _ => by
          have := i.isLt
          simp [show (i : ℕ) ≠ m by omega]
      rw [this]; simp
  -- at time `n`: `‖A_n‖ = ‖X_n‖` and `‖Z_n‖ = 𝒮_n X`
  have hAn : ∀ ω, ‖A n ω‖ = ‖X n ω‖ := fun ω => by simp [hAdef, hL, PiLp.norm_single]
  have hZn : ∀ ω, ‖Z n ω‖ = √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2) := by
    intro ω
    simp only [hZdef, hL]
    rw [norm_sum_single, ← Fin.sum_univ_eq_sum_range (fun k => ‖X (k + 1) ω - X k ω‖ ^ 2) n]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have := i.isLt
    rw [min_eq_left (by omega : (i : ℕ) + 1 ≤ n), min_eq_left (by omega : (i : ℕ) ≤ n)]
  have eA : eLpNorm (A n) (ENNReal.ofReal p) μ = eLpNorm (X n) (ENNReal.ofReal p) μ := by
    rw [← eLpNorm_norm (A n) (hA.integrable n).aestronglyMeasurable,
      ← eLpNorm_norm (X n) (hX.integrable n).aestronglyMeasurable]
    simp only [hAn]
  have eZ : eLpNorm (Z n) (ENNReal.ofReal p) μ = eLpNorm
      (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ := by
    rw [← eLpNorm_norm (Z n) (hZ.integrable n).aestronglyMeasurable]
    simp only [hZn]
  refine ⟨?_, ?_⟩
  · have := inequality_of_subordinate hp hZ hA hZ0 hA0
      (fun m => Eventually.of_forall fun ω => (hinc m ω).le) n
    rwa [eZ, eA] at this
  · have := inequality_of_subordinate hp hA hZ hA0 hZ0
      (fun m => Eventually.of_forall fun ω => (hinc m ω).ge) n
    rwa [eZ, eA] at this

/-- **Burkholder's square function inequality** (Burkholder; Osękowski, *Sharp martingale and
semimartingale inequalities* (2012), Theorem 8.6; Cassese, Theorem 2.3 (2)): for a martingale `X`
with values in a separable real Hilbert space, started at `0`, `p > 1` and
`𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`,
`‖𝒮_n X‖_{L^p} ≤ (p* − 1) ‖X_n‖_{L^p}` and `‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`.

Proved by the standard derivation from Burkholder's inequality (`inequality`): in the
Hilbert space `H^{n+1}` with the `ℓ²` norm, the martingale `Z_m = Σ_{k < n} dX_{k+1} 1_{k < m} e_k`
has `‖Z_n‖ = 𝒮_n X` and `‖dZ_m‖ = ‖dX_{m+1}‖ 1_{m < n}`, which is also the norm of the increments
of `A_m = X_{n ∧ m} e_n`; each of the two martingales is differentially subordinate to the other.

Departure from the source's proof (representation, reason 3): the `ℓ²(H)`-valued martingale
`Σ_k dX_k e_k` is replaced by its truncation to `H^{n+1}` (`PiLp 2`), since `n` is fixed; the
argument is the same. The separability of `H` is not used. -/
theorem squareFunction {X : ℕ → Ω → H} [TopologicalSpace.SeparableSpace H] {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) :
    eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2))
            (ENNReal.ofReal p) μ :=
  squareFunction_of_martingale hp hX hX0 n

end SquareFunction

end External.Burkholder
