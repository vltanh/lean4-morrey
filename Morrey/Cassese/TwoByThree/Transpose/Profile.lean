module

public import Morrey.Cassese.TwoByThree.Transpose.Potential
public import Morrey.Cassese.TwoByThree.Polynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Corollary 5.3: the profile `φ = r^{5/2} cos 3θ`

`φ (x, y) = (x³ − 3 x y²) (x² + y²)^{−1/4}` (`tbt3Phi`). Its partial derivatives stay in the class
`P · s^α` (`P` a polynomial, `s = x² + y²`): `∂ₖ (P s^α) = (∂ₖP · s + 2α xₖ P) s^{α−1}`
(`tbt3_D1_F`), so the third derivatives `a, b, c, e = φ_xxx, φ_xxy, φ_xyy, φ_yyy` are
`(A, B, C, E) s^{−13/4}` with explicit sextics. Hence, on `s > 0`, for `T = tbt3T a b c e`:
`q₃ (T) ≤ −(75/8) / s` and `|T|⁴ ≤ 4·10⁶ / s` (`tbt3_bulk_bounds`).

Helpers are prefixed `tbt3_`.
-/

@[expose] public section

open MeasureTheory MvPolynomial
open scoped Matrix

namespace Cassese

/-- `s = x² + y²`. -/
noncomputable def tbt3S : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2

/-- `x³ − 3 x y² = Re (z³)`. -/
noncomputable def tbt3P0 : MvPolynomial (Fin 2) ℝ := X 0 ^ 3 - C 3 * X 0 * X 1 ^ 2

/-- The recursion `P ↦ ∂ₖP · s + 2α xₖ P` of `∂ₖ (P s^α)`. -/
noncomputable def tbt3Tk (k : Fin 2) (α : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  pderiv k p * tbt3S + C (2 * α) * X k * p

/-- The class `P · s^α`. -/
noncomputable def tbt3F (p : MvPolynomial (Fin 2) ℝ) (α : ℝ) (z : Fin 2 → ℝ) : ℝ :=
  eval z p * eval z tbt3S ^ α

/-- The profile `φ = r^{5/2} cos 3θ`. -/
noncomputable def tbt3Phi : (Fin 2 → ℝ) → ℝ := tbt3F tbt3P0 (-1 / 4)

@[simp] theorem tbt3_pderiv_ofNat (i : Fin 2) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (no_index (OfNat.ofNat n : MvPolynomial (Fin 2) ℝ)) = 0 := by
  have : (OfNat.ofNat n : MvPolynomial (Fin 2) ℝ) = ((n : ℕ) : MvPolynomial (Fin 2) ℝ) :=
    (Nat.cast_ofNat).symm
  rw [this]; exact Derivation.map_natCast _ _

theorem tbt3_eval_S (z : Fin 2 → ℝ) : eval z tbt3S = z 0 ^ 2 + z 1 ^ 2 := by simp [tbt3S]

/-- The derivative of a polynomial function. -/
theorem tbt3_hasFDerivAt_eval (p : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    HasFDerivAt (fun z => eval z p)
      (∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i)
      x := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const a x
  | add p q hp hq =>
    convert hp.add hq using 1
    · funext z; simp
    · simp [add_smul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have hi : HasFDerivAt (fun z : Fin 2 → ℝ => z i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) x := hasFDerivAt_apply i x
    convert hp.mul hi using 1
    · funext z; simp
    · ext v
      fin_cases i <;> simp [Fin.sum_univ_two, pderiv_X] <;> ring

theorem tbt3_fderiv_eval (p : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) (k : Fin 2) :
    fderiv ℝ (fun z => eval z p) x (Pi.single k 1) = eval x (pderiv k p) := by
  rw [(tbt3_hasFDerivAt_eval p x).fderiv]
  fin_cases k <;> simp [Fin.sum_univ_two]

/-- `∂ₖ (P s^α) = (∂ₖP · s + 2α xₖ P) s^{α−1}` where `s > 0`. -/
theorem tbt3_D1_F (p : MvPolynomial (Fin 2) ℝ) (α : ℝ) (k : Fin 2) {x : Fin 2 → ℝ}
    (hx : 0 < eval x tbt3S) : tbt3D1 (tbt3F p α) k x = tbt3F (tbt3Tk k α p) (α - 1) x := by
  have hS := tbt3_hasFDerivAt_eval tbt3S x
  have hP := tbt3_hasFDerivAt_eval p x
  have hR := hS.rpow_const (p := α) (Or.inl hx.ne')
  have h := hP.mul hR
  simp only [tbt3D1]
  rw [show tbt3F p α = (fun z => eval z p) * (fun z => eval z tbt3S ^ α) from rfl, h.fderiv]
  simp only [tbt3F]
  have e1 : eval x tbt3S ^ α = eval x tbt3S * eval x tbt3S ^ (α - 1) := by
    rw [Real.rpow_sub_one hx.ne']; field_simp
  fin_cases k <;>
  · simp [Fin.sum_univ_two, tbt3Tk, tbt3S, pderiv_X] at e1 ⊢
    rw [e1]; ring

theorem tbt3_isOpen_pos : IsOpen {z : Fin 2 → ℝ | 0 < eval z tbt3S} := by
  simp only [tbt3_eval_S]
  exact isOpen_lt continuous_const (by fun_prop)

theorem tbt3_D1_F_eqOn (p : MvPolynomial (Fin 2) ℝ) (α β : ℝ) (hβ : β = α - 1) (k : Fin 2) :
    Set.EqOn (tbt3D1 (tbt3F p α) k) (tbt3F (tbt3Tk k α p) β) {z | 0 < eval z tbt3S} :=
  fun _ hx => by rw [hβ]; exact tbt3_D1_F p α k hx

/-- The third derivatives of `φ` on `s > 0`. -/
theorem tbt3_D3_Phi (i j k : Fin 2) {x : Fin 2 → ℝ} (hx : 0 < eval x tbt3S) :
    tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi j) i) k x =
      tbt3F (tbt3Tk k (-9 / 4) (tbt3Tk i (-5 / 4) (tbt3Tk j (-1 / 4) tbt3P0))) (-13 / 4) x := by
  have U := tbt3_isOpen_pos
  have h1 := tbt3_D1_F_eqOn tbt3P0 (-1 / 4) (-5 / 4) (by norm_num) j
  have h2 := tbt3_D1_eqOn U h1 i
  have h2' := h2.trans (tbt3_D1_F_eqOn _ (-5 / 4) (-9 / 4) (by norm_num) i)
  have h3 := tbt3_D1_eqOn U h2' k
  exact (h3.trans (tbt3_D1_F_eqOn _ (-9 / 4) (-13 / 4) (by norm_num) k)) hx

theorem tbt3_q3_T (a b c e : ℝ) :
    q3 (tbt3T a b c e) = 4 * (b * c - a * e) ^ 2 - 16 * (b ^ 2 - a * c) * (c ^ 2 - b * e) := by
  rw [tbt_q3_eq]; simp [tbt3T]; ring

theorem tbt3_frobSq_T (a b c e : ℝ) :
    frobSq (tbt3T a b c e) = 2 * a ^ 2 + 6 * b ^ 2 + 6 * c ^ 2 + 2 * e ^ 2 := by
  simp [frobSq, tbt3T, Fin.sum_univ_two, Fin.sum_univ_three]; ring

theorem tbt3_H_bound {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    100 * (u + v) ^ 6 ≤ 10985 * u ^ 6 + 112638 * u ^ 5 * v + 616842 * u ^ 4 * v ^ 2 -
      185760 * u ^ 3 * v ^ 3 + 362313 * u ^ 2 * v ^ 4 - 486 * u * v ^ 5 + 20412 * v ^ 6 := by
  have q1 : 0 ≤ 615342 * u ^ 2 - 187760 * u * v + 359000 * v ^ 2 := by
    have h1 := sq_nonneg (615342 * u - 93880 * v)
    have h2 := sq_nonneg v
    nlinarith
  have q2 : 0 ≤ 1813 * u ^ 2 - 1086 * u * v + 20312 * v ^ 2 := by
    have h1 := sq_nonneg (1813 * u - 543 * v)
    have h2 := sq_nonneg v
    nlinarith
  have e : (10985 * u ^ 6 + 112638 * u ^ 5 * v + 616842 * u ^ 4 * v ^ 2 -
      185760 * u ^ 3 * v ^ 3 + 362313 * u ^ 2 * v ^ 4 - 486 * u * v ^ 5 + 20412 * v ^ 6) -
      100 * (u + v) ^ 6 = 10885 * u ^ 6 + 112038 * u ^ 5 * v +
        u ^ 2 * v ^ 2 * (615342 * u ^ 2 - 187760 * u * v + 359000 * v ^ 2) +
        v ^ 4 * (1813 * u ^ 2 - 1086 * u * v + 20312 * v ^ 2) := by ring
  have : 0 ≤ 10885 * u ^ 6 + 112038 * u ^ 5 * v +
        u ^ 2 * v ^ 2 * (615342 * u ^ 2 - 187760 * u * v + 359000 * v ^ 2) +
        v ^ 4 * (1813 * u ^ 2 - 1086 * u * v + 20312 * v ^ 2) := by positivity
  linarith

theorem tbt3_G_bound {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (751 * u ^ 3 + 19578 * u ^ 2 * v - 9297 * u * v ^ 2 + 2676 * v ^ 3) ^ 2 ≤
      19578 ^ 2 * (u + v) ^ 6 := by
  set G := 751 * u ^ 3 + 19578 * u ^ 2 * v - 9297 * u * v ^ 2 + 2676 * v ^ 3
  have huv := mul_nonneg hu hv
  have h1 : G ≤ 19578 * (u + v) ^ 3 := by
    have : 19578 * (u + v) ^ 3 - G = 18827 * u ^ 3 + 39156 * u ^ 2 * v + 68031 * u * v ^ 2 +
        16902 * v ^ 3 := by simp only [G]; ring
    have : 0 ≤ 18827 * u ^ 3 + 39156 * u ^ 2 * v + 68031 * u * v ^ 2 + 16902 * v ^ 3 := by
      positivity
    linarith
  have h2 : -(19578 * (u + v) ^ 3) ≤ G := by
    have : G + 19578 * (u + v) ^ 3 = 20329 * u ^ 3 + 78312 * u ^ 2 * v + 49437 * u * v ^ 2 +
        22254 * v ^ 3 := by simp only [G]; ring
    have : 0 ≤ 20329 * u ^ 3 + 78312 * u ^ 2 * v + 49437 * u * v ^ 2 + 22254 * v ^ 3 := by
      positivity
    linarith
  have h3 : G ^ 2 ≤ (19578 * (u + v) ^ 3) ^ 2 := sq_le_sq' h2 h1
  calc G ^ 2 ≤ (19578 * (u + v) ^ 3) ^ 2 := h3
    _ = 19578 ^ 2 * (u + v) ^ 6 := by ring

/-- `s^{13/4} (φ_xxx, φ_xxy, φ_xyy, φ_yyy)`. -/
noncomputable def tbt3A (x y : ℝ) : ℝ := 3 / 8 * (5 * x ^ 6 + 13 * x ^ 4 * y ^ 2 - 24 * x ^ 2 * y ^ 4 + 28 * y ^ 6)
noncomputable def tbt3B (x y : ℝ) : ℝ := x * y * (13 * x ^ 4 + 151 * x ^ 2 * y ^ 2 - 42 * y ^ 4) / 8
noncomputable def tbt3C (x y : ℝ) : ℝ := -(26 * x ^ 6 + 215 * x ^ 4 * y ^ 2 + 27 * x ^ 2 * y ^ 4 + 18 * y ^ 6) / 8
noncomputable def tbt3E (x y : ℝ) : ℝ := 3 / 8 * (x * y * (58 * x ^ 4 + x ^ 2 * y ^ 2 + 3 * y ^ 4))

theorem tbt3_q3_identity (x y : ℝ) :
    4 * (tbt3B x y * tbt3C x y - tbt3A x y * tbt3E x y) ^ 2 -
        16 * (tbt3B x y ^ 2 - tbt3A x y * tbt3C x y) * (tbt3C x y ^ 2 - tbt3B x y * tbt3E x y) =
      -(3 / 32) * (x ^ 2 + y ^ 2) ^ 6 * (10985 * (x ^ 2) ^ 6 + 112638 * (x ^ 2) ^ 5 * y ^ 2 +
        616842 * (x ^ 2) ^ 4 * (y ^ 2) ^ 2 - 185760 * (x ^ 2) ^ 3 * (y ^ 2) ^ 3 +
        362313 * (x ^ 2) ^ 2 * (y ^ 2) ^ 4 - 486 * x ^ 2 * (y ^ 2) ^ 5 + 20412 * (y ^ 2) ^ 6) := by
  simp only [tbt3A, tbt3B, tbt3C, tbt3E]; ring

theorem tbt3_frob_identity (x y : ℝ) :
    2 * tbt3A x y ^ 2 + 6 * tbt3B x y ^ 2 + 6 * tbt3C x y ^ 2 + 2 * tbt3E x y ^ 2 =
      3 / 32 * (x ^ 2 + y ^ 2) ^ 3 * (751 * (x ^ 2) ^ 3 + 19578 * (x ^ 2) ^ 2 * y ^ 2 -
        9297 * x ^ 2 * (y ^ 2) ^ 2 + 2676 * (y ^ 2) ^ 3) := by
  simp only [tbt3A, tbt3B, tbt3C, tbt3E]; ring

/-- `4 (BC − AE)² − 16 (B² − AC)(C² − BE) ≤ −(75/8) s¹²`. -/
theorem tbt3_q3_poly_le (x y : ℝ) :
    4 * (tbt3B x y * tbt3C x y - tbt3A x y * tbt3E x y) ^ 2 -
        16 * (tbt3B x y ^ 2 - tbt3A x y * tbt3C x y) * (tbt3C x y ^ 2 - tbt3B x y * tbt3E x y) ≤
      -(75 / 8) * (x ^ 2 + y ^ 2) ^ 12 := by
  rw [tbt3_q3_identity]
  have h := tbt3_H_bound (sq_nonneg x) (sq_nonneg y)
  have h6 : 0 ≤ (x ^ 2 + y ^ 2) ^ 6 := by positivity
  have := mul_le_mul_of_nonneg_left h h6
  have e : (x ^ 2 + y ^ 2) ^ 12 = (x ^ 2 + y ^ 2) ^ 6 * (x ^ 2 + y ^ 2) ^ 6 := by ring
  rw [e]; nlinarith

theorem tbt3_frob_poly_le (x y : ℝ) :
    (2 * tbt3A x y ^ 2 + 6 * tbt3B x y ^ 2 + 6 * tbt3C x y ^ 2 + 2 * tbt3E x y ^ 2) ^ 2 ≤
      4000000 * (x ^ 2 + y ^ 2) ^ 12 := by
  rw [tbt3_frob_identity]
  have h := tbt3_G_bound (sq_nonneg x) (sq_nonneg y)
  have h6 : 0 ≤ (x ^ 2 + y ^ 2) ^ 6 := by positivity
  have e : (3 / 32 * (x ^ 2 + y ^ 2) ^ 3 * (751 * (x ^ 2) ^ 3 + 19578 * (x ^ 2) ^ 2 * y ^ 2 -
        9297 * x ^ 2 * (y ^ 2) ^ 2 + 2676 * (y ^ 2) ^ 3)) ^ 2 =
      9 / 1024 * (x ^ 2 + y ^ 2) ^ 6 * (751 * (x ^ 2) ^ 3 + 19578 * (x ^ 2) ^ 2 * y ^ 2 -
        9297 * x ^ 2 * (y ^ 2) ^ 2 + 2676 * (y ^ 2) ^ 3) ^ 2 := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_left h h6
  have e2 : (x ^ 2 + y ^ 2) ^ 12 = (x ^ 2 + y ^ 2) ^ 6 * (x ^ 2 + y ^ 2) ^ 6 := by ring
  rw [e2]; nlinarith

/-- The bulk bounds: with `a, b, c, e` the third derivatives of `φ` at `x ≠ 0` and
`s = |x|²`, `q₃ (T) ≤ −(75/8) / s` and `|T|⁴ ≤ 4·10⁶ / s`. -/
theorem tbt3_bulk_bounds {x : Fin 2 → ℝ} (hx : 0 < eval x tbt3S) :
    q3 (tbt3T (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 0) 0) 0 x) (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 0) 0 x)
        (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 1) 0 x) (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 1) 1 x)) ≤
        -(75 / 8) / eval x tbt3S ∧
      frobSq (tbt3T (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 0) 0) 0 x)
        (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 0) 0 x) (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 1) 0 x)
        (tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 1) 1 x)) ^ 2 ≤ 4000000 / eval x tbt3S := by
  have hs : eval x tbt3S = x 0 ^ 2 + x 1 ^ 2 := tbt3_eval_S x
  have hpos : 0 < x 0 ^ 2 + x 1 ^ 2 := hs ▸ hx
  obtain ⟨ρ, hρ0, hρ4, ha, hb, hc, he⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 4 * (x 0 ^ 2 + x 1 ^ 2) ^ 13 = 1 ∧
      tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 0) 0) 0 x = tbt3A (x 0) (x 1) * ρ ∧
      tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 0) 0 x = tbt3B (x 0) (x 1) * ρ ∧
      tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 1) 0 x = tbt3C (x 0) (x 1) * ρ ∧
      tbt3D1 (tbt3D1 (tbt3D1 tbt3Phi 1) 1) 1 x = tbt3E (x 0) (x 1) * ρ := by
    refine ⟨eval x tbt3S ^ (-13 / 4 : ℝ), Real.rpow_pos_of_pos hx _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hs, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_natCast, ←
        Real.rpow_add hx]
      norm_num
    · rw [tbt3_D3_Phi 0 0 0 hx, tbt3F]; congr 1
      simp [tbt3Tk, tbt3S, tbt3P0, pderiv_X, tbt3A]; ring
    · rw [tbt3_D3_Phi 0 1 0 hx, tbt3F]; congr 1
      simp [tbt3Tk, tbt3S, tbt3P0, pderiv_X, tbt3B]; ring
    · rw [tbt3_D3_Phi 1 1 0 hx, tbt3F]; congr 1
      simp [tbt3Tk, tbt3S, tbt3P0, pderiv_X, tbt3C]; ring
    · rw [tbt3_D3_Phi 1 1 1 hx, tbt3F]; congr 1
      simp [tbt3Tk, tbt3S, tbt3P0, pderiv_X, tbt3E]; ring
  have q := tbt3_q3_poly_le (x 0) (x 1)
  have f := tbt3_frob_poly_le (x 0) (x 1)
  rw [ha, hb, hc, he, hs, tbt3_q3_T, tbt3_frobSq_T]
  set S := x 0 ^ 2 + x 1 ^ 2
  set A := tbt3A (x 0) (x 1)
  set B := tbt3B (x 0) (x 1)
  set C := tbt3C (x 0) (x 1)
  set E := tbt3E (x 0) (x 1)
  have hρS : ρ ^ 4 * S ^ 12 = 1 / S := by
    field_simp; linear_combination hρ4
  have hρ4' : 0 ≤ ρ ^ 4 := by positivity
  constructor
  · have e : 4 * (B * ρ * (C * ρ) - A * ρ * (E * ρ)) ^ 2 -
        16 * ((B * ρ) ^ 2 - A * ρ * (C * ρ)) * ((C * ρ) ^ 2 - B * ρ * (E * ρ)) =
        ρ ^ 4 * (4 * (B * C - A * E) ^ 2 - 16 * (B ^ 2 - A * C) * (C ^ 2 - B * E)) := by ring
    have h1 := mul_le_mul_of_nonneg_left q hρ4'
    have h2 : ρ ^ 4 * (-(75 / 8) * S ^ 12) = -(75 / 8) / S := by
      rw [show ρ ^ 4 * (-(75 / 8) * S ^ 12) = -(75 / 8) * (ρ ^ 4 * S ^ 12) by ring, hρS]
      ring
    rw [e]; linarith
  · have e : (2 * (A * ρ) ^ 2 + 6 * (B * ρ) ^ 2 + 6 * (C * ρ) ^ 2 + 2 * (E * ρ) ^ 2) ^ 2 =
        ρ ^ 4 * (2 * A ^ 2 + 6 * B ^ 2 + 6 * C ^ 2 + 2 * E ^ 2) ^ 2 := by ring
    have h1 := mul_le_mul_of_nonneg_left f hρ4'
    have h2 : ρ ^ 4 * (4000000 * S ^ 12) = 4000000 / S := by
      rw [show ρ ^ 4 * (4000000 * S ^ 12) = 4000000 * (ρ ^ 4 * S ^ 12) by ring, hρS]
      ring
    rw [e]; linarith

end Cassese
