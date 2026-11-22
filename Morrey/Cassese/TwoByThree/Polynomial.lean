module

public import Morrey.Cassese.TwoByThree.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Section 5: `q₃` and `q_{δ,Λ}` are homogeneous quartic polynomials

`IsHomogeneousPolynomial` is closed under sums, products and scalar multiples
(`IsHomogeneousPolynomial.add`, `IsHomogeneousPolynomial.mul`,
`IsHomogeneousPolynomial.const_mul`, in `Toolkit`; differences and squares here), and contains
the linear functions of the entries (`tbt_ihp_linear`). From these, `q₃ ∘ π` and `q_{δ,Λ}` are
homogeneous of degree `4` (`tbt_ihp_qDeltaLambda`), and `q₃` is `4`-homogeneous and smooth
(and continuous, `tbt_continuous_q3`).

Helpers are prefixed `tbt_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ComplexConjugate

namespace Cassese

variable {d m : ℕ}

theorem tbt_ihp_sub {n : ℕ} {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : IsHomogeneousPolynomial n f) (hg : IsHomogeneousPolynomial n g) :
    IsHomogeneousPolynomial n fun A => f A - g A := by
  obtain ⟨P, hP, hPf⟩ := hf
  obtain ⟨Q, hQ, hQg⟩ := hg
  exact ⟨P - Q, hP.sub hQ, fun A => by simp only [hPf A, hQg A, map_sub]⟩

theorem tbt_ihp_sq {n : ℕ} {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : IsHomogeneousPolynomial n f) : IsHomogeneousPolynomial (2 * n) fun A => f A ^ 2 := by
  have := hf.mul hf
  rw [show n + n = 2 * n by ring] at this
  exact this.congr fun A => by ring

/-- A linear function of the entries is a homogeneous polynomial of degree `1`. -/
theorem tbt_ihp_linear (ℓ : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (hadd : ∀ A B, ℓ (A + B) = ℓ A + ℓ B) (hsmul : ∀ (c : ℝ) A, ℓ (c • A) = c * ℓ A) :
    IsHomogeneousPolynomial 1 ℓ := by
  let L : Matrix (Fin d) (Fin m) ℝ →+ ℝ := ⟨⟨ℓ, by simpa using hsmul 0 0⟩, hadd⟩
  refine ⟨∑ ij : Fin d × Fin m, MvPolynomial.C (ℓ (Matrix.single ij.1 ij.2 1)) *
    MvPolynomial.X ij, MvPolynomial.IsHomogeneous.sum _ _ _ fun ij _ =>
      MvPolynomial.isHomogeneous_C_mul_X _ _, fun A => ?_⟩
  simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  have : ℓ (∑ i, ∑ j, Matrix.single i j (A i j)) = L (∑ i, ∑ j, Matrix.single i j (A i j)) := rfl
  rw [this, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ℓ (Matrix.single i j (A i j)) = _
  rw [show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], hsmul, mul_comm]

/-- Composition with a map whose entries are linear. -/
theorem tbt_ihp_comp {d' m' n : ℕ} {g : Matrix (Fin d') (Fin m') ℝ → ℝ}
    (hg : IsHomogeneousPolynomial n g)
    (T : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d') (Fin m') ℝ)
    (hT : ∀ i j, IsHomogeneousPolynomial 1 fun A => T A i j) :
    IsHomogeneousPolynomial n fun A => g (T A) := by
  obtain ⟨P, hP, hPg⟩ := hg
  choose Q hQ hQT using hT
  refine ⟨MvPolynomial.bind₁ (fun ij : Fin d' × Fin m' => Q ij.1 ij.2) P, ?_, fun A => ?_⟩
  · have := hP.aeval (fun ij : Fin d' × Fin m' => Q ij.1 ij.2) (fun ij => hQ ij.1 ij.2)
    rwa [one_mul] at this
  · show g (T A) = MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij => A ij.1 ij.2)
      (MvPolynomial.bind₁ (fun ij : Fin d' × Fin m' => Q ij.1 ij.2) P)
    rw [hPg (T A), MvPolynomial.eval₂Hom_bind₁]
    show MvPolynomial.eval₂Hom (RingHom.id ℝ) _ P = _
    congr 2
    funext ij
    exact hQT ij.1 ij.2 A

theorem tbt_ihp_entry (i : Fin d) (j : Fin m) :
    IsHomogeneousPolynomial 1 fun A : Matrix (Fin d) (Fin m) ℝ => A i j :=
  tbt_ihp_linear _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- `q₃` in the entries `B = (a b e; c d f)`, through the real and imaginary parts of
`Z (J B) = (z₀, z₁, z₂)`. -/
theorem tbt_q3_eq (B : Matrix (Fin 2) (Fin 3) ℝ) :
    let z0r := B 0 2 / 2
    let z0i := -(B 1 2 / 2)
    let z1r := (B 0 0 + B 1 1) / 2
    let z1i := -((B 1 0 - B 0 1) / 2)
    let z2r := (B 0 0 - B 1 1) / 2
    let z2i := (B 1 0 + B 0 1) / 2
    q3 B = 4 * ((z0r * z2r - z0i * z2i - (z1r ^ 2 - z1i ^ 2)) ^ 2 +
        (z0r * z2i + z0i * z2r - 2 * z1r * z1i) ^ 2) -
      (z0r ^ 2 + z0i ^ 2 + (z2r ^ 2 + z2i ^ 2) - 2 * (z1r ^ 2 + z1i ^ 2)) ^ 2 := by
  intro z0r z0i z1r z1i z2r z2i
  simp only [q3, quarticQ, zCoord, embedJ, wirtAlpha, wirtBeta, Matrix.of_apply]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im, pow_two]
  norm_num
  simp only [z0r, z0i, z1r, z1i, z2r, z2i]
  ring

/-- `q₃` is a homogeneous quartic polynomial. -/
theorem tbt_ihp_q3 : IsHomogeneousPolynomial 4 q3 := by
  have hl : ∀ (c : Fin 2 → Fin 3 → ℝ), IsHomogeneousPolynomial 1
      fun B : Matrix (Fin 2) (Fin 3) ℝ => ∑ i, ∑ j, c i j * B i j := fun c =>
    tbt_ihp_linear _ (fun A B => by simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib])
      (fun r A => by
        simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
  have h0r := hl ![![0, 0, 1 / 2], ![0, 0, 0]]
  have h0i := hl ![![0, 0, 0], ![0, 0, -(1 / 2)]]
  have h1r := hl ![![1 / 2, 0, 0], ![0, 1 / 2, 0]]
  have h1i := hl ![![0, 1 / 2, 0], ![-(1 / 2), 0, 0]]
  have h2r := hl ![![1 / 2, 0, 0], ![0, -(1 / 2), 0]]
  have h2i := hl ![![0, 1 / 2, 0], ![1 / 2, 0, 0]]
  have hD1 := tbt_ihp_sq (tbt_ihp_sub (tbt_ihp_sub (h0r.mul h2r) (h0i.mul h2i))
    (tbt_ihp_sub (tbt_ihp_sq h1r) (tbt_ihp_sq h1i)))
  have hD2 := tbt_ihp_sq (tbt_ihp_sub ((h0r.mul h2i).add (h0i.mul h2r)) ((h1r.mul h1i).const_mul 2))
  have hH := tbt_ihp_sq (tbt_ihp_sub (((tbt_ihp_sq h0r).add (tbt_ihp_sq h0i)).add
    ((tbt_ihp_sq h2r).add (tbt_ihp_sq h2i))) (((tbt_ihp_sq h1r).add (tbt_ihp_sq h1i)).const_mul 2))
  have := tbt_ihp_sub ((hD1.add hD2).const_mul 4) hH
  refine this.congr fun B => ?_
  rw [tbt_q3_eq]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem tbt_continuous_q3 : Continuous q3 := tbt_ihp_q3.continuous

theorem tbt_ihp_sum {ι : Type*} {n : ℕ} (s : Finset ι)
    (f : ι → Matrix (Fin d) (Fin m) ℝ → ℝ) (h : ∀ i ∈ s, IsHomogeneousPolynomial n (f i)) :
    IsHomogeneousPolynomial n fun A => ∑ i ∈ s, f i A := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun A => by simp⟩
  | insert i s hi ih =>
    refine ((h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr fun A => ?_
    rw [Finset.sum_insert hi]

theorem tbt_ihp_frobSq :
    IsHomogeneousPolynomial 2 fun A : Matrix (Fin d) (Fin m) ℝ => frobSq A :=
  tbt_ihp_sum _ _ fun i _ => tbt_ihp_sum _ _ fun j _ => tbt_ihp_sq (tbt_ihp_entry i j)

theorem tbt_ihp_projL3_entry (i : Fin 2) (j : Fin 3) :
    IsHomogeneousPolynomial 1 fun A => projL3 A i j :=
  tbt_ihp_linear _
    (fun A B => by fin_cases i <;> fin_cases j <;> simp [projL3] <;> ring)
    (fun c A => by fin_cases i <;> fin_cases j <;> simp [projL3] <;> ring)

theorem tbt_ihp_perp_entry (i : Fin 2) (j : Fin 3) :
    IsHomogeneousPolynomial 1 fun A => (A - projL3 A) i j :=
  tbt_ihp_linear _
    (fun A B => by fin_cases i <;> fin_cases j <;> simp [projL3] <;> ring)
    (fun c A => by fin_cases i <;> fin_cases j <;> simp [projL3] <;> ring)

/-- `q_{δ,Λ}` is a homogeneous quartic polynomial, for every `δ`, `Λ`. -/
theorem tbt_ihp_qDeltaLambda (δ Λ : ℝ) : IsHomogeneousPolynomial 4 (qDeltaLambda δ Λ) := by
  have h1 := tbt_ihp_comp tbt_ihp_q3 projL3 tbt_ihp_projL3_entry
  have h2 := tbt_ihp_comp (tbt_ihp_frobSq (d := 2) (m := 3)) projL3 tbt_ihp_projL3_entry
  have h3 := tbt_ihp_comp (tbt_ihp_frobSq (d := 2) (m := 3)) (fun A => A - projL3 A)
    tbt_ihp_perp_entry
  have h4 := (tbt_ihp_sq (h2.add (h3.const_mul (Λ ^ 2)))).const_mul δ
  exact (h1.add h4).congr fun A => rfl

/-- `q̂_{δ,Λ}` is a homogeneous quartic polynomial, for every `δ`, `Λ`. -/
theorem tbt_ihp_qHat (δ Λ : ℝ) : IsHomogeneousPolynomial 4 (qHat δ Λ) :=
  tbt_ihp_comp (tbt_ihp_qDeltaLambda δ Λ) (fun A => Aᵀ) fun i j => tbt_ihp_entry j i

/-- `q₃` is homogeneous of degree `4`: `q₃ (t X) = t⁴ q₃ (X)`. -/
theorem tbt_q3_smul (t : ℝ) (X : Matrix (Fin 2) (Fin 3) ℝ) : q3 (t • X) = t ^ 4 * q3 X := by
  rw [tbt_q3_eq, tbt_q3_eq]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- `X ↦ q₃ (π X)` is smooth, as a function of the entries. -/
theorem tbt_contDiff_q3_projL3 {n : WithTop ℕ∞} :
    ContDiff ℝ n fun X : Fin 2 → Fin 3 → ℝ => q3 (projL3 (Matrix.of X)) := by
  have he : ∀ (i : Fin 2) (j : Fin 3), ContDiff ℝ n fun X : Fin 2 → Fin 3 → ℝ => X i j :=
    fun i j => contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) i j
  simp only [tbt_q3_eq, projL3, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons]
  have h00 := he 0 0; have h01 := he 0 1; have h02 := he 0 2
  have h10 := he 1 0; have h11 := he 1 1; have h12 := he 1 2
  fun_prop

end Cassese
