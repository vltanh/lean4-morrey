module

public import Morrey.Cassese.Square.Torus
public import Morrey.Cassese.Square.Witness
public import Morrey.Cassese.Square.Hessian

/-!
# The witness of Corollary 6.1 on `𝕋^{2n}`

The proof of Corollary 6.1 (TeX lines 2489–2520) takes, on `𝕋^{2n} = 𝕋^n × 𝕋^n`,
`φ (x, y) = Σ_{i,j} sin (x_i − y_j)` and `J = diag (I_n, −I_n)`, and says that "the calculation
of Proposition 6.1 gives" `‖Skew (J D²φ)‖_{L^p (S_q)} / ‖Sym (J D²φ)‖_{L^p (S_q)} ≳_{p,q}
n^{1/2 − 1/q}`. Here `q = 4`, on the unit torus (`ψ (z) = (2π)⁻² φ (2πz)`, `square_corWitness`,
so `D²ψ (z) = D²φ (2πz)`), with `θ = 2πz`:

* `D²ψ = [[−diag r, M], [Mᵀ, −diag c]]` with `M_{ij} = sin (θx_i − θy_j)`, `r_i = Σ_j M_{ij}`,
  `c_j = Σ_i M_{ij}` (`square_corWitness_hessian`, in the uniform form
  `(D²ψ)_{ab} = Q_{ab} sin (θ_a − θ_b) − δ_{ab} Σ_l Q_{al} sin (θ_a − θ_l)`); hence
  `Sym (J D²ψ) = diag (−r, c)` (`square_cor_sym`) and `Skew (J D²ψ) = [[0, M], [−Mᵀ, 0]]`
  (`square_cor_skew`);
* the lower bound (`square_cor_skew_lower`): `Skew (J D²ψ)` has rank at most `4`, so at most four
  nonzero singular values, and `‖K‖_{S_4} ≥ ‖K‖_{S_2} / √2 = ‖M‖_F`; `‖M‖_F ≤ n` and
  `E ‖M‖_F² = n² / 2`, so `‖K‖_{L^p (S_4)} ≥ E ‖M‖_F ≥ E ‖M‖_F² / n = n / 2`;
* the upper bound (`square_cor_sym_upper`): `|r_i| ≤ |Z_y|`, `|c_j| ≤ |Z_x|` with
  `Z_x = Σ_i e^{iθx_i}`, `Z_y = Σ_j e^{iθy_j}`, so `‖Sym (J D²ψ)‖_{S_4} ≤ (2n)^{1/4} max (|Z_x|, |Z_y|)`,
  and `‖Z_x‖_{L^p}, ‖Z_y‖_{L^p} ≤ √(p n)` (the moments `E |Σ_k w_k e^{iθ_k}|^{2m} ≤ m! (Σ w_k²)^m`,
  `square_cor_moment`, as in Proposition 6.1), giving `‖Sym (J D²ψ)‖_{L^p (S_4)} ≤
  2 (2n)^{1/4} √(p n)`.

Helpers have the prefix `square_cor_`.
-/

@[expose] public section

open MeasureTheory Real
open scoped Matrix ENNReal

namespace Cassese

/-- The witness of Corollary 6.1 on the unit torus: the paper's `φ (x, y) = Σ_{i,j} sin (x_i − y_j)`
on `𝕋^{2n}`, rescaled, `ψ (z) = (2π)⁻² φ (2πz)`, so that `D²ψ (z) = D²φ (2πz)`. -/
noncomputable def square_corWitness (n : ℕ) (z : Fin (n + n) → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 2)⁻¹ * ∑ i : Fin n, ∑ j : Fin n,
    Real.sin (2 * Real.pi * (z (Fin.castAdd n i) - z (Fin.natAdd n j)))

/-- `J = diag (I_n, −I_n)`. -/
def square_J (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  Matrix.diagonal fun k => if (k : ℕ) < n then 1 else -1

/-! ### Sums with Kronecker deltas -/

section Delta

variable {N : ℕ}

theorem square_cor_sum_sum_delta_left (g : Fin N → Fin N → ℝ) (b : Fin N) :
    ∑ k, ∑ l, g k l * (if k = b then 1 else 0) = ∑ l, g b l := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp

theorem square_cor_sum_sum_delta_right (g : Fin N → Fin N → ℝ) (b : Fin N) :
    ∑ k, ∑ l, g k l * (if l = b then 1 else 0) = ∑ k, g k b := by
  simp

theorem square_cor_sum_delta (g : Fin N → ℝ) (a : Fin N) :
    ∑ l, g l * (if l = a then 1 else 0) = g a := by
  simp

end Delta

/-! ### Pair sums `(2π)⁻² Σ_{k,l} W_{kl} sin (2π (z_k − z_l))` and their Hessians -/

section Pair

variable {N : ℕ}

/-- `f (z) = (2π)⁻² Σ_{k,l} W_{kl} sin (2π (z_k − z_l))`. -/
noncomputable def square_cor_pair (W : Fin N → Fin N → ℝ) (z : Fin N → ℝ) : ℝ :=
  ((2 * π) ^ 2)⁻¹ * ∑ k, ∑ l, W k l * sin (2 * π * (z k - z l))

theorem square_cor_pair_hasFDerivAt (W : Fin N → Fin N → ℝ) (y : Fin N → ℝ) :
    HasFDerivAt (square_cor_pair W)
      (((2 * π) ^ 2)⁻¹ • ∑ k, ∑ l, W k l • (cos (2 * π * (y k - y l)) •
        ((2 * π) • ((ContinuousLinearMap.proj k : (Fin N → ℝ) →L[ℝ] ℝ) -
          ContinuousLinearMap.proj l)))) y := by
  have h : ∀ k l, HasFDerivAt (fun y : Fin N → ℝ => W k l * sin (2 * π * (y k - y l)))
      (W k l • (cos (2 * π * (y k - y l)) •
        ((2 * π) • ((ContinuousLinearMap.proj k : (Fin N → ℝ) →L[ℝ] ℝ) -
          ContinuousLinearMap.proj l)))) y := fun k l =>
    ((((hasFDerivAt_apply k y).sub (hasFDerivAt_apply l y)).const_mul (2 * π)).sin).const_mul
      (W k l)
  have hs := (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => h k l).const_mul (((2 * π) ^ 2)⁻¹)
  exact hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

/-- `∂_b f (y) = (2π)⁻¹ Σ_l (W_{bl} − W_{lb}) cos (2π (y_b − y_l))`. -/
theorem square_cor_pair_fderiv (W : Fin N → Fin N → ℝ) (y : Fin N → ℝ) (b : Fin N) :
    fderiv ℝ (square_cor_pair W) y (Pi.single b 1) =
      (2 * π)⁻¹ * ∑ l, (W b l - W l b) * cos (2 * π * (y b - y l)) := by
  rw [(square_cor_pair_hasFDerivAt W y).fderiv]
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, sub_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul]
  have e : ∀ k l, W k l * (cos (2 * π * (y k - y l)) *
      (2 * π * ((if k = b then (1 : ℝ) else 0) - if l = b then 1 else 0))) =
      2 * π * (W k l * cos (2 * π * (y k - y l))) * (if k = b then 1 else 0) -
        2 * π * (W k l * cos (2 * π * (y k - y l))) * (if l = b then 1 else 0) :=
    fun k l => by ring
  simp_rw [e, Finset.sum_sub_distrib]
  simp only [square_cor_sum_sum_delta_left, square_cor_sum_sum_delta_right]
  have hc : ∀ k, cos (2 * π * (y k - y b)) = cos (2 * π * (y b - y k)) := fun k => by
    rw [← cos_neg]; ring_nf
  simp_rw [hc]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hπ : (2 * π) ≠ 0 := by positivity
  field_simp

/-- The Hessian of a pair sum: with `Q_{ab} = W_{ab} − W_{ba}`,
`(D²f)_{ab} = Q_{ab} sin (2π (z_a − z_b)) − δ_{ab} Σ_l Q_{al} sin (2π (z_a − z_l))`. -/
theorem square_cor_pair_hessian (W : Fin N → Fin N → ℝ) (z : Fin N → ℝ) :
    hessian (square_cor_pair W) z = Matrix.of fun a b =>
      (W a b - W b a) * sin (2 * π * (z a - z b)) -
        if a = b then ∑ l, (W a l - W l a) * sin (2 * π * (z a - z l)) else 0 := by
  ext a b
  simp only [hessian, Matrix.of_apply]
  have hfun : (fun y => fderiv ℝ (square_cor_pair W) y (Pi.single b 1)) =
      fun y => (2 * π)⁻¹ * ∑ l, (W b l - W l b) * cos (2 * π * (y b - y l)) :=
    funext fun y => square_cor_pair_fderiv W y b
  rw [hfun]
  have h : ∀ l, HasFDerivAt (fun y : Fin N → ℝ => (W b l - W l b) * cos (2 * π * (y b - y l)))
      ((W b l - W l b) • (-sin (2 * π * (z b - z l)) •
        ((2 * π) • ((ContinuousLinearMap.proj b : (Fin N → ℝ) →L[ℝ] ℝ) -
          ContinuousLinearMap.proj l)))) z := fun l =>
    ((((hasFDerivAt_apply b z).sub (hasFDerivAt_apply l z)).const_mul (2 * π)).cos).const_mul _
  have hD := (HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => h l).const_mul (2 * π)⁻¹
  rw [hD.fderiv]
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, sub_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul]
  have e : ∀ l, (W b l - W l b) * (-sin (2 * π * (z b - z l)) *
      (2 * π * ((if b = a then (1 : ℝ) else 0) - if l = a then 1 else 0))) =
      -(2 * π) * ((W b l - W l b) * sin (2 * π * (z b - z l))) * (if b = a then 1 else 0) +
        2 * π * ((W b l - W l b) * sin (2 * π * (z b - z l))) * (if l = a then 1 else 0) :=
    fun l => by ring
  simp_rw [e, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, square_cor_sum_delta (fun l => 2 * π * ((W b l - W l b) *
    sin (2 * π * (z b - z l)))) a]
  have hπ : (2 * π) ≠ 0 := by positivity
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte, sub_self, mul_zero, sin_zero, mul_one, ← Finset.mul_sum]
    field_simp
    ring
  · have hba : b ≠ a := Ne.symm hab
    simp only [hab, hba, ↓reduceIte, mul_zero, zero_add, sub_zero]
    rw [show 2 * π * (z b - z a) = -(2 * π * (z a - z b)) by ring, sin_neg]
    field_simp
    ring

end Pair

/-! ### The witness -/

/-- The indicator of the first block (the `x` coordinates). -/
noncomputable def square_cor_cx (n : ℕ) (k : Fin (n + n)) : ℝ := if (k : ℕ) < n then 1 else 0

/-- The indicator of the second block (the `y` coordinates). -/
noncomputable def square_cor_cy (n : ℕ) (k : Fin (n + n)) : ℝ := if (k : ℕ) < n then 0 else 1

theorem square_cor_cx_castAdd (n : ℕ) (i : Fin n) : square_cor_cx n (Fin.castAdd n i) = 1 := by
  simp [square_cor_cx]

theorem square_cor_cx_natAdd (n : ℕ) (j : Fin n) : square_cor_cx n (Fin.natAdd n j) = 0 := by
  simp [square_cor_cx]

theorem square_cor_cy_castAdd (n : ℕ) (i : Fin n) : square_cor_cy n (Fin.castAdd n i) = 0 := by
  simp [square_cor_cy]

theorem square_cor_cy_natAdd (n : ℕ) (j : Fin n) : square_cor_cy n (Fin.natAdd n j) = 1 := by
  simp [square_cor_cy]

theorem square_corWitness_eq_pair (n : ℕ) :
    square_corWitness n = square_cor_pair fun k l => square_cor_cx n k * square_cor_cy n l := by
  funext z
  simp only [square_corWitness, square_cor_pair]
  congr 1
  simp only [Fin.sum_univ_add, square_cor_cx_castAdd, square_cor_cx_natAdd, square_cor_cy_castAdd,
    square_cor_cy_natAdd, one_mul, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]

theorem square_corWitness_contDiff (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (square_corWitness n) := by
  unfold square_corWitness
  fun_prop

theorem square_corWitness_periodic (n : ℕ) (x : Fin (n + n) → ℝ) (z : Fin (n + n) → ℤ) :
    square_corWitness n (x + fun i => (z i : ℝ)) = square_corWitness n x := by
  simp only [square_corWitness, Pi.add_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * π * (x (Fin.castAdd n i) + (z (Fin.castAdd n i) : ℝ) -
      (x (Fin.natAdd n j) + (z (Fin.natAdd n j) : ℝ))) =
    2 * π * (x (Fin.castAdd n i) - x (Fin.natAdd n j)) +
      ((z (Fin.castAdd n i) - z (Fin.natAdd n j) : ℤ) : ℝ) * (2 * π) by push_cast; ring,
    sin_add_int_mul_two_pi]

/-- `Q_{ab} = W_{ab} − W_{ba}` for `W_{kl} = [k ∈ x] [l ∈ y]`. -/
noncomputable def square_cor_Q (n : ℕ) (a b : Fin (n + n)) : ℝ :=
  square_cor_cx n a * square_cor_cy n b - square_cor_cx n b * square_cor_cy n a

/-- The Hessian of the witness: `(D²ψ)_{ab} = Q_{ab} sin (θ_a − θ_b) − δ_{ab} Σ_l Q_{al}
sin (θ_a − θ_l)`, i.e. `D²ψ = [[−diag r, M], [Mᵀ, −diag c]]`. -/
theorem square_corWitness_hessian (n : ℕ) (z : Fin (n + n) → ℝ) :
    hessian (square_corWitness n) z = Matrix.of fun a b =>
      square_cor_Q n a b * sin (2 * π * (z a - z b)) -
        if a = b then ∑ l, square_cor_Q n a l * sin (2 * π * (z a - z l)) else 0 := by
  rw [square_corWitness_eq_pair, square_cor_pair_hessian]
  rfl

theorem square_continuous_J_hessian (n : ℕ) :
    Continuous fun z => square_J n * hessian (square_corWitness n) z := by
  refine continuous_const.matrix_mul ?_
  rw [show hessian (square_corWitness n) = _ from funext (square_corWitness_hessian n)]
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  split_ifs <;> fun_prop

/-! ### `Sym (J D²ψ)` and `Skew (J D²ψ)` -/

/-- `Skew (J D²ψ) = [[0, M], [−Mᵀ, 0]]`: its `(a, b)` entry is `sin (θ_a − θ_b)` when `a` and `b`
are in different blocks, `0` otherwise. -/
theorem square_cor_skew (n : ℕ) (z : Fin (n + n) → ℝ) :
    (1 / 2 : ℝ) • (square_J n * hessian (square_corWitness n) z -
        (square_J n * hessian (square_corWitness n) z)ᵀ) =
      Matrix.of fun a b => (square_cor_cx n a * square_cor_cy n b +
        square_cor_cy n a * square_cor_cx n b) * sin (2 * π * (z a - z b)) := by
  ext a b
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply, square_J,
    Matrix.diagonal_mul, square_corWitness_hessian, Matrix.of_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab; simp
  · have hba : b ≠ a := Ne.symm hab
    simp only [hab, hba, ↓reduceIte, sub_zero]
    rw [show 2 * π * (z b - z a) = -(2 * π * (z a - z b)) by ring, sin_neg]
    simp only [square_cor_Q, square_cor_cx, square_cor_cy]
    split_ifs <;> ring

/-- `Sym (J D²ψ) = diag (−r, c)`. -/
theorem square_cor_sym (n : ℕ) (z : Fin (n + n) → ℝ) :
    (1 / 2 : ℝ) • (square_J n * hessian (square_corWitness n) z +
        (square_J n * hessian (square_corWitness n) z)ᵀ) =
      Matrix.diagonal fun a : Fin (n + n) => (if (a : ℕ) < n then 1 else -1) *
        -∑ l, square_cor_Q n a l * sin (2 * π * (z a - z l)) := by
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, square_J,
    Matrix.diagonal_mul, square_corWitness_hessian, Matrix.of_apply, smul_eq_mul,
    Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte, sub_self, mul_zero, sin_zero, zero_sub]
    ring
  · have hba : b ≠ a := Ne.symm hab
    simp only [hab, hba, ↓reduceIte, sub_zero]
    rw [show 2 * π * (z b - z a) = -(2 * π * (z a - z b)) by ring, sin_neg]
    simp only [square_cor_Q, square_cor_cx, square_cor_cy]
    split_ifs <;> ring

/-! ### The Schatten `4`-norm -/

theorem square_cor_schattenNorm_four_eq {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm 4 A = ((Aᵀ * A * (Aᵀ * A)).trace) ^ (1 / 4 : ℝ) := by
  rw [← square_schattenNorm_four_rpow, ← Real.rpow_mul (schattenNorm_nonneg _ _)]
  norm_num

theorem square_cor_continuous_schattenNorm_four {X : Type*} [TopologicalSpace X] {d m : ℕ}
    {G : X → Matrix (Fin d) (Fin m) ℝ} (hG : Continuous G) :
    Continuous fun x => schattenNorm 4 (G x) := by
  simp_rw [square_cor_schattenNorm_four_eq]
  exact (((hG.matrix_transpose.matrix_mul hG).matrix_mul
    (hG.matrix_transpose.matrix_mul hG)).matrix_trace).rpow_const fun _ => Or.inr (by norm_num)

/-! ### The weighted moments -/

/-- `Z_w (z) = Σ_k w_k e^{2πi z_k}`. -/
noncomputable def square_cor_zw {N : ℕ} (w : Fin N → ℝ) (z : Fin N → ℝ) : ℂ :=
  ∑ k, (w k : ℂ) * square_cexp (z k)

theorem square_cor_continuous_zw {N : ℕ} (w : Fin N → ℝ) : Continuous (square_cor_zw w) := by
  unfold square_cor_zw
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.mul (square_continuous_cexp.comp (continuous_apply k))

/-- One coordinate of the weighted moment computation: for `v ∈ ℂ`, `c ∈ ℝ`,
`∫₀¹ |v + c e^{2πit}|^{2m} dt = Σ_k (m choose k)² |v|^{2k} (c²)^{m−k}`. -/
theorem square_cor_integral_norm_add_pow (v : ℂ) (c : ℝ) (m : ℕ) :
    ∫ t in Set.Ioo (0:ℝ) 1, ‖v + (c : ℂ) * square_cexp t‖ ^ (2 * m) =
      ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ)) ^ 2 * ‖v‖ ^ (2 * k) * (c ^ 2) ^ (m - k) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hpt : ∀ t : ℝ, ((‖v + (c : ℂ) * square_cexp t‖ ^ (2 * m) : ℝ) : ℂ) =
      ∑ k ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m + 1),
        (v ^ k * (starRingEnd ℂ) v ^ l * ((c : ℂ) ^ (m - k) * (c : ℂ) ^ (m - l)) *
          ((m.choose k : ℂ) * (m.choose l : ℂ))) *
          Complex.exp (↑(2 * π * (((m - k : ℕ) : ℤ) - ((m - l : ℕ) : ℤ) : ℤ) * t) *
            Complex.I) := by
    intro t
    rw [pow_mul, Complex.ofReal_pow, Complex.ofReal_pow, ← Complex.mul_conj', mul_pow,
      map_add, map_mul, Complex.conj_ofReal, add_pow, add_pow, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← square_cexp_pow_mul_conj_pow]
    ring
  simp_rw [hpt]
  have hint : ∀ (c : ℂ) (j : ℤ), IntegrableOn
      (fun t : ℝ => c * Complex.exp (↑(2 * π * j * t) * Complex.I)) (Set.Ioo (0:ℝ) 1) :=
    fun c j => (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioo_subset_Icc_self
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint _ _]
  simp_rw [integral_finsetSum _ fun l _ => hint _ _, integral_const_mul,
    square_integral_cexp_int]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_eq_single k]
  · rw [sub_self, ite_eq_left_iff.2 fun h => absurd rfl h, mul_one]
    have hv : v ^ k * (starRingEnd ℂ) v ^ k = (‖v‖ : ℂ) ^ (2 * k) := by
      rw [← mul_pow, Complex.mul_conj', ← pow_mul]
    rw [hv]
    ring
  · intro l hl hlk
    have hkm : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hlm : l ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    rw [ite_eq_right_iff.2 fun h => absurd h (by omega), mul_zero]
  · intro h; exact absurd hk h

/-- **The weighted moments**: `E |Σ_k w_k e^{2πi z_k}|^{2m} ≤ m! (Σ_k w_k²)^m`. -/
theorem square_cor_moment (N m : ℕ) (w : Fin N → ℝ) :
    ∫ z in unitCube N, ‖square_cor_zw w z‖ ^ (2 * m) ≤
      (m.factorial : ℝ) * (∑ k, w k ^ 2) ^ m := by
  induction N generalizing m with
  | zero =>
    have : ∀ z : Fin 0 → ℝ, square_cor_zw w z = 0 := fun z => by simp [square_cor_zw]
    simp_rw [this, norm_zero, square_integral_cube_const]
    rcases m with _ | m
    · simp
    · simp
  | succ N ih =>
    have hc1 := square_cor_continuous_zw w
    rw [square_integral_cube_succ (by fun_prop) 0]
    set w' : Fin N → ℝ := fun k => w (Fin.succAbove 0 k)
    have hsplit : ∀ (y : Fin N → ℝ) (t : ℝ),
        square_cor_zw w (Fin.insertNth 0 t y : Fin (N + 1) → ℝ) =
          square_cor_zw w' y + (w 0 : ℂ) * square_cexp t := by
      intro y t
      rw [square_cor_zw, Fin.sum_univ_succAbove _ 0, Fin.insertNth_apply_same, add_comm]
      simp only [Fin.insertNth_apply_succAbove, square_cor_zw, w']
    have hW : ∑ k, w k ^ 2 = (∑ k, w' k ^ 2) + w 0 ^ 2 := by
      rw [Fin.sum_univ_succAbove _ 0, add_comm]
    simp_rw [hsplit, square_cor_integral_norm_add_pow]
    have hc0 := square_cor_continuous_zw w'
    have e : ∀ y : Fin N → ℝ, ∑ k ∈ Finset.range (m + 1),
        ((m.choose k : ℝ)) ^ 2 * ‖square_cor_zw w' y‖ ^ (2 * k) * (w 0 ^ 2) ^ (m - k) =
        ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ)) ^ 2 * (w 0 ^ 2) ^ (m - k) *
          ‖square_cor_zw w' y‖ ^ (2 * k) := fun y =>
      Finset.sum_congr rfl fun k _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun k _ =>
      (square_integrableOn_cube (by fun_prop)).const_mul _]
    simp_rw [integral_const_mul]
    rw [hW]
    set W' := ∑ k, w' k ^ 2
    have hW'0 : 0 ≤ W' := Finset.sum_nonneg fun k _ => sq_nonneg _
    calc ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ)) ^ 2 * (w 0 ^ 2) ^ (m - k) *
          ∫ y in unitCube N, ‖square_cor_zw w' y‖ ^ (2 * k)
        ≤ ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ)) ^ 2 * (w 0 ^ 2) ^ (m - k) *
            ((k.factorial : ℝ) * W' ^ k) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (ih k w') (by positivity)
      _ ≤ ∑ k ∈ Finset.range (m + 1), (m.factorial : ℝ) *
            (W' ^ k * (w 0 ^ 2) ^ (m - k) * (m.choose k : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkm : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
          have h1 : m.choose k * k.factorial ≤ m.factorial := by
            have := Nat.choose_mul_factorial_mul_factorial hkm
            calc m.choose k * k.factorial ≤ m.choose k * k.factorial * (m - k).factorial :=
                  Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
              _ = m.factorial := this
          have h1' : (m.choose k : ℝ) * k.factorial ≤ m.factorial := by exact_mod_cast h1
          have hc : (0 : ℝ) ≤ m.choose k * W' ^ k * (w 0 ^ 2) ^ (m - k) := by positivity
          calc ((m.choose k : ℝ)) ^ 2 * (w 0 ^ 2) ^ (m - k) * ((k.factorial : ℝ) * W' ^ k) =
                ((m.choose k : ℝ) * k.factorial) * ((m.choose k : ℝ) * W' ^ k *
                  (w 0 ^ 2) ^ (m - k)) := by ring
            _ ≤ (m.factorial : ℝ) * ((m.choose k : ℝ) * W' ^ k * (w 0 ^ 2) ^ (m - k)) :=
                mul_le_mul_of_nonneg_right h1' hc
            _ = _ := by ring
      _ = (m.factorial : ℝ) * (W' + w 0 ^ 2) ^ m := by
          rw [← Finset.mul_sum, add_pow]

/-- `‖Z_w‖_{L^p} ≤ √(p Σ_k w_k²)` for `p ≥ 1`: with `m = ⌈p/2⌉ ≤ p`,
`‖Z_w‖_{L^p} ≤ ‖Z_w‖_{L^{2m}} ≤ (m! W^m)^{1/(2m)} ≤ √(m W)`. -/
theorem square_cor_lp_le (N : ℕ) (w : Fin N → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (∫ z in unitCube N, ‖square_cor_zw w z‖ ^ p) ^ (1 / p) ≤ √(p * ∑ k, w k ^ 2) := by
  have hp0 : 0 < p := by linarith
  set W := ∑ k, w k ^ 2
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun k _ => sq_nonneg _
  set m := ⌈p / 2⌉₊ with hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 fun h => by
    rw [hm, Nat.ceil_eq_zero] at h; linarith
  have hpm : p ≤ 2 * m := by
    have := Nat.le_ceil (p / 2); rw [← hm] at this; linarith
  have hmp : (m : ℝ) ≤ p := by
    rcases le_or_gt p 2 with h | h
    · have : m = 1 := le_antisymm (Nat.ceil_le.2 (by rw [Nat.cast_one]; linarith)) hm1
      rw [this, Nat.cast_one]; exact hp
    · have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ p / 2 by linarith)
      rw [← hm] at this; linarith
  have hcz := square_cor_continuous_zw w
  have hmono := square_cube_lp_mono hcz.norm (fun x => norm_nonneg _) hp0 hpm
  have h2m : ∫ x in unitCube N, ‖square_cor_zw w x‖ ^ ((2 * m : ℕ) : ℝ) ≤
      (m.factorial : ℝ) * W ^ m := by
    simp_rw [Real.rpow_natCast]; exact square_cor_moment N m w
  have hI0 : 0 ≤ ∫ x in unitCube N, ‖square_cor_zw w x‖ ^ ((2 * m : ℕ) : ℝ) :=
    setIntegral_nonneg (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
      fun x _ => Real.rpow_nonneg (norm_nonneg _) _
  have hfact : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  calc (∫ x in unitCube N, ‖square_cor_zw w x‖ ^ p) ^ (1 / p)
      ≤ (∫ x in unitCube N, ‖square_cor_zw w x‖ ^ (2 * (m : ℝ))) ^ (1 / (2 * (m : ℝ))) := hmono
    _ ≤ ((m : ℝ) ^ m * W ^ m) ^ (1 / (2 * (m : ℝ))) := by
        rw [show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring]
        exact Real.rpow_le_rpow hI0 (h2m.trans (mul_le_mul_of_nonneg_right hfact (by positivity)))
          (by positivity)
    _ = √(m * W) := by
        rw [← mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
        congr 1; field_simp
    _ ≤ √(p * W) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmp hW0)

/-- `|Σ_l w_l sin (θ − φ_l)| ≤ |Σ_l w_l e^{iφ_l}|`. -/
theorem square_cor_abs_sum_sin_le {N : ℕ} (w : Fin N → ℝ) (θ : ℝ) (φ : Fin N → ℝ) :
    |∑ l, w l * sin (θ - φ l)| ≤ ‖∑ l, (w l : ℂ) * Complex.exp (↑(φ l) * Complex.I)‖ := by
  set A := ∑ l, w l * sin (φ l)
  set B := ∑ l, w l * cos (φ l)
  have he : ∑ l, w l * sin (θ - φ l) = sin θ * B - cos θ * A := by
    simp only [B, A, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sin_sub]; ring
  have hn : ‖∑ l, (w l : ℂ) * Complex.exp (↑(φ l) * Complex.I)‖ ^ 2 = B ^ 2 + A ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, A, B]
    ring
  have h : (∑ l, w l * sin (θ - φ l)) ^ 2 ≤
      ‖∑ l, (w l : ℂ) * Complex.exp (↑(φ l) * Complex.I)‖ ^ 2 := by
    rw [hn, he]
    have h1 := sin_sq_add_cos_sq θ
    have key : (sin θ * B - cos θ * A) ^ 2 + (sin θ * A + cos θ * B) ^ 2 =
        (sin θ ^ 2 + cos θ ^ 2) * (A ^ 2 + B ^ 2) := by ring
    rw [h1, one_mul] at key
    nlinarith [sq_nonneg (sin θ * A + cos θ * B)]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by rw [sq_abs]; exact h)

theorem square_cor_sum_cx_sq (n : ℕ) : ∑ k, square_cor_cx n k ^ 2 = n := by
  rw [Fin.sum_univ_add]
  simp only [square_cor_cx_castAdd, square_cor_cx_natAdd]
  simp

theorem square_cor_sum_cy_sq (n : ℕ) : ∑ k, square_cor_cy n k ^ 2 = n := by
  rw [Fin.sum_univ_add]
  simp only [square_cor_cy_castAdd, square_cor_cy_natAdd]
  simp

/-! ### The upper bound for `Sym (J D²ψ)` -/

/-- `|r_i| ≤ |Z_y|`, `|c_j| ≤ |Z_x|`: every diagonal entry of `Sym (J D²ψ)` is at most
`max (|Z_x|, |Z_y|)`. -/
theorem square_cor_abs_diag_le (n : ℕ) (z : Fin (n + n) → ℝ) (a : Fin (n + n)) :
    |(if (a : ℕ) < n then (1 : ℝ) else -1) *
        -∑ l, square_cor_Q n a l * sin (2 * π * (z a - z l))| ≤
      max ‖square_cor_zw (square_cor_cx n) z‖ ‖square_cor_zw (square_cor_cy n) z‖ := by
  have hσ : |(if (a : ℕ) < n then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
  rw [abs_mul, hσ, one_mul, abs_neg]
  have hφ : ∀ l, 2 * π * (z a - z l) = 2 * π * z a - 2 * π * z l := fun l => by ring
  simp_rw [hφ]
  by_cases ha : (a : ℕ) < n
  · have hQ : ∀ l, square_cor_Q n a l = square_cor_cy n l := fun l => by
      simp [square_cor_Q, square_cor_cx, square_cor_cy, ha]
    simp_rw [hQ]
    exact (square_cor_abs_sum_sin_le _ _ _).trans (le_max_right _ _)
  · have hQ : ∀ l, square_cor_Q n a l = -square_cor_cx n l := fun l => by
      simp [square_cor_Q, square_cor_cx, square_cor_cy, ha]
    simp_rw [hQ, neg_mul, Finset.sum_neg_distrib, abs_neg]
    exact (square_cor_abs_sum_sin_le _ _ _).trans (le_max_left _ _)

/-- **The upper bound of Corollary 6.1's computation**:
`‖Sym (J D²ψ)‖_{L^p (S_4)} ≤ 2 (2n)^{1/4} √(p n)`. -/
theorem square_cor_sym_upper (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (∫ z in unitCube (n + n), schattenNorm 4 ((1 / 2 : ℝ) •
      (square_J n * hessian (square_corWitness n) z +
        (square_J n * hessian (square_corWitness n) z)ᵀ)) ^ p) ^ (1 / p) ≤
      2 * ((n + n : ℕ) : ℝ) ^ (1 / 4 : ℝ) * √(p * n) := by
  have hp0 : 0 < p := by linarith
  have hcube : MeasurableSet (unitCube (n + n)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  set c : ℝ := ((n + n : ℕ) : ℝ) ^ (1 / 4 : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  set S : (Fin (n + n) → ℝ) → ℝ := fun z => schattenNorm 4 ((1 / 2 : ℝ) •
      (square_J n * hessian (square_corWitness n) z +
        (square_J n * hessian (square_corWitness n) z)ᵀ)) with hS
  have hJH := square_continuous_J_hessian n
  have hsum : Continuous fun z => square_J n * hessian (square_corWitness n) z +
      (square_J n * hessian (square_corWitness n) z)ᵀ := hJH.add hJH.matrix_transpose
  have hsm : Continuous fun z => (1 / 2 : ℝ) • (square_J n * hessian (square_corWitness n) z +
      (square_J n * hessian (square_corWitness n) z)ᵀ) := hsum.const_smul (1 / 2 : ℝ)
  have hSc : Continuous S := square_cor_continuous_schattenNorm_four hsm
  set X := fun z => ‖square_cor_zw (square_cor_cx n) z‖
  set Y := fun z => ‖square_cor_zw (square_cor_cy n) z‖
  have hXc : Continuous X := (square_cor_continuous_zw _).norm
  have hYc : Continuous Y := (square_cor_continuous_zw _).norm
  have hle : ∀ z, S z ≤ c * max (X z) (Y z) := fun z => by
    simp only [S, square_cor_sym]
    have := square_schattenNorm_diagonal_le _ (le_max_of_le_left (norm_nonneg _))
      (square_cor_abs_diag_le n z) (show (1 : ℝ≥0∞) ≤ 4 by norm_num)
    rwa [show ((4 : ℝ≥0∞)).toReal = 4 by norm_num] at this
  have hpt : ∀ z, S z ^ p ≤ c ^ p * (X z ^ p + Y z ^ p) := fun z => by
    have hS0 : 0 ≤ S z := schattenNorm_nonneg _ _
    calc S z ^ p ≤ (c * max (X z) (Y z)) ^ p := Real.rpow_le_rpow hS0 (hle z) hp0.le
      _ = c ^ p * max (X z) (Y z) ^ p :=
          Real.mul_rpow hc0 (le_max_of_le_left (norm_nonneg _))
      _ ≤ c ^ p * (X z ^ p + Y z ^ p) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hX0 : 0 ≤ X z ^ p := Real.rpow_nonneg (norm_nonneg _) _
          have hY0 : 0 ≤ Y z ^ p := Real.rpow_nonneg (norm_nonneg _) _
          rcases le_total (X z) (Y z) with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
  have hXp : Continuous fun z => X z ^ p := hXc.rpow_const fun _ => Or.inr hp0.le
  have hYp : Continuous fun z => Y z ^ p := hYc.rpow_const fun _ => Or.inr hp0.le
  have hLp : ∀ w : Fin (n + n) → ℝ, ∑ k, w k ^ 2 = n →
      ∫ z in unitCube (n + n), ‖square_cor_zw w z‖ ^ p ≤ √(p * n) ^ p := fun w hw => by
    have h := square_cor_lp_le (n + n) w hp
    rw [hw] at h
    have hI0 : 0 ≤ ∫ z in unitCube (n + n), ‖square_cor_zw w z‖ ^ p :=
      setIntegral_nonneg hcube fun z _ => Real.rpow_nonneg (norm_nonneg _) _
    calc ∫ z in unitCube (n + n), ‖square_cor_zw w z‖ ^ p =
          ((∫ z in unitCube (n + n), ‖square_cor_zw w z‖ ^ p) ^ (1 / p)) ^ p := by
          rw [← Real.rpow_mul hI0, one_div_mul_cancel hp0.ne', Real.rpow_one]
      _ ≤ √(p * n) ^ p := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) h hp0.le
  have hint : ∫ z in unitCube (n + n), S z ^ p ≤ c ^ p * (2 * √(p * n) ^ p) := by
    calc ∫ z in unitCube (n + n), S z ^ p ≤
          ∫ z in unitCube (n + n), c ^ p * (X z ^ p + Y z ^ p) :=
          setIntegral_mono (square_integrableOn_cube (hSc.rpow_const fun _ => Or.inr hp0.le))
            (square_integrableOn_cube (continuous_const.mul (hXp.add hYp))) hpt
      _ = c ^ p * ((∫ z in unitCube (n + n), X z ^ p) + ∫ z in unitCube (n + n), Y z ^ p) := by
          rw [integral_const_mul, integral_add (square_integrableOn_cube hXp)
            (square_integrableOn_cube hYp)]
      _ ≤ c ^ p * (√(p * n) ^ p + √(p * n) ^ p) := by
          gcongr
          · exact hLp _ (square_cor_sum_cx_sq n)
          · exact hLp _ (square_cor_sum_cy_sq n)
      _ = c ^ p * (2 * √(p * n) ^ p) := by ring
  have hI0 : 0 ≤ ∫ z in unitCube (n + n), S z ^ p :=
    setIntegral_nonneg hcube fun z _ => Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  have hsq0 : 0 ≤ √(p * n) := Real.sqrt_nonneg _
  calc (∫ z in unitCube (n + n), S z ^ p) ^ (1 / p) ≤ (c ^ p * (2 * √(p * n) ^ p)) ^ (1 / p) :=
        Real.rpow_le_rpow hI0 hint (by positivity)
    _ = c * (2 ^ (1 / p) * √(p * n)) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num)
          (by positivity), ← Real.rpow_mul hc0, ← Real.rpow_mul hsq0, mul_one_div_cancel hp0.ne',
          Real.rpow_one, Real.rpow_one]
    _ ≤ c * (2 * √(p * n)) := by
        gcongr
        calc (2 : ℝ) ^ (1 / p) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [div_le_one hp0]; exact hp)
          _ = 2 := Real.rpow_one 2
    _ = 2 * c * √(p * n) := by ring

/-! ### The lower bound for `Skew (J D²ψ)` -/

/-- `E cos (4π (z_a − z_b)) = 0` for `a ≠ b`. -/
theorem square_cor_integral_cos_sub {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    ∫ z in unitCube N, cos (4 * π * (z a - z b)) = 0 := by
  cases N with
  | zero => exact a.elim0
  | succ k =>
    obtain ⟨b', rfl⟩ := Fin.exists_succAbove_eq (x := b) (y := a) (Ne.symm hab)
    rw [square_integral_cube_succ (by fun_prop) a]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    have : ∀ y : Fin k → ℝ, ∫ t in Set.Ioo (0:ℝ) 1, cos (4 * π * (t - y b')) = 0 := fun y =>
      square_integral_cos_of (k := 2) (by norm_num) (-(4 * π * y b')) fun t => by push_cast; ring
    simp_rw [this, integral_zero]

/-- `E sin² (2π (z_a − z_b)) = 1/2` for `a ≠ b`. -/
theorem square_cor_integral_sin_sq {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    ∫ z in unitCube N, sin (2 * π * (z a - z b)) ^ 2 = 1 / 2 := by
  have e : ∀ z : Fin N → ℝ, sin (2 * π * (z a - z b)) ^ 2 =
      1 / 2 - cos (4 * π * (z a - z b)) / 2 := fun z => by
    rw [sin_sq, cos_sq, show 2 * (2 * π * (z a - z b)) = 4 * π * (z a - z b) by ring]; ring
  simp_rw [e]
  rw [integral_sub (square_integrableOn_cube continuous_const)
    (square_integrableOn_cube (by fun_prop)), square_integral_cube_const, integral_div,
    square_cor_integral_cos_sub hab]
  ring

/-- The weights `D_{ab} = [a ∈ x] [b ∈ y] + [a ∈ y] [b ∈ x]` of `Skew (J D²ψ)`. -/
noncomputable def square_cor_D (n : ℕ) (a b : Fin (n + n)) : ℝ :=
  square_cor_cx n a * square_cor_cy n b + square_cor_cy n a * square_cor_cx n b

theorem square_cor_D_sq (n : ℕ) (a b : Fin (n + n)) : square_cor_D n a b ^ 2 = square_cor_D n a b := by
  simp only [square_cor_D, square_cor_cx, square_cor_cy]
  split_ifs <;> norm_num

theorem square_cor_D_self (n : ℕ) (a : Fin (n + n)) : square_cor_D n a a = 0 := by
  simp only [square_cor_D, square_cor_cx, square_cor_cy]
  split_ifs <;> norm_num

theorem square_cor_sum_D (n : ℕ) : ∑ a, ∑ b, square_cor_D n a b = 2 * (n : ℝ) ^ 2 := by
  have hx : ∑ a, square_cor_cx n a = n := by
    rw [Fin.sum_univ_add]
    simp only [square_cor_cx_castAdd, square_cor_cx_natAdd]
    simp
  have hy : ∑ a, square_cor_cy n a = n := by
    rw [Fin.sum_univ_add]
    simp only [square_cor_cy_castAdd, square_cor_cy_natAdd]
    simp
  simp only [square_cor_D, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hx, hy]
  ring

/-- `Skew (J D²ψ)` as a product of a `2n × 4` and a `4 × 2n` matrix, hence of rank at most `4`. -/
theorem square_cor_skew_rank (n : ℕ) (z : Fin (n + n) → ℝ) :
    (Matrix.of fun a b => square_cor_D n a b * sin (2 * π * (z a - z b))).rank ≤ 4 := by
  set u1 : Fin (n + n) → ℝ := fun a => square_cor_cx n a * sin (2 * π * z a)
  set u2 : Fin (n + n) → ℝ := fun a => square_cor_cx n a * cos (2 * π * z a)
  set v1 : Fin (n + n) → ℝ := fun a => square_cor_cy n a * sin (2 * π * z a)
  set v2 : Fin (n + n) → ℝ := fun a => square_cor_cy n a * cos (2 * π * z a)
  set U : Matrix (Fin (n + n)) (Fin 4) ℝ := Matrix.of fun a k => ![u1 a, u2 a, v1 a, v2 a] k
  set V : Matrix (Fin 4) (Fin (n + n)) ℝ := Matrix.of fun k b => ![v2 b, -v1 b, u2 b, -u1 b] k
  have hUV : (Matrix.of fun a b => square_cor_D n a b * sin (2 * π * (z a - z b))) = U * V := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four, U, V, u1, u2, v1, v2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, square_cor_D]
    rw [show 2 * π * (z a - z b) = 2 * π * z a - 2 * π * z b by ring, sin_sub]
    ring
  rw [hUV]
  exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_width U)

/-- `‖K‖_{S_4} ≥ ‖K‖_{S_2} / √2` for a matrix of rank at most `4`. -/
theorem square_cor_sq_le_four {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (hK : K.rank ≤ 4) :
    ((Kᵀ * K).trace) ^ 2 ≤ 4 * schattenNorm 4 K ^ 4 := by
  set S := Finset.univ.filter fun i => sval K i ≠ 0
  have hS : S.card ≤ 4 := by
    have h1 : S = Finset.univ.filter fun i =>
        (Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i ≠ 0 := by
      refine Finset.filter_congr fun i _ => ?_
      rw [sval, ne_eq, ne_eq, Real.sqrt_eq_zero (square_eigenvalues_nonneg K i)]
    have h2 := (Matrix.isHermitian_conjTranspose_mul_self K).rank_eq_card_non_zero_eigs
    rw [Matrix.rank_conjTranspose_mul_self, Fintype.card_subtype] at h2
    rw [h1, ← h2]; exact hK
  rw [← square_sum_sval_sq, square_schattenNorm_four_pow, ← square_sum_sval_pow_four]
  have hsum : ∑ i, sval K i ^ 2 = ∑ i ∈ S, sval K i ^ 2 := by
    rw [Finset.sum_filter_of_ne]
    intro i _ h hi
    exact h (by rw [hi]; ring)
  rw [hsum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => sval K i ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have h4 : ∑ i ∈ S, (sval K i ^ 2) ^ 2 ≤ ∑ i, sval K i ^ 4 := by
    simp_rw [← pow_mul]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => pow_nonneg (square_sval_nonneg K i) _
  have hS' : (S.card : ℝ) ≤ 4 := by exact_mod_cast hS
  have h0 : 0 ≤ ∑ i ∈ S, (sval K i ^ 2) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  calc (∑ i ∈ S, sval K i ^ 2) ^ 2 ≤ S.card * ∑ i ∈ S, (sval K i ^ 2) ^ 2 := hcs
    _ ≤ 4 * ∑ i, sval K i ^ 4 := mul_le_mul hS' h4 h0 (by norm_num)

/-- **The lower bound of Corollary 6.1's computation**:
`‖Skew (J D²ψ)‖_{L^p (S_4)} ≥ n / 2`. -/
theorem square_cor_skew_lower {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) :
    (n : ℝ) / 2 ≤ (∫ z in unitCube (n + n), schattenNorm 4 ((1 / 2 : ℝ) •
      (square_J n * hessian (square_corWitness n) z -
        (square_J n * hessian (square_corWitness n) z)ᵀ)) ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcube : MeasurableSet (unitCube (n + n)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  set K : (Fin (n + n) → ℝ) → Matrix (Fin (n + n)) (Fin (n + n)) ℝ := fun z =>
    Matrix.of fun a b => square_cor_D n a b * sin (2 * π * (z a - z b)) with hK
  set T : (Fin (n + n) → ℝ) → ℝ := fun z => ∑ b, ∑ a, (square_cor_D n a b *
    sin (2 * π * (z a - z b))) ^ 2 with hT
  have hTc : Continuous T := by simp only [hT]; fun_prop
  have hT0 : ∀ z, 0 ≤ T z := fun z => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have htr : ∀ z, ((K z)ᵀ * K z).trace = T z := fun z => by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, hK, hT,
      Matrix.of_apply, sq]
  -- `T ≤ 2 n²`
  have hTle : ∀ z, T z ≤ 2 * (n : ℝ) ^ 2 := fun z => by
    have hab : ∀ a b, (square_cor_D n a b * sin (2 * π * (z a - z b))) ^ 2 ≤
        square_cor_D n a b := fun a b => by
      rw [mul_pow, square_cor_D_sq]
      have hD0 : 0 ≤ square_cor_D n a b := by
        simp only [square_cor_D, square_cor_cx, square_cor_cy]; split_ifs <;> norm_num
      calc square_cor_D n a b * sin (2 * π * (z a - z b)) ^ 2 ≤ square_cor_D n a b * 1 :=
            mul_le_mul_of_nonneg_left (sin_sq_le_one _) hD0
        _ = _ := mul_one _
    calc T z ≤ ∑ b, ∑ a, square_cor_D n a b :=
          Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => hab a b
      _ = 2 * (n : ℝ) ^ 2 := by rw [Finset.sum_comm, square_cor_sum_D]
  -- `E T = n²`
  have hET : ∫ z in unitCube (n + n), T z = (n : ℝ) ^ 2 := by
    have hi : ∀ a b : Fin (n + n), Integrable
        (fun z : Fin (n + n) → ℝ => (square_cor_D n a b * sin (2 * π * (z a - z b))) ^ 2)
        (volume.restrict (unitCube (n + n))) := fun a b => square_integrableOn_cube (by fun_prop)
    have h1 : ∀ b, ∫ z in unitCube (n + n),
        ∑ a, (square_cor_D n a b * sin (2 * π * (z a - z b))) ^ 2 =
        ∑ a, ∫ z in unitCube (n + n), (square_cor_D n a b * sin (2 * π * (z a - z b))) ^ 2 :=
      fun b => integral_finsetSum _ fun a _ => hi a b
    have h2 : ∀ a b : Fin (n + n), ∫ z in unitCube (n + n),
        (square_cor_D n a b * sin (2 * π * (z a - z b))) ^ 2 = square_cor_D n a b / 2 := by
      intro a b
      simp_rw [mul_pow]
      rw [integral_const_mul]
      by_cases hab : a = b
      · subst hab; rw [square_cor_D_self]; ring
      · rw [square_cor_integral_sin_sq hab, square_cor_D_sq]; ring
    show ∫ z in unitCube (n + n),
      ∑ b, ∑ a, (square_cor_D n a b * sin (2 * π * (z a - z b))) ^ 2 = _
    rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun a _ => hi a b]
    simp_rw [h1, h2]
    calc ∑ b, ∑ a, square_cor_D n a b / 2 = (∑ b, ∑ a, square_cor_D n a b) / 2 := by
          simp only [Finset.sum_div]
      _ = (∑ a, ∑ b, square_cor_D n a b) / 2 := by rw [Finset.sum_comm]
      _ = (n : ℝ) ^ 2 := by rw [square_cor_sum_D]; ring
  -- `‖K‖_{S_4} ≥ √(T/2)`
  set m : (Fin (n + n) → ℝ) → ℝ := fun z => √(T z / 2) with hm
  have hmc : Continuous m := Real.continuous_sqrt.comp (hTc.div_const _)
  have hKm : ∀ z, m z ≤ schattenNorm 4 ((1 / 2 : ℝ) •
      (square_J n * hessian (square_corWitness n) z -
        (square_J n * hessian (square_corWitness n) z)ᵀ)) := fun z => by
    rw [square_cor_skew]
    have h := square_cor_sq_le_four (K z) (square_cor_skew_rank n z)
    rw [htr] at h
    have hm4 : m z ^ 4 = T z ^ 2 / 4 := by
      simp only [hm]
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by linarith [hT0 z])]
      ring
    have hm0 : 0 ≤ m z := Real.sqrt_nonneg _
    refine (pow_le_pow_iff_left₀ hm0 (schattenNorm_nonneg _ _)
      (by norm_num : (4 : ℕ) ≠ 0)).1 ?_
    rw [hm4]
    show T z ^ 2 / 4 ≤ schattenNorm 4 (K z) ^ 4
    linarith
  -- `m ≤ n`, `E m² = n² / 2`, so `E m ≥ n / 2`
  have hmn : ∀ z, m z ≤ n := fun z => by
    simp only [hm]
    calc √(T z / 2) ≤ √((n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by linarith [hTle z])
      _ = n := Real.sqrt_sq (Nat.cast_nonneg n)
  have hlow : ∀ z, m z ^ 2 / n ≤ m z := fun z => by
    rw [div_le_iff₀ hn0, sq]
    exact mul_le_mul_of_nonneg_left (hmn z) (Real.sqrt_nonneg _)
  have hm2 : ∀ z, m z ^ 2 = T z / 2 := fun z => Real.sq_sqrt (by linarith [hT0 z])
  set Kn : (Fin (n + n) → ℝ) → ℝ := fun z => schattenNorm 4 ((1 / 2 : ℝ) •
      (square_J n * hessian (square_corWitness n) z -
        (square_J n * hessian (square_corWitness n) z)ᵀ)) with hKn
  have hJH := square_continuous_J_hessian n
  have hdif : Continuous fun z => square_J n * hessian (square_corWitness n) z -
      (square_J n * hessian (square_corWitness n) z)ᵀ := hJH.sub hJH.matrix_transpose
  have hdm : Continuous fun z => (1 / 2 : ℝ) • (square_J n * hessian (square_corWitness n) z -
      (square_J n * hessian (square_corWitness n) z)ᵀ) := hdif.const_smul (1 / 2 : ℝ)
  have hKnc : Continuous Kn := square_cor_continuous_schattenNorm_four hdm
  have hmp : Continuous fun z => m z ^ p := hmc.rpow_const fun _ => Or.inr hp0.le
  have hKp : Continuous fun z => Kn z ^ p := hKnc.rpow_const fun _ => Or.inr hp0.le
  calc (n : ℝ) / 2 = (∫ z in unitCube (n + n), T z / 2) / n := by
        rw [integral_div, hET]; field_simp
    _ = ∫ z in unitCube (n + n), m z ^ 2 / n := by
        rw [← integral_div]; simp_rw [hm2]
    _ ≤ ∫ z in unitCube (n + n), m z :=
        setIntegral_mono (square_integrableOn_cube ((hmc.pow 2).div_const _))
          (square_integrableOn_cube hmc) hlow
    _ = (∫ z in unitCube (n + n), m z ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) := by
        simp only [Real.rpow_one, div_one]
    _ ≤ (∫ z in unitCube (n + n), m z ^ p) ^ (1 / p) :=
        square_cube_lp_mono hmc (fun z => Real.sqrt_nonneg _) one_pos hp
    _ ≤ (∫ z in unitCube (n + n), Kn z ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (setIntegral_nonneg hcube fun z _ =>
            Real.rpow_nonneg (Real.sqrt_nonneg _) _)
          (setIntegral_mono (square_integrableOn_cube hmp) (square_integrableOn_cube hKp)
            fun z => Real.rpow_le_rpow (Real.sqrt_nonneg _) (hKm z) hp0.le)
          (by positivity)

end Cassese
