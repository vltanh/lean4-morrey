module

public import Morrey.Cassese.Defs
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

/-!
# Schatten norms of even order as traces

For a real matrix `A`, the squared singular values `s_i (A)²` are the eigenvalues of the positive
semidefinite `AᵀA`. Hence `‖A‖_{S_2}² = tr (AᵀA)` and `‖A‖_{S_4}⁴ = tr ((AᵀA)²)`: the norms of even
order are polynomials in the entries. These are the forms in which Section 6.3 (`p = q = 4`)
computes: Proposition 6.6 integrates `‖·‖_{S_4}⁴` of a trigonometric field, and Corollary 6.4 is a
quartic polynomial written with `‖·‖_{S_4}⁴` and `‖·‖_{S_2}²`.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-- For real matrices the conjugate transpose is the transpose. -/
theorem square_conjTranspose_eq (A : Matrix (Fin d) (Fin m) ℝ) : Aᴴ = Aᵀ :=
  Matrix.conjTranspose_eq_transpose_of_trivial A

/-- The eigenvalues of `AᵀA` are nonnegative. -/
theorem square_eigenvalues_nonneg (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin m) :
    0 ≤ (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i

theorem square_sval_nonneg (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin m) : 0 ≤ sval A i :=
  Real.sqrt_nonneg _

/-- `s_i (A)² = λ_i (AᵀA)`. -/
theorem square_sval_sq (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin m) :
    sval A i ^ 2 = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  Real.sq_sqrt (square_eigenvalues_nonneg A i)

/-- The trace of the square of a real symmetric matrix is the sum of the squares of its
eigenvalues (spectral theorem). -/
theorem square_trace_mul_self {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    (B * B).trace = ∑ i, hB.eigenvalues i ^ 2 := by
  set U := hB.eigenvectorUnitary
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)
  have hB' : B = (U : Matrix (Fin n) (Fin n) ℝ) * D * (star U : Matrix (Fin n) (Fin n) ℝ) := by
    conv_lhs => rw [hB.spectral_theorem]
    rfl
  have hU : (star U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.coe_star_mul_self U
  have hBB : B * B = (U : Matrix (Fin n) (Fin n) ℝ) * (D * D) * (star U : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hB']
    calc (U : Matrix (Fin n) (Fin n) ℝ) * D * (star U : Matrix (Fin n) (Fin n) ℝ) *
          ((U : Matrix (Fin n) (Fin n) ℝ) * D * (star U : Matrix (Fin n) (Fin n) ℝ)) =
        (U : Matrix (Fin n) (Fin n) ℝ) * D *
          ((star U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ)) * D *
            (star U : Matrix (Fin n) (Fin n) ℝ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℝ) D D]
  rw [hBB, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  simp [sq]

/-- `Σ s_i (A)² = tr (AᵀA)`. -/
theorem square_sum_sval_sq (A : Matrix (Fin d) (Fin m) ℝ) :
    ∑ i, sval A i ^ 2 = (Aᵀ * A).trace := by
  simp_rw [square_sval_sq]
  have := (Matrix.isHermitian_conjTranspose_mul_self A).trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id_eq] at this
  rw [← this, square_conjTranspose_eq]

/-- `Σ s_i (A)⁴ = tr ((AᵀA)²)`. -/
theorem square_sum_sval_pow_four (A : Matrix (Fin d) (Fin m) ℝ) :
    ∑ i, sval A i ^ 4 = (Aᵀ * A * (Aᵀ * A)).trace := by
  have h : ∀ i, sval A i ^ 4 = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i ^ 2 :=
    fun i => by rw [← square_sval_sq]; ring
  simp_rw [h]
  rw [← square_trace_mul_self, square_conjTranspose_eq]

/-- `‖A‖_{S_2}² = tr (AᵀA)`. -/
theorem square_schattenNorm_two_sq (A : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm 2 A ^ 2 = (Aᵀ * A).trace := by
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  simp only [schattenNorm, ENNReal.ofNat_ne_top, ite_false, h2]
  have hs : ∀ i, sval A i ^ (2 : ℝ) = sval A i ^ 2 := fun i => Real.rpow_natCast _ 2
  simp_rw [hs]
  rw [square_sum_sval_sq, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · rw [← square_sum_sval_sq]; exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- `‖A‖_{S_4}⁴ = tr ((AᵀA)²)`. -/
theorem square_schattenNorm_four_pow (A : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm 4 A ^ 4 = (Aᵀ * A * (Aᵀ * A)).trace := by
  have h4 : ((4 : ℝ≥0∞)).toReal = 4 := by norm_num
  simp only [schattenNorm, ENNReal.ofNat_ne_top, ite_false, h4]
  have hs : ∀ i, sval A i ^ (4 : ℝ) = sval A i ^ 4 := fun i => Real.rpow_natCast _ 4
  simp_rw [hs]
  rw [square_sum_sval_pow_four, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · rw [← square_sum_sval_pow_four]; exact Finset.sum_nonneg fun i _ => by positivity

/-- The real power version: `‖A‖_{S_4}^{(4 : ℝ)} = tr ((AᵀA)²)`. -/
theorem square_schattenNorm_four_rpow (A : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm 4 A ^ (4 : ℝ) = (Aᵀ * A * (Aᵀ * A)).trace := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, square_schattenNorm_four_pow]

/-- A sum of products separates: `Σ_j Σ_l f_j g_l = (Σ f) (Σ g)`. -/
theorem square_sum_sum_mul {n : ℕ} (f g : Fin n → ℝ) :
    ∑ j, ∑ l, f j * g l = (∑ j, f j) * ∑ l, g l := by
  rw [Finset.sum_mul_sum]

/-- `‖K‖_{S_4}⁴` for the rank-two skew matrix `K = a ⊗ b − b ⊗ a`:
`tr ((KᵀK)²) = 2 σ⁴` with `σ² = |a|² |b|² − ⟨a, b⟩²`, the square of the common value of its two
nonzero singular values (proof of Proposition 6.1). -/
theorem square_trace_skew_rank_two {n : ℕ} (a b : Fin n → ℝ) :
    ((Matrix.of fun i j => a i * b j - b i * a j)ᵀ * (Matrix.of fun i j => a i * b j - b i * a j) *
      ((Matrix.of fun i j => a i * b j - b i * a j)ᵀ *
        (Matrix.of fun i j => a i * b j - b i * a j))).trace =
      2 * ((∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2) ^ 2 := by
  set K : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => a i * b j - b i * a j
  set α := ∑ i, a i ^ 2
  set β := ∑ i, b i ^ 2
  set γ := ∑ i, a i * b i
  have hM : ∀ j l, (Kᵀ * K) j l =
      α * (b j * b l) - γ * (a j * b l + b j * a l) + β * (a j * a l) := by
    intro j l
    simp only [Matrix.mul_apply, Matrix.transpose_apply, K, Matrix.of_apply]
    have : ∀ i, (a i * b j - b i * a j) * (a i * b l - b i * a l) =
        a i ^ 2 * (b j * b l) - a i * b i * (a j * b l + b j * a l) + b i ^ 2 * (a j * a l) :=
      fun i => by ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rfl
  have hE : ∀ j l, (Kᵀ * K) j l * (Kᵀ * K) l j =
      α ^ 2 * (b j ^ 2 * b l ^ 2) + γ ^ 2 * (a j ^ 2 * b l ^ 2) +
      2 * γ ^ 2 * (a j * b j * (a l * b l)) + γ ^ 2 * (b j ^ 2 * a l ^ 2) +
      β ^ 2 * (a j ^ 2 * a l ^ 2) - 2 * α * γ * (a j * b j * b l ^ 2) -
      2 * α * γ * (b j ^ 2 * (a l * b l)) + 2 * α * β * (a j * b j * (a l * b l)) -
      2 * β * γ * (a j ^ 2 * (a l * b l)) - 2 * β * γ * (a j * b j * a l ^ 2) := by
    intro j l; rw [hM, hM]; ring
  have htr : (Kᵀ * K * (Kᵀ * K)).trace = ∑ j, ∑ l, (Kᵀ * K) j l * (Kᵀ * K) l j := by
    rfl
  rw [htr]
  simp_rw [hE]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- `‖diag (c)‖_{S_4}⁴ = Σ c_i⁴`. -/
theorem square_trace_diagonal_four {n : ℕ} (c : Fin n → ℝ) :
    ((Matrix.diagonal c)ᵀ * Matrix.diagonal c * ((Matrix.diagonal c)ᵀ * Matrix.diagonal c)).trace =
      ∑ i, c i ^ 4 := by
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  congr 1; funext i; ring

end Cassese
