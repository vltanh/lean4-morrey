module

public import Morrey.Cassese.Square.Moments
public import Morrey.Cassese.Square.Schatten
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The torus witness of Proposition 6.1: singular values and moments

The ingredients of the proof of Proposition 6.1 (TeX lines 2223–2275) that do not involve the
integrand (30):

* the singular values of the rank-two skew matrix `K = a ⊗ b − b ⊗ a`: its only nonzero singular
  values are both equal to `σ = (|a|² |b|² − ⟨a, b⟩²)^{1/2}`, so `‖K‖_{S_q} = 2^{1/q} σ` for every
  `q ∈ [1, ∞]` (`square_schattenNorm_skew_two`). With `G = KᵀK`, `G² = σ² G` and `tr G = 2σ²`:
  every eigenvalue of `G` is `0` or `σ²`, and exactly two are `σ²` when `σ ≠ 0`;
* the Schatten norms of a diagonal matrix: `‖diag (c)‖_{S_q} ≤ n^{1/q} max |c_i|`
  (`square_schattenNorm_diagonal_le`);
* the moments of `Z = Σ_j e^{i θ_j}` (TeX 2262–2268): the exact formula
  `E |Z|^{2m} = Σ_{k₁ + ⋯ + k_d = m} (m; k₁, …, k_d)²` (`square_moment_zc_eq`), from
  `|Z|^{2m} = Z^m conj (Z^m)`, the multinomial theorem `Z^m = Σ_{|k| = m} (m; k) e^{i ⟨k, θ⟩}` and
  the orthogonality `E e^{i ⟨k − l, θ⟩} = [k = l]` (`square_integral_cube_prod_cexp`, the product
  over the coordinates of the one-dimensional `square_integral_cexp_int`); and the bound
  `E |Z|^{2m} ≤ m! d^m` (`square_moment_zc`), from `(m; k) ≤ m!` and `Σ_{|k| = m} (m; k) = d^m`;
* the monotonicity of `L^p` norms on the unit cube (a probability space), by Jensen's inequality
  (`square_cube_lp_mono`), and the resulting `‖Z‖_{L^p} ≤ √(p d)` for `p ≥ 1`
  (`square_lp_zc_le`): `‖Z‖_{L^p} ≤ ‖Z‖_{L^{2m}} ≤ (m! d^m)^{1/(2m)} ≤ √(m d)` with
  `m = ⌈p/2⌉ ≤ p`.

The angles are `θ_j = 2π x_j`, `x ∈ (0, 1)^d`.
-/

@[expose] public section

open MeasureTheory Real
open scoped Matrix ENNReal

namespace Cassese

/-! ### The rank-two skew matrix `a ⊗ b − b ⊗ a` -/

/-- The eigenvalues of a symmetric `G` with `G² = c G` satisfy `λ² = c λ`. -/
theorem square_eigenvalues_sq_of_mul_self {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.IsHermitian) {c : ℝ} (h : G * G = c • G) (i : Fin n) :
    hG.eigenvalues i ^ 2 = c * hG.eigenvalues i := by
  set U := (hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hsp := square_spectral hG
  have hD : Matrix.diagonal hG.eigenvalues = star U * G * U := by
    calc Matrix.diagonal hG.eigenvalues = (star U * U) * Matrix.diagonal hG.eigenvalues *
          (star U * U) := by rw [hU, Matrix.one_mul, Matrix.mul_one]
      _ = star U * (U * Matrix.diagonal hG.eigenvalues * star U) * U := by
          simp only [Matrix.mul_assoc]
      _ = star U * G * U := by rw [← hsp]
  have hDD : Matrix.diagonal hG.eigenvalues * Matrix.diagonal hG.eigenvalues =
      c • Matrix.diagonal hG.eigenvalues := by
    calc Matrix.diagonal hG.eigenvalues * Matrix.diagonal hG.eigenvalues =
          star U * G * (U * star U) * G * U := by rw [hD]; simp only [Matrix.mul_assoc]
      _ = star U * (G * G) * U := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = c • Matrix.diagonal hG.eigenvalues := by
          rw [h, hD, Matrix.mul_smul, Matrix.smul_mul]
  have := congrFun (congrFun hDD i) i
  rw [Matrix.diagonal_mul_diagonal, Matrix.smul_apply, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_eq, smul_eq_mul] at this
  rw [sq, this]

/-- The Gram matrix of `K = a ⊗ b − b ⊗ a`: `KᵀK = u ⊗ a + v ⊗ b` with `u = |b|² a − ⟨a, b⟩ b`,
`v = |a|² b − ⟨a, b⟩ a`. -/
theorem square_skew_two_gram_apply {n : ℕ} (a b : Fin n → ℝ) (i k : Fin n) :
    ((Matrix.of fun i j => a i * b j - b i * a j)ᴴ * (Matrix.of fun i j => a i * b j - b i * a j))
        i k =
      ((∑ j, b j ^ 2) * a i - (∑ j, a j * b j) * b i) * a k +
        ((∑ j, a j ^ 2) * b i - (∑ j, a j * b j) * a i) * b k := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
  have : ∀ j, (a j * b i - b j * a i) * (a j * b k - b j * a k) =
      a j ^ 2 * (b i * b k) - a j * b j * (a i * b k + b i * a k) + b j ^ 2 * (a i * a k) :=
    fun j => by ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- `G = KᵀK` satisfies `G² = σ² G` and `tr G = 2 σ²`, `σ² = |a|² |b|² − ⟨a, b⟩²`. -/
theorem square_skew_two_gram {n : ℕ} (a b : Fin n → ℝ) :
    let K : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => a i * b j - b i * a j
    (Kᴴ * K) * (Kᴴ * K) =
        ((∑ j, a j ^ 2) * (∑ j, b j ^ 2) - (∑ j, a j * b j) ^ 2) • (Kᴴ * K) ∧
      (Kᴴ * K).trace = 2 * ((∑ j, a j ^ 2) * (∑ j, b j ^ 2) - (∑ j, a j * b j) ^ 2) := by
  intro K
  set α := ∑ j, a j ^ 2
  set β := ∑ j, b j ^ 2
  set γ := ∑ j, a j * b j
  set u : Fin n → ℝ := fun i => β * a i - γ * b i
  set v : Fin n → ℝ := fun i => α * b i - γ * a i
  have hG : ∀ i k, (Kᴴ * K) i k = u i * a k + v i * b k := square_skew_two_gram_apply a b
  have hau : ∑ j, a j * u j = α * β - γ ^ 2 := by
    simp only [u, mul_sub, Finset.sum_sub_distrib]
    rw [show ∑ j, a j * (β * a j) = β * α by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring,
      show ∑ j, a j * (γ * b j) = γ * γ by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    ring
  have hav : ∑ j, a j * v j = 0 := by
    simp only [v, mul_sub, Finset.sum_sub_distrib]
    rw [show ∑ j, a j * (α * b j) = α * γ by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring,
      show ∑ j, a j * (γ * a j) = γ * α by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    ring
  have hbu : ∑ j, b j * u j = 0 := by
    simp only [u, mul_sub, Finset.sum_sub_distrib]
    rw [show ∑ j, b j * (β * a j) = β * γ by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring,
      show ∑ j, b j * (γ * b j) = γ * β by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    ring
  have hbv : ∑ j, b j * v j = α * β - γ ^ 2 := by
    simp only [v, mul_sub, Finset.sum_sub_distrib]
    rw [show ∑ j, b j * (α * b j) = α * β by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring,
      show ∑ j, b j * (γ * a j) = γ * γ by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    ring
  refine ⟨?_, ?_⟩
  · ext i k
    rw [Matrix.mul_apply, Matrix.smul_apply, hG, smul_eq_mul]
    simp_rw [hG]
    have : ∀ j, (u i * a j + v i * b j) * (u j * a k + v j * b k) =
        u i * a k * (a j * u j) + u i * b k * (a j * v j) + v i * a k * (b j * u j) +
          v i * b k * (b j * v j) := fun j => by ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, hau, hav, hbu, hbv]
    ring
  · rw [Matrix.trace]
    simp only [Matrix.diag, hG]
    rw [Finset.sum_add_distrib]
    have e1 : ∑ i, u i * a i = α * β - γ ^ 2 := by
      rw [← hau]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have e2 : ∑ i, v i * b i = α * β - γ ^ 2 := by
      rw [← hbv]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e1, e2]; ring

/-- Lagrange's identity gives `σ² ≥ 0`. -/
theorem square_skew_two_sigma_nonneg {n : ℕ} (a b : Fin n → ℝ) :
    0 ≤ (∑ j, a j ^ 2) * (∑ j, b j ^ 2) - (∑ j, a j * b j) ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  linarith

/-- The singular values of `K = a ⊗ b − b ⊗ a`: `Σ_i s_i (K)^r = 2 σ^r` for `r > 0`. -/
theorem square_sum_sval_skew_two {n : ℕ} (a b : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    ∑ i, sval (Matrix.of fun i j => a i * b j - b i * a j) i ^ r =
      2 * √((∑ j, a j ^ 2) * (∑ j, b j ^ 2) - (∑ j, a j * b j) ^ 2) ^ r := by
  set K : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => a i * b j - b i * a j
  set c := (∑ j, a j ^ 2) * (∑ j, b j ^ 2) - (∑ j, a j * b j) ^ 2
  have hc0 : 0 ≤ c := square_skew_two_sigma_nonneg a b
  obtain ⟨hGG, htr⟩ := square_skew_two_gram a b
  set hG := Matrix.isHermitian_conjTranspose_mul_self K
  have hsq := square_eigenvalues_sq_of_mul_self hG hGG
  have hval : ∀ i, hG.eigenvalues i = 0 ∨ hG.eigenvalues i = c := fun i => by
    have h := hsq i
    have : hG.eigenvalues i * (hG.eigenvalues i - c) = 0 := by rw [mul_sub, ← sq, h]; ring
    rcases mul_eq_zero.1 this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  have hsum : ∑ i, hG.eigenvalues i = 2 * c := by
    rw [← htr, hG.trace_eq_sum_eigenvalues]; rfl
  set S := Finset.univ.filter fun i => hG.eigenvalues i = c
  have hsplit : ∀ f : ℝ → ℝ, f 0 = 0 → ∑ i, f (hG.eigenvalues i) = S.card * f c := by
    intro f hf
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => hG.eigenvalues i = c)]
    rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2],
      Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_eq_zero fun i hi => by
      rw [((hval i).resolve_right (Finset.mem_filter.1 hi).2), hf], add_zero]
  simp only [sval]
  rw [hsplit (fun x => √x ^ r) (by simp [Real.zero_rpow hr.ne'])]
  rcases hc0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp [Real.zero_rpow hr.ne']
  · have := hsplit id rfl
    simp only [id] at this
    rw [hsum] at this
    have hcard : (S.card : ℝ) = 2 := by
      have := this.symm
      field_simp at this
      linarith
    rw [hcard]

/-- `max_i s_i (a ⊗ b − b ⊗ a) = σ`. -/
theorem square_iSup_sval_skew_two {n : ℕ} (a b : Fin n → ℝ) :
    ⨆ i, sval (Matrix.of fun i j => a i * b j - b i * a j) i =
      √((∑ j, a j ^ 2) * (∑ j, b j ^ 2) - (∑ j, a j * b j) ^ 2) := by
  set K : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => a i * b j - b i * a j
  set c := (∑ j, a j ^ 2) * (∑ j, b j ^ 2) - (∑ j, a j * b j) ^ 2
  have hc0 : 0 ≤ c := square_skew_two_sigma_nonneg a b
  obtain ⟨hGG, htr⟩ := square_skew_two_gram a b
  set hG := Matrix.isHermitian_conjTranspose_mul_self K
  have hsq := square_eigenvalues_sq_of_mul_self hG hGG
  have hval : ∀ i, hG.eigenvalues i = 0 ∨ hG.eigenvalues i = c := fun i => by
    have h := hsq i
    have : hG.eigenvalues i * (hG.eigenvalues i - c) = 0 := by rw [mul_sub, ← sq, h]; ring
    rcases mul_eq_zero.1 this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  have hsum : ∑ i, hG.eigenvalues i = 2 * c := by
    rw [← htr, hG.trace_eq_sum_eigenvalues]; rfl
  have hle : ∀ i, sval K i ≤ √c := fun i => by
    simp only [sval]
    rcases hval i with h | h
    · rw [h, Real.sqrt_zero]; exact Real.sqrt_nonneg _
    · rw [h]
  rcases hc0.eq_or_lt with h0 | hpos
  · have : ∀ i, sval K i = 0 := fun i =>
      le_antisymm ((hle i).trans (by rw [← h0, Real.sqrt_zero])) (square_sval_nonneg K i)
    simp only [this, Real.iSup_const_zero, ← h0, Real.sqrt_zero]
  · -- some eigenvalue equals `σ²`, since they sum to `2 σ² > 0`
    obtain ⟨i, hi⟩ : ∃ i, hG.eigenvalues i = c := by
      by_contra hne
      push Not at hne
      have : ∑ i, hG.eigenvalues i = 0 :=
        Finset.sum_eq_zero fun i _ => (hval i).resolve_right (hne i)
      linarith
    have : Nonempty (Fin n) := ⟨i⟩
    refine le_antisymm (ciSup_le hle) ?_
    calc √c = sval K i := by simp only [sval]; rw [hi]
      _ ≤ ⨆ i, sval K i := le_ciSup (Set.finite_range _).bddAbove i

/-- **The Schatten norms of the rank-two skew matrix** (proof of Proposition 6.1): the only
possibly nonzero singular values of `K = a ⊗ b − b ⊗ a` are both equal to
`σ = (|a|² |b|² − ⟨a, b⟩²)^{1/2}`, so `‖K‖_{S_q} = 2^{1/q} σ` for every `q ∈ [1, ∞]`
(`1/∞ = 0`). -/
theorem square_schattenNorm_skew_two {n : ℕ} (a b : Fin n → ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    schattenNorm q (Matrix.of fun i j => a i * b j - b i * a j) =
      (2 : ℝ) ^ (1 / q.toReal) *
        √((∑ j, a j ^ 2) * (∑ j, b j ^ 2) - (∑ j, a j * b j) ^ 2) := by
  unfold schattenNorm
  split_ifs with ht
  · rw [square_iSup_sval_skew_two, ht, ENNReal.toReal_top, div_zero, Real.rpow_zero, one_mul]
  · have hr : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq).ne' ht
    rw [square_sum_sval_skew_two a b hr, Real.mul_rpow (by norm_num)
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _), ← Real.rpow_mul (Real.sqrt_nonneg _),
      mul_one_div_cancel hr.ne', Real.rpow_one]

/-! ### Diagonal matrices -/

theorem square_diagonal_gram {n : ℕ} (c : Fin n → ℝ) :
    (Matrix.diagonal c)ᴴ * Matrix.diagonal c =
      ((1 : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal (fun i => c i ^ 2) *
        star ((1 : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  simp only [star_trivial, Pi.star_apply, OneMemClass.coe_one, star_one, Matrix.one_mul,
    Matrix.mul_one]
  congr 1; funext i; ring

/-- The singular values of `diag (c)` are the `|c_i|`, up to order. -/
theorem square_sum_sval_diagonal {n : ℕ} (c : Fin n → ℝ) (f : ℝ → ℝ) :
    ∑ i, f (sval (Matrix.diagonal c) i) = ∑ i, f |c i| := by
  have := square_sum_eigenvalues_eq (Matrix.isHermitian_conjTranspose_mul_self
    (Matrix.diagonal c)) _ _ (square_diagonal_gram c) (fun x => f √x)
  simp only [sval]
  rw [this]
  simp_rw [Real.sqrt_sq_eq_abs]

theorem square_iSup_sval_diagonal {n : ℕ} (c : Fin n → ℝ) :
    ⨆ i, sval (Matrix.diagonal c) i = ⨆ i, |c i| := by
  have := square_iSup_eigenvalues_eq (Matrix.isHermitian_conjTranspose_mul_self
    (Matrix.diagonal c)) _ _ (square_diagonal_gram c) (fun x => √x)
  simp only [sval]
  rw [this]
  simp_rw [Real.sqrt_sq_eq_abs]

/-- `‖diag (c)‖_{S_q} ≤ n^{1/q} M` when every `|c_i| ≤ M`. -/
theorem square_schattenNorm_diagonal_le {n : ℕ} (c : Fin n → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, |c i| ≤ M) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    schattenNorm q (Matrix.diagonal c) ≤ (n : ℝ) ^ (1 / q.toReal) * M := by
  unfold schattenNorm
  split_ifs with ht
  · rw [ht, ENNReal.toReal_top, div_zero, Real.rpow_zero, one_mul, square_iSup_sval_diagonal]
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · rw [Real.iSup_of_isEmpty]; exact hM0
    · exact ciSup_le hM
  · have hr : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq).ne' ht
    rw [square_sum_sval_diagonal c (fun x => x ^ q.toReal)]
    have := square_lp_le_card_mul_max Finset.univ (f := fun i => |c i|) (fun i => abs_nonneg _) hr
      (fun i _ => hM i)
    simpa only [Finset.card_univ, Fintype.card_fin] using this

/-! ### The moments of `Z = Σ_j e^{2πi x_j}` -/

/-- `e (t) = e^{2πit}`. -/
noncomputable def square_cexp (t : ℝ) : ℂ := Complex.exp (↑(2 * π * t) * Complex.I)

/-- `Z (x) = Σ_j e^{2πi x_j}`. -/
noncomputable def square_zc {n : ℕ} (x : Fin n → ℝ) : ℂ := ∑ j, square_cexp (x j)

theorem square_continuous_cexp : Continuous square_cexp := by
  unfold square_cexp; fun_prop

theorem square_continuous_zc {n : ℕ} : Continuous (square_zc (n := n)) := by
  unfold square_zc
  exact continuous_finsetSum _ fun j _ => square_continuous_cexp.comp (continuous_apply j)

theorem square_norm_cexp (t : ℝ) : ‖square_cexp t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- `|Z|² = (Σ cos θ_j)² + (Σ sin θ_j)²`. -/
theorem square_norm_zc_sq {n : ℕ} (x : Fin n → ℝ) :
    ‖square_zc x‖ ^ 2 = (∑ j, cos (2 * π * x j)) ^ 2 + (∑ j, sin (2 * π * x j)) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, square_zc, Complex.re_sum, Complex.im_sum]
  simp only [square_cexp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- `|Z| ≤ d`. -/
theorem square_norm_zc_le {n : ℕ} (x : Fin n → ℝ) : ‖square_zc x‖ ≤ n := by
  calc ‖square_zc x‖ ≤ ∑ j, ‖square_cexp (x j)‖ := norm_sum_le _ _
    _ = n := by simp [square_norm_cexp]

/-- `e (t)^k conj (e (t))^l = e^{2πi (k − l) t}`. -/
theorem square_cexp_pow_mul_conj_pow (t : ℝ) (k l : ℕ) :
    square_cexp t ^ k * (starRingEnd ℂ) (square_cexp t) ^ l =
      Complex.exp (↑(2 * π * ((k : ℤ) - l : ℤ) * t) * Complex.I) := by
  simp only [square_cexp, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `∫₀¹ e^{2πi n t} dt = [n = 0]` for an integer `n`. -/
theorem square_integral_cexp_int (k : ℤ) :
    ∫ t in Set.Ioo (0:ℝ) 1, Complex.exp (↑(2 * π * k * t) * Complex.I) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero]
    rw [setIntegral_const]; simp
  · have hIoo : ∀ g : ℝ → ℂ, ∫ t in Set.Ioo (0:ℝ) 1, g t = ∫ t in (0:ℝ)..1, g t := fun g => by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    rw [hIoo]
    have hc : (2 * π * k * Complex.I : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := Int.cast_ne_zero.2 hk
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) this) Complex.I_ne_zero
    have e : ∀ t : ℝ, Complex.exp (↑(2 * π * k * t) * Complex.I) =
        Complex.exp ((2 * π * k * Complex.I) * t) := fun t => by
      congr 1; push_cast; ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * π * k * Complex.I) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * π * k * Complex.I) * ((1 : ℝ) : ℂ) = k * (2 * π * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h1, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, zero_div]

/-- **Orthogonality on the unit cube**: for `k, l ∈ ℕ^n`,
`∫_{(0,1)^n} e^{2πi ⟨k − l, x⟩} dx = [k = l]`. The integrand is the product of the one-dimensional
characters `e^{2πi (k_i − l_i) x_i}`, so the integral over the product measure is the product of
the integrals (`integral_fintype_prod_eq_prod`), each of which is `[k_i = l_i]`
(`square_integral_cexp_int`). -/
theorem square_integral_cube_prod_cexp {n : ℕ} (k l : Fin n → ℕ) :
    ∫ x in unitCube n, ∏ i, Complex.exp (↑(2 * π * ((k i : ℤ) - l i : ℤ) * x i) * Complex.I) =
      if k = l then 1 else 0 := by
  rw [square_restrict_unitCube, integral_fintype_prod_eq_prod
    (fun i t => Complex.exp (↑(2 * π * ((k i : ℤ) - l i : ℤ) * t) * Complex.I))]
  simp_rw [square_integral_cexp_int, Fintype.prod_boole, sub_eq_zero, Nat.cast_inj, ← funext_iff]

/-- **The moments of `Z`, exactly** (proof of Proposition 6.1, TeX 2262–2268):
`E |Z|^{2m} = Σ_{k₁ + ⋯ + k_d = m} (m; k₁, …, k_d)²`. As in the paper: `|Z|^{2m} = Z^m conj (Z^m)`,
the multinomial theorem `Z^m = Σ_{|k| = m} (m; k) e^{2πi ⟨k, x⟩}`
(`Finset.sum_pow_eq_sum_piAntidiag`), and the orthogonality
`∫ e^{2πi ⟨k − l, x⟩} dx = [k = l]` (`square_integral_cube_prod_cexp`). -/
theorem square_moment_zc_eq (n m : ℕ) :
    ∫ x in unitCube n, ‖square_zc x‖ ^ (2 * m) =
      ∑ k ∈ (Finset.univ : Finset (Fin n)).piAntidiag m,
        (Nat.multinomial Finset.univ k : ℝ) ^ 2 := by
  set A := (Finset.univ : Finset (Fin n)).piAntidiag m
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  -- `|Z|^{2m} = Z^m conj (Z^m)`, expanded by the multinomial theorem
  have hpt : ∀ x : Fin n → ℝ, ((‖square_zc x‖ ^ (2 * m) : ℝ) : ℂ) =
      ∑ k ∈ A, ∑ l ∈ A,
        ((Nat.multinomial Finset.univ k : ℂ) * (Nat.multinomial Finset.univ l : ℂ)) *
          ∏ i, Complex.exp (↑(2 * π * ((k i : ℤ) - l i : ℤ) * x i) * Complex.I) := by
    intro x
    rw [pow_mul, Complex.ofReal_pow, Complex.ofReal_pow, ← Complex.mul_conj', mul_pow, ← map_pow,
      square_zc, Finset.sum_pow_eq_sum_piAntidiag, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.prod_congr rfl fun i _ => (square_cexp_pow_mul_conj_pow (x i) (k i) (l i)).symm,
      Finset.prod_mul_distrib, map_mul, map_natCast, map_prod]
    simp only [map_pow]
    ring
  simp_rw [hpt]
  have hint : ∀ (c : ℂ) (k l : Fin n → ℕ), Integrable
      (fun x : Fin n → ℝ =>
        c * ∏ i, Complex.exp (↑(2 * π * ((k i : ℤ) - l i : ℤ) * x i) * Complex.I))
      (volume.restrict (unitCube n)) := fun c k l =>
    ((Continuous.continuousOn (by fun_prop)).integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
      (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self)
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint _ k l]
  simp_rw [integral_finsetSum _ fun l _ => hint _ _ l, integral_const_mul,
    square_integral_cube_prod_cexp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [ite_eq_left hk, sq]

/-- **The moments of `Z`** (proof of Proposition 6.1, TeX 2262–2268): `E |Z|^{2m} ≤ m! d^m`. From
the exact formula `E |Z|^{2m} = Σ_{|k| = m} (m; k)²` (`square_moment_zc_eq`), with
`(m; k) ≤ m!` (`Nat.multinomial_spec`: `(∏_i k_i!) (m; k) = m!`) and `Σ_{|k| = m} (m; k) = d^m`
(the multinomial theorem with all terms `1`): `Σ_k (m; k)² ≤ m! Σ_k (m; k) = m! d^m`. -/
theorem square_moment_zc (n m : ℕ) :
    ∫ x in unitCube n, ‖square_zc x‖ ^ (2 * m) ≤ (m.factorial : ℝ) * (n : ℝ) ^ m := by
  rw [square_moment_zc_eq]
  set A := (Finset.univ : Finset (Fin n)).piAntidiag m
  have hsum : ∑ k ∈ A, (Nat.multinomial Finset.univ k : ℝ) = (n : ℝ) ^ m := by
    have := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℝ)) m
    simpa using this.symm
  have hle : ∀ k ∈ A, (Nat.multinomial Finset.univ k : ℝ) ≤ m.factorial := by
    intro k hk
    have hspec := Nat.multinomial_spec Finset.univ k
    rw [(Finset.mem_piAntidiag.1 hk).1] at hspec
    exact_mod_cast (Nat.le_mul_of_pos_left _
      (Finset.prod_pos fun i _ => Nat.factorial_pos (k i))).trans hspec.le
  calc ∑ k ∈ A, (Nat.multinomial Finset.univ k : ℝ) ^ 2
      ≤ ∑ k ∈ A, (m.factorial : ℝ) * Nat.multinomial Finset.univ k :=
        Finset.sum_le_sum fun k hk => by
          rw [sq]; exact mul_le_mul_of_nonneg_right (hle k hk) (Nat.cast_nonneg _)
    _ = (m.factorial : ℝ) * (n : ℝ) ^ m := by rw [← Finset.mul_sum, hsum]

/-! ### `L^p` norms on the unit cube -/

instance square_isProbabilityMeasure_cube (n : ℕ) :
    IsProbabilityMeasure (volume.restrict (unitCube n)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact Sverak.volume_unitCube⟩

/-- **Monotonicity of `L^p` norms** on the unit cube (a probability space), by Jensen's
inequality: `(∫ f^p)^{1/p} ≤ (∫ f^{p'})^{1/p'}` for `0 < p ≤ p'` and a continuous `f ≥ 0`. -/
theorem square_cube_lp_mono {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) {p p' : ℝ} (hp : 0 < p) (hpp : p ≤ p') :
    (∫ x in unitCube n, f x ^ p) ^ (1 / p) ≤ (∫ x in unitCube n, f x ^ p') ^ (1 / p') := by
  have hp' : 0 < p' := hp.trans_le hpp
  have hr : 1 ≤ p' / p := (one_le_div hp).2 hpp
  have hfp : Continuous fun x => f x ^ p := hf.rpow_const fun x => Or.inr hp.le
  have hcomp : (fun x => (f x ^ p) ^ (p' / p)) = fun x => f x ^ p' := funext fun x => by
    rw [← Real.rpow_mul (hf0 x), mul_div_cancel₀ _ hp.ne']
  have hJ := (convexOn_rpow hr).map_integral_le (μ := volume.restrict (unitCube n))
    (f := fun x => f x ^ p) (Real.continuous_rpow_const (by linarith)).continuousOn isClosed_Ici
    (ae_of_all _ fun x => Real.rpow_nonneg (hf0 x) p) (square_integrableOn_cube hfp)
    (by
      show Integrable ((fun x => x ^ (p' / p)) ∘ fun x => f x ^ p) (volume.restrict (unitCube n))
      rw [Function.comp_def, hcomp]
      exact square_integrableOn_cube (hf.rpow_const fun x => Or.inr hp'.le))
  simp only [hcomp] at hJ
  have hI0 : 0 ≤ ∫ x in unitCube n, f x ^ p :=
    setIntegral_nonneg (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
      fun x _ => Real.rpow_nonneg (hf0 x) p
  calc (∫ x in unitCube n, f x ^ p) ^ (1 / p) =
        ((∫ x in unitCube n, f x ^ p) ^ (p' / p)) ^ (1 / p') := by
        rw [← Real.rpow_mul hI0]; congr 1; field_simp
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hJ (by positivity)

/-- `‖Z‖_{L^p} ≤ √(p d)` for `p ≥ 1` (proof of Proposition 6.1): with `m = ⌈p/2⌉ ≤ p`,
`‖Z‖_{L^p} ≤ ‖Z‖_{L^{2m}} ≤ (m! d^m)^{1/(2m)} ≤ √(m d)`. -/
theorem square_lp_zc_le (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (∫ x in unitCube n, ‖square_zc x‖ ^ p) ^ (1 / p) ≤ √(p * n) := by
  have hp0 : 0 < p := by linarith
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
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hcz := square_continuous_zc (n := n)
  have hmono := square_cube_lp_mono hcz.norm (fun x => norm_nonneg _) hp0 hpm
  have h2m : ∫ x in unitCube n, ‖square_zc x‖ ^ ((2 * m : ℕ) : ℝ) ≤ (m.factorial : ℝ) * n ^ m := by
    simp_rw [Real.rpow_natCast]; exact square_moment_zc n m
  have hI0 : 0 ≤ ∫ x in unitCube n, ‖square_zc x‖ ^ ((2 * m : ℕ) : ℝ) :=
    setIntegral_nonneg (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
      fun x _ => Real.rpow_nonneg (norm_nonneg _) _
  have hfact : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (∫ x in unitCube n, ‖square_zc x‖ ^ p) ^ (1 / p)
      ≤ (∫ x in unitCube n, ‖square_zc x‖ ^ (2 * (m : ℝ))) ^ (1 / (2 * (m : ℝ))) := hmono
    _ ≤ ((m : ℝ) ^ m * n ^ m) ^ (1 / (2 * (m : ℝ))) := by
        rw [show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring]
        exact Real.rpow_le_rpow hI0 (h2m.trans (mul_le_mul_of_nonneg_right hfact (by positivity)))
          (by positivity)
    _ = √(m * n) := by
        rw [← mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
        congr 1; field_simp
    _ ≤ √(p * n) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmp hn0)

/-- `‖Z‖_{L^p} ≤ d`, from `|Z| ≤ d`. -/
theorem square_lp_zc_le_card (n : ℕ) {p : ℝ} (hp : 0 < p) :
    (∫ x in unitCube n, ‖square_zc x‖ ^ p) ^ (1 / p) ≤ n := by
  have hle : ∫ x in unitCube n, ‖square_zc x‖ ^ p ≤ ∫ _x in unitCube n, (n : ℝ) ^ p :=
    setIntegral_mono (square_integrableOn_cube
      (square_continuous_zc.norm.rpow_const fun x => Or.inr hp.le))
      (square_integrableOn_cube continuous_const)
      fun x => Real.rpow_le_rpow (norm_nonneg _) (square_norm_zc_le x) hp.le
  rw [square_integral_cube_const] at hle
  calc (∫ x in unitCube n, ‖square_zc x‖ ^ p) ^ (1 / p) ≤ ((n : ℝ) ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (setIntegral_nonneg (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
          fun x _ => Real.rpow_nonneg (norm_nonneg _) _) hle (by positivity)
    _ = n := by rw [← Real.rpow_mul (Nat.cast_nonneg n), mul_one_div_cancel hp.ne',
          Real.rpow_one]

end Cassese
