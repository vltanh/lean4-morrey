module

public import Morrey.Cassese.Square.Trace
public import Mathlib.Analysis.MeanInequalities

/-!
# Spectral tools for the Schatten norms

The singular values `s_i (A) = √λ_i (AᴴA)` enter the Schatten norms only through the multiset of
the eigenvalues of `AᴴA`, which is the multiset of roots of the characteristic polynomial
(`Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`). If `B = U diag (μ) Uᴴ` with `U` unitary,
that multiset is the multiset of the `μ_i` (`square_eigenvalues_map_eq`), so sums and suprema of
functions of the eigenvalues can be computed from any unitary diagonalization
(`square_sum_eigenvalues_eq`, `square_iSup_eigenvalues_eq`). This gives the behaviour of the
singular values under scaling (`s_i (c A) = |c| s_i (A)`) and under squaring a symmetric matrix
(`s_i (A²) = s_i (A)²`), from which facts (1) of Section 1.5 and the absolute homogeneity of the
Schatten norms follow (Bhatia, *Matrix analysis*, Chapter IV).
-/

@[expose] public section

open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-- The spectral theorem for a real symmetric matrix: `B = U diag (λ) Uᵀ`. -/
theorem square_spectral {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    B = (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal hB.eigenvalues *
      star (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
  conv_lhs => rw [hB.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  try rfl

/-- The eigenvalues of `B = U diag (μ) Uᴴ` are the `μ_i`, up to order. -/
theorem square_eigenvalues_map_eq {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (μ : Fin n → ℝ)
    (h : B = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ *
      star (U : Matrix (Fin n) (Fin n) ℝ)) :
    Multiset.map hB.eigenvalues Finset.univ.val = Multiset.map μ Finset.univ.val := by
  have hc : B.charpoly = (Matrix.diagonal μ).charpoly := by
    rw [h, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self,
      Matrix.one_mul]
  have h1 := hB.roots_charpoly_eq_eigenvalues
  rw [hc, Matrix.charpoly_diagonal, Polynomial.roots_prod] at h1
  · simpa using h1.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

theorem square_sum_eigenvalues_eq {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (μ : Fin n → ℝ)
    (h : B = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ *
      star (U : Matrix (Fin n) (Fin n) ℝ)) (f : ℝ → ℝ) :
    ∑ i, f (hB.eigenvalues i) = ∑ i, f (μ i) := by
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  show (Multiset.map (f ∘ hB.eigenvalues) _).sum = (Multiset.map (f ∘ μ) _).sum
  rw [← Multiset.map_map, ← Multiset.map_map, square_eigenvalues_map_eq hB U μ h]

theorem square_range_eigenvalues_eq {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (μ : Fin n → ℝ)
    (h : B = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ *
      star (U : Matrix (Fin n) (Fin n) ℝ)) (f : ℝ → ℝ) :
    Set.range (fun i => f (hB.eigenvalues i)) = Set.range fun i => f (μ i) := by
  have hm := congrArg (Multiset.map f) (square_eigenvalues_map_eq hB U μ h)
  simp only [Multiset.map_map] at hm
  ext x
  have e1 : x ∈ Set.range (fun i => f (hB.eigenvalues i)) ↔
      x ∈ Multiset.map (f ∘ hB.eigenvalues) Finset.univ.val := by simp
  have e2 : x ∈ Set.range (fun i => f (μ i)) ↔ x ∈ Multiset.map (f ∘ μ) Finset.univ.val := by
    simp
  rw [e1, e2, hm]

theorem square_iSup_eigenvalues_eq {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (μ : Fin n → ℝ)
    (h : B = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ *
      star (U : Matrix (Fin n) (Fin n) ℝ)) (f : ℝ → ℝ) :
    ⨆ i, f (hB.eigenvalues i) = ⨆ i, f (μ i) := by
  rw [iSup, iSup, square_range_eigenvalues_eq hB U μ h f]

/-- The spectral decomposition of `AᴴA`. -/
theorem square_spectral_gram (A : Matrix (Fin d) (Fin m) ℝ) :
    Aᴴ * A = ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary :
        Matrix (Fin m) (Fin m) ℝ) *
      Matrix.diagonal (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues *
      star ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary :
        Matrix (Fin m) (Fin m) ℝ) :=
  square_spectral _

/-- `Σ_i F (s_i (cA)) = Σ_i F (|c| s_i (A))`. -/
theorem square_sum_sval_smul (c : ℝ) (A : Matrix (Fin d) (Fin m) ℝ) (F : ℝ → ℝ) :
    ∑ i, F (sval (c • A) i) = ∑ i, F (|c| * sval A i) := by
  set hA := Matrix.isHermitian_conjTranspose_mul_self A
  have h : (c • A)ᴴ * (c • A) = (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) *
      Matrix.diagonal (fun i => c ^ 2 * hA.eigenvalues i) *
      star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) := by
    have hd : Matrix.diagonal (fun i => c ^ 2 * hA.eigenvalues i) =
        (c ^ 2) • Matrix.diagonal hA.eigenvalues := by
      ext i j; simp [Matrix.diagonal_apply]
    have hc : (c • A)ᴴ * (c • A) = (c ^ 2) • (Aᴴ * A) := by
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        sq]
    rw [hc, hd, Matrix.mul_smul, Matrix.smul_mul]
    conv_lhs => rw [square_spectral_gram A]
  have := square_sum_eigenvalues_eq (Matrix.isHermitian_conjTranspose_mul_self (c • A)) _ _ h
    (fun x => F √x)
  simp only [sval] at this ⊢
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- `range (s (cA)) = range (|c| s (A))`. -/
theorem square_range_sval_smul (c : ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    Set.range (fun i => sval (c • A) i) = Set.range fun i => |c| * sval A i := by
  set hA := Matrix.isHermitian_conjTranspose_mul_self A
  have h : (c • A)ᴴ * (c • A) = (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) *
      Matrix.diagonal (fun i => c ^ 2 * hA.eigenvalues i) *
      star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) := by
    have hd : Matrix.diagonal (fun i => c ^ 2 * hA.eigenvalues i) =
        (c ^ 2) • Matrix.diagonal hA.eigenvalues := by
      ext i j; simp [Matrix.diagonal_apply]
    have hc : (c • A)ᴴ * (c • A) = (c ^ 2) • (Aᴴ * A) := by
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        sq]
    rw [hc, hd, Matrix.mul_smul, Matrix.smul_mul]
    conv_lhs => rw [square_spectral_gram A]
  have := square_range_eigenvalues_eq (Matrix.isHermitian_conjTranspose_mul_self (c • A)) _ _ h
    (fun x => √x)
  simp only [sval] at this ⊢
  rw [this]
  congr 1; funext i
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- For a symmetric `A`: `Σ_i F (s_i (A²)) = Σ_i F (s_i (A)²)`. -/
theorem square_sum_sval_mul_self {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm) (F : ℝ → ℝ) :
    ∑ i, F (sval (A * A) i) = ∑ i, F (sval A i ^ 2) := by
  set hG := Matrix.isHermitian_conjTranspose_mul_self A
  set U := (hG.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hAA : Aᴴ = A := by rw [square_conjTranspose_eq]; exact hA
  have h : (A * A)ᴴ * (A * A) = U * Matrix.diagonal (fun i => hG.eigenvalues i ^ 2) * star U := by
    have hg : A * A = U * Matrix.diagonal hG.eigenvalues * star U := by
      calc A * A = Aᴴ * A := by rw [hAA]
        _ = _ := square_spectral_gram A
    conv_lhs => rw [Matrix.conjTranspose_mul, hAA, hg]
    have hd : Matrix.diagonal (fun i => hG.eigenvalues i ^ 2) =
        Matrix.diagonal hG.eigenvalues * Matrix.diagonal hG.eigenvalues := by
      rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; ring
    rw [hd]
    calc U * Matrix.diagonal hG.eigenvalues * star U * (U * Matrix.diagonal hG.eigenvalues * star U)
        = U * Matrix.diagonal hG.eigenvalues * (star U * U) * Matrix.diagonal hG.eigenvalues *
            star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have := square_sum_eigenvalues_eq (Matrix.isHermitian_conjTranspose_mul_self (A * A)) _ _ h
    (fun x => F √x)
  simp only [sval] at this ⊢
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.sqrt_sq (square_eigenvalues_nonneg A i), Real.sq_sqrt (square_eigenvalues_nonneg A i)]

/-! ### Finite `ℓ^p` sums -/

/-- Each term is at most the `ℓ^p` sum. -/
theorem square_le_lp {ι : Type*} {s : Finset ι} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) {p : ℝ}
    (hp : 0 < p) {j : ι} (hj : j ∈ s) : f j ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) := by
  have h0 : 0 ≤ ∑ i ∈ s, f i ^ p := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _
  calc f j = (f j ^ p) ^ (1 / p) := by
        rw [← Real.rpow_mul (hf j), mul_one_div_cancel hp.ne', Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (hf j) _)
        (Finset.single_le_sum (fun i _ => Real.rpow_nonneg (hf i) p) hj) (by positivity)

/-- `ℓ^q ≤ ℓ^p` for `0 < p ≤ q` (finite sums of nonnegative terms). -/
theorem square_lq_le_lp {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i ∈ s, f i ^ q) ^ (1 / q) ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) := by
  have hq : 0 < q := hp.trans_le hpq
  set S := (∑ i ∈ s, f i ^ p) ^ (1 / p) with hS
  have hsum0 : 0 ≤ ∑ i ∈ s, f i ^ p := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _
  have hS0 : 0 ≤ S := Real.rpow_nonneg hsum0 _
  have hSp : S ^ p = ∑ i ∈ s, f i ^ p := by
    rw [hS, ← Real.rpow_mul hsum0, one_div_mul_cancel hp.ne', Real.rpow_one]
  have hfi : ∀ i ∈ s, f i ≤ S := fun i hi => square_le_lp hf hp hi
  have key : ∑ i ∈ s, f i ^ q ≤ S ^ q := by
    calc ∑ i ∈ s, f i ^ q = ∑ i ∈ s, f i ^ p * f i ^ (q - p) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Real.rpow_add' (hf i) (by linarith : p + (q - p) ≠ 0), add_sub_cancel]
      _ ≤ ∑ i ∈ s, f i ^ p * S ^ (q - p) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hf i) (hfi i hi) (by linarith)) (Real.rpow_nonneg (hf i) _)
      _ = S ^ p * S ^ (q - p) := by rw [← Finset.sum_mul, hSp]
      _ = S ^ q := by rw [← Real.rpow_add' hS0 (by linarith : p + (q - p) ≠ 0), add_sub_cancel]
  calc (∑ i ∈ s, f i ^ q) ^ (1 / q) ≤ (S ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _) key
          (by positivity)
    _ = S := by rw [← Real.rpow_mul hS0, mul_one_div_cancel hq.ne', Real.rpow_one]

/-- The power-mean inequality: `ℓ^p ≤ |s|^{1/p − 1/q} ℓ^q` for `1 ≤ p ≤ q`. -/
theorem square_lp_le_card_mul_lq {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i)
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    (∑ i ∈ s, f i ^ p) ^ (1 / p) ≤ (s.card : ℝ) ^ (1 / p - 1 / q) * (∑ i ∈ s, f i ^ q) ^ (1 / q) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hr : 1 ≤ q / p := (one_le_div hp0).2 hpq
  have hsum0 : 0 ≤ ∑ i ∈ s, f i ^ p := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _
  have hsumq : 0 ≤ ∑ i ∈ s, f i ^ q := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _
  have hc0 : (0:ℝ) ≤ s.card := Nat.cast_nonneg _
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := s) (f := fun i => f i ^ p) hr
    (fun i _ => Real.rpow_nonneg (hf i) _)
  have hpow : ∀ i, (f i ^ p) ^ (q / p) = f i ^ q := fun i => by
    rw [← Real.rpow_mul (hf i), mul_div_cancel₀ _ hp0.ne']
  simp only [hpow] at h
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hsum0 _) h (by positivity : (0:ℝ) ≤ 1 / q)
  calc (∑ i ∈ s, f i ^ p) ^ (1 / p) = ((∑ i ∈ s, f i ^ p) ^ (q / p)) ^ (1 / q) := by
        rw [← Real.rpow_mul hsum0]; congr 1; field_simp
    _ ≤ ((s.card : ℝ) ^ (q / p - 1) * ∑ i ∈ s, f i ^ q) ^ (1 / q) := h2
    _ = (s.card : ℝ) ^ (1 / p - 1 / q) * (∑ i ∈ s, f i ^ q) ^ (1 / q) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hc0 _) hsumq, ← Real.rpow_mul hc0]
        congr 2; field_simp

/-- `ℓ^p ≤ |s|^{1/p} max` for `p > 0`. -/
theorem square_lp_le_card_mul_max {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i)
    {p : ℝ} (hp : 0 < p) {M : ℝ} (hM : ∀ i ∈ s, f i ≤ M) :
    (∑ i ∈ s, f i ^ p) ^ (1 / p) ≤ (s.card : ℝ) ^ (1 / p) * M := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    rw [Real.zero_rpow (by positivity : (1:ℝ) / p ≠ 0), zero_mul]
  obtain ⟨j, hj⟩ := hne
  have hM0 : 0 ≤ M := (hf j).trans (hM j hj)
  have hsum : ∑ i ∈ s, f i ^ p ≤ s.card * M ^ p := by
    calc ∑ i ∈ s, f i ^ p ≤ ∑ _i ∈ s, M ^ p :=
          Finset.sum_le_sum fun i hi => Real.rpow_le_rpow (hf i) (hM i hi) hp.le
      _ = s.card * M ^ p := by rw [Finset.sum_const, nsmul_eq_mul]
  calc (∑ i ∈ s, f i ^ p) ^ (1 / p) ≤ ((s.card : ℝ) * M ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) _) hsum
          (by positivity)
    _ = (s.card : ℝ) ^ (1 / p) * M := by
        rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM0 _), ← Real.rpow_mul hM0,
          mul_one_div_cancel hp.ne', Real.rpow_one]

/-! ### Singular values -/

/-- At most `min (d, m)` singular values are nonzero (`rank (AᴴA) = rank A`). -/
theorem square_card_sval_ne_zero (A : Matrix (Fin d) (Fin m) ℝ) :
    ((Finset.univ.filter fun i => sval A i ≠ 0).card : ℝ) ≤ min (d : ℝ) (m : ℝ) := by
  have h1 : (Finset.univ.filter fun i => sval A i ≠ 0) =
      Finset.univ.filter fun i => (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i ≠ 0 := by
    refine Finset.filter_congr fun i _ => ?_
    rw [sval, ne_eq, ne_eq, Real.sqrt_eq_zero (square_eigenvalues_nonneg A i)]
  have h2 := (Matrix.isHermitian_conjTranspose_mul_self A).rank_eq_card_non_zero_eigs
  rw [Matrix.rank_conjTranspose_mul_self, Fintype.card_subtype] at h2
  rw [h1, ← h2]
  have h3 : A.rank ≤ min d m := le_min (Matrix.rank_le_height A) (Matrix.rank_le_width A)
  exact_mod_cast h3

/-- The `ℓ^p` sum of the singular values is the sum over the nonzero ones. -/
theorem square_sum_sval_filter (A : Matrix (Fin d) (Fin m) ℝ) {p : ℝ} (hp : 0 < p) :
    ∑ i, sval A i ^ p = ∑ i ∈ Finset.univ.filter (fun i => sval A i ≠ 0), sval A i ^ p := by
  rw [Finset.sum_filter_of_ne]
  intro i _ h hi
  rw [hi, Real.zero_rpow hp.ne'] at h
  exact h rfl

end Cassese
