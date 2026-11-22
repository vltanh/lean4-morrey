module

public import Morrey.Cassese.Square.Schatten
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The triangle inequality for the Schatten norms

The paper takes for granted that `‖·‖_{S_q}`, `q ∈ [1, ∞]`, is a norm on `ℝ^{d×m}` (Section 1.5;
Bhatia, *Matrix analysis*, Chapter IV). The triangle inequality is proved here by the standard
argument through doubly substochastic matrices:

* for `A = Σ_j s_j x_j ⊗ y_j` (`y_j` the eigenvectors of `AᵀA`, `A y_j = s_j x_j`), every
  orthogonal `V` (columns `v_k`) and every `X` (columns `ξ_k`) with `‖ξ_k‖ ≤ 1` and `XXᵀ ⪯ Id`
  (Bessel's inequality for the `ξ_k`),
  `|⟨ξ_k, A v_k⟩| ≤ Σ_j M_{kj} s_j` with `M_{kj} = (⟨ξ_k, A y_j⟩² / s_j² + ⟨y_j, v_k⟩²) / 2`
  doubly substochastic (`square_exists_substochastic`, by `2|ab| ≤ a²/s + s b²` and Bessel's
  inequality `square_bessel`);
* hence, by Jensen's inequality for `t ↦ t^q` (`square_rpow_sum_le`),
  `Σ_k |⟨ξ_k, A v_k⟩|^q ≤ Σ_j s_j^q` (`square_sum_abs_diag_rpow_le`) and
  `|⟨ξ_k, A v_k⟩| ≤ max_j s_j` (`square_abs_diag_le_iSup`);
* for `W = A + B` with its own singular vectors (`v_k` the eigenvectors of `WᵀW`,
  `ξ_k = W v_k / s_k (W)`), `s_k (W) = ⟨ξ_k, A v_k⟩ + ⟨ξ_k, B v_k⟩`, and Minkowski's inequality
  in `ℓ^q` (`Real.Lp_add_le`) gives `‖W‖_{S_q} ≤ ‖A‖_{S_q} + ‖B‖_{S_q}`
  (`square_schattenNorm_add_le`).
-/

@[expose] public section

open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-- Bessel's inequality for a family of orthogonal columns `Y_j` with `‖Y_j‖² = λ_j`:
`Σ_j ⟨w, Y_j⟩² / λ_j ≤ ‖w‖²` (a term with `λ_j = 0` is `0`). -/
theorem square_bessel (Y : Matrix (Fin d) (Fin m) ℝ) (lam : Fin m → ℝ)
    (hY : ∀ j l, ∑ i, Y i j * Y i l = if j = l then lam j else 0) (w : Fin d → ℝ) :
    ∑ j, (∑ i, w i * Y i j) ^ 2 / lam j ≤ ∑ i, w i ^ 2 := by
  set a : Fin m → ℝ := fun j => ∑ i, w i * Y i j with ha
  set c : Fin m → ℝ := fun j => a j / lam j with hc
  set z : Fin d → ℝ := fun i => ∑ j, c j * Y i j with hz
  have h1 : ∑ i, w i * z i = ∑ j, a j ^ 2 / lam j := by
    have e : ∀ j, a j ^ 2 / lam j = c j * ∑ i, w i * Y i j := fun j => by
      simp only [hc, ha]; ring
    simp_rw [e]
    simp only [hz, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, z i ^ 2 = ∑ j, a j ^ 2 / lam j := by
    have e1 : ∑ i, z i ^ 2 = ∑ j, ∑ l, c j * c l * ∑ i, Y i j * Y i l := by
      have : ∀ i, z i ^ 2 = ∑ j, ∑ l, c j * c l * (Y i j * Y i l) := fun i => by
        simp only [hz, sq, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      simp_rw [this, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
    rw [e1]
    simp only [hY, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hc]
    by_cases h : lam j = 0
    · simp [h]
    · field_simp
  set S := ∑ j, a j ^ 2 / lam j
  have hS0 : 0 ≤ S := h2 ▸ Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w z
  rw [h1, h2] at hcs
  have hw0 : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_contra hlt
  push Not at hlt
  have hSpos : 0 < S := lt_of_le_of_lt hw0 hlt
  nlinarith

/-- Jensen's inequality for `t ↦ t^q`, `q ≥ 1`, with weights of total mass at most one:
`(Σ w_i t_i)^q ≤ Σ w_i t_i^q`. -/
theorem square_rpow_sum_le {ι : Type*} (s : Finset ι) {w t : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : ∑ i ∈ s, w i ≤ 1) (ht : ∀ i ∈ s, 0 ≤ t i) {q : ℝ} (hq : 1 ≤ q) :
    (∑ i ∈ s, w i * t i) ^ q ≤ ∑ i ∈ s, w i * t i ^ q := by
  set W := ∑ i ∈ s, w i with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg hw
  rcases hW0.eq_or_lt with h0 | hpos
  · have hz : ∀ i ∈ s, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).1 h0.symm
    rw [Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul],
      Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul], Real.zero_rpow (by linarith)]
  · have hw' : ∑ i ∈ s, w i / W = 1 := by rw [← Finset.sum_div, div_self hpos.ne']
    have hJ := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => w i / W) t
      (fun i hi => div_nonneg (hw i hi) hW0) hw' ht hq
    have e1 : ∑ i ∈ s, w i * t i = W * ∑ i ∈ s, w i / W * t i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have e2 : ∑ i ∈ s, w i * t i ^ q = W * ∑ i ∈ s, w i / W * t i ^ q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have hsum0 : 0 ≤ ∑ i ∈ s, w i / W * t i :=
      Finset.sum_nonneg fun i hi => mul_nonneg (div_nonneg (hw i hi) hW0) (ht i hi)
    have hsumq0 : 0 ≤ ∑ i ∈ s, w i / W * t i ^ q := Finset.sum_nonneg fun i hi =>
      mul_nonneg (div_nonneg (hw i hi) hW0) (Real.rpow_nonneg (ht i hi) _)
    rw [e1, e2, Real.mul_rpow hW0 hsum0]
    calc W ^ q * (∑ i ∈ s, w i / W * t i) ^ q ≤ W ^ q * ∑ i ∈ s, w i / W * t i ^ q :=
          mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hW0 _)
      _ ≤ W * ∑ i ∈ s, w i / W * t i ^ q := by
          refine mul_le_mul_of_nonneg_right ?_ hsumq0
          calc W ^ q ≤ W ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hpos hW hq
            _ = W := Real.rpow_one W

/-- The right singular vectors of `A`: the orthogonal matrix of eigenvectors of `AᵀA`. -/
noncomputable def square_rsv (A : Matrix (Fin d) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)

theorem square_rsv_transpose_mul (A : Matrix (Fin d) (Fin m) ℝ) :
    (square_rsv A)ᵀ * square_rsv A = 1 := by
  have := Unitary.coe_star_mul_self (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this

theorem square_rsv_mul_transpose (A : Matrix (Fin d) (Fin m) ℝ) :
    square_rsv A * (square_rsv A)ᵀ = 1 := by
  have := Unitary.coe_mul_star_self (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this

/-- The columns `A y_j` of `A V` (`V = square_rsv A`) are orthogonal, with `‖A y_j‖² = s_j²`. -/
theorem square_gram_rsv (A : Matrix (Fin d) (Fin m) ℝ) (j l : Fin m) :
    ∑ i, (A * square_rsv A) i j * (A * square_rsv A) i l =
      if j = l then (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j else 0 := by
  set U := square_rsv A
  have h1 : Aᵀ * A = U * Matrix.diagonal (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues *
      Uᵀ := by
    have := square_spectral_gram A
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hYY : (A * U)ᵀ * (A * U) =
      Matrix.diagonal (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues := by
    rw [Matrix.transpose_mul]
    calc Uᵀ * Aᵀ * (A * U) = Uᵀ * (Aᵀ * A) * U := by simp only [Matrix.mul_assoc]
      _ = Uᵀ * U * Matrix.diagonal (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues *
            (Uᵀ * U) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [square_rsv_transpose_mul, Matrix.one_mul, Matrix.mul_one]
  have := congrFun (congrFun hYY j) l
  rw [Matrix.mul_apply, Matrix.diagonal_apply] at this
  simpa only [Matrix.transpose_apply] using this

/-- For orthogonal `O`, the squares of the entries of each column sum to `1`. -/
theorem square_sum_sq_col {O : Matrix (Fin m) (Fin m) ℝ} (hO : Oᵀ * O = 1) (k : Fin m) :
    ∑ j, O j k ^ 2 = 1 := by
  have := congrFun (congrFun hO k) k
  simpa [Matrix.mul_apply, Matrix.transpose_apply, sq] using this

/-- **The substochastic domination.** For `A ∈ ℝ^{d×m}`, an orthogonal `V` and an `X` whose
columns have norm at most one and satisfy Bessel's inequality, the diagonal entries of `XᵀAV` are
dominated by a doubly substochastic average of the singular values of `A`. -/
theorem square_exists_substochastic (A : Matrix (Fin d) (Fin m) ℝ) {V : Matrix (Fin m) (Fin m) ℝ}
    (hV1 : Vᵀ * V = 1) (hV2 : V * Vᵀ = 1) {X : Matrix (Fin d) (Fin m) ℝ}
    (hX1 : ∀ k, ∑ i, X i k ^ 2 ≤ 1)
    (hX2 : ∀ w : Fin d → ℝ, ∑ k, (∑ i, w i * X i k) ^ 2 ≤ ∑ i, w i ^ 2) :
    ∃ M : Fin m → Fin m → ℝ, (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j ≤ 1) ∧
      (∀ j, ∑ k, M k j ≤ 1) ∧ ∀ k, |(Xᵀ * A * V) k k| ≤ ∑ j, M k j * sval A j := by
  have hY := square_gram_rsv A
  have hlam : ∀ j, 0 ≤ (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j :=
    square_eigenvalues_nonneg A
  have hs2 : ∀ j, sval A j ^ 2 = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j :=
    square_sval_sq A
  set U := square_rsv A
  set lam := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues
  set Y := A * U
  set P := Xᵀ * Y
  set O := Uᵀ * V
  have hT : Xᵀ * A * V = P * O := by
    calc Xᵀ * A * V = Xᵀ * (A * (U * Uᵀ)) * V := by rw [square_rsv_mul_transpose, Matrix.mul_one]
      _ = _ := by simp only [P, O, Y, Matrix.mul_assoc]
  have hOO : Oᵀ * O = 1 := by
    calc Oᵀ * O = Vᵀ * (U * Uᵀ) * V := by simp only [O, Matrix.transpose_mul,
          Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [square_rsv_mul_transpose, Matrix.mul_one, hV1]
  have hOOt : Oᵀᵀ * Oᵀ = 1 := by
    calc Oᵀᵀ * Oᵀ = Uᵀ * (V * Vᵀ) * U := by simp only [O, Matrix.transpose_mul,
          Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [hV2, Matrix.mul_one, square_rsv_transpose_mul]
  have hP : ∀ k j, P k j = ∑ i, X i k * Y i j := fun k j => by
    simp only [P, Matrix.mul_apply, Matrix.transpose_apply]
  refine ⟨fun k j => (P k j ^ 2 / lam j + O j k ^ 2) / 2, fun k j => ?_, fun k => ?_,
    fun j => ?_, fun k => ?_⟩
  · exact div_nonneg (add_nonneg (div_nonneg (sq_nonneg _) (hlam j)) (sq_nonneg _)) zero_le_two
  · -- row sums: Bessel's inequality for the columns of `Y`, and `Σ_j O_{jk}² = 1`
    have hb := square_bessel Y lam hY (fun i => X i k)
    have hO := square_sum_sq_col hOO k
    simp only [← hP] at hb
    rw [← Finset.sum_div, Finset.sum_add_distrib, hO]
    linarith [hX1 k]
  · -- column sums: Bessel's inequality for `X`, and `Σ_k O_{jk}² = 1`
    have hb := hX2 (fun i => Y i j)
    have hO := square_sum_sq_col hOOt j
    simp only [Matrix.transpose_apply] at hO
    have hPs : ∑ k, P k j ^ 2 = ∑ k, (∑ i, Y i j * X i k) ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hP]; congr 1; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hYj : ∑ i, Y i j ^ 2 = lam j := by
      have := hY j j
      simp only [ite_true] at this
      rw [← this]; exact Finset.sum_congr rfl fun i _ => sq _
    have hc : ∑ k, P k j ^ 2 / lam j ≤ 1 := by
      rw [← Finset.sum_div, hPs]
      calc (∑ k, (∑ i, Y i j * X i k) ^ 2) / lam j ≤ lam j / lam j :=
            div_le_div_of_nonneg_right (hYj ▸ hb) (hlam j)
        _ ≤ 1 := div_self_le_one _
    rw [← Finset.sum_div, Finset.sum_add_distrib, hO]
    linarith
  · rw [hT, Matrix.mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    beta_reduce
    have hs2 := hs2 j
    set s := sval A j
    have hs0 : 0 ≤ s := square_sval_nonneg A j
    rcases (hlam j).eq_or_lt with h0 | hpos
    · -- `λ_j = 0`: the column `Y_j` vanishes, so `P_{kj} = 0`
      have hYj : ∀ i, Y i j = 0 := by
        have := hY j j
        simp only [ite_true, ← h0] at this
        intro i
        have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (Y i j))).1 this
          i (Finset.mem_univ i)
        exact mul_self_eq_zero.1 h
      have : P k j = 0 := by rw [hP]; simp [hYj]
      rw [this, zero_mul, abs_zero]
      exact mul_nonneg (div_nonneg (add_nonneg (div_nonneg (sq_nonneg _) (hlam j))
        (sq_nonneg _)) zero_le_two) hs0
    · have hspos : 0 < s := by
        rcases hs0.eq_or_lt with h | h
        · rw [← h] at hs2; linarith [hs2]
        · exact h
      rw [← hs2, abs_mul]
      have key : ((P k j ^ 2 / s ^ 2 + O j k ^ 2) / 2) * s - |P k j| * |O j k| =
          (|P k j| - s * |O j k|) ^ 2 / (2 * s) := by
        rw [← sq_abs (P k j), ← sq_abs (O j k)]
        field_simp
        ring
      have : 0 ≤ (|P k j| - s * |O j k|) ^ 2 / (2 * s) := by positivity
      linarith

/-- `Σ_k |(XᵀAV)_{kk}|^q ≤ Σ_j s_j (A)^q` for `q ≥ 1`. -/
theorem square_sum_abs_diag_rpow_le (A : Matrix (Fin d) (Fin m) ℝ) {V : Matrix (Fin m) (Fin m) ℝ}
    (hV1 : Vᵀ * V = 1) (hV2 : V * Vᵀ = 1) {X : Matrix (Fin d) (Fin m) ℝ}
    (hX1 : ∀ k, ∑ i, X i k ^ 2 ≤ 1)
    (hX2 : ∀ w : Fin d → ℝ, ∑ k, (∑ i, w i * X i k) ^ 2 ≤ ∑ i, w i ^ 2) {q : ℝ} (hq : 1 ≤ q) :
    ∑ k, |(Xᵀ * A * V) k k| ^ q ≤ ∑ j, sval A j ^ q := by
  obtain ⟨M, hM0, hrow, hcol, hle⟩ := square_exists_substochastic A hV1 hV2 hX1 hX2
  calc ∑ k, |(Xᵀ * A * V) k k| ^ q ≤ ∑ k, (∑ j, M k j * sval A j) ^ q :=
        Finset.sum_le_sum fun k _ => Real.rpow_le_rpow (abs_nonneg _) (hle k) (by linarith)
    _ ≤ ∑ k, ∑ j, M k j * sval A j ^ q :=
        Finset.sum_le_sum fun k _ => square_rpow_sum_le _ (fun j _ => hM0 k j) (hrow k)
          (fun j _ => square_sval_nonneg A j) hq
    _ = ∑ j, (∑ k, M k j) * sval A j ^ q := by
        rw [Finset.sum_comm]; simp only [Finset.sum_mul]
    _ ≤ ∑ j, sval A j ^ q := Finset.sum_le_sum fun j _ =>
        mul_le_of_le_one_left (Real.rpow_nonneg (square_sval_nonneg A j) q) (hcol j)

/-- `|(XᵀAV)_{kk}| ≤ max_j s_j (A)`. -/
theorem square_abs_diag_le_iSup (A : Matrix (Fin d) (Fin m) ℝ) {V : Matrix (Fin m) (Fin m) ℝ}
    (hV1 : Vᵀ * V = 1) (hV2 : V * Vᵀ = 1) {X : Matrix (Fin d) (Fin m) ℝ}
    (hX1 : ∀ k, ∑ i, X i k ^ 2 ≤ 1)
    (hX2 : ∀ w : Fin d → ℝ, ∑ k, (∑ i, w i * X i k) ^ 2 ≤ ∑ i, w i ^ 2) (k : Fin m) :
    |(Xᵀ * A * V) k k| ≤ ⨆ j, sval A j := by
  obtain ⟨M, hM0, hrow, hcol, hle⟩ := square_exists_substochastic A hV1 hV2 hX1 hX2
  calc |(Xᵀ * A * V) k k| ≤ ∑ j, M k j * sval A j := hle k
    _ ≤ ∑ j, M k j * ⨆ j, sval A j := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (le_ciSup (Set.finite_range _).bddAbove j) (hM0 k j)
    _ = (∑ j, M k j) * ⨆ j, sval A j := by rw [Finset.sum_mul]
    _ ≤ ⨆ j, sval A j :=
        mul_le_of_le_one_left (Real.iSup_nonneg (square_sval_nonneg A)) (hrow k)

/-- The triangle inequality for `‖·‖_{S_q}`, `q ∈ [1, ∞]`. -/
theorem square_schattenNorm_add_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B := by
  set W := A + B with hWdef
  have hV1 : (square_rsv W)ᵀ * square_rsv W = 1 := square_rsv_transpose_mul W
  have hV2 : square_rsv W * (square_rsv W)ᵀ = 1 := square_rsv_mul_transpose W
  have hY := square_gram_rsv W
  have hs2 : ∀ k, sval W k ^ 2 = (Matrix.isHermitian_conjTranspose_mul_self W).eigenvalues k :=
    square_sval_sq W
  set V := square_rsv W
  set lam := (Matrix.isHermitian_conjTranspose_mul_self W).eigenvalues
  set Y := W * V
  have hYk : ∀ k, ∑ i, Y i k ^ 2 = lam k := fun k => by
    have := hY k k
    simp only [ite_true] at this
    rw [← this]; exact Finset.sum_congr rfl fun i _ => sq _
  set X : Matrix (Fin d) (Fin m) ℝ := Matrix.of fun i k => Y i k / sval W k with hX
  have hX1 : ∀ k, ∑ i, X i k ^ 2 ≤ 1 := fun k => by
    simp only [X, Matrix.of_apply, div_pow]
    rw [← Finset.sum_div, hYk, hs2]
    exact div_self_le_one _
  have hX2 : ∀ w : Fin d → ℝ, ∑ k, (∑ i, w i * X i k) ^ 2 ≤ ∑ i, w i ^ 2 := fun w => by
    have e : ∀ k, (∑ i, w i * X i k) ^ 2 = (∑ i, w i * Y i k) ^ 2 / lam k := fun k => by
      simp only [X, Matrix.of_apply, mul_div_assoc', ← Finset.sum_div, div_pow, hs2]
    simp_rw [e]
    exact square_bessel Y lam hY w
  have hdiag : ∀ k, sval W k = (Xᵀ * A * V) k k + (Xᵀ * B * V) k k := fun k => by
    rw [← Matrix.add_apply, ← Matrix.add_mul, ← Matrix.mul_add, ← hWdef, Matrix.mul_assoc,
      Matrix.mul_apply]
    simp only [Matrix.transpose_apply, X, Matrix.of_apply]
    have : ∑ i, Y i k / sval W k * Y i k = lam k / sval W k := by
      rw [← hYk, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, ← hs2]
    rcases eq_or_ne (sval W k) 0 with h | h
    · rw [h]; simp
    · field_simp
  unfold schattenNorm
  split_ifs with ht
  · rcases isEmpty_or_nonempty (Fin m) with hm | hm
    · simp only [Real.iSup_of_isEmpty, add_zero, le_refl]
    · refine ciSup_le fun k => ?_
      rw [hdiag k]
      have h1 := square_abs_diag_le_iSup A hV1 hV2 hX1 hX2 k
      have h2 := square_abs_diag_le_iSup B hV1 hV2 hX1 hX2 k
      linarith [le_abs_self ((Xᵀ * A * V) k k), le_abs_self ((Xᵀ * B * V) k k)]
  · have hr : 1 ≤ q.toReal := by
      have := ENNReal.toReal_mono ht hq
      rwa [ENNReal.toReal_one] at this
    have hr0 : 0 ≤ 1 / q.toReal := by positivity
    calc (∑ k, sval W k ^ q.toReal) ^ (1 / q.toReal) =
          (∑ k, |(Xᵀ * A * V) k k + (Xᵀ * B * V) k k| ^ q.toReal) ^ (1 / q.toReal) := by
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← hdiag k, abs_of_nonneg (square_sval_nonneg W k)]
      _ ≤ (∑ k, |(Xᵀ * A * V) k k| ^ q.toReal) ^ (1 / q.toReal) +
          (∑ k, |(Xᵀ * B * V) k k| ^ q.toReal) ^ (1 / q.toReal) := Real.Lp_add_le _ _ _ hr
      _ ≤ (∑ k, sval A k ^ q.toReal) ^ (1 / q.toReal) +
          (∑ k, sval B k ^ q.toReal) ^ (1 / q.toReal) :=
          add_le_add
            (Real.rpow_le_rpow (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (abs_nonneg _) _)
              (square_sum_abs_diag_rpow_le A hV1 hV2 hX1 hX2 hr) hr0)
            (Real.rpow_le_rpow (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (abs_nonneg _) _)
              (square_sum_abs_diag_rpow_le B hV1 hV2 hX1 hX2 hr) hr0)

end Cassese
