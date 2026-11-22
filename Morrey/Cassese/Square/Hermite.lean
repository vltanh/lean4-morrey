module

public import Morrey.Cassese.Square.Trace
public import Morrey.Cassese.Square.Frobenius
public import Morrey.Cassese.Rademacher

/-!
# The Hermite supermartingale of Theorem 6.2

Tools for the proof of Theorem 6.2: averages over the signs (`avg`, with the elementary lemmas
`rad_avg_add`, … and the flip `rad_flip` of `Rademacher`), the invariance of `avg` under flipping
one sign (`square_avg_flip`), the Cauchy–Schwarz inequality for `avg`, and the
one-step inequality of the supermartingale
`Φ_n = tr H_n² − 6 tr (H_n Ṽ_n) + 3 tr Ṽ_n²` (`H_n = M_nᵀ M_n`): averaging over the sign of the
new increment, `Φ_n` decreases by at least `−(‖W_n‖² − 4 tr (H_{n−1} V_n) − 2 tr V_n²) ≥ 0`
(`square_phi_step`).
-/

@[expose] public section

open scoped Matrix

namespace Cassese

variable {n N : ℕ}

/-! ### Averages over the signs -/

theorem square_avg_const (c : ℝ) : avg (fun _ : Fin N → Bool => c) = c := by
  simp only [avg, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- `avg` is invariant under flipping one sign. -/
theorem square_avg_flip (k : Fin N) (f : (Fin N → Bool) → ℝ) :
    avg (fun ε => f (rad_flip k ε)) = avg f := by
  simp only [avg]
  congr 1
  exact Equiv.sum_comp ((rad_flip_involutive k).toPerm _) f

theorem square_coin_flip (k : Fin N) (ε : Fin N → Bool) :
    coin (rad_flip k ε k) = -coin (ε k) := by
  rw [rad_flip_apply_self]; cases ε k <;> simp [coin]

theorem square_coin_sq (b : Bool) : coin b ^ 2 = 1 := by cases b <;> simp [coin]

/-- Cauchy–Schwarz for `avg`: `E [√a √b] ≤ √(E a) √(E b)`. -/
theorem square_avg_sqrt_mul_le {a b : (Fin N → Bool) → ℝ} (ha : ∀ ε, 0 ≤ a ε)
    (hb : ∀ ε, 0 ≤ b ε) : avg (fun ε => √(a ε) * √(b ε)) ≤ √(avg a) * √(avg b) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun ε => √(a ε)) (fun ε => √(b ε))
  simp only [Real.sq_sqrt (ha _), Real.sq_sqrt (hb _)] at hcs
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  have hs0 : 0 ≤ ∑ ε, √(a ε) * √(b ε) := Finset.sum_nonneg fun ε _ => by positivity
  simp only [avg]
  rw [← Real.sqrt_mul (div_nonneg (Finset.sum_nonneg fun ε _ => ha ε) h2.le)]
  rw [div_mul_div_comm, Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ 2 ^ N * 2 ^ N),
    Real.sqrt_mul_self h2.le]
  exact div_le_div_of_nonneg_right ((Real.le_sqrt hs0 (mul_nonneg
    (Finset.sum_nonneg fun ε _ => ha ε) (Finset.sum_nonneg fun ε _ => hb ε))).2 hcs) h2.le

/-! ### Martingales of matrices -/

theorem square_filter_succ {N : ℕ} {m : ℕ} (hm : m < N) :
    (Finset.univ.filter fun k : Fin N => k.val < m + 1) =
      insert ⟨m, hm⟩ (Finset.univ.filter fun k : Fin N => k.val < m) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext h)
  · rintro (h | h)
    · rw [h]; exact Nat.lt_succ_self m
    · exact Nat.lt_succ_of_lt h

theorem square_sum_filter_succ {β : Type*} [AddCommMonoid β] {m : ℕ} (hm : m < N)
    (f : Fin N → β) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < m + 1), f k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < m), f k + f ⟨m, hm⟩ := by
  rw [square_filter_succ hm, Finset.sum_insert, add_comm]
  simp

theorem square_filter_all : (Finset.univ.filter fun k : Fin N => k.val < N) = Finset.univ := by
  ext k; simp

/-! ### The one-step inequality -/

/-- `Φ (M, Ṽ) = tr ((MᵀM)²) − 6 tr (MᵀM Ṽ) + 3 tr (Ṽ²)`. -/
noncomputable def squarePhi (M V : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  squareFrob (Mᵀ * M) (Mᵀ * M) - 6 * squareFrob (Mᵀ * M) V + 3 * squareFrob V V

set_option linter.unusedSimpArgs false in
/-- **The supermartingale step** (proof of Theorem 6.2): for normal `M`, `D`, symmetric `Ṽ` and
`c = ±1`, averaging `Φ` over the two signs of the new increment `± c D` gives at most
`Φ (M, Ṽ)`: the difference is `‖W‖² − 4 tr (HV) − 2 tr V² ≤ 0`, with `W = MᵀD + DᵀM`,
`H = MᵀM`, `V = DᵀD`, and `‖W‖ ≤ 2 ‖MᵀD‖ = 2 tr (HV)^{1/2}` by normality. -/
theorem square_phi_step {M D V : Matrix (Fin n) (Fin n) ℝ} (hM : M * Mᵀ = Mᵀ * M)
    (hD : D * Dᵀ = Dᵀ * D) {c : ℝ} (hc : c ^ 2 = 1) :
    squarePhi (M + c • D) (V + Dᵀ * D) + squarePhi (M + (-c) • D) (V + Dᵀ * D) ≤
      2 * squarePhi M V := by
  have hmul : ∀ (t : ℝ), (M + t • D)ᵀ * (M + t • D) =
      Mᵀ * M + t • (Mᵀ * D + Dᵀ * M) + (t ^ 2) • (Dᵀ * D) := by
    intro t
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
    module
  have hc' : (-c) ^ 2 = 1 := by rw [neg_sq, hc]
  -- `‖W‖² ≤ 4 ⟨H, V_D⟩`
  have hW : squareFrob (Mᵀ * D + Dᵀ * M) (Mᵀ * D + Dᵀ * M) ≤
      4 * squareFrob (Mᵀ * M) (Dᵀ * D) := by
    have h := squareFrob_add_self_le (Mᵀ * D) (Dᵀ * M)
    have r : squareFrob (Mᵀ * M) (Dᵀ * D) = ((Mᵀ * M) * (Dᵀ * D)).trace := by
      simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_transpose]
    have e1 : squareFrob (Mᵀ * D) (Mᵀ * D) = squareFrob (Mᵀ * M) (Dᵀ * D) := by
      have l : squareFrob (Mᵀ * D) (Mᵀ * D) = (Dᵀ * (M * (Mᵀ * D))).trace := by
        simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [l, r, square_tr_cyc, ← Matrix.mul_assoc M Mᵀ, hM, hD]
    have e2 : squareFrob (Dᵀ * M) (Dᵀ * M) = squareFrob (Mᵀ * M) (Dᵀ * D) := by
      have l : squareFrob (Dᵀ * M) (Dᵀ * M) = (Mᵀ * ((D * Dᵀ) * M)).trace := by
        simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [l, r, hD, Matrix.trace_mul_comm, Matrix.mul_assoc, hM, Matrix.trace_mul_comm]
    rw [e1, e2] at h
    linarith
  have hVV := squareFrob_self_nonneg (Dᵀ * D)
  have hcc : ∀ x : ℝ, c * (c * x) = x := fun x => by rw [← mul_assoc, ← sq, hc, one_mul]
  have hcc' : ∀ x : ℝ, -c * (-c * x) = x := fun x => by rw [← mul_assoc, ← sq, hc', one_mul]
  simp only [squarePhi, hmul, hc, hc', one_smul]
  simp only [squareFrob_add_left, squareFrob_add_right, squareFrob_smul_left,
    squareFrob_smul_right, mul_add, hcc, hcc', squareFrob_comm (Dᵀ * M) (Mᵀ * D),
    squareFrob_comm (Dᵀ * D) (Mᵀ * M), squareFrob_comm (Mᵀ * D) (Mᵀ * M),
    squareFrob_comm (Dᵀ * M) (Mᵀ * M), squareFrob_comm (Dᵀ * D) (Mᵀ * D),
    squareFrob_comm (Dᵀ * D) (Dᵀ * M), squareFrob_comm V (Mᵀ * M), squareFrob_comm V (Mᵀ * D),
    squareFrob_comm V (Dᵀ * M), squareFrob_comm V (Dᵀ * D)] at hW ⊢
  linarith

end Cassese
