module

public import Morrey.Cassese.Square.Hermite
public import Morrey.Cassese.Rademacher
public import Morrey.Cassese.Hypotheses
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The rank-one geometry of Proposition 6.2

The pointwise square-function comparison in the proof of Proposition 6.2 (TeX lines 2353–2378)
rests on the shape of the symmetric and skew parts of a rank-one matrix. After rescaling,
`R = (u + w) ⊗ (u − w)` with `u ⊥ w` (`square_korn_rankOne_orth`), so that
`S = Sym R = u ⊗ u − w ⊗ w` and `K = Skew R = w ⊗ u − u ⊗ w`: the paper's
`S = α û ⊗ û − β ŵ ⊗ ŵ`, `K = √(αβ) (ŵ ⊗ û − û ⊗ ŵ)` with `α = |u|²`, `β = |w|²`. Then
`S Sᵀ = α u ⊗ u + β w ⊗ w`, `K Kᵀ = β u ⊗ u + α w ⊗ w`, and with the paper's
`S^# = (β² / α) u ⊗ u + (α² / β) w ⊗ w` (`β² û ⊗ û + α² ŵ ⊗ ŵ`),
`K Kᵀ ⪯ (t/2) S Sᵀ + (1/(2t)) S^#` for every `t > 0` and `tr S^# ≤ tr S Sᵀ` (equality unless
`u = 0` or `w = 0`) (`square_korn_loewner`).

Also: orthogonality of the increments of a Rademacher martingale of matrices in the Frobenius
norm (`square_korn_avg_frob_mart`), and Burkholder's square function inequality
(Theorem 2.3 (2), `burkholderSquareFunction_holds`) for such martingales in the Hilbert space
`S_2^{d×d}` (`square_korn_burkholder`), through the model `EuclideanSpace ℝ (Fin d × Fin d)` of
`S_2^{d×d}` (`square_korn_toE`, an isometry for the Frobenius norm) and the bridge of
`Morrey/Cassese/Rademacher.lean` from Rademacher martingales on the signs to
`MeasureTheory.Martingale` (`rad_martingale`, `rad_eLpNorm_uniform`).
-/

@[expose] public section

open scoped Matrix

namespace Cassese

variable {n : ℕ}

theorem square_korn_vecMulVec_mul (a b c e : Fin n → ℝ) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c e = (b ⬝ᵥ c) • Matrix.vecMulVec a e := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]

theorem square_korn_dot_self_nonneg (a : Fin n → ℝ) : 0 ≤ a ⬝ᵥ a :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

/-- After rescaling, a matrix of rank at most one is `(u + w) ⊗ (u − w)` with `u ⊥ w`. -/
theorem square_korn_rankOne_orth {R : Matrix (Fin n) (Fin n) ℝ} (hR : R.rank ≤ 1) :
    ∃ u w : Fin n → ℝ, u ⬝ᵥ w = 0 ∧ R = Matrix.vecMulVec (u + w) (u - w) := by
  obtain ⟨a, b, rfl⟩ := square_exists_vecMulVec hR
  by_cases h : a = 0 ∨ b = 0
  · refine ⟨0, 0, by simp, ?_⟩
    rcases h with rfl | rfl <;> simp
  push Not at h
  obtain ⟨ha, hb⟩ := h
  have hα : 0 < a ⬝ᵥ a := lt_of_le_of_ne (square_korn_dot_self_nonneg a)
    (Ne.symm (mt dotProduct_self_eq_zero.1 ha))
  have hβ : 0 < b ⬝ᵥ b := lt_of_le_of_ne (square_korn_dot_self_nonneg b)
    (Ne.symm (mt dotProduct_self_eq_zero.1 hb))
  set τ := √((b ⬝ᵥ b) / (a ⬝ᵥ a)) with hτ
  have hτ0 : 0 < τ := Real.sqrt_pos.2 (div_pos hβ hα)
  have hτ2 : τ ^ 2 = (b ⬝ᵥ b) / (a ⬝ᵥ a) := Real.sq_sqrt (div_pos hβ hα).le
  set t := √τ with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 hτ0
  have ht2 : t ^ 2 = τ := Real.sq_sqrt hτ0.le
  refine ⟨(1 / 2 : ℝ) • (t • a + t⁻¹ • b), (1 / 2 : ℝ) • (t • a - t⁻¹ • b), ?_, ?_⟩
  · simp only [dotProduct_smul, smul_dotProduct, add_dotProduct, dotProduct_sub, smul_eq_mul,
      dotProduct_comm b a]
    have : t ^ 2 * (a ⬝ᵥ a) = t⁻¹ ^ 2 * (b ⬝ᵥ b) := by
      rw [inv_pow, ht2, eq_inv_mul_iff_mul_eq₀ hτ0.ne', ← mul_assoc, ← sq, hτ2,
        div_mul_cancel₀ _ hα.ne']
    have ht' : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0.ne'
    linear_combination (1 / 4 : ℝ) * this
  · have e1 : (1 / 2 : ℝ) • (t • a + t⁻¹ • b) + (1 / 2 : ℝ) • (t • a - t⁻¹ • b) = t • a := by
      module
    have e2 : (1 / 2 : ℝ) • (t • a + t⁻¹ • b) - (1 / 2 : ℝ) • (t • a - t⁻¹ • b) = t⁻¹ • b := by
      module
    rw [e1, e2, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul,
      mul_inv_cancel₀ ht0.ne', one_smul]

/-- **The Loewner bound of the proof of Proposition 6.2** (TeX lines 2363–2373): for `u ⊥ w`,
`S = u ⊗ u − w ⊗ w`, `K = w ⊗ u − u ⊗ w`, the matrix `S^# = (β² / α) u ⊗ u + (α² / β) w ⊗ w`
(`α = |u|²`, `β = |w|²`) is positive semidefinite, `tr S^# ≤ tr S Sᵀ`, and
`K Kᵀ ⪯ (t/2) S Sᵀ + (1/(2t)) S^#` for every `t > 0`. -/
theorem square_korn_loewner {u w : Fin n → ℝ} (huw : u ⬝ᵥ w = 0) :
    ∃ T : Matrix (Fin n) (Fin n) ℝ, T.PosSemidef ∧
      T.trace ≤ ((Matrix.vecMulVec u u - Matrix.vecMulVec w w) *
        (Matrix.vecMulVec u u - Matrix.vecMulVec w w)ᵀ).trace ∧
      ∀ t : ℝ, 0 < t → ((t / 2) • ((Matrix.vecMulVec u u - Matrix.vecMulVec w w) *
        (Matrix.vecMulVec u u - Matrix.vecMulVec w w)ᵀ) + (1 / (2 * t)) • T -
        (Matrix.vecMulVec w u - Matrix.vecMulVec u w) *
          (Matrix.vecMulVec w u - Matrix.vecMulVec u w)ᵀ).PosSemidef := by
  set α := u ⬝ᵥ u with hαdef
  set β := w ⬝ᵥ w with hβdef
  have hα0 : 0 ≤ α := square_korn_dot_self_nonneg u
  have hβ0 : 0 ≤ β := square_korn_dot_self_nonneg w
  have hwu : w ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huw
  set Pu := Matrix.vecMulVec u u
  set Pw := Matrix.vecMulVec w w
  have hPu : Pu.PosSemidef := by
    simpa [star_trivial] using Matrix.posSemidef_vecMulVec_self_star u
  have hPw : Pw.PosSemidef := by
    simpa [star_trivial] using Matrix.posSemidef_vecMulVec_self_star w
  have hSS : (Pu - Pw) * (Pu - Pw)ᵀ = α • Pu + β • Pw := by
    simp only [Pu, Pw, Matrix.transpose_sub, Matrix.transpose_vecMulVec, Matrix.sub_mul,
      Matrix.mul_sub, square_korn_vecMulVec_mul, huw, hwu, zero_smul, sub_zero]
    rw [← hαdef, ← hβdef]
    abel
  have hKK : (Matrix.vecMulVec w u - Matrix.vecMulVec u w) *
      (Matrix.vecMulVec w u - Matrix.vecMulVec u w)ᵀ = β • Pu + α • Pw := by
    simp only [Pu, Pw, Matrix.transpose_sub, Matrix.transpose_vecMulVec, Matrix.sub_mul,
      Matrix.mul_sub, square_korn_vecMulVec_mul, huw, hwu, zero_smul, sub_zero, zero_sub]
    rw [← hαdef, ← hβdef]
    abel
  -- a term `c • (v ⊗ v)` is positive semidefinite if `c ≥ 0` or `v = 0`
  have hterm : ∀ (v : Fin n → ℝ) (c : ℝ), (v ⬝ᵥ v ≠ 0 → 0 ≤ c) →
      (c • Matrix.vecMulVec v v).PosSemidef := by
    intro v c hc
    by_cases hv : v ⬝ᵥ v = 0
    · rw [dotProduct_self_eq_zero.1 hv]; simpa using Matrix.PosSemidef.zero
    · exact (by simpa [star_trivial] using Matrix.posSemidef_vecMulVec_self_star v :
        (Matrix.vecMulVec v v).PosSemidef).smul (hc hv)
  refine ⟨(β ^ 2 / α) • Pu + (α ^ 2 / β) • Pw, ?_, ?_, fun t ht => ?_⟩
  · exact (hPu.smul (div_nonneg (sq_nonneg _) hα0)).add (hPw.smul (div_nonneg (sq_nonneg _) hβ0))
  · rw [hSS, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.trace_smul]
    simp only [Pu, Pw, Matrix.trace_vecMulVec, smul_eq_mul]
    rw [← hαdef, ← hβdef]
    have h1 : β ^ 2 / α * α ≤ β * β := by
      rcases hα0.eq_or_lt with h | h
      · rw [← h]; simp; nlinarith
      · rw [div_mul_cancel₀ _ h.ne', sq]
    have h2 : α ^ 2 / β * β ≤ α * α := by
      rcases hβ0.eq_or_lt with h | h
      · rw [← h]; simp; nlinarith
      · rw [div_mul_cancel₀ _ h.ne', sq]
    linarith
  · rw [hSS, hKK]
    have e : (t / 2) • (α • Pu + β • Pw) + (1 / (2 * t)) • ((β ^ 2 / α) • Pu + (α ^ 2 / β) • Pw) -
        (β • Pu + α • Pw) =
        (t / 2 * α + 1 / (2 * t) * (β ^ 2 / α) - β) • Pu +
          (t / 2 * β + 1 / (2 * t) * (α ^ 2 / β) - α) • Pw := by
      module
    rw [e]
    refine (hterm u _ fun h => ?_).add (hterm w _ fun h => ?_)
    · have hpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm h)
      have : t / 2 * α + 1 / (2 * t) * (β ^ 2 / α) - β = (t * α - β) ^ 2 / (2 * t * α) := by
        field_simp; ring
      rw [this]; positivity
    · have hpos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm h)
      have : t / 2 * β + 1 / (2 * t) * (α ^ 2 / β) - α = (t * β - α) ^ 2 / (2 * t * β) := by
        field_simp; ring
      rw [this]; positivity

/-- Orthogonality of the increments of a Rademacher martingale of matrices in the Frobenius norm:
`E ‖Σ_{k<N} ε_k ξ_k‖_F² = Σ_{k<N} E ‖ξ_k‖_F²` for predictable `ξ`. -/
theorem square_korn_avg_frob_mart {N : ℕ} (ξ : Fin N → (Fin N → Bool) → Matrix (Fin n) (Fin n) ℝ)
    (hξ : IsPredictable ξ) :
    avg (fun ε => squareFrob (mart ξ N ε) (mart ξ N ε)) =
      avg (fun ε => ∑ k, squareFrob (ξ k ε) (ξ k ε)) := by
  set G : ℕ → (Fin N → Bool) → ℝ := fun m ε =>
    ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < m), squareFrob (ξ k ε) (ξ k ε)
  have hξflip : ∀ (k j : Fin N), j ≤ k → ∀ ε, ξ j (rad_flip k ε) = ξ j ε := by
    intro k j hjk ε
    exact hξ j _ _ fun i hi => rad_flip_apply_ne (ne_of_lt (lt_of_lt_of_le hi hjk)) ε
  have hlt : ∀ m (hm : m < N) (j : Fin N), j ∈ Finset.univ.filter (fun k : Fin N => k.val < m) →
      j < ⟨m, hm⟩ := fun m hm j hj => Fin.lt_def.2 (Finset.mem_filter.1 hj).2
  have hMflip : ∀ m (hm : m < N) ε, mart ξ m (rad_flip ⟨m, hm⟩ ε) = mart ξ m ε := by
    intro m hm ε
    simp only [mart]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [rad_flip_apply_ne (ne_of_lt (hlt m hm j hj)), hξflip _ j (hlt m hm j hj).le ε]
  have hstep : ∀ m (hm : m < N),
      avg (fun ε => squareFrob (mart ξ (m + 1) ε) (mart ξ (m + 1) ε)) =
        avg (fun ε => squareFrob (mart ξ m ε) (mart ξ m ε)) +
          avg (fun ε => squareFrob (ξ ⟨m, hm⟩ ε) (ξ ⟨m, hm⟩ ε)) := by
    intro m hm
    have hM1 : ∀ ε, mart ξ (m + 1) ε = mart ξ m ε + coin (ε ⟨m, hm⟩) • ξ ⟨m, hm⟩ ε :=
      fun ε => square_sum_filter_succ hm _
    set F := fun ε => squareFrob (mart ξ (m + 1) ε) (mart ξ (m + 1) ε)
    have hpair : ∀ ε, F ε + F (rad_flip ⟨m, hm⟩ ε) =
        2 * (squareFrob (mart ξ m ε) (mart ξ m ε) + squareFrob (ξ ⟨m, hm⟩ ε) (ξ ⟨m, hm⟩ ε)) := by
      intro ε
      simp only [F]
      rw [hM1, hM1, hMflip m hm, hξflip _ _ le_rfl, square_coin_flip]
      have hc := square_coin_sq (ε ⟨m, hm⟩)
      simp only [squareFrob_add_left, squareFrob_add_right, squareFrob_smul_left,
        squareFrob_smul_right, squareFrob_comm (ξ ⟨m, hm⟩ ε) (mart ξ m ε)]
      linear_combination (2 * squareFrob (ξ ⟨m, hm⟩ ε) (ξ ⟨m, hm⟩ ε)) * hc
    calc avg F = avg (fun ε => (F ε + F (rad_flip ⟨m, hm⟩ ε)) / 2) := by
          simp only [div_eq_mul_inv, mul_comm _ (2 : ℝ)⁻¹]
          rw [rad_avg_mul_left, rad_avg_add, square_avg_flip ⟨m, hm⟩ F]; ring
      _ = _ := by
          simp_rw [hpair]
          rw [← rad_avg_add]
          congr 1; funext ε; ring
  have hind : ∀ m, m ≤ N → avg (fun ε => squareFrob (mart ξ m ε) (mart ξ m ε)) = avg (G m) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h1 : (fun ε => squareFrob (mart ξ 0 ε) (mart ξ 0 ε)) = fun _ => 0 := funext fun ε => by
        simp [mart, squareFrob]
      have h2 : G 0 = fun _ => 0 := funext fun ε => by simp [G]
      rw [h1, h2]
    | succ m ih =>
      intro hm
      have hm' : m < N := hm
      rw [hstep m hm', ih hm'.le]
      have : G (m + 1) = fun ε => G m ε + squareFrob (ξ ⟨m, hm'⟩ ε) (ξ ⟨m, hm'⟩ ε) :=
        funext fun ε => square_sum_filter_succ hm' _
      rw [this, rad_avg_add]
  rw [hind N le_rfl]
  simp only [G, square_filter_all]

/-- The Hilbert space `S_2^{d×d}`: a matrix as a vector of `ℝ^{d×d}` with the Euclidean norm
(`‖square_korn_toE M‖ = ‖M‖_F`). -/
noncomputable def square_korn_toE : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n) where
  toFun M := WithLp.toLp 2 (fun ij => M ij.1 ij.2)
  map_add' M M' := by rw [← WithLp.toLp_add]; rfl
  map_smul' c M := by rw [RingHom.id_apply, ← WithLp.toLp_smul]; rfl

theorem square_korn_norm_toE (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖square_korn_toE M‖ = √(squareFrob M M) := by
  rw [EuclideanSpace.norm_eq, squareFrob_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [square_korn_toE, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, Real.norm_eq_abs,
    sq, abs_mul_abs_self]

/-- **Burkholder's square function inequality in `S_2^{d×d}`** (Theorem 2.3 (2),
`burkholderSquareFunction_holds`, in the Hilbert space `S_2^{d×d}`), for a Rademacher martingale
of matrices `f_N = Σ_{k<N} ε_k ξ_k` with predictable `ξ`:
`‖(Σ_k ‖ξ_k‖_F²)^{1/2}‖_{L^p} ≤ (p* − 1) ‖f_N‖_{L^p (S_2)}`. -/
theorem square_korn_burkholder {p : ℝ} (hp : 1 < p) {N : ℕ}
    (ξ : Fin N → (Fin N → Bool) → Matrix (Fin n) (Fin n) ℝ) (hξ : IsPredictable ξ) :
    (avg fun ε => (∑ k, squareFrob (ξ k ε) (ξ k ε)) ^ (p / 2)) ^ (1 / p) ≤
      (pStar p - 1) * (avg fun ε => squareFrob (mart ξ N ε) (mart ξ N ε) ^ (p / 2)) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hβ : 0 ≤ pStar p - 1 := by
    have : p ≤ pStar p := le_max_left _ _
    linarith
  set L := square_korn_toE (n := n)
  set ζ : Fin N → (Fin N → Bool) → EuclideanSpace ℝ (Fin n × Fin n) := fun k ε => L (ξ k ε)
    with hζdef
  have hζ : IsPredictable ζ := fun k ε ε' h => by simp only [hζdef, hξ k ε ε' h]
  have hm : ∀ k ε, mart ζ k ε = L (mart ξ k ε) := by
    intro k ε; simp [hζdef, mart, map_sum, map_smul]
  obtain ⟨h1, -⟩ := burkholderSquareFunction_holds (Fin N → Bool) inferInstance
    (ProbabilityTheory.uniformOn Set.univ)
    (rad_filtration N) (EuclideanSpace ℝ (Fin n × Fin n)) (fun k => mart ζ k) p hp
    (rad_martingale ζ hζ) (rad_mart_zero ζ) N
  rw [rad_eLpNorm_uniform _ hp0, rad_eLpNorm_uniform _ hp0,
    ← ENNReal.ofReal_mul hβ] at h1
  have hsq : ∀ x : ℝ, 0 ≤ x → √x ^ p = x ^ (p / 2) := fun x hx => by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; congr 1; ring
  have hinc : ∀ ε, ∑ k ∈ Finset.range N, ‖mart ζ (k + 1) ε - mart ζ k ε‖ ^ 2 =
      ∑ k, squareFrob (ξ k ε) (ξ k ε) := by
    intro ε
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rad_mart_succ, add_sub_cancel_left]
    simp only [k.isLt, ↓reduceDIte]
    rw [norm_smul]
    have hc : ‖coin (ε k)‖ = 1 := by cases ε k <;> simp [coin]
    rw [hc, one_mul, hζdef]
    simp only [Fin.eta]
    rw [square_korn_norm_toE, Real.sq_sqrt (squareFrob_self_nonneg _)]
  have hl : ∀ ε, ‖√(∑ k ∈ Finset.range N, ‖mart ζ (k + 1) ε - mart ζ k ε‖ ^ 2)‖ ^ p =
      (∑ k, squareFrob (ξ k ε) (ξ k ε)) ^ (p / 2) := by
    intro ε
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), hinc,
      hsq _ (Finset.sum_nonneg fun k _ => squareFrob_self_nonneg _)]
  have hr : ∀ ε, ‖mart ζ N ε‖ ^ p = squareFrob (mart ξ N ε) (mart ξ N ε) ^ (p / 2) := by
    intro ε
    rw [hm, square_korn_norm_toE, hsq _ (squareFrob_self_nonneg _)]
  simp only [hl, hr] at h1
  have hb0 : 0 ≤ (avg fun ε => squareFrob (mart ξ N ε) (mart ξ N ε) ^ (p / 2)) ^ (1 / p) :=
    Real.rpow_nonneg (rad_avg_nonneg fun ε =>
      Real.rpow_nonneg (squareFrob_self_nonneg _) _) _
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hβ hb0)).1 h1

end Cassese
