module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Module
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The Frobenius inner product and rank-one matrices

Tools for the proof of Corollary 6.4: the Frobenius (Hilbert–Schmidt) inner product
`⟨P, Q⟩ = tr (PᵀQ)` on `ℝ^{n×n}`, whose norm is `‖·‖_{S_2}`, with the Cauchy–Schwarz inequality
(`squareFrob_sq_le`) and the expansion of `⟨P(t), P(t)⟩` for a quadratic matrix polynomial
`P(t) = P₀ + t P₁ + t² P₂` (`squareFrob_quad`); and the factorization of a matrix of rank at most
one as `u ⊗ v` (`square_exists_vecMulVec`).
-/

@[expose] public section

open scoped Matrix

namespace Cassese

variable {n : ℕ}

/-- The Frobenius inner product `⟨P, Q⟩ = tr (PᵀQ) = Σ_{ij} P_{ij} Q_{ij}`. -/
noncomputable def squareFrob (P Q : Matrix (Fin n) (Fin n) ℝ) : ℝ := (Pᵀ * Q).trace

theorem squareFrob_eq_sum (P Q : Matrix (Fin n) (Fin n) ℝ) :
    squareFrob P Q = ∑ x : Fin n × Fin n, P x.1 x.2 * Q x.1 x.2 := by
  rw [squareFrob, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem squareFrob_comm (P Q : Matrix (Fin n) (Fin n) ℝ) : squareFrob P Q = squareFrob Q P := by
  simp only [squareFrob_eq_sum, mul_comm]

theorem squareFrob_self_nonneg (P : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ squareFrob P P := by
  rw [squareFrob_eq_sum]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem squareFrob_add_left (P Q R : Matrix (Fin n) (Fin n) ℝ) :
    squareFrob (P + Q) R = squareFrob P R + squareFrob Q R := by
  simp only [squareFrob, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add]

theorem squareFrob_add_right (P Q R : Matrix (Fin n) (Fin n) ℝ) :
    squareFrob P (Q + R) = squareFrob P Q + squareFrob P R := by
  simp only [squareFrob, Matrix.mul_add, Matrix.trace_add]

theorem squareFrob_smul_left (c : ℝ) (P Q : Matrix (Fin n) (Fin n) ℝ) :
    squareFrob (c • P) Q = c * squareFrob P Q := by
  simp only [squareFrob, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

theorem squareFrob_smul_right (c : ℝ) (P Q : Matrix (Fin n) (Fin n) ℝ) :
    squareFrob P (c • Q) = c * squareFrob P Q := by
  simp only [squareFrob, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem squareFrob_neg_left (P Q : Matrix (Fin n) (Fin n) ℝ) :
    squareFrob (-P) Q = -squareFrob P Q := by
  simp only [squareFrob, Matrix.transpose_neg, Matrix.neg_mul, Matrix.trace_neg]

theorem squareFrob_neg_right (P Q : Matrix (Fin n) (Fin n) ℝ) :
    squareFrob P (-Q) = -squareFrob P Q := by
  simp only [squareFrob, Matrix.mul_neg, Matrix.trace_neg]

/-- **Cauchy–Schwarz** for the Frobenius inner product. -/
theorem squareFrob_sq_le (P Q : Matrix (Fin n) (Fin n) ℝ) :
    squareFrob P Q ^ 2 ≤ squareFrob P P * squareFrob Q Q := by
  simp only [squareFrob_eq_sum, ← sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- Cauchy–Schwarz with norms: `⟨P, Q⟩ ≤ ‖P‖ ‖Q‖`. -/
theorem squareFrob_le_sqrt (P Q : Matrix (Fin n) (Fin n) ℝ) :
    |squareFrob P Q| ≤ √(squareFrob P P) * √(squareFrob Q Q) := by
  rw [← Real.sqrt_mul (squareFrob_self_nonneg P), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (squareFrob_sq_le P Q)

/-- `2 ⟨P, Q⟩ ≤ ‖P‖² + ‖Q‖²`. -/
theorem squareFrob_two_mul_le (P Q : Matrix (Fin n) (Fin n) ℝ) :
    2 * squareFrob P Q ≤ squareFrob P P + squareFrob Q Q := by
  have h := squareFrob_self_nonneg (P - Q)
  simp only [sub_eq_add_neg, squareFrob_add_left, squareFrob_add_right, squareFrob_neg_left,
    squareFrob_neg_right, squareFrob_comm Q P] at h
  linarith

/-- `‖P + Q‖² ≤ 2 ‖P‖² + 2 ‖Q‖²`. -/
theorem squareFrob_add_self_le (P Q : Matrix (Fin n) (Fin n) ℝ) :
    squareFrob (P + Q) (P + Q) ≤ 2 * squareFrob P P + 2 * squareFrob Q Q := by
  have h := squareFrob_two_mul_le P Q
  simp only [squareFrob_add_left, squareFrob_add_right, squareFrob_comm Q P]
  linarith

/-- The expansion of `‖P₀ + t P₁ + t² P₂‖²`. -/
theorem squareFrob_quad (P₀ P₁ P₂ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    squareFrob (P₀ + t • P₁ + (t ^ 2) • P₂) (P₀ + t • P₁ + (t ^ 2) • P₂) =
      squareFrob P₀ P₀ + 2 * squareFrob P₀ P₁ * t +
        (squareFrob P₁ P₁ + 2 * squareFrob P₀ P₂) * t ^ 2 + 2 * squareFrob P₁ P₂ * t ^ 3 +
        squareFrob P₂ P₂ * t ^ 4 := by
  simp only [squareFrob_add_left, squareFrob_add_right, squareFrob_smul_left,
    squareFrob_smul_right, squareFrob_comm P₁ P₀, squareFrob_comm P₂ P₀, squareFrob_comm P₂ P₁]
  ring

/-- A matrix of rank at most one is `u ⊗ v`. -/
theorem square_exists_vecMulVec {R : Matrix (Fin n) (Fin n) ℝ} (h : R.rank ≤ 1) :
    ∃ u v : Fin n → ℝ, R = Matrix.vecMulVec u v := by
  rw [Matrix.rank_eq_finrank_span_cols] at h
  obtain ⟨w, hw⟩ := finrank_le_one_iff.1 h
  choose c hc using fun j => hw ⟨R.col j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨(w : Fin n → ℝ), c, ?_⟩
  ext i j
  have := congrArg (fun z : Submodule.span ℝ (Set.range R.col) => (z : Fin n → ℝ) i) (hc j)
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.vecMulVec_apply, mul_comm, this]
  rfl

/-! ### Trace identities for four factors -/

/-- Cyclicity of the trace of four factors (right-associated). -/
theorem square_tr_cyc (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    (A * (B * (C * D))).trace = (B * (C * (D * A))).trace := by
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]

/-- The trace of four factors is the trace of the transposed product. -/
theorem square_tr_rev (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    (A * (B * (C * D))).trace = (Dᵀ * (Cᵀ * (Bᵀ * Aᵀ))).trace := by
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The arithmetic of the proof of Corollary 6.4: from `‖W‖ ≤ 2a`, `ρ ≤ 2e`, `a ≤ b`, `c ≤ e`
and the Cauchy–Schwarz bounds, `φ''(0) / 2 ≤ 0` (the paper's quadratic-form chain). -/
theorem square_zigzag_arith {a b c e w ρ p1 p2 pW : ℝ} (pa : 0 ≤ a) (pw : 0 ≤ w) (pρ : 0 ≤ ρ) (f6 : w ^ 2 ≤ 4 * a ^ 2) (f7 : ρ ^ 2 ≤ 4 * e ^ 2)
    (fab : a ^ 2 ≤ b ^ 2) (fce : c ^ 2 ≤ e ^ 2) (cs1 : |p1| ≤ b * c) (cs2 : |p2| ≤ e * a)
    (cs3 : |pW| ≤ w * ρ) (hf5 : pW = 2 * p1 - 2 * p2) :
    w ^ 2 + 2 * a ^ 2 - 15 / 2 * (b ^ 2 + 2 * p1 + c ^ 2 + 2 * -p2) -
      95 / 4 * (ρ ^ 2 + 2 * e ^ 2) ≤ 0 := by
  have hwa : w ≤ 2 * a := by
    have := (pow_le_pow_iff_left₀ pw (by positivity : (0:ℝ) ≤ 2 * a) two_ne_zero).1
      (by nlinarith)
    exact this
  -- the paper's `⟨W, Z⟩ = 2 p₂ − 2 p₁` satisfies `⟨W, Z⟩ ≤ 2ae + 2bc` and `⟨W, Z⟩ ≤ 2aρ`
  have hPi1 : 2 * p2 - 2 * p1 ≤ 2 * (e * a) + 2 * (b * c) := by
    have := le_abs_self p2; have := neg_abs_le p1; linarith
  have hPi2 : 2 * p2 - 2 * p1 ≤ 2 * a * ρ := by
    have h := neg_abs_le pW
    have : w * ρ ≤ 2 * a * ρ := mul_le_mul_of_nonneg_right hwa pρ
    linarith
  -- `φ''(0) = 2 × (the coefficient)`, and the paper's chain of inequalities
  have h1 : 2 * (w ^ 2 + 2 * a ^ 2 - 15 / 2 * (b ^ 2 + 2 * p1 + c ^ 2 + 2 * -p2) -
      95 / 4 * (ρ ^ 2 + 2 * e ^ 2)) ≤ 12 * a ^ 2 - 15 * b ^ 2 - 15 * c ^ 2 + 20 * a * ρ +
      10 * a * e + 10 * b * c - 95 / 2 * ρ ^ 2 - 95 * e ^ 2 := by
    nlinarith
  have h2 : 12 * a ^ 2 - 15 * b ^ 2 - 15 * c ^ 2 + 20 * a * ρ + 10 * a * e + 10 * b * c -
      95 / 2 * ρ ^ 2 - 95 * e ^ 2 ≤
      29 / 2 * (a ^ 2 - b ^ 2) + 35 * (c ^ 2 - e ^ 2) + 5 / 2 * (ρ ^ 2 - 4 * e ^ 2) := by
    nlinarith [sq_nonneg (b - 10 * c), sq_nonneg (ρ - a / 5), sq_nonneg (e - a / 10)]
  have h3 : 29 / 2 * (a ^ 2 - b ^ 2) + 35 * (c ^ 2 - e ^ 2) + 5 / 2 * (ρ ^ 2 - 4 * e ^ 2) ≤ 0 := by
    nlinarith
  linarith

/-- **Zig-zag concavity of `U`** (proof of Corollary 6.4, TeX lines 2668–2690): for `X, D`
symmetric and `Y, E` skew-symmetric with `EEᵀ ⪯ D²`, the second-order coefficient of `t ↦ U (X + t D, Y + t E)`, `U (X, Y) = ‖Y‖_{S_4}⁴ − (15/2) ‖YX‖_{S_2}² −
(95/4) ‖X‖_{S_4}⁴`, is `≤ 0`. In the paper's notation this coefficient is `φ''(0) / 2` with
`φ''(0) = 2‖W‖² + 4a² − 15b² − 15c² + 15⟨W, Z⟩ − (95/2)ρ² − 95e²` (`W = YE + EY`,
`Z = XD + DX`, `a = ‖YE‖`, `b = ‖YD‖`, `c = ‖EX‖`, `e = ‖XD‖`, `ρ = ‖Z‖`, all `S_2` norms), and
the paper's bounds are `a ≤ b`, `c ≤ e` (TeX lines 2672–2673: from `EEᵀ ⪯ D²`,
`a² = tr (YᵀY EEᵀ) ≤ tr (YᵀY D²) = b²` and `c² = tr (EEᵀ XXᵀ) ≤ tr (D² XXᵀ) = e²`, the traces of
products of positive semidefinite matrices being `≥ 0`), `⟨W, Z⟩ ≤ (2ae + 2bc)/3 + (2/3)(2aρ)`
(inventory E7: `⟨W, Z⟩ = 2 tr (YEXD) + 2 tr (YEDX) ≤ 2bc + 2ae` and `⟨W, Z⟩ ≤ ‖W‖ ρ ≤ 2aρ`),
and the quadratic-form chain
`φ''(0) ≤ 12a² − 15b² − 15c² + 20aρ + 10ae + 10bc − (95/2)ρ² − 95e²
  ≤ (29/2)(a² − b²) + 35(c² − e²) + (5/2)(ρ² − 4e²) ≤ 0`. The paper applies it to
`D = Sym_{1/2} R`, `E = Skew R` with `R` of rank one, where `D² − EEᵀ = D² + E² = ¼ tr (R)² Id`
(`square_rankOne_sq`, `square_zz_nonpos`). -/
theorem square_zigzag {X Y D E : Matrix (Fin n) (Fin n) ℝ} (hX : Xᵀ = X) (hY : Yᵀ = -Y)
    (hD : Dᵀ = D) (hE : Eᵀ = -E) (hDE : (D * D - E * Eᵀ).PosSemidef) :
    (squareFrob (Yᵀ * E + Eᵀ * Y) (Yᵀ * E + Eᵀ * Y) + 2 * squareFrob (Yᵀ * Y) (Eᵀ * E)) -
      15 / 2 * (squareFrob (Y * D + E * X) (Y * D + E * X) + 2 * squareFrob (Y * X) (E * D)) -
      95 / 4 * (squareFrob (Xᵀ * D + Dᵀ * X) (Xᵀ * D + Dᵀ * X) +
        2 * squareFrob (Xᵀ * X) (Dᵀ * D)) ≤ 0 := by
  -- the basic quantities `a² = ‖YE‖²`, `b² = ‖YD‖²`, `c² = ‖EX‖²`, `e² = ‖XD‖²`
  set a2 := squareFrob (Y * E) (Y * E) with ha2
  set b2 := squareFrob (Y * D) (Y * D) with hb2
  set c2 := squareFrob (E * X) (E * X) with hc2
  set e2 := squareFrob (X * D) (X * D) with he2
  set w2 := squareFrob (Yᵀ * E + Eᵀ * Y) (Yᵀ * E + Eᵀ * Y) with hw2
  set r2 := squareFrob (Xᵀ * D + Dᵀ * X) (Xᵀ * D + Dᵀ * X) with hr2
  set p1 := squareFrob (Y * D) (E * X) with hp1
  set p2 := squareFrob (X * D) (Y * E) with hp2
  set pW := squareFrob (Yᵀ * E + Eᵀ * Y) (Xᵀ * D + Dᵀ * X) with hpW
  have tY : ∀ M : Matrix (Fin n) (Fin n) ℝ, squareFrob (Y * M) =
      fun N => -((M)ᵀ * (Y * N)).trace := by
    intro M; funext N
    simp only [squareFrob, Matrix.transpose_mul, hY, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.trace_neg, Matrix.mul_assoc]
  -- normal forms of the quantities, as traces of four factors
  have na2 : a2 = (E * (Y * (Y * E))).trace := by simp only [ha2, squareFrob, Matrix.transpose_mul, hY, hE, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have nb2 : b2 = -(D * (Y * (Y * D))).trace := by simp only [hb2, squareFrob, Matrix.transpose_mul, hY, hD, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_assoc]
  have nc2 : c2 = -(X * (E * (E * X))).trace := by simp only [hc2, squareFrob, Matrix.transpose_mul, hX, hE, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_assoc]
  have ne2 : e2 = (D * (X * (X * D))).trace := by simp only [he2, squareFrob, Matrix.transpose_mul, hX, hD, Matrix.mul_assoc]
  -- (f1), (f2)
  have f1 : squareFrob (Yᵀ * Y) (Eᵀ * E) = a2 := by
    rw [na2, square_tr_cyc]; simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_neg, hY, hE, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have f2 : squareFrob (Xᵀ * X) (Dᵀ * D) = e2 := by
    rw [ne2, square_tr_cyc]; simp only [squareFrob, Matrix.transpose_mul, hX, hD, Matrix.mul_assoc]
  -- (f4): `⟨YX, ED⟩ = −⟨XD, YE⟩`
  have q2 : squareFrob (Y * X) (E * D) = -(X * (Y * (E * D))).trace := by simp only [squareFrob, Matrix.transpose_mul, hX, hY, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_assoc]
  have f4 : squareFrob (Y * X) (E * D) = -p2 := by
    have h2 : p2 = (D * (X * (Y * E))).trace := by simp only [hp2, squareFrob, Matrix.transpose_mul, hX, hD, Matrix.mul_assoc]
    rw [q2, h2, square_tr_cyc D]
  -- (f5): `⟨Yᵀ E + Eᵀ Y, Xᵀ D + Dᵀ X⟩ = 2 ⟨YD, EX⟩ + 2 ⟨YX, ED⟩`
  have f5 : pW = 2 * p1 + 2 * squareFrob (Y * X) (E * D) := by
    have t1 : squareFrob (Yᵀ * E) (Xᵀ * D) = -(E * (Y * (X * D))).trace := by simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_neg, hX, hY, hE, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.trace_neg, Matrix.mul_assoc]
    have t2 : squareFrob (Yᵀ * E) (Dᵀ * X) = -(E * (Y * (D * X))).trace := by simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_neg, hY, hD, hE, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.trace_neg, Matrix.mul_assoc]
    have t3 : squareFrob (Eᵀ * Y) (Xᵀ * D) = -(Y * (E * (X * D))).trace := by simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_neg, hX, hY, hE, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.trace_neg, Matrix.mul_assoc]
    have t4 : squareFrob (Eᵀ * Y) (Dᵀ * X) = -(Y * (E * (D * X))).trace := by simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_neg, hY, hD, hE, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.trace_neg, Matrix.mul_assoc]
    have q1 : p1 = -(D * (Y * (E * X))).trace := by simp only [hp1, squareFrob, Matrix.transpose_mul, hY, hD, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_assoc]
    -- `τ(YEXD) = τ(DYEX)`, `τ(YEDX) = τ(XYED)`, `τ(EYXD) = τ(XYED)`, `τ(EYDX) = τ(DYEX)`
    have c3 : (Y * (E * (X * D))).trace = (D * (Y * (E * X))).trace := by
      rw [square_tr_cyc D]
    have c4 : (Y * (E * (D * X))).trace = (X * (Y * (E * D))).trace := by
      rw [square_tr_cyc X]
    have c1 : (E * (Y * (X * D))).trace = (X * (Y * (E * D))).trace := by
      rw [square_tr_rev, hD, hX, hY, hE, ← square_tr_cyc D]
      simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    have c2' : (E * (Y * (D * X))).trace = (D * (Y * (E * X))).trace := by
      rw [square_tr_rev, hD, hX, hY, hE, ← square_tr_cyc X]
      simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [hpW]
    simp only [squareFrob_add_left, squareFrob_add_right]
    rw [t1, t2, t3, t4, q1, q2, c1, c2', c3, c4]
    ring
  -- (f6), (f7): `‖W‖² ≤ 4a²`, `ρ² ≤ 4e²`
  have f6 : w2 ≤ 4 * a2 := by
    have h := squareFrob_add_self_le (Yᵀ * E) (Eᵀ * Y)
    have e1 : squareFrob (Yᵀ * E) (Yᵀ * E) = a2 := by rw [na2]; simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_neg, hY, hE, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    have e2' : squareFrob (Eᵀ * Y) (Eᵀ * Y) = a2 := by
      rw [na2, square_tr_cyc, square_tr_cyc]; (try simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_neg, hY, hE, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc])
    rw [e1, e2'] at h
    linarith
  have f7 : r2 ≤ 4 * e2 := by
    have h := squareFrob_add_self_le (Xᵀ * D) (Dᵀ * X)
    have e1 : squareFrob (Xᵀ * D) (Xᵀ * D) = e2 := by rw [ne2]; simp only [squareFrob, Matrix.transpose_mul, hX, hD, Matrix.mul_assoc]
    have e2' : squareFrob (Dᵀ * X) (Dᵀ * X) = e2 := by
      rw [ne2]; simp only [squareFrob, Matrix.transpose_mul, hX, hD, Matrix.mul_assoc]; rw [square_tr_cyc, square_tr_cyc]
    rw [e1, e2'] at h
    linarith
  -- `EEᵀ ⪯ D²`: `b² − a² = tr (Y (D² − EEᵀ) Yᵀ) ≥ 0`, `e² − c² = tr (Xᵀ (D² − EEᵀ) X) ≥ 0`
  have hct : ∀ M : Matrix (Fin n) (Fin n) ℝ, Mᴴ = Mᵀ := fun M => by
    ext i j; simp [Matrix.conjTranspose_apply]
  have fab : a2 ≤ b2 := by
    have h := (hDE.mul_mul_conjTranspose_same Y).trace_nonneg
    rw [hct] at h
    have e1 : (Y * (D * D - E * Eᵀ) * Yᵀ).trace = b2 - a2 := by
      rw [hb2, ha2]
      simp only [squareFrob, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub,
        Matrix.transpose_mul, hD, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm Y, Matrix.trace_mul_comm Y, Matrix.mul_assoc, Matrix.mul_assoc,
        Matrix.mul_assoc, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm D, Matrix.trace_mul_comm E]
      simp only [Matrix.mul_assoc]
    linarith
  have fce : c2 ≤ e2 := by
    have h := (hDE.conjTranspose_mul_mul_same X).trace_nonneg
    rw [hct] at h
    have e1 : (Xᵀ * (D * D - E * Eᵀ) * X).trace = e2 - c2 := by
      have c1 : (D * (X * (X * D))).trace = (D * (D * (X * X))).trace := by
        rw [square_tr_cyc, square_tr_cyc, square_tr_cyc]
      have c2' : (X * (E * (E * X))).trace = (E * (E * (X * X))).trace := square_tr_cyc _ _ _ _
      rw [he2, hc2]
      simp only [squareFrob, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub,
        Matrix.transpose_mul, hD, hX, hE, Matrix.neg_mul, Matrix.mul_neg, Matrix.trace_neg,
        Matrix.mul_assoc]
      rw [c1, c2', square_tr_cyc X]
    linarith
  -- Cauchy–Schwarz
  have ha0 := squareFrob_self_nonneg (Y * E)
  have hb0 := squareFrob_self_nonneg (Y * D)
  have hc0 := squareFrob_self_nonneg (E * X)
  have he0 := squareFrob_self_nonneg (X * D)
  have hw0 := squareFrob_self_nonneg (Yᵀ * E + Eᵀ * Y)
  have hr0 := squareFrob_self_nonneg (Xᵀ * D + Dᵀ * X)
  set a := √a2 with ha
  set b := √b2 with hb
  set c := √c2 with hc
  set e := √e2 with he
  set w := √w2 with hw
  set ρ := √r2 with hρ
  have sa : a ^ 2 = a2 := Real.sq_sqrt ha0
  have sb : b ^ 2 = b2 := Real.sq_sqrt hb0
  have sc : c ^ 2 = c2 := Real.sq_sqrt hc0
  have se : e ^ 2 = e2 := Real.sq_sqrt he0
  have sw : w ^ 2 = w2 := Real.sq_sqrt hw0
  have sρ : ρ ^ 2 = r2 := Real.sq_sqrt hr0
  have pa : 0 ≤ a := Real.sqrt_nonneg _
  have pb : 0 ≤ b := Real.sqrt_nonneg _
  have pc : 0 ≤ c := Real.sqrt_nonneg _
  have pe : 0 ≤ e := Real.sqrt_nonneg _
  have pw : 0 ≤ w := Real.sqrt_nonneg _
  have pρ : 0 ≤ ρ := Real.sqrt_nonneg _
  have cs1 : |p1| ≤ b * c := squareFrob_le_sqrt (Y * D) (E * X)
  have cs2 : |p2| ≤ e * a := squareFrob_le_sqrt (X * D) (Y * E)
  have cs3 : |pW| ≤ w * ρ := squareFrob_le_sqrt _ _
  have hf5 : pW = 2 * p1 - 2 * p2 := by rw [f5, f4]; ring
  have hH : squareFrob (Y * D + E * X) (Y * D + E * X) = b2 + 2 * p1 + c2 := by
    simp only [squareFrob_add_left, squareFrob_add_right, squareFrob_comm (E * X) (Y * D)]
    ring
  rw [f1, f2, f4, hH]
  rw [← sw] at f6
  rw [← sρ] at f7
  rw [← sa] at f6 fab
  rw [← sb] at fab
  rw [← sc] at fce
  rw [← se] at fce f7
  rw [← sw, ← sρ, ← sa, ← sb, ← sc, ← se]
  clear_value a b c e w ρ p1 p2 pW a2 b2 c2 e2 w2 r2
  exact square_zigzag_arith pa pw pρ f6 f7 fab fce cs1 cs2 cs3 hf5

end Cassese
