module

public import Morrey.Cassese.Toolkit
public import Morrey.Cassese.Bridges
public import Morrey.Cassese.Square.Trace
public import Morrey.Cassese.Square.Moments
public import Morrey.Cassese.Square.Witness
public import Morrey.Cassese.Square.Frobenius
public import Morrey.Cassese.Square.Schatten
public import Morrey.Cassese.Square.Hermite
public import Morrey.Cassese.Square.Weyl
public import Morrey.Cassese.Square.Triangle
public import Morrey.Cassese.Square.Hessian
public import Morrey.Cassese.Square.Korn
public import Morrey.Cassese.Square.Torus
public import Morrey.Cassese.Square.TorusTwo
public import Morrey.Cassese.Square.Envelope
public import Morrey.Cassese.Square.Sharpness
public import Mathlib.Basic.Real.Pointwise
public import Morrey.Sverak.Lemma2
public import Morrey.Sverak.Lemma1
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Section 6: the square case `ℝ^{d×d}`

* `symPart A = (A + Aᵀ)/2`, `skewPart A = (A − Aᵀ)/2`, `symHalfPart A = Sym A − ½ tr (A) Id`
  (`Sym_{1/2}`, Section 6.3);
* `kornF d p q C (A) = C^p ‖Sym A‖_{S_q}^p − ‖Skew A‖_{S_q}^p`, the integrand (30), with thresholds
  `C^{rc} (S_q^{d×d}, p) = rcThreshold (kornF d p q)` and
  `C^{qc} (S_q^{d×d}, p) = qcThreshold (kornF d p q)`;
* `hF d p q C (A) = C^p ‖Sym_{1/2} A‖_{S_q}^p − ‖Skew A‖_{S_q}^p` (Section 6.3), with
  `C^{rc} (d) = rcThreshold (hF d 4 4)` and `C^{qc} (d) = qcThreshold (hF d 4 4)` (Section 6.3);
* `gSquare d` and the function `U` of Corollary 6.4.

The proofs use the submodules `Square.Trace` (`‖·‖_{S_2}²`, `‖·‖_{S_4}⁴` as traces),
`Square.Schatten` (spectral tools and finite `ℓ^p` inequalities), `Square.Weyl` (Weyl's
monotonicity theorem), `Square.Frobenius` (the Frobenius inner product, rank-one matrices, the
zig-zag concavity of `U`), `Square.Hermite` (averages over signs, the supermartingale of
Theorem 6.2), `Square.Witness` (the trigonometric witness), `Square.Moments` (its moments),
`Square.Triangle` (the triangle inequality for `‖·‖_{S_q}`), `Square.Torus` (the singular values
of `a ⊗ b − b ⊗ a`, diagonal Schatten norms, the moments `E |Z|^{2m} ≤ m! d^m` and `L^p` monotonicity
on the cube, for Proposition 6.1), `Square.Korn` (the rank-one geometry and the Burkholder bridge
of Propositions 6.2 and 6.5), `Square.Hessian` (periodic test maps for Hessian quasiconvexity),
`Square.Envelope` (the rank-one convex envelope as an integrand, and the scaling argument "not
Hessian quasiconvex at `0` ⇒ nowhere"), `Square.TorusTwo` (the witness of Corollary 6.1 on
`𝕋^{2n}`) and `Square.Sharpness` (the sharpness of Burkholder's constant for dyadic martingale
transforms, `burkholderSharpness_holds`, for the lower bound of Corollary 6.3).

The Schatten exponent `q ∈ [1, ∞]` is an extended real (`⊤` for `S_∞`); in exponents such as
`d^{1 − 1/q}`, `1/q` is `1 / q.toReal`, which is `0` for `q = ∞` (the paper's `1/∞ = 0`).
`L^p (S_q)` norms of a rank-one Rademacher martingale are `lpNormWith (schattenNorm q) p`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace Cassese

variable {d : ℕ}

/-- `Sym (A) = (A + Aᵀ) / 2`. -/
noncomputable def symPart (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / 2 : ℝ) • (A + Aᵀ)

/-- `Skew (A) = (A − Aᵀ) / 2`. -/
noncomputable def skewPart (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / 2 : ℝ) • (A - Aᵀ)

/-- `Sym_{1/2} (A) = Sym (A) − ½ tr (A) Id` (Section 6.3). -/
noncomputable def symHalfPart (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  symPart A - ((1 / 2 : ℝ) * A.trace) • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The integrand (30): `f_{p,q,C} (A) = C^p ‖Sym (A)‖_{S_q}^p − ‖Skew (A)‖_{S_q}^p`. -/
noncomputable def kornF (d : ℕ) (p : ℝ) (q : ℝ≥0∞) (C : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  C ^ p * schattenNorm q (symPart A) ^ p - schattenNorm q (skewPart A) ^ p

/-- The integrand of Section 6.3:
`h_{p,q,C} (A) = C^p ‖Sym (A) − ½ tr (A) Id‖_{S_q}^p − ‖Skew (A)‖_{S_q}^p`. -/
noncomputable def hF (d : ℕ) (p : ℝ) (q : ℝ≥0∞) (C : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  C ^ p * schattenNorm q (symHalfPart A) ^ p - schattenNorm q (skewPart A) ^ p

/-! ### Linear algebra of `Sym_{1/2}` and `Skew` -/

theorem square_symHalfPart_add_smul (A R : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    symHalfPart (A + t • R) = symHalfPart A + t • symHalfPart R := by
  simp only [symHalfPart, symPart, Matrix.transpose_add, Matrix.transpose_smul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul]
  module

theorem square_skewPart_add_smul (A R : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    skewPart (A + t • R) = skewPart A + t • skewPart R := by
  simp only [skewPart, Matrix.transpose_add, Matrix.transpose_smul]
  module

theorem square_symHalfPart_transpose (A : Matrix (Fin d) (Fin d) ℝ) :
    (symHalfPart A)ᵀ = symHalfPart A := by
  simp only [symHalfPart, symPart, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_one]
  congr 2; abel

theorem square_skewPart_transpose (A : Matrix (Fin d) (Fin d) ℝ) :
    (skewPart A)ᵀ = -skewPart A := by
  simp only [skewPart, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose]
  rw [← smul_neg, neg_sub]

/-- The rank-one fact of Section 6.3, in the form used for Corollary 6.4: for `M` of rank at
most one, `Sym_{1/2} (M)² + Skew (M)² = ¼ tr (M)² Id`, so that
`Skew (M) Skew (M)ᵀ = −Skew (M)² ⪯ Sym_{1/2} (M)²`. -/
theorem square_rankOne_sq {R : Matrix (Fin d) (Fin d) ℝ} (hR : R.rank ≤ 1) :
    symHalfPart R * symHalfPart R + skewPart R * skewPart R = (R.trace ^ 2 / 4) • 1 := by
  obtain ⟨u, v, rfl⟩ := square_exists_vecMulVec hR
  set R := Matrix.vecMulVec u v
  have hRR : R * R = R.trace • R := by
    ext i k
    simp only [R, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.trace, Matrix.diag]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hRtRt : Rᵀ * Rᵀ = R.trace • Rᵀ := by
    rw [← Matrix.transpose_mul, hRR, Matrix.transpose_smul]
  simp only [symHalfPart, symPart, skewPart, sub_mul, mul_sub, add_mul, mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hRR, hRtRt, smul_smul, smul_sub, smul_add]
  module

theorem square_symHalfPart_zero : symHalfPart (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  simp only [symHalfPart, symPart, Matrix.transpose_zero, add_zero, smul_zero,
    Matrix.trace_zero, mul_zero, zero_smul, sub_zero]

theorem square_skewPart_zero : skewPart (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  simp only [skewPart, Matrix.transpose_zero, sub_zero, smul_zero]

/-- `0 < q.toReal` for a finite `q ≥ 1`. -/
theorem square_toReal_pos {q : ℝ≥0∞} (hq : 1 ≤ q) (ht : q ≠ ⊤) : 0 < q.toReal :=
  ENNReal.toReal_pos (zero_lt_one.trans_le hq).ne' ht

theorem square_one_le_toReal {q : ℝ≥0∞} (hq : 1 ≤ q) (ht : q ≠ ⊤) : 1 ≤ q.toReal := by
  have := ENNReal.toReal_mono ht hq
  rwa [ENNReal.toReal_one] at this

/-- Each singular value is at most the Schatten norm. -/
theorem square_sval_le_schattenNorm {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (A : Matrix (Fin d) (Fin m) ℝ) (k : Fin m) : sval A k ≤ schattenNorm q A := by
  unfold schattenNorm
  split_ifs with ht
  · exact le_ciSup (Set.finite_range _).bddAbove k
  · exact square_le_lp (square_sval_nonneg A) (square_toReal_pos hq ht) (Finset.mem_univ k)

/-- Each entry is at most a singular value: `|A_{ij}|² ≤ (AᵀA)_{jj} ≤ max_k λ_k (AᵀA)`. -/
theorem square_entry_le_sval {m : ℕ} (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin d) (j : Fin m) :
    ∃ k, |A i j| ≤ sval A k := by
  set hG := Matrix.isHermitian_conjTranspose_mul_self A
  set U := (hG.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
  have hU : U * star U = 1 := Unitary.coe_mul_star_self _
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ hG.eigenvalues ⟨j, Finset.mem_univ j⟩
  refine ⟨k, ?_⟩
  have hjj : (Aᴴ * A) j j = ∑ l, U j l ^ 2 * hG.eigenvalues l := by
    conv_lhs => rw [square_spectral_gram A]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, star_trivial,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hrow : ∑ l, U j l ^ 2 = 1 := by
    have := congrFun (congrFun hU j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply_eq] at this
    rw [← this]; exact Finset.sum_congr rfl fun l _ => by ring
  have hle : (Aᴴ * A) j j ≤ hG.eigenvalues k := by
    rw [hjj]
    calc ∑ l, U j l ^ 2 * hG.eigenvalues l ≤ ∑ l, U j l ^ 2 * hG.eigenvalues k :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hk l (Finset.mem_univ l))
            (sq_nonneg _)
      _ = hG.eigenvalues k := by rw [← Finset.sum_mul, hrow, one_mul]
  have hent : A i j ^ 2 ≤ (Aᴴ * A) j j := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
    calc A i j ^ 2 = A i j * A i j := sq _
      _ ≤ ∑ l, A l j * A l j :=
          Finset.single_le_sum (f := fun l => A l j * A l j) (fun l _ => mul_self_nonneg _)
            (Finset.mem_univ i)
  calc |A i j| = √(A i j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(hG.eigenvalues k) := Real.sqrt_le_sqrt (hent.trans hle)

/-- Fact (1) of Section 1.5, stated for every `q ≥ 1` (the paper states it for `q ≥ 2` and the
proof of Proposition 6.2 uses it for `q / 2 ∈ (1, 2)`, inventory E2): for self-adjoint `A`,
`‖A²‖_{S_q} = ‖A‖_{S_{2q}}²`. One of the facts that the paper calls "immediate consequences of
the definitions (see also Bhatia, *Matrix analysis*, Chapter 4)". It is the bridge
(`schattenNorm_sq_of_mul_self`, `schattenNorm_sqrt_sq`) between the paper's square function
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}` in Proposition 6.3 and (31) and the form `√‖Σ x_i x_iᵀ‖_{S_{q/2}}`
in which `PisierXuKhintchine`, `equation31` and the proofs of Section 6.2 write it.

Proof (the standard one): with `AᵀA = U diag (λ) Uᵀ`, `(A²)ᵀ A² = (AᵀA)² = U diag (λ²) Uᵀ`, so
the singular values of `A²` are the `s_i (A)²` up to order (`square_sum_sval_mul_self`). -/
theorem schattenNorm_mul_self {q : ℝ} (hq : 1 ≤ q) {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm) :
    schattenNorm (ENNReal.ofReal q) (A * A) = schattenNorm (ENNReal.ofReal (2 * q)) A ^ 2 := by
  have hq0 : 0 < q := by linarith
  unfold schattenNorm
  rw [ite_eq_right ENNReal.ofReal_ne_top, ite_eq_right ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le,
    ENNReal.toReal_ofReal (by linarith), square_sum_sval_mul_self hA (fun x => x ^ q)]
  have h : ∀ i, (sval A i ^ 2) ^ q = sval A i ^ (2 * q) := fun i => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (square_sval_nonneg A i)]; norm_num
  simp_rw [h]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (square_sval_nonneg A i) _)]
  congr 1
  field_simp
  norm_num

/-- A positive semidefinite `B` has a positive semidefinite square root `B^{1/2}`
(`B^{1/2} B^{1/2} = B`): `B^{1/2} = U diag (√λ) Uᵀ` from the spectral theorem
`B = U diag (λ) Uᵀ` (`square_spectral`). -/
theorem square_exists_sqrt {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosSemidef) :
    ∃ S : Matrix (Fin d) (Fin d) ℝ, S.PosSemidef ∧ S * S = B := by
  set U := (hB.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  set D := Matrix.diagonal fun i => √(hB.1.eigenvalues i)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hD : D.PosSemidef := Matrix.PosSemidef.diagonal fun i => Real.sqrt_nonneg _
  refine ⟨U * D * star U, ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose]; exact hD.mul_mul_conjTranspose_same U
  · have hDD : D * D = Matrix.diagonal hB.1.eigenvalues := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      exact Real.mul_self_sqrt (hB.eigenvalues_nonneg i)
    conv_rhs => rw [square_spectral hB.1]
    calc U * D * star U * (U * D * star U) = U * D * (star U * U) * D * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (D * D) * star U := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hDD]

/-- **The two forms of the square function** (Proposition 6.3, equation (31)): for `q ≥ 2` and a
symmetric square root `S` of `B` (`S * S = B`; for `B ⪰ 0`, the positive semidefinite root
`B^{1/2}` of `square_exists_sqrt`), `‖S‖_{S_q}² = ‖B‖_{S_{q/2}}`. Fact (1)
(`schattenNorm_mul_self`) applied to `S` at the exponent `q / 2 ≥ 1`. So the paper's
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}` equals the `√‖Σ x_i x_iᵀ‖_{S_{q/2}}` in which `PisierXuKhintchine`,
`equation31` and the proofs of Section 6.2 write the square function (`schattenNorm_sqrt_sq`). -/
theorem schattenNorm_sq_of_mul_self {q : ℝ} (hq : 2 ≤ q) {S B : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.IsSymm) (hSB : S * S = B) :
    schattenNorm (ENNReal.ofReal q) S ^ 2 = schattenNorm (ENNReal.ofReal (q / 2)) B := by
  rw [← hSB, schattenNorm_mul_self (by linarith) hS, mul_div_cancel₀ q two_ne_zero]

/-- `‖B^{1/2}‖_{S_q}² = ‖B‖_{S_{q/2}}` for `B ⪰ 0` and `q ≥ 2`, with `B^{1/2}` the positive
semidefinite square root (`square_exists_sqrt`); equivalently
`‖B^{1/2}‖_{S_q} = √‖B‖_{S_{q/2}}`. The bridge between the paper's form
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}` of Proposition 6.3 and (31) and the form
`√‖Σ x_i x_iᵀ‖_{S_{q/2}}` of `PisierXuKhintchine` and `equation31`. -/
theorem schattenNorm_sqrt_sq {q : ℝ} (hq : 2 ≤ q) {B : Matrix (Fin d) (Fin d) ℝ}
    (hB : B.PosSemidef) :
    ∃ S : Matrix (Fin d) (Fin d) ℝ, S.PosSemidef ∧ S * S = B ∧
      schattenNorm (ENNReal.ofReal q) S ^ 2 = schattenNorm (ENNReal.ofReal (q / 2)) B ∧
      schattenNorm (ENNReal.ofReal q) S = √(schattenNorm (ENNReal.ofReal (q / 2)) B) := by
  obtain ⟨S, hS, hSB⟩ := square_exists_sqrt hB
  have hSs : S.IsSymm := by
    rw [Matrix.IsSymm, ← square_conjTranspose_eq]; exact hS.1
  have h := schattenNorm_sq_of_mul_self hq hSs hSB
  refine ⟨S, hS, hSB, h, ?_⟩
  rw [← h, Real.sqrt_sq (schattenNorm_nonneg _ _)]

/-- Fact (2) of Section 1.5, first part: `‖A‖_{S_1} ≥ ‖A‖_{S_p} ≥ ‖A‖_{S_q} ≥ ‖A‖_{S_∞}` for
`p ≤ q`.

Proof (the standard one): the `ℓ^p` norms of the singular values decrease in `p`
(`square_lq_le_lp`: `s_i ≤ ‖s‖_p`, so `Σ s_i^q ≤ ‖s‖_p^{q−p} Σ s_i^p`). -/
theorem schattenNorm_anti {m : ℕ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (A : Matrix (Fin d) (Fin m) ℝ) : schattenNorm q A ≤ schattenNorm p A := by
  by_cases hqt : q = ⊤
  · by_cases hpt : p = ⊤
    · rw [hqt, hpt]
    · have hr := square_toReal_pos hp hpt
      unfold schattenNorm
      rw [ite_eq_left hqt, ite_eq_right hpt]
      rcases isEmpty_or_nonempty (Fin m) with hm | hm
      · rw [Real.iSup_of_isEmpty]
        exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
          Real.rpow_nonneg (square_sval_nonneg A i) _) _
      · exact ciSup_le fun k => square_le_lp (square_sval_nonneg A) hr (Finset.mem_univ k)
  · have hpt : p ≠ ⊤ := ne_top_of_le_ne_top hqt hpq
    unfold schattenNorm
    rw [ite_eq_right hqt, ite_eq_right hpt]
    exact square_lq_le_lp _ (square_sval_nonneg A) (square_toReal_pos hp hpt)
      (ENNReal.toReal_mono hqt hpq)

/-- Fact (2) of Section 1.5, second part: `‖A‖_{S_p} ≤ min (d, m)^{1/p − 1/q} ‖A‖_{S_q}` for
`1 ≤ p ≤ q ≤ ∞` (with `1/∞ = 0`).

Proof (the standard one): at most `rank A ≤ min (d, m)` singular values are nonzero
(`square_card_sval_ne_zero`: they are the nonzero eigenvalues of `AᵀA`), and on those the power-mean
inequality gives `‖s‖_p ≤ k^{1/p − 1/q} ‖s‖_q` (`square_lp_le_card_mul_lq`). -/
theorem schattenNorm_le_rpow_mul {m : ℕ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm p A ≤ (min d m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * schattenNorm q A := by
  set S := Finset.univ.filter fun i => sval A i ≠ 0
  have hS := square_card_sval_ne_zero A
  by_cases hpt : p = ⊤
  · have hqt : q = ⊤ := top_le_iff.1 (hpt ▸ hpq)
    rw [hpt, hqt, ENNReal.toReal_top, div_zero, sub_zero, Real.rpow_zero, one_mul]
  have hr := square_toReal_pos hp hpt
  by_cases hqt : q = ⊤
  · have hM : ∀ i ∈ S, sval A i ≤ ⨆ k, sval A k := fun i _ =>
      le_ciSup (Set.finite_range _).bddAbove i
    have hM0 : 0 ≤ ⨆ k, sval A k := Real.iSup_nonneg (square_sval_nonneg A)
    unfold schattenNorm
    rw [ite_eq_right hpt, ite_eq_left hqt, hqt, ENNReal.toReal_top, div_zero, sub_zero,
      square_sum_sval_filter A hr]
    calc (∑ i ∈ S, sval A i ^ p.toReal) ^ (1 / p.toReal)
        ≤ (S.card : ℝ) ^ (1 / p.toReal) * ⨆ k, sval A k :=
          square_lp_le_card_mul_max S (square_sval_nonneg A) hr hM
      _ ≤ (min d m : ℝ) ^ (1 / p.toReal) * ⨆ k, sval A k :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hS (by positivity))
            hM0
  · have ht := ENNReal.toReal_mono hqt hpq
    have hr1 := square_one_le_toReal hp hpt
    unfold schattenNorm
    rw [ite_eq_right hpt, ite_eq_right hqt, square_sum_sval_filter A hr,
      square_sum_sval_filter A (by linarith)]
    have he : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hr ht
    calc (∑ i ∈ S, sval A i ^ p.toReal) ^ (1 / p.toReal)
        ≤ (S.card : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
            (∑ i ∈ S, sval A i ^ q.toReal) ^ (1 / q.toReal) :=
          square_lp_le_card_mul_lq S (square_sval_nonneg A) hr1 ht
      _ ≤ (min d m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
            (∑ i ∈ S, sval A i ^ q.toReal) ^ (1 / q.toReal) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hS he)
            (Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
              Real.rpow_nonneg (square_sval_nonneg A i) _) _)

/-- Weyl's monotonicity for matrices: `A ⪯ B` increases the decreasingly ordered
eigenvalues (`square_weyl`, the Courant–Fischer argument). -/
theorem square_eigenvalues₀_mono {A B : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : (B - A).PosSemidef) (k : Fin (Fintype.card (Fin d))) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  refine square_weyl (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace (fun v => ?_) k
  have h := hAB.re_dotProduct_nonneg (WithLp.ofLp v)
  simp only [RCLike.re_to_real, star_trivial, Matrix.sub_mulVec, dotProduct_sub] at h
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toLpLin_apply, star_trivial, WithLp.ofLp_toLp]
  linarith

/-- For a positive semidefinite `A`, the singular values are the eigenvalues:
`Σ_i f (s_i (A)) = Σ_k f (λ_k (A))`. -/
theorem square_sum_sval_psd {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) (f : ℝ → ℝ) :
    ∑ i, f (sval A i) = ∑ k, f (hA.1.eigenvalues₀ k) := by
  set U := (hA.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hAh : Aᴴ = A := hA.1
  have hsp := square_spectral hA.1
  have h : Aᴴ * A = U * Matrix.diagonal (fun i => hA.1.eigenvalues i ^ 2) * star U := by
    have hd : Matrix.diagonal (fun i => hA.1.eigenvalues i ^ 2) =
        Matrix.diagonal hA.1.eigenvalues * Matrix.diagonal hA.1.eigenvalues := by
      rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; ring
    conv_lhs => rw [hAh, hsp]
    rw [hd]
    calc U * Matrix.diagonal hA.1.eigenvalues * star U * (U * Matrix.diagonal hA.1.eigenvalues * star U)
        = U * Matrix.diagonal hA.1.eigenvalues * (star U * U) * Matrix.diagonal hA.1.eigenvalues *
            star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have := square_sum_eigenvalues_eq (Matrix.isHermitian_conjTranspose_mul_self A) _ _ h
    (fun x => f √x)
  simp only [sval]
  rw [this]
  simp_rw [Real.sqrt_sq (hA.eigenvalues_nonneg _)]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => f (hA.1.eigenvalues₀ k))

/-- For a positive semidefinite `A`: `max_i s_i (A) = max_k λ_k (A)`. -/
theorem square_iSup_sval_psd {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) :
    ⨆ i, sval A i = ⨆ k, hA.1.eigenvalues₀ k := by
  set U := (hA.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hAh : Aᴴ = A := hA.1
  have hsp := square_spectral hA.1
  have h : Aᴴ * A = U * Matrix.diagonal (fun i => hA.1.eigenvalues i ^ 2) * star U := by
    have hd : Matrix.diagonal (fun i => hA.1.eigenvalues i ^ 2) =
        Matrix.diagonal hA.1.eigenvalues * Matrix.diagonal hA.1.eigenvalues := by
      rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; ring
    conv_lhs => rw [hAh, hsp]
    rw [hd]
    calc U * Matrix.diagonal hA.1.eigenvalues * star U * (U * Matrix.diagonal hA.1.eigenvalues * star U)
        = U * Matrix.diagonal hA.1.eigenvalues * (star U * U) * Matrix.diagonal hA.1.eigenvalues *
            star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have := square_iSup_eigenvalues_eq (Matrix.isHermitian_conjTranspose_mul_self A) _ _ h
    (fun x => √x)
  simp only [sval]
  rw [this]
  simp_rw [Real.sqrt_sq (hA.eigenvalues_nonneg _)]
  exact Equiv.iSup_comp (g := fun k => hA.1.eigenvalues₀ k)
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm

/-- Fact (3) of Section 1.5: if `0 ⪯ A ⪯ B` (Loewner order) then `‖A‖_{S_q} ≤ ‖B‖_{S_q}` for
every `q ∈ [1, ∞]`.

Proof (the standard one, Bhatia, Corollary III.2.3): for positive semidefinite `A` the singular
values are the eigenvalues (`square_sum_sval_psd`), and `A ⪯ B` increases each decreasingly
ordered eigenvalue (Weyl's monotonicity theorem `square_weyl`, by the Courant–Fischer argument). -/
theorem schattenNorm_mono {q : ℝ≥0∞} (hq : 1 ≤ q) {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) : schattenNorm q A ≤ schattenNorm q B := by
  have hB : B.PosSemidef := by simpa using hA.add hAB
  have hmono := square_eigenvalues₀_mono hA.1 hB.1 hAB
  have hnA : ∀ k, 0 ≤ hA.1.eigenvalues₀ k := fun k => by
    have := hA.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) k)
    simpa [Matrix.IsHermitian.eigenvalues] using this
  unfold schattenNorm
  split_ifs with ht
  · rw [square_iSup_sval_psd hA, square_iSup_sval_psd hB]
    rcases isEmpty_or_nonempty (Fin (Fintype.card (Fin d))) with he | he
    · simp
    · exact ciSup_mono (Set.finite_range _).bddAbove hmono
  · have hr := square_toReal_pos hq ht
    rw [square_sum_sval_psd hA (fun x => x ^ q.toReal), square_sum_sval_psd hB (fun x => x ^ q.toReal)]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hnA k) _)
      (Finset.sum_le_sum fun k _ => Real.rpow_le_rpow (hnA k) (hmono k) hr.le) (by positivity)

/-! ### The Schatten norm is a norm

The paper takes for granted that `‖·‖_{S_q}`, `q ∈ [1, ∞]`, is a norm on `ℝ^{d×m}` (Section 1.5,
TeX lines 348–357; Bhatia, *Matrix analysis*, Chapter IV). Propositions 6.2, 6.5 and
Corollary 6.1 apply `HNVWExtrapolation` and `CoxVeraarDecoupling` (`hnvwExtrapolation_holds`,
`coxVeraarDecoupling_holds`) to `S_q^{d×d}`, that is to `E = Fin d → Fin d → ℝ` with
`nrm X = ‖X‖_{S_q}`, which requires the hypotheses on `nrm` of those statements: the triangle inequality, absolute homogeneity, and equivalence with the norm of `E`
(the supremum norm of the entries). They are proved here (nonnegativity, `schattenNorm_nonneg`,
in `Square.Schatten`), and bundled in `schattenNorm_renorms`. -/

/-- The triangle inequality for `‖·‖_{S_q}`, `q ∈ [1, ∞]` (Bhatia, Chapter IV).

Proof (`square_schattenNorm_add_le`, module `Square.Triangle`), by the standard argument through
doubly substochastic matrices: with `v_k` the eigenvectors of `(A + B)ᵀ (A + B)` and
`ξ_k = (A + B) v_k / s_k (A + B)`, `s_k (A + B) = ⟨ξ_k, A v_k⟩ + ⟨ξ_k, B v_k⟩`; the diagonal entries
`|⟨ξ_k, A v_k⟩|` are dominated by a doubly substochastic average `Σ_j M_{kj} s_j (A)`
(`M_{kj} = (⟨ξ_k, A y_j⟩² / s_j² + ⟨y_j, v_k⟩²) / 2`, Bessel's inequality), so that
`Σ_k |⟨ξ_k, A v_k⟩|^q ≤ ‖A‖_{S_q}^q` (Jensen) and `|⟨ξ_k, A v_k⟩| ≤ ‖A‖_{S_∞}`; Minkowski's
inequality in `ℓ^q` concludes. Departure from the source: Bhatia, Chapter IV, derives the
triangle inequality from Ky Fan's dominance theorem (the Ky Fan `k`-norms are norms, and
symmetric gauge functions are monotone under weak majorization); the argument here avoids the
theory of majorization, which Mathlib lacks, and uses only Bessel's, Jensen's and Minkowski's
inequalities. -/
theorem schattenNorm_add_le {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B :=
  square_schattenNorm_add_le hq A B

/-- Absolute homogeneity of `‖·‖_{S_q}`, `q ∈ [1, ∞]`: `s_i (c A) = |c| s_i (A)`. -/
theorem schattenNorm_smul {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) (c : ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm q (c • A) = |c| * schattenNorm q A := by
  unfold schattenNorm
  split_ifs with ht
  · rw [Real.mul_iSup_of_nonneg (abs_nonneg c)]
    show sSup (Set.range fun i => sval (c • A) i) = sSup (Set.range fun i => |c| * sval A i)
    rw [square_range_sval_smul]
  · have hr := square_toReal_pos hq ht
    rw [square_sum_sval_smul c A (fun x => x ^ q.toReal)]
    simp_rw [Real.mul_rpow (abs_nonneg c) (square_sval_nonneg A _)]
    rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (square_sval_nonneg A i) _),
      ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hr.ne', Real.rpow_one]

/-- `‖·‖_{S_q}`, `q ∈ [1, ∞]`, is positive definite: `‖A‖_{S_q} = 0` only for `A = 0`. -/
theorem schattenNorm_eq_zero_iff {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (A : Matrix (Fin d) (Fin m) ℝ) : schattenNorm q A = 0 ↔ A = 0 := by
  have hsv : (∀ i, sval A i = 0) ↔ A = 0 := by
    constructor
    · intro h
      have hev : (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues = 0 := by
        funext i
        have := h i
        rwa [sval, Real.sqrt_eq_zero (square_eigenvalues_nonneg A i)] at this
      rw [Matrix.IsHermitian.eigenvalues_eq_zero_iff] at hev
      exact Matrix.conjTranspose_mul_self_eq_zero.1 hev
    · rintro rfl i
      have : (Matrix.isHermitian_conjTranspose_mul_self
          (0 : Matrix (Fin d) (Fin m) ℝ)).eigenvalues = 0 := by
        rw [Matrix.IsHermitian.eigenvalues_eq_zero_iff, Matrix.mul_zero]
      rw [sval, this, Pi.zero_apply, Real.sqrt_zero]
  rw [← hsv]
  unfold schattenNorm
  split_ifs with ht
  · constructor
    · intro h i
      exact le_antisymm (h ▸ le_ciSup (Set.finite_range _).bddAbove i) (square_sval_nonneg A i)
    · intro h
      simp only [h, Real.iSup_const_zero]
  · have hr := square_toReal_pos hq ht
    rw [Real.rpow_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (square_sval_nonneg A i) _),
      Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Real.rpow_nonneg (square_sval_nonneg A i) _)]
    simp only [Finset.mem_univ, forall_const, Real.rpow_eq_zero_iff_of_nonneg
      (square_sval_nonneg A _), ne_eq, hr.ne', not_false_eq_true, and_true, one_div,
      inv_eq_zero]

/-- The lower comparison with the supremum norm of the entries: `|A_{ij}| ≤ s_max (A) ≤ ‖A‖_{S_q}`
for `q ∈ [1, ∞]`. -/
theorem norm_le_schattenNorm {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) (X : Fin d → Fin m → ℝ) :
    ‖X‖ ≤ schattenNorm q (Matrix.of X) := by
  have hnn := schattenNorm_nonneg q (Matrix.of X)
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => (pi_norm_le_iff_of_nonneg hnn).2 fun j => ?_
  rw [Real.norm_eq_abs]
  obtain ⟨k, hk⟩ := square_entry_le_sval (Matrix.of X) i j
  exact hk.trans (square_sval_le_schattenNorm hq _ k)

/-- The upper comparison with the supremum norm of the entries, with an explicit constant:
`‖A‖_{S_q} ≤ ‖A‖_{S_1} ≤ √m ‖A‖_{S_2} ≤ √m √(d m) max |A_{ij}| ≤ d m max |A_{ij}|` for
`q ∈ [1, ∞]`. -/
theorem schattenNorm_le_norm {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) (X : Fin d → Fin m → ℝ) :
    schattenNorm q (Matrix.of X) ≤ (d * m : ℝ) * ‖X‖ := by
  set A := Matrix.of X
  have h1 : schattenNorm q A ≤ schattenNorm 1 A := schattenNorm_anti le_rfl hq A
  have h2 : schattenNorm 1 A = ∑ i, sval A i := by
    simp [schattenNorm]
  -- `(Σ s_i)² ≤ m Σ s_i² = m tr (AᵀA) ≤ m · d m ‖X‖² ≤ (d m ‖X‖)²`
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (sval A) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hcs
  rw [square_sum_sval_sq] at hcs
  have htr : (Aᵀ * A).trace ≤ d * m * ‖X‖ ^ 2 := by
    have : (Aᵀ * A).trace = ∑ j, ∑ i, X i j ^ 2 := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, A,
        Matrix.of_apply, sq]
    rw [this]
    have hb : ∀ i j, X i j ^ 2 ≤ ‖X‖ ^ 2 := fun i j => by
      have h := (norm_le_pi_norm (X i) j).trans (norm_le_pi_norm X i)
      rw [Real.norm_eq_abs] at h
      exact (sq_abs (X i j)).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) h 2)
    calc ∑ j, ∑ i, X i j ^ 2 ≤ ∑ _j : Fin m, ∑ _i : Fin d, ‖X‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hb i j
      _ = d * m * ‖X‖ ^ 2 := by simp [Finset.sum_const]; ring
  have hsum0 : 0 ≤ ∑ i, sval A i := Finset.sum_nonneg fun i _ => square_sval_nonneg A i
  have hd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith
  have hsq : (∑ i, sval A i) ^ 2 ≤ ((d * m : ℝ) * ‖X‖) ^ 2 := by
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hX0 : 0 ≤ ‖X‖ ^ 2 := by positivity
    calc (∑ i, sval A i) ^ 2 ≤ (Aᵀ * A).trace * m := hcs
      _ ≤ (d * m * ‖X‖ ^ 2) * m := mul_le_mul_of_nonneg_right htr hm0
      _ = d * m ^ 2 * ‖X‖ ^ 2 := by ring
      _ ≤ d ^ 2 * m ^ 2 * ‖X‖ ^ 2 := by gcongr
      _ = ((d * m : ℝ) * ‖X‖) ^ 2 := by ring
  have h3 : ∑ i, sval A i ≤ (d * m : ℝ) * ‖X‖ :=
    (pow_le_pow_iff_left₀ hsum0 (by positivity) two_ne_zero).1 hsq
  linarith

/-- `S_q^{d×d}`, `q ∈ [1, ∞]`, is `Fin d → Fin d → ℝ` renormed by an equivalent norm: the
hypotheses on `nrm = ‖·‖_{S_q}` of `HNVWExtrapolation` and `CoxVeraarDecoupling` (with `a = 1`,
`b = d² + 1`). -/
theorem schattenNorm_renorms {q : ℝ≥0∞} (hq : 1 ≤ q) :
    (∀ X Y : Fin d → Fin d → ℝ, schattenNorm q (Matrix.of (X + Y)) ≤
      schattenNorm q (Matrix.of X) + schattenNorm q (Matrix.of Y)) ∧
    (∀ (c : ℝ) (X : Fin d → Fin d → ℝ),
      schattenNorm q (Matrix.of (c • X)) = |c| * schattenNorm q (Matrix.of X)) ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ X : Fin d → Fin d → ℝ,
      a * ‖X‖ ≤ schattenNorm q (Matrix.of X) ∧ schattenNorm q (Matrix.of X) ≤ b * ‖X‖ := by
  refine ⟨fun X Y => ?_, fun c X => ?_, 1, (d * d : ℝ) + 1, one_pos, by positivity, fun X =>
    ⟨by rw [one_mul]; exact norm_le_schattenNorm hq X, ?_⟩⟩
  · rw [← Matrix.of_add_of]; exact schattenNorm_add_le hq _ _
  · rw [← Matrix.smul_of]; exact schattenNorm_smul hq c _
  · calc schattenNorm q (Matrix.of X) ≤ (d * d : ℝ) * ‖X‖ := schattenNorm_le_norm hq X
      _ ≤ ((d * d : ℝ) + 1) * ‖X‖ := by nlinarith [norm_nonneg X]

/-! ### Tools for the results of Section 6.2

The proofs of equation (31), Propositions 6.2, 6.5 and Remark 6.3. Helpers have the prefix
`square_`. -/

/-- `‖0‖_{S_q} = 0`. -/
theorem square_schattenNorm_zero {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) :
    schattenNorm q (0 : Matrix (Fin d) (Fin m) ℝ) = 0 :=
  (schattenNorm_eq_zero_iff hq 0).2 rfl

/-- `‖·‖_{S_q}`, `q ∈ [1, ∞]`, is continuous: it is `d m`-Lipschitz for the supremum norm of the
entries (triangle inequality and `schattenNorm_le_norm`). -/
theorem square_continuous_schattenNorm {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) :
    Continuous (fun A : Matrix (Fin d) (Fin m) ℝ => schattenNorm q A) := by
  have hL : LipschitzWith ((d * m : ℕ) : NNReal)
      (fun X : Fin d → Fin m → ℝ => schattenNorm q (Matrix.of X)) := by
    refine LipschitzWith.of_dist_le_mul fun X Y => ?_
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_natCast]
    push_cast
    have e1 : Matrix.of X = Matrix.of (X - Y) + Matrix.of Y := by ext i j; simp
    have e2 : Matrix.of Y = (-1 : ℝ) • Matrix.of (X - Y) + Matrix.of X := by ext i j; simp
    have h1 := schattenNorm_add_le hq (Matrix.of (X - Y)) (Matrix.of Y)
    have h2 := schattenNorm_add_le hq ((-1 : ℝ) • Matrix.of (X - Y)) (Matrix.of X)
    rw [← e1] at h1
    rw [← e2, schattenNorm_smul hq, abs_neg, abs_one, one_mul] at h2
    have h4 := schattenNorm_le_norm hq (X - Y)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  exact hL.continuous

theorem square_continuous_symPart :
    Continuous (symPart : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
  unfold symPart
  fun_prop

theorem square_continuous_skewPart :
    Continuous (skewPart : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
  unfold skewPart
  fun_prop

/-- The integrand (30) is continuous for `p ≥ 0`. -/
theorem square_continuous_kornF {p : ℝ} (hp : 0 ≤ p) {q : ℝ≥0∞} (hq : 1 ≤ q) (C : ℝ) :
    Continuous (kornF d p q C) := by
  have hs := (square_continuous_schattenNorm (d := d) (m := d) hq).comp square_continuous_symPart
  have hk := (square_continuous_schattenNorm (d := d) (m := d) hq).comp
    square_continuous_skewPart
  exact (continuous_const.mul (hs.rpow_const fun _ => Or.inr hp)).sub
    (hk.rpow_const fun _ => Or.inr hp)

theorem square_symPart_zero : symPart (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  simp [symPart]

theorem square_kornF_zero {p : ℝ} (hp : 0 < p) {q : ℝ≥0∞} (hq : 1 ≤ q) (C : ℝ) :
    kornF d p q C 0 = 0 := by
  rw [kornF, square_symPart_zero, square_skewPart_zero, square_schattenNorm_zero hq,
    Real.zero_rpow hp.ne', mul_zero, sub_zero]

/-- `Sym` and `Skew` of a Rademacher martingale are the Rademacher martingales of the `Sym` and
`Skew` of its increments. -/
theorem square_symPart_mart {N : ℕ} (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (ε : Fin N → Bool) :
    symPart (mart A n ε) = mart (fun k ε => symPart (A k ε)) n ε := by
  simp only [mart, symPart, Matrix.transpose_sum, Matrix.transpose_smul, ← Finset.sum_add_distrib,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by module

theorem square_skewPart_mart {N : ℕ} (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (ε : Fin N → Bool) :
    skewPart (mart A n ε) = mart (fun k ε => skewPart (A k ε)) n ε := by
  simp only [mart, skewPart, Matrix.transpose_sum, Matrix.transpose_smul, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by module

/-- `‖Y‖_{S_1} = tr Y` for positive semidefinite `Y` (its singular values are its eigenvalues). -/
theorem square_schattenNorm_one_psd {Y : Matrix (Fin d) (Fin d) ℝ} (hY : Y.PosSemidef) :
    schattenNorm 1 Y = Y.trace := by
  have h1 : schattenNorm 1 Y = ∑ i, sval Y i := by simp [schattenNorm]
  have h2 := square_sum_sval_psd hY id
  simp only [id] at h2
  rw [h1, h2, hY.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => hY.1.eigenvalues₀ k)).symm

/-- Optimising `t ↦ (t/2) X + Y / (2t)` over `t > 0`: its infimum is `√(XY)`. -/
theorem square_le_sqrt_mul_of_forall {Z X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : ∀ t : ℝ, 0 < t → Z ≤ t / 2 * X + 1 / (2 * t) * Y) : Z ≤ √X * √Y := by
  rw [← Real.sqrt_mul hX]
  rcases le_or_gt Z 0 with hZ | hZ
  · exact hZ.trans (Real.sqrt_nonneg _)
  rw [Real.le_sqrt' hZ]
  rcases hX.eq_or_lt with hX0 | hXp
  · exfalso
    have h1 := h ((Y + 1) / Z) (by positivity)
    rw [← hX0, mul_zero, zero_add] at h1
    have e : 1 / (2 * ((Y + 1) / Z)) * Y = Y * Z / (2 * (Y + 1)) := by field_simp
    rw [e, le_div_iff₀ (by positivity)] at h1
    nlinarith
  · have h1 := h (Z / X) (by positivity)
    have e : Z / X / 2 * X + 1 / (2 * (Z / X)) * Y = Z / 2 + X * Y / (2 * Z) := by field_simp
    rw [e] at h1
    have h2 : Z / 2 ≤ X * Y / (2 * Z) := by linarith
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith

/-- **The pointwise square-function comparison of Proposition 6.2** (TeX lines 2353–2378): for
matrices `R_k` of rank at most one, with `S_k = Sym R_k`, `K_k = Skew R_k` and `r ≥ 1`,
`‖Σ K_k K_kᵀ‖_{S_r} ≤ ‖Σ S_k S_kᵀ‖_{S_r}^{1/2} (tr Σ S_k S_kᵀ)^{1/2}`; with `r = q/2` this is
`‖𝔖_n g‖_{S_q}² ≤ ‖𝔖_n f‖_{S_q} ‖𝔖_n f‖_{S_2}`.

Proof (the paper's): the Loewner bound `K_k K_kᵀ ⪯ (t/2) S_k² + (1/(2t)) S_k^#` with
`tr S_k^# ≤ tr S_k²` (`square_korn_loewner`, after writing `R_k = (u + w) ⊗ (u − w)`, `u ⊥ w`,
`square_korn_rankOne_orth`), summed over `k`; fact (3) (`schattenNorm_mono`), the triangle
inequality, `‖Σ S_k^#‖_{S_r} ≤ ‖Σ S_k^#‖_{S_1} = tr Σ S_k^#` (fact (2)); and optimisation in `t`. -/
theorem square_rankOne_comparison {N : ℕ} {r : ℝ≥0∞} (hr : 1 ≤ r)
    (R : Fin N → Matrix (Fin d) (Fin d) ℝ) (hR : ∀ k, (R k).rank ≤ 1) :
    schattenNorm r (∑ k, skewPart (R k) * (skewPart (R k))ᵀ) ≤
      √(schattenNorm r (∑ k, symPart (R k) * (symPart (R k))ᵀ)) *
        √((∑ k, symPart (R k) * (symPart (R k))ᵀ).trace) := by
  choose u w huw hRuw using fun k => square_korn_rankOne_orth (hR k)
  have hS : ∀ k, symPart (R k) =
      Matrix.vecMulVec (u k) (u k) - Matrix.vecMulVec (w k) (w k) := fun k => by
    rw [hRuw k, symPart, Matrix.transpose_vecMulVec]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
      Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hK : ∀ k, skewPart (R k) =
      Matrix.vecMulVec (w k) (u k) - Matrix.vecMulVec (u k) (w k) := fun k => by
    rw [hRuw k, skewPart, Matrix.transpose_vecMulVec]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
      Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  choose T hT0 hTtr hTle using fun k => square_korn_loewner (huw k)
  set X := ∑ k, symPart (R k) * (symPart (R k))ᵀ with hXdef
  set Z := ∑ k, skewPart (R k) * (skewPart (R k))ᵀ with hZdef
  set Y := ∑ k, T k with hYdef
  have hpsd : ∀ P : Matrix (Fin d) (Fin d) ℝ, (P * Pᵀ).PosSemidef := fun P => by
    simpa [square_conjTranspose_eq] using Matrix.posSemidef_self_mul_conjTranspose P
  have hZ : Z.PosSemidef := Matrix.posSemidef_sum _ fun k _ => hpsd _
  have hX : X.PosSemidef := Matrix.posSemidef_sum _ fun k _ => hpsd _
  have hY : Y.PosSemidef := Matrix.posSemidef_sum _ fun k _ => hT0 k
  have hYtr : Y.trace ≤ X.trace := by
    rw [hYdef, hXdef, Matrix.trace_sum, Matrix.trace_sum]
    exact Finset.sum_le_sum fun k _ => by rw [hS k]; exact hTtr k
  have hYn : schattenNorm r Y ≤ X.trace :=
    (schattenNorm_anti le_rfl hr Y).trans ((square_schattenNorm_one_psd hY).le.trans hYtr)
  refine square_le_sqrt_mul_of_forall (schattenNorm_nonneg r X) hX.trace_nonneg fun t ht => ?_
  have hdiff : ((t / 2) • X + (1 / (2 * t)) • Y - Z).PosSemidef := by
    have e : (t / 2) • X + (1 / (2 * t)) • Y - Z = ∑ k, ((t / 2) • (symPart (R k) *
        (symPart (R k))ᵀ) + (1 / (2 * t)) • T k - skewPart (R k) * (skewPart (R k))ᵀ) := by
      simp only [hXdef, hYdef, hZdef, Finset.smul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
    rw [e]
    exact Matrix.posSemidef_sum _ fun k _ => by rw [hS k, hK k]; exact hTle k t ht
  calc schattenNorm r Z ≤ schattenNorm r ((t / 2) • X + (1 / (2 * t)) • Y) :=
        schattenNorm_mono hr hZ hdiff
    _ ≤ schattenNorm r ((t / 2) • X) + schattenNorm r ((1 / (2 * t)) • Y) :=
        schattenNorm_add_le hr _ _
    _ = t / 2 * schattenNorm r X + 1 / (2 * t) * schattenNorm r Y := by
        rw [schattenNorm_smul hr, schattenNorm_smul hr, abs_of_pos (by positivity),
          abs_of_pos (by positivity)]
    _ ≤ t / 2 * schattenNorm r X + 1 / (2 * t) * X.trace := by
        gcongr

/-- `lpNormWith nrm 2 X = (E nrm (X)²)^{1/2}`. -/
theorem square_lpNormWith_two {N : ℕ} {E : Type*} (nrm : E → ℝ) (X : (Fin N → Bool) → E) :
    lpNormWith nrm 2 X = √(avg fun ε => nrm (X ε) ^ 2) := by
  rw [lpNormWith, Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two]

/-- Decoupling (Proposition 2.8, `CoxVeraarDecoupling`) in `S_q^{d×d}`, in real form, for a
`UMD_p` bound `u` of `S_q^{d×d}`: with `f̃_N` the decoupled martingale,
`‖f̃_N‖_{L^p (S_q)} ≤ u ‖f_N‖_{L^p (S_q)}` and `‖f_N‖_{L^p (S_q)} ≤ u ‖f̃_N‖_{L^p (S_q)}`. -/
theorem square_decoupling {q u : ℝ} (hq : 1 < q) (hu : 0 ≤ u)
    {p : ℝ} (hp : 1 < p)
    (hU : umdConstWith (Fin d → Fin d → ℝ)
      (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) p ≤ ENNReal.ofReal u)
    {N : ℕ} (ξ : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ) (hξ : IsPredictable ξ) :
    (avg fun ε => avg fun ε' =>
        schattenNorm (ENNReal.ofReal q) (∑ k, coin (ε' k) • ξ k ε) ^ p) ^ (1 / p) ≤
        u * lpNormWith (schattenNorm (ENNReal.ofReal q)) p (mart ξ N) ∧
      lpNormWith (schattenNorm (ENNReal.ofReal q)) p (mart ξ N) ≤
        u * (avg fun ε => avg fun ε' =>
          schattenNorm (ENNReal.ofReal q) (∑ k, coin (ε' k) • ξ k ε) ^ p) ^ (1 / p) := by
  have hQ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le
  have hp0 : 0 < p := by linarith
  obtain ⟨htri, hhom, hequiv⟩ := schattenNorm_renorms (d := d) hQ1
  obtain ⟨h1, h2⟩ :=
    coxVeraarDecoupling_holds (Fin d → Fin d → ℝ) _ htri hhom hequiv p hp N ξ hξ N
  set a := (avg fun ε => avg fun ε' =>
    schattenNorm (ENNReal.ofReal q) (∑ k, coin (ε' k) • ξ k ε) ^ p) ^ (1 / p) with ha
  set b := lpNormWith (schattenNorm (ENNReal.ofReal q)) p (mart ξ N) with hb
  have hdec : (avg fun ε => avg fun ε' => (fun X : Fin d → Fin d → ℝ =>
      schattenNorm (ENNReal.ofReal q) (Matrix.of X)) (mart (fun k _ => ξ k ε) N ε') ^ p) ^
        (1 / p) = a := by
    rw [ha]
    refine congrArg (· ^ (1 / p)) (congrArg avg (funext fun ε => congrArg avg
      (funext fun ε' => congrArg (· ^ p) (congrArg (schattenNorm (ENNReal.ofReal q)) ?_))))
    ext i j
    simp only [mart, square_filter_all, Matrix.of_apply, Finset.sum_apply, Matrix.sum_apply,
      Matrix.smul_apply]
    exact Finset.sum_congr rfl fun k _ => rfl
  have hlp : lpNormWith (fun X : Fin d → Fin d → ℝ =>
      schattenNorm (ENNReal.ofReal q) (Matrix.of X)) p (mart ξ N) = b := by
    rw [hb]
    unfold lpNormWith
    refine congrArg (· ^ (1 / p)) (congrArg avg (funext fun ε =>
      congrArg (· ^ p) (congrArg (schattenNorm (ENNReal.ofReal q)) ?_)))
    ext i j
    simp only [mart, Matrix.of_apply, Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply]
    exact Finset.sum_congr rfl fun k _ => rfl
  have h1' : ENNReal.ofReal a ≤ umdConstWith (Fin d → Fin d → ℝ)
      (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) p * ENNReal.ofReal b := by
    rw [← hdec, ← hlp]; exact h1
  have h2' : ENNReal.ofReal b ≤ umdConstWith (Fin d → Fin d → ℝ)
      (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) p * ENNReal.ofReal a := by
    rw [← hdec, ← hlp]; exact h2
  have ha0 : 0 ≤ a := Real.rpow_nonneg (rad_avg_nonneg fun ε => rad_avg_nonneg fun ε' =>
    Real.rpow_nonneg (schattenNorm_nonneg _ _) _) _
  have hb0 : 0 ≤ b := Real.rpow_nonneg (rad_avg_nonneg fun ε =>
    Real.rpow_nonneg (schattenNorm_nonneg _ _) _) _
  constructor
  · have := h1'.trans (by gcongr : _ ≤ ENNReal.ofReal u * ENNReal.ofReal b)
    rw [← ENNReal.ofReal_mul hu] at this
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hu hb0)).1 this
  · have := h2'.trans (by gcongr : _ ≤ ENNReal.ofReal u * ENNReal.ofReal a)
    rw [← ENNReal.ofReal_mul hu] at this
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hu ha0)).1 this

theorem square_symPart_transpose (A : Matrix (Fin d) (Fin d) ℝ) : (symPart A)ᵀ = symPart A := by
  simp only [symPart, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose,
    add_comm]

/-- **Equation (31)** (`eq:KKgen`): for `q ∈ [2, ∞)` and `p ∈ (1, ∞)`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≈_{p,q} (E ‖Σ ε_i x_i‖_{S_q}^p)^{1/p}` for normal `d × d` matrices
`x_i`, uniformly in `d` and `n`. From Propositions 6.3 and 6.4, which it combines
(`pisierXuKhintchine_holds`, `kahaneKhintchine_holds`; Proposition 6.4 with no bound on its
constants: the hypercontractive bound, `KahaneKhintchineHypercontractive`, is not used). Stated, like
`PisierXuKhintchine`, with `√‖Σ x_i x_iᵀ‖_{S_{q/2}}` in place of `‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`;
the two are equal, `‖B^{1/2}‖_{S_q}² = ‖B‖_{S_{q/2}}` for the positive semidefinite
`B = Σ x_i x_iᵀ` (`schattenNorm_sqrt_sq`, fact (1) applied to the square root `B^{1/2}`).

Proof (the paper's, "combining the two inequalities", TeX line 2322): the non-commutative
Khintchine inequality at the exponent `q` (Proposition 6.3, `PisierXuKhintchine`),
`‖𝔖‖ ≤ ‖Σ ε_i x_i‖_{L^q (S_q)} ≤ C √q ‖𝔖‖`, and the Kahane–Khintchine inequality between the
exponents `p` and `q` (Proposition 6.4, `KahaneKhintchine`, for the norm `‖·‖_{S_q}`, a norm by
`schattenNorm_add_le` and `schattenNorm_smul`), `k_{q,p}⁻¹ ‖·‖_{L^q} ≤ ‖·‖_{L^p} ≤ k_{p,q} ‖·‖_{L^q}`;
the constant is `max (k_{q,p}, k_{p,q} C √q)`. Stated here, before Proposition 6.2, whose proof
uses it. -/
theorem equation31 (p q : ℝ) (hp : 1 < p) (hq : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d n : ℕ) (x : Fin n → Matrix (Fin d) (Fin d) ℝ),
      (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
        c⁻¹ * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
            lpNormWith (schattenNorm (ENNReal.ofReal q)) p
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ∧
          lpNormWith (schattenNorm (ENNReal.ofReal q)) p
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
            c * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) := by
  obtain ⟨C, hC, hPX'⟩ := pisierXuKhintchine_holds
  obtain ⟨κ, hκ, hKK'⟩ := kahaneKhintchine_holds
  have hq1 : 1 < q := by linarith
  have hQ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le
  refine ⟨max (κ q p) (κ p q * C * √q), lt_max_of_lt_left (hκ q p), fun d n x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hPX' q hq d n x hx
  obtain ⟨k1, k2⟩ := hKK' p q hp hq1 (Matrix (Fin d) (Fin d) ℝ)
    (schattenNorm (ENNReal.ofReal q)) (fun x y => schattenNorm_add_le hQ1 x y)
    (fun c x => schattenNorm_smul hQ1 c x) n x
  have hs0 := Real.sqrt_nonneg (schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
  constructor
  · calc (max (κ q p) (κ p q * C * √q))⁻¹ *
          √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
        ≤ (κ q p)⁻¹ * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (hκ q p) (le_max_left _ _)) hs0
      _ ≤ (κ q p)⁻¹ * lpNormWith (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (hκ q p).le)
      _ ≤ _ := k1
  · calc lpNormWith (schattenNorm (ENNReal.ofReal q)) p
          (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i)
        ≤ κ p q * lpNormWith (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := k2
      _ ≤ κ p q * (C * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))) :=
          mul_le_mul_of_nonneg_left h2 (hκ p q).le
      _ = (κ p q * C * √q) * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hs0

/-- From `√a ≤ c √b` (`a, b ≥ 0`, `c ≥ 0`): `a ≤ c² b`. -/
theorem square_sq_le_of_sqrt_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : √a ≤ c * √b) : a ≤ c ^ 2 * b := by
  have := pow_le_pow_left₀ (Real.sqrt_nonneg a) h 2
  rwa [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb] at this

/-- **The bound of Proposition 6.2** (`p = 2`), with explicit constants: if `u` is a `UMD₂`
bound of `S_q^{d×d}` and `c` a constant of (31) at `p = 2`, then for every rank-one Rademacher
martingale `M` started at `0`, with `f = Sym M`, `g = Skew M`,
`‖g_N‖²_{L² (S_q)} ≤ (u c)³ d^{1/2 − 1/q} ‖f_N‖²_{L² (S_q)}`.

Proof (the paper's, TeX lines 2329–2415): decoupling `‖g_N‖ ≤ u ‖g̃_N‖`; (31) in the decoupled
signs `E_ε̃ ‖g̃_N‖² ≤ c² ‖𝔖_N g‖²`; the pointwise comparison
`‖𝔖_N g‖_{S_q}² ≤ ‖𝔖_N f‖_{S_q} ‖𝔖_N f‖_{S_2}` (`square_rankOne_comparison`); Cauchy–Schwarz;
`E ‖𝔖_N f‖_{S_q}² ≤ c² ‖f̃_N‖² ≤ c² u² ‖f_N‖²` ((31) and decoupling); and
`E ‖𝔖_N f‖²_{S_2} = E ‖f_N‖²_{S_2} ≤ d^{1 − 2/q} ‖f_N‖²_{L² (S_q)}` (orthogonality of martingale
increments, `square_korn_avg_frob_mart`, and fact (2)). -/
theorem square_skew_le_sym_two {q : ℝ} (hq : 2 < q) {u c : ℝ}
    (hu : 0 ≤ u) (hc : 0 < c)
    (hU : umdConstWith (Fin d → Fin d → ℝ)
      (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) 2 ≤ ENNReal.ofReal u)
    (h31 : ∀ (n : ℕ) (x : Fin n → Matrix (Fin d) (Fin d) ℝ),
      (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
        c⁻¹ * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
            lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ∧
          lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
            c * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)))
    {N : ℕ} (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ)
    (hA : IsRankOneIncrements A) :
    (avg fun ε => schattenNorm (ENNReal.ofReal q) (skewPart (radMart 0 A N ε)) ^ 2) ≤
      (u * c) ^ 3 * (d : ℝ) ^ (1 / 2 - 1 / q) *
        avg fun ε => schattenNorm (ENNReal.ofReal q) (symPart (radMart 0 A N ε)) ^ 2 := by
  set Q := ENNReal.ofReal q with hQdef
  set r := ENNReal.ofReal (q / 2) with hrdef
  have hq1 : 1 < q := by linarith
  have hQ1 : (1 : ℝ≥0∞) ≤ Q := by
    rw [hQdef, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le
  have hr1 : (1 : ℝ≥0∞) ≤ r := by
    rw [hrdef, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hQ2 : (2 : ℝ≥0∞) ≤ Q := by
    rw [hQdef, ← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal hq.le
  set S : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ := fun k ε => symPart (A k ε)
    with hSdef
  set K : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ := fun k ε => skewPart (A k ε)
    with hKdef
  have hSp : IsPredictable S := fun k ε ε' h => by simp only [hSdef, hA.1 k ε ε' h]
  have hKp : IsPredictable K := fun k ε ε' h => by simp only [hKdef, hA.1 k ε ε' h]
  have hf : ∀ ε, symPart (radMart 0 A N ε) = mart S N ε := fun ε => by
    rw [radMart, zero_add, square_symPart_mart]
  have hg : ∀ ε, skewPart (radMart 0 A N ε) = mart K N ε := fun ε => by
    rw [radMart, zero_add, square_skewPart_mart]
  simp_rw [hf, hg]
  set LS := avg fun ε => schattenNorm Q (mart S N ε) ^ 2 with hLS
  set LK := avg fun ε => schattenNorm Q (mart K N ε) ^ 2 with hLK
  set IS : (Fin N → Bool) → ℝ := fun ε => avg fun ε' =>
    schattenNorm Q (∑ k, coin (ε' k) • S k ε) ^ 2 with hIS
  set IK : (Fin N → Bool) → ℝ := fun ε => avg fun ε' =>
    schattenNorm Q (∑ k, coin (ε' k) • K k ε) ^ 2 with hIK
  set X : (Fin N → Bool) → ℝ := fun ε => schattenNorm r (∑ k, S k ε * (S k ε)ᵀ) with hX
  set Z : (Fin N → Bool) → ℝ := fun ε => schattenNorm r (∑ k, K k ε * (K k ε)ᵀ) with hZ
  set W : (Fin N → Bool) → ℝ := fun ε => (∑ k, S k ε * (S k ε)ᵀ).trace with hW
  have hLS0 : 0 ≤ LS := rad_avg_nonneg fun ε => sq_nonneg _
  have hIS0 : ∀ ε, 0 ≤ IS ε := fun ε => rad_avg_nonneg fun ε' => sq_nonneg _
  have hIK0 : ∀ ε, 0 ≤ IK ε := fun ε => rad_avg_nonneg fun ε' => sq_nonneg _
  have hX0 : ∀ ε, 0 ≤ X ε := fun ε => schattenNorm_nonneg _ _
  have hZ0 : ∀ ε, 0 ≤ Z ε := fun ε => schattenNorm_nonneg _ _
  have hpsd : ∀ P : Matrix (Fin d) (Fin d) ℝ, (P * Pᵀ).PosSemidef := fun P => by
    simpa [square_conjTranspose_eq] using Matrix.posSemidef_self_mul_conjTranspose P
  have hW0 : ∀ ε, 0 ≤ W ε := fun ε =>
    (Matrix.posSemidef_sum _ fun k _ => hpsd (S k ε)).trace_nonneg
  -- decoupling
  have hdS := (square_decoupling hq1 hu one_lt_two hU S hSp).1
  have hdK := (square_decoupling hq1 hu one_lt_two hU K hKp).2
  rw [square_lpNormWith_two] at hdS hdK
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hdS hdK
  have hdS' : avg IS ≤ u ^ 2 * LS :=
    square_sq_le_of_sqrt_le (rad_avg_nonneg hIS0) hLS0 hdS
  have hdK' : LK ≤ u ^ 2 * avg IK :=
    square_sq_le_of_sqrt_le (rad_avg_nonneg fun ε => sq_nonneg _)
      (rad_avg_nonneg hIK0) hdK
  -- (31) in the decoupled signs
  have h31K : ∀ ε, IK ε ≤ c ^ 2 * Z ε := fun ε => by
    have h := (h31 N (fun k => K k ε) fun i => by
      simp only [hKdef, square_skewPart_transpose, Matrix.mul_neg, Matrix.neg_mul]).2
    rw [square_lpNormWith_two] at h
    exact square_sq_le_of_sqrt_le (hIK0 ε) (hZ0 ε) h
  have h31S : ∀ ε, X ε ≤ c ^ 2 * IS ε := fun ε => by
    have h := (h31 N (fun k => S k ε) fun i => by
      simp only [hSdef, square_symPart_transpose]).1
    rw [square_lpNormWith_two] at h
    have h' : √(X ε) ≤ c * √(IS ε) :=
      calc √(X ε) = c * (c⁻¹ * √(X ε)) := by field_simp
        _ ≤ c * √(IS ε) := mul_le_mul_of_nonneg_left h hc.le
    exact square_sq_le_of_sqrt_le (hX0 ε) (hIS0 ε) h'
  -- the pointwise comparison and Cauchy–Schwarz
  have hpt : ∀ ε, Z ε ≤ √(X ε) * √(W ε) := fun ε =>
    square_rankOne_comparison hr1 (fun k => A k ε) fun k => hA.2 k ε
  have hcs : avg Z ≤ √(avg X) * √(avg W) :=
    (rad_avg_mono hpt).trans (square_avg_sqrt_mul_le hX0 hW0)
  -- `E ‖𝔖_N f‖_{S_q}² ≤ c² u² ‖f_N‖²`
  have hXb : √(avg X) ≤ c * u * √LS := by
    have : avg X ≤ (c * u) ^ 2 * LS := by
      calc avg X ≤ avg fun ε => c ^ 2 * IS ε := rad_avg_mono h31S
        _ = c ^ 2 * avg IS := rad_avg_mul_left _ _
        _ ≤ c ^ 2 * (u ^ 2 * LS) := mul_le_mul_of_nonneg_left hdS' (sq_nonneg _)
        _ = (c * u) ^ 2 * LS := by ring
    calc √(avg X) ≤ √((c * u) ^ 2 * LS) := Real.sqrt_le_sqrt this
      _ = c * u * √LS := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hc.le hu)]
  -- `E ‖𝔖_N f‖²_{S_2} = E ‖f_N‖²_{S_2} ≤ d^{1 − 2/q} ‖f_N‖²_{L² (S_q)}`
  set D := (d : ℝ) ^ (1 / 2 - 1 / q) with hD
  have hD0 : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hWb : √(avg W) ≤ D * √LS := by
    have hWf : avg W = avg fun ε => squareFrob (mart S N ε) (mart S N ε) := by
      rw [square_korn_avg_frob_mart S hSp]
      congr 1; funext ε
      simp only [hW, Matrix.trace_sum, squareFrob]
      exact Finset.sum_congr rfl fun k _ => Matrix.trace_mul_comm _ _
    have h2q : ∀ M : Matrix (Fin d) (Fin d) ℝ, squareFrob M M ≤ D ^ 2 * schattenNorm Q M ^ 2 := by
      intro M
      have h := schattenNorm_le_rpow_mul (by norm_num : (1 : ℝ≥0∞) ≤ 2) hQ2 M
      rw [min_self, hQdef, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofNat] at h
      have h' := pow_le_pow_left₀ (schattenNorm_nonneg _ _) h 2
      rw [square_schattenNorm_two_sq, mul_pow] at h'
      exact h'
    have : avg W ≤ D ^ 2 * LS := by
      rw [hWf, hLS, ← rad_avg_mul_left]
      exact rad_avg_mono fun ε => h2q _
    calc √(avg W) ≤ √(D ^ 2 * LS) := Real.sqrt_le_sqrt this
      _ = D * √LS := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hD0]
  calc LK ≤ u ^ 2 * avg IK := hdK'
    _ ≤ u ^ 2 * (c ^ 2 * avg Z) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [← rad_avg_mul_left]; exact rad_avg_mono h31K
    _ ≤ u ^ 2 * (c ^ 2 * ((c * u * √LS) * (D * √LS))) := by
        gcongr
        exact hcs.trans (mul_le_mul hXb hWb (Real.sqrt_nonneg _)
          (mul_nonneg (mul_nonneg hc.le hu) (Real.sqrt_nonneg _)))
    _ = (u * c) ^ 3 * D * (√LS * √LS) := by ring
    _ = (u * c) ^ 3 * D * LS := by rw [Real.mul_self_sqrt hLS0]

/-- **Proposition 6.2** (`prop:qgenp2`): for `q ∈ (2, ∞)` there is `C_q` such that for every
`d ≥ 2`, `C^{rc} (S_q^{d×d}, 2) ≤ C_q d^{1/4 − 1/(2q)}`. The proof uses Proposition 2.7 (2)
(Randrianantoanina), Proposition 2.8 (decoupling), Proposition 6.3 (non-commutative Khintchine)
and Proposition 6.4 (Kahane–Khintchine), all proved (`Morrey/Cassese/Hypotheses.lean`).

Proof (the paper's, TeX lines 2329–2415): with `UMD₂ (S_q^{d×d}) ≤ u = C_R (q* − 1)`
(Proposition 2.7 (2)) and the constant `c` of (31) at `p = 2` (`equation31`), every rank-one
Rademacher martingale started at `0` has
`‖Skew M_N‖²_{L² (S_q)} ≤ (u c)³ d^{1/2 − 1/q} ‖Sym M_N‖²_{L² (S_q)}` (`square_skew_le_sym_two`:
decoupling, (31), the pointwise rank-one comparison `square_rankOne_comparison`, Cauchy–Schwarz,
orthogonality of the increments and fact (2)); so for `C = (u c)^{3/2} d^{1/4 − 1/(2q)}`,
`E f_{2,q,C} (M_N) ≥ 0 = f_{2,q,C} (0)`, and `f_{2,q,C}` is rank-one convex at `0` by
Proposition 2.5. The paper's proof stops at the martingale bound (TeX line 2415) and leaves this
last step implicit: `C^{rc}` is defined through rank-one convexity at `0`, which Proposition 2.5
(as the paper says at TeX lines 708–712 and 905–912) characterizes by the rank-one Rademacher
martingales started at `0`.
Proposition 6.4 is used with no bound on its constants (the hypercontractive bound,
`KahaneKhintchineHypercontractive`, is not used here). -/
theorem proposition6_2 (q : ℝ) (hq : 2 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      rcThreshold (kornF d 2 (ENNReal.ofReal q)) ≤
        ENNReal.ofReal (C * (d : ℝ) ^ (1 / 4 - 1 / (2 * q))) := by
  obtain ⟨CR, hCR, hR'⟩ := randrianantoaninaSchattenUMD_holds
  have hq1 : 1 < q := by linarith
  obtain ⟨c, hc, h31⟩ := equation31 2 q one_lt_two hq.le
  set u := CR * (pStar q - 1) with hudef
  have hu : 0 < u := mul_pos hCR (by have : q ≤ pStar q := le_max_left _ _; linarith)
  refine ⟨(u * c) ^ (3 / 2 : ℝ), by positivity, fun d _ => ?_⟩
  have hQ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le
  set C := (u * c) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hC2 : C ^ 2 = (u * c) ^ 3 * (d : ℝ) ^ (1 / 2 - 1 / q) := by
    have e1 : ((u * c) ^ (3 / 2 : ℝ)) ^ 2 = (u * c) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e2 : ((d : ℝ) ^ (1 / 4 - 1 / (2 * q))) ^ 2 = (d : ℝ) ^ (1 / 2 - 1 / q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1; push_cast; ring
    rw [hCdef, mul_pow, e1, e2]
  refine iInf₂_le C ⟨hC0, (proposition2_5 (square_continuous_kornF (by norm_num) hQ1 C)).2
    fun N A hA => ?_⟩
  rw [square_kornF_zero (by norm_num) hQ1]
  have hb := square_skew_le_sym_two hq hu.le hc (hR' q hq1 d) (h31 d) A hA
  have hval : (avg fun ε => kornF d 2 (ENNReal.ofReal q) C (radMart 0 A N ε)) =
      C ^ 2 * (avg fun ε => schattenNorm (ENNReal.ofReal q) (symPart (radMart 0 A N ε)) ^ 2) -
        avg fun ε => schattenNorm (ENNReal.ofReal q) (skewPart (radMart 0 A N ε)) ^ 2 := by
    simp only [kornF, Real.rpow_two]
    rw [rad_avg_sub, rad_avg_mul_left]
  rw [hval, sub_nonneg, hC2]
  exact hb

/-- Monotonicity of the `L^p` norms on the signs (Jensen's inequality, power means):
`‖X‖_{L^p} ≤ ‖X‖_{L^q}` for `0 < p ≤ q`. -/
theorem square_lpNormWith_mono {N : ℕ} {E : Type*} (nrm : E → ℝ) (hn : ∀ x, 0 ≤ nrm x)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (X : (Fin N → Bool) → E) :
    lpNormWith nrm p X ≤ lpNormWith nrm q X := by
  have hq : 0 < q := hp.trans_le hpq
  have havg : ∀ g : (Fin N → Bool) → ℝ, avg g = ∑ ε, (1 / 2 ^ N : ℝ) * g ε := fun g => by
    rw [avg, ← Finset.mul_sum, div_eq_inv_mul, one_div]
  have hw : ∑ _ε : Fin N → Bool, (1 / 2 ^ N : ℝ) = 1 := by
    simp
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun _ => (1 / 2 ^ N : ℝ))
    (fun ε => nrm (X ε) ^ p) (fun _ _ => by positivity) hw
    (fun ε _ => Real.rpow_nonneg (hn _) _) ((one_le_div hp).2 hpq)
  have hpow : ∀ ε, (nrm (X ε) ^ p) ^ (q / p) = nrm (X ε) ^ q := fun ε => by
    rw [← Real.rpow_mul (hn _), mul_div_cancel₀ _ hp.ne']
  simp only [hpow, ← havg] at hJ
  have h0 : 0 ≤ avg fun ε => nrm (X ε) ^ p :=
    rad_avg_nonneg fun ε => Real.rpow_nonneg (hn _) _
  unfold lpNormWith
  calc (avg fun ε => nrm (X ε) ^ p) ^ (1 / p) =
        ((avg fun ε => nrm (X ε) ^ p) ^ (q / p)) ^ (1 / q) := by
        rw [← Real.rpow_mul h0]; congr 1; field_simp
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hJ (by positivity)

/-- `L²` norms are monotone in a pointwise bound of the norms. -/
theorem square_lpNormWith_two_le {N : ℕ} {E F : Type*} {n₁ : E → ℝ} {n₂ : F → ℝ}
    {X : (Fin N → Bool) → E} {Y : (Fin N → Bool) → F} {a : ℝ} (ha : 0 ≤ a)
    (h0 : ∀ ε, 0 ≤ n₁ (X ε)) (h : ∀ ε, n₁ (X ε) ≤ a * n₂ (Y ε)) :
    lpNormWith n₁ 2 X ≤ a * lpNormWith n₂ 2 Y := by
  rw [square_lpNormWith_two, square_lpNormWith_two]
  calc √(avg fun ε => n₁ (X ε) ^ 2) ≤ √(avg fun ε => a ^ 2 * n₂ (Y ε) ^ 2) :=
        Real.sqrt_le_sqrt (rad_avg_mono fun ε => by
          rw [← mul_pow]; exact pow_le_pow_left₀ (h0 ε) (h ε) 2)
    _ = a * √(avg fun ε => n₂ (Y ε) ^ 2) := by
        rw [rad_avg_mul_left, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- (31) at `p = 2` with a constant `c₀ √q` (the constant tracked in Remark 6.3): the
non-commutative Khintchine inequality (Proposition 6.3) at the exponent `q`, the hypercontractive
Kahane–Khintchine bound `‖·‖_{L^q} ≤ √(q − 1) ‖·‖_{L²}` (`kahaneKhintchineHypercontractive_holds`) for
the lower bound, and `‖·‖_{L²} ≤ ‖·‖_{L^q}` (monotonicity of `L^p` norms) for the upper bound. -/
theorem square_eq31_two :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ q : ℝ, 2 ≤ q → ∀ (d n : ℕ) (x : Fin n → Matrix (Fin d) (Fin d) ℝ),
      (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
        (c₀ * √q)⁻¹ * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
            lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ∧
          lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
            (c₀ * √q) * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) := by
  obtain ⟨C, hC, hPX'⟩ := pisierXuKhintchine_holds
  refine ⟨max 1 C, lt_max_of_lt_left one_pos, fun q hq d n x hx => ?_⟩
  have hq1 : 1 < q := by linarith
  have hQ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le
  obtain ⟨h1, h2⟩ := hPX' q hq d n x hx
  have k1 := kahaneKhintchineHypercontractive_holds 2 q one_lt_two hq (Matrix (Fin d) (Fin d) ℝ)
    (schattenNorm (ENNReal.ofReal q)) (fun x y => schattenNorm_add_le hQ1 x y)
    (fun c x => schattenNorm_smul hQ1 c x) n x
  set s := √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
  set L2 := lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
    (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i)
  have hL2 : 0 ≤ L2 :=
    Real.rpow_nonneg (rad_avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _) _
  have hsq : 0 < √q := Real.sqrt_pos.2 (by linarith)
  have hc0 : 0 < max 1 C * √q := mul_pos (lt_max_of_lt_left one_pos) hsq
  -- `k_{q,2} ≤ √(q − 1) ≤ c₀ √q`
  have hκ2 : √((q - 1) / (2 - 1)) ≤ max 1 C * √q := by
    calc √((q - 1) / (2 - 1)) ≤ √q := Real.sqrt_le_sqrt (by norm_num)
      _ = 1 * √q := (one_mul _).symm
      _ ≤ max 1 C * √q := mul_le_mul_of_nonneg_right (le_max_left _ _) hsq.le
  constructor
  · rw [inv_mul_le_iff₀ hc0]
    calc s ≤ lpNormWith (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := h1
      _ ≤ √((q - 1) / (2 - 1)) * L2 := k1
      _ ≤ max 1 C * √q * L2 := mul_le_mul_of_nonneg_right hκ2 hL2
  · calc L2 ≤ lpNormWith (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) :=
          square_lpNormWith_mono _ (schattenNorm_nonneg _) two_pos hq _
      _ ≤ C * √q * s := h2
      _ ≤ max 1 C * √q * s := by gcongr; exact le_max_right _ _

/-- **Remark 6.3, first bound, in `S_q`**: there is an absolute `C` with
`‖g_N‖_{L² (S_q)} ≤ C q³ d^{1/4 − 1/(2q)} ‖f_N‖_{L² (S_q)}` for every `q > 2`, `d` and rank-one
Rademacher martingale `M` (`f = Sym M`, `g = Skew M`): the bound of Proposition 6.2
(`square_skew_le_sym_two`) with `UMD₂ (S_q) ≤ C_R (q* − 1) ≤ C_R q` and the constant `c₀ √q` of
(31) (`square_eq31_two`), since `(C_R q · c₀ √q)^{3/2} ≲ q³`. -/
theorem square_skew_le_sym_two_q :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 2 < q → ∀ (d N : ℕ)
      (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ), IsRankOneIncrements A →
        lpNormWith (schattenNorm (ENNReal.ofReal q)) 2 (fun ε => skewPart (radMart 0 A N ε)) ≤
          C * q ^ 3 * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) *
            lpNormWith (schattenNorm (ENNReal.ofReal q)) 2 (fun ε => symPart (radMart 0 A N ε)) := by
  obtain ⟨CR, hCR, hR'⟩ := randrianantoaninaSchattenUMD_holds
  obtain ⟨c₀, hc₀, h31⟩ := square_eq31_two
  refine ⟨(CR * c₀) ^ 2 + 1, by positivity, fun q hq d N A hA => ?_⟩
  have hq1 : 1 < q := by linarith
  have hqs : 0 < √q := Real.sqrt_pos.2 (by linarith)
  have hpq : pStar q = q := by
    refine max_eq_left ?_
    rw [div_le_iff₀ (by linarith)]; nlinarith
  set u := CR * (pStar q - 1) with hudef
  have hu : 0 ≤ u := mul_nonneg hCR.le (by rw [hpq]; linarith)
  set c := c₀ * √q with hcdef
  have hc : 0 < c := mul_pos hc₀ hqs
  have hb := square_skew_le_sym_two hq hu hc (hR' q hq1 d) (fun n x hx => h31 q hq.le d n x hx)
    A hA
  set D := (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) with hD
  have hD0 : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hD2 : D ^ 2 = (d : ℝ) ^ (1 / 2 - 1 / q) := by
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1; push_cast; ring
  -- `(u c)³ ≤ (C_R c₀)³ q⁶ ≤ ((C_R c₀)² + 1)² q⁶`
  have huc : u * c ≤ CR * c₀ * q ^ 2 := by
    have h1 : u ≤ CR * q := by rw [hudef, hpq]; nlinarith
    have h2 : √q ≤ q := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    calc u * c = u * (c₀ * √q) := rfl
      _ ≤ (CR * q) * (c₀ * q) := by gcongr
      _ = CR * c₀ * q ^ 2 := by ring
  have hx : CR * c₀ ≤ (CR * c₀) ^ 2 + 1 := by nlinarith [sq_nonneg (CR * c₀ - 1)]
  have hk : (u * c) ^ 3 ≤ ((CR * c₀) ^ 2 + 1) ^ 2 * (q ^ 3) ^ 2 := by
    have h0 : 0 ≤ u * c := mul_nonneg hu hc.le
    have hx0 : 0 ≤ CR * c₀ := by positivity
    calc (u * c) ^ 3 ≤ (CR * c₀ * q ^ 2) ^ 3 := pow_le_pow_left₀ h0 huc 3
      _ = (CR * c₀) ^ 3 * (q ^ 3) ^ 2 := by ring
      _ ≤ ((CR * c₀) ^ 2 + 1) ^ 2 * (q ^ 3) ^ 2 := by
          gcongr
          nlinarith [sq_nonneg (CR * c₀), sq_nonneg (CR * c₀ - 1), mul_nonneg hx0 (sq_nonneg (CR * c₀ - 1))]
  rw [square_lpNormWith_two, square_lpNormWith_two]
  set LS := avg fun ε => schattenNorm (ENNReal.ofReal q) (symPart (radMart 0 A N ε)) ^ 2
  have hLS0 : 0 ≤ LS := rad_avg_nonneg fun ε => sq_nonneg _
  have hfin : (avg fun ε => schattenNorm (ENNReal.ofReal q) (skewPart (radMart 0 A N ε)) ^ 2) ≤
      (((CR * c₀) ^ 2 + 1) * q ^ 3 * D) ^ 2 * LS := by
    refine hb.trans ?_
    rw [← hD2]
    have : (u * c) ^ 3 * D ^ 2 ≤ (((CR * c₀) ^ 2 + 1) * q ^ 3 * D) ^ 2 := by
      have e : (((CR * c₀) ^ 2 + 1) * q ^ 3 * D) ^ 2 =
          ((CR * c₀) ^ 2 + 1) ^ 2 * (q ^ 3) ^ 2 * D ^ 2 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right this hLS0
  calc √(avg fun ε => schattenNorm (ENNReal.ofReal q) (skewPart (radMart 0 A N ε)) ^ 2)
      ≤ √((((CR * c₀) ^ 2 + 1) * q ^ 3 * D) ^ 2 * LS) := Real.sqrt_le_sqrt hfin
    _ = ((CR * c₀) ^ 2 + 1) * q ^ 3 * D * √LS := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- **Remark 6.3** (`rmk:interpolation`): tracking the constants in the proof of Proposition 6.2,
for every rank-one Rademacher martingale `M` in `ℝ^{d×d}` started at `0`, with `f = Sym M` and
`g = Skew M`, `‖g_N‖_{L² (S_q)} ≲ d^{1/4} q³ d^{−1/(2q)} ‖f_N‖_{L² (S_q)}` and
`‖g_N‖_{L² (S_∞)} ≲ d^{1/4} q³ d^{1/(2q)} ‖f_N‖_{L² (S_∞)}` for `q ∈ (2, ∞)`, with absolute
constants; with `q ≈ log d`, `C^{rc} (S_∞^{d×d}, 2) ≲ d^{1/4} log³ d`. The proof uses
Proposition 2.7 (2) (Randrianantoanina), Proposition 2.8 (decoupling), Proposition 6.3
(non-commutative Khintchine) and the hypercontractive Kahane–Khintchine bound
`k_{q,p} ≤ √((q − 1)/(p − 1))` (`KahaneKhintchineHypercontractive`, Borell's), which gives the
constants of Proposition 6.4 that the tracking of the constants needs (inventory E27: the paper
names no source for it), all proved (`Morrey/Cassese/Hypotheses.lean`); it uses only that bound,
not `KahaneKhintchine` itself.

Proof (the paper's: "tracking the constants in the proof", TeX lines 2425–2437): the bound of
the proof of Proposition 6.2 (`square_skew_le_sym_two`) with `UMD₂ (S_q) ≤ C_R (q* − 1) ≤ C_R q`
and a constant `c₀ √q` of (31) at `p = 2` (`square_eq31_two`: Proposition 6.3, the hypercontractive
Kahane–Khintchine bound `k_{q,2} ≤ √(q − 1)`, and `‖·‖_{L²} ≤ ‖·‖_{L^q}`),
so that `(u c)^{3/2} ≲ q^{9/4} ≤ q³` (`square_skew_le_sym_two_q`); then
`d^{−1/q} ‖·‖_{S_q} ≤ ‖·‖_{S_∞} ≤ ‖·‖_{S_q}` (fact (2)); and, for the threshold, the paper's
`q ≈ log d` taken as `q = log d + 2` (so that `q > 2` for every `d ≥ 2`), where
`q³ d^{1/(2q)} ≤ 250 log³ d`, with Proposition 2.5. The constants of (31) and of
`UMD₂ (S_q)` are tracked directly (`square_eq31_two`, `square_skew_le_sym_two_q`) rather than
through the statements of `equation31` and `proposition6_2`, whose constants are existential. -/
theorem remark6_3 :
    (∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ), 2 < q → ∀ (d : ℕ), 2 ≤ d → ∀ (N : ℕ)
      (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ), IsRankOneIncrements A →
        lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
            (fun ε => skewPart (radMart 0 A N ε)) ≤
          C * (d : ℝ) ^ (1 / 4 : ℝ) * q ^ 3 * (d : ℝ) ^ (-(1 / (2 * q))) *
            lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
              (fun ε => symPart (radMart 0 A N ε)) ∧
        lpNormWith (schattenNorm ⊤) 2 (fun ε => skewPart (radMart 0 A N ε)) ≤
          C * (d : ℝ) ^ (1 / 4 : ℝ) * q ^ 3 * (d : ℝ) ^ (1 / (2 * q)) *
            lpNormWith (schattenNorm ⊤) 2 (fun ε => symPart (radMart 0 A N ε))) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      rcThreshold (kornF d 2 ⊤) ≤
        ENNReal.ofReal (C * (d : ℝ) ^ (1 / 4 : ℝ) * Real.log d ^ 3) := by
  obtain ⟨C, hC, hb⟩ := square_skew_le_sym_two_q
  have hQ1 : ∀ q : ℝ, 2 < q → (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := fun q hq => by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the two bounds of the remark
  have part1 : ∀ (q : ℝ), 2 < q → ∀ (d : ℕ), 2 ≤ d → ∀ (N : ℕ)
      (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ), IsRankOneIncrements A →
        lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
            (fun ε => skewPart (radMart 0 A N ε)) ≤
          C * (d : ℝ) ^ (1 / 4 : ℝ) * q ^ 3 * (d : ℝ) ^ (-(1 / (2 * q))) *
            lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
              (fun ε => symPart (radMart 0 A N ε)) ∧
        lpNormWith (schattenNorm ⊤) 2 (fun ε => skewPart (radMart 0 A N ε)) ≤
          C * (d : ℝ) ^ (1 / 4 : ℝ) * q ^ 3 * (d : ℝ) ^ (1 / (2 * q)) *
            lpNormWith (schattenNorm ⊤) 2 (fun ε => symPart (radMart 0 A N ε)) := by
    intro q hq d hd N A hA
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hq0 : 0 < q := by linarith
    have h1 := hb q hq d N A hA
    have hsplit : (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) = (d : ℝ) ^ (1 / 4 : ℝ) * (d : ℝ) ^ (-(1 / (2 * q))) := by
      rw [← Real.rpow_add hd0, ← sub_eq_add_neg]
    have hf0 : 0 ≤ lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
        (fun ε => symPart (radMart 0 A N ε)) := by
      rw [square_lpNormWith_two]; exact Real.sqrt_nonneg _
    refine ⟨h1.trans (le_of_eq (by rw [hsplit]; ring)), ?_⟩
    -- `‖·‖_{S_∞} ≤ ‖·‖_{S_q} ≤ d^{1/q} ‖·‖_{S_∞}`
    have hgq : lpNormWith (schattenNorm ⊤) 2 (fun ε => skewPart (radMart 0 A N ε)) ≤
        1 * lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
          (fun ε => skewPart (radMart 0 A N ε)) :=
      square_lpNormWith_two_le zero_le_one (fun ε => schattenNorm_nonneg _ _) fun ε => by
        rw [one_mul]; exact schattenNorm_anti (hQ1 q hq) le_top _
    have hfq : lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
        (fun ε => symPart (radMart 0 A N ε)) ≤ (d : ℝ) ^ (1 / q) *
          lpNormWith (schattenNorm ⊤) 2 (fun ε => symPart (radMart 0 A N ε)) :=
      square_lpNormWith_two_le (Real.rpow_nonneg hd0.le _) (fun ε => schattenNorm_nonneg _ _)
        fun ε => by
          have h := schattenNorm_le_rpow_mul (hQ1 q hq) le_top (symPart (radMart 0 A N ε))
          rwa [min_self, ENNReal.toReal_ofReal hq0.le, ENNReal.toReal_top, div_zero,
            sub_zero] at h
    have hK0 : 0 ≤ C * q ^ 3 * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) := by positivity
    calc lpNormWith (schattenNorm ⊤) 2 (fun ε => skewPart (radMart 0 A N ε))
        ≤ 1 * lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
          (fun ε => skewPart (radMart 0 A N ε)) := hgq
      _ ≤ C * q ^ 3 * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) *
          lpNormWith (schattenNorm (ENNReal.ofReal q)) 2
            (fun ε => symPart (radMart 0 A N ε)) := by rw [one_mul]; exact h1
      _ ≤ C * q ^ 3 * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) * ((d : ℝ) ^ (1 / q) *
          lpNormWith (schattenNorm ⊤) 2 (fun ε => symPart (radMart 0 A N ε))) :=
          mul_le_mul_of_nonneg_left hfq hK0
      _ = C * (d : ℝ) ^ (1 / 4 : ℝ) * q ^ 3 * (d : ℝ) ^ (1 / (2 * q)) *
            lpNormWith (schattenNorm ⊤) 2 (fun ε => symPart (radMart 0 A N ε)) := by
          have : (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) * (d : ℝ) ^ (1 / q) =
              (d : ℝ) ^ (1 / 4 : ℝ) * (d : ℝ) ^ (1 / (2 * q)) := by
            rw [← Real.rpow_add hd0, ← Real.rpow_add hd0]; congr 1; field_simp; ring
          calc C * q ^ 3 * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) * ((d : ℝ) ^ (1 / q) *
                lpNormWith (schattenNorm ⊤) 2 (fun ε => symPart (radMart 0 A N ε))) =
              C * q ^ 3 * ((d : ℝ) ^ (1 / 4 - 1 / (2 * q)) * (d : ℝ) ^ (1 / q)) *
                lpNormWith (schattenNorm ⊤) 2 (fun ε => symPart (radMart 0 A N ε)) := by ring
            _ = _ := by rw [this]; ring
  refine ⟨⟨C, hC, part1⟩, 250 * C, by positivity, fun d hd => ?_⟩
  -- `q = log d + 2`: `q³ d^{1/(2q)} ≤ 250 log³ d`
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogd : Real.log 2 ≤ Real.log d :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hd)
  have hl : (0.69 : ℝ) < Real.log d := by linarith
  set q := Real.log d + 2 with hqdef
  have hq : 2 < q := by linarith
  have hq0 : 0 < q := by linarith
  have hq5 : q ≤ 5 * Real.log d := by linarith
  have hq3 : q ^ 3 ≤ 125 * Real.log d ^ 3 := by
    calc q ^ 3 ≤ (5 * Real.log d) ^ 3 := pow_le_pow_left₀ hq0.le hq5 3
      _ = 125 * Real.log d ^ 3 := by ring
  have hexp : (d : ℝ) ^ (1 / (2 * q)) ≤ 2 := by
    rw [Real.rpow_def_of_pos hd0]
    have h1 : Real.log d * (1 / (2 * q)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
    have h2 : Real.exp (1 / 2) < 2 := by
      have he := Real.exp_one_lt_d9
      have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_pos (1 / 2)]
    exact (Real.exp_le_exp.2 h1).trans h2.le
  set Crc := 250 * C * (d : ℝ) ^ (1 / 4 : ℝ) * Real.log d ^ 3 with hCrc
  have hCrc0 : 0 ≤ Crc := by
    have : 0 ≤ Real.log d := by linarith
    positivity
  have hC' : C * (d : ℝ) ^ (1 / 4 : ℝ) * q ^ 3 * (d : ℝ) ^ (1 / (2 * q)) ≤ Crc := by
    have hd4 : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hd0.le _
    have hp : q ^ 3 * (d : ℝ) ^ (1 / (2 * q)) ≤ 250 * Real.log d ^ 3 := by
      calc q ^ 3 * (d : ℝ) ^ (1 / (2 * q)) ≤ (125 * Real.log d ^ 3) * 2 :=
            mul_le_mul hq3 hexp (Real.rpow_nonneg hd0.le _) (by positivity)
        _ = 250 * Real.log d ^ 3 := by ring
    calc C * (d : ℝ) ^ (1 / 4 : ℝ) * q ^ 3 * (d : ℝ) ^ (1 / (2 * q)) =
          C * (d : ℝ) ^ (1 / 4 : ℝ) * (q ^ 3 * (d : ℝ) ^ (1 / (2 * q))) := by ring
      _ ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) * (250 * Real.log d ^ 3) := by gcongr
      _ = Crc := by rw [hCrc]; ring
  refine iInf₂_le Crc ⟨hCrc0, (proposition2_5 (square_continuous_kornF (by norm_num) le_top Crc)).2
    fun N A hA => ?_⟩
  rw [square_kornF_zero (by norm_num) le_top]
  have h2 := (part1 q hq d hd N A hA).2
  rw [square_lpNormWith_two, square_lpNormWith_two] at h2
  have hval : (avg fun ε => kornF d 2 ⊤ Crc (radMart 0 A N ε)) =
      Crc ^ 2 * (avg fun ε => schattenNorm ⊤ (symPart (radMart 0 A N ε)) ^ 2) -
        avg fun ε => schattenNorm ⊤ (skewPart (radMart 0 A N ε)) ^ 2 := by
    simp only [kornF, Real.rpow_two]
    rw [rad_avg_sub, rad_avg_mul_left]
  rw [hval, sub_nonneg]
  have hS0 : 0 ≤ avg fun ε => schattenNorm ⊤ (symPart (radMart 0 A N ε)) ^ 2 :=
    rad_avg_nonneg fun ε => sq_nonneg _
  have h3 := square_sq_le_of_sqrt_le (rad_avg_nonneg fun ε => sq_nonneg _) hS0 h2
  have hC'0 : 0 ≤ C * (d : ℝ) ^ (1 / 4 : ℝ) * q ^ 3 * (d : ℝ) ^ (1 / (2 * q)) := by positivity
  exact h3.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC'0 hC' 2) hS0)

/-- `A ≤ c^p B` gives `A^{1/p} ≤ c B^{1/p}` (`A, B, c ≥ 0`, `p > 0`). -/
theorem square_rpow_one_div_le {A B c p : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c) (hp : 0 < p)
    (h : A ≤ c ^ p * B) : A ^ (1 / p) ≤ c * B ^ (1 / p) := by
  calc A ^ (1 / p) ≤ (c ^ p * B) ^ (1 / p) := Real.rpow_le_rpow hA h (by positivity)
    _ = c * B ^ (1 / p) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hc _) hB, ← Real.rpow_mul hc,
          mul_one_div_cancel hp.ne', Real.rpow_one]

/-- `A^{1/p} ≤ c B` gives `A ≤ c^p B^p` (`A, B, c ≥ 0`, `p > 0`). -/
theorem square_le_rpow_of_rpow_one_div_le {A B c p : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hp : 0 < p) (h : A ^ (1 / p) ≤ c * B) : A ≤ c ^ p * B ^ p := by
  have h' := Real.rpow_le_rpow (Real.rpow_nonneg hA _) h hp.le
  rwa [Real.mul_rpow hc hB, ← Real.rpow_mul hA, one_div_mul_cancel hp.ne', Real.rpow_one] at h'

theorem square_sqrt_rpow {x : ℝ} (hx : 0 ≤ x) (p : ℝ) : √x ^ p = x ^ (p / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; congr 1; ring

/-- **The bound of Proposition 6.5** (general `p`), with explicit constants: if `u` is a `UMD_p`
bound of `S_q^{d×d}` and `c` a constant of (31) at `p`, then for every rank-one Rademacher
martingale `M` started at `0`, with `f = Sym M`, `g = Skew M`,
`‖g_N‖_{L^p (S_q)} ≤ (u c)^{3/2} (p* − 1)^{1/2} d^{1/4 − 1/(2q)} ‖f_N‖_{L^p (S_q)}`.

Proof (the paper's, TeX lines 2448–2480, "the same proof, mutatis mutandis"): Hölder,
`‖𝔖_N g‖_{L^p (S_q)} ≤ ‖𝔖_N f‖_{L^p (S_q)}^{1/2} ‖𝔖_N f‖_{L^p (S_2)}^{1/2}` (from the pointwise
comparison `square_rankOne_comparison` and Cauchy–Schwarz); decoupling and (31) at `p`,
`‖g_N‖ ≤ u ‖g̃_N‖ ≤ u c ‖𝔖_N g‖` and `‖𝔖_N f‖_{L^p (S_q)} ≤ c ‖f̃_N‖ ≤ c u ‖f_N‖`; and the
Hilbert-valued square function inequality in `S_2` (Burkholder, Theorem 2.3 (2),
`square_korn_burkholder`) with fact (2):
`‖𝔖_N f‖_{L^p (S_2)} = ‖𝒮_N f‖_{L^p} ≤ (p* − 1) ‖f_N‖_{L^p (S_2)} ≤ (p* − 1) d^{1/2 − 1/q} ‖f_N‖_{L^p (S_q)}`. -/
theorem square_skew_le_sym_p {q : ℝ} (hq : 2 < q) {p : ℝ} (hp : 1 < p) {u c : ℝ} (hu : 0 ≤ u)
    (hc : 0 < c)
    (hU : umdConstWith (Fin d → Fin d → ℝ)
      (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) p ≤ ENNReal.ofReal u)
    (h31 : ∀ (n : ℕ) (x : Fin n → Matrix (Fin d) (Fin d) ℝ),
      (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
        c⁻¹ * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
            lpNormWith (schattenNorm (ENNReal.ofReal q)) p
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ∧
          lpNormWith (schattenNorm (ENNReal.ofReal q)) p
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
            c * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)))
    {N : ℕ} (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ)
    (hA : IsRankOneIncrements A) :
    lpNormWith (schattenNorm (ENNReal.ofReal q)) p (fun ε => skewPart (radMart 0 A N ε)) ≤
      u * c * √(u * c) * √(pStar p - 1) * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) *
        lpNormWith (schattenNorm (ENNReal.ofReal q)) p (fun ε => symPart (radMart 0 A N ε)) := by
  set Q := ENNReal.ofReal q with hQdef
  set r := ENNReal.ofReal (q / 2) with hrdef
  have hp0 : 0 < p := by linarith
  have hq1 : 1 < q := by linarith
  have hQ2 : (2 : ℝ≥0∞) ≤ Q := by
    rw [hQdef, ← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal hq.le
  have hr1 : (1 : ℝ≥0∞) ≤ r := by
    rw [hrdef, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  set β := pStar p - 1 with hβdef
  have hβ : 0 ≤ β := by
    have : p ≤ pStar p := le_max_left _ _
    linarith
  set S : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ := fun k ε => symPart (A k ε)
    with hSdef
  set K : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ := fun k ε => skewPart (A k ε)
    with hKdef
  have hSp : IsPredictable S := fun k ε ε' h => by simp only [hSdef, hA.1 k ε ε' h]
  have hKp : IsPredictable K := fun k ε ε' h => by simp only [hKdef, hA.1 k ε ε' h]
  have hf : (fun ε => symPart (radMart 0 A N ε)) = mart S N := funext fun ε => by
    rw [radMart, zero_add, square_symPart_mart]
  have hg : (fun ε => skewPart (radMart 0 A N ε)) = mart K N := funext fun ε => by
    rw [radMart, zero_add, square_skewPart_mart]
  rw [hf, hg]
  set a := lpNormWith (schattenNorm Q) p (mart K N) with ha
  set bf := lpNormWith (schattenNorm Q) p (mart S N) with hbf
  set IS : (Fin N → Bool) → ℝ := fun ε => avg fun ε' =>
    schattenNorm Q (∑ k, coin (ε' k) • S k ε) ^ p with hIS
  set IK : (Fin N → Bool) → ℝ := fun ε => avg fun ε' =>
    schattenNorm Q (∑ k, coin (ε' k) • K k ε) ^ p with hIK
  set X : (Fin N → Bool) → ℝ := fun ε => schattenNorm r (∑ k, S k ε * (S k ε)ᵀ) with hX
  set Z : (Fin N → Bool) → ℝ := fun ε => schattenNorm r (∑ k, K k ε * (K k ε)ᵀ) with hZ
  set W : (Fin N → Bool) → ℝ := fun ε => (∑ k, S k ε * (S k ε)ᵀ).trace with hW
  have hbf0 : 0 ≤ bf := Real.rpow_nonneg (rad_avg_nonneg fun ε =>
    Real.rpow_nonneg (schattenNorm_nonneg _ _) _) _
  have hIS0 : ∀ ε, 0 ≤ IS ε := fun ε => rad_avg_nonneg fun ε' =>
    Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  have hIK0 : ∀ ε, 0 ≤ IK ε := fun ε => rad_avg_nonneg fun ε' =>
    Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  have hX0 : ∀ ε, 0 ≤ X ε := fun ε => schattenNorm_nonneg _ _
  have hZ0 : ∀ ε, 0 ≤ Z ε := fun ε => schattenNorm_nonneg _ _
  have hpsd : ∀ P : Matrix (Fin d) (Fin d) ℝ, (P * Pᵀ).PosSemidef := fun P => by
    simpa [square_conjTranspose_eq] using Matrix.posSemidef_self_mul_conjTranspose P
  have hW0 : ∀ ε, 0 ≤ W ε := fun ε =>
    (Matrix.posSemidef_sum _ fun k _ => hpsd (S k ε)).trace_nonneg
  have hXp0 : 0 ≤ avg fun ε => X ε ^ (p / 2) :=
    rad_avg_nonneg fun ε => Real.rpow_nonneg (hX0 ε) _
  have hWp0 : 0 ≤ avg fun ε => W ε ^ (p / 2) :=
    rad_avg_nonneg fun ε => Real.rpow_nonneg (hW0 ε) _
  have hZp0 : 0 ≤ avg fun ε => Z ε ^ (p / 2) :=
    rad_avg_nonneg fun ε => Real.rpow_nonneg (hZ0 ε) _
  -- decoupling
  have hdS := (square_decoupling hq1 hu hp hU S hSp).1
  have hdK := (square_decoupling hq1 hu hp hU K hKp).2
  -- (31) in the decoupled signs: `E_ε̃ ‖g̃‖^p ≤ c^p ‖𝔖 g‖^p`, `‖𝔖 f‖^p ≤ c^p E_ε̃ ‖f̃‖^p`
  have h31K : ∀ ε, IK ε ≤ c ^ p * Z ε ^ (p / 2) := fun ε => by
    have h := (h31 N (fun k => K k ε) fun i => by
      simp only [hKdef, square_skewPart_transpose, Matrix.mul_neg, Matrix.neg_mul]).2
    have := square_le_rpow_of_rpow_one_div_le (hIK0 ε) (Real.sqrt_nonneg _) hc.le hp0 h
    rwa [square_sqrt_rpow (hZ0 ε)] at this
  have h31S : ∀ ε, X ε ^ (p / 2) ≤ c ^ p * IS ε := fun ε => by
    have h := (h31 N (fun k => S k ε) fun i => by
      simp only [hSdef, square_symPart_transpose]).1
    have h' : √(X ε) ≤ c * IS ε ^ (1 / p) :=
      calc √(X ε) = c * (c⁻¹ * √(X ε)) := by field_simp
        _ ≤ c * IS ε ^ (1 / p) := mul_le_mul_of_nonneg_left h hc.le
    have := Real.rpow_le_rpow (Real.sqrt_nonneg _) h' hp0.le
    rwa [square_sqrt_rpow (hX0 ε), Real.mul_rpow hc.le (Real.rpow_nonneg (hIS0 ε) _),
      ← Real.rpow_mul (hIS0 ε), one_div_mul_cancel hp0.ne', Real.rpow_one] at this
  -- the pointwise comparison and Cauchy–Schwarz: `E ‖𝔖 g‖^p ≤ (E ‖𝔖 f‖_{S_q}^p)^{1/2} (E ‖𝔖 f‖_{S_2}^p)^{1/2}`
  have hpt : ∀ ε, Z ε ^ (p / 2) ≤ √(X ε ^ (p / 2)) * √(W ε ^ (p / 2)) := fun ε => by
    have h := square_rankOne_comparison hr1 (fun k => A k ε) fun k => hA.2 k ε
    have h' := Real.rpow_le_rpow (hZ0 ε) h (by positivity : 0 ≤ p / 2)
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), square_sqrt_rpow (hX0 ε),
      square_sqrt_rpow (hW0 ε)] at h'
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (hX0 ε), ← Real.rpow_mul (hW0 ε)]
    convert h' using 3 <;> ring
  have hcs : (avg fun ε => Z ε ^ (p / 2)) ≤
      √(avg fun ε => X ε ^ (p / 2)) * √(avg fun ε => W ε ^ (p / 2)) :=
    (rad_avg_mono hpt).trans (square_avg_sqrt_mul_le (fun ε => Real.rpow_nonneg (hX0 ε) _)
      (fun ε => Real.rpow_nonneg (hW0 ε) _))
  -- `(E ‖𝔖 f‖_{S_q}^p)^{1/p} ≤ c u ‖f_N‖`
  have hXb : (avg fun ε => X ε ^ (p / 2)) ^ (1 / p) ≤ c * (u * bf) := by
    have : (avg fun ε => X ε ^ (p / 2)) ≤ c ^ p * avg IS := by
      rw [← rad_avg_mul_left]; exact rad_avg_mono h31S
    exact (square_rpow_one_div_le hXp0 (rad_avg_nonneg hIS0) hc.le hp0 this).trans
      (mul_le_mul_of_nonneg_left hdS hc.le)
  -- `(E ‖𝔖 f‖_{S_2}^p)^{1/p} ≤ (p* − 1) d^{1/2 − 1/q} ‖f_N‖`
  set D := (d : ℝ) ^ (1 / 2 - 1 / q) with hD
  have hD0 : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hWb : (avg fun ε => W ε ^ (p / 2)) ^ (1 / p) ≤ β * (D * bf) := by
    have hWs : ∀ ε, W ε = ∑ k, squareFrob (S k ε) (S k ε) := fun ε => by
      simp only [hW, Matrix.trace_sum, squareFrob]
      exact Finset.sum_congr rfl fun k _ => Matrix.trace_mul_comm _ _
    have hB := square_korn_burkholder hp S hSp
    simp only [← hWs] at hB
    refine hB.trans (mul_le_mul_of_nonneg_left ?_ hβ)
    have h2q : ∀ M : Matrix (Fin d) (Fin d) ℝ,
        squareFrob M M ^ (p / 2) ≤ D ^ p * schattenNorm Q M ^ p := by
      intro M
      have h := schattenNorm_le_rpow_mul (by norm_num : (1 : ℝ≥0∞) ≤ 2) hQ2 M
      rw [min_self, hQdef, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofNat] at h
      have h' := Real.rpow_le_rpow (schattenNorm_nonneg _ _) h hp0.le
      rw [Real.mul_rpow hD0 (schattenNorm_nonneg _ _)] at h'
      have e : squareFrob M M ^ (p / 2) = schattenNorm 2 M ^ p := by
        rw [show squareFrob M M = schattenNorm 2 M ^ 2 from (square_schattenNorm_two_sq M).symm,
          ← square_sqrt_rpow (sq_nonneg _), Real.sqrt_sq (schattenNorm_nonneg _ _)]
      rw [e]; exact h'
    have : (avg fun ε => squareFrob (mart S N ε) (mart S N ε) ^ (p / 2)) ≤
        D ^ p * avg fun ε => schattenNorm Q (mart S N ε) ^ p := by
      rw [← rad_avg_mul_left]; exact rad_avg_mono fun ε => h2q _
    exact square_rpow_one_div_le (rad_avg_nonneg fun ε =>
      Real.rpow_nonneg (squareFrob_self_nonneg _) _) (rad_avg_nonneg fun ε =>
        Real.rpow_nonneg (schattenNorm_nonneg _ _) _) hD0 hp0 this
  -- assemble
  have hZb : (avg fun ε => Z ε ^ (p / 2)) ^ (1 / p) ≤
      √((avg fun ε => X ε ^ (p / 2)) ^ (1 / p)) * √((avg fun ε => W ε ^ (p / 2)) ^ (1 / p)) := by
    calc (avg fun ε => Z ε ^ (p / 2)) ^ (1 / p)
        ≤ (√(avg fun ε => X ε ^ (p / 2)) * √(avg fun ε => W ε ^ (p / 2))) ^ (1 / p) :=
          Real.rpow_le_rpow hZp0 hcs (by positivity)
      _ = _ := by
          rw [Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
            Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hXp0,
            ← Real.rpow_mul hWp0, ← Real.rpow_mul hXp0, ← Real.rpow_mul hWp0, mul_comm (1 / 2)]
  have hKb : (avg IK) ^ (1 / p) ≤ c * (avg fun ε => Z ε ^ (p / 2)) ^ (1 / p) := by
    have : avg IK ≤ c ^ p * avg fun ε => Z ε ^ (p / 2) := by
      rw [← rad_avg_mul_left]; exact rad_avg_mono h31K
    exact square_rpow_one_div_le (rad_avg_nonneg hIK0) hZp0 hc.le hp0 this
  have hsD : √D = (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) := by
    rw [hD, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg _)]; congr 1; ring
  have huc : 0 ≤ u * c := mul_nonneg hu hc.le
  calc a ≤ u * (avg IK) ^ (1 / p) := hdK
    _ ≤ u * (c * (√((avg fun ε => X ε ^ (p / 2)) ^ (1 / p)) *
          √((avg fun ε => W ε ^ (p / 2)) ^ (1 / p)))) := by
        gcongr; exact hKb.trans (mul_le_mul_of_nonneg_left hZb hc.le)
    _ ≤ u * (c * (√(c * (u * bf)) * √(β * (D * bf)))) := by
        gcongr
    _ = u * c * √(u * c) * √β * √D * (√bf * √bf) := by
        rw [Real.sqrt_mul hc.le, Real.sqrt_mul hu, Real.sqrt_mul hβ, Real.sqrt_mul hD0,
          Real.sqrt_mul hu]
        ring
    _ = u * c * √(u * c) * √β * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) * bf := by
        rw [Real.mul_self_sqrt hbf0, hsD]

/-- `L^p` norms are monotone in a pointwise bound of the norms (`p > 0`). -/
theorem square_lpNormWith_le {N : ℕ} {E F : Type*} {n₁ : E → ℝ} {n₂ : F → ℝ}
    {X : (Fin N → Bool) → E} {Y : (Fin N → Bool) → F} {a p : ℝ} (ha : 0 ≤ a) (hp : 0 < p)
    (h0 : ∀ ε, 0 ≤ n₁ (X ε)) (h0' : ∀ ε, 0 ≤ n₂ (Y ε)) (h : ∀ ε, n₁ (X ε) ≤ a * n₂ (Y ε)) :
    lpNormWith n₁ p X ≤ a * lpNormWith n₂ p Y := by
  refine square_rpow_one_div_le (rad_avg_nonneg fun ε => Real.rpow_nonneg (h0 ε) _)
    (rad_avg_nonneg fun ε => Real.rpow_nonneg (h0' ε) _) ha hp ?_
  rw [← rad_avg_mul_left]
  refine rad_avg_mono fun ε => ?_
  rw [← Real.mul_rpow ha (h0' ε)]
  exact Real.rpow_le_rpow (h0 ε) (h ε) hp.le

/-- From `‖g_N‖_{L^p (S_q)} ≤ C ‖f_N‖_{L^p (S_q)}` (`f = Sym M`, `g = Skew M`):
`E f_{p,q,C} (M_N) ≥ 0`. -/
theorem square_avg_kornF_nonneg {p : ℝ} (hp : 0 < p) {q : ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (M : (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ)
    (h : lpNormWith (schattenNorm q) p (fun ε => skewPart (M ε)) ≤
      C * lpNormWith (schattenNorm q) p (fun ε => symPart (M ε))) :
    0 ≤ avg fun ε => kornF d p q C (M ε) := by
  have hS0 : 0 ≤ avg fun ε => schattenNorm q (symPart (M ε)) ^ p :=
    rad_avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  have hK0 : 0 ≤ avg fun ε => schattenNorm q (skewPart (M ε)) ^ p :=
    rad_avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _
  have h' := square_le_rpow_of_rpow_one_div_le hK0 (Real.rpow_nonneg hS0 _) hC hp h
  rw [← Real.rpow_mul hS0, one_div_mul_cancel hp.ne', Real.rpow_one] at h'
  have hval : (avg fun ε => kornF d p q C (M ε)) =
      C ^ p * (avg fun ε => schattenNorm q (symPart (M ε)) ^ p) -
        avg fun ε => schattenNorm q (skewPart (M ε)) ^ p := by
    simp only [kornF]
    rw [rad_avg_sub, rad_avg_mul_left]
  rw [hval, sub_nonneg]
  exact h'

/-- `UMD_p (S_q^{d×d}) ≤ 100 p* C_R (q* − 1)`: extrapolation (Proposition 2.7 (1),
`hnvwExtrapolation_holds`) from Randrianantoanina's bound (Proposition 2.7 (2)). -/
theorem square_umd_p {CR : ℝ}
    (hR' : ∀ (q : ℝ), 1 < q → ∀ d : ℕ,
      umdConstWith (Fin d → Fin d → ℝ) (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) 2 ≤
        ENNReal.ofReal (CR * (pStar q - 1)))
    {q : ℝ} (hq : 1 < q) {p : ℝ} (hp : 1 < p) (d : ℕ) :
    umdConstWith (Fin d → Fin d → ℝ) (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) p ≤
      ENNReal.ofReal (100 * pStar p * (CR * (pStar q - 1))) := by
  have hQ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le
  have hps : 0 ≤ 100 * pStar p := by
    have : p ≤ pStar p := le_max_left _ _
    linarith
  obtain ⟨htri, hhom, hequiv⟩ := schattenNorm_renorms (d := d) hQ1
  have h := ((hnvwExtrapolation_holds (Fin d → Fin d → ℝ) _ htri hhom hequiv).2 p hp).2
  calc _ ≤ ENNReal.ofReal (100 * pStar p) * umdConstWith (Fin d → Fin d → ℝ)
        (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) 2 := h
    _ ≤ ENNReal.ofReal (100 * pStar p) * ENNReal.ofReal (CR * (pStar q - 1)) := by
        gcongr; exact hR' q hq d
    _ = _ := (ENNReal.ofReal_mul hps).symm

/-- (31) at a general `p ∈ (1, ∞)` with a constant `c₀ (p) √q`, uniformly in `q ∈ [2, ∞)`
(the polynomial dependence on `q` used for the case `q = ∞` of Proposition 6.5): Proposition 6.3
at the exponent `q`, with the hypercontractive Kahane–Khintchine bound
(`kahaneKhintchineHypercontractive_holds`) and the monotonicity of `L^p` norms (for `p ≤ q`:
`‖·‖_{L^q} ≤ √((q − 1)/(p − 1)) ‖·‖_{L^p}` and `‖·‖_{L^p} ≤ ‖·‖_{L^q}`; for
`p > q`: `‖·‖_{L^q} ≤ ‖·‖_{L^p} ≤ √((p − 1)/(q − 1)) ‖·‖_{L^q}`). -/
theorem square_eq31_q {p : ℝ} (hp : 1 < p) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ q : ℝ, 2 ≤ q → ∀ (d n : ℕ) (x : Fin n → Matrix (Fin d) (Fin d) ℝ),
      (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
        (c₀ * √q)⁻¹ * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
            lpNormWith (schattenNorm (ENNReal.ofReal q)) p
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ∧
          lpNormWith (schattenNorm (ENNReal.ofReal q)) p
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
            (c₀ * √q) * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) := by
  obtain ⟨C, hC, hPX'⟩ := pisierXuKhintchine_holds
  have hp0 : 0 < p := by linarith
  have hs : 0 < √(p - 1) := Real.sqrt_pos.2 (by linarith)
  set c₀ := (1 + C) * (1 + √(p - 1) + (√(p - 1))⁻¹) with hc₀
  have hc₀1 : 1 ≤ c₀ := by
    have h1 : 1 ≤ 1 + C := by linarith
    have h2 : 1 ≤ 1 + √(p - 1) + (√(p - 1))⁻¹ := by
      have := inv_pos.2 hs; linarith
    nlinarith
  have hc₀C : C ≤ c₀ := by
    have h2 : 1 ≤ 1 + √(p - 1) + (√(p - 1))⁻¹ := by
      have := inv_pos.2 hs; linarith
    nlinarith
  have hc₀i : (√(p - 1))⁻¹ ≤ c₀ := by
    have := inv_pos.2 hs
    nlinarith
  have hc₀s : C * √(p - 1) ≤ c₀ := by
    have := inv_pos.2 hs
    nlinarith
  refine ⟨c₀, by linarith, fun q hq d n x hx => ?_⟩
  have hq1 : 1 < q := by linarith
  have hQ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le
  have hsq : 0 < √q := Real.sqrt_pos.2 (by linarith)
  have hsq1 : 1 ≤ √q := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  obtain ⟨h1, h2⟩ := hPX' q hq d n x hx
  have kk : ∀ a b : ℝ, 1 < a → a ≤ b →
      lpNormWith (schattenNorm (ENNReal.ofReal q)) b
          (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
        √((b - 1) / (a - 1)) * lpNormWith (schattenNorm (ENNReal.ofReal q)) a
          (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) := fun a b ha hab =>
    kahaneKhintchineHypercontractive_holds a b ha hab (Matrix (Fin d) (Fin d) ℝ)
      (schattenNorm (ENNReal.ofReal q)) (fun x y => schattenNorm_add_le hQ1 x y)
      (fun c x => schattenNorm_smul hQ1 c x) n x
  set s := √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))
  set Lp := lpNormWith (schattenNorm (ENNReal.ofReal q)) p
    (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i)
  set Lq := lpNormWith (schattenNorm (ENNReal.ofReal q)) q
    (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hLq0 : 0 ≤ Lq :=
    Real.rpow_nonneg (rad_avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _) _
  have hLp0 : 0 ≤ Lp :=
    Real.rpow_nonneg (rad_avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _) _
  have hc0 : 0 < c₀ * √q := mul_pos (by linarith) hsq
  rcases le_or_gt p q with hpq | hpq
  · -- `p ≤ q`
    have hκ' : √((q - 1) / (p - 1)) ≤ c₀ * √q := by
      calc √((q - 1) / (p - 1)) ≤ √q * (√(p - 1))⁻¹ := by
            rw [Real.sqrt_div' _ (by linarith : (0:ℝ) ≤ p - 1), div_eq_mul_inv]
            gcongr; linarith
        _ ≤ √q * c₀ := mul_le_mul_of_nonneg_left hc₀i hsq.le
        _ = c₀ * √q := mul_comm _ _
    constructor
    · rw [inv_mul_le_iff₀ hc0]
      calc s ≤ Lq := h1
        _ ≤ √((q - 1) / (p - 1)) * Lp := kk p q hp hpq
        _ ≤ c₀ * √q * Lp := mul_le_mul_of_nonneg_right hκ' hLp0
    · calc Lp ≤ Lq := square_lpNormWith_mono _ (schattenNorm_nonneg _) hp0 hpq _
        _ ≤ C * √q * s := h2
        _ ≤ c₀ * √q * s := by gcongr
  · -- `p > q`
    have hκ' : √((p - 1) / (q - 1)) ≤ √(p - 1) :=
      Real.sqrt_le_sqrt (div_le_self (by linarith) (by linarith))
    constructor
    · calc (c₀ * √q)⁻¹ * s ≤ 1 * s := by
            gcongr; rw [inv_le_one₀ hc0]; nlinarith
        _ ≤ Lq := by rw [one_mul]; exact h1
        _ ≤ Lp := square_lpNormWith_mono _ (schattenNorm_nonneg _) (by linarith) hpq.le _
    · calc Lp ≤ √((p - 1) / (q - 1)) * Lq := kk q p hq1 hpq.le
        _ ≤ √(p - 1) * (C * √q * s) :=
            mul_le_mul hκ' h2 hLq0 hs.le
        _ = (C * √(p - 1)) * √q * s := by ring
        _ ≤ c₀ * √q * s := by gcongr

/-- `q = log d + 2` for `d ≥ 2`: `q > 2` and `q³ d^{1/(2q)} ≤ 250 log³ d` (`log 2 > 0.69`,
`exp (1/2) < 2`). -/
theorem square_log_choice {d : ℕ} (hd : 2 ≤ d) :
    2 < Real.log d + 2 ∧ 0 ≤ Real.log d ∧
      (Real.log d + 2) ^ 3 * (d : ℝ) ^ (1 / (2 * (Real.log d + 2))) ≤ 250 * Real.log d ^ 3 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogd : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) (by exact_mod_cast hd)
  have hl : (0.69 : ℝ) < Real.log d := by linarith
  set q := Real.log d + 2 with hqdef
  have hq0 : 0 < q := by linarith
  have hq3 : q ^ 3 ≤ 125 * Real.log d ^ 3 := by
    calc q ^ 3 ≤ (5 * Real.log d) ^ 3 := pow_le_pow_left₀ hq0.le (by linarith) 3
      _ = 125 * Real.log d ^ 3 := by ring
  have hexp : (d : ℝ) ^ (1 / (2 * q)) ≤ 2 := by
    rw [Real.rpow_def_of_pos hd0]
    have h1 : Real.log d * (1 / (2 * q)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
    have h2 : Real.exp (1 / 2) < 2 := by
      have he := Real.exp_one_lt_d9
      have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_pos (1 / 2)]
    exact (Real.exp_le_exp.2 h1).trans h2.le
  refine ⟨by linarith, by linarith, ?_⟩
  calc q ^ 3 * (d : ℝ) ^ (1 / (2 * q)) ≤ (125 * Real.log d ^ 3) * 2 :=
        mul_le_mul hq3 hexp (Real.rpow_nonneg hd0.le _) (by positivity)
    _ = 250 * Real.log d ^ 3 := by ring

/-- **Proposition 6.5** (`cs-prop6.5`), case `q ∈ (2, ∞)`: for `q ∈ (2, ∞)` and `p ∈ (1, ∞)`
there is `C_{q,p}` with `C^{rc} (S_q^{d×d}, p) ≤ C_{q,p} d^{1/4 − 1/(2q)}` for every `d ≥ 2`.
The proof uses Propositions 2.7 (1), (2), 2.8, 6.3, 6.4 and Burkholder's square function
inequality, Theorem 2.3 (2), all proved (`Morrey/Cassese/Hypotheses.lean`); Proposition 6.4 with no
bound on its constants: this case does not use the hypercontractive bound
(`KahaneKhintchineHypercontractive`).

Proof (the paper's, TeX lines 2448–2480): the bound
`‖Skew M_N‖_{L^p (S_q)} ≤ (u c)^{3/2} (p* − 1)^{1/2} d^{1/4 − 1/(2q)} ‖Sym M_N‖_{L^p (S_q)}`
(`square_skew_le_sym_p`: Hölder, decoupling with `UMD_p (S_q) ≤ u = 100 p* C_R (q* − 1)`
(Propositions 2.7 (1), (2), `square_umd_p`), (31) at `p` (`equation31`), and the Hilbert-valued
square function inequality in `S_2` (Theorem 2.3 (2), `square_korn_burkholder`) with fact (2)),
then Proposition 2.5. -/
theorem proposition6_5_finite :
    ∀ q : ℝ, 2 < q → ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      rcThreshold (kornF d p (ENNReal.ofReal q)) ≤
        ENNReal.ofReal (C * (d : ℝ) ^ (1 / 4 - 1 / (2 * q))) := by
  obtain ⟨CR, hCR, hR'⟩ := randrianantoaninaSchattenUMD_holds
  have hCRq : ∀ q : ℝ, 1 < q → ∀ d : ℕ,
      umdConstWith (Fin d → Fin d → ℝ) (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) 2 ≤
        ENNReal.ofReal (CR * (pStar q - 1)) := hR'
  have hps : ∀ p : ℝ, 1 < p → 1 < pStar p := fun p hp => lt_of_lt_of_le hp (le_max_left _ _)
  intro q hq p hp
  have hq1 : 1 < q := by linarith
  have hp0 : 0 < p := by linarith
  have hQ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le
  obtain ⟨c, hc, h31⟩ := equation31 p q hp hq.le
  set u := 100 * pStar p * (CR * (pStar q - 1)) with hudef
  have hu : 0 < u := by
    have h1 := hps p hp; have h2 := hps q hq1
    have : 0 < pStar q - 1 := by linarith
    positivity
  have hβ : 0 < pStar p - 1 := by linarith [hps p hp]
  refine ⟨u * c * √(u * c) * √(pStar p - 1), by positivity, fun d _ => ?_⟩
  set C := u * c * √(u * c) * √(pStar p - 1) * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine (iInf₂_le C ⟨hC0, (proposition2_5 (square_continuous_kornF hp0.le hQ1 C)).2
    fun N A hA => ?_⟩).trans (le_of_eq (by rw [hCdef]))
  rw [square_kornF_zero hp0 hQ1]
  exact square_avg_kornF_nonneg hp0 hC0 _ (square_skew_le_sym_p hq hp hu.le hc
    (square_umd_p hCRq hq1 hp d) (h31 d) A hA)

/-- **Proposition 6.5** (`cs-prop6.5`), case `q = ∞`: there is `α > 0` such that for every
`p ∈ (1, ∞)` there is `C_p` with `C^{rc} (S_∞^{d×d}, p) ≤ C_p d^{1/4} log^α d` for every `d ≥ 2`;
the proof gives `α = 3`. The proof uses Propositions 2.7 (1), (2), 2.8, 6.3, Theorem 2.3 (2) and
the hypercontractive Kahane–Khintchine bound `k_{q,p} ≤ √((q − 1)/(p − 1))`
(`KahaneKhintchineHypercontractive`, Borell's), which gives the constants of Proposition 6.4
polynomial in `q` that this case needs (inventory E27), all proved
(`Morrey/Cassese/Hypotheses.lean`).

Statement change. The paper's "`C^{rc} (S_∞^{d×d}, p) ≤ C_p d^{1/4} log^α d` for some
`α > 0`" was formalized with `α` depending on `p` (`∀ p, ∃ α`); it is now stated uniformly
(`∃ α, ∀ p`), a strengthening that covers both readings, since the proof gives `α = 3` for every
`p`.

Proof (the paper's, TeX lines 2448–2480): "the same norm-comparison and optimisation argument as
in Remark 6.3": the constants are polynomial in `q` (`UMD_p (S_q) ≤ 100 p* C_R q`, and (31) at `p`
with a constant `c₀ (p) √q`, `square_eq31_q`, from the hypercontractive bound), so
`‖·‖_{L^p (S_∞)}` of `Skew M_N` is at most `K_p q³ d^{1/4} d^{1/(2q)}` times that of `Sym M_N`;
with `q = log d + 2`, `α = 3`. -/
theorem proposition6_5_infty :
    ∃ α : ℝ, 0 < α ∧ ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      rcThreshold (kornF d p ⊤) ≤ ENNReal.ofReal (C * (d : ℝ) ^ (1 / 4 : ℝ) * Real.log d ^ α) := by
  obtain ⟨CR, hCR, hR'⟩ := randrianantoaninaSchattenUMD_holds
  have hCRq : ∀ q : ℝ, 1 < q → ∀ d : ℕ,
      umdConstWith (Fin d → Fin d → ℝ) (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) 2 ≤
        ENNReal.ofReal (CR * (pStar q - 1)) := hR'
  have hps : ∀ p : ℝ, 1 < p → 1 < pStar p := fun p hp => lt_of_lt_of_le hp (le_max_left _ _)
  refine ⟨3, by norm_num, fun p hp => ?_⟩
  have hp0 : 0 < p := by linarith
  obtain ⟨c₀, hc₀, h31⟩ := square_eq31_q hp
  have hβ : 0 < pStar p - 1 := by linarith [hps p hp]
  set G := 100 * pStar p * CR * c₀ with hG
  have hG0 : 0 < G := by have := hps p hp; positivity
  refine ⟨250 * (G * √G * √(pStar p - 1)), by positivity, fun d hd => ?_⟩
  obtain ⟨hq, hlog0, hlog⟩ := square_log_choice hd
  set q := Real.log d + 2 with hqdef
  have hq1 : 1 < q := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hQ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le
  have hpq : pStar q = q := by
    refine max_eq_left ?_
    rw [div_le_iff₀ (by linarith)]; nlinarith
  set u := 100 * pStar p * (CR * (pStar q - 1)) with hudef
  have hu : 0 ≤ u := by
    have := hps p hp
    have : 0 ≤ pStar q - 1 := by rw [hpq]; linarith
    positivity
  set c := c₀ * √q with hcdef
  have hsq : 0 < √q := Real.sqrt_pos.2 (by linarith)
  have hc : 0 < c := mul_pos hc₀ hsq
  have hb := fun N (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ)
    (hA : IsRankOneIncrements A) => square_skew_le_sym_p hq hp hu hc
      (square_umd_p hCRq hq1 hp d) (fun n x hx => h31 q hq.le d n x hx) A hA
  -- `u c √(u c) ≤ G √G q³`
  have huc : u * c ≤ G * q ^ 2 := by
    have h1 : u ≤ 100 * pStar p * CR * q := by
      rw [hudef, hpq]
      have := hps p hp
      have : 0 ≤ 100 * pStar p * CR := by positivity
      nlinarith
    have h2 : √q ≤ q := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    calc u * c = u * (c₀ * √q) := rfl
      _ ≤ (100 * pStar p * CR * q) * (c₀ * q) := by
          have hA0 : 0 ≤ 100 * pStar p * CR * q :=
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith [hps p hp])) hCR.le)
              (by linarith)
          exact mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hc₀.le) (by positivity) hA0
      _ = G * q ^ 2 := by rw [hG]; ring
  have hK : u * c * √(u * c) * √(pStar p - 1) ≤ G * √G * √(pStar p - 1) * q ^ 3 := by
    have h0 : 0 ≤ u * c := mul_nonneg hu hc.le
    have hs : √(u * c) ≤ √G * q := by
      calc √(u * c) ≤ √(G * q ^ 2) := Real.sqrt_le_sqrt huc
        _ = √G * q := by rw [Real.sqrt_mul hG0.le, Real.sqrt_sq (by linarith)]
    calc u * c * √(u * c) * √(pStar p - 1) ≤ (G * q ^ 2) * (√G * q) * √(pStar p - 1) := by
          gcongr
      _ = G * √G * √(pStar p - 1) * q ^ 3 := by ring
  set K := G * √G * √(pStar p - 1) with hKdef
  have hK0 : 0 ≤ K := by positivity
  set Crc := 250 * K * (d : ℝ) ^ (1 / 4 : ℝ) * Real.log d ^ (3 : ℝ) with hCrc
  have hCrc0 : 0 ≤ Crc := by positivity
  refine (iInf₂_le Crc ⟨hCrc0, (proposition2_5 (square_continuous_kornF hp0.le le_top Crc)).2
    fun N A hA => ?_⟩).trans (le_of_eq (by rw [hCrc]))
  rw [square_kornF_zero hp0 le_top]
  refine square_avg_kornF_nonneg hp0 hCrc0 _ ?_
  -- `‖·‖_{S_∞} ≤ ‖·‖_{S_q} ≤ d^{1/q} ‖·‖_{S_∞}`
  have hgq : lpNormWith (schattenNorm ⊤) p (fun ε => skewPart (radMart 0 A N ε)) ≤
      1 * lpNormWith (schattenNorm (ENNReal.ofReal q)) p
        (fun ε => skewPart (radMart 0 A N ε)) :=
    square_lpNormWith_le zero_le_one hp0 (fun ε => schattenNorm_nonneg _ _)
      (fun ε => schattenNorm_nonneg _ _) fun ε => by
        rw [one_mul]; exact schattenNorm_anti hQ1 le_top _
  have hfq : lpNormWith (schattenNorm (ENNReal.ofReal q)) p
      (fun ε => symPart (radMart 0 A N ε)) ≤ (d : ℝ) ^ (1 / q) *
        lpNormWith (schattenNorm ⊤) p (fun ε => symPart (radMart 0 A N ε)) :=
    square_lpNormWith_le (Real.rpow_nonneg hd0.le _) hp0 (fun ε => schattenNorm_nonneg _ _)
      (fun ε => schattenNorm_nonneg _ _) fun ε => by
        have h := schattenNorm_le_rpow_mul hQ1 le_top (symPart (radMart 0 A N ε))
        rwa [min_self, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_top, div_zero,
          sub_zero] at h
  have hexp : (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) * (d : ℝ) ^ (1 / q) =
      (d : ℝ) ^ (1 / 4 : ℝ) * (d : ℝ) ^ (1 / (2 * q)) := by
    rw [← Real.rpow_add hd0, ← Real.rpow_add hd0]; congr 1; field_simp; ring
  have hlog3 : Real.log d ^ (3 : ℝ) = Real.log d ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hfin : u * c * √(u * c) * √(pStar p - 1) * ((d : ℝ) ^ (1 / 4 : ℝ) *
      (d : ℝ) ^ (1 / (2 * q))) ≤ Crc := by
    have hd4 : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hd0.le _
    calc u * c * √(u * c) * √(pStar p - 1) * ((d : ℝ) ^ (1 / 4 : ℝ) * (d : ℝ) ^ (1 / (2 * q)))
        ≤ K * q ^ 3 * ((d : ℝ) ^ (1 / 4 : ℝ) * (d : ℝ) ^ (1 / (2 * q))) := by
          gcongr
      _ = K * (d : ℝ) ^ (1 / 4 : ℝ) * (q ^ 3 * (d : ℝ) ^ (1 / (2 * q))) := by ring
      _ ≤ K * (d : ℝ) ^ (1 / 4 : ℝ) * (250 * Real.log d ^ 3) := by gcongr
      _ = Crc := by rw [hCrc, hlog3]; ring
  have hf0 : 0 ≤ lpNormWith (schattenNorm ⊤) p (fun ε => symPart (radMart 0 A N ε)) :=
    Real.rpow_nonneg (rad_avg_nonneg fun ε => Real.rpow_nonneg (schattenNorm_nonneg _ _) _) _
  have hKq0 : 0 ≤ u * c * √(u * c) * √(pStar p - 1) * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) := by
    have : 0 ≤ u * c := mul_nonneg hu hc.le
    positivity
  calc lpNormWith (schattenNorm ⊤) p (fun ε => skewPart (radMart 0 A N ε))
      ≤ 1 * lpNormWith (schattenNorm (ENNReal.ofReal q)) p
        (fun ε => skewPart (radMart 0 A N ε)) := hgq
    _ ≤ u * c * √(u * c) * √(pStar p - 1) * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) *
        lpNormWith (schattenNorm (ENNReal.ofReal q)) p
          (fun ε => symPart (radMart 0 A N ε)) := by rw [one_mul]; exact hb N A hA
    _ ≤ u * c * √(u * c) * √(pStar p - 1) * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)) *
        ((d : ℝ) ^ (1 / q) *
          lpNormWith (schattenNorm ⊤) p (fun ε => symPart (radMart 0 A N ε))) :=
        mul_le_mul_of_nonneg_left hfq hKq0
    _ = u * c * √(u * c) * √(pStar p - 1) * ((d : ℝ) ^ (1 / 4 - 1 / (2 * q)) *
        (d : ℝ) ^ (1 / q)) *
          lpNormWith (schattenNorm ⊤) p (fun ε => symPart (radMart 0 A N ε)) := by ring
    _ ≤ Crc * lpNormWith (schattenNorm ⊤) p (fun ε => symPart (radMart 0 A N ε)) := by
        rw [hexp]; exact mul_le_mul_of_nonneg_right hfin hf0

/-- **Proposition 6.5** (`cs-prop6.5`): for `q ∈ (2, ∞)` and `p ∈ (1, ∞)` there is `C_{q,p}` with
`C^{rc} (S_q^{d×d}, p) ≤ C_{q,p} d^{1/4 − 1/(2q)}` for every `d ≥ 2`; and there is `α > 0` such
that for every `p ∈ (1, ∞)` there is `C_p` with `C^{rc} (S_∞^{d×d}, p) ≤ C_p d^{1/4} log^α d` for
every `d ≥ 2`. The proof uses Propositions 2.7 (1), (2), 2.8, 6.3, 6.4, Theorem 2.3 (2) and, for
the case `q = ∞`, the hypercontractive Kahane–Khintchine bound
(`KahaneKhintchineHypercontractive`), all proved (`Morrey/Cassese/Hypotheses.lean`). The two cases
are `proposition6_5_finite` and `proposition6_5_infty`.

Statement change: `α` is uniform in `p` (`∃ α, ∀ p`, a strengthening of the former `∀ p, ∃ α`;
the proof gives `α = 3`). -/
theorem proposition6_5 :
    (∀ q : ℝ, 2 < q → ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      rcThreshold (kornF d p (ENNReal.ofReal q)) ≤
        ENNReal.ofReal (C * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)))) ∧
    ∃ α : ℝ, 0 < α ∧ ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      rcThreshold (kornF d p ⊤) ≤ ENNReal.ofReal (C * (d : ℝ) ^ (1 / 4 : ℝ) * Real.log d ^ α) :=
  ⟨proposition6_5_finite, proposition6_5_infty⟩

/-- **Periodic test maps for Hessian quasiconvexity** (`cs-hess-periodic`): a smooth
`ℤ^n`-periodic `φ : ℝ^n → ℝ` with `∫_{(0,1)^n} F (A + D²φ) < F (A)`, for a continuous `F`,
witnesses that `F` is not Hessian quasiconvex at `A` (whose test maps, `HessianQuasiconvexAt`,
have compact support in the open cube). The second-order analogue of the periodic
characterization of quasiconvexity (Lemma 2.2; Šverák's Lemma 1, `Sverak.lemma1_witness`).

Proof (`square_not_hessianQuasiconvexAt_of_periodic`, module `Square.Hessian`): the test maps are
`ψ_K (x) = N_K⁻² η_K (x) φ (N_K x)`, with Šverák's cutoff `η_K = Sverak.l1_eta n K` (equal to `1`
on `[1/K, 1 − 1/K]^n`, vanishing off `(1/(16K), 1 − 1/(16K))^n`) and the oscillation
`N_K = K + a_K + b_K`, where `a_K`, `b_K` bound `‖D η_K‖`, `‖D² η_K‖` (finite: `η_K` is smooth with
compact support). By Leibniz's rule `‖D² ψ_K‖ ≤ ‖D²φ‖_∞ + 2 ‖Dφ‖_∞ + ‖φ‖_∞` for `K ≥ 1`, and
`D² ψ_K (x) = D²φ (N_K x)` on `(1/K, 1 − 1/K)^n`; dominated convergence and the averaging limit of
periodic functions (`Sverak.l1_tendsto_setIntegral_comp_smul`) give
`∫ F (A + D² ψ_K) → ∫ F (A + D²φ) < F (A)` as `K → ∞`, so some `ψ_K` (smooth, with compact support
in `(0, 1)^n`) violates Hessian quasiconvexity at `A`.

The proof of Corollary 6.1 (TeX lines 2489–2520) integrates over `𝕋^{2n}` with the
`2π`-periodic `φ (x, y) = Σ_{i,j} sin (x_i − y_j)`, which the paper treats as a test map of
Hessian quasiconvexity without comment. It reaches this lemma through the rescaled witness
`ψ (z) = (2π)⁻² φ (2π z)` (`square_corWitness`), which is `ℤ^{2n}`-periodic with
`D²ψ (z) = D²φ (2π z)` (no homogeneity factor), so that
`∫_{(0,1)^{2n}} F (D²ψ) = (2π)^{−2n} ∫_{[0, 2π]^{2n}} F (D²φ) < 0`. -/
theorem not_hessianQuasiconvexAt_of_periodic {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hF : Continuous F) {A : Matrix (Fin n) (Fin n) ℝ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hper : ∀ (x : Fin n → ℝ) (z : Fin n → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (hlt : ∫ x in unitCube n, F (A + hessian φ x) < F A) :
    ¬ HessianQuasiconvexAt F A :=
  square_not_hessianQuasiconvexAt_of_periodic hF hφ hper hlt

/-- `Sym (t A) = t Sym (A)`, `Skew (t A) = t Skew (A)`. -/
theorem square_symPart_skewPart_smul (t : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    symPart (t • A) = t • symPart A ∧ skewPart (t • A) = t • skewPart A := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [symPart, skewPart, Matrix.transpose_smul, smul_add, smul_sub, smul_smul]
    rw [mul_comm]

/-- The integrand (30) is `p`-homogeneous. -/
theorem square_kornF_hom {p : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (C : ℝ) :
    IsPHomogeneous p (kornF d p q C) := by
  intro t A
  obtain ⟨h1, h2⟩ := square_symPart_skewPart_smul t A
  simp only [kornF, h1, h2, schattenNorm_smul hq,
    Real.mul_rpow (abs_nonneg t) (schattenNorm_nonneg _ _)]
  ring

/-- `C ↦ f_{p,q,C}` is increasing on `C ≥ 0`. -/
theorem square_kornF_mono {p : ℝ} (hp : 0 ≤ p) {q : ℝ≥0∞} {C C' : ℝ} (hC' : 0 ≤ C')
    (hCC' : C' ≤ C) (A : Matrix (Fin d) (Fin d) ℝ) : kornF d p q C' A ≤ kornF d p q C A := by
  simp only [kornF]
  have := Real.rpow_le_rpow hC' hCC' hp
  have h1 := Real.rpow_nonneg (schattenNorm_nonneg q (symPart A)) p
  nlinarith

/-- A continuous integrand is locally bounded (the hypothesis of Lemma 2.2,
`External.Rindler.quasiconvexAtOn_iff_periodic`). -/
theorem square_isLocallyBounded_of_continuous {f : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hf : Continuous f) : CalculusOfVariations.IsLocallyBounded f := fun A =>
  ⟨f ⁻¹' Set.Ioo (f A - 1) (f A + 1),
    hf.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)),
    |f A| + 1, fun B hB => by
      obtain ⟨h1, h2⟩ := hB
      rw [abs_le]
      constructor <;> linarith [le_abs_self (f A), neg_abs_le (f A)]⟩

/-- The conclusion of Corollary 6.1 in dimension `d`, with its periodic witness: `F` is
continuous, convex along the Hessian rank-one lines `H + t a ⊗ a` through symmetric `H`,
`p`-homogeneous on symmetric matrices, and a smooth `ℤ^d`-periodic `ψ` has
`∫_{(0,1)^d} F (0 + D²ψ) < F (0)`. -/
def square_Cor61 (p : ℝ) (d : ℕ) (F : Matrix (Fin d) (Fin d) ℝ → ℝ) : Prop :=
  Continuous F ∧
    (∀ H : Matrix (Fin d) (Fin d) ℝ, H.IsSymm → ∀ a : Fin d → ℝ,
      ConvexOn ℝ Set.univ fun t : ℝ => F (H + t • Matrix.vecMulVec a a)) ∧
    (∀ (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ), H.IsSymm → F (t • H) = |t| ^ p * F H) ∧
    ∃ ψ : (Fin d → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ (x : Fin d → ℝ) (z : Fin d → ℤ), ψ (x + fun i => (z i : ℝ)) = ψ x) ∧
      ∫ x in unitCube d, F (0 + hessian ψ x) < F 0

/-- The conclusion of Corollary 6.1 from `square_Cor61`: a continuous function is an integrand;
the periodic witness refutes Hessian quasiconvexity at `0` (`not_hessianQuasiconvexAt_of_periodic`);
and homogeneity gives "nowhere" (`square_not_hessianQuasiconvexAt_of_zero`). -/
theorem square_cor61_conclusion {p : ℝ} (hp : 0 < p) {F : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hF : square_Cor61 p d F) :
    IsIntegrand F ∧
      (∀ H : Matrix (Fin d) (Fin d) ℝ, H.IsSymm → ∀ a : Fin d → ℝ,
        ConvexOn ℝ Set.univ fun t : ℝ => F (H + t • Matrix.vecMulVec a a)) ∧
      (∀ (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ), H.IsSymm → F (t • H) = |t| ^ p * F H) ∧
      ¬ HessianQuasiconvexAt F 0 ∧
      ∀ A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm → ¬ HessianQuasiconvexAt F A := by
  obtain ⟨hFc, hconv, hhom, ψ, hψ, hper, hwit⟩ := hF
  have h0 : ¬ HessianQuasiconvexAt F 0 := not_hessianQuasiconvexAt_of_periodic hFc hψ hper hwit
  refine ⟨⟨hFc.lowerSemicontinuous, square_isLocallyBounded_of_continuous hFc⟩, hconv, hhom, h0,
    fun A hA => square_not_hessianQuasiconvexAt_of_zero hp hFc hhom h0 hA⟩

/-- The upper left `d × d` block of a `(d + 1) × (d + 1)` matrix. -/
def square_truncLast (H : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  H.submatrix Fin.castSucc Fin.castSucc

/-- The first `d` coordinates of `x ∈ ℝ^{d+1}`, a continuous linear map. -/
noncomputable def square_initCLM (d : ℕ) : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castSucc i)

theorem square_initCLM_apply (x : Fin (d + 1) → ℝ) (i : Fin d) :
    square_initCLM d x i = x (Fin.castSucc i) := rfl

theorem square_initCLM_single (j : Fin d) :
    square_initCLM d (Pi.single (Fin.castSucc j) 1) = Pi.single j 1 := by
  funext i
  simp only [square_initCLM_apply, Pi.single_apply, Fin.castSucc_inj]

/-- The Hessian of `ψ (x₁, …, x_d)` on `ℝ^{d+1}` has `D²ψ` as upper left block. -/
theorem square_truncLast_hessian {ψ : (Fin d → ℝ) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (x : Fin (d + 1) → ℝ) :
    square_truncLast (hessian (ψ ∘ square_initCLM d) x) = hessian ψ (square_initCLM d x) := by
  have hψ' : ContDiff ℝ 2 (ψ ∘ square_initCLM d) := hψ.comp (square_initCLM d).contDiff
  ext i j
  rw [square_truncLast, Matrix.submatrix_apply, square_hess_hessian_apply hψ',
    square_hess_hessian_apply hψ, (square_initCLM d).iteratedFDeriv_comp_right hψ x le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext k
  fin_cases k <;> simp [square_initCLM_single]

/-- **Corollary 6.1 in every larger dimension** (the trivial embedding): `square_Cor61` in
dimension `d` gives it in dimension `d + 1`, with `F_{d+1} (H) = F_d (H')`, `H'` the upper left
`d × d` block of `H`, and the witness `ψ_{d+1} (x) = ψ_d (x₁, …, x_d)`, whose Hessian has `D²ψ_d`
as upper left block (`square_truncLast_hessian`), so that the integral over `(0, 1)^{d+1}` is the
integral over `(0, 1)^d` (Fubini, `square_integral_cube_succ`). -/
theorem square_cor61_succ {p : ℝ} {F : Matrix (Fin d) (Fin d) ℝ → ℝ} (hF : square_Cor61 p d F) :
    square_Cor61 p (d + 1) (F ∘ square_truncLast) := by
  obtain ⟨hFc, hconv, hhom, ψ, hψ, hper, hwit⟩ := hF
  have htc : Continuous (square_truncLast : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ → _) := by
    unfold square_truncLast; fun_prop
  have htadd : ∀ H K : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      square_truncLast (H + K) = square_truncLast H + square_truncLast K := fun H K => rfl
  have htsmul : ∀ (t : ℝ) (H : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
      square_truncLast (t • H) = t • square_truncLast H := fun t H => rfl
  have htsymm : ∀ H : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ, H.IsSymm →
      (square_truncLast H).IsSymm := fun H hH => by
    rw [Matrix.IsSymm, square_truncLast, Matrix.transpose_submatrix, hH.eq]
  have ht0 : square_truncLast (0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) = 0 := rfl
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  refine ⟨hFc.comp htc, fun H hH a => ?_, fun t H hH => ?_, ψ ∘ square_initCLM d,
    hψ.comp (square_initCLM d).contDiff, fun x z => ?_, ?_⟩
  · have e : (fun t : ℝ => (F ∘ square_truncLast) (H + t • Matrix.vecMulVec a a)) =
        fun t => F (square_truncLast H + t • Matrix.vecMulVec (a ∘ Fin.castSucc)
          (a ∘ Fin.castSucc)) := by
      funext t
      simp only [Function.comp_apply, htadd, htsmul]
      rfl
    rw [e]; exact hconv _ (htsymm H hH) _
  · simp only [Function.comp_apply, htsmul]; exact hhom t _ (htsymm H hH)
  · have : square_initCLM d (x + fun i => (z i : ℝ)) =
        square_initCLM d x + fun i => ((z ∘ Fin.castSucc) i : ℝ) := by
      funext i; rfl
    simp only [Function.comp_apply, this, hper]
  · have hint : ∀ y : Fin (d + 1) → ℝ, (F ∘ square_truncLast) (0 + hessian (ψ ∘ square_initCLM d) y) =
        F (0 + hessian ψ (square_initCLM d y)) := fun y => by
      simp only [Function.comp_apply, zero_add, square_truncLast_hessian hψ2]
    simp_rw [hint]
    have hgc : Continuous fun y : Fin d → ℝ => F (0 + hessian ψ y) :=
      hFc.comp (continuous_const.add (square_hess_continuous_hessian hψ))
    rw [square_integral_cube_succ (F := fun y => F (0 + hessian ψ (square_initCLM d y)))
      (hgc.comp (square_initCLM d).continuous) (Fin.last d)]
    have hins : ∀ (y : Fin d → ℝ) (t : ℝ),
        square_initCLM d ((Fin.last d).insertNth t y) = y := fun y t => by
      funext i
      simp only [square_initCLM_apply, Fin.insertNth_last', Fin.snoc_castSucc]
    simp only [Function.comp_apply, hins, square_integral_Ioo_const]
    simpa [Function.comp_apply, ht0] using hwit

/-- **Corollary 6.1 in all large dimensions**: from `square_Cor61` in dimension `d₀`, the
conclusion of Corollary 6.1 holds in every dimension `d ≥ d₀` (`square_cor61_succ`, by induction). -/
theorem square_cor61_ge {p : ℝ} {d₀ : ℕ} {F₀ : Matrix (Fin d₀) (Fin d₀) ℝ → ℝ}
    (hF₀ : square_Cor61 p d₀ F₀) :
    ∀ d ≥ d₀, ∃ F : Matrix (Fin d) (Fin d) ℝ → ℝ, square_Cor61 p d F := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => exact ⟨F₀, hF₀⟩
  | succ d _ ih =>
    obtain ⟨F, hF⟩ := ih
    exact ⟨_, square_cor61_succ hF⟩

/-- The proof of Corollary 6.1, with its periodic witness: `square_Cor61` in the dimension
`d = 2 m⁸` of the paper's proof (see `corollary6_1`). -/
theorem square_cor61_core (p : ℝ) (hp : 1 < p) :
    ∃ d : ℕ, 2 ≤ d ∧ ∃ F : Matrix (Fin d) (Fin d) ℝ → ℝ, square_Cor61 p d F := by
  have hp0 : 0 < p := by linarith
  have h4 : ENNReal.ofReal 4 = (4 : ℝ≥0∞) := by norm_num
  have hq4 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 4 := by rw [h4]; norm_num
  obtain ⟨Cp, hCp, hrc⟩ := proposition6_5_finite 4 (by norm_num) p hp
  -- the size `n = m⁸`, with `m > a (b + 1)`
  set a : ℝ := 4 * (2 : ℝ) ^ (1 / 4 : ℝ) * √p with ha
  set b : ℝ := Cp * (2 : ℝ) ^ (1 / 8 : ℝ) with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  set m : ℕ := ⌈a * (b + 1)⌉₊ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hmR : a * (b + 1) < m := by
    have := Nat.le_ceil (a * (b + 1)); push_cast [hm]; linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  set n : ℕ := m ^ 8 with hn
  have hn1 : 1 ≤ n := Nat.one_le_pow _ _ hm1
  have hd2 : 2 ≤ n + n := by omega
  have hdR : ((n + n : ℕ) : ℝ) = 2 * (m : ℝ) ^ 8 := by push_cast [hn]; ring
  have hm8 : ∀ k : ℕ, 0 < k → k ∣ 8 → ((m : ℝ) ^ 8) ^ (1 / (k : ℝ)) = (m : ℝ) ^ (8 / k) := by
    intro k hk hkd
    obtain ⟨j, hj⟩ := hkd
    have hkj : 8 / k = j := by rw [hj, Nat.mul_div_cancel_left _ hk]
    rw [hkj, hj, pow_mul', one_div, Real.pow_rpow_inv_natCast (by positivity) hk.ne']
  -- the constants: `(2n)^{1/8} = 2^{1/8} m`, `(2n)^{1/4} = 2^{1/4} m²`, `√(p n) = √p m⁴`
  have e8 : ((n + n : ℕ) : ℝ) ^ (1 / 4 - 1 / (2 * (4 : ℝ))) = (2 : ℝ) ^ (1 / 8 : ℝ) * m := by
    rw [show (1 / 4 - 1 / (2 * (4 : ℝ))) = 1 / ((8 : ℕ) : ℝ) by norm_num, hdR,
      Real.mul_rpow (by norm_num) (by positivity), hm8 8 (by norm_num) dvd_rfl]
    norm_num
  have e4 : ((n + n : ℕ) : ℝ) ^ (1 / 4 : ℝ) = (2 : ℝ) ^ (1 / 4 : ℝ) * (m : ℝ) ^ 2 := by
    rw [show (1 / 4 : ℝ) = 1 / ((4 : ℕ) : ℝ) by norm_num, hdR,
      Real.mul_rpow (by norm_num) (by positivity), hm8 4 (by norm_num) (by norm_num)]
  have esq : √(p * n) = √p * (m : ℝ) ^ 4 := by
    rw [Real.sqrt_mul hp0.le, hn]
    push_cast
    rw [show (m : ℝ) ^ 8 = ((m : ℝ) ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  -- `f_{p,4,C}` is rank-one convex at `0` for `C = C_p (2n)^{1/8} + 1` (Proposition 6.5)
  set X : ℝ := Cp * ((n + n : ℕ) : ℝ) ^ (1 / 4 - 1 / (2 * (4 : ℝ))) with hX
  have hX0 : 0 ≤ X := by positivity
  set C₁ : ℝ := X + 1 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hrc1 : RankOneConvexAt (kornF (n + n) p (ENNReal.ofReal 4) C₁) 0 := by
    have hlt : rcThreshold (kornF (n + n) p (ENNReal.ofReal 4)) < ENNReal.ofReal C₁ :=
      (hrc (n + n) hd2).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
    unfold rcThreshold at hlt
    obtain ⟨C', hC'⟩ := iInf_lt_iff.1 hlt
    obtain ⟨⟨hC'0, g, hgI, hgR, hgle, hg0⟩, hlt'⟩ := iInf_lt_iff.1 hC'
    have hCC' : C' ≤ C₁ := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt').1.le
    exact ⟨g, hgI, hgR, fun B => (hgle B).trans (square_kornF_mono hp0.le hC'0 hCC' B), by
      rw [hg0, square_kornF_zero hp0 hq4, square_kornF_zero hp0 hq4]⟩
  -- the envelope `f^{rc}` and `F = f^{rc} (J ·)`
  set f := kornF (n + n) p (ENNReal.ofReal 4) C₁ with hf
  have hfc : Continuous f := square_continuous_kornF hp0.le hq4 C₁
  obtain ⟨-, hGc, -, hGconv, hGle, hG0, hGhom⟩ :=
    square_env_rc hp hfc (square_kornF_hom hq4 C₁) hrc1
  set G : Matrix (Fin (n + n)) (Fin (n + n)) ℝ → ℝ := fun A => (rcEnvelope f A).toReal with hG
  set J := square_J n
  set F : Matrix (Fin (n + n)) (Fin (n + n)) ℝ → ℝ := fun H => G (J * H) with hF
  have hFc : Continuous F := hGc.comp (continuous_const.matrix_mul continuous_id)
  have hFhom : ∀ (t : ℝ) (H : Matrix (Fin (n + n)) (Fin (n + n)) ℝ), F (t • H) = |t| ^ p * F H :=
    fun t H => by simp only [F, Matrix.mul_smul]; exact hGhom t _
  have hF0 : F 0 = 0 := by simp only [F, Matrix.mul_zero]; exact hG0
  -- the witness: `∫ F (D²φ) ≤ ∫ f (J D²φ) < 0 = F (0)`
  set Hz : (Fin (n + n) → ℝ) → Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
    fun z => J * hessian (square_corWitness n) z with hHz
  have hHc : Continuous Hz := square_continuous_J_hessian n
  set S : (Fin (n + n) → ℝ) → ℝ := fun z => schattenNorm 4 ((1 / 2 : ℝ) • (Hz z + (Hz z)ᵀ))
    with hSdef
  set K : (Fin (n + n) → ℝ) → ℝ := fun z => schattenNorm 4 ((1 / 2 : ℝ) • (Hz z - (Hz z)ᵀ))
    with hKdef
  have hSc : Continuous S := square_cor_continuous_schattenNorm_four
    ((hHc.add hHc.matrix_transpose).const_smul (1 / 2 : ℝ))
  have hKc : Continuous K := square_cor_continuous_schattenNorm_four
    ((hHc.sub hHc.matrix_transpose).const_smul (1 / 2 : ℝ))
  have hS0 : ∀ z, 0 ≤ S z := fun z => schattenNorm_nonneg _ _
  have hK0 : ∀ z, 0 ≤ K z := fun z => schattenNorm_nonneg _ _
  have hSp : Continuous fun z => S z ^ p := hSc.rpow_const fun _ => Or.inr hp0.le
  have hKp : Continuous fun z => K z ^ p := hKc.rpow_const fun _ => Or.inr hp0.le
  have hcube : MeasurableSet (unitCube (n + n)) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hIS0 : 0 ≤ ∫ z in unitCube (n + n), S z ^ p :=
    setIntegral_nonneg hcube fun z _ => Real.rpow_nonneg (hS0 z) _
  have hIK0 : 0 ≤ ∫ z in unitCube (n + n), K z ^ p :=
    setIntegral_nonneg hcube fun z _ => Real.rpow_nonneg (hK0 z) _
  have hNS := square_cor_sym_upper n hp.le
  have hNK := square_cor_skew_lower hn1 hp.le
  -- `C U < L` with `U = 2 (2n)^{1/4} √(p n)`, `L = n / 2`
  have hCU : C₁ * (2 * ((n + n : ℕ) : ℝ) ^ (1 / 4 : ℝ) * √(p * n)) < (n : ℝ) / 2 := by
    rw [e4, esq, hC₁, hX, e8]
    have hnR : (n : ℝ) = (m : ℝ) ^ 8 := by rw [hn]; push_cast; ring
    rw [hnR]
    have key : a * (b * m + 1) < (m : ℝ) ^ 2 := by
      have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      calc a * (b * m + 1) = a * b * m + a * 1 := by ring
        _ ≤ a * b * m + a * m := by gcongr
        _ = a * (b + 1) * m := by ring
        _ < (m : ℝ) * m := mul_lt_mul_of_pos_right hmR hm0
        _ = (m : ℝ) ^ 2 := by ring
    have hm6 : (0 : ℝ) < (m : ℝ) ^ 6 := by positivity
    have : (Cp * ((2 : ℝ) ^ (1 / 8 : ℝ) * m) + 1) *
        (2 * ((2 : ℝ) ^ (1 / 4 : ℝ) * (m : ℝ) ^ 2) * (√p * (m : ℝ) ^ 4)) =
        a * (b * m + 1) * (m : ℝ) ^ 6 / 2 := by rw [ha, hb]; ring
    rw [this]
    calc a * (b * m + 1) * (m : ℝ) ^ 6 / 2 < (m : ℝ) ^ 2 * (m : ℝ) ^ 6 / 2 := by
          have := mul_lt_mul_of_pos_right key hm6; linarith
      _ = (m : ℝ) ^ 8 / 2 := by ring
  have hNS0 : 0 ≤ (∫ z in unitCube (n + n), S z ^ p) ^ (1 / p) := Real.rpow_nonneg hIS0 _
  have hlt2 : C₁ * (∫ z in unitCube (n + n), S z ^ p) ^ (1 / p) <
      (∫ z in unitCube (n + n), K z ^ p) ^ (1 / p) :=
    calc C₁ * (∫ z in unitCube (n + n), S z ^ p) ^ (1 / p) ≤
          C₁ * (2 * ((n + n : ℕ) : ℝ) ^ (1 / 4 : ℝ) * √(p * n)) :=
          mul_le_mul_of_nonneg_left hNS hC₁0
      _ < (n : ℝ) / 2 := hCU
      _ ≤ _ := hNK
  have hpow : ∀ I : ℝ, 0 ≤ I → (I ^ (1 / p)) ^ p = I := fun I hI => by
    rw [← Real.rpow_mul hI, one_div_mul_cancel hp0.ne', Real.rpow_one]
  have h3 : C₁ ^ p * ∫ z in unitCube (n + n), S z ^ p < ∫ z in unitCube (n + n), K z ^ p := by
    have := Real.rpow_lt_rpow (mul_nonneg hC₁0 hNS0) hlt2 hp0
    rwa [Real.mul_rpow hC₁0 hNS0, hpow _ hIS0, hpow _ hIK0] at this
  have hfHz : ∀ z, f (Hz z) = C₁ ^ p * S z ^ p - K z ^ p := fun z => by
    simp only [hf, kornF, h4, S, K]
    rfl
  have hwit : ∫ z in unitCube (n + n), F (0 + hessian (square_corWitness n) z) < F 0 := by
    rw [hF0]
    have hle : ∫ z in unitCube (n + n), F (0 + hessian (square_corWitness n) z) ≤
        ∫ z in unitCube (n + n), (C₁ ^ p * S z ^ p - K z ^ p) := by
      refine setIntegral_mono (square_integrableOn_cube (hFc.comp
        (continuous_const.add (square_hess_continuous_hessian (square_corWitness_contDiff n)))))
        (square_integrableOn_cube ((continuous_const.mul hSp).sub hKp)) fun z => ?_
      simp only [zero_add, F]
      rw [← hfHz]
      exact hGle _
    rw [integral_sub ((square_integrableOn_cube hSp).const_mul _) (square_integrableOn_cube hKp),
      integral_const_mul] at hle
    linarith
  refine ⟨n + n, hd2, F, hFc, ?_, fun t H _ => hFhom t H, square_corWitness n,
    square_corWitness_contDiff n, square_corWitness_periodic n, hwit⟩
  -- `J (H + t a ⊗ a) = J H + t (J a) ⊗ a`, a rank-one line
  intro H _ v
  have hR : (J * Matrix.vecMulVec v v).rank ≤ 1 := by
    rw [Matrix.mul_vecMulVec]; exact Matrix.rank_vecMulVec_le _ _
  have := hGconv (J * H) (J * Matrix.vecMulVec v v) hR
  simpa only [F, Matrix.mul_add, Matrix.mul_smul] using this

/-- **Corollary 6.1** (`cor:symm`): for every `p ∈ (1, ∞)` there are `d` and an integrand
`F : Sym (d) → ℝ`, rank-one convex (convex along the lines `H + t a ⊗ a`) and `p`-homogeneous,
which is not Hessian quasiconvex at `0`, and hence is nowhere Hessian quasiconvex. `F` is given
on all of `ℝ^{d×d}`; only its values on symmetric matrices enter. The proof uses the bound of
the case `q ∈ (2, ∞)` of Proposition 6.5 (`proposition6_5_finite`), and through it
Propositions 2.7 (1), (2), 2.8, 6.3 and 6.4, all proved (`Morrey/Cassese/Hypotheses.lean`; the
hypercontractive bound, `KahaneKhintchineHypercontractive`, is not used). The proof is
`square_cor61_core` (which also gives the periodic witness) and
`square_cor61_conclusion`; `corollary6_1_ge` extends the conclusion to every larger `d`.

Proof (the paper's), with `q = 4` and `d = 2n`, `n = m⁸` large: `J = diag (I_n, −I_n)`
(`square_J`) and `F (H) = f^{rc}_{p,4,C} (J H)`, with `f_{p,4,C}` the integrand (30) and
`C = C_p (2n)^{1/8} + 1`, just above the bound `C^{rc} (S_4^{2n×2n}, p) ≤ C_p (2n)^{1/8}` of
Proposition 6.5, so that `f_{p,4,C}` is rank-one convex at `0`. The envelope `f^{rc}` is a
continuous, rank-one convex, `p`-homogeneous integrand `≤ f` with `f^{rc} (0) = 0`
(`square_env_rc`: Definition 2.3, Lemma 2.1, Proposition 2.3 (a)); since
`J (H + t a ⊗ a) = J H + t (J a) ⊗ a` is an ordinary rank-one line, `F` is convex along Hessian
rank-one lines. On `𝕋^{2n}` the witness `φ (x, y) = Σ_{i,j} sin (x_i − y_j)`
(`square_corWitness`, on the unit torus) has, by the calculation of Proposition 6.1
(`square_cor_skew_lower`, `square_cor_sym_upper`),
`‖Skew (J D²φ)‖_{L^p (S_4)} ≥ n / 2` and `‖Sym (J D²φ)‖_{L^p (S_4)} ≤ 2 (2n)^{1/4} √(p n)`, a
ratio `n^{1/4} / (4 · 2^{1/4} √p) > C` for `n = m⁸` large. Hence
`∫ F (D²φ) ≤ ∫ f_{p,4,C} (J D²φ) < 0 = F (0)`, and `F` is not Hessian quasiconvex at `0`
(`not_hessianQuasiconvexAt_of_periodic`, `cs-hess-periodic`). "Hence nowhere": for symmetric
`A`, `F (A + λ D²φ) = λ^p F (λ⁻¹ A + D²φ)`, and `λ → ∞` (`square_not_hessianQuasiconvexAt_of_zero`,
the Hessian analogue of the consequence of Proposition 2.3 that is
`quasiconvexAt_zero_of_quasiconvexAt`). -/
theorem corollary6_1 (p : ℝ) (hp : 1 < p) :
    ∃ (d : ℕ) (F : Matrix (Fin d) (Fin d) ℝ → ℝ), IsIntegrand F ∧
      (∀ H : Matrix (Fin d) (Fin d) ℝ, H.IsSymm → ∀ a : Fin d → ℝ,
        ConvexOn ℝ Set.univ fun t : ℝ => F (H + t • Matrix.vecMulVec a a)) ∧
      (∀ (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ), H.IsSymm → F (t • H) = |t| ^ p * F H) ∧
      ¬ HessianQuasiconvexAt F 0 ∧
      ∀ A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm → ¬ HessianQuasiconvexAt F A := by
  obtain ⟨d, -, F, hF⟩ := square_cor61_core p hp
  exact ⟨d, F, square_cor61_conclusion (by linarith) hF⟩

/-- **Corollary 6.1 in every large dimension**: for every `p ∈ (1, ∞)` there is `d₀` such that
for every `d ≥ d₀` there is an integrand `F : Sym (d) → ℝ` as in Corollary 6.1. The paper states
Corollary 6.1 for one `d` ("there are `d` and `F`"; `corollary6_1`); this extension to all larger
`d` is the trivial embedding `F_{d+1} (H) = F_d (H')`, `H'` the upper left `d × d` block of `H`
(`square_cor61_succ`, `square_cor61_ge`). -/
theorem corollary6_1_ge (p : ℝ) (hp : 1 < p) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ F : Matrix (Fin d) (Fin d) ℝ → ℝ, IsIntegrand F ∧
      (∀ H : Matrix (Fin d) (Fin d) ℝ, H.IsSymm → ∀ a : Fin d → ℝ,
        ConvexOn ℝ Set.univ fun t : ℝ => F (H + t • Matrix.vecMulVec a a)) ∧
      (∀ (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ), H.IsSymm → F (t • H) = |t| ^ p * F H) ∧
      ¬ HessianQuasiconvexAt F 0 ∧
      ∀ A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm → ¬ HessianQuasiconvexAt F A := by
  obtain ⟨d₀, -, F₀, hF₀⟩ := square_cor61_core p hp
  refine ⟨d₀, fun d hd => ?_⟩
  obtain ⟨F, hF⟩ := square_cor61_ge hF₀ d hd
  exact ⟨F, square_cor61_conclusion (by linarith) hF⟩

/-! ### Section 6.3: the integrand `h_{4,4,C}` and the witness of Proposition 6.6 -/

section SquareFour

open Real

/-- `h_{4,4,C}` as a trace polynomial: `C⁴ tr ((XᵀX)²) − tr ((YᵀY)²)`, `X = Sym_{1/2} (A)`,
`Y = Skew (A)` (`‖·‖_{S_4}⁴ = tr ((·ᵀ ·)²)`). -/
theorem square_hF_eq (C : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    hF d 4 4 C A = C ^ 4 * ((symHalfPart A)ᵀ * symHalfPart A * ((symHalfPart A)ᵀ * symHalfPart A)).trace -
      ((skewPart A)ᵀ * skewPart A * ((skewPart A)ᵀ * skewPart A)).trace := by
  rw [hF, square_schattenNorm_four_rpow, square_schattenNorm_four_rpow,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem square_continuous_symHalfPart :
    Continuous (symHalfPart : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) := by
  unfold symHalfPart symPart
  fun_prop

/-- `h_{4,4,C}` is continuous (a polynomial in the entries). -/
theorem square_continuous_hF (C : ℝ) : Continuous (hF d 4 4 C) := by
  have h1 := square_continuous_symHalfPart (d := d)
  have h2 := square_continuous_skewPart (d := d)
  rw [show hF d 4 4 C = fun A => C ^ 4 * ((symHalfPart A)ᵀ * symHalfPart A *
      ((symHalfPart A)ᵀ * symHalfPart A)).trace -
      ((skewPart A)ᵀ * skewPart A * ((skewPart A)ᵀ * skewPart A)).trace from
    funext (square_hF_eq C)]
  fun_prop

theorem square_hF_zero (C : ℝ) : hF d 4 4 C 0 = 0 := by
  have h1 : symHalfPart (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
    simp only [symHalfPart, symPart, Matrix.transpose_zero, add_zero, smul_zero,
      Matrix.trace_zero, mul_zero, zero_smul, sub_zero]
  have h2 : skewPart (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
    simp only [skewPart, Matrix.transpose_zero, sub_zero, smul_zero]
  rw [square_hF_eq C, h1, h2]
  simp only [Matrix.transpose_zero, Matrix.trace_zero, mul_zero, sub_zero]

/-- An antisymmetric double sum vanishes. -/
theorem square_sum_sum_antisymm {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f j i = -f i j) :
    ∑ i, ∑ j, f i j = 0 := by
  have h : ∑ i, ∑ j, f i j = ∑ i, ∑ j, -f i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hf i j
  simp only [Finset.sum_neg_distrib] at h
  linarith

/-- The parts of the gradient of the witness (proof of Proposition 6.1): with `θ = 2π x`,
`a = sin θ`, `b = cos θ`, `Skew (∇w) = a ⊗ b − b ⊗ a`, `tr (∇w) = 0` and
`Sym_{1/2} (∇w) = Sym (∇w) = diag (A b − B a) = diag (−Σ_j sin (θ_i − θ_j))`. -/
theorem square_witness_parts (x : Fin d → ℝ) :
    skewPart (jac (squareWitness d) x) = (Matrix.of fun i k =>
      sin (2 * π * x i) * cos (2 * π * x k) - cos (2 * π * x i) * sin (2 * π * x k)) ∧
    symHalfPart (jac (squareWitness d) x) =
      Matrix.diagonal fun i => -∑ j, sin (2 * π * (x i - x j)) := by
  have htr : (jac (squareWitness d) x).trace = 0 := by
    rw [jac_squareWitness, Matrix.trace]
    simp only [Matrix.diag, Matrix.of_apply, sub_self, mul_zero, sin_zero, ↓reduceIte, zero_sub,
      Finset.sum_neg_distrib, neg_eq_zero]
    exact square_sum_sum_antisymm _ fun i j => by rw [← sin_neg]; ring_nf
  refine ⟨?_, ?_⟩
  · ext i k
    simp only [skewPart, jac_squareWitness, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul]
    by_cases h : i = k
    · subst h; simp only [↓reduceIte]; ring
    · simp only [h, Ne.symm h, ↓reduceIte,
        show 2 * π * (x k - x i) = -(2 * π * (x i - x k)) by ring, sin_neg,
        show 2 * π * (x i - x k) = 2 * π * x i - 2 * π * x k by ring, sin_sub]
      ring
  · rw [symHalfPart, htr, mul_zero, zero_smul, sub_zero]
    ext i k
    simp only [symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      jac_squareWitness, Matrix.of_apply, smul_eq_mul, Matrix.diagonal_apply]
    by_cases h : i = k
    · subst h; simp only [↓reduceIte, sub_self, mul_zero, sin_zero]; ring
    · simp only [h, Ne.symm h, ↓reduceIte,
        show 2 * π * (x k - x i) = -(2 * π * (x i - x k)) by ring, sin_neg]
      ring

/-- `h_{4,4,C} (∇w)` along the witness: with `θ = 2π x`,
`C⁴ Σ_i (Σ_j sin (θ_i − θ_j))⁴ − (d² − |W|²)² / 8`, `W = Σ_k e^{2iθ_k}`
(`‖Skew (∇w)‖_{S_4}⁴ = 2σ⁴`, `4σ² = d² − |W|²`). -/
theorem square_hF_witness (C : ℝ) (x : Fin d → ℝ) :
    hF d 4 4 C (0 + jac (squareWitness d) x) =
      C ^ 4 * ∑ i, (∑ j, sin (2 * π * (x i - x j))) ^ 4 -
        ((d : ℝ) ^ 2 - ((∑ k, cos (4 * π * x k)) ^ 2 + (∑ k, sin (4 * π * x k)) ^ 2)) ^ 2 / 8 := by
  obtain ⟨hK, hS⟩ := square_witness_parts (d := d) x
  rw [zero_add, square_hF_eq C, hK, hS, square_trace_diagonal_four,
    square_trace_skew_rank_two]
  have hsum : ∀ i, (-∑ j, sin (2 * π * (x i - x j))) ^ 4 = (∑ j, sin (2 * π * (x i - x j))) ^ 4 :=
    fun i => by ring
  simp_rw [hsum]
  set α := ∑ i, sin (2 * π * x i) ^ 2
  set β := ∑ i, cos (2 * π * x i) ^ 2
  set γ := ∑ i, sin (2 * π * x i) * cos (2 * π * x i)
  have hd : α + β = d := by
    rw [← Finset.sum_add_distrib]
    simp [sin_sq_add_cos_sq]
  have hP : ∑ k, cos (4 * π * x k) = β - α := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 4 * π * x k = 2 * (2 * π * x k) by ring, cos_two_mul]
    have := sin_sq_add_cos_sq (2 * π * x k)
    linarith
  have hQ : ∑ k, sin (4 * π * x k) = 2 * γ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show 4 * π * x k = 2 * (2 * π * x k) by ring, sin_two_mul]
    ring
  rw [hP, hQ, ← hd]
  ring

/-- `∫_{(0,1)^d} (Σ_j sin (θ_i − θ_j))⁴ = (d − 1) (6d − 9) / 8` for each `i`, with
`d = n + 1`: separating the coordinate `i`, the `d − 1` variables `sin (θ_i − θ_j)`, `j ≠ i`, are
independent with means `0`, second moments `1/2` and fourth moments `3/8`. -/
theorem square_integral_sym_witness (n : ℕ) (i : Fin (n + 1)) :
    ∫ x in unitCube (n + 1), (∑ j, sin (2 * π * (x i - x j))) ^ 4 =
      3 * n * (2 * n - 1) / 8 := by
  rw [square_integral_cube_succ' (by fun_prop) i]
  have hin : ∀ t : ℝ, ∫ y in unitCube n,
      (∑ j, sin (2 * π * ((Fin.insertNth i t y : Fin (n + 1) → ℝ) i -
        (Fin.insertNth i t y : Fin (n + 1) → ℝ) j))) ^ 4 = 3 * n * (2 * n - 1) / 8 := by
    intro t
    have hsplit : ∀ y : Fin n → ℝ, ∑ j, sin (2 * π * ((Fin.insertNth i t y : Fin (n + 1) → ℝ) i -
        (Fin.insertNth i t y : Fin (n + 1) → ℝ) j)) = ∑ k, sin (2 * π * (t - y k)) := by
      intro y
      rw [Fin.sum_univ_succAbove _ i]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, sub_self, mul_zero,
        sin_zero, zero_add]
    simp_rw [hsplit]
    have := (square_moments_sum (g := fun s => sin (2 * π * (t - s))) (by fun_prop)
      (square_integral_sin_shift t) (square_integral_sin_shift_sq t)
      (square_integral_sin_shift_pow_four t) n).2.2
    rw [this]; ring
  simp_rw [hin]
  rw [square_integral_Ioo_const]

/-- **The moments of Proposition 6.6** (inventory E6): along the witness,
`∫ h_{4,4,C} (∇w) = C⁴ d (d − 1) (6d − 9) / 8 − d (d − 1) (d² − d + 1) / 8`, from
`E ‖Sym (∇w)‖_{S_4}⁴ = d (d − 1) (6d − 9) / 8` and `E ‖Skew (∇w)‖_{S_4}⁴ = d (d − 1) (d² − d + 1) / 8`
(with `E |W|² = d`, `E |W|⁴ = 2d² − d`). -/
theorem square_integral_hF_witness (n : ℕ) (C : ℝ) :
    ∫ x in unitCube (n + 1), hF (n + 1) 4 4 C (0 + jac (squareWitness (n + 1)) x) =
      C ^ 4 * ((n + 1) * (3 * n * (2 * n - 1) / 8)) -
        (n + 1) * n * ((n + 1) ^ 2 - (n + 1) + 1) / 8 := by
  simp_rw [square_hF_witness C]
  set R : (Fin (n + 1) → ℝ) → ℝ := fun x =>
    (∑ k, cos (4 * π * x k)) ^ 2 + (∑ k, sin (4 * π * x k)) ^ 2 with hR
  have hRc : Continuous R := by simp only [hR]; fun_prop
  have hW := square_moments_walk (n + 1)
  rw [integral_sub, integral_const_mul, integral_finsetSum]
  · simp_rw [square_integral_sym_witness]
    have hq := square_integral_cube_quartic hRc (((n + 1 : ℕ) : ℝ) ^ 4 / 8)
      (-(2 * ((n + 1 : ℕ) : ℝ) ^ 2) / 8) (1 / 8) 0 0
    rw [hW.1, hW.2] at hq
    have : ∫ x in unitCube (n + 1), ((((n + 1 : ℕ) : ℝ)) ^ 2 - R x) ^ 2 / 8 =
        ∫ x in unitCube (n + 1), (((n + 1 : ℕ) : ℝ) ^ 4 / 8 +
          (-(2 * ((n + 1 : ℕ) : ℝ) ^ 2) / 8) * R x + 1 / 8 * R x ^ 2 + 0 * R x ^ 3 +
          0 * R x ^ 4) := by
      congr 1; funext x; ring
    simp only [hR] at this hq
    rw [this, hq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  · exact fun i _ => square_integrableOn_cube (by fun_prop)
  · exact (square_integrableOn_cube (by fun_prop)).const_mul _
  · exact square_integrableOn_cube (by fun_prop)

end SquareFour

/-! ### Proposition 6.1: the quasiconvex lower bound -/

section Prop61

open Real

/-- `tr ∇w = 0` for the witness of Propositions 6.1 and 6.6. -/
theorem square_trace_jac_witness (x : Fin d → ℝ) : (jac (squareWitness d) x).trace = 0 := by
  rw [jac_squareWitness, Matrix.trace]
  simp only [Matrix.diag, Matrix.of_apply, sub_self, mul_zero, sin_zero, ↓reduceIte, zero_sub,
    Finset.sum_neg_distrib, neg_eq_zero]
  exact square_sum_sum_antisymm _ fun i j => by rw [← sin_neg]; ring_nf

/-- `Sym (∇w) = diag (A b − B a) = diag (−Σ_j sin (θ_i − θ_j))` (proof of Proposition 6.1). -/
theorem square_symPart_witness (x : Fin d → ℝ) :
    symPart (jac (squareWitness d) x) =
      Matrix.diagonal fun i => -∑ j, sin (2 * π * (x i - x j)) := by
  rw [← (square_witness_parts x).2, symHalfPart, square_trace_jac_witness, mul_zero, zero_smul,
    sub_zero]

/-- `|Σ_j sin (θ_i − θ_j)| = |Z| |sin (φ − θ_i)| ≤ |Z|`, `Z = Σ_j e^{iθ_j}` (proof of
Proposition 6.1). -/
theorem square_abs_sum_sin_le (x : Fin d → ℝ) (i : Fin d) :
    |∑ j, sin (2 * π * (x i - x j))| ≤ ‖square_zc x‖ := by
  set A := ∑ j, sin (2 * π * x j)
  set B := ∑ j, cos (2 * π * x j)
  have he : ∑ j, sin (2 * π * (x i - x j)) = sin (2 * π * x i) * B - cos (2 * π * x i) * A := by
    simp only [B, A, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 2 * π * (x i - x j) = 2 * π * x i - 2 * π * x j by ring, sin_sub]
  have h : (∑ j, sin (2 * π * (x i - x j))) ^ 2 ≤ ‖square_zc x‖ ^ 2 := by
    rw [square_norm_zc_sq, he]
    have h1 := sin_sq_add_cos_sq (2 * π * x i)
    have key : (sin (2 * π * x i) * B - cos (2 * π * x i) * A) ^ 2 +
        (sin (2 * π * x i) * A + cos (2 * π * x i) * B) ^ 2 =
        (sin (2 * π * x i) ^ 2 + cos (2 * π * x i) ^ 2) * (A ^ 2 + B ^ 2) := by ring
    rw [h1, one_mul] at key
    nlinarith [sq_nonneg (sin (2 * π * x i) * A + cos (2 * π * x i) * B)]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1 (by rw [sq_abs]; exact h)

/-- The witness is Lipschitz: it is smooth and `ℤ^d`-periodic, so its derivative is bounded. -/
theorem square_lipschitz_witness : ∃ K, LipschitzWith K (squareWitness d) := by
  have hc1 : ContDiff ℝ 1 (squareWitness d) := squareWitness_contDiff.of_le (by simp)
  have hdiff : Differentiable ℝ (squareWitness d) := hc1.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ (squareWitness d)) := hc1.continuous_fderiv one_ne_zero
  have hper : ∀ x (z : Fin d → ℤ), fderiv ℝ (squareWitness d) (x + fun i => (z i : ℝ)) =
      fderiv ℝ (squareWitness d) x := by
    intro x z
    have h : (fun y => squareWitness d (y + fun i => (z i : ℝ))) = squareWitness d :=
      funext fun y => squareWitness_periodic y z
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := squareWitness d) (x := x) (fun i => (z i : ℝ))
    rw [h] at this
    exact this.symm
  obtain ⟨U, hU0, hU⟩ := Sverak.l1_periodic_bounded hcont hper
  refine ⟨U.toNNReal, lipschitzWith_of_nnnorm_fderiv_le hdiff fun x => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hU0]
  exact hU x

/-- `σ² = |a|² |b|² − ⟨a, b⟩²` for `a = sin θ`, `b = cos θ` (proof of Proposition 6.1). -/
noncomputable def square_sig2 (x : Fin d → ℝ) : ℝ :=
  (∑ j, sin (2 * π * x j) ^ 2) * (∑ j, cos (2 * π * x j) ^ 2) -
    (∑ j, sin (2 * π * x j) * cos (2 * π * x j)) ^ 2

theorem square_continuous_sig2 : Continuous (square_sig2 (d := d)) := by
  unfold square_sig2; fun_prop

/-- `‖Skew (∇w)‖_{S_q} = 2^{1/q} σ`: `Skew (∇w) = a ⊗ b − b ⊗ a`, whose only possibly nonzero
singular values are both equal to `σ` (proof of Proposition 6.1). -/
theorem square_schattenNorm_skew_witness {q : ℝ≥0∞} (hq : 1 ≤ q) (x : Fin d → ℝ) :
    schattenNorm q (skewPart (jac (squareWitness d) x)) =
      (2 : ℝ) ^ (1 / q.toReal) * √(square_sig2 x) := by
  rw [(square_witness_parts x).1]
  exact square_schattenNorm_skew_two (fun i => sin (2 * π * x i)) (fun i => cos (2 * π * x i)) hq

/-- `σ ≤ d` (from `σ² = αβ − γ² ≤ αβ ≤ (α + β)² = d²`, `α + β = d`; the sharper `σ ≤ d / 2`,
from `αβ ≤ (α + β)² / 4`, is not needed). -/
theorem square_sqrt_sig2_le (x : Fin d → ℝ) : √(square_sig2 x) ≤ d := by
  set α := ∑ j, sin (2 * π * x j) ^ 2
  set β := ∑ j, cos (2 * π * x j) ^ 2
  set γ := ∑ j, sin (2 * π * x j) * cos (2 * π * x j)
  have hd : α + β = d := by
    rw [← Finset.sum_add_distrib]
    simp [sin_sq_add_cos_sq]
  have hα : 0 ≤ α := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hβ : 0 ≤ β := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hle : square_sig2 x ≤ (d : ℝ) ^ 2 := by
    show α * β - γ ^ 2 ≤ (d : ℝ) ^ 2
    rw [← hd]; nlinarith [sq_nonneg γ]
  calc √(square_sig2 x) ≤ √((d : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
    _ = d := Real.sqrt_sq (Nat.cast_nonneg d)

/-- `E σ² = d (d − 1) / 4`: `4σ² = d² − |W|²` with `W = Σ_k e^{2iθ_k}` and `E |W|² = d`. -/
theorem square_integral_sig2 :
    ∫ x in unitCube d, square_sig2 x = ((d : ℝ) ^ 2 - d) / 4 := by
  have hpt : ∀ x : Fin d → ℝ, square_sig2 x =
      ((d : ℝ) ^ 2 - ((∑ k, cos (4 * π * x k)) ^ 2 + (∑ k, sin (4 * π * x k)) ^ 2)) / 4 := by
    intro x
    set α := ∑ j, sin (2 * π * x j) ^ 2
    set β := ∑ j, cos (2 * π * x j) ^ 2
    set γ := ∑ j, sin (2 * π * x j) * cos (2 * π * x j)
    have hd : α + β = d := by
      rw [← Finset.sum_add_distrib]
      simp [sin_sq_add_cos_sq]
    have hP : ∑ k, cos (4 * π * x k) = β - α := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show 4 * π * x k = 2 * (2 * π * x k) by ring, cos_two_mul]
      have := sin_sq_add_cos_sq (2 * π * x k)
      linarith
    have hQ : ∑ k, sin (4 * π * x k) = 2 * γ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show 4 * π * x k = 2 * (2 * π * x k) by ring, sin_two_mul]
      ring
    show α * β - γ ^ 2 = _
    rw [hP, hQ, ← hd]
    ring
  simp_rw [hpt]
  rw [integral_div, integral_sub (square_integrableOn_cube continuous_const)
    (square_integrableOn_cube (by fun_prop)), square_integral_cube_const,
    (square_moments_walk d).1]

/-- **Proposition 6.1** (`prop:qcboundsquare`): for `q ∈ [2, ∞]` there is `c_q > 0` such that for
every `d ≥ 2` and `p ∈ [1, ∞)`, `C^{qc} (S_q^{d×d}, p) ≥ c_q d^{1 − 1/q} / min (√(d p), d)`.

Proof (the paper's), with `c_q = 1/8` for every `q`. The witness is
`u_i (x) = Σ_{j ≠ i} cos (x_i − x_j)` on `𝕋^d`, here `w = squareWitness d` on the unit torus
(`∇w (x) = ∇u (2πx)`, `θ = 2πx`); it is smooth, periodic and Lipschitz, so a strict inequality
`∫ f_{p,q,C} (∇w) < 0 = f_{p,q,C} (0)` refutes quasiconvexity at `0` (Lemma 2.2, the periodic
characterization `External.Rindler.quasiconvexAtOn_iff_periodic`, the paper's formula for
`C^{qc}` as a supremum over `C^∞ (𝕋^d, ℝ^d)`), and `C^{qc} ≥ ‖Skew ∇w‖_{L^p (S_q)} /
‖Sym ∇w‖_{L^p (S_q)}`.
* `Skew (∇w) = a ⊗ b − b ⊗ a` (`square_witness_parts`), with both nonzero singular values equal to
  `σ`, so `‖Skew (∇w)‖_{S_q} = 2^{1/q} σ` (`square_schattenNorm_skew_witness`); since
  `E σ² = d (d − 1) / 4` (`square_integral_sig2`) and `σ ≤ d` (`square_sqrt_sig2_le`),
  `‖σ‖_{L^p} ≥ E σ ≥ E σ² / d = (d − 1) / 4` (monotonicity of `L^p` norms,
  `square_cube_lp_mono`), so `‖Skew (∇w)‖_{L^p (S_q)} ≥ (d − 1) / 4 ≥ d / 8`.
* `Sym (∇w) = diag (−Σ_j sin (θ_i − θ_j))` (`square_symPart_witness`) with
  `|Σ_j sin (θ_i − θ_j)| ≤ |Z|`, `Z = Σ_j e^{iθ_j}` (`square_abs_sum_sin_le`), so
  `‖Sym (∇w)‖_{S_q} ≤ d^{1/q} |Z|` (`square_schattenNorm_diagonal_le`, also for `q = ∞`); and
  `|Z| ≤ d`, `‖Z‖_{L^p} ≤ √(p d)` (`square_lp_zc_le`: the exact moments
  `E |Z|^{2m} = Σ_{k₁ + ⋯ + k_d = m} (m; k₁, …, k_d)² ≤ m! d^m`, `square_moment_zc_eq` and
  `square_moment_zc`, and monotonicity of `L^p` norms), so
  `‖Sym (∇w)‖_{L^p (S_q)} ≤ d^{1/q} min (√(d p), d)`.
The ratio is at least `d^{1 − 1/q} / (8 min (√(d p), d))`. -/
theorem proposition6_1 (q : ℝ≥0∞) (hq : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ p : ℝ, 1 ≤ p →
      ENNReal.ofReal (c * (d : ℝ) ^ (1 - 1 / q.toReal) / min (√((d : ℝ) * p)) d) ≤
        qcThreshold (kornF d p q) := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := le_trans (by norm_num) hq
  refine ⟨1 / 8, by norm_num, fun d hd p hp => ?_⟩
  have hp0 : 0 < p := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  set r := 1 / q.toReal with hr
  have hr0 : 0 ≤ r := by positivity
  set μ := min (√((d : ℝ) * p)) d with hμ
  have hμ0 : 0 < μ := lt_min (Real.sqrt_pos.2 (by positivity)) hd0
  have hcube : MeasurableSet (unitCube d) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  -- the parts of `∇w`
  set S : (Fin d → ℝ) → ℝ := fun x => schattenNorm q (symPart (0 + jac (squareWitness d) x))
    with hSdef
  set K : (Fin d → ℝ) → ℝ := fun x => schattenNorm q (skewPart (0 + jac (squareWitness d) x))
    with hKdef
  have hSc : Continuous S :=
    Sverak.gen_continuous_comp_jac ((square_continuous_schattenNorm hq1).comp
      square_continuous_symPart) 0 squareWitness_contDiff
  have hKc : Continuous K :=
    Sverak.gen_continuous_comp_jac ((square_continuous_schattenNorm hq1).comp
      square_continuous_skewPart) 0 squareWitness_contDiff
  have hS0 : ∀ x, 0 ≤ S x := fun x => schattenNorm_nonneg _ _
  have hK0 : ∀ x, 0 ≤ K x := fun x => schattenNorm_nonneg _ _
  have hSp : Continuous fun x => S x ^ p := hSc.rpow_const fun _ => Or.inr hp0.le
  have hKp : Continuous fun x => K x ^ p := hKc.rpow_const fun _ => Or.inr hp0.le
  have hIS0 : 0 ≤ ∫ x in unitCube d, S x ^ p :=
    setIntegral_nonneg hcube fun x _ => Real.rpow_nonneg (hS0 x) _
  have hIK0 : 0 ≤ ∫ x in unitCube d, K x ^ p :=
    setIntegral_nonneg hcube fun x _ => Real.rpow_nonneg (hK0 x) _
  -- `‖Sym (∇w)‖_{L^p (S_q)} ≤ d^{1/q} min (√(d p), d)`
  have hNS : (∫ x in unitCube d, S x ^ p) ^ (1 / p) ≤ (d : ℝ) ^ r * μ := by
    have hZc := square_continuous_zc (n := d)
    have hSle : ∀ x, S x ≤ (d : ℝ) ^ r * ‖square_zc x‖ := fun x => by
      simp only [S, zero_add, square_symPart_witness]
      exact square_schattenNorm_diagonal_le _ (norm_nonneg _) (fun i => by
        rw [abs_neg]; exact square_abs_sum_sin_le x i) hq1
    have hZp : Continuous fun x => ‖square_zc x‖ ^ p :=
      hZc.norm.rpow_const fun _ => Or.inr hp0.le
    have hIZ0 : 0 ≤ ∫ x in unitCube d, ‖square_zc x‖ ^ p :=
      setIntegral_nonneg hcube fun x _ => Real.rpow_nonneg (norm_nonneg _) _
    have h1 : ∫ x in unitCube d, S x ^ p ≤
        ((d : ℝ) ^ r) ^ p * ∫ x in unitCube d, ‖square_zc x‖ ^ p := by
      rw [← integral_const_mul]
      refine setIntegral_mono (square_integrableOn_cube hSp)
        (square_integrableOn_cube (continuous_const.mul hZp)) fun x => ?_
      rw [← Real.mul_rpow (by positivity) (norm_nonneg _)]
      exact Real.rpow_le_rpow (hS0 x) (hSle x) hp0.le
    have hZμ : (∫ x in unitCube d, ‖square_zc x‖ ^ p) ^ (1 / p) ≤ μ := by
      refine le_min ?_ (square_lp_zc_le_card d hp0)
      rw [mul_comm]; exact square_lp_zc_le d hp
    calc (∫ x in unitCube d, S x ^ p) ^ (1 / p) ≤
          (((d : ℝ) ^ r) ^ p * ∫ x in unitCube d, ‖square_zc x‖ ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow hIS0 h1 (by positivity)
      _ = (d : ℝ) ^ r * (∫ x in unitCube d, ‖square_zc x‖ ^ p) ^ (1 / p) := by
          rw [Real.mul_rpow (by positivity) hIZ0, ← Real.rpow_mul (by positivity),
            mul_one_div_cancel hp0.ne', Real.rpow_one]
      _ ≤ (d : ℝ) ^ r * μ := mul_le_mul_of_nonneg_left hZμ (by positivity)
  -- `‖Skew (∇w)‖_{L^p (S_q)} ≥ (d − 1) / 4 ≥ d / 8`
  have hNK : (d : ℝ) / 8 ≤ (∫ x in unitCube d, K x ^ p) ^ (1 / p) := by
    have hsc : Continuous fun x : Fin d → ℝ => √(square_sig2 x) :=
      Real.continuous_sqrt.comp square_continuous_sig2
    have hsig : ∀ x, √(square_sig2 x) ≤ K x := fun x => by
      simp only [K, zero_add]
      rw [square_schattenNorm_skew_witness hq1 x]
      exact le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_rpow (by norm_num) hr0)
    have hlow : ∀ x : Fin d → ℝ, square_sig2 x / d ≤ √(square_sig2 x) := fun x => by
      rw [div_le_iff₀ hd0]
      have h0 : 0 ≤ square_sig2 x := square_skew_two_sigma_nonneg _ _
      calc square_sig2 x = √(square_sig2 x) * √(square_sig2 x) := (Real.mul_self_sqrt h0).symm
        _ ≤ √(square_sig2 x) * d :=
            mul_le_mul_of_nonneg_left (square_sqrt_sig2_le x) (Real.sqrt_nonneg _)
    have hsp : Continuous fun x => √(square_sig2 x) ^ p := hsc.rpow_const fun _ => Or.inr hp0.le
    calc (d : ℝ) / 8 ≤ ((d : ℝ) ^ 2 - d) / 4 / d := by
          rw [le_div_iff₀ hd0]; nlinarith
      _ = ∫ x in unitCube d, square_sig2 x / d := by rw [integral_div, square_integral_sig2]
      _ ≤ ∫ x in unitCube d, √(square_sig2 x) :=
          setIntegral_mono (square_integrableOn_cube (square_continuous_sig2.div_const _))
            (square_integrableOn_cube hsc) hlow
      _ = (∫ x in unitCube d, √(square_sig2 x) ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) := by
          simp only [Real.rpow_one, div_one]
      _ ≤ (∫ x in unitCube d, √(square_sig2 x) ^ p) ^ (1 / p) :=
          square_cube_lp_mono hsc (fun x => Real.sqrt_nonneg _) one_pos hp
      _ ≤ (∫ x in unitCube d, K x ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow (setIntegral_nonneg hcube fun x _ =>
              Real.rpow_nonneg (Real.sqrt_nonneg _) _)
            (setIntegral_mono (square_integrableOn_cube hsp) (square_integrableOn_cube hKp)
              fun x => Real.rpow_le_rpow (Real.sqrt_nonneg _) (hsig x) hp0.le)
            (by positivity)
  -- every admissible `C` is at least the ratio
  refine le_iInf₂ fun C hC => ENNReal.ofReal_le_ofReal ?_
  by_contra hlt
  push Not at hlt
  have hC0 := hC.1
  have h1 : C * ((d : ℝ) ^ r * μ) < d / 8 := by
    have hdd : (d : ℝ) ^ (1 - r) * (d : ℝ) ^ r = d := by
      rw [← Real.rpow_add hd0, sub_add_cancel, Real.rpow_one]
    rw [lt_div_iff₀ hμ0] at hlt
    calc C * ((d : ℝ) ^ r * μ) = (C * μ) * (d : ℝ) ^ r := by ring
      _ < (1 / 8 * (d : ℝ) ^ (1 - r)) * (d : ℝ) ^ r :=
          mul_lt_mul_of_pos_right hlt (Real.rpow_pos_of_pos hd0 _)
      _ = d / 8 := by rw [mul_assoc, hdd]; ring
  have hNS0 : 0 ≤ (∫ x in unitCube d, S x ^ p) ^ (1 / p) := Real.rpow_nonneg hIS0 _
  have hlt2 : C * (∫ x in unitCube d, S x ^ p) ^ (1 / p) < (∫ x in unitCube d, K x ^ p) ^ (1 / p) :=
    calc C * (∫ x in unitCube d, S x ^ p) ^ (1 / p) ≤ C * ((d : ℝ) ^ r * μ) :=
          mul_le_mul_of_nonneg_left hNS hC0
      _ < d / 8 := h1
      _ ≤ _ := hNK
  have hpow : ∀ I : ℝ, 0 ≤ I → (I ^ (1 / p)) ^ p = I := fun I hI => by
    rw [← Real.rpow_mul hI, one_div_mul_cancel hp0.ne', Real.rpow_one]
  have h3 : C ^ p * ∫ x in unitCube d, S x ^ p < ∫ x in unitCube d, K x ^ p := by
    have := Real.rpow_lt_rpow (mul_nonneg hC0 hNS0) hlt2 hp0
    rwa [Real.mul_rpow hC0 hNS0, hpow _ hIS0, hpow _ hIK0] at this
  have hint : ∫ x in unitCube d, kornF d p q C (0 + jac (squareWitness d) x) <
      kornF d p q C 0 := by
    rw [square_kornF_zero hp0 hq1]
    have e : ∫ x in unitCube d, kornF d p q C (0 + jac (squareWitness d) x) =
        C ^ p * (∫ x in unitCube d, S x ^ p) - ∫ x in unitCube d, K x ^ p := by
      rw [← integral_const_mul, ← integral_sub ((square_integrableOn_cube hSp).const_mul _)
        (square_integrableOn_cube hKp)]
      rfl
    rw [e]; linarith
  -- Lemma 2.2: quasiconvexity at `0` is tested by the periodic Lipschitz maps
  have hfc := square_continuous_kornF (d := d) hp0.le hq1 C
  have hbdd := square_isLocallyBounded_of_continuous hfc
  have hper := (External.Rindler.quasiconvexAtOn_iff_periodic hfc.lowerSemicontinuous hbdd 0).1
    ((cov_quasiconvexAtOn_unitCube_iff _ 0).2 hC.2)
  obtain ⟨K, hK⟩ := square_lipschitz_witness (d := d)
  have := hper (squareWitness d) K hK (fun x z => squareWitness_periodic x z)
    (square_integrableOn_cube (Sverak.gen_continuous_comp_jac hfc 0 squareWitness_contDiff))
  exact absurd this (not_le.2 hint)

end Prop61

/-- **Proposition 6.6** (`prop:qcexact4`): for every `d ≥ 2`,
`C^{qc} (d)⁴ ≥ (d² − d + 1) / (6d − 9)`.

Proof. The paper gives none (inventory E6), only the witness: "using the same divergence-free
witness `Σ_{i≠j} cos (x_i − x_j) e_j`" of Proposition 6.1. With it (`squareWitness`, on the unit
torus), `tr ∇u = 0`, `Sym_{1/2} (∇u) = diag (−Σ_j sin (θ_i − θ_j))` and
`Skew (∇u) = a ⊗ b − b ⊗ a` (`square_witness_parts`, the computation of Proposition 6.1), and the
exact moments `E ‖Sym_{1/2} ∇u‖_{S_4}⁴ = d (d − 1) (6d − 9) / 8`,
`E ‖Skew ∇u‖_{S_4}⁴ = 2 E σ⁴ = d (d − 1) (d² − d + 1) / 8` (`square_integral_hF_witness`;
`4σ² = d² − |Σ_k e^{2iθ_k}|²`) give `∫ h_{4,4,C} (∇u) < 0` whenever `C⁴ < (d² − d + 1) / (6d − 9)`.
The periodic witness refutes quasiconvexity at `0` by Lemma 2.2
(`External.Rindler.quasiconvexAtOn_iff_periodic`: quasiconvexity at `0` is tested by the periodic
Lipschitz maps), as in Proposition 6.1 and as the paper does. -/
theorem proposition6_6 (d : ℕ) (hd : 2 ≤ d) :
    ENNReal.ofReal (((d : ℝ) ^ 2 - d + 1) / (6 * d - 9)) ≤ qcThreshold (hF d 4 4) ^ 4 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  push_cast
  set r : ℝ := (((n:ℝ) + 1) ^ 2 - ((n:ℝ) + 1) + 1) / (6 * ((n:ℝ) + 1) - 9) with hr
  have hden : 0 < 6 * ((n:ℝ) + 1) - 9 := by linarith
  have hr0 : 0 < r := div_pos (by nlinarith) hden
  -- every constant `C` for which `h_{4,4,C}` is quasiconvex at `0` has `C⁴ ≥ r`: otherwise the
  -- witness `w` gives `∫ h_{4,4,C} (∇w) < 0 = h_{4,4,C} (0)`
  have key : ∀ C : ℝ, 0 ≤ C ∧ QuasiconvexAt (hF (n + 1) 4 4 C) 0 → r ≤ C ^ 4 := by
    rintro C ⟨hC, hqc⟩
    refine le_of_not_gt fun hlt => ?_
    have hlt' : C ^ 4 * (6 * ((n:ℝ) + 1) - 9) < ((n:ℝ) + 1) ^ 2 - ((n:ℝ) + 1) + 1 := by
      rwa [hr, lt_div_iff₀ hden] at hlt
    have hint : ∫ x in unitCube (n + 1), hF (n + 1) 4 4 C (0 + jac (squareWitness (n + 1)) x) <
        hF (n + 1) 4 4 C 0 := by
      rw [square_integral_hF_witness, square_hF_zero]
      have hfac : C ^ 4 * (((n:ℝ) + 1) * (3 * n * (2 * n - 1) / 8)) -
          ((n:ℝ) + 1) * n * (((n:ℝ) + 1) ^ 2 - ((n:ℝ) + 1) + 1) / 8 =
          (((n:ℝ) + 1) * n / 8) * (C ^ 4 * (6 * ((n:ℝ) + 1) - 9) -
            (((n:ℝ) + 1) ^ 2 - ((n:ℝ) + 1) + 1)) := by ring
      rw [hfac]
      exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
    -- Lemma 2.2: quasiconvexity at `0` is tested by the periodic Lipschitz maps
    have hfc := square_continuous_hF (d := n + 1) C
    have hper := (External.Rindler.quasiconvexAtOn_iff_periodic hfc.lowerSemicontinuous
      (square_isLocallyBounded_of_continuous hfc) 0).1 ((cov_quasiconvexAtOn_unitCube_iff _ 0).2 hqc)
    obtain ⟨K, hK⟩ := square_lipschitz_witness (d := n + 1)
    have := hper (squareWitness (n + 1)) K hK (fun x z => squareWitness_periodic x z)
      (square_integrableOn_cube (Sverak.gen_continuous_comp_jac hfc 0 squareWitness_contDiff))
    exact absurd this (not_le.2 hint)
  set s : ℝ := r ^ (((4 : ℕ) : ℝ)⁻¹) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hr0.le _
  have hs4 : s ^ 4 = r := Real.rpow_inv_natCast_pow hr0.le (by norm_num)
  have h1 : ENNReal.ofReal s ≤ qcThreshold (hF (n + 1) 4 4) := by
    refine le_iInf₂ fun C hC => ENNReal.ofReal_le_ofReal ?_
    refine le_of_not_gt fun hlt => ?_
    have : C ^ 4 < s ^ 4 := pow_lt_pow_left₀ hlt hC.1 (by norm_num)
    linarith [key C hC]
  calc ENNReal.ofReal r = ENNReal.ofReal s ^ 4 := by rw [← ENNReal.ofReal_pow hs0, hs4]
    _ ≤ _ := by gcongr

/-- **Theorem 6.2** (`thm:sharp2sided`): let `D_k ∈ ℝ^{d×d}` be predictable, all symmetric or all
skew-symmetric, `M_n = Σ_{k<n} ε_k D_k`, `V_k = D_kᵀ D_k`, `V̂ = Σ_k V_k`, `x² = E ‖M_N‖_{S_4}^4`,
`y² = E ‖V̂‖_{S_2}^2` (`x, y ≥ 0`). Then `x² − 6 x y + 3 y² ≤ 0` (32), that is
`z₋² y ≤ x ≤ z₊² y` with `z_±² = 3 ± √6`.

Proof (the paper's): `Φ_n = tr H_n² − 6 tr (H_n Ṽ_n) + 3 tr Ṽ_n²`, `H_n = M_nᵀ M_n`, is a
supermartingale: averaging over the sign `ε_n` (`square_avg_flip`; the earlier signs and `D_n` are
unchanged by predictability), `E[Φ_n | ℱ_{n−1}] − Φ_{n−1} = ‖W_n‖² − 4 tr (H_{n−1} V_n) − 2 tr V_n²
≤ 0` with `‖W_n‖ ≤ 2 ‖M_{n−1} D_n‖` by normality (`square_phi_step`). Hence `E Φ_N ≤ Φ_0 = 0`, and
`x² + 3y² ≤ 6 E tr (H_N V̂) ≤ 6 E [‖H_N‖_{S_2} ‖V̂‖_{S_2}] ≤ 6xy` (Cauchy–Schwarz twice). -/
theorem theorem6_2 {N : ℕ} (D : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ)
    (hD : IsPredictable D)
    (hsym : (∀ k ε, (D k ε).IsSymm) ∨ ∀ k ε, (D k ε)ᵀ = -D k ε) :
    let x := √(avg fun ε => schattenNorm 4 (mart D N ε) ^ 4)
    let y := √(avg fun ε => schattenNorm 2 (∑ k, (D k ε)ᵀ * D k ε) ^ 2)
    x ^ 2 - 6 * x * y + 3 * y ^ 2 ≤ 0 ∧ (3 - √6) * y ≤ x ∧ x ≤ (3 + √6) * y := by
  intro x y
  -- all increments are `s`-symmetric, `s = ±1`; hence they and the `M_n` are normal
  obtain ⟨s, hs1, hs⟩ : ∃ s : ℝ, s ^ 2 = 1 ∧ ∀ k ε, (D k ε)ᵀ = s • D k ε := by
    rcases hsym with h | h
    · exact ⟨1, by norm_num, fun k ε => by rw [one_smul]; exact h k ε⟩
    · exact ⟨-1, by norm_num, fun k ε => by rw [neg_one_smul]; exact h k ε⟩
  have hnormal : ∀ {P : Matrix (Fin d) (Fin d) ℝ}, Pᵀ = s • P → P * Pᵀ = Pᵀ * P := by
    intro P hP; rw [hP, Matrix.mul_smul, Matrix.smul_mul]
  -- `M_n = Σ_{k<n} ε_k D_k`, `Ṽ_n = Σ_{k<n} D_kᵀ D_k`, `Φ_n = Φ (M_n, Ṽ_n)`
  let Vn : ℕ → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ := fun n ε =>
    ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < n), (D k ε)ᵀ * D k ε
  let Φ : ℕ → (Fin N → Bool) → ℝ := fun n ε => squarePhi (mart D n ε) (Vn n ε)
  have hMt : ∀ n ε, (mart D n ε)ᵀ = s • mart D n ε := by
    intro n ε
    simp only [mart, Matrix.transpose_sum, Matrix.transpose_smul, hs, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  -- predictability: the signs `ε_j`, `j ≥ n`, do not enter `M_n`, `Ṽ_n`, `D_n`
  have hDflip : ∀ (k j : Fin N), j ≤ k → ∀ ε, D j (rad_flip k ε) = D j ε := by
    intro k j hjk ε
    exact hD j _ _ fun i hi => rad_flip_apply_ne (ne_of_lt (lt_of_lt_of_le hi hjk)) ε
  have hlt : ∀ n (hn : n < N) (j : Fin N), j ∈ Finset.univ.filter (fun k : Fin N => k.val < n) →
      j < ⟨n, hn⟩ := fun n hn j hj => Fin.lt_def.2 (Finset.mem_filter.1 hj).2
  have hMflip : ∀ n (hn : n < N) ε, mart D n (rad_flip ⟨n, hn⟩ ε) = mart D n ε := by
    intro n hn ε
    simp only [mart]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [rad_flip_apply_ne (ne_of_lt (hlt n hn j hj)), hDflip _ j (hlt n hn j hj).le ε]
  have hVflip : ∀ n (hn : n < N) ε, Vn n (rad_flip ⟨n, hn⟩ ε) = Vn n ε := by
    intro n hn ε
    simp only [Vn]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hDflip _ j (hlt n hn j hj).le ε]
  -- one step: `E Φ_{n+1} ≤ E Φ_n`
  have hstep : ∀ n (hn : n < N), avg (Φ (n + 1)) ≤ avg (Φ n) := by
    intro n hn
    have hM1 : ∀ ε, mart D (n + 1) ε = mart D n ε + coin (ε ⟨n, hn⟩) • D ⟨n, hn⟩ ε :=
      fun ε => square_sum_filter_succ hn _
    have hV1 : ∀ ε, Vn (n + 1) ε = Vn n ε + (D ⟨n, hn⟩ ε)ᵀ * D ⟨n, hn⟩ ε := fun ε =>
      square_sum_filter_succ hn _
    have hpair : ∀ ε, Φ (n + 1) ε + Φ (n + 1) (rad_flip ⟨n, hn⟩ ε) ≤ 2 * Φ n ε := by
      intro ε
      have h1 : Φ (n + 1) ε = squarePhi (mart D n ε + coin (ε ⟨n, hn⟩) • D ⟨n, hn⟩ ε)
          (Vn n ε + (D ⟨n, hn⟩ ε)ᵀ * D ⟨n, hn⟩ ε) := by
        show squarePhi (mart D (n + 1) ε) (Vn (n + 1) ε) = _
        rw [hM1, hV1]
      have h2 : Φ (n + 1) (rad_flip ⟨n, hn⟩ ε) =
          squarePhi (mart D n ε + (-coin (ε ⟨n, hn⟩)) • D ⟨n, hn⟩ ε)
            (Vn n ε + (D ⟨n, hn⟩ ε)ᵀ * D ⟨n, hn⟩ ε) := by
        show squarePhi (mart D (n + 1) (rad_flip ⟨n, hn⟩ ε))
          (Vn (n + 1) (rad_flip ⟨n, hn⟩ ε)) = _
        rw [hM1, hV1, hMflip n hn, hVflip n hn, hDflip _ _ le_rfl, square_coin_flip]
      rw [h1, h2]
      exact square_phi_step (hnormal (hMt n ε)) (hnormal (hs _ ε)) (square_coin_sq _)
    calc avg (Φ (n + 1)) =
          avg (fun ε => (Φ (n + 1) ε + Φ (n + 1) (rad_flip ⟨n, hn⟩ ε)) / 2) := by
          simp only [div_eq_mul_inv, mul_comm _ (2 : ℝ)⁻¹]
          rw [rad_avg_mul_left, rad_avg_add,
            square_avg_flip ⟨n, hn⟩ (Φ (n + 1))]; ring
      _ ≤ avg (Φ n) := rad_avg_mono fun ε => by linarith [hpair ε]
  have hΦ0 : avg (Φ 0) = 0 := by
    have : Φ 0 = fun _ => 0 := funext fun ε => by
      simp [Φ, Vn, mart, squarePhi, squareFrob]
    rw [this, square_avg_const]
  have hΦN : avg (Φ N) ≤ 0 := by
    have : ∀ n, n ≤ N → avg (Φ n) ≤ 0 := by
      intro n
      induction n with
      | zero => intro _; rw [hΦ0]
      | succ n ih => intro hn; exact (hstep n hn).trans (ih (Nat.le_of_succ_le hn))
    exact this N le_rfl
  -- `x² = E ‖H_N‖_F²`, `y² = E ‖V̂‖_F²`, and `E ⟨H_N, V̂⟩ ≤ x y`
  have hVN : ∀ ε, Vn N ε = ∑ k, (D k ε)ᵀ * D k ε := fun ε => by
    simp only [Vn, square_filter_all]
  have hsym' : ∀ P : Matrix (Fin d) (Fin d) ℝ, (Pᵀ * P)ᵀ = Pᵀ * P := fun P => by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hVt : ∀ ε, (Vn N ε)ᵀ = Vn N ε := fun ε => by
    simp only [Vn, Matrix.transpose_sum, hsym']
  set H : (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ := fun ε => (mart D N ε)ᵀ * mart D N ε
  have hx : avg (fun ε => schattenNorm 4 (mart D N ε) ^ 4) = avg fun ε => squareFrob (H ε) (H ε) := by
    congr 1; funext ε; rw [square_schattenNorm_four_pow, squareFrob, hsym']
  have hy : avg (fun ε => schattenNorm 2 (∑ k, (D k ε)ᵀ * D k ε) ^ 2) =
      avg fun ε => squareFrob (Vn N ε) (Vn N ε) := by
    congr 1; funext ε; rw [square_schattenNorm_two_sq, squareFrob, hVN]
  have hHH : ∀ ε, 0 ≤ squareFrob (H ε) (H ε) := fun ε => squareFrob_self_nonneg _
  have hVV : ∀ ε, 0 ≤ squareFrob (Vn N ε) (Vn N ε) := fun ε => squareFrob_self_nonneg _
  have hx2 : x ^ 2 = avg fun ε => squareFrob (H ε) (H ε) := by
    rw [show x = √(avg fun ε => schattenNorm 4 (mart D N ε) ^ 4) from rfl, hx,
      Real.sq_sqrt (rad_avg_nonneg hHH)]
  have hy2 : y ^ 2 = avg fun ε => squareFrob (Vn N ε) (Vn N ε) := by
    rw [show y = √(avg fun ε => schattenNorm 2 (∑ k, (D k ε)ᵀ * D k ε) ^ 2) from rfl, hy,
      Real.sq_sqrt (rad_avg_nonneg hVV)]
  have hxy : avg (fun ε => squareFrob (H ε) (Vn N ε)) ≤ x * y := by
    calc avg (fun ε => squareFrob (H ε) (Vn N ε))
        ≤ avg (fun ε => √(squareFrob (H ε) (H ε)) * √(squareFrob (Vn N ε) (Vn N ε))) :=
          rad_avg_mono fun ε => (le_abs_self _).trans (squareFrob_le_sqrt _ _)
      _ ≤ √(avg fun ε => squareFrob (H ε) (H ε)) * √(avg fun ε => squareFrob (Vn N ε) (Vn N ε)) :=
          square_avg_sqrt_mul_le hHH hVV
      _ = x * y := by rw [show x = √(avg fun ε => schattenNorm 4 (mart D N ε) ^ 4) from rfl,
            show y = √(avg fun ε => schattenNorm 2 (∑ k, (D k ε)ᵀ * D k ε) ^ 2) from rfl, hx, hy]
  have hΦN' : avg (Φ N) = x ^ 2 - 6 * avg (fun ε => squareFrob (H ε) (Vn N ε)) + 3 * y ^ 2 := by
    rw [hx2, hy2, ← rad_avg_mul_left, ← rad_avg_mul_left, ← rad_avg_sub,
      ← rad_avg_add]
    rfl
  have h32 : x ^ 2 - 6 * x * y + 3 * y ^ 2 ≤ 0 := by
    have := hxy; rw [hΦN'] at hΦN; nlinarith
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h60 : 0 ≤ √6 := Real.sqrt_nonneg 6
  have hfac : (x - (3 - √6) * y) * (x - (3 + √6) * y) ≤ 0 := by nlinarith
  refine ⟨h32, ?_, ?_⟩
  · refine le_of_not_gt fun hc => ?_
    have h1 : 0 < (3 - √6) * y - x := by linarith
    have h2 : 0 < (3 + √6) * y - x := by nlinarith
    nlinarith [mul_pos h1 h2]
  · refine le_of_not_gt fun hc => ?_
    have h1 : 0 < x - (3 + √6) * y := by linarith
    have h2 : 0 < x - (3 - √6) * y := by nlinarith
    nlinarith [mul_pos h1 h2]

/-- **Corollary 6.3** (`cor:uncond`), lower bound: `3 ≤ C^{rc} (d)` for every `d ≥ 2`.
Unconditional: the sharpness of Burkholder's constant `4* − 1 = 3` for dyadic martingales that
the proof uses is proved (`burkholderSharpness_holds`, module `Square.Sharpness`). Statement change:
the hypothesis `hS : BurkholderSharpness` of the earlier, conditional version is
removed.

Proof (the paper's): for `C < 3`, the sharpness gives a dyadic martingale `f_N` and a `±1`
transform `g_N` with `‖g_N‖_{L⁴} > C ‖f_N‖_{L⁴}`; then `M_n = f_n Sym (e₁ ⊗ e₂) + g_n Skew (e₁ ⊗ e₂)`
is a rank-one Rademacher martingale (its increments are multiples of `e₁ ⊗ e₂` or `e₂ ⊗ e₁`) with
`E h_{4,4,C} (M_N) = c (C⁴ E f_N⁴ − E g_N⁴) < 0` (`c = ‖Sym (e₁ ⊗ e₂)‖_{S_4}⁴ =
‖Skew (e₁ ⊗ e₂)‖_{S_4}⁴ > 0`), so `h_{4,4,C}` is not rank-one convex at `0` (Proposition 2.5). -/
theorem corollary6_3_lower (d : ℕ) (hd : 2 ≤ d) :
    ENNReal.ofReal 3 ≤ rcThreshold (hF d 4 4) := by
  have hS := burkholderSharpness_holds
  refine le_iInf₂ fun C hC => ENNReal.ofReal_le_ofReal (le_of_not_gt fun hC3 => ?_)
  obtain ⟨hC0, hrc⟩ := hC
  -- a dyadic martingale `f_n` and a `±1` transform `g_n` with `‖g_N‖₄ > C ‖f_N‖₄` (`4* − 1 = 3`)
  have hp4 : pStar 4 - 1 = 3 := by
    rw [pStar, max_eq_left (by norm_num)]; norm_num
  obtain ⟨N, φ, σ, hφ, hσ, hσ1, hlt⟩ := hS 4 (by norm_num) C (by rw [hp4]; exact hC3)
  -- `M_n = f_n Sym (e₀ ⊗ e₁) + g_n Skew (e₀ ⊗ e₁)`, a rank-one Rademacher martingale
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set u : Fin d → ℝ := Pi.single i0 1
  set w : Fin d → ℝ := Pi.single i1 1
  set S : Matrix (Fin d) (Fin d) ℝ := (1 / 2 : ℝ) • (Matrix.vecMulVec u w + Matrix.vecMulVec w u)
  set K : Matrix (Fin d) (Fin d) ℝ := (1 / 2 : ℝ) • (Matrix.vecMulVec u w - Matrix.vecMulVec w u)
  set A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ := fun k ε =>
    φ k ε • (S + σ k ε • K)
  have hA : IsRankOneIncrements A := by
    refine ⟨fun k ε ε' h => by simp only [A, hφ k ε ε' h, hσ k ε ε' h], fun k ε => ?_⟩
    have hSK : S + σ k ε • K = Matrix.vecMulVec u w ∨ S + σ k ε • K = Matrix.vecMulVec w u := by
      rcases hσ1 k ε with h | h
      · left; simp only [S, K, h, one_smul]; module
      · right; simp only [S, K, h, neg_one_smul]; module
    have hsm : ∀ (c : ℝ) (a b : Fin d → ℝ), (c • Matrix.vecMulVec a b).rank ≤ 1 := by
      intro c a b
      rw [← Matrix.smul_vecMulVec]
      exact Matrix.rank_vecMulVec_le _ _
    rcases hSK with h | h <;> simp only [A, h] <;> exact hsm _ _ _
  have hM : ∀ ε, radMart 0 A N ε = mart φ N ε • S + mart (fun k ε => σ k ε * φ k ε) N ε • K := by
    intro ε
    simp only [radMart, zero_add, mart, A, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_add, smul_smul]
    ring_nf
  -- the two parts of `M_N`
  have hSt : Sᵀ = S := by
    simp only [S, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_vecMulVec, add_comm]
  have hKt : Kᵀ = -K := by
    simp only [K, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_vecMulVec]
    rw [← smul_neg, neg_sub]
  have hdiag : ∀ x : Fin d, u x * w x = 0 := fun x => by
    simp only [u, w, Pi.single_apply]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) h01
    all_goals simp
  have htrS : S.trace = 0 := by
    simp only [S, Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.add_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, mul_comm (w _) (u _), hdiag]
    simp
  have htrK : K.trace = 0 := by
    simp only [K, Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, mul_comm (w _) (u _), hdiag]
    simp
  have hparts : ∀ a b : ℝ, symHalfPart (a • S + b • K) = a • S ∧ skewPart (a • S + b • K) = b • K := by
    intro a b
    constructor
    · simp only [symHalfPart, symPart, Matrix.transpose_add, Matrix.transpose_smul, hSt, hKt,
        Matrix.trace_add, Matrix.trace_smul, htrS, htrK, smul_zero, add_zero, mul_zero, zero_smul,
        sub_zero]
      module
    · simp only [skewPart, Matrix.transpose_add, Matrix.transpose_smul, hSt, hKt]
      module
  -- `SᵀS = KᵀK` (`= (e₀⊗e₀ + e₁⊗e₁)/4`), so `h_{4,4,C} (M_N) = c (C⁴ f_N⁴ − g_N⁴)`, `c > 0`
  have hE : Matrix.vecMulVec u w * Matrix.vecMulVec u w = 0 ∧
      Matrix.vecMulVec w u * Matrix.vecMulVec w u = 0 := by
    constructor <;> ext i j <;>
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply, u, w, Pi.single_apply, h01, h01.symm]
  have hSK : Sᵀ * S = Kᵀ * K := by
    rw [hSt, hKt, Matrix.neg_mul, ← sub_eq_zero, sub_neg_eq_add]
    simp only [S, K, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, hE.1, hE.2]
    module
  set c := squareFrob (Sᵀ * S) (Sᵀ * S) with hc
  have hc0 : 0 < c := by
    have hent : (Sᵀ * S) i0 i0 = 1 / 4 := by
      simp [S, Matrix.mul_apply, Matrix.vecMulVec_apply, u, w, Pi.single_apply, h01]
      norm_num
    rw [hc, squareFrob_eq_sum]
    have := Finset.single_le_sum (s := Finset.univ) (f := fun x : Fin d × Fin d =>
      (Sᵀ * S) x.1 x.2 * (Sᵀ * S) x.1 x.2) (fun x _ => mul_self_nonneg _)
      (Finset.mem_univ (i0, i0))
    simp only [hent] at this
    linarith
  have hval : ∀ a b : ℝ, hF d 4 4 C (a • S + b • K) = c * (C ^ 4 * a ^ 4 - b ^ 4) := by
    intro a b
    rw [square_hF_eq, (hparts a b).1, (hparts a b).2]
    have h1 : (a • S)ᵀ * (a • S) * ((a • S)ᵀ * (a • S)) = a ^ 4 • (Sᵀ * S * (Sᵀ * S)) := by
      simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; ring_nf
    have h2 : (b • K)ᵀ * (b • K) * ((b • K)ᵀ * (b • K)) = b ^ 4 • (Sᵀ * S * (Sᵀ * S)) := by
      simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hSK]
      ring_nf
    have hcS : (Sᵀ * S * (Sᵀ * S)).trace = c := by
      rw [hc, squareFrob, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [h1, h2, Matrix.trace_smul, Matrix.trace_smul, hcS, smul_eq_mul, smul_eq_mul]
    ring
  -- rank-one convexity at `0` (Proposition 2.5) gives `E g_N⁴ ≤ C⁴ E f_N⁴`
  have hineq := (proposition2_5 (square_continuous_hF C)).1 hrc N A hA
  rw [square_hF_zero] at hineq
  simp only [hM, hval] at hineq
  set F := mart φ N
  set G := mart (fun k ε => σ k ε * φ k ε) N
  have h4 : avg (fun ε => G ε ^ 4) ≤ C ^ 4 * avg (fun ε => F ε ^ 4) := by
    rw [rad_avg_mul_left c (fun ε => C ^ 4 * F ε ^ 4 - G ε ^ 4), rad_avg_sub,
      rad_avg_mul_left] at hineq
    have := (mul_nonneg_iff_of_pos_left hc0).1 hineq
    linarith
  have hrpow : ∀ X : (Fin N → Bool) → ℝ, lpNormWith (fun x => |x|) 4 X =
      (avg fun ε => X ε ^ 4) ^ (1 / 4 : ℝ) := by
    intro X
    simp only [lpNormWith]
    congr 2; funext ε
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs,
      abs_of_nonneg (by positivity)]
  rw [hrpow, hrpow] at hlt
  have hF0 : 0 ≤ avg fun ε => F ε ^ 4 := rad_avg_nonneg fun ε => by positivity
  have hG0 : 0 ≤ avg fun ε => G ε ^ 4 := rad_avg_nonneg fun ε => by positivity
  have := Real.rpow_le_rpow hG0 h4 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [Real.mul_rpow (by positivity) hF0, show C ^ 4 = C ^ ((4 : ℕ) : ℝ) by
    rw [Real.rpow_natCast], ← Real.rpow_mul hC0] at this
  norm_num at this
  linarith

-- The proof does not use the paper's hypothesis `d ≥ 2` (see the docstring).
set_option linter.unusedVariables false in
/-- **Corollary 6.3** (`cor:uncond`), upper bound:
`C^{rc} (d) ≤ [3 (√3 + √2)² · ⅓ (√3 + √2)²]^{1/4} = √2 + √3` for every `d ≥ 2`. The hypothesis
`d ≥ 2` is the paper's; the proof does not use it (for `d ≤ 1` the bound holds as well).

Proof (the paper's): for a rank-one Rademacher martingale `M` started at `0`, Theorem 6.2 applied
to the skew martingale `Skew (M)` and to the symmetric martingale `Sym_{1/2} (M)`, with the
rank-one fact `Skew (R)ᵀ Skew (R) = Sym_{1/2} (R)² − ¼ tr (R)² Id ⪯ Sym_{1/2} (R)²`
(`square_rankOne_sq`) and fact (3) (`schattenNorm_mono`, for `S_2`), gives
`‖Skew M_N‖_{L⁴(S_4)} ≤ (z₊² / z₋²) ‖Sym_{1/2} M_N‖_{L⁴(S_4)}`, `z₊² / z₋² = 5 + 2√6 = (√2 + √3)²`;
so `E h_{4,4,√2+√3} (M_N) ≥ 0`, and `h_{4,4,√2+√3}` is rank-one convex at `0` (Proposition 2.5). -/
theorem corollary6_3_upper (d : ℕ) (hd : 2 ≤ d) :
    rcThreshold (hF d 4 4) ≤ ENNReal.ofReal (√2 + √3) := by
  set C := √2 + √3 with hCdef
  have hC0 : 0 ≤ C := by positivity
  have h6s : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h6a : (2.449 : ℝ) < √6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h6b : √6 < (2.45 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hC4 : C ^ 4 = (5 + 2 * √6) ^ 2 := by
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    have h23 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
    have hc2 : C ^ 2 = 5 + 2 * √6 := by rw [hCdef, h23]; nlinarith
    rw [show C ^ 4 = (C ^ 2) ^ 2 by ring, hc2]
  -- `h_{4,4,C}` is rank-one convex at `0` (Proposition 2.5)
  refine iInf₂_le C ⟨hC0, (proposition2_5 (square_continuous_hF C)).2 fun N A hA => ?_⟩
  rw [square_hF_zero]
  -- `Sym_{1/2}` and `Skew` are linear, so `Sym_{1/2} (M_N)`, `Skew (M_N)` are martingales
  have hadd : ∀ P Q : Matrix (Fin d) (Fin d) ℝ,
      symHalfPart (P + Q) = symHalfPart P + symHalfPart Q ∧ skewPart (P + Q) = skewPart P + skewPart Q :=
    fun P Q => ⟨by simpa using square_symHalfPart_add_smul P Q 1,
      by simpa using square_skewPart_add_smul P Q 1⟩
  have hsm : ∀ (c : ℝ) (P : Matrix (Fin d) (Fin d) ℝ),
      symHalfPart (c • P) = c • symHalfPart P ∧ skewPart (c • P) = c • skewPart P :=
    fun c P => ⟨by simpa [square_symHalfPart_zero] using square_symHalfPart_add_smul 0 P c,
      by simpa [square_skewPart_zero] using square_skewPart_add_smul 0 P c⟩
  have hsumS : ∀ (s : Finset (Fin N)) (ε : Fin N → Bool),
      symHalfPart (∑ k ∈ s, coin (ε k) • A k ε) = ∑ k ∈ s, coin (ε k) • symHalfPart (A k ε) ∧
        skewPart (∑ k ∈ s, coin (ε k) • A k ε) = ∑ k ∈ s, coin (ε k) • skewPart (A k ε) := by
    intro s ε
    induction s using Finset.induction_on with
    | empty => simp [square_symHalfPart_zero, square_skewPart_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, (hadd _ _).1,
        (hadd _ _).2, (hsm _ _).1, (hsm _ _).2, ih.1, ih.2]
      exact ⟨rfl, rfl⟩
  set D : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ := fun k ε => symHalfPart (A k ε)
  set E : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ := fun k ε => skewPart (A k ε)
  have hMD : ∀ ε, symHalfPart (radMart 0 A N ε) = mart D N ε := fun ε => by
    rw [radMart, zero_add]; exact (hsumS _ ε).1
  have hME : ∀ ε, skewPart (radMart 0 A N ε) = mart E N ε := fun ε => by
    rw [radMart, zero_add]; exact (hsumS _ ε).2
  have hDp : IsPredictable D := fun k ε ε' h => by simp only [D, hA.1 k ε ε' h]
  have hEp : IsPredictable E := fun k ε ε' h => by simp only [E, hA.1 k ε ε' h]
  -- Theorem 6.2 for both martingales
  obtain ⟨-, hD1, -⟩ := theorem6_2 D hDp (Or.inl fun k ε => square_symHalfPart_transpose _)
  obtain ⟨-, -, hE2⟩ := theorem6_2 E hEp (Or.inr fun k ε => square_skewPart_transpose _)
  set xD := √(avg fun ε => schattenNorm 4 (mart D N ε) ^ 4)
  set yD := √(avg fun ε => schattenNorm 2 (∑ k, (D k ε)ᵀ * D k ε) ^ 2)
  set xE := √(avg fun ε => schattenNorm 4 (mart E N ε) ^ 4)
  set yE := √(avg fun ε => schattenNorm 2 (∑ k, (E k ε)ᵀ * E k ε) ^ 2)
  -- the rank-one Loewner fact: `Σ E_kᵀ E_k ⪯ Σ D_k²`, hence `‖𝔖 Skew M‖ ≤ ‖𝔖 Sym_{1/2} M‖`
  have hyEyD : yE ≤ yD := by
    refine Real.sqrt_le_sqrt (rad_avg_mono fun ε => ?_)
    have hVE : (∑ k, (E k ε)ᵀ * E k ε).PosSemidef := Matrix.posSemidef_sum _ fun k _ => by
      simpa [square_conjTranspose_eq] using Matrix.posSemidef_conjTranspose_mul_self (E k ε)
    have hdiff : (∑ k, (D k ε)ᵀ * D k ε) - ∑ k, (E k ε)ᵀ * E k ε =
        (∑ k, (A k ε).trace ^ 2 / 4) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [D, E, square_symHalfPart_transpose, square_skewPart_transpose, Matrix.neg_mul,
        sub_neg_eq_add]
      exact square_rankOne_sq (hA.2 k ε)
    have hPSD : ((∑ k, (D k ε)ᵀ * D k ε) - ∑ k, (E k ε)ᵀ * E k ε).PosSemidef := by
      rw [hdiff]
      exact Matrix.PosSemidef.one.smul (Finset.sum_nonneg fun k _ => by positivity)
    have := schattenNorm_mono (le_refl _ |>.trans (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hVE hPSD
    exact pow_le_pow_left₀ (schattenNorm_nonneg _ _) this 2
  have h3 : (0 : ℝ) < 3 - √6 := by linarith
  have hxyD : xE ≤ (5 + 2 * √6) * xD := by
    have hq : (3 + √6) / (3 - √6) = 5 + 2 * √6 := by
      rw [div_eq_iff h3.ne']; nlinarith
    calc xE ≤ (3 + √6) * yE := hE2
      _ ≤ (3 + √6) * yD := mul_le_mul_of_nonneg_left hyEyD (by positivity)
      _ ≤ (3 + √6) * (xD / (3 - √6)) := by
          gcongr; rw [le_div_iff₀ h3, mul_comm]; exact hD1
      _ = (5 + 2 * √6) * xD := by rw [← hq]; ring
  -- `E h_{4,4,C} (M_N) = C⁴ x_D² − x_E² ≥ 0`
  have hxD2 : xD ^ 2 = avg fun ε => schattenNorm 4 (mart D N ε) ^ 4 :=
    Real.sq_sqrt (rad_avg_nonneg fun ε => by positivity)
  have hxE2 : xE ^ 2 = avg fun ε => schattenNorm 4 (mart E N ε) ^ 4 :=
    Real.sq_sqrt (rad_avg_nonneg fun ε => by positivity)
  have hval : (avg fun ε => hF d 4 4 C (radMart 0 A N ε)) = C ^ 4 * xD ^ 2 - xE ^ 2 := by
    rw [hxD2, hxE2, ← rad_avg_mul_left, ← rad_avg_sub]
    congr 1; funext ε
    rw [hF, hMD, hME, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.rpow_natCast, Real.rpow_natCast]
  rw [hval, hC4]
  have hxD0 : 0 ≤ xD := Real.sqrt_nonneg _
  have hxE0 : 0 ≤ xE := Real.sqrt_nonneg _
  have : xE ^ 2 ≤ ((5 + 2 * √6) * xD) ^ 2 := pow_le_pow_left₀ hxE0 hxyD 2
  nlinarith

/-- **Corollary 6.3** (`cor:uncond`), separation: `C^{qc} (d) > C^{rc} (d)` whenever
`(d² − d + 1) / (6d − 9) > (5 + 2√6)² = 49 + 20√6`, that is, for every `d ≥ d₀ = 588`.

Proof: `C^{rc} (d) ≤ √2 + √3` (the upper bound) and `C^{qc} (d)⁴ ≥ (d² − d + 1) / (6d − 9)`
(Proposition 6.6) with `(√2 + √3)⁴ = (5 + 2√6)²`; the threshold `588` is arithmetic
(`2.449 < √6 < 2.45` suffices). -/
theorem corollary6_3_separation :
    (∀ d : ℕ, 2 ≤ d → (5 + 2 * √6) ^ 2 < ((d : ℝ) ^ 2 - d + 1) / (6 * d - 9) →
      rcThreshold (hF d 4 4) < qcThreshold (hF d 4 4)) ∧
    (∀ d : ℕ, 2 ≤ d → ((5 + 2 * √6) ^ 2 < ((d : ℝ) ^ 2 - d + 1) / (6 * d - 9) ↔ 588 ≤ d)) := by
  have h6a : (2.449 : ℝ) < √6 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h6b : √6 < (2.45 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h6s : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hsq : (5 + 2 * √6) ^ 2 = 49 + 20 * √6 := by nlinarith
  refine ⟨fun d hd hlt => ?_, fun d hd => ?_⟩
  · -- `C^{rc} (d) ≤ √2 + √3` and `C^{qc} (d)⁴ ≥ (d² − d + 1) / (6d − 9) > (√2 + √3)⁴`
    have hup := corollary6_3_upper d hd
    have h66 := proposition6_6 d hd
    set c := √2 + √3 with hc
    have hc0 : 0 ≤ c := by positivity
    have hc4 : c ^ 4 = (5 + 2 * √6) ^ 2 := by
      have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
      have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
      have h23 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
      have hc2 : c ^ 2 = 5 + 2 * √6 := by rw [hc, h23]; nlinarith
      rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hc2]
    refine lt_of_not_ge fun hge => ?_
    have h1 : qcThreshold (hF d 4 4) ^ 4 ≤ ENNReal.ofReal c ^ 4 := by
      have := hge.trans hup
      gcongr
    have h2 : ENNReal.ofReal (((d : ℝ) ^ 2 - d + 1) / (6 * d - 9)) ≤ ENNReal.ofReal (c ^ 4) := by
      rw [ENNReal.ofReal_pow hc0]; exact h66.trans h1
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
    linarith
  · have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hden : 0 < 6 * (d : ℝ) - 9 := by linarith
    rw [hsq, lt_div_iff₀ hden]
    constructor
    · intro h
      by_contra hlt
      have hle : (d : ℝ) ≤ 587 := by exact_mod_cast (by omega : d ≤ 587)
      nlinarith [mul_nonneg (sub_nonneg.2 hdR) (sub_nonneg.2 hle)]
    · intro h
      have hge : (588 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith [mul_nonneg (sub_nonneg.2 hge) (by linarith : (0:ℝ) ≤ d - 1)]

/-- The function `U (X, Y) = ‖Y‖_{S_4}^4 − (15/2) ‖Y X‖_{S_2}^2 − (95/4) ‖X‖_{S_4}^4` of
Corollary 6.4 (on `Sym (d) × Skew (d)`). -/
noncomputable def squareU (X Y : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  schattenNorm 4 Y ^ 4 - 15 / 2 * schattenNorm 2 (Y * X) ^ 2 -
    95 / 4 * schattenNorm 4 X ^ 4

/-- The quartic of Corollary 6.4: `g (M) = −(8/5) U (Sym_{1/2} (M), Skew (M))`. -/
noncomputable def gSquare (d : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  -(8 / 5) * squareU (symHalfPart M) (skewPart M)

/-! ### Corollary 6.4: the quartic `g` -/

section Cor64

/-- `U (X, Y) = ‖YᵀY‖_F² − (15/2) ‖YX‖_F² − (95/4) ‖XᵀX‖_F²` (`‖·‖_{S_4}⁴ = ‖(·)ᵀ(·)‖_F²`,
`‖·‖_{S_2} = ‖·‖_F`). -/
theorem square_squareU_eq (X Y : Matrix (Fin d) (Fin d) ℝ) :
    squareU X Y = squareFrob (Yᵀ * Y) (Yᵀ * Y) - 15 / 2 * squareFrob (Y * X) (Y * X) -
      95 / 4 * squareFrob (Xᵀ * X) (Xᵀ * X) := by
  have h : ∀ Z : Matrix (Fin d) (Fin d) ℝ, (Zᵀ * Z)ᵀ = Zᵀ * Z := fun Z => by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [squareU, square_schattenNorm_four_pow, square_schattenNorm_two_sq, squareFrob, h]

/-- The second-order coefficient of `t ↦ U (X + t D, Y + t E)` (`X = Sym_{1/2} A`, `Y = Skew A`,
`D = Sym_{1/2} R`, `E = Skew R`), in Frobenius form; `φ''(0) = 2 square_zz A R` in the paper's
notation. -/
noncomputable def square_zz (A R : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  let X := symHalfPart A
  let Y := skewPart A
  let D := symHalfPart R
  let E := skewPart R
  (squareFrob (Yᵀ * E + Eᵀ * Y) (Yᵀ * E + Eᵀ * Y) + 2 * squareFrob (Yᵀ * Y) (Eᵀ * E)) -
    15 / 2 * (squareFrob (Y * D + E * X) (Y * D + E * X) + 2 * squareFrob (Y * X) (E * D)) -
    95 / 4 * (squareFrob (Xᵀ * D + Dᵀ * X) (Xᵀ * D + Dᵀ * X) +
      2 * squareFrob (Xᵀ * X) (Dᵀ * D))

/-- `t ↦ g (A + t R)` is a quartic polynomial, whose `t²`-coefficient is `−(8/5)` times the
second-order coefficient of `t ↦ U (X + t D, Y + t E)`. -/
theorem square_gSquare_line (A R : Matrix (Fin d) (Fin d) ℝ) :
    ∃ c0 c1 c3 c4 : ℝ, ∀ t, gSquare d (A + t • R) = c0 + c1 * t +
      (-(8 / 5) * square_zz A R) * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4 := by
  set X := symHalfPart A
  set Y := skewPart A
  set D := symHalfPart R
  set E := skewPart R
  have hmul : ∀ (P Q P' Q' : Matrix (Fin d) (Fin d) ℝ) (t : ℝ),
      (P + t • Q) * (P' + t • Q') = P * P' + t • (P * Q' + Q * P') + (t ^ 2) • (Q * Q') := by
    intro P Q P' Q' t
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul]
    module
  have htr : ∀ (P Q : Matrix (Fin d) (Fin d) ℝ) (t : ℝ), (P + t • Q)ᵀ = Pᵀ + t • Qᵀ := by
    intro P Q t; rw [Matrix.transpose_add, Matrix.transpose_smul]
  refine ⟨-(8 / 5) * (squareFrob (Yᵀ * Y) (Yᵀ * Y) - 15 / 2 * squareFrob (Y * X) (Y * X) -
      95 / 4 * squareFrob (Xᵀ * X) (Xᵀ * X)),
    -(8 / 5) * (2 * squareFrob (Yᵀ * Y) (Yᵀ * E + Eᵀ * Y) -
      15 / 2 * (2 * squareFrob (Y * X) (Y * D + E * X)) -
      95 / 4 * (2 * squareFrob (Xᵀ * X) (Xᵀ * D + Dᵀ * X))),
    -(8 / 5) * (2 * squareFrob (Yᵀ * E + Eᵀ * Y) (Eᵀ * E) -
      15 / 2 * (2 * squareFrob (Y * D + E * X) (E * D)) -
      95 / 4 * (2 * squareFrob (Xᵀ * D + Dᵀ * X) (Dᵀ * D))),
    -(8 / 5) * (squareFrob (Eᵀ * E) (Eᵀ * E) - 15 / 2 * squareFrob (E * D) (E * D) -
      95 / 4 * squareFrob (Dᵀ * D) (Dᵀ * D)), fun t => ?_⟩
  rw [gSquare, square_symHalfPart_add_smul, square_skewPart_add_smul, square_squareU_eq,
    htr, htr, hmul, hmul, hmul, squareFrob_quad, squareFrob_quad, squareFrob_quad, square_zz]
  ring

/-- For rank-one `R`, `square_zz A R ≤ 0`: the zig-zag concavity of `U` (`square_zigzag`, for
symmetric `D` and skew `E` with `EEᵀ ⪯ D²`) with the rank-one fact
`Sym_{1/2} (R)² − Skew (R) Skew (R)ᵀ = Sym_{1/2} (R)² + Skew (R)² = ¼ tr (R)² Id ⪰ 0`
(`square_rankOne_sq`). -/
theorem square_zz_nonpos (A R : Matrix (Fin d) (Fin d) ℝ) (hR : R.rank ≤ 1) :
    square_zz A R ≤ 0 := by
  refine square_zigzag (square_symHalfPart_transpose A) (square_skewPart_transpose A)
    (square_symHalfPart_transpose R) (square_skewPart_transpose R) ?_
  rw [square_skewPart_transpose, Matrix.mul_neg, sub_neg_eq_add, square_rankOne_sq hR]
  exact Matrix.PosSemidef.one.smul (by positivity)

/-- Equal quartic polynomial functions have equal `s²`-coefficients. -/
theorem square_quartic_coeff2 {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℝ}
    (h : ∀ s : ℝ, a0 + a1 * s + a2 * s ^ 2 + a3 * s ^ 3 + a4 * s ^ 4 =
      b0 + b1 * s + b2 * s ^ 2 + b3 * s ^ 3 + b4 * s ^ 4) : a2 = b2 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  have h3 := h 2
  have h4 := h (-2)
  norm_num at h0 h1 h2 h3 h4
  linarith

/-- `t ↦ g (A + t R)` is convex for every rank-one `R`: its second derivative at `t` is
`2 × (−8/5) square_zz (A + t R) R ≥ 0` (the second-order coefficient of `s ↦ g ((A + t R) + s R)`,
which is `s ↦ g (A + (t + s) R)`). -/
theorem square_gSquare_rankOneConvex : RankOneConvex (gSquare d) := by
  rw [← rankOneConvex_iff]
  intro A R hR
  obtain ⟨c0, c1, c3, c4, hA⟩ := square_gSquare_line A R
  obtain ⟨h1, h2, h3⟩ := Sverak.l2_quartic_deriv2 c0 c1 _ c3 c4 hA
  refine convexOn_univ_of_deriv2_nonneg h1 h2 fun t => ?_
  obtain ⟨e0, e1, e3, e4, hB⟩ := square_gSquare_line (A + t • R) R
  have hcoef : -(8 / 5) * square_zz (A + t • R) R =
      -(8 / 5) * square_zz A R + 3 * c3 * t + 6 * c4 * t ^ 2 := by
    refine square_quartic_coeff2 (a0 := e0) (a1 := e1) (a3 := e3) (a4 := e4)
      (b0 := c0 + c1 * t + (-(8 / 5) * square_zz A R) * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4)
      (b1 := c1 + 2 * (-(8 / 5) * square_zz A R) * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3)
      (b3 := c3 + 4 * c4 * t) (b4 := c4) fun s => ?_
    rw [← hB s, show A + t • R + s • R = A + (t + s) • R by rw [add_smul, add_assoc], hA]
    ring
  rw [h3 t]
  have := square_zz_nonpos (A + t • R) R hR.le
  nlinarith

/-! #### `g` is a homogeneous quartic polynomial -/

section Poly

open MvPolynomial

/-- A matrix of polynomials in the entries whose entries are all homogeneous of degree `k`. -/
def square_IsHomMat (k : ℕ) (M : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin d) ℝ)) :
    Prop :=
  ∀ i j, (M i j).IsHomogeneous k

theorem square_IsHomMat.mul {a b : ℕ} {M N : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin d) ℝ)}
    (hM : square_IsHomMat a M) (hN : square_IsHomMat b N) : square_IsHomMat (a + b) (M * N) :=
  fun i j => IsHomogeneous.sum _ _ _ fun k _ => (hM i k).mul (hN k j)

theorem square_IsHomMat.transpose {a : ℕ}
    {M : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin d) ℝ)} (hM : square_IsHomMat a M) :
    square_IsHomMat a Mᵀ :=
  fun i j => hM j i

theorem square_IsHomMat.trace {a : ℕ}
    {M : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin d) ℝ)} (hM : square_IsHomMat a M) :
    (M.trace).IsHomogeneous a :=
  IsHomogeneous.sum _ _ _ fun i _ => hM i i

/-- The polynomial matrix `Sym_{1/2}` of the generic matrix `(X_{ij})`. -/
noncomputable def square_symHalfPoly (d : ℕ) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin d) ℝ) :=
  Matrix.of fun i j => C (1 / 2) * (X (i, j) + X (j, i)) -
    if i = j then C (1 / 2) * ∑ k, X (k, k) else 0

/-- The polynomial matrix `Skew` of the generic matrix `(X_{ij})`. -/
noncomputable def square_skewPoly (d : ℕ) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin d) ℝ) :=
  Matrix.of fun i j => C (1 / 2) * (X (i, j) - X (j, i))

theorem square_symHalfPoly_hom : square_IsHomMat 1 (square_symHalfPoly d) := by
  intro i j
  simp only [square_symHalfPoly, Matrix.of_apply]
  refine IsHomogeneous.sub (((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).C_mul _) ?_
  split_ifs
  · exact (IsHomogeneous.sum _ _ _ fun k _ => isHomogeneous_X _ _).C_mul _
  · exact isHomogeneous_zero _ _ _

theorem square_skewPoly_hom : square_IsHomMat 1 (square_skewPoly d) := by
  intro i j
  simp only [square_skewPoly, Matrix.of_apply]
  exact ((isHomogeneous_X _ _).sub (isHomogeneous_X _ _)).C_mul _

theorem square_symHalfPoly_eval (A : Matrix (Fin d) (Fin d) ℝ) :
    (square_symHalfPoly d).map (eval fun ij => A ij.1 ij.2) = symHalfPart A := by
  ext i j
  simp only [square_symHalfPoly, Matrix.map_apply, Matrix.of_apply, symHalfPart, symPart,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.one_apply, smul_eq_mul, map_sub, map_mul, map_add, eval_C, eval_X, Matrix.trace,
    Matrix.diag]
  split_ifs <;> simp [map_sum]

theorem square_skewPoly_eval (A : Matrix (Fin d) (Fin d) ℝ) :
    (square_skewPoly d).map (eval fun ij => A ij.1 ij.2) = skewPart A := by
  ext i j
  simp only [square_skewPoly, Matrix.map_apply, Matrix.of_apply, skewPart, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, map_sub, eval_C, eval_X]

theorem square_eval_trace (f : Fin d × Fin d → ℝ)
    (M : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Fin d) ℝ)) :
    eval f M.trace = (M.map (eval f)).trace := by
  simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

/-- The polynomial `g` in the entries. -/
noncomputable def square_gPoly (d : ℕ) : MvPolynomial (Fin d × Fin d) ℝ :=
  let SH := square_symHalfPoly d
  let SK := square_skewPoly d
  C (-(8 / 5)) * (((SKᵀ * SK)ᵀ * (SKᵀ * SK)).trace - C (15 / 2) * ((SK * SH)ᵀ * (SK * SH)).trace -
    C (95 / 4) * ((SHᵀ * SH)ᵀ * (SHᵀ * SH)).trace)

theorem square_gPoly_hom : (square_gPoly d).IsHomogeneous 4 := by
  have h1 := square_symHalfPoly_hom (d := d)
  have h2 := square_skewPoly_hom (d := d)
  have hA : square_IsHomMat 2 ((square_skewPoly d)ᵀ * square_skewPoly d) := h2.transpose.mul h2
  have hB : square_IsHomMat 2 (square_skewPoly d * square_symHalfPoly d) := h2.mul h1
  have hC : square_IsHomMat 2 ((square_symHalfPoly d)ᵀ * square_symHalfPoly d) :=
    h1.transpose.mul h1
  have t1 := (hA.transpose.mul hA).trace
  have t2 := (hB.transpose.mul hB).trace
  have t3 := (hC.transpose.mul hC).trace
  exact ((t1.sub (t2.C_mul _)).sub (t3.C_mul _)).C_mul _

theorem square_gPoly_eval (A : Matrix (Fin d) (Fin d) ℝ) :
    gSquare d A = eval (fun ij => A ij.1 ij.2) (square_gPoly d) := by
  simp only [square_gPoly, map_mul, map_sub, eval_C, square_eval_trace, Matrix.map_mul,
    Matrix.transpose_map, square_symHalfPoly_eval, square_skewPoly_eval]
  rw [gSquare, square_squareU_eq]
  rfl

end Poly

/-- `g ≤ h_{4,4,98^{1/4}}`: `(8/5) U (X, Y) ≥ ‖Y‖_{S_4}⁴ − 98 ‖X‖_{S_4}⁴`, from Hölder's
`‖YX‖_{S_2} ≤ ‖Y‖_{S_4} ‖X‖_{S_4}` (here Cauchy–Schwarz `⟨YᵀY, XXᵀ⟩ ≤ ‖YᵀY‖_F ‖XXᵀ‖_F`) and
`(3/5) (‖Y‖² − 10 ‖X‖²)² ≥ 0`. -/
theorem square_gSquare_le_hF (M : Matrix (Fin d) (Fin d) ℝ) :
    gSquare d M ≤ hF d 4 4 ((98 : ℝ) ^ (1 / 4 : ℝ)) M := by
  set X := symHalfPart M
  set Y := skewPart M
  have hX : Xᵀ = X := square_symHalfPart_transpose M
  have hsym : ∀ Z : Matrix (Fin d) (Fin d) ℝ, (Zᵀ * Z)ᵀ = Zᵀ * Z := fun Z => by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have h98 : ((98 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = 98 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [square_hF_eq, h98, gSquare, square_squareU_eq]
  -- `‖YX‖_F² = ⟨YᵀY, XXᵀ⟩` and `‖XXᵀ‖_F = ‖XᵀX‖_F` (`X` symmetric)
  have hm : squareFrob (Y * X) (Y * X) = squareFrob (Yᵀ * Y) (X * X) := by
    simp only [squareFrob, Matrix.transpose_mul, hX, hsym]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm X, Matrix.mul_assoc, Matrix.mul_assoc]
    simp only [Matrix.mul_assoc]
  have hXX : squareFrob (X * X) (X * X) = squareFrob (Xᵀ * X) (Xᵀ * X) := by rw [hX]
  have hcs := squareFrob_le_sqrt (Yᵀ * Y) (X * X)
  rw [hXX] at hcs
  have hy := squareFrob_self_nonneg (Yᵀ * Y)
  have hx := squareFrob_self_nonneg (Xᵀ * X)
  set s := √(squareFrob (Yᵀ * Y) (Yᵀ * Y))
  set r := √(squareFrob (Xᵀ * X) (Xᵀ * X))
  have hs2 : s ^ 2 = squareFrob (Yᵀ * Y) (Yᵀ * Y) := Real.sq_sqrt hy
  have hr2 : r ^ 2 = squareFrob (Xᵀ * X) (Xᵀ * X) := Real.sq_sqrt hx
  have h1 : squareFrob (Y * X) (Y * X) ≤ s * r := by
    rw [hm]; exact (le_abs_self _).trans hcs
  have hT : ∀ Z : Matrix (Fin d) (Fin d) ℝ, (Zᵀ * Z * (Zᵀ * Z)).trace = squareFrob (Zᵀ * Z) (Zᵀ * Z) :=
    fun Z => by rw [squareFrob, hsym]
  rw [hT, hT, ← hs2, ← hr2]
  rw [← hs2, ← hr2] at *
  nlinarith [sq_nonneg (s - 10 * r)]

end Cor64

/-- **Corollary 6.4** (`cor:polsquare`): `g` is a rank-one convex homogeneous quartic polynomial
and `g ≤ h_{4,4,98^{1/4}}`.

Proof (the paper's sketch, completed). `g ≤ h_{4,4,98^{1/4}}`: `(8/5) U ≥ ‖Y‖⁴ − 98 ‖X‖⁴` from
Hölder's `‖YX‖_{S_2} ≤ ‖Y‖_{S_4} ‖X‖_{S_4}` and `(3/5) (‖Y‖² − 10 ‖X‖²)² ≥ 0`
(`square_gSquare_le_hF`). Rank-one convexity: along `A + tR`, `R` of rank one, `g` is a quartic in
`t` whose second derivative at `t` is `−(16/5)` times the second-order coefficient of
`s ↦ U (X + s D, Y + s E)` at the base point `A + tR` (`square_gSquare_line`,
`square_quartic_coeff2`), and that coefficient is `≤ 0` by the zig-zag concavity of `U`
(`square_zigzag`, with the paper's `a ≤ b`, `c ≤ e`, the bound on `⟨W, Z⟩` of inventory E7, and the
quadratic-form chain), since `D² + E² = ¼ tr (R)² Id` for `D = Sym_{1/2} R`, `E = Skew R`
(`square_rankOne_sq`, the rank-one fact `EEᵀ ⪯ D²`). `g` is the evaluation of a homogeneous
quartic `MvPolynomial` (`square_gPoly`). -/
theorem corollary6_4 (d : ℕ) :
    RankOneConvex (gSquare d) ∧ IsHomogeneousPolynomial 4 (gSquare d) ∧
      ∀ M, gSquare d M ≤ hF d 4 4 ((98 : ℝ) ^ (1 / 4 : ℝ)) M :=
  ⟨square_gSquare_rankOneConvex, ⟨square_gPoly d, square_gPoly_hom, square_gPoly_eval⟩,
    square_gSquare_le_hF⟩

/-! ### Corollary 6.4, conclusion, and Theorem 1.4 at `p = 4` -/

section Main

/-- `g` is continuous (a polynomial in the entries). -/
theorem square_continuous_gSquare : Continuous (gSquare d) := by
  have h1 := square_continuous_symHalfPart (d := d)
  have h2 := square_continuous_skewPart (d := d)
  have : gSquare d = fun A => -(8 / 5) *
      ((((skewPart A)ᵀ * skewPart A)ᵀ * ((skewPart A)ᵀ * skewPart A)).trace -
        15 / 2 * ((skewPart A * symHalfPart A)ᵀ * (skewPart A * symHalfPart A)).trace -
        95 / 4 * (((symHalfPart A)ᵀ * symHalfPart A)ᵀ * ((symHalfPart A)ᵀ * symHalfPart A)).trace) := by
    funext A; rw [gSquare, square_squareU_eq]; rfl
  rw [this]
  fun_prop

theorem square_gSquare_zero : gSquare d 0 = 0 := by
  rw [gSquare, square_squareU_eq, square_symHalfPart_zero, square_skewPart_zero]
  simp [squareFrob]

/-- If `g ≤ h`, `g (0) = h (0)` and `h` is not quasiconvex at `0`, neither is `g` (for a
continuous `g`). -/
theorem square_not_quasiconvexAt_of_le {m n : ℕ} {g h : Matrix (Fin m) (Fin n) ℝ → ℝ}
    (hg : Continuous g) (hle : ∀ M, g M ≤ h M) (h0 : g 0 = h 0) (hh : ¬ QuasiconvexAt h 0) :
    ¬ QuasiconvexAt g 0 := by
  intro hqc
  apply hh
  intro φ K hφ hz hint
  have hint' := integrableOn_comp_jac hg 0 hφ
  calc h 0 = g 0 := h0.symm
    _ ≤ ∫ x in unitCube n, g (0 + jac φ x) := hqc φ K hφ hz hint'
    _ ≤ ∫ x in unitCube n, h (0 + jac φ x) :=
      MeasureTheory.setIntegral_mono hint' hint fun x => hle _

end Main

/-- **Corollary 6.4** (`cor:polsquare`), the conclusion of its proof: "since `h_{4,4,98^{1/4}}`
fails to be quasiconvex at `0` in sufficiently high dimension, so does `g`". Reading: by
Proposition 6.6, `(d² − d + 1) / (6d − 9) > 98` exactly for `d ≥ 588`.

Proof: by Proposition 6.6, `C^{qc} (d)⁴ ≥ (d² − d + 1) / (6d − 9) > 98 = (98^{1/4})⁴`, so
`h_{4,4,98^{1/4}}` is not quasiconvex at `0` (otherwise `C^{qc} (d) ≤ 98^{1/4}`); and
`g ≤ h_{4,4,98^{1/4}}` (Corollary 6.4) with `g (0) = h_{4,4,98^{1/4}} (0) = 0`. -/
theorem corollary6_4_not_quasiconvexAt (d : ℕ) (hd : 588 ≤ d) :
    ¬ QuasiconvexAt (gSquare d) 0 := by
  have h66 := proposition6_6 d (by omega)
  set C : ℝ := (98 : ℝ) ^ (1 / 4 : ℝ) with hCdef
  have hC0 : 0 ≤ C := Real.rpow_nonneg (by norm_num) _
  have hC4 : C ^ 4 = 98 := by
    rw [hCdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hdR : (588 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < 6 * (d : ℝ) - 9 := by linarith
  have hr : 98 < ((d : ℝ) ^ 2 - d + 1) / (6 * d - 9) := by
    rw [lt_div_iff₀ hden]; nlinarith
  have hh : ¬ QuasiconvexAt (hF d 4 4 C) 0 := by
    intro hqc
    have hle : qcThreshold (hF d 4 4) ≤ ENNReal.ofReal C := iInf₂_le C ⟨hC0, hqc⟩
    have h4 : qcThreshold (hF d 4 4) ^ 4 ≤ ENNReal.ofReal 98 := by
      rw [← hC4, ENNReal.ofReal_pow hC0]; gcongr
    have := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 (h66.trans h4)
    linarith
  exact square_not_quasiconvexAt_of_le square_continuous_gSquare (corollary6_4 d).2.2
    (by rw [square_gSquare_zero, square_hF_zero]) hh

/-- `Sym_{1/2}`, `Skew` and `g` under orthogonal conjugation and transposition. -/
theorem square_conj_parts {U : Matrix (Fin d) (Fin d) ℝ} (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) :
    symHalfPart (U * A * Uᵀ) = U * symHalfPart A * Uᵀ ∧
      skewPart (U * A * Uᵀ) = U * skewPart A * Uᵀ := by
  have htr : (U * (A * Uᵀ)).trace = A.trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have h1 : U * (1 : Matrix (Fin d) (Fin d) ℝ) * Uᵀ = 1 := by rw [Matrix.mul_one, hU']
  constructor
  · simp only [symHalfPart, symPart, htr, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, h1, Matrix.mul_assoc]
  · simp only [skewPart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem square_frob_conj {U : Matrix (Fin d) (Fin d) ℝ} (hU : Uᵀ * U = 1)
    (P Q : Matrix (Fin d) (Fin d) ℝ) :
    squareFrob (U * P * Uᵀ) (U * Q * Uᵀ) = squareFrob P Q := by
  simp only [squareFrob, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc (U * (Pᵀ * Uᵀ) * (U * Q * Uᵀ)).trace = (U * (Pᵀ * (Uᵀ * U) * Q) * Uᵀ).trace := by
        simp only [Matrix.mul_assoc]
    _ = (Pᵀ * Q).trace := by
        rw [hU, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- **Theorem 1.4 at `p = 4`** (`cs-thm1.4-p4`): for every `d ≥ d₀ = 588` there is a
conjugation- and transposition-invariant, `4`-homogeneous integrand `f : ℝ^{d×d} → ℝ` which is
rank-one convex but nowhere quasiconvex; namely the explicit quartic polynomial `g` of
Corollary 6.4. Unconditional.

This is Theorem 1.4 (`theorem1_4`, `thm:main`) specialised to `p = 4`, with `d₀ (4) = 588`, by the
route that the paper gives in Section 6.3 (TeX lines 2550–2690): the "simple, somewhat
quantitative proof" for `p = q = 4` through Proposition 6.6 (the lower bound on `C^{qc} (d)`) and
Corollary 6.4 (the rank-one convex quartic `g ≤ h_{4,4,98^{1/4}}`, which "fails to be quasiconvex
at `0` in sufficiently high dimension"). It is a special case proved by a route the paper gives,
not a departure: it does not use Propositions 6.2 and 6.5 of the general proof.
The remaining properties of `g`, which Theorem 1.4 asks for but the paper does not state for `g`,
are immediate from its form: `U (O X Oᵀ, O Y Oᵀ) = U (X, Y)` for orthogonal `O`,
`Sym_{1/2} (Mᵀ) = Sym_{1/2} (M)`, `Skew (Mᵀ) = −Skew (M)` and `U (X, −Y) = U (X, Y)`, `g` is a
homogeneous quartic (so `4`-homogeneous) and continuous (so an integrand); nowhere quasiconvexity
follows from the failure at `0` by homogeneity (`nowhereQuasiconvex_of_not_quasiconvexAt_zero`,
the consequence of Proposition 2.3 at TeX lines 206–209, as in the paper's general proof). -/
theorem theorem1_4_four : ∀ d ≥ 588, ∃ f : Matrix (Fin d) (Fin d) ℝ → ℝ,
    IsIntegrand f ∧ IsConjugationInvariant f ∧ IsTranspositionInvariant f ∧
      IsPHomogeneous 4 f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  intro d hd
  have hcont := square_continuous_gSquare (d := d)
  -- `4`-homogeneity
  have hhom : IsPHomogeneous 4 (gSquare d) := by
    intro t A
    have h1 : symHalfPart (t • A) = t • symHalfPart A := by
      simpa [square_symHalfPart_zero] using
        square_symHalfPart_add_smul (0 : Matrix (Fin d) (Fin d) ℝ) A t
    have h2 : skewPart (t • A) = t • skewPart A := by
      simpa [square_skewPart_zero] using
        square_skewPart_add_smul (0 : Matrix (Fin d) (Fin d) ℝ) A t
    have ht : |t| ^ (4 : ℝ) = t ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs,
        abs_of_nonneg (by positivity)]
    rw [ht, gSquare, gSquare, square_squareU_eq, square_squareU_eq, h1, h2]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      squareFrob_smul_left, squareFrob_smul_right]
    ring
  refine ⟨gSquare d, ⟨hcont.lowerSemicontinuous, fun A => ?_⟩, ?_, ?_, hhom,
    (corollary6_4 d).1, ?_⟩
  · -- locally bounded
    refine ⟨gSquare d ⁻¹' Set.Ioo (gSquare d A - 1) (gSquare d A + 1),
      hcont.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)),
      |gSquare d A| + 1, fun B hB => ?_⟩
    have hB' : gSquare d B ∈ Set.Ioo (gSquare d A - 1) (gSquare d A + 1) := hB
    have := hB'.1; have := hB'.2
    rw [abs_le]; constructor <;> linarith [neg_abs_le (gSquare d A), le_abs_self (gSquare d A)]
  · -- conjugation invariance
    intro U hU A
    have hU' : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).1 hU
    have hU'' : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hU
    obtain ⟨hs, hk⟩ := square_conj_parts hU' hU'' A
    have hc : ∀ P : Matrix (Fin d) (Fin d) ℝ, (U * P * Uᵀ)ᵀ * (U * P * Uᵀ) = U * (Pᵀ * P) * Uᵀ := by
      intro P
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      calc Uᵀᵀ * (Pᵀ * Uᵀ) * (U * P * Uᵀ) = U * (Pᵀ * (Uᵀ * U) * P) * Uᵀ := by
            rw [Matrix.transpose_transpose]; simp only [Matrix.mul_assoc]
        _ = U * (Pᵀ * P) * Uᵀ := by rw [hU', Matrix.mul_one]
    have hp : (U * skewPart A * Uᵀ) * (U * symHalfPart A * Uᵀ) =
        U * (skewPart A * symHalfPart A) * Uᵀ := by
      calc (U * skewPart A * Uᵀ) * (U * symHalfPart A * Uᵀ) =
          U * (skewPart A * (Uᵀ * U) * symHalfPart A) * Uᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU', Matrix.mul_one]
    rw [gSquare, gSquare, square_squareU_eq, square_squareU_eq, hs, hk, hc, hc, hp,
      square_frob_conj hU', square_frob_conj hU', square_frob_conj hU']
  · -- transposition invariance
    intro A
    have hs : symHalfPart Aᵀ = symHalfPart A := by
      simp only [symHalfPart, symPart, Matrix.transpose_transpose, Matrix.trace_transpose,
        add_comm]
    have hk : skewPart Aᵀ = -skewPart A := by
      simp only [skewPart, Matrix.transpose_transpose]
      rw [← smul_neg, neg_sub]
    rw [gSquare, gSquare, square_squareU_eq, square_squareU_eq, hs, hk]
    simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
      squareFrob_neg_left, squareFrob_neg_right]
  · -- nowhere quasiconvex: not quasiconvex at `0` (Corollary 6.4), and homogeneity
    exact nowhereQuasiconvex_of_not_quasiconvexAt_zero (by norm_num : (1:ℝ) < 4) hcont
      (Or.inl hhom) (corollary6_4_not_quasiconvexAt d hd)

end Cassese
