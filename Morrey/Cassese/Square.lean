module

public import Morrey.Cassese.Toolkit
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Section 6: the square case `ℝ^{d×d}`

* `symPart A = (A + Aᵀ)/2`, `skewPart A = (A − Aᵀ)/2`, `symHalfPart A = Sym A − ½ tr (A) Id`
  (`Sym_{1/2}`, Section 6.4);
* `kornF d p q C (A) = C^p ‖Sym A‖_{S_q}^p − ‖Skew A‖_{S_q}^p`, the integrand (30), with thresholds
  `C^{rc} (S_q^{d×d}, p) = rcThreshold (kornF d p q)` and
  `C^{qc} (S_q^{d×d}, p) = qcThreshold (kornF d p q)`;
* `hF d p q C (A) = C^p ‖Sym_{1/2} A‖_{S_q}^p − ‖Skew A‖_{S_q}^p` (Section 6.3), with
  `C^{rc} (d) = rcThreshold (hF d 4 4)` and `C^{qc} (d) = qcThreshold (hF d 4 4)` (Section 6.4);
* `gSquare d` and the function `U` of Corollary 6.4.

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

/-- `Sym_{1/2} (A) = Sym (A) − ½ tr (A) Id` (Section 6.4). -/
noncomputable def symHalfPart (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  symPart A - ((1 / 2 : ℝ) * A.trace) • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The integrand (30): `f_{p,q,C} (A) = C^p ‖Sym (A)‖_{S_q}^p − ‖Skew (A)‖_{S_q}^p`. -/
noncomputable def kornF (d : ℕ) (p : ℝ) (q : ℝ≥0∞) (C : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  C ^ p * schattenNorm q (symPart A) ^ p - schattenNorm q (skewPart A) ^ p

/-- The integrand of Section 6.3:
`h_{p,q,C} (A) = C^p ‖Sym (A) − ½ tr (A) Id‖_{S_q}^p − ‖Skew (A)‖_{S_q}^p`. -/
noncomputable def hF (d : ℕ) (p : ℝ) (q : ℝ≥0∞) (C : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  C ^ p * schattenNorm q (symHalfPart A) ^ p - schattenNorm q (skewPart A) ^ p

/-- Fact (1) of Section 1.5, stated for every `q ≥ 1` (the paper states it for `q ≥ 2` and the
proof of Proposition 6.2 uses it for `q / 2 ∈ (1, 2)`, inventory E2): for self-adjoint `A`,
`‖A²‖_{S_q} = ‖A‖_{S_{2q}}²`. One of the facts that the paper calls "immediate consequences of
the definitions (see also Bhatia, *Matrix analysis*, Chapter 4)". -/
theorem schattenNorm_mul_self {q : ℝ} (hq : 1 ≤ q) {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm) :
    schattenNorm (ENNReal.ofReal q) (A * A) = schattenNorm (ENNReal.ofReal (2 * q)) A ^ 2 := by
  sorry

/-- Fact (2) of Section 1.5, first part: `‖A‖_{S_1} ≥ ‖A‖_{S_p} ≥ ‖A‖_{S_q} ≥ ‖A‖_{S_∞}` for
`p ≤ q`. -/
theorem schattenNorm_anti {m : ℕ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (A : Matrix (Fin d) (Fin m) ℝ) : schattenNorm q A ≤ schattenNorm p A := by
  sorry

/-- Fact (2) of Section 1.5, second part: `‖A‖_{S_p} ≤ min (d, m)^{1/p − 1/q} ‖A‖_{S_q}` for
`1 ≤ p ≤ q ≤ ∞` (with `1/∞ = 0`). -/
theorem schattenNorm_le_rpow_mul {m : ℕ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm p A ≤ (min d m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * schattenNorm q A := by
  sorry

/-- Fact (3) of Section 1.5: if `0 ⪯ A ⪯ B` (Loewner order) then `‖A‖_{S_q} ≤ ‖B‖_{S_q}` for
every `q ∈ [1, ∞]`. -/
theorem schattenNorm_mono {q : ℝ≥0∞} (hq : 1 ≤ q) {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) : schattenNorm q A ≤ schattenNorm q B := by
  sorry

/-! ### The Schatten norm is a norm

The paper takes for granted that `‖·‖_{S_q}`, `q ∈ [1, ∞]`, is a norm on `ℝ^{d×m}` (Section 1.5,
TeX lines 348–357; Bhatia, *Matrix analysis*, Chapter IV). Propositions 6.2, 6.5 and
Corollary 6.1 apply `HNVWExtrapolation` and `CoxVeraarDecoupling` to `S_q^{d×d}`, that is to
`E = Fin d → Fin d → ℝ` with `nrm X = ‖X‖_{S_q}`, which requires the hypotheses on `nrm` of those
statements: the triangle inequality, absolute homogeneity, and equivalence with the norm of `E`
(the supremum norm of the entries). They are stated here (to be proved), and bundled in
`schattenNorm_renorms`. -/

/-- The Schatten norm is nonnegative. -/
theorem schattenNorm_nonneg {m : ℕ} (q : ℝ≥0∞) (A : Matrix (Fin d) (Fin m) ℝ) :
    0 ≤ schattenNorm q A := by
  unfold schattenNorm
  split_ifs
  · exact Real.iSup_nonneg fun i => Real.sqrt_nonneg _
  · exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (Real.sqrt_nonneg _) _) _

/-- The triangle inequality for `‖·‖_{S_q}`, `q ∈ [1, ∞]` (Bhatia, Chapter IV). -/
theorem schattenNorm_add_le {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B := by
  sorry

/-- Absolute homogeneity of `‖·‖_{S_q}`, `q ∈ [1, ∞]`: `s_i (c A) = |c| s_i (A)`. -/
theorem schattenNorm_smul {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) (c : ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm q (c • A) = |c| * schattenNorm q A := by
  sorry

/-- `‖·‖_{S_q}`, `q ∈ [1, ∞]`, is positive definite: `‖A‖_{S_q} = 0` only for `A = 0`. -/
theorem schattenNorm_eq_zero_iff {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (A : Matrix (Fin d) (Fin m) ℝ) : schattenNorm q A = 0 ↔ A = 0 := by
  sorry

/-- The lower comparison with the supremum norm of the entries: `|A_{ij}| ≤ s_max (A) ≤ ‖A‖_{S_q}`
for `q ∈ [1, ∞]`. -/
theorem norm_le_schattenNorm {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) (X : Fin d → Fin m → ℝ) :
    ‖X‖ ≤ schattenNorm q (Matrix.of X) := by
  sorry

/-- The upper comparison with the supremum norm of the entries, with an explicit constant:
`‖A‖_{S_q} ≤ ‖A‖_{S_1} ≤ √m ‖A‖_{S_2} ≤ √m √(d m) max |A_{ij}| ≤ d m max |A_{ij}|` for
`q ∈ [1, ∞]`. -/
theorem schattenNorm_le_norm {m : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) (X : Fin d → Fin m → ℝ) :
    schattenNorm q (Matrix.of X) ≤ (d * m : ℝ) * ‖X‖ := by
  sorry

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

/-- The sharpness of Burkholder's constant for dyadic martingale transforms, as used for the
lower bound of Corollary 6.3: for `p ∈ (1, ∞)` and `K < p* − 1` there are a real dyadic martingale
`f_N = Σ_{k<N} ε_k φ_k` (predictable `φ_k`) and predictable signs `σ_k` with
`‖Σ_{k<N} σ_k ε_k φ_k‖_{L^p} > K ‖f_N‖_{L^p}`.

How the paper cites it: the proof of Corollary 6.3 (TeX lines 2624–2633) takes "a dyadic
martingale `f_n` and `g_n` a `±1` transform of it" and says "by choosing the martingale-transform
pair suitably (see also [Cassese 2025, *Martingales, laminates and minimal Korn inequalities*,
J. Math. Pures Appl. 213]), this construction shows `C^{rc} (d) ≥ 4* − 1 = 3`"; it names no
source for the sharpness itself. The sharpness of `p* − 1` for dyadic (Paley–Walsh) martingales
is D. L. Burkholder, *An elementary proof of an inequality of R. E. A. C. Paley*, Bull. London
Math. Soc. 17 (1985); it also follows from the sharpness for general martingale transforms
(Burkholder, Ann. Probab. 12 (1984): `UMD_p (ℝ) = p* − 1`) and Proposition 2.7 (4)
(`HNVWDyadicUMD`, HNVW I, Theorem 4.2.5: the dyadic UMD constant is the UMD constant) with
`X = ℝ`. Neither Burkholder paper was consulted. Large but feasible (class L of the inventory): a
proposition with no proof, a hypothesis of every statement whose proof uses it. Defined here
because it is stated with the shared definitions of `Morrey/Cassese/Defs.lean`. -/
def BurkholderSharpness : Prop :=
  ∀ p : ℝ, 1 < p → ∀ K : ℝ, K < pStar p - 1 →
    ∃ (N : ℕ) (φ σ : Fin N → (Fin N → Bool) → ℝ), IsPredictable φ ∧ IsPredictable σ ∧
      (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) ∧
      K * lpNormWith (fun x => |x|) p (mart φ N) <
        lpNormWith (fun x => |x|) p (mart (fun k ε => σ k ε * φ k ε) N)

/-- **Proposition 6.1** (`prop:qcboundsquare`): for `q ∈ [2, ∞]` there is `c_q > 0` such that for
every `d ≥ 2` and `p ∈ [1, ∞)`, `C^{qc} (S_q^{d×d}, p) ≥ c_q d^{1 − 1/q} / min (√(d p), d)`. -/
theorem proposition6_1 (q : ℝ≥0∞) (hq : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ p : ℝ, 1 ≤ p →
      ENNReal.ofReal (c * (d : ℝ) ^ (1 - 1 / q.toReal) / min (√((d : ℝ) * p)) d) ≤
        qcThreshold (kornF d p q) := by
  sorry

/-- **Proposition 6.2** (`prop:qgenp2`): for `q ∈ (2, ∞)` there is `C_q` such that for every
`d ≥ 2`, `C^{rc} (S_q^{d×d}, 2) ≤ C_q d^{1/4 − 1/(2q)}`. Conditional on Proposition 2.7 (2)
(Randrianantoanina), Proposition 2.8 (decoupling), Proposition 6.3 (non-commutative Khintchine)
and Proposition 6.4 (Kahane–Khintchine). -/
theorem proposition6_2 (hR : RandrianantoaninaSchattenUMD)
    (hCV : CoxVeraarDecoupling) (hPX : PisierXuKhintchine)
    (hKK : KahaneKhintchine) (q : ℝ) (hq : 2 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      rcThreshold (kornF d 2 (ENNReal.ofReal q)) ≤
        ENNReal.ofReal (C * (d : ℝ) ^ (1 / 4 - 1 / (2 * q))) := by
  sorry

/-- **Equation (31)** (`eq:KKgen`): for `q ∈ [2, ∞)` and `p ∈ (1, ∞)`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≈_{p,q} (E ‖Σ ε_i x_i‖_{S_q}^p)^{1/p}` for normal `d × d` matrices
`x_i`, uniformly in `d` and `n`. Conditional on Propositions 6.3 and 6.4, which it combines.
(`‖B^{1/2}‖_{S_q} = ‖B‖_{S_{q/2}}^{1/2}` for the positive semidefinite `B = Σ x_i x_iᵀ`.) -/
theorem equation31 (hPX : PisierXuKhintchine) (hKK : KahaneKhintchine)
    (p q : ℝ) (hp : 1 < p) (hq : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d n : ℕ) (x : Fin n → Matrix (Fin d) (Fin d) ℝ),
      (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
        c⁻¹ * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
            lpNormWith (schattenNorm (ENNReal.ofReal q)) p
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ∧
          lpNormWith (schattenNorm (ENNReal.ofReal q)) p
              (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
            c * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) := by
  sorry

/-- **Remark 6.3** (`rmk:interpolation`): tracking the constants in the proof of Proposition 6.2,
for every rank-one Rademacher martingale `M` in `ℝ^{d×d}` started at `0`, with `f = Sym M` and
`g = Skew M`, `‖g_N‖_{L² (S_q)} ≲ d^{1/4} q³ d^{−1/(2q)} ‖f_N‖_{L² (S_q)}` and
`‖g_N‖_{L² (S_∞)} ≲ d^{1/4} q³ d^{1/(2q)} ‖f_N‖_{L² (S_∞)}` for `q ∈ (2, ∞)`, with absolute
constants; with `q ≈ log d`, `C^{rc} (S_∞^{d×d}, 2) ≲ d^{1/4} log³ d`. Conditional as
Proposition 6.2. -/
theorem remark6_3 (hR : RandrianantoaninaSchattenUMD)
    (hCV : CoxVeraarDecoupling) (hPX : PisierXuKhintchine)
    (hKK : KahaneKhintchine) :
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
  sorry

/-- **Proposition 6.5** (`cs-prop6.5`): for `q ∈ (2, ∞)` and `p ∈ (1, ∞)` there is `C_{q,p}` with
`C^{rc} (S_q^{d×d}, p) ≤ C_{q,p} d^{1/4 − 1/(2q)}` for every `d ≥ 2`; and for every `p ∈ (1, ∞)`
there are `α > 0` and `C_p` with `C^{rc} (S_∞^{d×d}, p) ≤ C_p d^{1/4} log^α d` for every `d ≥ 2`.
Conditional on Propositions 2.7 (1), (2), 2.8, 6.3, 6.4 and Burkholder's square function
inequality (Theorem 2.3 (2)). Reading: `α` may depend on `p`. -/
theorem proposition6_5 (hH : HNVWExtrapolation)
    (hR : RandrianantoaninaSchattenUMD) (hCV : CoxVeraarDecoupling)
    (hPX : PisierXuKhintchine) (hKK : KahaneKhintchine)
    (hS : BurkholderSquareFunction) :
    (∀ q : ℝ, 2 < q → ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      rcThreshold (kornF d p (ENNReal.ofReal q)) ≤
        ENNReal.ofReal (C * (d : ℝ) ^ (1 / 4 - 1 / (2 * q)))) ∧
    ∀ p : ℝ, 1 < p → ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      rcThreshold (kornF d p ⊤) ≤ ENNReal.ofReal (C * (d : ℝ) ^ (1 / 4 : ℝ) * Real.log d ^ α) := by
  sorry

/-- **Periodic test maps for Hessian quasiconvexity** (`cs-hess-periodic`): a smooth
`ℤ^n`-periodic `φ : ℝ^n → ℝ` with `∫_{(0,1)^n} F (A + D²φ) < F (A)`, for a continuous `F`,
witnesses that `F` is not Hessian quasiconvex at `A` (whose test maps, `HessianQuasiconvexAt`,
have compact support in the open cube). The second-order analogue of the periodic
characterization of quasiconvexity (Lemma 2.2; Šverák's Lemma 1, `Sverak.lemma1_witness`):
the cut-off maps `η_k (x) N⁻² φ (N x)`, with `η_k ∈ C_c^∞ ((0,1)^n)` equal to `1` on
`[1/k, 1 − 1/k]^n`, have `D² = η_k (D²φ) (N ·) + O (k / N + k² / N²)`, so their integrals tend to
`∫_{(0,1)^n} F (A + D²φ)` as `N → ∞` and then `k → ∞`.

The proof of Corollary 6.1 (TeX lines 2489–2520) integrates over `𝕋^{2n}` with the
`2π`-periodic `φ (x, y) = Σ_{i,j} sin (x_i − y_j)`, which the paper treats as a test map of
Hessian quasiconvexity without comment. It reaches this lemma through `ψ (z) = φ (2π z)`, which is
`ℤ^{2n}`-periodic with `D²ψ (z) = 4π² D²φ (2π z)`: for the `p`-homogeneous `F` with `F (0) = 0`,
`∫_{(0,1)^{2n}} F (D²ψ) = (4π²)^p (2π)^{−2n} ∫_{[0, 2π]^{2n}} F (D²φ) < 0`. -/
theorem not_hessianQuasiconvexAt_of_periodic {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hF : Continuous F) {A : Matrix (Fin n) (Fin n) ℝ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hper : ∀ (x : Fin n → ℝ) (z : Fin n → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (hlt : ∫ x in unitCube n, F (A + hessian φ x) < F A) :
    ¬ HessianQuasiconvexAt F A := by
  sorry

/-- **Corollary 6.1** (`cor:symm`): for every `p ∈ (1, ∞)` there are `d` and an integrand
`F : Sym (d) → ℝ`, rank-one convex (convex along the lines `H + t a ⊗ a`) and `p`-homogeneous,
which is not Hessian quasiconvex at `0`, and hence is nowhere Hessian quasiconvex. `F` is given
on all of `ℝ^{d×d}`; only its values on symmetric matrices enter. Conditional as Proposition 6.5,
whose bound its proof uses. The proof's witness is the `2π`-periodic `Σ_{i,j} sin (x_i − y_j)`
on `𝕋^{2n}`; `not_hessianQuasiconvexAt_of_periodic` (`cs-hess-periodic`) turns it into a failure
of `HessianQuasiconvexAt`, whose test maps have compact support. -/
theorem corollary6_1 (hH : HNVWExtrapolation)
    (hR : RandrianantoaninaSchattenUMD) (hCV : CoxVeraarDecoupling)
    (hPX : PisierXuKhintchine) (hKK : KahaneKhintchine)
    (hS : BurkholderSquareFunction) (p : ℝ) (hp : 1 < p) :
    ∃ (d : ℕ) (F : Matrix (Fin d) (Fin d) ℝ → ℝ), IsIntegrand F ∧
      (∀ H : Matrix (Fin d) (Fin d) ℝ, H.IsSymm → ∀ a : Fin d → ℝ,
        ConvexOn ℝ Set.univ fun t : ℝ => F (H + t • Matrix.vecMulVec a a)) ∧
      (∀ (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ), H.IsSymm → F (t • H) = |t| ^ p * F H) ∧
      ¬ HessianQuasiconvexAt F 0 ∧
      ∀ A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm → ¬ HessianQuasiconvexAt F A := by
  sorry

/-- **Proposition 6.6** (`prop:qcexact4`): for every `d ≥ 2`,
`C^{qc} (d)⁴ ≥ (d² − d + 1) / (6d − 9)`. -/
theorem proposition6_6 (d : ℕ) (hd : 2 ≤ d) :
    ENNReal.ofReal (((d : ℝ) ^ 2 - d + 1) / (6 * d - 9)) ≤ qcThreshold (hF d 4 4) ^ 4 := by
  sorry

/-- **Theorem 6.2** (`thm:sharp2sided`): let `D_k ∈ ℝ^{d×d}` be predictable, all symmetric or all
skew-symmetric, `M_n = Σ_{k<n} ε_k D_k`, `V_k = D_kᵀ D_k`, `V̂ = Σ_k V_k`, `x² = E ‖M_N‖_{S_4}^4`,
`y² = E ‖V̂‖_{S_2}^2` (`x, y ≥ 0`). Then `x² − 6 x y + 3 y² ≤ 0` (32), that is
`z₋² y ≤ x ≤ z₊² y` with `z_±² = 3 ± √6`. -/
theorem theorem6_2 {N : ℕ} (D : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin d) ℝ)
    (hD : IsPredictable D)
    (hsym : (∀ k ε, (D k ε).IsSymm) ∨ ∀ k ε, (D k ε)ᵀ = -D k ε) :
    let x := √(avg fun ε => schattenNorm 4 (mart D N ε) ^ 4)
    let y := √(avg fun ε => schattenNorm 2 (∑ k, (D k ε)ᵀ * D k ε) ^ 2)
    x ^ 2 - 6 * x * y + 3 * y ^ 2 ≤ 0 ∧ (3 - √6) * y ≤ x ∧ x ≤ (3 + √6) * y := by
  sorry

/-- **Corollary 6.3** (`cor:uncond`), lower bound: `3 ≤ C^{rc} (d)` for every `d ≥ 2`.
Conditional on the sharpness of Burkholder's constant `4* − 1 = 3` for dyadic martingales. -/
theorem corollary6_3_lower (hS : BurkholderSharpness) (d : ℕ) (hd : 2 ≤ d) :
    ENNReal.ofReal 3 ≤ rcThreshold (hF d 4 4) := by
  sorry

/-- **Corollary 6.3** (`cor:uncond`), upper bound:
`C^{rc} (d) ≤ [3 (√3 + √2)² · ⅓ (√3 + √2)²]^{1/4} = √2 + √3` for every `d ≥ 2`. -/
theorem corollary6_3_upper (d : ℕ) (hd : 2 ≤ d) :
    rcThreshold (hF d 4 4) ≤ ENNReal.ofReal (√2 + √3) := by
  sorry

/-- **Corollary 6.3** (`cor:uncond`), separation: `C^{qc} (d) > C^{rc} (d)` whenever
`(d² − d + 1) / (6d − 9) > (5 + 2√6)² = 49 + 20√6`, that is, for every `d ≥ d₀ = 588`. -/
theorem corollary6_3_separation :
    (∀ d : ℕ, 2 ≤ d → (5 + 2 * √6) ^ 2 < ((d : ℝ) ^ 2 - d + 1) / (6 * d - 9) →
      rcThreshold (hF d 4 4) < qcThreshold (hF d 4 4)) ∧
    (∀ d : ℕ, 2 ≤ d → ((5 + 2 * √6) ^ 2 < ((d : ℝ) ^ 2 - d + 1) / (6 * d - 9) ↔ 588 ≤ d)) := by
  sorry

/-- The function `U (X, Y) = ‖Y‖_{S_4}^4 − (15/2) ‖Y X‖_{S_2}^2 − (95/4) ‖X‖_{S_4}^4` of
Corollary 6.4 (on `Sym (d) × Skew (d)`). -/
noncomputable def squareU (X Y : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  schattenNorm 4 Y ^ 4 - 15 / 2 * schattenNorm 2 (Y * X) ^ 2 -
    95 / 4 * schattenNorm 4 X ^ 4

/-- The quartic of Corollary 6.4: `g (M) = −(8/5) U (Sym_{1/2} (M), Skew (M))`. -/
noncomputable def gSquare (d : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  -(8 / 5) * squareU (symHalfPart M) (skewPart M)

/-- **Corollary 6.4** (`cor:polsquare`): `g` is a rank-one convex homogeneous quartic polynomial
and `g ≤ h_{4,4,98^{1/4}}`. -/
theorem corollary6_4 (d : ℕ) :
    RankOneConvex (gSquare d) ∧ IsHomogeneousPolynomial 4 (gSquare d) ∧
      ∀ M, gSquare d M ≤ hF d 4 4 ((98 : ℝ) ^ (1 / 4 : ℝ)) M := by
  sorry

/-- **Corollary 6.4** (`cor:polsquare`), the conclusion of its proof: "since `h_{4,4,98^{1/4}}`
fails to be quasiconvex at `0` in sufficiently high dimension, so does `g`". Reading: by
Proposition 6.6, `(d² − d + 1) / (6d − 9) > 98` exactly for `d ≥ 588`. -/
theorem corollary6_4_not_quasiconvexAt (d : ℕ) (hd : 588 ≤ d) :
    ¬ QuasiconvexAt (gSquare d) 0 := by
  sorry

end Cassese
