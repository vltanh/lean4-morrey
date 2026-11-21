module

public import Cassese.Toolkit
public import External.Burkholder.ScalarFunction
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Section 4: Morrey's problem in `ℝ^{2×m}`

`ℝ^{2×2n}` is written as `(A₁ | ⋯ | A_n)` with `2 × 2` blocks; block `j` (from `0`) is formed by
the columns `2j` and `2j + 1` (`blockCol`). With both copies of `ℝ²` identified with `ℂ`, each
block acts as `z ↦ α_j z + β_j z̄`, and `P_n (A) = (α_j)_j`, `Q_n (A) = (β_j)_j ∈ ℂ^n` (`wirtP`,
`wirtQ`). `lqNorm q` is the `ℓ_q^n (ℂ)` norm `(Σ |z_j|^q)^{1/q}`, and
`blockF n p q C (A) = C^p ‖P_n A‖_q^p − ‖Q_n A‖_q^p` is the integrand (7), with thresholds
`C^{rc} (p, q, n) = rcThreshold (fun C => blockF n p q C)` and
`C^{qc} (p, q, n) = qcThreshold (fun C => blockF n p q C)`.

`ℓ_q (ℂ)` is `L^q (ℕ, counting measure; ℂ)`, and `umdEllq p q = UMD_{ℂ,p} (ℓ_q)`.

Expectations and `L^p` norms over a rank-one Rademacher martingale are averages over the signs
(`avg`, `lpNormWith`); `L^p` norms over `ℝ^{2n}` are `eLpNorm` for the
Lebesgue measure. `ℝ^{2n} ≅ ℂ^n` by `ξ ↦ (ξ_{2j} + i ξ_{2j+1})_j` (`blockZ`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Matrix ENNReal ComplexConjugate

namespace Cassese

/-- The column `2j + k` of `ℝ^{2×2n}`: column `k` of block `j`. -/
def blockCol {n : ℕ} (j : Fin n) (k : Fin 2) : Fin (2 * n) :=
  ⟨2 * j.val + k.val, by omega⟩

/-- `P_n (A) = (α₁ (A), …, α_n (A))` (Section 4.1). -/
noncomputable def wirtP {n : ℕ} (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) (j : Fin n) : ℂ :=
  wirtAlpha A (blockCol j 0) (blockCol j 1)

/-- `Q_n (A) = (β₁ (A), …, β_n (A))` (Section 4.1). -/
noncomputable def wirtQ {n : ℕ} (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) (j : Fin n) : ℂ :=
  wirtBeta A (blockCol j 0) (blockCol j 1)

/-- The `ℓ_q^n (ℂ)` norm `(Σ_j |z_j|^q)^{1/q}`. -/
noncomputable def lqNorm {n : ℕ} (q : ℝ) (z : Fin n → ℂ) : ℝ :=
  (∑ j, ‖z j‖ ^ q) ^ (1 / q)

/-- The integrand (7): `F_{n,p,q,C} (A) = C^p ‖P_n A‖_{ℓ_q^n}^p − ‖Q_n A‖_{ℓ_q^n}^p`. -/
noncomputable def blockF (n : ℕ) (p q C : ℝ) (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) : ℝ :=
  C ^ p * lqNorm q (wirtP A) ^ p - lqNorm q (wirtQ A) ^ p

/-- `1 ≤ ofReal q` from `1 ≤ q`. -/
theorem one_le_ofReal_of_one_le {q : ℝ} (h : 1 ≤ q) : 1 ≤ ENNReal.ofReal q := by
  rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h

/-- `UMD_{ℂ,p} (ℓ_q)`, with `ℓ_q (ℂ) = L^q (ℕ, counting measure; ℂ)` (`∞` for `q < 1`). -/
noncomputable def umdEllq (p q : ℝ) : ℝ≥0∞ :=
  if h : 1 ≤ q then
    haveI : Fact (1 ≤ ENNReal.ofReal q) := ⟨one_le_ofReal_of_one_le h⟩
    complexUMDConst (Lp ℂ (ENNReal.ofReal q) (Measure.count : Measure ℕ)) p
  else ⊤

/-- **Lemma 4.1** (`lem:rankonecomplex`, rank-one identity): there is a measurable `λ` such that
for every `R ∈ ℝ^{2×2n}` of rank at most one, `|λ (R)| = 1`, `Q_n R = λ (R) conj (P_n R)`
componentwise (8), and `λ (t R) = λ (R)` for every real `t ≠ 0`. -/
theorem lemma4_1 (n : ℕ) :
    ∃ lam : Matrix (Fin 2) (Fin (2 * n)) ℝ → ℂ, Measurable lam ∧
      ∀ R : Matrix (Fin 2) (Fin (2 * n)) ℝ, R.rank ≤ 1 →
        ‖lam R‖ = 1 ∧ (∀ j, wirtQ R j = lam R * conj (wirtP R j)) ∧
          ∀ t : ℝ, t ≠ 0 → lam (t • R) = lam R := by
  sorry

/-- **Proposition 4.1** (`prop:laminate`, uniform laminate bound), inequality (9): for every
rank-one Rademacher martingale `(M_k)_{k ≤ N}` in `ℝ^{2×2n}` (any start `M₀`) and
`p, q ∈ (1, ∞)`,
`‖Q_n (M_N) − Q_n (M₀)‖_{L^p (ℓ_q^n)} ≤ UMD_{ℂ,p} (ℓ_q) ‖P_n (M_N) − P_n (M₀)‖_{L^p (ℓ_q^n)}`.
(The section's standing assumption `q > p + 2` is not used and not assumed.) -/
theorem proposition4_1 {p q : ℝ} (hp : 1 < p) (hq : 1 < q) {n N : ℕ}
    (M₀ : Matrix (Fin 2) (Fin (2 * n)) ℝ)
    (A : Fin N → (Fin N → Bool) → Matrix (Fin 2) (Fin (2 * n)) ℝ) (hA : IsRankOneIncrements A) :
    ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtQ (radMart M₀ A N ε) - wirtQ M₀) ≤
      umdEllq p q *
        ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtP (radMart M₀ A N ε) - wirtP M₀) := by
  sorry

/-- **Proposition 4.1** (`prop:laminate`), final assertion: if `M₀ = 0` and
`C > UMD_{ℂ,p} (ℓ_q)`, then `E F_{n,p,q,C} (M_N) ≥ 0`. -/
theorem proposition4_1_nonneg {p q : ℝ} (hp : 1 < p) (hq : 1 < q) {n N : ℕ}
    (A : Fin N → (Fin N → Bool) → Matrix (Fin 2) (Fin (2 * n)) ℝ) (hA : IsRankOneIncrements A)
    {C : ℝ} (hC : umdEllq p q < ENNReal.ofReal C) :
    0 ≤ avg fun ε => blockF n p q C (radMart 0 A N ε) := by
  sorry

/-- **Equation (10)** (`eq:rank1bound`): `C^{rc} (p, q, n) ≤ UMD_{ℂ,p} (ℓ_q)` for every `n`. -/
theorem equation10 {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (n : ℕ) :
    rcThreshold (fun C => blockF n p q C) ≤ umdEllq p q := by
  sorry

/-- **Finiteness of UMD_{ℂ,p} (ℓ_q)** (`cs-ellq-umd`, lines 991–992, "by Proposition 2.7"):
for `p, q ∈ (1, ∞)`, `UMD_{ℂ,p} (ℓ_q) < ∞`. Conditional on Proposition 2.7 (1), (3), (5):
`ℓ_q` is UMD (Pisier), hence `UMD_p` (extrapolation, HNVW), hence complex `UMD_p`
(Yaroslavtsev). -/
theorem umdEllq_lt_top (hP : PisierLpUMD) (hH : HNVWExtrapolation)
    (hY : YaroslavtsevComplexUMD) {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    umdEllq p q < ⊤ := by
  sorry

/-- The point `(ξ_{2j} + i ξ_{2j+1})_j ∈ ℂ^n` of `ξ ∈ ℝ^{2n}`. -/
noncomputable def blockZ {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j : Fin n) : ℂ :=
  (ξ (blockCol j 0) : ℂ) + (ξ (blockCol j 1) : ℂ) * Complex.I

/-- The test map (11): `u_n (z) = (Π_j z̄_j) e^{−|z|²/2}` on `ℂ^n ≅ ℝ^{2n}`, with values in
`ℂ ≅ ℝ²`. -/
noncomputable def testU (n : ℕ) (ξ : Fin (2 * n) → ℝ) : Fin 2 → ℝ :=
  let w : ℂ := (∏ j, conj (blockZ ξ j)) * (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ)
  ![w.re, w.im]

/-- **Lemma 4.2** (`lem:order`): if `1 < p < ∞` and `p + 2 ≤ q < ∞`, then
`‖Q_n (∇u_n)‖_{L^p (ℂ^n; ℓ_q^n)} / ‖P_n (∇u_n)‖_{L^p (ℂ^n; ℓ_q^n)} → ∞` as `n → ∞` (12). -/
theorem lemma4_2 {p q : ℝ} (hp : 1 < p) (hpq : p + 2 ≤ q) :
    Tendsto (fun n : ℕ =>
        eLpNorm (fun ξ => lqNorm q (wirtQ (jac (testU n) ξ))) (ENNReal.ofReal p) volume /
          eLpNorm (fun ξ => lqNorm q (wirtP (jac (testU n) ξ))) (ENNReal.ofReal p) volume)
      atTop (𝓝 ⊤) := by
  sorry

/-- The integrand of Proposition 4.2: `f_n (A) = 5⁴ ‖P_n (A)‖_{ℓ_6}^3 − ‖Q_n (A)‖_{ℓ_6}^3`. -/
noncomputable def explicitF (n : ℕ) (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) : ℝ :=
  5 ^ 4 * lqNorm 6 (wirtP A) ^ 3 - lqNorm 6 (wirtQ A) ^ 3

/-- Burkholder's scalar function for the exponent `6` (proof of Proposition 4.2):
`u (a, b) = α (|b| − 5 |a|) (|a| + |b|)^5`, `α = 6 (5/6)^5 = 5^5 / 6^4`. -/
noncomputable def burkholderU (a b : ℂ) : ℝ :=
  5 ^ 5 / 6 ^ 4 * (‖b‖ - 5 * ‖a‖) * (‖a‖ + ‖b‖) ^ 5

/-- `burkholderU` is the function of `External.Burkholder.ScalarFunction`. -/
theorem burkholderU_eq : burkholderU = External.Burkholder.u6 := rfl

/-- `R (x, y) = Σ_j (u (x_j, y_j) + 2 · 5^6 |x_j|^6)` (proof of Proposition 4.2). -/
noncomputable def burkholderR {n : ℕ} (x y : Fin n → ℂ) : ℝ :=
  ∑ j, (burkholderU (x j) (y j) + 2 * 5 ^ 6 * ‖x j‖ ^ 6)

/-- `B (x) = ‖x‖_{ℓ_6}^6` (proof of Proposition 4.2). -/
noncomputable def burkholderB {n : ℕ} (x : Fin n → ℂ) : ℝ :=
  ∑ j, ‖x j‖ ^ 6

/-- (15): `U (x, y) = R (x, y)^{1/2} − 5⁴ B (x)^{1/2}`. -/
noncomputable def zigzagU {n : ℕ} (x y : Fin n → ℂ) : ℝ :=
  √(burkholderR x y) - 5 ^ 4 * √(burkholderB x)

/-- The rank-one convex minorant of the proof of Proposition 4.2:
`g_n (A) = −U (conj (P_n (A)), Q_n (A))`. -/
noncomputable def explicitG (n : ℕ) (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) : ℝ :=
  -zigzagU (fun j => conj (wirtP A j)) (wirtQ A)

/-- **Proposition 4.2** (`prop:explicit`): `f_n` is rank-one convex at `0` (for every `n`; the
section fixes `n ∈ ℕ`). Conditional on Burkholder's properties (13), (14) of `u`. -/
theorem proposition4_2 (hB : External.Burkholder.ScalarFunction) (n : ℕ) :
    RankOneConvexAt (explicitF n) 0 := by
  sorry

/-- **Proposition 4.2** (`prop:explicit`), the claim of its proof: `g_n` is a globally rank-one
convex integrand with `g_n ≤ f_n` and `g_n (0) = 0 = f_n (0)`. Conditional on (13), (14). -/
theorem proposition4_2_minorant (hB : External.Burkholder.ScalarFunction) (n : ℕ) :
    IsIntegrand (explicitG n) ∧ RankOneConvex (explicitG n) ∧
      (∀ A, explicitG n A ≤ explicitF n A) ∧ explicitG n 0 = 0 ∧ explicitF n 0 = 0 := by
  sorry

/-- **Proposition 4.3** (`prop:elem`): for `n` large enough, `g_n` is not quasiconvex at `0`, and
hence it is not quasiconvex anywhere. Conditional on (13), (14) and on Dacorogna's formula.

Why Dacorogna's formula (TeX lines 1359–1366). The proof reads: if `g_n` were quasiconvex at `0`,
then `0 = g_n (0) = g_n^{qc} (0) ≤ f_n^{qc} (0) ≤ f_n (0) = 0`, contradicting that `f_n` is not
quasiconvex at `0`. The steps `g_n^{qc} ≤ f_n^{qc} ≤ f_n` and "`f_n^{qc} (0) = f_n (0)` makes `f_n`
quasiconvex at `0`" need no formula. The step `g_n (0) = g_n^{qc} (0)` does: `g_n` is assumed
quasiconvex at `0` only, and `g_n^{qc} (0) = g_n (0)` asks for a quasiconvex (at every matrix)
minorant of `g_n` touching it at `0`. That is the "only if" direction of line 559, which the paper
derives from Proposition 2.2 (Kinderlehrer–Pedregal); without the formula no such minorant is
available. So the hypothesis stays, on the paper's route (`cs-qc-minorant`). A shorter argument
would avoid it, by never forming the envelope: for each test map `φ`,
`∫ f_n (∇φ) ≥ ∫ g_n (∇φ) ≥ g_n (0) = 0 = f_n (0)` (`g_n` is continuous and `∇φ` bounded, so the
second integral exists), so `f_n` would be quasiconvex at `0`; it is recorded as a simplification,
not used, because it departs from the paper's proof. -/
theorem proposition4_3 (hB : External.Burkholder.ScalarFunction)
    (hKP : External.KinderlehrerPedregal.DacorognaFormula) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ¬ QuasiconvexAt (explicitG n) 0 ∧ NowhereQuasiconvex (explicitG n) := by
  sorry

end Cassese
