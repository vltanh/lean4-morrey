module

public import BanachProbability.Martingale.Burkholder.Inequality

/-!
# Differentially subordinate martingales and square functions (Osękowski, Theorems 3.5, 8.6)

A. Osękowski, *Sharp Martingale and Semimartingale Inequalities*, Monografie Matematyczne 72,
Birkhäuser 2012 (read), Theorem 3.5 (ii) (p. 53) and Theorem 8.6 (p. 413), which Cassese
(arXiv:2608.03488v3) quotes together as Theorem 2.3 (`cs-thm2.3`, TeX lines 721–739, "the
foundational result of Burkholder").

## Main results

* `theorem3_5`: the inequality of Theorem 3.5 (ii), in the book's form. For martingales `f`, `g`
  with values in a real Hilbert space, `g` differentially subordinate to `f` (`‖g_0‖ ≤ ‖f_0‖` and
  `‖g_{k+1} − g_k‖ ≤ ‖f_{k+1} − f_k‖` almost surely), and `1 < p < ∞`,
  `‖g_n‖_{L^p} ≤ (p* − 1) ‖f_n‖_{L^p}` with `p* = max (p, p / (p − 1))`. (That the constant is the
  best possible, the other half of (ii), is in `Osekowski/Sharpness.lean`; (i), on `p ≤ 1`, is not
  formalized.)
* `inequality` (Theorem 2.3 (1) of Cassese): the case of martingales started at `0`, in a separable
  Hilbert space, `X` subordinate to `Y`.
* `theorem8_6`: the inequalities (8.28) of Theorem 8.6 for a martingale `X` started at `0`,
  `‖𝒮_n X‖_{L^p} ≤ (p* − 1) ‖X_n‖_{L^p}` and `‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`,
  `𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`. (The clauses on the sharpness of the two constants
  are not formalized.)
* `squareFunction` (Theorem 2.3 (2) of Cassese): the same in a separable Hilbert space.

The book's norms are `‖f‖_p = sup_n ‖f_n‖_{L^p}`; the statements here are at a fixed time `n`, as
Cassese's, which is equivalent. Cassese's martingales start at `0` (his convention, TeX lines
389–390), so the term `‖X_0‖²` of the book's square function is absent.

## The proofs

The statements are from the package `BanachProbability` (`lean4-banach-probability`), which proves
them by the book's arguments.

* Theorem 3.5 (ii), pp. 53–54 (`1 < p < 2`) and 58 (`p > 2`), by the integration method (§2.3):
  Burkholder's function `U_p` majorizes `V_p (x, y) = |y|^p − (p* − 1)^p |x|^p`, and it is
  `∫_0^∞ k (t) u (x / t, y / t) dt` with `k ≥ 0` and a simple function `u`, (3.6) or (3.12), for
  which Burkholder's method (Theorem 2.7) gives `E u (f_n / t, g_n / t) ≤ 0`. So
  `E V_p (f_n, g_n) ≤ E U_p (f_n, g_n) ≤ 0` by Fubini's theorem. The case `p = 2` is orthogonality.
  The slips of the book on these pages (signs on pp. 27 and 29, an absolute value on p. 30; on p. 54
  the order of the concave and the convex part of the function `F` and the constant of the integral
  formula) are repaired along the book's own lines, and noted in the package's files
  `Martingale/Osekowski/`. With the right order, `U_p ≥ V_p` also needs the sign of `F` at an
  endpoint, which the book does not mention; this is (1.11) of Burkholder 1988 (below), whose proof
  of the majorization, (1.10), is the one used for that step.
* Theorem 8.6, p. 414, by the device of §2.1.3 (p. 16): `(X_m, 0, 0, …)` and `(dX_1, …, dX_m, 0, …)`
  in `ℓ² (H)` are differentially subordinate to each other, and Theorem 3.5 applies to both pairs.
  Up to the time `n` both live in `H^{n+1}`, where the package works.

The same inequalities, for Hilbert-space-valued martingales, are Theorems 1.1 and 3.1 of D. L.
Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Astérisque 157–158
(1988); his proofs, apart from the majorization, are not the ones followed.
-/

@[expose] public section

open MeasureTheory

namespace External.Osekowski

/-- **Osękowski (2012), Theorem 3.5 (ii)**, the inequality (3.59): if the martingale `g` is
differentially subordinate to the martingale `f` (values in a real Hilbert space) and `1 < p < ∞`,
then `‖g_n‖_{L^p} ≤ (p* − 1) ‖f_n‖_{L^p}` for every `n`, `p* = max (p, p / (p − 1))`. From
`BanachProbability.Osekowski.eLpNorm_le_of_subordinate`, by the book's integration method. -/
theorem theorem3_5 {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f g : ℕ → Ω → H} {p : ℝ} (hp : 1 < p) (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ)
    (hsub0 : ∀ᵐ ω ∂μ, ‖g 0 ω‖ ≤ ‖f 0 ω‖)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖g (n + 1) ω - g n ω‖ ≤ ‖f (n + 1) ω - f n ω‖) (n : ℕ) :
    eLpNorm (g n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (f n) (ENNReal.ofReal p) μ :=
  BanachProbability.Osekowski.eLpNorm_le_of_subordinate hp hf hg hsub0 hsub n

/-- **Burkholder's inequality** (Osękowski 2012, Theorem 3.5 (ii); Cassese, Theorem 2.3 (1)): for
martingales `X`, `Y` with values in a separable real Hilbert space, started at `0`, with
`‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost surely, and `p > 1`,
`‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}`, `p* = max (p, p / (p − 1))`. The case `X_0 = Y_0 = 0` of
`theorem3_5`; the separability of `H` is not used. -/
theorem inequality {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ) :
    eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (Y n) (ENNReal.ofReal p) μ :=
  theorem3_5 hp hY hX (Filter.Eventually.of_forall fun ω => by rw [hX0, hY0]) hsub n

section SquareFunction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- **Osękowski (2012), Theorem 8.6**, the inequalities (8.28), for a martingale `X` with values in
a real Hilbert space, started at `0`, and `1 < p < ∞`:
`(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`,
`𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`. (The book's martingale may start anywhere; its square
function then has the term `‖X_0‖²`.)

From `BanachProbability.Burkholder.squareFunction_of_martingale`, by the book's argument (p. 414,
with p. 16): `Z_m = Σ_{k < n} 1_{k < m} (X_{k+1} − X_k) e_k` and `A_m = X_{n ∧ m} e_n` in `H^{n+1}`
(`ℓ²` norm) are each differentially subordinate to the other, `‖Z_n‖ = 𝒮_n X`, `‖A_n‖ = ‖X_n‖`. -/
theorem theorem8_6 {X : ℕ → Ω → H} {p : ℝ} (hp : 1 < p) (hX : Martingale X ℱ μ)
    (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) :
    eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2))
            (ENNReal.ofReal p) μ :=
  BanachProbability.Burkholder.squareFunction_of_martingale hp hX hX0 n

/-- **Burkholder's square function inequality** (Osękowski 2012, Theorem 8.6; Cassese, Theorem 2.3
(2)): `theorem8_6` for a martingale `X` with values in a separable real Hilbert space, started at
`0`; the separability is not used. -/
theorem squareFunction {X : ℕ → Ω → H} [TopologicalSpace.SeparableSpace H] {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) :
    eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2))
            (ENNReal.ofReal p) μ :=
  theorem8_6 hp hX hX0 n

end SquareFunction

end External.Osekowski
