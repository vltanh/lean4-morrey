module

public import BanachProbability.Martingale.Burkholder.Inequality

/-!
# Burkholder's inequality and square function inequality for Hilbert-space-valued martingales

D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*,
Ann. Probab. 12 (1984); A. Osękowski, *Sharp martingale and semimartingale inequalities* (2012),
Theorems 3.5 and 8.6. Cassese (arXiv:2608.03488v3) quotes both as Theorem 2.3 (`cs-thm2.3`).

## Main results

* `inequality` (Theorem 2.3 (1)): for martingales `X`, `Y` with values in a separable real Hilbert
  space `H`, started at `0`, with `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost surely, and `p > 1`,
  `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}` with `p* = max (p, p / (p − 1))`;
  `inequality_of_subordinate` is the same statement without the separability of `H`.
* `squareFunction` (Theorem 2.3 (2)): `‖𝒮_n X‖_{L^p} ≤ (p* − 1) ‖X_n‖_{L^p}` and
  `‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`, `𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`;
  `squareFunction_of_martingale` without separability.

## The proofs

The four statements are those of the package `BanachProbability` (`lean4-banach-probability`,
required by path while it is developed), `BanachProbability.Burkholder.inequality`,
`inequality_of_subordinate`, `squareFunction`, `squareFunction_of_martingale`, which proves them by
Burkholder's method, the sources' standard argument (Osękowski's book was not consulted):
Burkholder's function `U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}`
majorizes `V (x, y) = |x|^p − (p* − 1)^p |y|^p`, `t ↦ U (x + t h, y + t k)` is
concave for `|h| ≤ |k|` (with the kinks, where `x + t h = 0` or `y + t k = 0`, handled by gluing the
concave pieces through their one-sided derivatives), and integrating the concavity along the
martingale gives `E V (X_n, Y_n) ≤ E U (X_n, Y_n) ≤ U (0, 0) = 0`. The square function inequality
is the standard derivation from (1), with the `ℓ²(H)`-valued martingale `Σ_k dX_k e_k` truncated
to `H^{n+1}` (`n` is fixed). The separability of `H` is not used.
-/

@[expose] public section

open MeasureTheory

namespace External.Burkholder

/-- Burkholder's inequality without the separability of `H` (which the proof does not use).
From `BanachProbability.Burkholder.inequality_of_subordinate`. -/
theorem inequality_of_subordinate {Ω H : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ) :
    eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (Y n) (ENNReal.ofReal p) μ :=
  BanachProbability.Burkholder.inequality_of_subordinate hp hX hY hX0 hY0 hsub n

/-- **Burkholder's inequality** (Burkholder 1984; Osękowski, *Sharp martingale and semimartingale
inequalities* (2012), Theorem 3.5; Cassese, Theorem 2.3 (1)): for martingales `X`, `Y` with values
in a separable real Hilbert space, started at `0`, with `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost
surely, and `p > 1`, `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}`, `p* = max (p, p / (p − 1))`.

From `BanachProbability.Burkholder.inequality`, proved by Burkholder's method (see the module
docstring). -/
theorem inequality {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] {X Y : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (hY0 : ∀ ω, Y 0 ω = 0)
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) (n : ℕ) :
    eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (Y n) (ENNReal.ofReal p) μ :=
  BanachProbability.Burkholder.inequality hp hX hY hX0 hY0 hsub n

section SquareFunction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Burkholder's square function inequality without the separability of `H`. From
`BanachProbability.Burkholder.squareFunction_of_martingale`. -/
theorem squareFunction_of_martingale {X : ℕ → Ω → H} {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) :
    eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2))
            (ENNReal.ofReal p) μ :=
  BanachProbability.Burkholder.squareFunction_of_martingale hp hX hX0 n

/-- **Burkholder's square function inequality** (Burkholder; Osękowski, *Sharp martingale and
semimartingale inequalities* (2012), Theorem 8.6; Cassese, Theorem 2.3 (2)): for a martingale `X`
with values in a separable real Hilbert space, started at `0`, and `p > 1`,
`(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`,
`𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`.

From `BanachProbability.Burkholder.squareFunction`, the standard derivation from Burkholder's
inequality: in `H^{n+1}` with the `ℓ²` norm, `Z_m = Σ_{k < n} dX_{k+1} 1_{k < m} e_k` and
`A_m = X_{n ∧ m} e_n` are each differentially subordinate to the other, `‖Z_n‖ = 𝒮_n X`,
`‖A_n‖ = ‖X_n‖`. -/
theorem squareFunction {X : ℕ → Ω → H} [TopologicalSpace.SeparableSpace H] {p : ℝ} (hp : 1 < p)
    (hX : Martingale X ℱ μ) (hX0 : ∀ ω, X 0 ω = 0) (n : ℕ) :
    eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) * eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (max p (p / (p - 1)) - 1) *
          eLpNorm (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2))
            (ENNReal.ofReal p) μ :=
  BanachProbability.Burkholder.squareFunction hp hX hX0 n

end SquareFunction

end External.Burkholder
