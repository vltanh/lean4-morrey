module

public import BanachProbability.Martingale.Burkholder.Inequality

/-!
# Burkholder's inequality and square function inequality for Hilbert-space-valued martingales

D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*,
Ann. Probab. 12 (1984); A. Osękowski, *Sharp martingale and semimartingale inequalities* (2012),
Theorems 3.5 and 8.6. Cassese (arXiv:2608.03488v3) quotes both as Theorem 2.3 (`cs-thm2.3`).
Neither was obtained (Burkholder 1984 is open access on Project Euclid, which refused automated
download). The same two inequalities, for Hilbert-space-valued martingales, are Theorems 1.1 and
3.1 of D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Astérisque
157–158 (1988) (read: Numdam, https://www.numdam.org/item/AST_1988__157-158__75_0/), whose proofs
are the ones followed.

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
the arguments of Burkholder 1988, proofs of Theorems 1.1 and 3.1: Burkholder's function
`U (x, y) = p (1 − 1/p*)^{p−1} (|x| − (p* − 1)|y|)(|x| + |y|)^{p−1}` ((1.6)) majorizes
`V (x, y) = |x|^p − (p* − 1)^p |y|^p` ((1.10), through (1.11) and Burkholder's function `F`);
(1.12) holds on lines along which neither coordinate vanishes (the sign of the second derivative,
(1.14)); `E U (X_{k+1}, Y_{k+1}) ≤ E U (X_k, Y_k)` ((1.8)) by shifting the martingales by a vector
orthogonal to `H` in `H ⊕ ℝ`, integrating (1.12) (the martingale property removes the linear
terms) and letting the shift tend to `0` by dominated convergence; so
`E V (X_n, Y_n) ≤ E U (X_n, Y_n) ≤ U (0, 0) = 0`. The square function inequality is Burkholder's
derivation from (1) through the `ℓ²_H`-valued martingales `(X_m, 0, …)` and `(dX_1, …, dX_m, 0, …)`,
each differentially subordinate to the other, in their subspace `H^{n+1}` (`n` is fixed). The
separability of `H` is not used.
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
inequalities* (2012), Theorem 3.5; Burkholder 1988, Theorem 1.1; Cassese, Theorem 2.3 (1)): for
martingales `X`, `Y` with values
in a separable real Hilbert space, started at `0`, with `‖X_{n+1} − X_n‖ ≤ ‖Y_{n+1} − Y_n‖` almost
surely, and `p > 1`, `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}`, `p* = max (p, p / (p − 1))`.

From `BanachProbability.Burkholder.inequality`, proved by the argument of Burkholder 1988, proof
of Theorem 1.1 (see the module docstring). -/
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

/-- **Burkholder's square function inequality** (Burkholder 1988, Theorem 3.1; Osękowski, *Sharp
martingale and semimartingale inequalities* (2012), Theorem 8.6; Cassese, Theorem 2.3 (2)): for a
martingale `X`
with values in a separable real Hilbert space, started at `0`, and `p > 1`,
`(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`,
`𝒮_n X = (Σ_{k < n} ‖X_{k+1} − X_k‖²)^{1/2}`.

From `BanachProbability.Burkholder.squareFunction`, the argument of Burkholder 1988, proof of
Theorem 3.1, in the subspace `H^{n+1}` of `ℓ²_H`, with the `ℓ²` norm:
`Z_m = Σ_{k < n} dX_{k+1} 1_{k < m} e_k` and
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
