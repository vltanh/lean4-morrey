module

public import Morrey.Cassese.Defs
public import Morrey.Common.External.Burkholder.Inequality

/-!
# Cassese, arXiv:2608.03488v3: the cited results that are proved

The paper's Theorem 2.3 is Burkholder's pair of inequalities for Hilbert-space-valued
martingales, which the paper cites. This file states them in the paper's terms, as the
propositions `BurkholderInequality` and `BurkholderSquareFunction`, and proves them:

* Theorem 2.3 (`cs-thm2.3`), inequality (1): `burkholderInequality_holds : BurkholderInequality`,
  from `External.Burkholder.inequality` (Burkholder 1984; Osękowski 2012, Theorem 3.5);
* Theorem 2.3 (`cs-thm2.3`), inequality (2): `burkholderSquareFunction_holds :
  BurkholderSquareFunction`, from `External.Burkholder.squareFunction` (Osękowski 2012,
  Theorem 8.6).

Each follows from the result of `External/Burkholder` by unfolding `pStar p = max p (p / (p − 1))`.

The library's proofs use them through these two theorems. Earlier they were hypotheses of the
statements that use them; they left the shared block of `Morrey/Cassese/Defs.lean`, which the
Challenge copies, when no statement took them any more.
-/

@[expose] public section

namespace Cassese

/-- **Theorem 2.3** (`cs-thm2.3`), inequality (1), citing Osękowski, *Sharp martingale and
semimartingale inequalities* (2012), Theorem 3.5 (Burkholder): if `X`, `Y` are martingales with
values in a separable Hilbert space, started at `0`, with `‖dX_n‖ ≤ ‖dY_n‖` almost surely for
`n > 0`, then `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}` for `p ∈ (1, ∞)`. -/
def BurkholderInequality : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (ℱ : MeasureTheory.Filtration ℕ mΩ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (X Y : ℕ → Ω → H) (p : ℝ), 1 < p →
    MeasureTheory.Martingale X ℱ μ → MeasureTheory.Martingale Y ℱ μ → (∀ ω, X 0 ω = 0) →
    (∀ ω, Y 0 ω = 0) → (∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) →
    ∀ n, MeasureTheory.eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (pStar p - 1) * MeasureTheory.eLpNorm (Y n) (ENNReal.ofReal p) μ

/-- **Theorem 2.3** (`cs-thm2.3`), inequality (2), citing Osękowski (2012), Theorem 8.6
(Burkholder's square function inequality): for a martingale `X` with values in a separable Hilbert
space, started at `0`, `p ∈ (1, ∞)` and `𝒮_n X = (Σ_{k ≤ n} ‖dX_k‖²)^{1/2}`,
`(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`. -/
def BurkholderSquareFunction : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (ℱ : MeasureTheory.Filtration ℕ mΩ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (X : ℕ → Ω → H) (p : ℝ), 1 < p →
    MeasureTheory.Martingale X ℱ μ → (∀ ω, X 0 ω = 0) →
    ∀ n, MeasureTheory.eLpNorm
          (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (pStar p - 1) * MeasureTheory.eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      MeasureTheory.eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (pStar p - 1) * MeasureTheory.eLpNorm
          (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ

/-- **Theorem 2.3 (1)** (`cs-thm2.3`, `eq:burk`): Burkholder's inequality
`‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}` for differentially subordinate martingales with values in a
separable Hilbert space, started at `0`. Proved here, from External/Burkholder
(`External.Burkholder.inequality`, by Burkholder's method as in Osękowski 2012, Theorem 3.5). -/
theorem burkholderInequality_holds : BurkholderInequality := by
  intro Ω mΩ μ _ ℱ H _ _ _ _ X Y p hp hX hY hX0 hY0 hsub n
  exact External.Burkholder.inequality hp hX hY hX0 hY0 hsub n

/-- **Theorem 2.3 (2)** (`cs-thm2.3`, `eq:sq`): Burkholder's square function inequality
`(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}` for martingales with values in a
separable Hilbert space, started at `0`. Proved here, from External/Burkholder
(`External.Burkholder.squareFunction`, from Burkholder's inequality applied to `X` and the
`ℓ²`-valued martingale `Σ_k dX_k e_k`, each differentially subordinate to the other). -/
theorem burkholderSquareFunction_holds : BurkholderSquareFunction := by
  intro Ω mΩ μ _ ℱ H _ _ _ _ X p hp hX hX0 n
  exact External.Burkholder.squareFunction hp hX hX0 n

end Cassese
