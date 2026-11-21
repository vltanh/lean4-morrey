module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Osękowski: differential subordination characterizes Hilbert spaces

A. Osękowski, *Sharp martingale and semimartingale inequalities*, Birkhäuser 2012, Theorem 3.24.
Cassese quotes it as Proposition 2.6, for context only: no proof of the paper uses it. It is a
proposition with no proof, and a hypothesis of no statement.

(Cassese's Theorem 2.3, from Osękowski's Theorems 3.5 and 8.6, is used by the main theorems, so
its two parts are stated in the shared block of `Cassese/Defs.lean`:
`Cassese.BurkholderInequality` and `Cassese.BurkholderSquareFunction`.)
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace External.Osekowski

/-- **Proposition 2.6** (`cs-prop2.6`) of Cassese, citing Osękowski, Theorem 3.24 (TeX lines
768–787): let `X` be a Banach space and `p ∈ (1, ∞)`; if there is a constant `β ≥ 0` with
`‖U_n‖_{L^p} ≤ β ‖V_n‖_{L^p}` for every pair of `X`-valued martingales (on one filtration,
started at `0`) with `‖dU_n‖ ≤ ‖dV_n‖`, then `X` is isomorphic to a Hilbert space `H` with
Banach–Mazur distance `d_BM (X, H) ≲_p β`: there is an isomorphism `T : X ≃ H` with
`‖T‖ ‖T⁻¹‖ ≤ C_p β`. Context only; not a hypothesis of any statement. (The paper adds that the
dependence on `β` cannot be improved in general; that sentence is not formalized.)

The constant is required to be nonnegative (the paper's `β_p` is a bound for norms). Without
that, the statement was false: for `X = 0` every `β` satisfies the hypothesis, and `β < 0` makes
the conclusion impossible. With `β ≥ 0` that refutation is gone: for `X = 0` the conclusion holds
with `H = 0` (both operator norms are `0`), and for `X ≠ 0` the hypothesis forces `β ≥ 1` (take
`U = V` a nonzero martingale `U_n = ε x`, `n ≥ 1`, on two points), so `C_p β ≥ C_p > 0`.
The hypothesis is asked only of martingales started at `0`: with the convention `dU_0 = U_0`,
such pairs are differentially subordinate, so this hypothesis is weaker than the paper's and the
proposition at least as strong. Osękowski's own formulation was not consulted. -/
def HilbertCharacterization : Prop :=
  ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (β : ℝ), 0 ≤ β →
      (∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ mΩ) (U V : ℕ → Ω → X), Martingale U ℱ μ → Martingale V ℱ μ →
        (∀ ω, U 0 ω = 0) → (∀ ω, V 0 ω = 0) →
        (∀ n, ∀ᵐ ω ∂μ, ‖U (n + 1) ω - U n ω‖ ≤ ‖V (n + 1) ω - V n ω‖) →
        ∀ n, eLpNorm (U n) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal β * eLpNorm (V n) (ENNReal.ofReal p) μ) →
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (T : X ≃L[ℝ] H),
        ‖(T : X →L[ℝ] H)‖ * ‖(T.symm : H →L[ℝ] X)‖ ≤ C * β

end External.Osekowski
