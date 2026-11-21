module

public import Morrey.Cassese.Defs
public import Morrey.Common.External.Burkholder.Inequality

/-!
# Cassese, arXiv:2608.03488v3: the cited results that are proved

The main theorems of the paper are stated with the results of other works that their proofs use
as named hypotheses (the propositions of the shared block of `Morrey/Cassese/Defs.lean`). This file
proves those of them that the project builds:

* Theorem 2.3 (`cs-thm2.3`), inequality (1): `burkholderInequality_holds : BurkholderInequality`,
  from `External.Burkholder.inequality` (Burkholder 1984; Osękowski 2012, Theorem 3.5);
* Theorem 2.3 (`cs-thm2.3`), inequality (2): `burkholderSquareFunction_holds :
  BurkholderSquareFunction`, from `External.Burkholder.squareFunction` (Osękowski 2012,
  Theorem 8.6).

Each follows from the result of `External/Burkholder` by unfolding `pStar p = max p (p / (p − 1))`.
-/

@[expose] public section

namespace Cassese

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
