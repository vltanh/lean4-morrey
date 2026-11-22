module

public import BanachProbability.UMD.Extrapolation

/-!
# Extrapolation of the UMD property (HNVW I, Theorem 4.2.7)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I* (2016),
Theorem 4.2.7, which Cassese (arXiv:2608.03488v3) cites as Proposition 2.7 (1) (TeX lines
829–831): a Banach space that is `UMD_{p₀}` for some `p₀ ∈ (1, ∞)` is `UMD_p` for every
`p ∈ (1, ∞)`, and `UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 100 p* UMD₂ (X)`, `p* = max (p, p / (p − 1))`.
The book was not accessible; the statement is the one Cassese quotes.

* `External.HNVW.theorem4_2_7`: the statement, for a real Banach space `X`, with the `UMD_p`
  constant of predictable signs and general filtrations (`BanachProbability.umdConst`, which is at
  least the constant with deterministic signs, and equals Cassese's Definition 2.5).

Proof: in the package `BanachProbability` (`lean4-banach-probability`, required by path while it
is developed), `BanachProbability.umdConst_lt_top_of_lt_top`, `umdConst_two_le_mul`,
`umdConst_le_mul_umdConst_two`. The source being inaccessible, the argument is Burkholder's good-λ
method (D. L. Burkholder, *Distribution function inequalities for martingales*, Ann. Probab. 1
(1973); *A geometrical characterization of Banach spaces in which martingale difference sequences
are unconditional*, Ann. Probab. 9 (1981); both open access on Project Euclid but not obtained, the
site refusing automated download; for dyadic martingales, the second proof of the
extrapolation theorem in Pisier, *Martingales in Banach spaces* (2016)), run on Paley–Walsh
martingales, then lifted to general filtrations by Maurey's theorem (HNVW I, Theorem 4.2.5,
`External.HNVW.theorem4_2_5`). It gives the constants `76 p` (`p ≥ 2`), `48 p'` (`p < 2`) and
`180`, within the stated `100 p*` and `200`.
-/

@[expose] public section

open scoped ENNReal

namespace External.HNVW

open BanachProbability

/-- **HNVW I, Theorem 4.2.7** (extrapolation): if the real Banach space `X` is `UMD_{p₀}` for some
`p₀ ∈ (1, ∞)`, it is `UMD_p` for every `p ∈ (1, ∞)`; and for every `p ∈ (1, ∞)`,
`UMD₂ (X) ≤ 200 UMD_p (X)` and `UMD_p (X) ≤ 100 p* UMD₂ (X)`. -/
theorem theorem4_2_7 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
    ((∃ p₀ : ℝ, 1 < p₀ ∧ umdConst X p₀ < ⊤) → ∀ p : ℝ, 1 < p → umdConst X p < ⊤) ∧
      ∀ p : ℝ, 1 < p → umdConst X 2 ≤ 200 * umdConst X p ∧
        umdConst X p ≤ ENNReal.ofReal (100 * pStar p) * umdConst X 2 :=
  ⟨fun ⟨_p₀, hp₀, h⟩ _p hp => umdConst_lt_top_of_lt_top hp₀ h hp,
    fun _p hp => ⟨umdConst_two_le_mul hp, umdConst_le_mul_umdConst_two hp⟩⟩

end External.HNVW
