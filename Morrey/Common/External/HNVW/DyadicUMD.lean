module

public import BanachProbability.UMD.Maurey.Basic

/-!
# Dyadic UMD equals UMD (HNVW I, Theorem 4.2.5; Maurey)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I* (2016),
Theorem 4.2.5, which Cassese (arXiv:2608.03488v3) cites as Proposition 2.7 (4) (TeX lines
837–841): restricting the `UMD_p` inequality to dyadic (Paley–Walsh) martingales gives the same
optimal constant, `UMD_p^{dyad} (X) = UMD_p (X)`. The book was not accessible; the statement is the
one Cassese quotes.

* `External.HNVW.theorem4_2_5`: `dyadicUMDConst X p = umdConst X p` for a real Banach space `X`
  and `p ∈ (1, ∞)`.

Proof: `BanachProbability.dyadicUMDConst_eq_umdConst` in the package `BanachProbability`
(`lean4-banach-probability`, required by path while it is developed). The source being
inaccessible, the argument is Maurey's (B. Maurey, *Système de Haar*, Séminaire Maurey–Schwartz
1974–1975), as in G. Pisier, *Martingales in Banach spaces* (2016) (read in its open draft, the IHP
course notes of 2011, Lemmas 8.29–8.31 and Theorem 8.32): approximate a martingale and its
predictable signs by step processes on finite σ-algebras, perturb the transition probabilities to
dyadic rationals, and realise the resulting finite tree as a blocked Paley–Walsh martingale on a
sign cube.
-/

@[expose] public section

namespace External.HNVW

open BanachProbability

/-- **HNVW I, Theorem 4.2.5** (Maurey): for a real Banach space `X` and `p ∈ (1, ∞)`, the dyadic
`UMD_p` constant equals the `UMD_p` constant. -/
theorem theorem4_2_5 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) : dyadicUMDConst X p = umdConst X p :=
  dyadicUMDConst_eq_umdConst hp

end External.HNVW
