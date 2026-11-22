module

public import BanachProbability.UMD.Extrapolation

/-!
# Extrapolation of the UMD property (HNVW I, Theorem 4.2.7)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I* (2016; read),
Theorem 4.2.7 (p. 283), which Cassese (arXiv:2608.03488v3) cites as Proposition 2.7 (1) (TeX lines
829–831): a Banach space that is `UMD_{p₀}` for some `p₀ ∈ (1, ∞)` is `UMD_p` for every
`p ∈ (1, ∞)`, and `UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 100 p* UMD₂ (X)`, `p* = max (p, p / (p − 1))`.

The book's theorem is `UMD_p (X) ≤ 100 (p/q + p'/q') UMD_q (X)` for all `p, q ∈ (1, ∞)`, and "in
particular" `UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 50 (p + p') UMD₂ (X)`; the paper's `100 p*` is a weaker
form, as `50 (p + p') ≤ 100 p*`.

* `External.HNVW.theorem4_2_7_general`: the book's inequality;
* `External.HNVW.theorem4_2_7`: the form Cassese quotes.

Both are for a real Banach space `X` (the book: real or complex scalars), with the `UMD_p` constant
of predictable signs, as in Cassese's Definition 2.5 (`BanachProbability.umdConst`; the book's is
for deterministic signs, with the same value by its Theorem 4.2.25).

Proof: in the package `BanachProbability` (`lean4-banach-probability`),
`BanachProbability.umdConst_le_mul_umdConst` and its special cases `umdConst_lt_top_of_lt_top`,
`umdConst_two_le_mul`, `umdConst_le_mul_umdConst_two`, by the book's argument: for the transforms of
Paley–Walsh martingales by fixed signs, the good-λ inequality (Lemmas 3.5.13, 3.5.14), its
integration (Lemma 3.5.15, (3.59)), Doob's inequality and the adjoint transform (Lemma 3.5.3) give
(3.49) of Theorem 3.5.4 (pp. 229–234), then the supremum over the transforms (Lemma 4.2.8) and the
equality of the dyadic and the general constants (Theorem 4.2.5, `External.HNVW.theorem4_2_5`). The
proof of (3.49) gives `80 (p/q + p'/q')`, stated with `100`, as in the book.
-/

@[expose] public section

open scoped ENNReal

namespace External.HNVW

open BanachProbability

/-- **HNVW I, Theorem 4.2.7** (extrapolation), the book's inequality: for a real Banach space `X`
and `p, q ∈ (1, ∞)`, `UMD_p (X) ≤ 100 (p/q + p'/q') UMD_q (X)`, `p' = p / (p − 1)`,
`q' = q / (q − 1)`. -/
theorem theorem4_2_7_general {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    umdConst X p ≤
      ENNReal.ofReal (100 * (p / q + p / (p - 1) / (q / (q - 1)))) * umdConst X q :=
  umdConst_le_mul_umdConst hp hq

/-- **HNVW I, Theorem 4.2.7** (extrapolation), as Cassese quotes it: if the real Banach space `X` is
`UMD_{p₀}` for some `p₀ ∈ (1, ∞)`, it is `UMD_p` for every `p ∈ (1, ∞)`; and for every `p ∈ (1, ∞)`,
`UMD₂ (X) ≤ 200 UMD_p (X)` and `UMD_p (X) ≤ 100 p* UMD₂ (X)`. -/
theorem theorem4_2_7 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
    ((∃ p₀ : ℝ, 1 < p₀ ∧ umdConst X p₀ < ⊤) → ∀ p : ℝ, 1 < p → umdConst X p < ⊤) ∧
      ∀ p : ℝ, 1 < p → umdConst X 2 ≤ 200 * umdConst X p ∧
        umdConst X p ≤ ENNReal.ofReal (100 * pStar p) * umdConst X 2 :=
  ⟨fun ⟨_p₀, hp₀, h⟩ _p hp => umdConst_lt_top_of_lt_top hp₀ h hp,
    fun _p hp => ⟨umdConst_two_le_mul hp, umdConst_le_mul_umdConst_two hp⟩⟩

end External.HNVW
