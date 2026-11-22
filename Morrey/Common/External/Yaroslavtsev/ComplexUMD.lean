module

public import BanachProbability.UMD.Complex
public import BanachProbability.ZigZag.Basic

/-!
# Complex UMD constants (Yaroslavtsev 2018, Lemma 3.2 and Proposition 3.7)

I. Yaroslavtsev, *Even Fourier multipliers and martingale transforms in infinite dimensions*,
Indag. Math. 29 (2018) (arXiv:1710.04958), which Cassese (arXiv:2608.03488v3) cites
for Proposition 2.7 (5) (Lemma 3.2, TeX lines 842–856) and, with HNVW I, Theorem 4.5.6, for the
complex half of Proposition 2.7 (6) (Proposition 3.7, TeX lines 857–869):

* `External.Yaroslavtsev.lemma3_2`: for a complex Banach space `X` and `p ∈ (1, ∞)`,
  `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`, where `UMD_{ℂ,p}` is the best constant for
  transforms by predictable unimodular complex multipliers (`BanachProbability.complexUMDConst`)
  and `UMD_p` that of `X` as a real space;
* `External.Yaroslavtsev.proposition3_7`: if `U` is zig-zag concave in the complex sense
  (`z ↦ U (x + z, y + ε z)` concave for `|ε| ≤ 1`, `ε ∈ ℂ`; `U (0, 0) = 0`;
  `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`), then `UMD_{ℂ,p} (X) ≤ β`.

Proofs: in the package `BanachProbability` (`lean4-banach-probability`, required by path while it
is developed). Lemma 3.2 gives no proof (it refers to HNVW I, Proposition 4.2.10, which was not
accessible); `BanachProbability.umdConst_le_complexUMDConst_le` proves it by the standard
averaging argument, for general filtrations: real signs are unimodular, and for `|λ| = 1`,
`(1/2π) ∫ sgn cos (arg λ − φ) e^{iφ} dφ = (2/π) λ`, with the integral replaced by Riemann sums over
equally spaced angles, so that no joint measurability is needed.
`BanachProbability.complexUMDConst_le_of_isComplexZigZagConcave` proves Proposition 3.7 by
Burkholder's argument (midpoint concavity integrated along complex Paley–Walsh transforms on the
sign cube), then the complex form of Maurey's theorem. Only the statements of Yaroslavtsev's
Lemma 3.2 and Proposition 3.7 were read.
-/

@[expose] public section

open scoped ENNReal

namespace External.Yaroslavtsev

open BanachProbability

/-- **Yaroslavtsev (2018), Lemma 3.2**: for a complex Banach space `X` and `p ∈ (1, ∞)`,
`UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`. -/
theorem lemma3_2 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) :
    umdConst X p ≤ complexUMDConst X p ∧
      complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p :=
  umdConst_le_complexUMDConst_le hp

/-- **Yaroslavtsev (2018), Proposition 3.7**, the direction used: for a complex Banach space `X`,
`p ∈ (1, ∞)` and `β > 0`, a function `U` that is zig-zag concave in the complex sense bounds the
complex UMD constant, `UMD_{ℂ,p} (X) ≤ β`. -/
theorem proposition3_7 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {p β : ℝ} (hp : 1 < p) (hβ : 0 < β) {U : X → X → ℝ} (hU : IsComplexZigZagConcave p β U) :
    complexUMDConst X p ≤ ENNReal.ofReal β :=
  complexUMDConst_le_of_isComplexZigZagConcave hp hβ hU

end External.Yaroslavtsev
