module

public import BanachProbability.UMD.Lp

/-!
# `L^p` is a UMD space (Pisier 2016, Corollary 5.22)

G. Pisier, *Martingales in Banach spaces*, Cambridge University Press (2016), Corollary 5.22,
which Cassese (arXiv:2608.03488v3) cites as Proposition 2.7 (3) (TeX lines 835–836): for every
measure space `(Ω, Σ, μ)` and `p ∈ (1, ∞)`, `L^p (Ω, Σ, μ)` is a UMD space. The book was read in
its open draft (*Martingales in Banach spaces (in connection with type and cotype)*, IHP course
notes, 2011, Corollary 8.19, "by Fubini").

* `External.Pisier.corollary5_22`: `UMD_p (L^p (μ; ℂ)) < ∞`, for every measure `μ` and every
  `p ∈ (1, ∞)`, at the exponent `p` of the space, the complex `L^p` being a real Banach space;
* `External.Pisier.corollary5_22_vector`: the vector-valued form,
  `UMD_p (L^p (μ; B)) ≤ UMD_p (B)` for a real Banach space `B`.

Proof: `BanachProbability.umdConst_Lp_complex_lt_top` and `BanachProbability.umdConst_Lp_le` in the
package `BanachProbability` (`lean4-banach-probability`), the dyadic form of the source's Fubini
argument, which needs neither σ-finiteness nor joint measurability: a Paley–Walsh martingale with
values in `L^p (μ; B)` takes finitely many values, so for `μ`-almost every `s` its evaluation at `s`
is a `B`-valued Paley–Walsh martingale, and the transform commutes with evaluation; integrate the
dyadic bound in `s`, and pass to general filtrations by HNVW I, Theorem 4.2.5
(`External.HNVW.theorem4_2_5`). For `B = ℂ` (as the real Hilbert space `ℝ²`) the constant is
`p* − 1` (Osękowski 2012, Theorem 3.5, `External.Osekowski.theorem3_5`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace External.Pisier

open BanachProbability

/-- **Pisier (2016), Corollary 5.22**: for every measure space and `p ∈ (1, ∞)`, the complex
`L^p (μ)` is `UMD_p`. -/
theorem corollary5_22 {S : Type*} [MeasurableSpace S] (μ : Measure S) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p) (hpt : p ≠ ⊤) : umdConst (Lp ℂ p μ) p.toReal < ⊤ :=
  umdConst_Lp_complex_lt_top μ p hp hpt

/-- **Pisier (2016), Corollary 5.22**, vector-valued: `UMD_p (L^p (μ; B)) ≤ UMD_p (B)` for every
measure space, real Banach space `B` and `p ∈ (1, ∞)`. -/
theorem corollary5_22_vector {S : Type*} [MeasurableSpace S] (μ : Measure S) {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p) (hpt : p ≠ ⊤) : umdConst (Lp B p μ) p.toReal ≤ umdConst B p.toReal :=
  umdConst_Lp_le μ p hp hpt

end External.Pisier
