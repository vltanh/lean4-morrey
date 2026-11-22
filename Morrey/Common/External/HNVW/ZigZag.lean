module

public import BanachProbability.ZigZag.Basic

/-!
# Burkholder's characterisation of UMD by zig-zag concave functions (HNVW I, Theorem 4.5.6)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I* (2016),
Theorem 4.5.6, which Cassese (arXiv:2608.03488v3) cites, with Yaroslavtsev (2018),
Proposition 3.7, as Proposition 2.7 (6) (TeX lines 857–869): a real Banach space `X` is `UMD_p` if
and only if there is a zig-zag concave `U : X × X → ℝ` (`z ↦ U (x + z, y + ε z)` concave for
`|ε| ≤ 1`, `U (0, 0) = 0`, `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p` for some `β > 0`), and then
`β ≥ UMD_p (X)`. The book was not accessible; the statement is the one Cassese quotes. The complex
half (`β ≥ UMD_{ℂ,p} (X)`) is Yaroslavtsev's Proposition 3.7 (`External.Yaroslavtsev`).

* `External.HNVW.theorem4_5_6`: both assertions, for `p ∈ (1, ∞)`
  (`BanachProbability.IsZigZagConcave`).

Proof: in the package `BanachProbability` (`lean4-banach-probability`, required by path while it
is developed), `BanachProbability.umdConst_lt_top_iff_exists_isZigZagConcave` and
`umdConst_le_of_isZigZagConcave`. The source being inaccessible, the argument is the standard
one, Burkholder's (D. L. Burkholder, *A geometrical characterization of Banach spaces in which
martingale difference sequences are unconditional*, Ann. Probab. 9 (1981); *Boundary value
problems and sharp inequalities for martingale transforms*, Ann. Probab. 12 (1984); both open
access on Project Euclid but not obtained, the site refusing automated download): for the bound,
midpoint concavity along the zig-zag lines integrated along a Paley–Walsh martingale on the sign
cube, then
Maurey's theorem; for the converse, the Bellman function
`U (x, y) = sup E [‖y + g‖^p − β^p ‖x + f‖^p]` over Paley–Walsh pairs with predictable multipliers
in `[−1, 1]`, `β > UMD_p (X)`, which is zig-zag concave by splicing and the Bernstein–Doetsch
theorem.
-/

@[expose] public section

open scoped ENNReal

namespace External.HNVW

open BanachProbability

/-- **HNVW I, Theorem 4.5.6** (Burkholder): for a real Banach space `X` and `p ∈ (1, ∞)`, `X` is
`UMD_p` if and only if there is a zig-zag concave function `U` for some `β > 0`; and every such
`β` bounds `UMD_p (X)`. -/
theorem theorem4_5_6 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) :
    (umdConst X p < ⊤ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsZigZagConcave p β U) ∧
      ∀ (β : ℝ) (U : X → X → ℝ), 0 < β → IsZigZagConcave p β U →
        umdConst X p ≤ ENNReal.ofReal β :=
  ⟨umdConst_lt_top_iff_exists_isZigZagConcave hp,
    fun _β _U hβ hU => umdConst_le_of_isZigZagConcave hp hβ hU⟩

end External.HNVW
