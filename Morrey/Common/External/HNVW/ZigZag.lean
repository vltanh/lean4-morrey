module

public import BanachProbability.ZigZag.Basic

/-!
# Burkholder's characterisation of UMD by zig-zag concave functions (HNVW I, Theorem 4.5.6)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I* (2016; read),
Theorem 4.5.6 (p. 332), which Cassese (arXiv:2608.03488v3) cites, with Yaroslavtsev (2018),
Proposition 3.7, as Proposition 2.7 (6) (TeX lines 857–869): a real Banach space `X` is `UMD_p` if
and only if there is a zig-zag concave `U : X × X → ℝ` (`z ↦ U (x + z, y + ε z)` concave for
`|ε| ≤ 1`, `U (0, 0) = 0`, `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p` for some `β > 0`), and then
`β ≥ UMD_p (X)`. The complex half (`ε` in the unit disc, `β ≥ UMD_{ℂ,p} (X)`) is Yaroslavtsev's
Proposition 3.7 (`External.Yaroslavtsev`).

The book asks the concavity only for the signs `|ε| = 1` (Definition 4.5.3, p. 331) and not
`U (0, 0) = 0`, with `β ≥ 1`, and adds that the infimum of these `β` is `UMD_p (X)`. Cassese's form
asks more of the function, so his "only if" is stronger than the book's (the book's argument gives
it with multipliers in `[−1, 1]` instead of signs).

* `External.HNVW.theorem4_5_6`: both assertions of Proposition 2.7 (6), for a real Banach space and
  `p ∈ (1, ∞)` (`BanachProbability.IsZigZagConcave`);
* `External.HNVW.theorem4_5_6_isLeast`: the book's final clause, with the book's functions
  (`BanachProbability.IsSignZigZagConcave`) and with the attainment that its proof gives, for
  `X ≠ 0` (for `X = 0` every `β` is possible, and `UMD_p (X) = 0` with the constants used here).

Proof: in the package `BanachProbability` (`lean4-banach-probability`),
`BanachProbability.umdConst_lt_top_iff_exists_isZigZagConcave`, `umdConst_le_of_isZigZagConcave` and
`isLeast_umdConst_isSignZigZagConcave`, by the book's argument (pp. 330–337). (3)⇒(1): for a
martingale `f` on a finite probability space and its transform `g`, `E U (f_n, g_n)` decreases in
`n` (Lemma 4.5.5, by Jensen's inequality on the atoms, Lemma 4.5.4), then approximation by such
martingales (Lemma 3.6.17). (2)⇒(3): the function `U (x, y) = sup E [‖g‖^p − β^p ‖f‖^p]` over the
Paley–Walsh martingales `f` started at `x` and their transforms `g` started at `y` by constants in
`[−1, 1]`, `β` the dyadic constant; it is midpoint concave along the zig-zag lines by splicing,
finite by the choice `ε = −1`, hence concave (Lemma 4.5.2). In the book Lemma 4.5.2 is applied
before the finiteness is known; the order is changed. The signs of the UMD inequality are
predictable, which does not change the argument; the martingales start at `0`, so (4.32) and (4.33)
are not needed.
-/

@[expose] public section

open scoped ENNReal

namespace External.HNVW

open BanachProbability

/-- **HNVW I, Theorem 4.5.6** (Burkholder), as Cassese quotes it: for a real Banach space `X` and
`p ∈ (1, ∞)`, `X` is `UMD_p` if and only if there is a zig-zag concave function `U` for some
`β > 0`; and every such `β` bounds `UMD_p (X)`. -/
theorem theorem4_5_6 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) :
    (umdConst X p < ⊤ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsZigZagConcave p β U) ∧
      ∀ (β : ℝ) (U : X → X → ℝ), 0 < β → IsZigZagConcave p β U →
        umdConst X p ≤ ENNReal.ofReal β :=
  ⟨umdConst_lt_top_iff_exists_isZigZagConcave hp,
    fun _β _U hβ hU => umdConst_le_of_isZigZagConcave hp hβ hU⟩

/-- **HNVW I, Theorem 4.5.6** (Burkholder), the final clause: for a real Banach space `X ≠ 0` that
is `UMD_p`, the infimum of the `β ∈ [1, ∞)` for which there is a function `u`, zig-zag concave for
the signs `±1`, with `u (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`, is `UMD_p (X)`, and it is attained. -/
theorem theorem4_5_6_isLeast {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [Nontrivial X] {p : ℝ} (hp : 1 < p) (h : umdConst X p < ⊤) :
    IsLeast {β : ℝ | 1 ≤ β ∧ ∃ u : X → X → ℝ, IsSignZigZagConcave ℝ u ∧
      ∀ x y, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ u x y} (umdConst X p).toReal :=
  isLeast_umdConst_isSignZigZagConcave hp h

end External.HNVW
