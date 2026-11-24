module

public import BanachProbability.UMD.Maurey.Basic

/-!
# Dyadic UMD equals UMD (HNVW I, Theorem 4.2.5)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I* (2016; read),
Theorem 4.2.5 (p. 282), which Cassese (arXiv:2608.03488v3) cites as Proposition 2.7 (4) (TeX lines
837–841): restricting the `UMD_p` inequality to dyadic (Paley–Walsh) martingales gives the same
optimal constant, `UMD_p^{dyad} (X) = UMD_p (X)`.

* `External.HNVW.theorem4_2_5`: `dyadicUMDConst X p = umdConst X p` for a real Banach space `X`
  and `p ∈ (1, ∞)`.

The constants are those of Cassese's Definition 2.5: predictable signs, all probability spaces,
martingales started at `0`. The book's `β_{p,X}` (p. 282, after Definition 4.2.1) is for
deterministic signs and σ-finite measure spaces, over the scalars of `X`; by its Theorem 4.2.25 (p.
300) predictable signs have the same constant.

Proof: `BanachProbability.dyadicUMDConst_eq_umdConst` in the package `BanachProbability`
(`lean4-banach-probability`), by the book's alternative proof ("The result provides an alternative
proof of Theorem 4.2.5", p. 334; due to Burkholder (1986), p. 355): the dyadic UMD property gives a
zig-zag concave function with the dyadic constant (Theorem 4.5.6, (2)⇒(3)), and that function bounds
the UMD constant ((3)⇒(1)). The proof printed for Theorem 4.2.5 (pp. 284–285) approximates
martingales by Paley–Walsh ones (Theorem 3.6.1, after Maurey) and is not the one followed. The
alternative proof, run with deterministic signs in the hypothesis and predictable ones in the
conclusion, gives the statement for predictable signs directly.
-/

@[expose] public section

namespace External.HNVW

open BanachProbability

/-- **HNVW I, Theorem 4.2.5**: for a real Banach space `X` and `p ∈ (1, ∞)`, the dyadic `UMD_p`
constant equals the `UMD_p` constant. -/
theorem theorem4_2_5 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {p : ℝ} (hp : 1 < p) : dyadicUMDConst X p = umdConst X p :=
  dyadicUMDConst_eq_umdConst hp

end External.HNVW
