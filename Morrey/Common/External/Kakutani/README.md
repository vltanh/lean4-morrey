# Kakutani's fixed-point theorem

**Source.** S. Kakutani, *A generalization of Brouwer's fixed point theorem*, Duke Math. J. 8
(1941), 457–459. The paper cites it through G. V. Smirnov, *Introduction to the Theory of
Differential Inclusions*, Graduate Studies in Mathematics 41, AMS, 2002.

**Statement used by the paper** (Theorem 6.2). Let `A ⊆ ℝ^d` be nonempty, compact and convex, and
let `F : A ⇉ A` be upper semicontinuous with nonempty, convex, compact values. Then `x ∈ F(x)`
for some `x ∈ A`.

**Lean.** [`External.Kakutani.exists_fixedPoint`](Theorem.lean), in any finite-dimensional real
normed space, with upper semicontinuity in the topological sense of set-valued analysis
([`External.Kakutani.UpperSemicontinuousOn`](Theorem.lean)).

**Proof.** From `Kakutani.exists_fixedPoint` of
[lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point) (commit `5f650f0`), which
assumes a closed graph `{(x, y) | x ∈ A, y ∈ F x}` instead: an upper semicontinuous map with
closed values on a closed set has a closed graph.

**How the paper uses it.** Section 6 applies it to the map `𝐓` on `A = Θ_l`, a polytope in
`ℝ^{3·2^{2l+2}}`. Subsection 6.1 proves that the graph of `𝐓` is closed and that its values are
compact, and calls this upper semicontinuity. The library proves both and derives upper
semicontinuity from them, because `Θ_l` is compact.
