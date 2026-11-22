# Burkholder: sharp martingale inequalities and his scalar functions

**Sources.** D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*,
Astérisque 157–158 (1988), 75–94 (read: Numdam,
https://www.numdam.org/item/AST_1988__157-158__75_0/), Theorem 1.1 with (1.6), (1.10), (1.11),
Remark 1.2, and Theorem 3.1. Cassese also cites D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*, Ann.
Probab. 12 (1984), open access on Project Euclid but not obtained (the site refused automated
download), and A. Osękowski, *Sharp martingale and semimartingale inequalities*, Birkhäuser 2012,
Theorems 3.5 and 8.6, not obtained. Burkholder 1988 proves the two inequalities Cassese quotes,
for Hilbert-space-valued martingales, and its arguments are the ones followed.

**Statements used by Cassese.**

- Theorem 2.3 (1) (TeX lines 721–739), Burkholder's inequality: for martingales `X`, `Y` with values
  in a separable Hilbert space, started at `0`, with `‖dX_n‖ ≤ ‖dY_n‖`,
  `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}`, `p ∈ (1, ∞)`, `p* = max (p, p / (p − 1))`.
- Theorem 2.3 (2), the square function inequality:
  `(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`.
- (13) and (14) (proof of Proposition 4.2, TeX lines 1235–1245): Burkholder's function
  `u (a, b) = α (|b| − 5 |a|) (|a| + |b|)^5`, `α = 6 (5/6)^5`, on `ℂ × ℂ`, satisfies
  `u (a, b) ≥ |b|^6 − 5^6 |a|^6`, and `t ↦ u (a + t h, b + t ε h)` is concave for `|ε| ≤ 1`.
  Remark 4.5 (TeX lines 1367–1375) asks for the same properties of `u_q` for other exponents `q`.

**Lean.**

- [`Inequality.lean`](Inequality.lean): `External.Burkholder.inequality` and
  `External.Burkholder.squareFunction` (without separability: `inequality_of_subordinate`,
  `squareFunction_of_martingale`), for real Hilbert spaces and Mathlib's `MeasureTheory.Martingale`,
  each a one-line proof from `BanachProbability.Burkholder.inequality`, `inequality_of_subordinate`,
  `squareFunction`, `squareFunction_of_martingale` of the package `BanachProbability`
  ([lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability), commit
  `250cd49`).
- [`ScalarFunction.lean`](ScalarFunction.lean): the propositions `ScalarFunction` ((13), (14) for
  `u`) and `ScalarFunctionQ q` (the same for `u_q`), proved by `scalarFunction_holds` and, for
  every real `q ≥ 2`, `scalarFunctionQ_holds`, from the package's Burkholder function in
  Burkholder's notation, `BanachProbability.Burkholder.burkholderFun` (on the real inner product
  space `ℂ`, `u_q = burkholderFun q` for `q ≥ 2`, `uq_eq_burkholderFun`): (13) is
  `burkholderFun_ge`, (14) is `burkholderFun_concaveOn_line`; `u = u_6` (`uq_six`).

**Proofs.** The package follows Burkholder 1988 step by step. Theorem 1.1 (proof, §1): (1.11),
`(p − 1)^{p−1} / p^{p−2}` is `≤ 1` on `(1, 2]` and `≥ 1` on `[2, ∞)`, by the convexity of its
logarithm on `[1, 2]`, its concavity on `[2, ∞)` and its growth; (1.10), `V ≤ U`, by homogeneity
and the concave and convex pieces of Burkholder's function `F` on `[0, 1]`; (1.12), on lines along
which neither coordinate vanishes, from the sign of the second derivative (1.14); (1.8),
`E U (X_{k+1}, Y_{k+1}) ≤ E U (X_k, Y_k)`, by shifting both martingales by a vector orthogonal to
`H` in `H ⊕ ℝ` (Burkholder's "enlarge `H` slightly"), integrating (1.12) (the martingale property
removes the linear terms, (1.15)) and letting the shift tend to `0` by dominated convergence; so
`E V (X_n, Y_n) ≤ E U (X_n, Y_n) ≤ U (0, 0) = 0`. Theorem 3.1 (proof, §3): Theorem 1.1 applied to
the `ℓ²_H`-valued martingales `(X_m, 0, …)` and `(dX_1, …, dX_m, 0, …)`, each differentially
subordinate to the other, in their subspace `H^{n+1}` (`n` is fixed). The separability of `H` is
not used. (13) is (1.10), and (14) is Remark 1.2, (1.17), both with the roles of the two arguments
exchanged (Burkholder's `u (x, y)` has `x` dominating, the package's `U (x, y)` has `x`
subordinate). Remark 1.2 is stated in the paper without proof (a gap of the source); it is completed
from the paper's own steps, (1.12)–(1.14) on the lines along which neither coordinate vanishes and,
for the other lines, the shift of the proof of (1.8) with the shift tending to `0`. The equality
cases and the sharpness of the constants are not formalized. The package's source contains no
`sorry`.

**Who uses them.** Cassese's Theorem 2.3 is stated in the paper's terms in
[`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean) (`burkholderInequality_holds`,
`burkholderSquareFunction_holds`). The inequality is used by Lemma 5.1 (1) and the proof of
Theorem 1.3 (b) (Section 5) and by Proposition 7.1 (Section 7, and so Theorem 7.1, Theorem 1.5 and
Corollary 1.6); the square function inequality, in `S_2^{d×d}`, by Proposition 6.5 (and so
Theorem 1.4 for general `p` and Corollary 6.1). (13), (14) for `u` are used by Propositions 4.2
and 4.3. `u_q` is used by `Cassese.theorem1_2_elementary`, a second proof of Theorem 1.2 by the
route of Remark 4.5; `Cassese.theorem1_2` is the paper's proof, through the UMD constants of
Proposition 2.7. None of these takes Theorem 2.3, (13) or (14) as a hypothesis.
