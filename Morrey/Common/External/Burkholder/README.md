# Burkholder: sharp martingale inequalities and his scalar functions

**Sources.** D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale
transforms*, Ann. Probab. 12 (1984); D. L. Burkholder, *Sharp inequalities for martingales and
stochastic integrals*, Astérisque 157–158 (1988), proof of Theorem 1.1;
A. Osękowski, *Sharp martingale and semimartingale inequalities*, Birkhäuser 2012, Theorems 3.5 and
8.6.

**Statements used by Cassese.**

- Theorem 2.3 (1), Burkholder's inequality: for martingales `X`, `Y` with values in a separable
  Hilbert space, started at `0`, with `‖dX_n‖ ≤ ‖dY_n‖`, `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}`,
  `p ∈ (1, ∞)`, `p* = max (p, p / (p − 1))`.
- Theorem 2.3 (2), the square function inequality:
  `(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`.
- (13) and (14) (proof of Proposition 4.2): Burkholder's function
  `u (a, b) = α (|b| − 5 |a|) (|a| + |b|)^5`, `α = 6 (5/6)^5`, on `ℂ × ℂ`, satisfies
  `u (a, b) ≥ |b|^6 − 5^6 |a|^6`, and `t ↦ u (a + t h, b + t ε h)` is concave for `|ε| ≤ 1`.
  Remark 4.5 asks for the same two properties of `u_q` for other exponents `q`.

**Lean.**

- [`Inequality.lean`](Inequality.lean): `External.Burkholder.inequality` and
  `External.Burkholder.squareFunction` (without separability: `inequality_of_subordinate`,
  `squareFunction_of_martingale`), for real Hilbert spaces and Mathlib's `MeasureTheory.Martingale`.
- [`ScalarFunction.lean`](ScalarFunction.lean): the propositions `ScalarFunction` ((13), (14) for
  `u`) and `ScalarFunctionQ q` (the same for `u_q`), proved by `scalarFunction_holds` and, for every
  real `q ≥ 2`, `scalarFunctionQ_holds`.

**Proofs.** Burkholder's method: the special function `U ≥ V` with the zig-zag concavity property,
integrated along the martingale, so that `E V (X_n, Y_n) ≤ E U (X_n, Y_n) ≤ U (0, 0) = 0`; the
square function inequality from (1), applied to `X` and the `ℓ²`-valued martingale `Σ_k dX_k e_k`,
each differentially subordinate to the other. (13) is a polynomial inequality in `|a|`, `|b|`;
(14) follows from the sign of the second derivative where the lines avoid `0`, and by
approximation elsewhere. Two points of mechanics (see the module docstrings): the kinks of `U` are
smoothed with `√(|z|² + ε²)` instead of gluing concave pieces through one-sided derivatives, and
the square function inequality uses `H^{n+1}` for `ℓ²(H)`. The book was not consulted.

**Who uses them.** Cassese's Theorem 2.3 is stated in the paper's terms in
[`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean) (`burkholderInequality_holds`,
`burkholderSquareFunction_holds`). The inequality is used by Lemma 5.1 (1) and the proof of
Theorem 1.3 (b) (Section 5) and by Proposition 7.1 (Section 7, and so Theorem 7.1, Theorem 1.5 and
Corollary 1.6); the square function inequality, in `S_2^{d×d}`, by Proposition 6.5 (and so
Theorem 1.4 for general `p` and Corollary 6.1). (13), (14) are used by Propositions 4.2 and 4.3; `u_q` by
`Cassese.theorem1_2_elementary`, the route of Remark 4.5 to Theorem 1.2.
