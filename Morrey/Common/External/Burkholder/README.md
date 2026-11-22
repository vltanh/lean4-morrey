# Burkholder: his scalar function, (13) and (14)

**Source.** D. L. Burkholder, *Sharp inequalities for martingales and stochastic integrals*, Colloque
Paul Lévy sur les processus stochastiques, Astérisque 157–158 (1988), 75–94 (read: Numdam,
https://www.numdam.org/item/AST_1988__157-158__75_0/), the proof of Theorem 1.1: (1.6), (1.10), (1.11),
(1.12)–(1.14), and Remark 1.2, (1.17).

**Statements used by Cassese.** (13) and (14) (proof of Proposition 4.2, TeX lines 1235–1245), citing
"[Burkholder1988Sharp, Proof of Theorem 1.1], or [VasVol] for an alternative proof" (V. Vasyunin,
A. Volberg 2010, not used here): Burkholder's function `u (a, b) = α (|b| − 5 |a|) (|a| + |b|)^5`,
`α = 6 (5/6)^5`, on `ℂ × ℂ`, satisfies `u (a, b) ≥ |b|^6 − 5^6 |a|^6`, and
`t ↦ u (a + t h, b + t ε h)` is concave for `|ε| ≤ 1`. Remark 4.5 (TeX lines 1367–1375) says that the
argument extends to `1 < p < ∞`, `p + 2 < q < ∞`; the extension needs the same two properties of `u_q`.
(TeX line 719, "see also" for martingale transforms, is context.)

Cassese's Theorem 2.3 (Burkholder's inequality and square function inequality) is cited from
Osękowski's book and is in [`../Osekowski`](../Osekowski).

**Lean.** [`ScalarFunction.lean`](ScalarFunction.lean): the propositions `ScalarFunction` ((13), (14)
for `u`) and `ScalarFunctionQ q` (the same for `u_q`), proved by `scalarFunction_holds` and, for
every real `q ≥ 2`, `scalarFunctionQ_holds`, from the package's Burkholder function in
Burkholder's notation, `BanachProbability.Burkholder.burkholderFun` (on the real inner product
space `ℂ`, `u_q = burkholderFun q` for `q ≥ 2`, `uq_eq_burkholderFun`): (13) is
`burkholderFun_ge`, (14) is `burkholderFun_concaveOn_line`; `u = u_6` (`uq_six`).

**Constants.** `5^6` and `(q − 1)^q`, as Burkholder's (`p* − 1 = q − 1` for `q ≥ 2`).

**Proofs.** In the package `BanachProbability`
([lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability),
`Martingale/Burkholder/Function.lean`), step by step as Burkholder 1988. (13) is (1.10), `v ≤ u`:
(1.11), `(p − 1)^{p−1} / p^{p−2}` is `≤ 1` on `(1, 2]` and `≥ 1` on `[2, ∞)`, by the convexity of its
logarithm on `[1, 2]`, its concavity on `[2, ∞)` and its growth; then, by homogeneity, the concave and
convex pieces of Burkholder's function `F` on `[0, 1]`. (14) is Remark 1.2, (1.17), which Burkholder
states without proof (a gap of the source); it is completed from his own steps: the concavity
of `G (t) = u (x + t h, y + t k)` in the proof of (1.12), by the sign of the second derivative (1.14),
on the lines along which neither coordinate vanishes, and, for the other lines, the shift by a vector
orthogonal to `H` in `H ⊕ ℝ` of the proof of (1.8), with the shift tending to `0`. No other departure.

**Who uses them.** (13), (14) for `u` are used by Propositions 4.2 and 4.3. `u_q` is used by
`Cassese.theorem1_2_elementary`, a second proof of Theorem 1.2 by the route of Remark 4.5 (with
`q = p + 3`);
`Cassese.theorem1_2` is the paper's proof, through the UMD constants of Proposition 2.7. None of them
takes (13) or (14) as a hypothesis.
