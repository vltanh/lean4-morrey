# Cox–Veraar: decoupling with the UMD constant

**Sources.** S. Cox, M. Veraar, *Some remarks on tangent martingale difference sequences in
`L¹`-spaces*, Electron. Commun. Probab. 12 (2007), 421–433 (arXiv:0801.0695; introduction read); T.
Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I*, Springer 2016 (HNVW
I; read), Proposition 4.2.3 (p. 282), a corollary of Proposition 4.1.16 (proof pp. 279–280).

Cox–Veraar recall, without proof, that in a UMD space `X` a martingale difference sequence and a
decoupled tangent sequence of it (one satisfying the (CI) condition) have comparable `L^p` norms,
`p ∈ (1, ∞)`, and that one may take the constant to be the UMD constant `β_{p,X}`. They credit this to
T. R. McConnell (*Decoupling and stochastic integration in UMD Banach spaces*, Probab. Math. Statist.
10 (1989)) and, independently, to an unpublished manuscript of P. Hitczenko, and a proof from the
definition of UMD to S. Montgomery-Smith. HNVW's Proposition 4.2.3 (the randomised UMD property): for an
`L^p`-martingale `f` and Rademacher signs `r_n` on a further probability space,
`(1/β⁻) ‖Σ df_n‖_p ≤ ‖Σ r_n df_n‖_p ≤ β⁺ ‖Σ df_n‖_p`, with `max (β⁻, β⁺) ≤ β_{p,X} ≤ β⁻ β⁺`, and the
same for Paley–Walsh martingales.

**Statement used by Cassese.** Proposition 2.8 (TeX lines 875–896, (6)), citing "see [Cox–Veraar] and
[HNVW I, Proposition 4.2.3]": for a UMD space `X`, `p ∈ (1, ∞)`, a martingale `dY_n = ε_n ξ_n` for the
filtration of i.i.d. Rademacher signs, with `ξ_n` predictable and in `L^p (X)`, and `Ỹ_n` defined
by `dỸ_n = ε̃_n ξ_n` with `ε̃` an independent copy of the signs,
`UMD_p (X)⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p (X) ‖Ỹ_n‖_{L^p}`. This is the Paley–Walsh case of
Cox–Veraar's statement (by their Example 1, `ε̃_n ξ_n` is tangent to `ε_n ξ_n` and satisfies the
(CI) condition), and HNVW's proposition for Paley–Walsh martingales, as for fixed `ε` the signs
`r_n ε_n` have the law of `ε̃_n`. Only this case is stated.

**Lean.** [`Decoupling.lean`](Decoupling.lean):

- `External.CoxVeraar.decoupling`: for a real Banach space `X`, `p ∈ (1, ∞)` and predictable
  `ξ : Fin N → {±1}^N → X`, `‖Σ_{k<n} ε̃_k ξ_k‖_{L^p} ≤ UMD_p (X) ‖Σ_{k<n} ε_k ξ_k‖_{L^p}` and
  `‖Σ_{k<n} ε_k ξ_k‖_{L^p} ≤ UMD_p (X) ‖Σ_{k<n} ε̃_k ξ_k‖_{L^p}`, on the canonical spaces
  `{±1}^N` and `{±1}^N × {±1}^N` (`BanachProbability.SignCube.paleyWalsh`,
  `BanachProbability.decoupledLpNorm`), with `UMD_p (X) = BanachProbability.umdConst X p`.

**Constants.** `UMD_p (X)` on both sides, as the paper and both sources state.

**Proof.** `BanachProbability.decoupling` in the package `BanachProbability`
([lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability)), by the argument of
HNVW I (Proposition 4.1.16, (1)⇒(2)): for fixed values of the signs `r_k`, `Σ r_k ε_k ξ_k` is the
transform of `Σ ε_k ξ_k` by constant signs, and `Σ ε_k ξ_k` that of `Σ r_k ε_k ξ_k` by the same signs, so
each is at most the dyadic constant times the other; raise to the power `p` and average over the signs;
then replace `r_k ε_k` by `ε̃_k` for each `ε`. The dyadic constant is at most `UMD_p (X)`. The package
also has the randomised UMD property itself (real scalars), with the converse (2)⇒(1)
(`IsUMDBound.isUpperRandomisedUMDBound`, `IsUMDBound.isLowerRandomisedUMDBound`,
`isUMDBound_of_randomised`). The package's source contains no `sorry`.

**Departures.** None in the argument.

**Who uses it.** Cassese's `CoxVeraarDecoupling`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)), for every Banach space
`(E, nrm)`, is derived from `decoupling` by `Cassese.coxVeraarDecoupling_holds` there. It is
applied to `S_q^{d×d}` (`square_decoupling` in `Morrey/Cassese/Square.lean`) in the proofs of
Proposition 6.2, Remark 6.3 and Proposition 6.5, and so of Theorem 1.4 and Corollary 6.1. None of
them takes it as a hypothesis.
