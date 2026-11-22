# Cox–Veraar: decoupling with the UMD constant

**Source.** S. Cox, M. Veraar, *Some remarks on tangent martingale difference sequences in
`L¹`-spaces*, Electron. Commun. Probab. 12 (2007), 421–433 (arXiv:0801.0695). Its introduction
was read: in a UMD space `X`, a martingale difference sequence and a decoupled tangent sequence of
it (one satisfying the (CI) condition) have comparable `L^p` norms, `p ∈ (1, ∞)`, and one may take
the constant to be the UMD constant `β_{p,X}`. Cox–Veraar credit this to T. R. McConnell
(*Decoupling and stochastic integration in UMD Banach spaces*, Probab. Math. Statist. 10 (1989))
and, independently, to an unpublished manuscript of P. Hitczenko, and the proof from the
definition of UMD to S. Montgomery-Smith.

**Statement used by Cassese.** Proposition 2.8 (TeX lines 875–896, (6)), citing Cox–Veraar and
HNVW I, Proposition 4.2.3: for a UMD space `X`, `p ∈ (1, ∞)`, a martingale `dY_n = ε_n ξ_n` for the
filtration of i.i.d. Rademacher signs, with `ξ_n` predictable and in `L^p (X)`, and `Ỹ_n` defined
by `dỸ_n = ε̃_n ξ_n` with `ε̃` an independent copy of the signs,
`UMD_p (X)⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p (X) ‖Ỹ_n‖_{L^p}`. This is the Paley–Walsh case of
Cox–Veraar's statement (by their Example 1, `ε̃_n ξ_n` is tangent to `ε_n ξ_n` and satisfies the
(CI) condition), and only this case is stated.

**Lean.** [`Decoupling.lean`](Decoupling.lean):

- `External.CoxVeraar.decoupling`: for a real Banach space `X`, `p ∈ (1, ∞)` and predictable
  `ξ : Fin N → {±1}^N → X`, `‖Σ_{k<n} ε̃_k ξ_k‖_{L^p} ≤ UMD_p (X) ‖Σ_{k<n} ε_k ξ_k‖_{L^p}` and
  `‖Σ_{k<n} ε_k ξ_k‖_{L^p} ≤ UMD_p (X) ‖Σ_{k<n} ε̃_k ξ_k‖_{L^p}`, on the canonical spaces
  `{±1}^N` and `{±1}^N × {±1}^N` (`BanachProbability.SignCube.paleyWalsh`,
  `BanachProbability.decoupledLpNorm`), with `UMD_p (X) = BanachProbability.umdConst X p`.

The same statement is HNVW I, Proposition 4.2.3 (`External.HNVW.proposition4_2_3`, in
[`../HNVW`](../HNVW)).

**Proof.** `BanachProbability.decoupling` in the package `BanachProbability`
(`lean4-banach-probability`, required by path at `../lean4-banach-probability-int` while it is
developed), the proof from the definition that Cox–Veraar attribute to Montgomery-Smith: with
`η_k = ε_k ε̃_k`, the map `(ε, ε̃) ↦ (ε, η)` preserves the uniform measure, and in the interleaved
order `η_0, ε_0, η_1, ε_1, …` of the doubled cube `Σ ε̃_k ξ_k = Σ η_k ε_k ξ_k` is the transform of
`Σ ε_k ξ_k` by the predictable signs `η_k`, and conversely. This gives both inequalities with the
dyadic constant `UMD_p^Δ (X)`, hence with `UMD_p (X)`. The package's source contains no `sorry`.

**Who uses it.** Cassese's `CoxVeraarDecoupling`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)), for every Banach space
`(E, nrm)`, is derived from `decoupling` by `Cassese.coxVeraarDecoupling_holds` there. It is
applied to `S_q^{d×d}` (`square_decoupling` in `Morrey/Cassese/Square.lean`) in the proofs of
Proposition 6.2, Remark 6.3 and Proposition 6.5, and so of Theorem 1.4 and Corollary 6.1. None of
them takes it as a hypothesis.
