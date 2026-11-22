# Pisier: `L^p` spaces are UMD

**Source.** G. Pisier, *Martingales in Banach Spaces*, Cambridge Studies in Advanced Mathematics
155, Cambridge University Press 2016, Corollary 5.22. The book was read in its open draft,
*Martingales in Banach spaces (in connection with type and cotype)*, the IHP course notes of 2011,
where the result is Corollary 8.19, proved "by Fubini".

**Statement used by Cassese.** Proposition 2.7 (3) (TeX lines 835–836): for every measure space
`(Ω, Σ, μ)` and `p ∈ (1, ∞)`, `L^p (Ω, Σ, μ)` is a UMD space. It is used for `ℓ_q`: "by
Proposition 2.7 and the isometric embedding `ℓ_q^n ↪ ℓ_q`", `UMD_{ℂ,p} (ℓ_q)` controls the
`ℓ_q^n`-valued unimodular martingale transforms uniformly in `n` (TeX lines 991–992).

**Lean.** [`LpUMD.lean`](LpUMD.lean), with `UMD_p = BanachProbability.umdConst` (predictable signs,
general filtrations):

- `External.Pisier.corollary5_22`: `UMD_p (L^p (μ; ℂ)) < ∞` for every measure `μ` and
  `p ∈ (1, ∞)`, at the exponent `p` of the space, the complex `L^p` taken as a real Banach space;
- `External.Pisier.corollary5_22_vector`: `UMD_p (L^p (μ; B)) ≤ UMD_p (B)` for every measure `μ`,
  real Banach space `B` and `p ∈ (1, ∞)`.

**Proof.** `BanachProbability.umdConst_Lp_complex_lt_top` and `BanachProbability.umdConst_Lp_le`
in the package `BanachProbability`
([lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability), commit `250cd49`),
by the dyadic form of the source's
Fubini argument, which needs neither σ-finiteness nor joint measurability: a Paley–Walsh martingale
with values in `L^p (μ; B)` takes finitely many values, so for `μ`-almost every `s` its evaluation
at `s` is a `B`-valued Paley–Walsh martingale and the transform commutes with evaluation; the
dyadic bound of `B` is integrated in `s`, and Maurey's theorem (HNVW I, Theorem 4.2.5) passes to
general filtrations. For `B = ℂ`, the real Hilbert space `ℝ²`, the constant is Burkholder's
`p* − 1`. The package's source contains no `sorry`.

**Who uses it.** Cassese's `PisierLpUMD`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)) is derived from
`corollary5_22` by `Cassese.pisierLpUMD_holds` there. `Cassese.umdEllq_lt_top`
(`Morrey/Cassese/TwoByM.lean`) uses it, with extrapolation (`Cassese.hnvwExtrapolation_holds`) and
Yaroslavtsev's Lemma 3.2 (`Cassese.yaroslavtsevComplexUMD_holds`), for `UMD_{ℂ,p} (ℓ_q) < ∞`, in
the paper's proof of Theorem 1.2 (`Cassese.theorem1_2`), which does not take it as a hypothesis.
`corollary5_22_vector` is used by no proof.
