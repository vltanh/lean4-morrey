# HNVW: Hytönen, van Neerven, Veraar, Weis, *Analysis in Banach Spaces*

**Sources.** T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I:
Martingales and Littlewood–Paley Theory*, Springer 2016 (HNVW I), Proposition 4.2.3, Theorems
4.2.5, 4.2.7, 4.5.6, Corollary 5.7.6; *Volume II: Probabilistic Methods and Operator Theory*,
Springer 2017 (HNVW II), Theorem 6.2.4. Neither volume was accessible: the statements are the ones
Cassese quotes, and the exact form of Corollary 5.7.6 is not known here.

**Statements used by Cassese** (`p* = max (p, p / (p − 1))`, `UMD_p` as in his Definition 2.5).

- Theorem 4.2.7, Proposition 2.7 (1) (TeX lines 829–831): `UMD_{p₀}` for one `p₀ ∈ (1, ∞)` gives
  `UMD_p` for all `p ∈ (1, ∞)`, and `UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 100 p* UMD₂ (X)`. Theorem 4.2.5,
  Proposition 2.7 (4) (TeX lines 837–841): `UMD_p^{dyad} (X) = UMD_p (X)`.
- Theorem 4.5.6, Proposition 2.7 (6) (TeX lines 857–869): `X` is `UMD_p` if and only if some `U`
  with `U (0, 0) = 0`, `U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p` is zig-zag concave; then `β ≥ UMD_p (X)`.
- Proposition 4.2.3, with Cox–Veraar, Proposition 2.8 (TeX lines 875–896): for `dY_n = ε_n ξ_n`,
  `ξ_n` predictable, `dỸ_n = ε̃_n ξ_n`: `UMD_p⁻¹ ‖Ỹ_n‖_p ≤ ‖Y_n‖_p ≤ UMD_p ‖Ỹ_n‖_p`.
- Theorem 6.2.4 of HNVW II, Proposition 6.4 (TeX lines 2314–2321): for `p, q ∈ (1, ∞)` and every
  Banach space, `‖Σ ε_i x_i‖_{L^p} ≤ k_{p,q} ‖Σ ε_i x_i‖_{L^q}`.
- Corollary 5.7.6, proof of Proposition 7.2 (TeX lines 2832–2835), from the torus to the plane
  only: `‖𝓑^k‖_{L^p (ℝ²)} ≤ ‖𝓑^k‖_{L^p_0 (𝕋²)}`, `k ≥ 1`, `𝓑` the Beurling–Ahlfors transform.

**Lean.** Real Banach spaces, `BanachProbability.umdConst` (predictable signs, any filtration),
Paley–Walsh martingales on the sign cube `{±1}^N`: [`Extrapolation.lean`](Extrapolation.lean),
`External.HNVW.theorem4_2_7`; [`DyadicUMD.lean`](DyadicUMD.lean), `theorem4_2_5`
(`dyadicUMDConst X p = umdConst X p`); [`ZigZag.lean`](ZigZag.lean), `theorem4_5_6` (the
equivalence, and every admissible `β` bounds `UMD_p (X)`); [`Decoupling.lean`](Decoupling.lean),
`proposition4_2_3` (both inequalities); [`KahaneKhintchine.lean`](KahaneKhintchine.lean),
`theorem6_2_4` (normed spaces) and `theorem6_2_4_seminorm` (any seminorm), with
`κ_{p,q} = max (1, √((p − 1) / (q − 1)))`; [`Transference.lean`](Transference.lean),
`transference` (`‖T_m‖_{L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²)}`, `1 < p < ∞`, for `m : ℂ → ℂ` continuous
off `0` and homogeneous of degree `0`) and `transference_beurlingPow`, `m (ξ) = (ξ̄ / ξ)^k`.

**Proofs.** One line each from a package, which uses a named standard argument in place of the
inaccessible source. From `BanachProbability` (`lean4-banach-probability`, required by path at
`../lean4-banach-probability-int` while it is developed): Theorem 4.2.7 from
`umdConst_lt_top_of_lt_top`, `umdConst_two_le_mul`, `umdConst_le_mul_umdConst_two`, by Burkholder's
good-λ method (Ann. Probab. 1 (1973), 9 (1981)) on Paley–Walsh martingales and Maurey's theorem;
Theorem 4.2.5 from `dyadicUMDConst_eq_umdConst`, by Maurey's argument as in Pisier 2016 (read
in its open draft, the 2011 IHP course notes, Lemmas 8.29–8.31, Theorem 8.32); Theorem 4.5.6 from
`umdConst_lt_top_iff_exists_isZigZagConcave`, `umdConst_le_of_isZigZagConcave`, by Burkholder's
argument (1981, 1984; a Bellman function for the converse); Proposition 4.2.3 from `decoupling`, by
the proof from the definition that Cox–Veraar credit to Montgomery-Smith; Theorem 6.2.4 from
`kahaneKhintchine`, by hypercontractivity ([`../Borell`](../Borell)). Corollary 5.7.6 from the
package `HarmonicAnalysis` (by path; `multiplierNorm_le_torusMultiplierNorm`,
`beurlingPowNorm_le_torusBeurlingPowNorm`), by de Leeuw's argument (*On `L_p` multipliers*, Ann. of
Math. 81 (1965), 364–379). Neither package's source contains a `sorry`.

**Who uses it.** In [`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean),
`Cassese.hnvwExtrapolation_holds` is used by `Cassese.umdEllq_lt_top` (the paper's proof of Theorem
1.2, `Cassese.theorem1_2`) and Proposition 6.5; `Cassese.kahaneKhintchine_holds` by (31), so by
Propositions 6.2, 6.5, Theorem 1.4, Corollary 6.1; `Cassese.hnvwTransference_holds` by Proposition
7.2, Theorem 7.1, Corollary 7.2, Theorem 1.5, Corollary 1.6. No proof uses `hnvwDyadicUMD_holds`,
`hnvwZigZag_holds` or `proposition4_2_3` (Proposition 2.8 is from [`../CoxVeraar`](../CoxVeraar)).
None is a hypothesis of any statement.
