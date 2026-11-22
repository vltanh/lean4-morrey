# HNVW: Hytönen, van Neerven, Veraar, Weis, *Analysis in Banach Spaces*

**Source.** T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I:
Martingales and Littlewood–Paley Theory*, Springer 2016 (HNVW I), Corollary 5.7.6. The book was not
accessible: the statement of Corollary 5.7.6 was not consulted, and its exact form is not known
here.

**Statement used by Cassese.** In the proof of Proposition 7.2 (TeX lines 2832–2835), "the
standard transference identity for homogeneous multipliers; see [HNVW I, Corollary 5.7.6]", in the
direction from the torus to the plane: `‖𝓑^k‖_{L^p (ℝ²)} ≤ ‖𝓑^k‖_{L^p_0 (𝕋²)}` for `k ≥ 1`,
`p ∈ (1, ∞)`, where `𝓑` is the Beurling–Ahlfors transform, symbol `ξ̄ / ξ`. Only this direction
is used, and only it is stated.

**Lean.** [`Transference.lean`](Transference.lean):

- `External.HNVW.transference`: for a symbol `m : ℂ → ℂ`, continuous at every `ξ ≠ 0`, with
  `m (t ξ) = m (ξ)` for `t > 0` (hence bounded and measurable), and `1 < p < ∞`,
  `‖T_m‖_{L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²)}`; on the torus `T_m` multiplies the coefficient at
  `n ∈ ℤ²` by `m (n₀ + i n₁)`, and its norm is taken on mean-zero trigonometric polynomials.
- `External.HNVW.transference_beurlingPow`: the instance `m (ξ) = (ξ̄ / ξ)^k`.

**Proof.** The source being inaccessible, the standard argument is used: de Leeuw's
(K. de Leeuw, *On `L_p` multipliers*, Ann. of Math. 81 (1965), 364–379), in the direction from
`𝕋^d` to `ℝ^d`, for symbols continuous off `0` and homogeneous of degree `0`. Both statements are
derived in the package `HarmonicAnalysis` (`lean4-harmonic-analysis`, required by path while it is developed)
(`HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm`,
`HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm`): sample `𝓕 f` on `R⁻¹ ℤ²`, bound the
torus norms through the periodisation of `f` and Poisson summation on `ℤ²`, recognise the
multiplied series as lattice Riemann sums of `T_m f` (by homogeneity), and conclude with Fatou's
lemma. Some of the package's statements are still proved with `sorry`; its audit lists them, and
the project's audit reports `sorryAx` for the results here until they are proved.

**Who uses it.** Cassese's `HNVWTransference` ([`Morrey/Cassese/Defs.lean`](../../../Cassese/Defs.lean))
is derived from `transference_beurlingPow` by `Cassese.hnvwTransference_holds`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)). It is still a hypothesis
of Proposition 7.2 (lower bound), Theorem 7.1, Corollary 7.2, Theorem 1.5 and Corollary 1.6.

Other results of HNVW that Cassese cites (UMD spaces: extrapolation, decoupling, the dyadic and
zig-zag characterisations, Khintchine inequalities) are not in this directory.
