# Dragičević: lower bounds for the powers of the Beurling–Ahlfors transform

**Sources.**

- O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471, Theorem 1.1 (Cassese's `[Dragicevic]`). Not
  accessible; its theorem and proof were read in the next two sources.
- O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes (Seville, 2013),
  arXiv:2109.04555, §4.1, Proposition 4.2, attributed there to the 2011 article; Exercises 1.16
  and 2.19.
- A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex Riesz
  transform*, Math. Ann. 386 (2023), 1081–1125, arXiv:2109.08369 (Cassese's `[Dragicevic1]`),
  §1.1 (the 2011 theorem for even powers), §1.3.1 (`‖R^k‖_p = ‖R^k‖_q`), §2.1.

**The theorem.** For `n ∈ ℕ`, `p > 2` and `q = p / (p − 1)`,
`‖𝓑^n‖_{L^p} ≥ κ_n (p) = (1/q)_n / (1/p)_n`, with the Pochhammer symbol
`(a)_n = a (a + 1) ⋯ (a + n − 1)`. For `n = 2`, `κ₂ (p) = (p − 1)(2p − 1) / (p + 1)`.

**Statements used by Cassese.** The case `n = 2`: in the proof of Theorem 7.1 (TeX lines
2865–2870), `‖𝓑²‖_p > p* − 1` for `p ≠ 2`, `p* = max (p, q)`; in the proof of Corollary 7.2 (TeX
lines 2895–2900), `‖𝓑²‖₄ ≥ 21/5 = κ₂ (4)`. For `p < 2` the source's route is the duality
`‖𝓑^n‖_p = ‖𝓑^n‖_q` (Carbonaro–Dragičević–Kovač §1.3.1: `𝓑^{−n}` is the `L²`-adjoint of `𝓑^n`, and
`𝓑^{−n} f = conj (𝓑^n (conj f))`), then the theorem at `q > 2`. The excess
`κ₂ (p*) − (p* − 1) = (p* − 1)(p* − 2) / (p* + 1)` is positive for `p* > 2`.

**Lean.** [`LowerBound.lean`](LowerBound.lean):

- `External.Dragicevic.theorem1_1_two`: `κ₂ (p) ≤ ‖𝓑²‖_p` for `p > 2`;
- `External.Dragicevic.beurlingPowNorm_conjExponent`: `‖𝓑^n‖_p = ‖𝓑^n‖_q` for `1 < p < ∞`;
- `External.Dragicevic.theorem1_1_two_pStar`: `κ₂ (p*) ≤ ‖𝓑²‖_p` for `1 < p < ∞`, from the two.

The norms are suprema over Schwartz functions (`HarmonicAnalysis.beurlingPowNorm`). General `n`
is not formalized; Cassese uses only `n = 2`.

**Proof.** In the package `HarmonicAnalysis` (`lean4-harmonic-analysis`, required by path while it is developed)
(`HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two`,
`HarmonicAnalysis.beurlingPowNorm_conjExponent`), by the source's argument (lecture notes,
Proposition 4.2): `𝓑² (∂̄² F) = ∂² F` (Exercise 2.19), explicit radial integrals of `|∂² F|^p` and
`|∂̄² F|^p` over the unit disc, a bounded contribution outside it, and the limit of the ratio.
Departure from the source, forced by the representation: the source's test functions
`z² |z|^{−2α} g (|z|)`, `α < 1/p`, are not Schwartz functions, and `‖𝓑²‖_p` is a supremum over
Schwartz functions, so the proof uses `z² (|z|² + ε²)^{−1/p} σ (|z|²)` with a smooth cutoff `σ`,
at the critical exponent `α = 1/p`, and lets `ε → 0` instead of `α → 1/p` (Cassese mentions
"standard smoothing arguments", TeX line 2908). The duality is proved as in
Carbonaro–Dragičević–Kovač §1.3.1, for Fourier multipliers with bounded symbols.

**Who uses it.** Cassese's `DragicevicLowerBound`
([`Morrey/Cassese/Defs.lean`](../../../Cassese/Defs.lean)) and `DragicevicL4Bound`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)) are derived from these by
`Cassese.dragicevicLowerBound_holds` and `Cassese.dragicevicL4Bound_holds`. They are still
hypotheses of Theorem 7.1, Corollary 7.2, Theorem 1.5 and Corollary 1.6.
