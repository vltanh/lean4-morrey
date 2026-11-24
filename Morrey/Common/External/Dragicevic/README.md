# Dragičević: lower bounds for the powers of the Beurling–Ahlfors transform

**Sources.**

- O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471 (Cassese's `[Dragicevic]`; read), Theorem 1.1 (p. 465; proof
  pp. 466–467).
- A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p` estimates of powers of the complex Riesz
  transform*, Math. Ann. 386 (2023), 1081–1125, arXiv:2109.08369 (Cassese's `[Dragicevic1]`; read),
  §1.3.1 (`‖R^k‖_p = ‖R^k‖_q`, `𝓑 = R²`).
- O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes (Seville, 2013),
  arXiv:2109.04555 (read), Proposition 4.2, which repeats the 2011 theorem and its proof; Exercise 4.1
  on `W^{n,p}` (Exercise 2.19 for `n = 1`).

**The theorem.** For `n ∈ ℕ`, `p > 2` (the article's standing assumption, p. 464) and
`q = p / (p − 1)`, `‖𝓑^n‖_{L^p} ≥ κ_n (p) = (1/q)_n / (1/p)_n`, with the Pochhammer symbol
`(a)_n = a (a + 1) ⋯ (a + n − 1)`; it is the limit of `‖∂^n f_{n,α}‖_p / ‖∂̄^n f_{n,α}‖_p` as
`α ↗ 1/p`. For `n = 2`, `κ₂ (p) = (p − 1)(2p − 1) / (p + 1)`.

**Statements used by Cassese.** The case `n = 2`:

- in the proof of Theorem 7.1 (TeX lines 2865–2870), citing "[Dragicevic, Theorem 1.1] (see also
  [Dragicevic1])", `‖𝓑²‖_p > p* − 1` for `p ≠ 2`, `p* = max (p, q)`;
- in the proof of Corollary 7.2 (TeX lines 2895–2900), `‖𝓑²‖₄ ≥ 21/5 = κ₂ (4)`.

The theorem covers `p > 2`. For `p < 2` one uses the duality
`‖𝓑^n‖_p = ‖𝓑^n‖_q` of Carbonaro–Dragičević–Kovač §1.3.1 (`𝓑^{−n}` is the `L²`-adjoint of `𝓑^n`, and
`𝓑^{−n} f = conj (𝓑^n (conj f))`), then the theorem at `q > 2`. The excess
`κ₂ (p*) − (p* − 1) = (p* − 1)(p* − 2) / (p* + 1)` is positive for `p* > 2`.

**Lean.** [`LowerBound.lean`](LowerBound.lean):

- `External.Dragicevic.theorem1_1_two`: `κ₂ (p) ≤ ‖𝓑²‖_p` for `p > 2`;
- `External.Dragicevic.beurlingPowNorm_conjExponent`: `‖𝓑^n‖_p = ‖𝓑^n‖_q` for `1 < p < ∞`;
- `External.Dragicevic.theorem1_1_two_pStar`: `κ₂ (p*) ≤ ‖𝓑²‖_p` for `1 < p < ∞`, from the two (and, for
  `p = 2`, which the paper does not use, the package's bound for `p > 1`).

The norms are suprema over Schwartz functions (`HarmonicAnalysis.beurlingPowNorm`). General `n`
is not formalized; Cassese uses only `n = 2`.

**Constants.** `κ₂ (p)`, as in the article.

**Proof.** In the package `HarmonicAnalysis`
([lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis):
`HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two`,
`HarmonicAnalysis.beurlingPowNorm_conjExponent`), by the article's argument, with its test functions
`f_{2,α} (z) = z² |z|^{−2α} g₂ (|z|)`, `g₂ = 1` on `[0, 1]`, `g₂ (x) = exp (−(x − 1)²)` for `x > 1` (its
example), `0 < α < 1/p` (the article: `α < 1/p`):

- the explicit integrals of `|∂² f|^p` and `|∂̄² f|^p` over the unit disc;
- a bounded contribution outside it;
- the identity (2.1);
- the limit `α → 1/p`.

The article asserts without proof (p. 465) that `f_{n,α}` "belongs to `W^{n,p}`, which ensures that
`T^n (∂̄^n f) = ∂^n f`". Since `‖𝓑²‖_p` is a supremum over Schwartz functions and `f_{2,α}` is not one,
what is used of this sentence, `‖∂² f‖_p ≤ ‖𝓑²‖_p ‖∂̄² f‖_p`, is proved by approximating `f_{2,α}` by
Schwartz functions and a density statement (`HarmonicAnalysis.div_le_beurlingPowNorm_of_tendsto`). The
duality follows Carbonaro–Dragičević–Kovač §1.3.1, for Fourier multipliers with bounded symbols. The
package proves these with no `sorry` and only Lean's standard axioms.

**Departures.** None in the argument; the sentence on `W^{n,p}` is completed.

**Who uses it.** Cassese's `DragicevicLowerBound` and `DragicevicL4Bound`
([`Morrey/Cassese/Hypotheses.lean`](../../../Cassese/Hypotheses.lean)) are derived from these by
`Cassese.dragicevicLowerBound_holds` and `Cassese.dragicevicL4Bound_holds` there. Theorem 7.1,
Corollary 7.2, Theorem 1.5 and Corollary 1.6 use them through those theorems, and none of them
takes them as hypotheses.
