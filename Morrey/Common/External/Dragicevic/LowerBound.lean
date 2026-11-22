module

public import HarmonicAnalysis.BeurlingAhlfors.LowerBound

/-!
# Dragičević: the lower bound for `‖𝓑²‖_p`

O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling operator*,
Arch. Math. 96 (2011), 463–471 (read), Theorem 1.1 (p. 465; proof pp. 466–467), which Cassese
(arXiv:2608.03488v3) cites in the proofs of Theorem 7.1 (TeX lines 2865–2870) and Corollary 7.2 (TeX
lines 2895–2900), in the first with "see also" A. Carbonaro, O. Dragičević, V. Kovač, *Sharp `L^p`
estimates of powers of the complex Riesz transform*, Math. Ann. 386 (2023), 1081–1125
(arXiv:2109.08369).

The theorem: for `n ∈ ℕ`, `p > 2` (the article's standing assumption, p. 464) and `q = p / (p − 1)`,
`‖𝓑^n‖_p ≥ κ_n (p) = (1/q)_n / (1/p)_n`, with the Pochhammer symbol
`(a)_n = a (a + 1) ⋯ (a + n − 1)`. Cassese uses the case `n = 2`,
`κ₂ (p) = (p − 1)(2p − 1) / (p + 1)`, in Theorem 7.1 for every `p ≠ 2`, through `p* = max (p, q)`.
The article does not state the bound for `p < 2`; that case is `‖𝓑²‖_p = ‖𝓑²‖_q`,
Carbonaro–Dragičević–Kovač §1.3.1:

* `External.Dragicevic.theorem1_1_two`: `κ₂ (p) ≤ ‖𝓑²‖_p` for `p > 2`, the article's statement at
  `n = 2` (from `HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two`, which holds for every
  `p > 1`);
* `External.Dragicevic.beurlingPowNorm_conjExponent`: `‖𝓑^n‖_p = ‖𝓑^n‖_q` for `1 < p < ∞`,
  Carbonaro–Dragičević–Kovač §1.3.1 (`𝓑^{−n}` is the adjoint of `𝓑^n`, and
  `𝓑^{−n} f = conj (𝓑^n (conj f))`);
* `External.Dragicevic.theorem1_1_two_pStar`: `κ₂ (p*) ≤ ‖𝓑²‖_p` for every `p ∈ (1, ∞)`, from the
  two: for `p < 2`, `‖𝓑²‖_p = ‖𝓑²‖_q` and `q = p* > 2`. (For `p = 2`, where `κ₂ (2) = 1`, it is the
  package's bound for `p > 1`; the paper does not use that case.)

The package `HarmonicAnalysis` (`lean4-harmonic-analysis`) derives the theorem by the article's
argument, with its test functions `f_{2,α} (z) = z² |z|^{−2α} g₂ (|z|)`, `g₂` its example
(`HarmonicAnalysis.BeurlingAhlfors.testFun`): explicit integrals over the unit disc, bounded
integrals outside it, the identity (2.1) and the limit `α → 1/p`. The norm of `𝓑²` is a supremum
over Schwartz functions, which `f_{2,α}` is not. The article asserts without proof (p. 465) that
`f_{n,α}` belongs to `W^{n,p}`, "which ensures that `T^n (∂̄^n f) = ∂^n f`". What is used of it,
`‖∂²f‖_p ≤ ‖𝓑²‖_p ‖∂̄²f‖_p`, is proved by approximating `f_{2,α}` by Schwartz functions
(`HarmonicAnalysis.BeurlingAhlfors.exists_schwartz_tendsto_testFun`) and the density statement
`HarmonicAnalysis.div_le_beurlingPowNorm_of_tendsto`.

The theorem and its proof are repeated in Dragičević's lecture notes *Analysis of the
Ahlfors–Beurling transform* (arXiv:2109.04555), Proposition 4.2.
-/

@[expose] public section

namespace External.Dragicevic

/-- Dragičević (2011), Theorem 1.1, the case `n = 2`: `‖𝓑²‖_{L^p} ≥ κ₂ (p) = (1/q)₂ / (1/p)₂` for
`p > 2`, `q = p / (p − 1)`. -/
theorem theorem1_1_two {p : ℝ} (hp : 2 < p) :
    ENNReal.ofReal (HarmonicAnalysis.beurlingKappa 2 p) ≤ HarmonicAnalysis.beurlingPowNorm 2 p :=
  HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two (by linarith)

/-- Carbonaro–Dragičević–Kovač, §1.3.1: `‖𝓑^n‖_{L^p} = ‖𝓑^n‖_{L^q}` for `1 < p < ∞`,
`q = p / (p − 1)`. -/
theorem beurlingPowNorm_conjExponent (n : ℕ) {p : ℝ} (hp : 1 < p) :
    HarmonicAnalysis.beurlingPowNorm n p = HarmonicAnalysis.beurlingPowNorm n (p / (p - 1)) :=
  HarmonicAnalysis.beurlingPowNorm_conjExponent n hp

/-- Dragičević's bound for every `p ∈ (1, ∞)`: `‖𝓑²‖_{L^p} ≥ κ₂ (p*)`, `p* = max (p, q)`; for
`p < 2` from `‖𝓑²‖_p = ‖𝓑²‖_q`. -/
theorem theorem1_1_two_pStar {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (HarmonicAnalysis.beurlingKappa 2 (HarmonicAnalysis.pStar p)) ≤
      HarmonicAnalysis.beurlingPowNorm 2 p := by
  rcases le_or_gt 2 p with h2 | h2
  · rw [HarmonicAnalysis.pStar_of_two_le h2]
    rcases h2.lt_or_eq with h2 | rfl
    · exact theorem1_1_two h2
    · exact HarmonicAnalysis.beurlingKappa_two_le_beurlingPowNorm_two hp
  · rw [HarmonicAnalysis.pStar_of_lt_two hp h2, beurlingPowNorm_conjExponent 2 hp]
    exact theorem1_1_two (by rw [lt_div_iff₀ (by linarith)]; linarith)

end External.Dragicevic
