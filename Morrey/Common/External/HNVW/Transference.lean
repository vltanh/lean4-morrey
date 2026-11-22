module

public import HarmonicAnalysis.Transference.Homogeneous
public import HarmonicAnalysis.BeurlingAhlfors.Transference

/-!
# Transference for homogeneous Fourier multipliers (HNVW I, Corollary 5.7.6)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I* (2016; read),
Corollary 5.7.6 (pp. 462–463), which Cassese (arXiv:2608.03488v3) cites in the proof of Proposition
7.2 (TeX lines 2832–2835) as "the standard transference identity for homogeneous multipliers".

The book's corollary: for `m ∈ C (ℝ^d ∖ {0}; ℒ (X, Y))` homogeneous of degree `0` (with `m (0)` its
mean over the unit sphere), the boundedness of `T_m` from `L^p (ℝ^d; X)` to `L^p (ℝ^d; Y)`, of
`T_{(m (k))_{k ≠ 0}}` from `L^p_0 (𝕋^d; X)` to `L^p_0 (𝕋^d; Y)` and of `T_{(m (k))}` from
`L^p (𝕋^d; X)` to `L^p (𝕋^d; Y)` are equivalent, and the three norms `I`, `II`, `III` are equal.
Cassese uses the inequality `I ≤ II`, from the torus to the plane, for scalar symbols on `ℝ² ≅ ℂ`,
which is the case stated:

* `External.HNVW.transference`: for a symbol `m : ℂ → ℂ`, continuous off `0` and homogeneous of
  degree `0` (`m (t ξ) = m (ξ)`, `t > 0`; such an `m` is bounded and measurable), and `1 < p < ∞`,
  `‖T_m‖_{L^p (ℝ²) → L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²) → L^p_0 (𝕋²)}`, where on the torus `T_m`
  multiplies the Fourier coefficient at `n ∈ ℤ²` by `m (n₀ + i n₁)`;
* `External.HNVW.transference_beurlingPow`: the instance `m (ξ) = (ξ̄ / ξ)^k`, the powers of the
  Beurling–Ahlfors transform.

The norms are suprema over dense subspaces: Schwartz functions on `ℝ²`, mean-zero trigonometric
polynomials on `𝕋²` (`HarmonicAnalysis.multiplierNorm`, `HarmonicAnalysis.torusMultiplierNorm`).

Proof: in the package `HarmonicAnalysis` (`lean4-harmonic-analysis`),
`HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm`, by the book's argument: `I ≤ II` is its
Proposition 5.7.4 (pp. 460–462) for a homogeneous symbol. For `f`, `g` with Fourier transforms in
`C_c^∞ (ℝ² ∖ {0})`, the pairing `∫ T_m f · g` is a limit of Riemann sums that are pairings of
trigonometric polynomials on `𝕋²`; Hölder's inequality there, Lemma 5.7.5 (Poisson summation) for
`f` in `L^p` and `g` in `L^{p'}`, and the density of such functions (Proposition 2.4.23) with
duality give the bound. The slips of the book on these pages are repaired and listed in the package.
-/

@[expose] public section

namespace External.HNVW

/-- **HNVW I, Corollary 5.7.6**, the inequality `I ≤ II` (for `ℝ² ≅ ℂ` and scalar symbols): for a
symbol `m : ℂ → ℂ`, continuous at every `ξ ≠ 0` and homogeneous of degree `0`,
`‖T_m‖_{L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²)}` for `1 < p < ∞`. -/
theorem transference {m : ℂ → ℂ} (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ)
    (hmh : ∀ t : ℝ, 0 < t → ∀ ξ, m (t * ξ) = m ξ) {p : ℝ} (hp : 1 < p) :
    HarmonicAnalysis.multiplierNorm m p ≤
      HarmonicAnalysis.torusMultiplierNorm (fun n => m (HarmonicAnalysis.latticePoint n)) p :=
  HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm hmc hmh hp

/-- HNVW I, Corollary 5.7.6, for the powers of the Beurling–Ahlfors transform:
`‖𝓑^k‖_{L^p (ℝ²)} ≤ ‖𝓑^k‖_{L^p_0 (𝕋²)}` for `1 < p < ∞`. -/
theorem transference_beurlingPow (k : ℕ) {p : ℝ} (hp : 1 < p) :
    HarmonicAnalysis.beurlingPowNorm k p ≤ HarmonicAnalysis.torusBeurlingPowNorm k p :=
  HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm k hp

end External.HNVW
