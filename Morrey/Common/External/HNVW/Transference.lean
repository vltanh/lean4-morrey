module

public import HarmonicAnalysis.Transference.Homogeneous
public import HarmonicAnalysis.BeurlingAhlfors.Transference

/-!
# Transference for homogeneous Fourier multipliers (HNVW I, Corollary 5.7.6)

T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces. Volume I* (2016),
Corollary 5.7.6, which Cassese (arXiv:2608.03488v3) cites in the proof of Proposition 7.2 (TeX
lines 2832–2835) as "the standard transference identity for homogeneous multipliers". The book
was not accessible, so the exact form of its Corollary 5.7.6 was not consulted.

The direction that Cassese uses, from the torus to the plane, is stated here for scalar symbols
on `ℝ² ≅ ℂ` and derived by de Leeuw's argument (K. de Leeuw, *On `L_p` multipliers*, Ann. of
Math. 81 (1965), 364–379) in the package `HarmonicAnalysis`
(`HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm`):

* `External.HNVW.transference`: for a symbol `m : ℂ → ℂ`, continuous off `0` and homogeneous of
  degree `0` (`m (t ξ) = m (ξ)`, `t > 0`; such an `m` is bounded and measurable), and `1 < p < ∞`,
  `‖T_m‖_{L^p (ℝ²) → L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²) → L^p_0 (𝕋²)}`, where on the torus `T_m`
  multiplies the Fourier coefficient at `n ∈ ℤ²` by `m (n₀ + i n₁)`;
* `External.HNVW.transference_beurlingPow`: the instance `m (ξ) = (ξ̄ / ξ)^k`, the powers of the
  Beurling–Ahlfors transform.

The norms are suprema over dense subspaces: Schwartz functions on `ℝ²`, mean-zero trigonometric
polynomials on `𝕋²` (`HarmonicAnalysis.multiplierNorm`, `HarmonicAnalysis.torusMultiplierNorm`).
Only this direction (`≤`) of the identity is stated.
-/

@[expose] public section

namespace External.HNVW

/-- HNVW I, Corollary 5.7.6 (the direction used, by de Leeuw's argument): for a symbol
`m : ℂ → ℂ`, continuous at every `ξ ≠ 0` and homogeneous of degree `0`,
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
