module

public import CalculusOfVariations.Smoothing.RankOneConvex

/-!
# Kristensen: smoothing a rank-one convex, non-quasiconvex polynomial

J. Kristensen, *On the non-locality of quasiconvexity*, Ann. Inst. H. Poincaré Anal. Non Linéaire
16 (1999), Proposition 2 and its proof; S. Heinz, PhD thesis (2008). Cassese's Corollary 5.2 is
"a standard smoothing argument applied to the polynomial integrand" (TeX lines 2048–2050), with
these citations and no other proof.

It is stated in the narrowest form in which Cassese uses it, not in the generality of the
sources: on `ℝ^{2×m}` with `m ≥ 3`, for homogeneous quartic polynomials (the integrand to which
Corollary 5.2 applies it is the quartic of Theorem 1.3, lifted from `ℝ^{2×3}` to `ℝ^{2×m}` through
the first three columns). Kristensen's article was read from a scan of it (pp. 6–7: Proposition 2,
a statement about local quasiconvexity, and its proof, whose first step is the smoothing used
here); the statement below is that smoothing step in the form Cassese applies it, and the proof
follows Kristensen's proof of Proposition 2 (p. 7). Heinz's thesis was not consulted. The proof is
in the package `CalculusOfVariations` (`CalculusOfVariations.Smoothing.exists_smoothing`, for every
smooth rank-one convex integrand on `ℝ^{d×m}` that is not quasiconvex at `0`).

## The proof (`smoothing_holds`)

Kristensen's proof: for a rank-one convex, non-quasiconvex quartic `p` take cut-offs `ζ_s`, `ξ_s`
(`ζ_s = 1` below `s`, `0` above `s + 1`; `ξ_s = 0` below `s - 1`, `t²` above `s + 1`, convex and
nondecreasing); "it is not hard to see" that for suitable `s > 1`, `k > 0` the function
`p ζ_s (|X|) + k ξ_s (|X|)` is rank-one convex and not quasiconvex; then add `ε |X|²` with `ε` so
small that non-quasiconvexity survives, and the uniform Legendre–Hadamard condition with constant
`ε` holds. The "not hard to see" step is supplied here, along Kristensen's lines
(`CalculusOfVariations.Smoothing.exists_smoothing`):

* *not quasiconvex*: `p` fails quasiconvexity at `0` with a `K`-Lipschitz `φ`, so
  `|∇φ|² ≤ B := 2 m K²` everywhere. The radii are chosen beyond `B`, so `h = p + ε |·|² + K₀` on
  the range of `∇φ`, and `ε := δ / (2 (∫_Q |∇φ|² + 1))`, `δ := p (0) - ∫_Q p (∇φ) > 0`, keeps the
  strict inequality;
* *Legendre–Hadamard*: with `r = |A|²`, `D²h (A) [H, H] = D²(p ζ) (A) [H, H] + Φ'' (r) 4 ⟨A, H⟩² +
  2 Φ' (r) |H|²`, `Φ = k ξ + ε id + K₀`. Where `ζ = 1` (`r < a₀ + 1`) the first term is
  `D²p (A) [H, H] ≥ 0` (rank-one convexity); where `ζ = 0` it vanishes; on the compact annulus
  `a₀ + 1 ≤ r ≤ a₀ + 2` it is `≥ -M |H|²`, `M ≥ 0` a bound of `‖D²(p ζ)‖` on a ball containing
  the annulus, while `ξ' = 1` there, so `k := M / 2` compensates. In all cases
  `D²h (A) [H, H] ≥ 2 ε |H|² ≥ ε |H|²`, and `c := ε`;
* *growth*: `|p ζ| ≤ M'` (`M'` a bound of `|p|` on the support of `ζ`), `0 ≤ ξ (r) ≤ r`, so
  `ε |A|² ≤ h (A) ≤ (2 M' + 1 + k + ε) (1 + |A|²)` with `K₀ := M' + 1`;
* *smoothness*: `ζ`, `ξ` are smooth functions of `|X|²`, a polynomial.

Departures from Kristensen's construction, and their reasons:

* the cut-offs are functions of `r = |X|²` instead of `t = |X|`: `ζ (r) = σ (a₀ + 2 - r)` and
  `ξ (r) = ∫₀^r σ (τ - a₀) dτ` (`σ` = `Real.smoothTransition`). Kristensen's `ξ_s` (convex, `0`
  below `s - 1`, `t²` above `s + 1`, `ξ_s'' > 0` on `(s - 1, s + 1)`) exists only for `s < 3`
  (convexity at `s + 1` gives `0 = ξ_s (s - 1) ≥ (s + 1)² - 4 (s + 1)`), and he does not say how
  `s` is chosen; as functions of `|X|²` the cut-offs exist for every radius, which the choice of
  the radii beyond the range of `∇φ` uses, their compositions with `|·|²` are smooth, and
  `D²(ξ ∘ |·|²) [H, H] = 4 ξ'' ⟨A, H⟩² + 2 ξ' |H|²`. Read as
  functions of `t` (with `s = √(a₀ + 1)`), `ζ` has Kristensen's properties; `ξ` is convex and
  nondecreasing and `0` below `s - 1`, but equals `t² - c` (not `t²`) far out, and its second
  derivative vanishes on the part of `(s - 1, s + 1)` where `ξ = 0`. What the argument uses
  (`ξ'' ≥ 0`, `0 ≤ ξ' ≤ 1`, `ξ' = 1` where `ζ` is not constant) holds. Kristensen does not write
  this step out, so the argument for it is ours;
* the constant `K₀ = M' + 1` is added: the statement requires `c |A|² ≤ h (A)` for every `A`,
  so `h (0) > 0`, whereas Kristensen's `g (0) = p (0) = 0`. Adding a constant changes neither
  second derivatives nor quasiconvexity at `0` on the unit cube, whose volume is `1`;
* `ε` is chosen independently of `s` and `k`: on the range of `∇φ` the function is
  `p + ε |·|² + K₀` whatever `k` is.

Homogeneity of `P` and `m ≥ 3` are not used: `CalculusOfVariations.Smoothing.exists_smoothing`
holds on every `ℝ^{d×m}` for every smooth rank-one convex integrand that is not quasiconvex at `0`.
-/

@[expose] public section

open MeasureTheory

namespace External.Kristensen

open CalculusOfVariations

/-- The smoothing argument of Kristensen (1999), Proposition 2 and its proof, and Heinz (2008), in
the form Cassese uses for Corollary 5.2 (TeX lines 2048–2065): for `m ≥ 3`, if a homogeneous
quartic polynomial `P : ℝ^{2×m} → ℝ` is rank-one convex and not quasiconvex at `0`, there are a
smooth `h` and `c, C > 0` with `D²h (A) [H, H] ≥ c |H|²` for every `A` and every rank-one `H`,
`c |A|² ≤ h (A) ≤ C (1 + |A|²)`, and `h` not quasiconvex at `0` (`|·|` the Frobenius norm). It is
the smoothing step of Kristensen's proof of Proposition 2 (p. 7, read from a scan of the article),
stated as Cassese applies it; it is not the statement of Kristensen's Proposition 2. Heinz's thesis
was not consulted. -/
def Smoothing : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ P : MvPolynomial (Fin 2 × Fin m) ℝ, P.IsHomogeneous 4 →
    RankOneConvex
      (fun A : Matrix (Fin 2) (Fin m) ℝ => MvPolynomial.eval (fun ij => A ij.1 ij.2) P) →
    ¬ QuasiconvexAtOn (unitCube m)
      (fun A : Matrix (Fin 2) (Fin m) ℝ => MvPolynomial.eval (fun ij => A ij.1 ij.2) P) 0 →
    ∃ (h : Matrix (Fin 2) (Fin m) ℝ → ℝ) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X : Fin 2 → Fin m → ℝ => h (Matrix.of X)) ∧
      (∀ A H : Matrix (Fin 2) (Fin m) ℝ, H.rank = 1 →
        c * ∑ i, ∑ j, H i j ^ 2 ≤ iteratedDeriv 2 (fun t : ℝ => h (A + t • H)) 0) ∧
      (∀ A : Matrix (Fin 2) (Fin m) ℝ,
        c * ∑ i, ∑ j, A i j ^ 2 ≤ h A ∧ h A ≤ C * (1 + ∑ i, ∑ j, A i j ^ 2)) ∧
      ¬ QuasiconvexAtOn (unitCube m) h 0

open scoped ContDiff in
/-- **Kristensen's smoothing argument holds** (`Smoothing`), by Kristensen's proof of
Proposition 2, with its "not hard to see" step supplied along Kristensen's lines (module
docstring): `CalculusOfVariations.Smoothing.exists_smoothing` applied to the polynomial, which is
smooth. -/
theorem smoothing_holds : Smoothing := by
  intro m _ P _ hrc hnqc
  set p : Matrix (Fin 2) (Fin m) ℝ → ℝ := fun A => MvPolynomial.eval (fun ij => A ij.1 ij.2) P
  have hp : ContDiff ℝ ∞ fun X : Fin 2 → Fin m → ℝ => p (Matrix.of X) :=
    Smoothing.contDiff_eval_mvPolynomial P
      (fun (X : Fin 2 → Fin m → ℝ) (ij : Fin 2 × Fin m) => X ij.1 ij.2)
      fun ij => contDiff_apply_apply ℝ ij.1 ij.2
  exact CalculusOfVariations.Smoothing.exists_smoothing p hp hrc hnqc

end External.Kristensen
