module

public import Basic.CalculusOfVariations.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Kristensen: smoothing a rank-one convex, non-quasiconvex polynomial

J. Kristensen, *On the non-locality of quasiconvexity*, Ann. Inst. H. Poincaré Anal. Non Linéaire
16 (1999), Proposition 2 and its proof; S. Heinz, PhD thesis (2008). Cassese's Corollary 5.2 is
"a standard smoothing argument applied to the polynomial integrand" (TeX lines 2048–2050), with
these citations and no other proof. Large but feasible (class L of the inventory): a proposition
with no proof, a hypothesis of every statement whose proof uses it (only Corollary 5.2).

It is stated in the narrowest form in which Cassese uses it, not in the generality of the
sources: on `ℝ^{2×m}` with `m ≥ 3`, for homogeneous quartic polynomials (the integrand to which
Corollary 5.2 applies it is the quartic of Theorem 1.3, lifted from `ℝ^{2×3}` to `ℝ^{2×m}` through
the first three columns). Neither Kristensen's paper nor Heinz's thesis was consulted for this
formalization, so the form of their statements, and whether this instance is literally one of
them, are unverified.
-/

@[expose] public section

open MeasureTheory

namespace External.Kristensen

open CalculusOfVariations

/-- The smoothing argument of Kristensen (1999), Proposition 2 and its proof, and Heinz (2008), in
the form Cassese uses for Corollary 5.2 (TeX lines 2048–2065): for `m ≥ 3`, if a homogeneous
quartic polynomial `P : ℝ^{2×m} → ℝ` is rank-one convex and not quasiconvex at `0`, there are a
smooth `h` and `c, C > 0` with `D²h (A) [H, H] ≥ c |H|²` for every `A` and every rank-one `H`,
`c |A|² ≤ h (A) ≤ C (1 + |A|²)`, and `h` not quasiconvex at `0` (`|·|` the Frobenius norm). The
sources were not consulted: this is the statement as Cassese applies it. -/
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

end External.Kristensen
