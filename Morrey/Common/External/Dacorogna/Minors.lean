module

public import CalculusOfVariations.Minors.RankOneAffine
public import CalculusOfVariations.Minors.Quasiaffine
public import CalculusOfVariations.QuadraticForm.Quasiconvex

/-!
# Dacorogna: rank-one affine functions, minors and quadratic forms

B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer 2008,
Theorems 5.20 and 5.25 (i). Cassese uses both in the proof of Proposition 5.1 only. The book is
paywalled and was not consulted; each statement is proved, in the textbook terms of the package
`CalculusOfVariations`, by a named standard argument (reason (d) of the rules):

* Theorem 5.20, (iii) ⇒ (iv), is the proposition `RankOneAffineMinors`, which Cassese's
  Proposition 5.1 uses; `rankOneAffineMinors_holds` proves it from
  `CalculusOfVariations.RankOneAffine.exists_eq_sum_minor` (rank-one affine ⇒ affine combination of
  minors, by induction on the number of rows, an argument of our own in the spirit of the
  characterisation of null Lagrangians by J. M. Ball, J. C. Currie and P. J. Olver, J. Funct. Anal.
  41 (1981); the minors are rank-one affine by the matrix determinant lemma);
* Theorem 5.20, the direction "minors are quasiaffine", for `3 × 3` minors
  (`minor3_quasiaffine`): the argument of C. B. Morrey, *Quasi-convexity and the lower
  semicontinuity of multiple integrals*, Pacific J. Math. 2 (1952), Lemma 5.1 (divergence
  identities for smooth maps, then mollification);
* Theorem 5.25 (i) is `quadraticForm_quasiconvex`, by the argument of Morrey 1952, Theorem 5.2
  (the linear term integrates to zero; the quadratic term is nonnegative under the
  Legendre–Hadamard condition for smooth maps, here by Plancherel's formula, and then for
  Lipschitz maps, here by mollification).
-/

@[expose] public section

namespace External.Dacorogna

open CalculusOfVariations MeasureTheory

variable {d m : ℕ}

/-- The `k × k` minor of `A` with the rows `r` and the columns `c` (strictly increasing). It is the
package's `CalculusOfVariations.minor` (`minor_eq`). -/
noncomputable def minor (A : Matrix (Fin d) (Fin m) ℝ) {k : ℕ} (r : Fin k ↪o Fin d)
    (c : Fin k ↪o Fin m) : ℝ :=
  (A.submatrix r c).det

theorem minor_eq (A : Matrix (Fin d) (Fin m) ℝ) {k : ℕ} (r : Fin k ↪o Fin d)
    (c : Fin k ↪o Fin m) : minor A r c = CalculusOfVariations.minor A r c :=
  rfl

/-- Dacorogna, Theorem 5.20 (used in the proof of Cassese's Proposition 5.1): a
continuous rank-one affine `f : ℝ^{d×m} → ℝ` is an affine combination of the minors of its
argument (the `0 × 0` minor is the constant `1`). -/
def RankOneAffineMinors : Prop :=
  ∀ (d m : ℕ) (f : Matrix (Fin d) (Fin m) ℝ → ℝ), Continuous f → RankOneAffine f →
    ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
      ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c

/-- **Dacorogna, Theorem 5.20** ((iii) ⇒ (iv)): a rank-one affine `f : ℝ^{d×m} → ℝ` is an affine
combination of the minors of its argument.

Proof: Dacorogna's book was not accessible; the argument is the package's
(`CalculusOfVariations.RankOneAffine.exists_eq_sum_minor`), an induction on the rows (our own,
in the spirit of Ball–Currie–Olver 1981, whose proof was not checked against it): `f` is affine
along each rank-one line `A + t (u ⊗ v)`, hence affine in each row, and an induction on the number of rows writes it as a
combination of minors, the coefficients of the first row being identified through the rank-one
lines `(1; u') ⊗ v` and the Laplace expansion of the determinant along its first row; the minors
are rank-one affine by the matrix determinant lemma. Continuity is not needed. -/
theorem rankOneAffineMinors_holds : RankOneAffineMinors :=
  fun _ _ _ _ hf => RankOneAffine.exists_eq_sum_minor hf

/-- **Dacorogna, Theorem 5.20**, the direction "minors are quasiaffine", for `3 × 3` minors (used
in the proof of Cassese's Proposition 5.1): for a Lipschitz `φ` vanishing outside the unit cube,
`∫_{(0,1)^m} det ((A + ∇φ)_{rc}) = det (A_{rc})`.

Proof: the book was not accessible; the argument is Morrey 1952, Lemma 5.1, in the package
(`CalculusOfVariations.nl_minor3_quasiaffine`): expand
`det (X + Y) = det X + tr (adj X · Y) + tr (X · adj Y) + det Y`; the minors of `∇φ` of orders `1`,
`2`, `3` integrate to zero, for smooth compactly supported maps by the divergence identities and
for Lipschitz maps by mollification and dominated convergence. -/
theorem minor3_quasiaffine {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (h0 : ∀ x ∉ unitCube m, φ x = 0) (A : Matrix (Fin d) (Fin m) ℝ) (r : Fin 3 ↪o Fin d)
    (c : Fin 3 ↪o Fin m) :
    ∫ x in unitCube m, minor (A + grad φ x) r c = minor A r c :=
  nl_minor3_quasiaffine hφ h0 A r c

/-- **Dacorogna, Theorem 5.25 (i)** (used in the proof of Cassese's Proposition 5.1): a rank-one
convex quadratic form is quasiconvex.

Proof: the book was not accessible; the argument is Morrey 1952, Theorem 5.2, in the package
(`CalculusOfVariations.quadraticForm_quasiconvex`): since `Q` is quadratic,
`Q (A + ∇φ) = Q (A) + [Q (A, ∇φ) + Q (∇φ, A)] + Q (∇φ)`; the linear term integrates to `0` (Morrey's
Lemma 5.1), and `∫ Q (∇φ) ≥ 0` under the Legendre–Hadamard condition `Q (a ⊗ ξ) ≥ 0`, which is
rank-one convexity. Morrey takes the quadratic inequality from Van Hove for maps of class `C¹`
vanishing on the boundary and extends it to Lipschitz maps; here the smooth case is Plancherel's
formula for Schwartz functions and the extension is by mollification. -/
theorem quadraticForm_quasiconvex
    (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ))
    (hQ : RankOneConvex fun A => Q A A) : Quasiconvex fun A => Q A A :=
  CalculusOfVariations.quadraticForm_quasiconvex Q hQ

end External.Dacorogna
