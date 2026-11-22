module

public import CalculusOfVariations.Minors.RankOneAffine
public import CalculusOfVariations.Minors.Quasiaffine
public import CalculusOfVariations.QuadraticForm.Quasiconvex

/-!
# Dacorogna: rank-one affine functions, minors and quadratic forms

B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer 2008 (read),
Theorems 5.20 (p. 179) and 5.25 (i) (p. 191). Cassese uses both in the proof of Proposition 5.1 only
(TeX lines 1409–1413). Theorem 5.20 says that the following are equivalent for `f : ℝ^{N×n} → ℝ` (no
continuity is assumed): (i) `f` is quasiaffine; (ii) `f` is rank-one affine; (ii′) `f ∈ C¹` and
`f (ξ + a ⊗ b) = f (ξ) + ⟨∇f (ξ); a ⊗ b⟩`; (iii) `f` is polyaffine; (iii′)
`f (ξ) = f (0) + ⟨β; T (ξ)⟩`, `T (ξ)` the vector of the minors of `ξ`, that is, `f` is a linear
combination of the minors of orders `0` (the constant `1`), `1, …, min (N, n)`. Each statement is
proved, in the textbook terms of the package `CalculusOfVariations`, by the book's arguments:

* Theorem 5.20, (ii) ⇒ (iii′), is the proposition `RankOneAffineMinors`, which Cassese's
  Proposition 5.1 uses; `rankOneAffineMinors_holds` proves it from
  `CalculusOfVariations.RankOneAffine.exists_eq_sum_minor` (pp. 181–191: induction on the number of
  rows, and Lemma 5.24, with the repairs listed below);
* Theorem 5.20, "minors are quasiaffine" ((iii′) ⇒ (i)), for `3 × 3` minors (`minor3_quasiaffine`):
  (8.44) of Theorem 8.35 (p. 409), to which the book refers for it (p. 181; Lemma 5.5 (ii)), for the
  cube. The book proves (8.44) by induction on the order of the minor, and the more general part
  (ii) of the theorem (pp. 410–411) by expanding into mixed minors, writing these as divergences,
  and density; the argument here is the second, for an affine map plus a test map;
* Theorem 5.25 (i) is `quadraticForm_quasiconvex` (pp. 192–194: Lemmas 5.27 and 5.28, by
  Plancherel's formula).

Repairs of the proof of (ii) ⇒ (iii′), along the book's lines (the list with its reasons is in the
module docstring of the package's `Minors/RankOneAffine.lean`): the step from (ii) to `f ∈ C¹` is
not justified in the book and is not needed; in Lemma 5.24, Part 2, the columns are restricted to
the `(s + 1)`-set before its forms `X_β` (5.47) are used, since `g = Σ_β X_β` and the rank-one
affinity of the `X_β` fail for `n > s + 1`; the matrices of its `t²` test have the two columns equal
to zero, which makes the coefficients displayed on p. 190 complete, and the vector `b` is arbitrary,
so that the coefficients that occur in none of the displayed ones are reached too.
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

/-- Dacorogna, Theorem 5.20, (ii) ⇒ (iii′) (used in the proof of Cassese's Proposition 5.1): a
rank-one affine `f : ℝ^{d×m} → ℝ` is a linear combination of the minors of its argument, with the
`0 × 0` minor, the constant `1`. As in the book, `f` is not assumed continuous. -/
def RankOneAffineMinors : Prop :=
  ∀ (d m : ℕ) (f : Matrix (Fin d) (Fin m) ℝ → ℝ), RankOneAffine f →
    ∃ a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ,
      ∀ A, f A = ∑ k ∈ Finset.range (min d m + 1), ∑ r, ∑ c, a k r c * minor A r c

/-- **Dacorogna, Theorem 5.20**, (ii) ⇒ (iii′): a rank-one affine `f : ℝ^{d×m} → ℝ` is a linear
combination of the minors of its argument (of orders `0, …, min (d, m)`).

Proof: the book's (pp. 181–191), in the package
(`CalculusOfVariations.RankOneAffine.exists_eq_sum_minor`): transposing, there are at least as many
columns as rows; by induction on the number of rows, `f (ξ) = ⟨ψ (ξ′); ξ¹⟩ + χ (ξ′)` (5.42) with `χ`
and the entries of `ψ` rank-one affine in the other rows `ξ′`, so (5.44); the parts of the last sum
of (5.44) are rank-one affine, and Lemma 5.24 makes each of them a combination of minors, by the
vanishing of `t²` coefficients along rank-one lines. The repairs are in the module docstring. -/
theorem rankOneAffineMinors_holds : RankOneAffineMinors :=
  fun _ _ _ hf => RankOneAffine.exists_eq_sum_minor hf

/-- **Dacorogna, Theorem 5.20**, the direction "minors are quasiaffine" ((iii′) ⇒ (i)), for `3 × 3`
minors (used in the proof of Cassese's Proposition 5.1): for a Lipschitz `φ` vanishing outside the
unit cube, `∫_{(0,1)^m} det ((A + ∇φ)_{rc}) = det (A_{rc})`.

Proof: the book's (8.44) (Theorem 8.35 (i)) for `3 × 3` minors and the cube, by the proof of its
part (ii) with `u = A x + φ`, in the package (`CalculusOfVariations.nl_minor3_quasiaffine`): expand
`det (X + Y) = det X + tr (adj X · Y) + tr (X · adj Y) + det Y`; the minors of `∇φ` of orders `1`,
`2`, `3` integrate to zero, for smooth compactly supported maps by the divergence identities and
for Lipschitz maps by density (mollification and dominated convergence). -/
theorem minor3_quasiaffine {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (h0 : ∀ x ∉ unitCube m, φ x = 0) (A : Matrix (Fin d) (Fin m) ℝ) (r : Fin 3 ↪o Fin d)
    (c : Fin 3 ↪o Fin m) :
    ∫ x in unitCube m, minor (A + grad φ x) r c = minor A r c :=
  nl_minor3_quasiaffine hφ h0 A r c

/-- **Dacorogna, Theorem 5.25 (i)** (used in the proof of Cassese's Proposition 5.1): a rank-one
convex quadratic form is quasiconvex.

Proof: the book's (pp. 192–194), in the package (`CalculusOfVariations.quadraticForm_quasiconvex`):
since `Q` is quadratic, `Q (A + ∇φ) = Q (A) + [Q (A, ∇φ) + Q (∇φ, A)] + Q (∇φ)`; the linear term
integrates to `0`, so quasiconvexity is `∫ Q (∇φ) ≥ 0`, and rank-one convexity is the
Legendre–Hadamard condition `Q (a ⊗ ξ) ≥ 0` (Lemma 5.27); the Fourier transform of `∇φ` is
`2πi φ̂ ⊗ ξ`, whose real and imaginary parts have rank at most one, and Plancherel's formula gives
the inequality (Lemma 5.28). The book applies Plancherel's formula to the Lipschitz map; here it is
applied to smooth maps, and the inequality passes to Lipschitz maps by mollification. (The book
attributes the result to Van Hove.) -/
theorem quadraticForm_quasiconvex
    (Q : LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ))
    (hQ : RankOneConvex fun A => Q A A) : Quasiconvex fun A => Q A A :=
  CalculusOfVariations.quadraticForm_quasiconvex Q hQ

end External.Dacorogna
