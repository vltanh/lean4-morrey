module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Challenge: Šverák 1992, rank-one convexity does not imply quasiconvexity

V. Šverák, *Rank-one convexity does not imply quasiconvexity*, Proc. Roy. Soc. Edinburgh 120A
(1992), 185–189. The paper constructs a quartic polynomial `F` on the space `M^{3×2}` of real
`3 × 2` matrices that is rank-one convex but not quasiconvex, and lifts it to `M^{m×n}` for
`m ≥ 3`, `n ≥ 2`: rank-one convexity does not imply quasiconvexity for maps with at least three
components. This file states the paper's Theorem, Corollary and Remark.

## Conventions

* `m × n` matrices are `Matrix (Fin m) (Fin n) ℝ`, `ℝ^n` is `Fin n → ℝ`, and the gradient of
  `φ : ℝ^n → ℝ^m` at `x` is `jac φ x` (rows are the components).
* `RankOneConvex f`: `t ↦ f (A + t B)` is convex for every `A` and every `B` of rank one (the
  paper's (i)).
* `QuasiconvexOn Ω f`: `∫_Ω f (A) ≤ ∫_Ω f (A + ∇φ)` for every `A` and every smooth `φ` with
  compact support in `Ω` for which the right side is integrable (the paper's (ii)). The paper says
  the class does not depend on `Ω`; the statements use the open unit cube.
* `sverakF ε k (X) = f (P X) + ε |X|² + ε |X|⁴ + k |X − P X|²` (the paper's (5)), with `P` the
  orthogonal projection onto `L = {(r 0; 0 s; t t)}` and `f (r 0; 0 s; t t) = −r s t`.
* `topLeft hm hn X`: the upper left `3 × 2` block of `X` (the Corollary's `T X`).

The definitions are copied word for word from `Sverak/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in `Sverak/Solution.lean`.
-/

@[expose] public section

namespace Sverak

-- BEGIN SHARED DEFINITIONS

/-- The derivative matrix of `φ : ℝ^n → ℝ^m` at `x`: the `m × n` matrix with entries
`∂_k φ_i (x)` (rows are the components). -/
noncomputable def jac {m n : ℕ} (φ : (Fin n → ℝ) → Fin m → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i k => fderiv ℝ (fun y => φ y i) x (Pi.single k 1)

/-- Rank-one convexity (the paper's (i)): `t ↦ f (A + t B)` is convex for every matrix `A` and
every matrix `B` of rank one. -/
def RankOneConvex {m n : ℕ} (f : Matrix (Fin m) (Fin n) ℝ → ℝ) : Prop :=
  ∀ A B : Matrix (Fin m) (Fin n) ℝ, B.rank = 1 → ConvexOn ℝ Set.univ fun t : ℝ => f (A + t • B)

/-- The open unit cube `(0, 1)^n`. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo 0 1

/-- Quasiconvexity on a bounded open domain `Ω` (the paper's (ii), after Morrey): for every
matrix `A` and every smooth `φ` with compact support in `Ω`, `∫_Ω f (A) ≤ ∫_Ω f (A + ∇φ)`. The
integral is required to exist: test maps for which `f (A + ∇φ)` is not integrable do not count,
so that a failure of quasiconvexity is witnessed by a genuine integral. -/
def QuasiconvexOn {m n : ℕ} (Ω : Set (Fin n → ℝ)) (f : Matrix (Fin m) (Fin n) ℝ → ℝ) : Prop :=
  ∀ (A : Matrix (Fin m) (Fin n) ℝ) (φ : (Fin n → ℝ) → Fin m → ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      MeasureTheory.IntegrableOn (fun x => f (A + jac φ x)) Ω →
        ∫ _x in Ω, f A ≤ ∫ x in Ω, f (A + jac φ x)

/-- The squared Euclidean norm `|X|² = ∑ X_{ij}²` (the paper's norm on `M^{3×2}`, "the
six-dimensional euclidean space"). -/
def frobSq {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, X i j ^ 2

/-- The orthogonal projection `P` of `M^{3×2}` onto the subspace `L = {(r 0; 0 s; t t)}`. -/
noncomputable def sverakP (X : Matrix (Fin 3) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![X 0 0, 0; 0, X 1 1; (X 2 0 + X 2 1) / 2, (X 2 0 + X 2 1) / 2]

/-- The function `f` of (3), `f (r 0; 0 s; t t) = −r s t`, evaluated at `P X`. -/
noncomputable def sverakf (X : Matrix (Fin 3) (Fin 2) ℝ) : ℝ :=
  -(sverakP X 0 0 * sverakP X 1 1 * sverakP X 2 0)

/-- The integrand (5): `F (X) = f (P X) + ε |X|² + ε |X|⁴ + k |X − P X|²`. -/
noncomputable def sverakF (ε k : ℝ) (X : Matrix (Fin 3) (Fin 2) ℝ) : ℝ :=
  sverakf X + ε * frobSq X + ε * frobSq X ^ 2 + k * frobSq (X - sverakP X)

/-- The map `T : M^{m×n} → M^{3×2}` of the Corollary: the upper left `3 × 2` block. -/
def topLeft {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n) (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin 3) (Fin 2) ℝ :=
  Matrix.of fun i j => X (Fin.castLE hm i) (Fin.castLE hn j)

-- END SHARED DEFINITIONS

end Sverak

namespace SverakChallenge

open Sverak

/-- **Theorem.** There exist `ε > 0` and `k > 0` such that the function `F` given by (5) is
rank-one convex but is not quasiconvex. -/
theorem theorem_main :
    ∃ ε > 0, ∃ k > 0, RankOneConvex (sverakF ε k) ∧ ¬ QuasiconvexOn (unitCube 2) (sverakF ε k) := by
  sorry

/-- **Corollary.** Let `n ≥ 2` and `m ≥ 3`, and `F̃ (X) = F (T X)` with `F` the function of the
Theorem and `T X` the upper left `3 × 2` block of `X`. Then `F̃` is rank-one convex but is not
quasiconvex. -/
theorem corollary :
    ∃ ε > 0, ∃ k > 0, ∀ {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n),
      RankOneConvex (fun X : Matrix (Fin m) (Fin n) ℝ => sverakF ε k (topLeft hm hn X)) ∧
        ¬ QuasiconvexOn (unitCube n)
          (fun X : Matrix (Fin m) (Fin n) ℝ => sverakF ε k (topLeft hm hn X)) := by
  sorry

/-- **Remark.** `F` is a polynomial of degree four in the entries of the matrix (for `ε ≠ 0`). -/
theorem remark_polynomial {ε : ℝ} (hε : ε ≠ 0) (k : ℝ) :
    ∃ P : MvPolynomial (Fin 3 × Fin 2) ℝ, P.totalDegree = 4 ∧
      ∀ X, sverakF ε k X = MvPolynomial.eval (fun ij => X ij.1 ij.2) P := by
  sorry

end SverakChallenge
