module

public import Sverak.Lemma2
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Šverák 1992: the Theorem, the Corollary and the Remark

* `theorem_main` (`sv-theorem`): there exist `ε > 0` and `k > 0` such that `F = sverakF ε k`
  is rank-one convex but not quasiconvex.
* `corollary` (`sv-corollary`): for `n ≥ 2` and `m ≥ 3`, `F̃ (X) = F (T X)`, with `T X` the upper
  left `3 × 2` block of `X ∈ M^{m×n}`, is rank-one convex but not quasiconvex.
* `remark_polynomial` (`sv-remark`): `F` is a polynomial of degree four.
-/

@[expose] public section

open Morrey

namespace Sverak

/-- **Theorem** (`sv-theorem`). There exist `ε > 0` and `k > 0` such that the function `F` given
by (5) is rank-one convex but is not quasiconvex. -/
theorem theorem_main :
    ∃ ε > 0, ∃ k > 0, RankOneConvex (sverakF ε k) ∧ ¬ QuasiconvexOn (unitCube 2) (sverakF ε k) := by
  sorry

/-- **Theorem** (`sv-theorem`), in the form of Cassese's Definition 2.1: by (11) the same `F` fails
to be quasiconvex at `A = 0`. -/
theorem theorem_main_at_zero :
    ∃ ε > 0, ∃ k > 0, RankOneConvex (sverakF ε k) ∧ ¬ QuasiconvexAt (sverakF ε k) 0 := by
  sorry

/-- The map `T : M^{m×n} → M^{3×2}` of the Corollary: the upper left `3 × 2` block. -/
def topLeft {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n) (X : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin 3) (Fin 2) ℝ :=
  Matrix.of fun i j => X (Fin.castLE hm i) (Fin.castLE hn j)

/-- **Corollary** (`sv-corollary`). Let `n ≥ 2` and `m ≥ 3`, and `F̃ (X) = F (T X)` with `F` the
function of the Theorem and `T X` the upper left `3 × 2` block of `X`. Then `F̃` is rank-one convex
but is not quasiconvex. -/
theorem corollary :
    ∃ ε > 0, ∃ k > 0, ∀ {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n),
      RankOneConvex (fun X : Matrix (Fin m) (Fin n) ℝ => sverakF ε k (topLeft hm hn X)) ∧
        ¬ QuasiconvexOn (unitCube n)
          (fun X : Matrix (Fin m) (Fin n) ℝ => sverakF ε k (topLeft hm hn X)) := by
  sorry

/-- **Remark** (`sv-remark`). `F` is a polynomial of degree four in the entries of the matrix
(for `ε ≠ 0`). -/
theorem remark_polynomial {ε : ℝ} (hε : ε ≠ 0) (k : ℝ) :
    ∃ P : MvPolynomial (Fin 3 × Fin 2) ℝ, P.totalDegree = 4 ∧
      ∀ X, sverakF ε k X = MvPolynomial.eval (fun ij => X ij.1 ij.2) P := by
  sorry

end Sverak
