module

public import Sverak.Theorem

/-!
# Solution

The statements of `Sverak/Challenge.lean`, word for word, proved from the library.
-/

@[expose] public section

namespace SverakChallenge

open Sverak

theorem theorem_main :
    ∃ ε > 0, ∃ k > 0, RankOneConvex (sverakF ε k) ∧ ¬ QuasiconvexOn (unitCube 2) (sverakF ε k) :=
  Sverak.theorem_main

theorem corollary :
    ∃ ε > 0, ∃ k > 0, ∀ {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n),
      RankOneConvex (fun X : Matrix (Fin m) (Fin n) ℝ => sverakF ε k (topLeft hm hn X)) ∧
        ¬ QuasiconvexOn (unitCube n)
          (fun X : Matrix (Fin m) (Fin n) ℝ => sverakF ε k (topLeft hm hn X)) :=
  Sverak.corollary

theorem remark_polynomial {ε : ℝ} (hε : ε ≠ 0) (k : ℝ) :
    ∃ P : MvPolynomial (Fin 3 × Fin 2) ℝ, P.totalDegree = 4 ∧
      ∀ X, sverakF ε k X = MvPolynomial.eval (fun ij => X ij.1 ij.2) P :=
  Sverak.remark_polynomial hε k

end SverakChallenge
