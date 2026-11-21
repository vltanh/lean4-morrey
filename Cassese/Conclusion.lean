module

public import Cassese.Toolkit

/-!
# Section 8: the conjecture

Conjecture 1, weaker than the homogeneous Morrey problem, is open; it is stated as a proposition.
-/

@[expose] public section

namespace Cassese

/-- **Conjecture 1** (`cs-conj1`), open: for `p ∈ (1, ∞)`, every `p`-homogeneous rank-one convex
integrand `f : ℝ^{d×d} → ℝ` that is isotropic (`f (U A V) = f (A)` for `U, V ∈ SO (d)`) is
quasiconvex at `0`. -/
def Conjecture1 : Prop :=
  ∀ (p : ℝ), 1 < p → ∀ (d : ℕ) (f : Matrix (Fin d) (Fin d) ℝ → ℝ), IsIntegrand f →
    IsPHomogeneous p f → RankOneConvex f →
    (∀ U ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ, ∀ V ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ,
      ∀ A, f (U * A * V) = f A) →
    QuasiconvexAt f 0

end Cassese
