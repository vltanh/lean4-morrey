module

public import Basic.CalculusOfVariations.Basic

/-!
# Kirchheim–Kristensen: rank-one convex functions homogeneous of degree one

B. Kirchheim and J. Kristensen, *On rank-one convex functions that are homogeneous of degree
one*, Arch. Rational Mech. Anal. 221 (2016). Cassese quotes their theorem as Theorem 1.1, for
context only: no proof of Cassese's paper uses it. It is stated here as a proposition, with no
proof, so that every numbered result of the paper has a statement.
-/

@[expose] public section

namespace External.KirchheimKristensen

open CalculusOfVariations

/-- **Theorem 1.1** (`thm:KK`) of Cassese, citing Kirchheim–Kristensen (2016): a continuous
rank-one convex integrand `f : ℝ^{d×m} → ℝ` that is positively `1`-homogeneous has a subgradient
at each matrix of rank at most one: there is `G` with `f (A) + ⟨G, B − A⟩ ≤ f (B)` for every `B`
(a global affine supporting hyperplane of the epigraph at `A`). Context only; not a hypothesis of
any statement. -/
def Theorem1_1 : Prop :=
  ∀ (d m : ℕ) (f : Matrix (Fin d) (Fin m) ℝ → ℝ), Continuous f → RankOneConvex f →
    (∀ t : ℝ, 0 < t → ∀ A, f (t • A) = t * f A) →
      ∀ A : Matrix (Fin d) (Fin m) ℝ, A.rank ≤ 1 →
        ∃ G : Matrix (Fin d) (Fin m) ℝ, ∀ B, f A + ∑ i, ∑ j, G i j * (B i j - A i j) ≤ f B

end External.KirchheimKristensen
