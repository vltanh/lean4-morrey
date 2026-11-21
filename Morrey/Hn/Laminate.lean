module

public import Morrey.Hn.Mold

/-!
# `(H_n)`-conditions with rank-one directions are laminates

A mold fed with nonnegative weights and matrices whose decomposition directions all have rank at
most one describes, in its top-to-bottom form (Definition 3.1), a sequence of splittings of the
Dirac mass at its final mass point into its leaf measure along rank-one segments. So the leaf
measure is a laminate of finite order. This is the mechanism behind Proposition 6.1 ("fixed
points for such a map are identified with joint `(H_n)`-conditions whose decomposition
directions are parallel, i.e. with laminates", Section 1).
-/

@[expose] public section

namespace Morrey

namespace Mold

variable {ι : Type}

/-- The measure of the leaves of a mold, for weights `t` and matrices `A`: mass `t i` at `A i`
for each leaf `i`. -/
noncomputable def leafMeasure (t : ι → ℝ) (A : ι → Matrix (Fin 2) (Fin 2) ℝ) :
    Mold ι → (Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ)
  | leaf i => Finsupp.single (A i) (t i)
  | node L R => leafMeasure t A L + leafMeasure t A R

/-- The leaf measure of a mold is the sum over its leaves. -/
theorem leafMeasure_eq_sum (t : ι → ℝ) (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (M : Mold ι) :
    M.leafMeasure t A = (M.leaves.map fun i => Finsupp.single (A i) (t i)).sum := by
  sorry

/-- If every decomposition direction of a mold, for nonnegative weights `t` and matrices `A`,
has rank at most one, then splitting the atom at the mold's mass point gives the leaf measure:
whenever `ρ + δ_{point}·weight` is a laminate (for a nonnegative `ρ`), so is
`ρ + leafMeasure`. -/
theorem isLaminate_add_leafMeasure {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i)
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (M : Mold ι)
    (hrank : ∀ p ∈ M.nodes, (p.1.point t A - p.2.point t A).rank ≤ 1)
    {ρ : Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ} (hρ : ∀ X, 0 ≤ ρ X)
    (h : IsLaminate (ρ + Finsupp.single (M.point t A) (M.weight t))) :
    IsLaminate (ρ + M.leafMeasure t A) := by
  sorry

/-- A mold of total weight `1` whose decomposition directions all have rank at most one, for
nonnegative weights, has a laminate as its leaf measure. -/
theorem isLaminate_leafMeasure {t : ι → ℝ} (ht : ∀ i, 0 ≤ t i)
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (M : Mold ι) (hw : M.weight t = 1)
    (hrank : ∀ p ∈ M.nodes, (p.1.point t A - p.2.point t A).rank ≤ 1) :
    IsLaminate (M.leafMeasure t A) := by
  sorry

end Mold

end Morrey
