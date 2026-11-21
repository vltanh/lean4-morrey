module

public import Morrey.Defs

/-!
# Rank-one convexity and quasiconvexity: bridges between the papers' definitions

The papers formalized here state the two notions in slightly different forms.

* Šverák (1992) and the shared `RankOneConvex`: `t ↦ f (A + t B)` is convex for rank-one `B`.
  Cassese (2026, Definition 2.2): `t ↦ f (t A + (1 − t) B)` is convex on `[0, 1]` whenever
  `rank (A − B) = 1`. `rankOneConvex_iff_segment` proves them equivalent.
* Šverák: `QuasiconvexOn Ω f`, smooth test maps with compact support in `Ω`. Cassese:
  `QuasiconvexAt f A`, Lipschitz test maps on `[0, 1]^m` vanishing on the boundary.
  `not_quasiconvexAt_of_smooth` turns a smooth compactly supported witness in the unit cube into a
  failure of `QuasiconvexAt`, and `quasiconvexOn_of_quasiconvexAt` shows that Cassese's notion
  implies Šverák's on the unit cube.
-/

@[expose] public section

open MeasureTheory

namespace Morrey

variable {d m : ℕ}

/-- Šverák's rank-one convexity (convexity along rank-one lines) is Cassese's (convexity on every
segment whose endpoints differ by a rank-one matrix). -/
theorem rankOneConvex_iff_segment (f : Matrix (Fin d) (Fin m) ℝ → ℝ) :
    RankOneConvex f ↔ ∀ A B : Matrix (Fin d) (Fin m) ℝ, (A - B).rank = 1 →
      ConvexOn ℝ (Set.Icc 0 1) fun t : ℝ => f (t • A + (1 - t) • B) := by
  sorry

/-- The volume of the unit cube is `1`. -/
theorem volume_unitCube : volume (unitCube m) = 1 := by
  sorry

/-- A smooth map with compact support in the open unit cube is a test map of
`QuasiconvexAt`: it is Lipschitz and vanishes outside the cube. So a smooth witness refutes
quasiconvexity at `A` in Cassese's sense. -/
theorem not_quasiconvexAt_of_smooth {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    {A : Matrix (Fin d) (Fin m) ℝ} {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ unitCube m) (hlt : ∫ x in unitCube m, f (A + jac φ x) < f A) :
    ¬ QuasiconvexAt f A := by
  sorry

/-- Quasiconvexity at every matrix in Cassese's sense implies quasiconvexity on the unit cube in
Šverák's sense. -/
theorem quasiconvexOn_of_quasiconvexAt {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (h : ∀ A, QuasiconvexAt f A) : QuasiconvexOn (unitCube m) f := by
  sorry

end Morrey
