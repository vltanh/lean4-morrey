module

public import Cassese.Defs
public import Sverak.Cube
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Cassese's definitions and Šverák's

The two papers state the notions in slightly different forms (each paper's statements are in its
own terms: `Sverak.Defs`, `Cassese.Defs`).

* Rank-one convexity. Šverák (i): `t ↦ f (A + t B)` is convex for rank-one `B`. Cassese,
  Definition 2.2: `t ↦ f (t A + (1 − t) B)` is convex on `[0, 1]` whenever `rank (A − B) = 1`.
  `rankOneConvex_iff` proves them equivalent.
* Quasiconvexity. Šverák (ii): `Sverak.QuasiconvexOn Ω f`, smooth test maps with compact support
  in `Ω`. Cassese, Definition 2.1: `QuasiconvexAt f A`, Lipschitz test maps on `[0, 1]^m`
  vanishing on the boundary. `not_quasiconvexAt_of_smooth` turns a smooth compactly supported
  witness in the unit cube into a failure of `QuasiconvexAt`, and
  `quasiconvexOn_of_quasiconvexAt` shows that Cassese's notion implies Šverák's on the unit cube.

The derivative matrices `Sverak.jac` and `Cassese.jac`, and the two unit cubes, are the same
definitions (`jac_eq`, `unitCube_eq`).
-/

@[expose] public section

open MeasureTheory

namespace Cassese

variable {d m : ℕ}

theorem jac_eq (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) : jac φ x = Sverak.jac φ x := rfl

theorem unitCube_eq (m : ℕ) : unitCube m = Sverak.unitCube m := rfl

/-- Šverák's rank-one convexity (convexity along rank-one lines) is Cassese's (convexity on every
segment whose endpoints differ by a rank-one matrix). -/
theorem rankOneConvex_iff (f : Matrix (Fin d) (Fin m) ℝ → ℝ) :
    Sverak.RankOneConvex f ↔ RankOneConvex f := by
  constructor
  · -- restrict the line through `B` in the direction `A - B` to the segment
    intro hf A B hAB
    have := (hf B (A - B) hAB).subset (Set.subset_univ _) (convex_Icc 0 1)
    convert this using 2 with t
    congr 1
    module
  · -- `t ↦ f (A + t B)` is convex on the segment between any two parameters `x ≠ y`
    intro h A B hB
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    obtain rfl : b = 1 - a := by linarith
    rcases eq_or_ne x y with rfl | hxy
    · simp only [smul_eq_mul]
      rw [show a * x + (1 - a) * x = x by ring, show a * f (A + x • B) + (1 - a) * f (A + x • B) =
        f (A + x • B) by ring]
    · have hr : ((A + x • B) - (A + y • B)).rank = 1 := by
        rw [show (A + x • B) - (A + y • B) = (x - y) • B by module,
          Matrix.rank_smul_of_mem_nonZeroDivisors _
            (mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.2 hxy)), hB]
      have key := (h _ _ hr).2 (x := 1) (y := 0) ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ ha hb
        hab
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero, sub_self, zero_smul, one_smul,
        sub_zero, add_zero, zero_add] at key
      convert key using 2
      module

/-- A smooth map with compact support in the unit cube is Lipschitz and vanishes off the cube. -/
theorem testMap_of_smooth {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ unitCube m) :
    (∃ K, LipschitzWith K φ) ∧ ∀ x ∉ unitCube m, φ x = 0 :=
  ⟨hφ.lipschitzWith_of_hasCompactSupport hc (by simp), fun _ hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hs h')⟩

/-- A smooth map with compact support in the open unit cube is a test map of
`QuasiconvexAt`: it is Lipschitz and vanishes outside the cube, and for continuous `f` the integral
exists. So a smooth witness refutes quasiconvexity at `A` in Cassese's sense. -/
theorem not_quasiconvexAt_of_smooth {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    {A : Matrix (Fin d) (Fin m) ℝ} {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ unitCube m) (hlt : ∫ x in unitCube m, f (A + jac φ x) < f A) :
    ¬ QuasiconvexAt f A := by
  intro h
  obtain ⟨⟨K, hK⟩, h0⟩ := testMap_of_smooth hφ hc hs
  exact (h φ K hK h0 (Sverak.gen_integrableOn_unitCube
    (Sverak.gen_continuous_comp_jac hf A hφ))).not_gt hlt

/-- Quasiconvexity at every matrix in Cassese's sense implies quasiconvexity on the unit cube in
Šverák's sense. -/
theorem quasiconvexOn_of_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (h : Quasiconvex f) : Sverak.QuasiconvexOn (Sverak.unitCube m) f := by
  intro A φ hφ hc hs hint
  obtain ⟨⟨K, hK⟩, h0⟩ := testMap_of_smooth hφ hc hs
  have key : f A ≤ ∫ x in Sverak.unitCube m, f (A + Sverak.jac φ x) := h A φ K hK h0 hint
  simpa [Measure.real, Sverak.volume_unitCube] using key

end Cassese
