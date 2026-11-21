module

public import Morrey.Defs
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

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

/-- The volume of the unit cube is `1`. -/
theorem volume_unitCube : volume (unitCube m) = 1 := by
  simp [unitCube, Real.volume_pi_Ioo]

/-- For a smooth `φ` and a continuous `f`, the integrand `x ↦ f (A + ∇φ (x))` is continuous. -/
theorem gen_continuous_comp_jac {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : Continuous fun x => f (A + jac φ x) := by
  refine hf.comp (continuous_const.add ?_)
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have hi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => φ y i := (contDiff_pi.1 hφ) i
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

/-- A continuous function is integrable on the unit cube. -/
theorem gen_integrableOn_unitCube {g : (Fin m → ℝ) → ℝ} (hg : Continuous g) :
    IntegrableOn g (unitCube m) :=
  (hg.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self)

/-- A smooth map with compact support in the unit cube is Lipschitz and vanishes off the cube. -/
theorem gen_testMap {φ : (Fin m → ℝ) → Fin d → ℝ}
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
  obtain ⟨⟨K, hK⟩, h0⟩ := gen_testMap hφ hc hs
  exact (h φ K hK h0 (gen_integrableOn_unitCube (gen_continuous_comp_jac hf A hφ))).not_gt hlt

/-- Quasiconvexity at every matrix in Cassese's sense implies quasiconvexity on the unit cube in
Šverák's sense. -/
theorem quasiconvexOn_of_quasiconvexAt {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (h : ∀ A, QuasiconvexAt f A) : QuasiconvexOn (unitCube m) f := by
  intro A φ hφ hc hs hint
  obtain ⟨⟨K, hK⟩, h0⟩ := gen_testMap hφ hc hs
  simpa [Measure.real, volume_unitCube] using h A φ K hK h0 hint

end Morrey
