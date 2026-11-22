module

public import Morrey.Pedregal.Introduction
public import Morrey.Pedregal.Triangulation
public import Morrey.Common.Basic.CalculusOfVariations.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Tactic

/-!
# Jensen's inequality for Pedregal's finite laminates

Universal algebraic bridges from finite-order lamination to translated discrete Jensen
inequalities. The existence of laminates at arbitrary levels remains a hypothesis.
-/

@[expose] public section

namespace Pedregal

/-- The segment and line definitions of rank-one convexity agree. -/
theorem cov_rankOneConvex_iff (f : Matrix (Fin 2) (Fin 2) ℝ → ℝ) :
    CalculusOfVariations.RankOneConvex f ↔ RankOneConvex f := by
  constructor
  · intro h F₀ F₁ θ hR hθ0 hθ1
    have key := (h F₀ (F₁ - F₀) hR).2
      (x := 1) (y := 0) (by trivial) (by trivial) hθ0 (sub_nonneg.2 hθ1)
      (by ring)
    have e1 : F₀ + (1 : ℝ) • (F₁ - F₀) = F₁ := by module
    have e0 : F₀ + (0 : ℝ) • (F₁ - F₀) = F₀ := by simp
    have eθ : F₀ + θ • (F₁ - F₀) = θ • F₁ + (1 - θ) • F₀ := by module
    simpa only [smul_eq_mul, mul_one, mul_zero, add_zero, e1, e0, eθ] using key
  · intro h A B hB
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    obtain rfl : b = 1 - a := by linarith
    rcases eq_or_ne x y with rfl | hxy
    · simp only [smul_eq_mul]
      rw [show a * x + (1 - a) * x = x by ring,
        show a * f (A + x • B) + (1 - a) * f (A + x • B) = f (A + x • B) by ring]
    · have hr : ((A + x • B) - (A + y • B)).rank = 1 := by
        rw [show (A + x • B) - (A + y • B) = (x - y) • B by module,
          Matrix.rank_smul_of_mem_nonZeroDivisors _
            (mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.2 hxy)), hB]
      have key := h (A + y • B) (A + x • B) a hr ha (by linarith)
      convert key using 2
      module

private theorem jensen_eq_zero_of_rank_eq_zero {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : A.rank = 0) : A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun F => F (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply] using this

/-- The zero-rank case is harmless in the splitting definition. -/
theorem RankOneConvex.segment_le {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hf : RankOneConvex f) {B C : Matrix (Fin 2) (Fin 2) ℝ}
    (hBC : (B - C).rank ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    f (θ • B + (1 - θ) • C) ≤ θ * f B + (1 - θ) * f C := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hBC with h0 | h1
  · obtain rfl : B = C := sub_eq_zero.1 (jensen_eq_zero_of_rank_eq_zero h0)
    rw [show θ • C + (1 - θ) • C = C by module]
    nlinarith
  · exact hf C B θ h1 hθ0 hθ1

/-- Translation of the integrand preserves rank-one convexity. -/
theorem RankOneConvex.translate {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hf : RankOneConvex f) (F : Matrix (Fin 2) (Fin 2) ℝ) :
    RankOneConvex (fun A => f (F + A)) := by
  intro A B θ hAB hθ0 hθ1
  have hr : ((F + B) - (F + A)).rank = 1 := by simpa using hAB
  have key := hf (F + A) (F + B) θ hr hθ0 hθ1
  convert key using 2
  module

/-- Integration against a finite signed measure, as an additive map in its weights. -/
noncomputable def weightedEval (f : Matrix (Fin 2) (Fin 2) ℝ → ℝ) :
    (Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ) →+ ℝ :=
  Finsupp.liftAddHom fun A =>
    { toFun := fun c => c * f A
      map_zero' := by simp
      map_add' := fun c d => add_mul c d (f A) }

/-- The finite-measure barycenter, as an additive map in the weights. -/
noncomputable def discreteBarycenter :
    (Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ) →+ Matrix (Fin 2) (Fin 2) ℝ :=
  Finsupp.liftAddHom fun A =>
    { toFun := fun c => c • A
      map_zero' := by simp
      map_add' := fun c d => add_smul c d A }

@[simp] theorem weightedEval_single (f : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) :
    weightedEval f (Finsupp.single A c) = c * f A := by
  change (Finsupp.single A c).sum (fun B d => d * f B) = c * f A
  simp

@[simp] theorem discreteBarycenter_single (A : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) :
    discreteBarycenter (Finsupp.single A c) = c • A := by
  change (Finsupp.single A c).sum (fun B d => d • B) = c • A
  simp

/-- Every finite-order laminate has total mass one. -/
theorem IsLaminate.mass {μ : Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ}
    (hμ : IsLaminate μ) : weightedEval (fun _ => 1) μ = 1 := by
  induction hμ with
  | dirac A => simp
  | @split μ A B C c θ hμ hc hcμ hθ0 hθ1 hA hBC ih =>
    simp only [map_add, map_sub, weightedEval_single]
    rw [ih]
    ring

/-- Every finite-order laminate has nonnegative weights, including at repeated atoms. -/
theorem IsLaminate.nonneg {μ : Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ}
    (hμ : IsLaminate μ) : ∀ X, 0 ≤ μ X := by
  induction hμ with
  | dirac A =>
    intro X
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  | @split μ A B C c θ hμ hc hcμ hθ0 hθ1 hA hBC ih =>
    intro X
    have hres : 0 ≤ μ X - (Finsupp.single A c) X := by
      by_cases h : A = X
      · subst X
        simpa using sub_nonneg.2 hcμ
      · simpa [Finsupp.single_apply, h] using ih X
    have hB : 0 ≤ (Finsupp.single B (θ * c)) X := by
      simp only [Finsupp.single_apply]
      split_ifs <;> positivity
    have hC : 0 ≤ (Finsupp.single C ((1 - θ) * c)) X := by
      have : 0 ≤ 1 - θ := sub_nonneg.2 hθ1
      simp only [Finsupp.single_apply]
      split_ifs <;> positivity
    simpa only [Finsupp.add_apply, Finsupp.sub_apply] using add_nonneg (add_nonneg hres hB) hC

/-- Jensen's inequality holds for every finite-order laminate and every rank-one-convex
integrand. No continuity or grid-size hypothesis is needed. -/
theorem IsLaminate.jensen {μ : Matrix (Fin 2) (Fin 2) ℝ →₀ ℝ}
    (hμ : IsLaminate μ) {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hf : RankOneConvex f) :
    f (discreteBarycenter μ) ≤ weightedEval f μ := by
  induction hμ with
  | dirac A => simp
  | @split μ A B C c θ hμ hc hcμ hθ0 hθ1 hA hBC ih =>
    have hbary : discreteBarycenter
        (μ - Finsupp.single A c + Finsupp.single B (θ * c) +
          Finsupp.single C ((1 - θ) * c)) = discreteBarycenter μ := by
      simp only [map_add, map_sub, discreteBarycenter_single]
      rw [hA]
      module
    rw [hbary]
    simp only [map_add, map_sub, weightedEval_single]
    have hsplit := hf.segment_le hBC hθ0 hθ1
    rw [← hA] at hsplit
    have hscaled := mul_le_mul_of_nonneg_left hsplit hc
    nlinarith

/-- The barycenter of each periodic dyadic gradient measure is zero, at every level. -/
theorem discreteBarycenter_gradMeasure {l : ℕ} {u v : (Fin 2 → ℝ) → ℝ}
    (hu : u ∈ PL l) (hv : v ∈ PL l) : discreteBarycenter (gradMeasure l u v) = 0 := by
  classical
  simp only [gradMeasure, map_sum, discreteBarycenter_single]
  ext i j
  fin_cases i
  · simpa [gradMat] using congrFun (equation5_13 hu) j
  · simpa [gradMat] using congrFun (equation5_13 hv) j

@[simp] theorem weightedEval_gradMeasure (l : ℕ) (u v : (Fin 2 → ℝ) → ℝ)
    (f : Matrix (Fin 2) (Fin 2) ℝ → ℝ) :
    weightedEval f (gradMeasure l u v) =
      ∑ s : Tri l, (1 / 2 ^ (2 * l + 1) : ℝ) * f (gradMat l u v s) := by
  simp only [gradMeasure, map_sum, weightedEval_single]

/-- A laminate certificate implies the translated discrete Jensen inequality at any base.
The laminate existence hypothesis is the unresolved part at general levels. -/
theorem discrete_jensen_of_isLaminate {l : ℕ} {u v : (Fin 2 → ℝ) → ℝ}
    (hu : u ∈ PL l) (hv : v ∈ PL l) (hμ : IsLaminate (gradMeasure l u v))
    {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hf : RankOneConvex f)
    (F : Matrix (Fin 2) (Fin 2) ℝ) :
    f F ≤ ∑ s : Tri l, (1 / 2 ^ (2 * l + 1) : ℝ) * f (F + gradMat l u v s) := by
  have h := hμ.jensen (hf.translate F)
  simpa only [discreteBarycenter_gradMeasure hu hv, add_zero, weightedEval_gradMeasure] using h

/-- The all-level lamination hypothesis supplies all discrete translated Jensen inequalities.
This leaves interpolation/energy convergence to reach the full analytic theorem. -/
theorem discrete_jensen_of_theorem1_1_part1 (h : Theorem1_1_part1)
    {l : ℕ} (hl : 1 ≤ l) {u v : (Fin 2 → ℝ) → ℝ} (hu : u ∈ PL l) (hv : v ∈ PL l)
    {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hf : RankOneConvex f)
    (F : Matrix (Fin 2) (Fin 2) ℝ) :
    f F ≤ ∑ s : Tri l, (1 / 2 ^ (2 * l + 1) : ℝ) * f (F + gradMat l u v s) :=
  discrete_jensen_of_isLaminate hu hv (h l hl u v hu hv) hf F

end Pedregal
