module

public import Sverak.Defs
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The unit cube and smooth test maps

Facts that the paper uses without comment: the unit cube has volume `1`, and for a continuous `f`
and a smooth `φ` the integrand `x ↦ f (A + Dφ (x))` is continuous, hence integrable on the cube.
-/

@[expose] public section

open MeasureTheory

namespace Sverak

variable {m n : ℕ}

/-- The volume of the unit cube is `1`. -/
theorem volume_unitCube : volume (unitCube n) = 1 := by
  simp [unitCube, Real.volume_pi_Ioo]

/-- For a smooth `φ` and a continuous `f`, the integrand `x ↦ f (A + ∇φ (x))` is continuous. -/
theorem gen_continuous_comp_jac {f : Matrix (Fin m) (Fin n) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin m) (Fin n) ℝ) {φ : (Fin n → ℝ) → Fin m → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : Continuous fun x => f (A + jac φ x) := by
  refine hf.comp (continuous_const.add ?_)
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have hi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => φ y i := (contDiff_pi.1 hφ) i
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

/-- A continuous function is integrable on the unit cube. -/
theorem gen_integrableOn_unitCube {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    IntegrableOn g (unitCube n) :=
  (hg.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self)

end Sverak
