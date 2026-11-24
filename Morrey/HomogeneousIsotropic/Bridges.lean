module

public import Morrey.HomogeneousIsotropic.Defs
public import CalculusOfVariations.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The notions of the Challenge and those of the package

The statements of `palomar/HomogeneousIsotropic/Challenge.lean` use the definitions of
`Morrey/HomogeneousIsotropic/Defs.lean`: `jac`, `unitSquare`, `IsRankOneConvex`, `IsQuasiconvexAt`,
`IsQuasiconvex`. The proofs of the library use those of the package `CalculusOfVariations`:
`grad`, `unitCube`, `RankOneConvex`, `QuasiconvexAtOn`, `Quasiconvex`. They are the same notions:

* `jac_eq_grad`, `unitSquare_eq_unitCube`, `isRankOneConvex_iff`: by definition;
* `isQuasiconvexAt_iff`, `isQuasiconvex_iff`: the package writes `|Ω| F (A) ≤ ∫_Ω F (A + ∇φ)`, and
  the unit square has volume `1` (`volume_unitSquare`).
-/

@[expose] public section

open MeasureTheory

namespace HomogeneousIsotropic

/-- `jac` is the package's `grad`. -/
theorem jac_eq_grad (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    jac φ x = CalculusOfVariations.grad φ x := rfl

/-- `unitSquare` is the package's `unitCube 2`. -/
theorem unitSquare_eq_unitCube : unitSquare = CalculusOfVariations.unitCube 2 := rfl

/-- The unit square has volume `1`. -/
theorem volume_unitSquare : volume unitSquare = 1 := by
  simp [unitSquare, Real.volume_pi_Ioo]

/-- `IsRankOneConvex` is the package's `RankOneConvex`. -/
theorem isRankOneConvex_iff (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) :
    IsRankOneConvex F ↔ CalculusOfVariations.RankOneConvex F := Iff.rfl

/-- `IsQuasiconvexAt` is the package's `QuasiconvexAtOn` on the unit square. -/
theorem isQuasiconvexAt_iff (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    IsQuasiconvexAt F A ↔
      CalculusOfVariations.QuasiconvexAtOn (CalculusOfVariations.unitCube 2) F A := by
  have hv : (volume (CalculusOfVariations.unitCube 2)).toReal = 1 := by
    rw [← unitSquare_eq_unitCube, volume_unitSquare, ENNReal.toReal_one]
  constructor
  · intro h φ K hφ h0 hI
    rw [hv, one_mul]
    exact h φ K hφ h0 hI
  · intro h φ K hφ h0 hI
    have h' := h φ K hφ h0 hI
    rwa [hv, one_mul] at h'

/-- `IsQuasiconvex` is the package's `Quasiconvex`. -/
theorem isQuasiconvex_iff (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) :
    IsQuasiconvex F ↔ CalculusOfVariations.Quasiconvex F :=
  forall_congr' fun A => isQuasiconvexAt_iff F A

end HomogeneousIsotropic
