module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Rank-one convexity and quasiconvexity

The standard notions of the vectorial calculus of variations, in the form of the textbooks
(Dacorogna, *Direct methods in the calculus of variations*, 2008, Chapter 5; Rindler, *Calculus of
variations*, 2018, Chapter 5), for integrands `f : ℝ^{d×m} → ℝ`:

* `grad φ x`: the derivative matrix of `φ : ℝ^m → ℝ^d` (rows are the components);
* `RankOneConvex f`: `t ↦ f (A + t B)` is convex for every `A` and every `B` of rank one;
  `RankOneAffine f`: `f` and `−f` are rank-one convex;
* `QuasiconvexAtOn Ω f A`: `|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)` for every Lipschitz `φ` vanishing outside
  `Ω` (that is, `φ ∈ W^{1,∞}_0 (Ω, ℝ^d)` extended by `0`) for which the integral exists;
  `QuasiconvexAtPeriodic f A`: the same on the unit cube for `ℤ^m`-periodic Lipschitz `φ`
  (`φ ∈ W^{1,∞}_per (𝕋^m, ℝ^d)`);
* `Quasiconvex f`: quasiconvexity on the unit cube at every matrix;
* `IsLocallyBounded f`, and `qcEnvelope f`, the largest quasiconvex minorant (in `EReal`,
  `⊥` when there is none).
-/

@[expose] public section

open MeasureTheory

namespace CalculusOfVariations

variable {d m : ℕ}

/-- The derivative matrix of `φ : ℝ^m → ℝ^d` at `x` (rows are the components). -/
noncomputable def grad (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  Matrix.of fun i k => fderiv ℝ (fun y => φ y i) x (Pi.single k 1)

/-- The open unit cube `(0, 1)^m`. -/
def unitCube (m : ℕ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo 0 1

/-- The open Euclidean unit ball of `ℝ^m`. -/
def unitBall (m : ℕ) : Set (Fin m → ℝ) :=
  {x | ∑ i, x i ^ 2 < 1}

/-- Rank-one convexity: `t ↦ f (A + t B)` is convex for every `A` and every `B` of rank one. -/
def RankOneConvex (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A B : Matrix (Fin d) (Fin m) ℝ, B.rank = 1 → ConvexOn ℝ Set.univ fun t : ℝ => f (A + t • B)

/-- Rank-one affinity: `f` and `−f` are rank-one convex. -/
def RankOneAffine (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  RankOneConvex f ∧ RankOneConvex (-f)

/-- `f` is bounded on a neighbourhood of every matrix. -/
def IsLocallyBounded (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A, ∃ U ∈ nhds A, ∃ C : ℝ, ∀ B ∈ U, |f B| ≤ C

/-- Quasiconvexity at `A` on the domain `Ω`: `|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)` for every Lipschitz `φ`
vanishing outside `Ω` for which the integral exists. -/
def QuasiconvexAtOn (Ω : Set (Fin m → ℝ)) (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) : Prop :=
  ∀ (φ : (Fin m → ℝ) → Fin d → ℝ) (K : NNReal), LipschitzWith K φ → (∀ x ∉ Ω, φ x = 0) →
    IntegrableOn (fun x => f (A + grad φ x)) Ω →
      (volume Ω).toReal * f A ≤ ∫ x in Ω, f (A + grad φ x)

/-- Quasiconvexity at `A` with periodic test maps: `f (A) ≤ ∫_{(0,1)^m} f (A + ∇φ)` for every
`ℤ^m`-periodic Lipschitz `φ` for which the integral exists. -/
def QuasiconvexAtPeriodic (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    Prop :=
  ∀ (φ : (Fin m → ℝ) → Fin d → ℝ) (K : NNReal), LipschitzWith K φ →
    (∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x) →
    IntegrableOn (fun x => f (A + grad φ x)) (unitCube m) →
      f A ≤ ∫ x in unitCube m, f (A + grad φ x)

/-- Quasiconvexity: quasiconvexity on the unit cube at every matrix. -/
def Quasiconvex (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A, QuasiconvexAtOn (unitCube m) f A

/-- The quasiconvex envelope: the supremum of `g (A)` over the quasiconvex, lower semicontinuous,
locally bounded `g ≤ f` (`⊥` when there is none). -/
noncomputable def qcEnvelope (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    EReal :=
  ⨆ (g : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (_ : LowerSemicontinuous g ∧ IsLocallyBounded g ∧ Quasiconvex g ∧ ∀ B, g B ≤ f B),
    (g A : EReal)

end CalculusOfVariations
