module

public import Morrey.Pedregal.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Section 1: the statements of Theorems 1.1 and 1.2

The paper's main results, as propositions. **They are not proved here.** Theorem 1.1 (2) and
Theorem 1.2 are the two-dimensional, two-component case of Morrey's problem, which is open; the
paper's proof of Theorem 1.1 fails at Corollary 7.2 (`Pedregal.corollary7_2_false`), and the
formalization neither proves nor refutes them. What the paper's argument does establish is
`Pedregal.theorem1_1_of_nonempty`.

* `RankOneConvex ψ`: `ψ (θ F₁ + (1 − θ) F₀) ≤ θ ψ F₁ + (1 − θ) ψ F₀` for `θ ∈ [0, 1]` whenever
  `F₁ − F₀` has rank one.
* `Quasiconvex ψ`: `|D| ψ F ≤ ∫_D ψ (F + ∇φ)` for every bounded open `D ⊆ ℝ²` with `|∂D| = 0`,
  every matrix `F` and every Lipschitz `φ : ℝ² → ℝ²` vanishing outside `D` (that is, `φ` in
  `W^{1,∞}_0(D; ℝ²)`, extended by `0`); `∇φ` is the derivative, defined almost everywhere.
* `Theorem1_1_part1`, `Theorem1_1_part2`, `Theorem1_2`.

Reading. Theorem 1.2 takes "an arbitrary function" `ψ`; the integral in (2) needs `ψ` measurable,
and the paper's Introduction works with continuous integrands, so `ψ` is continuous here.
"Rank one" in (1) is rank exactly one, as in the paper; rank at most one gives the same notion.
-/

@[expose] public section

open MeasureTheory

namespace Pedregal

/-- The matrix whose rows are the derivatives of the two components of `φ : ℝ² → ℝ²` at `x`. -/
noncomputable def jacobian (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i k => fderiv ℝ (fun y => φ y i) x (Pi.single k 1)

/-- Rank-one convexity of `ψ : ℝ^{2×2} → ℝ`. -/
def RankOneConvex (ψ : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ (F₀ F₁ : Matrix (Fin 2) (Fin 2) ℝ) (θ : ℝ), (F₁ - F₀).rank = 1 → 0 ≤ θ → θ ≤ 1 →
    ψ (θ • F₁ + (1 - θ) • F₀) ≤ θ * ψ F₁ + (1 - θ) * ψ F₀

/-- Quasiconvexity of `ψ : ℝ^{2×2} → ℝ` (Theorem 1.2 (2)). -/
def Quasiconvex (ψ : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ (D : Set (Fin 2 → ℝ)), IsOpen D → Bornology.IsBounded D → volume (frontier D) = 0 →
    ∀ (F : Matrix (Fin 2) (Fin 2) ℝ) (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (K : NNReal),
      LipschitzWith K φ → (∀ x ∉ D, φ x = 0) →
        (volume D).toReal * ψ F ≤ ∫ x in D, ψ (F + jacobian φ x)

/-- **Theorem 1.1 (1)** (`objetivo`), as a proposition: for every `l` and every `u, v ∈ ℙ_l`, the
gradient measure `ν` of `(u, v)` is a laminate. **Not proved**: see the module docstring. -/
def Theorem1_1_part1 : Prop :=
  ∀ l : ℕ, 1 ≤ l → ∀ u v : (Fin 2 → ℝ) → ℝ, u ∈ PL l → v ∈ PL l → IsLaminate (gradMeasure l u v)

/-- **Theorem 1.1 (2)** (`objetivo`), as a proposition: rank-one convexity implies quasiconvexity
for two-dimensional, two-component maps. **Not proved**: this is Morrey's problem for `2 × 2`
matrices, which is open. -/
def Theorem1_1_part2 : Prop :=
  ∀ ψ : Matrix (Fin 2) (Fin 2) ℝ → ℝ, Continuous ψ → RankOneConvex ψ → Quasiconvex ψ

/-- **Theorem 1.2** (`thm:intro`, unlabelled in the paper), as a proposition: for continuous `ψ`,
rank-one convexity and quasiconvexity are equivalent. **Not proved.** -/
def Theorem1_2 : Prop :=
  ∀ ψ : Matrix (Fin 2) (Fin 2) ℝ → ℝ, Continuous ψ → (RankOneConvex ψ ↔ Quasiconvex ψ)

end Pedregal
