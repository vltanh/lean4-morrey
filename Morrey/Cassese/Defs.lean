module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Cassese, arXiv:2608.03488v3: the definitions

G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*, arXiv:2608.03488v3 (16 September
2026). The paper writes integrands `f : ℝ^{d×m} → ℝ` and maps `u : [0, 1]^m → ℝ^d`; here `d × m`
matrices are `Matrix (Fin d) (Fin m) ℝ`, `ℝ^m` is `Fin m → ℝ`, and the gradient of `φ` at `x` is
`jac φ x`, whose rows are the derivatives of the components.

* `QuasiconvexAt` (Definition 2.1, `Quasiconvexity`), `Quasiconvex`, `NowhereQuasiconvex`.
* `RankOneConvex` (Definition 2.2, `Rank-one convexity`): convexity on segments whose endpoints
  differ by a rank-one matrix.
* `IsPHomogeneous`: `f (t A) = |t|^p f (A)` for every real `t` (Section 1.3).
* `IsHomogeneousPolynomial`: a homogeneous polynomial in the entries.
* `unitCube`: the open cube `(0, 1)^m`; a Lipschitz map on `[0, 1]^m` vanishing on the boundary,
  extended by `0`, is a Lipschitz map on `ℝ^m` vanishing outside the open cube.

Everything between the markers below is copied word for word into `Cassese/Challenge.lean` by
`scripts/sync_challenge_defs.py`.
-/

@[expose] public section

namespace Cassese

-- BEGIN SHARED DEFINITIONS

/-- The derivative matrix of `φ : ℝ^m → ℝ^d` at `x`: the `d × m` matrix with entries
`∂_k φ_i (x)` (rows are the components). For a Lipschitz `φ` it is the gradient almost
everywhere (Rademacher's theorem); elsewhere `fderiv` is `0`. -/
noncomputable def jac {d m : ℕ} (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  Matrix.of fun i k => fderiv ℝ (fun y => φ y i) x (Pi.single k 1)

/-- The open unit cube `(0, 1)^m`. -/
def unitCube (m : ℕ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo 0 1

/-- Quasiconvexity at a matrix `A` (Definition 2.1): for every Lipschitz `φ : [0, 1]^m → ℝ^d`
vanishing on the boundary (extended by `0` outside the cube),
`f (A) ≤ ∫_{[0,1]^m} f (A + ∇φ)`. The integral is required to exist: test maps for which
`f (A + ∇φ)` is not integrable do not count, so that a failure of quasiconvexity is witnessed by a
genuine integral. -/
def QuasiconvexAt {d m : ℕ} (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    Prop :=
  ∀ (φ : (Fin m → ℝ) → Fin d → ℝ) (K : NNReal), LipschitzWith K φ →
    (∀ x ∉ unitCube m, φ x = 0) →
      MeasureTheory.IntegrableOn (fun x => f (A + jac φ x)) (unitCube m) →
        f A ≤ ∫ x in unitCube m, f (A + jac φ x)

/-- Quasiconvexity (Definition 2.1): quasiconvexity at every matrix. -/
def Quasiconvex {d m : ℕ} (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A, QuasiconvexAt f A

/-- `f` is quasiconvex at no matrix. -/
def NowhereQuasiconvex {d m : ℕ} (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A, ¬ QuasiconvexAt f A

/-- Rank-one convexity (Definition 2.2): for any two matrices `A`, `B` with `rank (A − B) = 1`,
`t ↦ f (t A + (1 − t) B)` is convex on `[0, 1]`. -/
def RankOneConvex {d m : ℕ} (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ A B : Matrix (Fin d) (Fin m) ℝ, (A - B).rank = 1 →
    ConvexOn ℝ (Set.Icc 0 1) fun t : ℝ => f (t • A + (1 - t) • B)

/-- `p`-homogeneity (Section 1.3): `f (t A) = |t|^p f (A)` for every real `t`. -/
def IsPHomogeneous {d m : ℕ} (p : ℝ) (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ (t : ℝ) (A : Matrix (Fin d) (Fin m) ℝ), f (t • A) = |t| ^ p * f A

/-- `f` is a homogeneous polynomial of degree `n` in the entries of the matrix. -/
def IsHomogeneousPolynomial {d m : ℕ} (n : ℕ) (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin d × Fin m) ℝ, P.IsHomogeneous n ∧
    ∀ A, f A = MvPolynomial.eval (fun ij => A ij.1 ij.2) P

-- END SHARED DEFINITIONS

end Cassese
