module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.Matrix

/-!
# Isotropic homogeneous integrands on `2 × 2` matrices: the definitions

Integrands are functions `F : ℝ^{2×2} → ℝ`, with `ℝ^{2×2}` as `Matrix (Fin 2) (Fin 2) ℝ`.

The definitions that the statements of `palomar/HomogeneousIsotropic/Challenge.lean` use are
between the two marker lines, and are copied word for word into the Challenge by
`scripts/sync_challenge_defs.py`:

* `jac φ x`: the derivative matrix of `φ : ℝ² → ℝ²` (rows are the components); `unitSquare`, the
  open square `(0, 1)²`.
* `IsRankOneConvex F`: `t ↦ F (A + t B)` is convex on `ℝ` for every `A` and every `B` of rank
  one.
* `IsQuasiconvexAt F A`: `F (A) ≤ ∫_{(0,1)²} F (A + ∇φ)` for every Lipschitz `φ` vanishing outside
  the unit square for which the integral exists; `IsQuasiconvex F`: at every matrix.
* `IsIsotropic F`: `F (Q A R) = F (A)` for all rotations `Q, R ∈ SO(2)`.
* `IsPosHomogeneous p F`: `F (c A) = c^p F (A)` for every `c > 0`.
* `polyaffine k K c`: the polyaffine function `A ↦ k + ⟨K, A⟩ + c det A`.
* `HasPolyaffineSupportAt F A₀`: some polyaffine function lies below `F` and equals `F` at `A₀`.
* `Polyconvex F`: `F (A) = g (A, det A)` for a convex `g : ℝ^{2×2} × ℝ → ℝ`.
* `conformalPart A`, `anticonformalPart A`: the complex numbers `z`, `w` with
  `A ζ = z ζ + w ζ̄`, when `ℝ²` is identified with `ℂ`. Then `det A = |z|² − |w|²` and an isotropic
  `F` is a function of `(|z|, |w|)` (both proved in
  `Morrey/HomogeneousIsotropic/Coordinates.lean`). The singular values of `A` are `|z| + |w|` and
  `||z| − |w||`, so that `|z| + |w|` is the operator norm `|A|`; this is not proved here, and the
  definitions below use `|z| + |w|`.
* `burkholderType p c₀ m`: the function `|A|^{p-2} (c₀ |A|² + m det A)`; `burkholder p`: the
  Burkholder function `(|z| − (p − 1) |w|) (|z| + |w|)^{p−1}`, in the form used for `1 < p ≤ 2`.
* `reflection`: the matrix `J = diag (1, −1)`.
* `multiplier p H m t`: the determinant coefficient of the support of Theorem 1.2.

The library's proofs use the rank-one convexity and the quasiconvexity of the package
`CalculusOfVariations`; `Morrey/HomogeneousIsotropic/Bridges.lean` proves that they are the
notions above. After the shared block:

* `ofComplex z w`: the matrix with conformal part `z` and anticonformal part `w`.
* `profile F x y = F (ofComplex x y)` for real `x`, `y`: the *profile* of an isotropic `F`.
* `IsProfile p Φ`: the two properties of the profile of an isotropic, positively `p`-homogeneous,
  rank-one convex integrand that the proofs use: homogeneity, and convexity along the images of
  the rank-one lines `τ ↦ (z + τ α, w + τ β)`, `|α| = |β|`.
-/

@[expose] public section

namespace HomogeneousIsotropic

-- BEGIN SHARED DEFINITIONS

/-- The derivative matrix of `φ : ℝ² → ℝ²` at `x`: the matrix with the entries `∂_k φ_i (x)`
(rows are the components). For a Lipschitz `φ` it is the gradient almost everywhere; an entry is
`0` where `φ_i` is not differentiable. -/
noncomputable def jac (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i k => fderiv ℝ (fun y => φ y i) x (Pi.single k 1)

/-- The open unit square `(0, 1)²`. -/
def unitSquare : Set (Fin 2 → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo 0 1

/-- Rank-one convexity: `t ↦ F (A + t B)` is convex on `ℝ` for every `A` and every `B` of rank
one. -/
def IsRankOneConvex (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, B.rank = 1 → ConvexOn ℝ Set.univ fun t : ℝ => F (A + t • B)

/-- Quasiconvexity at `A`: `F (A) ≤ ∫_{(0,1)²} F (A + ∇φ)` for every Lipschitz `φ` vanishing
outside the unit square for which the integral exists (for a Borel, locally bounded `F` it always
does). -/
def IsQuasiconvexAt (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (K : NNReal), LipschitzWith K φ →
    (∀ x ∉ unitSquare, φ x = 0) →
      MeasureTheory.IntegrableOn (fun x => F (A + jac φ x)) unitSquare →
        F A ≤ ∫ x in unitSquare, F (A + jac φ x)

/-- Quasiconvexity: quasiconvexity at every matrix. -/
def IsQuasiconvex (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ A, IsQuasiconvexAt F A

/-- Isotropy: `F (Q A R) = F (A)` for all `Q, R ∈ SO(2)`. -/
def IsIsotropic (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ Q ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ, ∀ R ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ,
    ∀ A : Matrix (Fin 2) (Fin 2) ℝ, F (Q * A * R) = F A

/-- Positive `p`-homogeneity: `F (c A) = c^p F (A)` for every `c > 0`. -/
def IsPosHomogeneous (p : ℝ) (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ A : Matrix (Fin 2) (Fin 2) ℝ, F (c • A) = c ^ p * F A

/-- The polyaffine function `A ↦ k + ⟨K, A⟩ + c det A` on `ℝ^{2×2}`. -/
noncomputable def polyaffine (k : ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  k + ∑ i, ∑ j, K i j * A i j + c * A.det

/-- `F` has a polyaffine support at `A₀`: a polyaffine function below `F` that equals `F` at
`A₀`. -/
def HasPolyaffineSupportAt (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (A₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    Prop :=
  ∃ (k : ℝ) (K : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
    (∀ A, polyaffine k K c A ≤ F A) ∧ polyaffine k K c A₀ = F A₀

/-- Polyconvexity on `ℝ^{2×2}`: `F (A) = g (A, det A)` for a convex `g : ℝ^{2×2} × ℝ → ℝ`. -/
def Polyconvex (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) : Prop :=
  ∃ g : Matrix (Fin 2) (Fin 2) ℝ × ℝ → ℝ, ConvexOn ℝ Set.univ g ∧ ∀ A, F A = g (A, A.det)

/-- The conformal part `z = ((a₁₁ + a₂₂) + i (a₂₁ − a₁₂)) / 2` of `A`: with `ℝ² = ℂ`,
`A ζ = z ζ + w ζ̄`. -/
noncomputable def conformalPart (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ⟨(A 0 0 + A 1 1) / 2, (A 1 0 - A 0 1) / 2⟩

/-- The anticonformal part `w = ((a₁₁ − a₂₂) + i (a₂₁ + a₁₂)) / 2` of `A`. -/
noncomputable def anticonformalPart (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ⟨(A 0 0 - A 1 1) / 2, (A 1 0 + A 0 1) / 2⟩

/-- The Burkholder-type function `(|z| + |w|)^{p−1} (c₀ (|z| + |w|) + m (|z| − |w|))`, in
conformal coordinates. With `|A| = |z| + |w|`, the operator norm, it is
`|A|^{p−2} (c₀ |A|² + m det A)`. -/
noncomputable def burkholderType (p c₀ m : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
    (c₀ * (‖conformalPart A‖ + ‖anticonformalPart A‖) +
      m * (‖conformalPart A‖ - ‖anticonformalPart A‖))

/-- The Burkholder function `(|z| − (p − 1) |w|) (|z| + |w|)^{p−1}` on `ℝ^{2×2}`, in the form
that is rank-one convex for `1 < p ≤ 2`. In terms of the operator norm `|A|` it is
`((p/2) det A + (1 − p/2) |A|²) |A|^{p−2}`. For `1 < p < 2` it is `p/2` times the Burkholder
integrand `(|1 − 2/p| |A|² + det A) |A|^{p−2}` of Guerra and Kristensen, and `p − 1` times that
of arXiv:2609.28311, (2). For `p > 2` this formula is not the rank-one convex Burkholder
function; the library uses it for `1 ≤ p < 2` only. -/
noncomputable def burkholder (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
    (‖conformalPart A‖ - (p - 1) * ‖anticonformalPart A‖)

/-- The reflection `J = diag (1, −1)`. -/
def reflection : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- The determinant multiplier of the support of Theorem 1.2: `(p − 1) m` clamped to the
interval `[L, U]`, `L = ((1 + t) m − p H)/(1 − t)`, `U = (p H + (1 − t) m)/(1 + t)`. -/
noncomputable def multiplier (p H m t : ℝ) : ℝ :=
  min ((p * H + (1 - t) * m) / (1 + t)) (max (((1 + t) * m - p * H) / (1 - t)) ((p - 1) * m))

-- END SHARED DEFINITIONS

/-- The matrix with conformal part `z` and anticonformal part `w`. -/
noncomputable def ofComplex (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![z.re + w.re, w.im - z.im; z.im + w.im, z.re - w.re]

/-- The profile of `F`: `(x, y) ↦ F (ofComplex x y)`, for real `x`, `y`. For `x, y ≥ 0` the
matrix `ofComplex x y` is `diag (x + y, x − y)`. -/
noncomputable def profile (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (x y : ℝ) : ℝ :=
  F (ofComplex x y)

/-- The properties of the profile `Φ (|z|, |w|) = F (A)` of an isotropic, positively
`p`-homogeneous, rank-one convex `F` that the proofs use: homogeneity, and convexity along the
image of every rank-one line `τ ↦ (z + τ α, w + τ β)`, `|α| = |β|`. Only the values of `Φ` on
`[0, ∞)²` matter. -/
structure IsProfile (p : ℝ) (Φ : ℝ → ℝ → ℝ) : Prop where
  /-- `Φ (c x, c y) = c^p Φ (x, y)` for `c > 0`. -/
  homog : ∀ c x y : ℝ, 0 < c → 0 ≤ x → 0 ≤ y → Φ (c * x) (c * y) = c ^ p * Φ x y
  /-- `τ ↦ Φ (|z + τ α|, |w + τ β|)` is convex when `|α| = |β|`. -/
  convex : ∀ z w α β : ℂ, ‖α‖ = ‖β‖ →
    ConvexOn ℝ Set.univ fun τ : ℝ => Φ ‖z + τ * α‖ ‖w + τ * β‖

end HomogeneousIsotropic
