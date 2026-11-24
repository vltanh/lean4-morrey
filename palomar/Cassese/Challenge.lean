module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Challenge: Cassese, a solution to Morrey's problem in `ℝ^{2×m}`

G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*, arXiv:2608.03488v3 (16 September 2026).
Morrey's problem asks whether rank-one convexity implies quasiconvexity for integrands
`f : ℝ^{d×m} → ℝ`; the homogeneous Morrey problem (Kirchheim–Kristensen) asks whether every
`p`-homogeneous rank-one convex integrand is quasiconvex at `0`. The paper answers the homogeneous
problem negatively in `2 × m` for `m` large (Theorem 1.2), in `2 × 3` (Theorem 1.3), in `3 × 2`
(Corollary 5.3), in `d × d` with symmetries (Theorem 1.4) and in `4 × 2` for `p ≠ 2` (Theorem 1.5),
and shows that Kirchheim–Kristensen's theorem on `1`-homogeneous integrands does not extend to
rank-two matrices (Corollary 1.6). With Šverák's example (1992), Theorem 1.3 leaves `2 × 2` as the
only nontrivial dimension in which Morrey's problem may have a positive answer (the paper's
remark after Theorem 1.3, `morrey_landscape`); with Corollary 5.3, the same holds for the
homogeneous problem at `p = 4` (`homMorrey_landscape`).

## The theorems

All the theorems are unconditional.

* `theorem1_2`, `theorem1_3_a`, `theorem1_3_b`, `corollary5_3`, `morrey_landscape`,
  `homMorrey_landscape`: Theorems 1.2 and 1.3, Corollary 5.3 and the landscape after Theorem 1.3.
* `theorem1_4`: Theorem 1.4 for every `p ∈ (1, ∞)`; `theorem1_4_four`: Theorem 1.4 at `p = 4`,
  with the dimension `d₀ (4) = 588` of the paper's Corollary 6.3 (the paper's "simple, somewhat
  quantitative proof" for `p = 4`, Section 6.3).
* `theorem1_5`, `corollary1_6`: Theorem 1.5 and Corollary 1.6.
* `projL3_mem`: a check of the definitions of Section 5.2 (`projL3` maps into `𝓛₃`).

## Conventions

* `d × m` matrices are `Matrix (Fin d) (Fin m) ℝ`, `ℝ^m` is `Fin m → ℝ`, and the gradient of
  `φ : ℝ^m → ℝ^d` at `x` is `jac φ x` (rows are the components; for a Lipschitz `φ` it is the
  gradient almost everywhere, and `0` where `φ` is not differentiable).
* `IsIntegrand f`: `f` is lower semicontinuous and locally bounded (the paper's "integrand",
  Section 1.5).
* `QuasiconvexAt f A` (Definition 2.1): `f (A) ≤ ∫_{(0,1)^m} f (A + ∇φ)` for every Lipschitz `φ`
  vanishing outside the open unit cube (`W^{1,∞}_0`), whenever the integral exists;
  `NowhereQuasiconvex f`: quasiconvex at no matrix; `Quasiconvex f`: quasiconvex at every matrix.
* `RankOneConvex f` (Definition 2.2): `t ↦ f (t A + (1 − t) B)` is convex on `[0, 1]` whenever
  `rank (A − B) = 1`.
* `IsPHomogeneous p f`: `f (t A) = |t|^p f (A)` for every real `t`; `IsHomogeneousPolynomial n f`:
  a homogeneous polynomial of degree `n` in the entries.
* `IsConjugationInvariant f`: `f (U A Uᵀ) = f (A)` for orthogonal `U`;
  `IsTranspositionInvariant f`: `f (Aᵀ) = f (A)`.
* Corollary 5.3 names a quartic built in Section 5: `ℝ²` and the columns of `A ∈ ℝ^{2×4}` are
  read as complex numbers, each `2 × 2` block `(a b; c d)` acts as `z ↦ α z + β z̄` with
  `α = (a + d + i (c − b)) / 2`, `β = (a − d + i (c + b)) / 2` (`wirtAlpha`, `wirtBeta`);
  `Z = (conj α₂, conj α₁, β₁)` (`zCoord`), `q = 4 |z₀ z₂ − z₁²|² − (|z₀|² + |z₂|² − 2 |z₁|²)²`
  (`quarticQ`), `J A = (A | 0)` (`embedJ`), `q₃ = q ∘ J` (`q3`), `𝓛₃ = J⁻¹ {β₂ = conj α₁}` (`L3`),
  `π` the Frobenius-orthogonal projection onto `𝓛₃` (`projL3`, explicit),
  `q_{δ,Λ} (A) = q₃ (π A) + δ (|π A|² + Λ² |A − π A|²)²` (`qDeltaLambda`, with `|·|` the Frobenius
  norm, `frobSq`) and `q̂_{δ,Λ} (A) = q_{δ,Λ} (Aᵀ)` (`qHat`).

## The results of other works

The paper's proofs cite results of other works: Burkholder's inequalities for Hilbert-space-valued
martingales (Theorem 2.3) and his scalar functions (13), (14); Dacorogna's formula for the
quasiconvex envelope (Proposition 2.2, citing Kinderlehrer–Pedregal 1991, Proposition 8.1) and
Dacorogna's theorems on rank-one affine functions and quadratic forms; Rindler's lemmas (Lemmas
2.1, 2.2, the latter with Dacorogna 2008, Propositions 5.11, 5.13); Kristensen's smoothing argument;
the properties of UMD spaces (Proposition 2.7: extrapolation, HNVW I, Theorem 4.2.7; the Schatten
classes, Randrianantoanina 2002, Corollary 4.5; `L^p`, Pisier 2016, Corollary 5.22; dyadic
martingales, HNVW I, Theorem 4.2.5; complex constants, Yaroslavtsev 2018, Lemma 3.2; zig-zag
concave functions, HNVW I, Theorem 4.5.6, and Yaroslavtsev 2018, Proposition 3.7) and decoupling
(Proposition 2.8; Cox–Veraar 2007, HNVW I, Proposition 4.2.3); the non-commutative Khintchine
inequality (Proposition 6.3; Pisier–Xu 2003, Theorem 6.1, with Lust-Piquard 1986 and
Lust-Piquard–Pisier 1991) and the Kahane–Khintchine inequality (Proposition 6.4; HNVW II,
Theorem 6.2.4); and, in Section 7, the results of Cassese 2025 (J. Math. Pures Appl. 213) in the
proof of Proposition 7.1, and, for the Beurling–Ahlfors transform `𝓑`, transference for homogeneous multipliers (HNVW I,
Corollary 5.7.6: `‖𝓑^k‖_{L^p (ℝ²)} ≤ ‖𝓑^k‖_{L^p_0 (𝕋²)}`) and Dragičević's lower bound (Arch. Math.
96 (2011), Theorem 1.1: `‖𝓑²‖_{L^p (ℝ²)} > p* − 1` for `p ≠ 2`, and `‖𝓑²‖_{L⁴} ≥ 21/5`). These are
proved in the library, and no statement here assumes them.

The definitions are copied word for word from `Morrey/Cassese/Defs.lean` (kept in sync by
`scripts/sync_challenge_defs.py`); the theorems are proved in `palomar/Cassese/Solution.lean`.
-/

@[expose] public section

namespace Cassese

-- BEGIN SHARED DEFINITIONS

open scoped Matrix ENNReal

/-- The derivative matrix of `φ : ℝ^m → ℝ^d` at `x`: the `d × m` matrix with entries
`∂_k φ_i (x)` (rows are the components). For a Lipschitz `φ` it is the gradient almost
everywhere (Rademacher's theorem); elsewhere `fderiv` is `0`. -/
noncomputable def jac {d m : ℕ} (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  Matrix.of fun i k => fderiv ℝ (fun y => φ y i) x (Pi.single k 1)

/-- The open unit cube `(0, 1)^m`. -/
def unitCube (m : ℕ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo 0 1

/-- An integrand (Section 1.5): a locally bounded lower semicontinuous function
`f : ℝ^{d×m} → ℝ`. -/
def IsIntegrand {d m : ℕ} (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  LowerSemicontinuous f ∧ ∀ A, ∃ U ∈ nhds A, ∃ C : ℝ, ∀ B ∈ U, |f B| ≤ C

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

/-- Conjugation invariance (Section 1.3): `f (U A Uᵀ) = f (A)` for every `A ∈ ℝ^{d×d}` and every
orthogonal `U ∈ O(d)`. -/
def IsConjugationInvariant {d : ℕ} (f : Matrix (Fin d) (Fin d) ℝ → ℝ) : Prop :=
  ∀ U ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∀ A : Matrix (Fin d) (Fin d) ℝ, f (U * A * Uᵀ) = f A

/-- Transposition invariance (Theorem 1.4): `f (Aᵀ) = f (A)`. -/
def IsTranspositionInvariant {d : ℕ} (f : Matrix (Fin d) (Fin d) ℝ → ℝ) : Prop :=
  ∀ A : Matrix (Fin d) (Fin d) ℝ, f Aᵀ = f A

/-- The squared Frobenius norm `|A|² = ∑ A_{ij}²`. -/
def frobSq {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- The conformal coefficient `α` of the `2 × 2` block of `A ∈ ℝ^{2×m}` in the columns `k`, `l`
(Section 4.1): identifying both copies of `ℝ²` with `ℂ` (`(x, y) ↦ x + i y`), the block
`(a b; c d)` acts as `z ↦ α z + β z̄`, with `α = (a + d + i (c − b)) / 2`. -/
noncomputable def wirtAlpha {m : ℕ} (A : Matrix (Fin 2) (Fin m) ℝ) (k l : Fin m) : ℂ :=
  (((A 0 k + A 1 l) / 2 : ℝ) : ℂ) + (((A 1 k - A 0 l) / 2 : ℝ) : ℂ) * Complex.I

/-- The anticonformal coefficient `β = (a − d + i (c + b)) / 2` of the same block
(Section 4.1). -/
noncomputable def wirtBeta {m : ℕ} (A : Matrix (Fin 2) (Fin m) ℝ) (k l : Fin m) : ℂ :=
  (((A 0 k - A 1 l) / 2 : ℝ) : ℂ) + (((A 1 k + A 0 l) / 2 : ℝ) : ℂ) * Complex.I

/-- The coordinates `Z = (Z⁰, Z¹, Z²) = (X², X¹, Y¹)` of `A ∈ ℝ^{2×4}` (Section 5.1), where
`X = conj P₂ (A) = (conj α₁, conj α₂)` and `Y = Q₂ (A) = (β₁, β₂)`; the first block is formed by
the columns `0, 1` and the second by the columns `2, 3`. -/
noncomputable def zCoord (A : Matrix (Fin 2) (Fin 4) ℝ) : Fin 3 → ℂ :=
  ![starRingEnd ℂ (wirtAlpha A 2 3), starRingEnd ℂ (wirtAlpha A 0 1), wirtBeta A 0 1]

/-- The quartic (23) on `ℝ^{2×4}`:
`q = 4 |z₀ z₂ − z₁²|² − (|z₀|² + |z₂|² − 2 |z₁|²)²` at `z = Z (A)`. -/
noncomputable def quarticQ (A : Matrix (Fin 2) (Fin 4) ℝ) : ℝ :=
  4 * ‖zCoord A 0 * zCoord A 2 - zCoord A 1 ^ 2‖ ^ 2 -
    (‖zCoord A 0‖ ^ 2 + ‖zCoord A 2‖ ^ 2 - 2 * ‖zCoord A 1‖ ^ 2) ^ 2

/-- The subspace `𝓛 = {A ∈ ℝ^{2×4} : Y² (A) = X¹ (A)}` of (20), that is `β₂ = conj α₁`. -/
def calL : Set (Matrix (Fin 2) (Fin 4) ℝ) :=
  {A | wirtBeta A 2 3 = starRingEnd ℂ (wirtAlpha A 0 1)}

/-- The embedding `J : ℝ^{2×3} → ℝ^{2×4}`, `J A = (A | 0)` (Section 5.2). -/
def embedJ (A : Matrix (Fin 2) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  Matrix.of fun i j => if h : j.val < 3 then A i ⟨j.val, h⟩ else 0

/-- The subspace `𝓛₃ = J⁻¹ 𝓛 ⊆ ℝ^{2×3}` (Section 5.2). -/
def L3 : Set (Matrix (Fin 2) (Fin 3) ℝ) :=
  {A | embedJ A ∈ calL}

/-- The quartic `q₃ = q ∘ J` on `ℝ^{2×3}` (Section 5.2). -/
noncomputable def q3 (A : Matrix (Fin 2) (Fin 3) ℝ) : ℝ :=
  quarticQ (embedJ A)

/-- The orthogonal projection `π` of `ℝ^{2×3}` (Frobenius inner product) onto `𝓛₃`. For
`A = (a b e; c d f)`, `𝓛₃ = {e = a + d, f = b − c}`, whose normal space is spanned by the
orthogonal matrices `N₁ = (−1 0 1; 0 −1 0)` and `N₂ = (0 −1 0; 1 0 1)`, both of squared norm `3`;
so `π A = A − s N₁ − t N₂` with `s = ⟨A, N₁⟩ / 3 = (e − a − d) / 3` and
`t = ⟨A, N₂⟩ / 3 = (f − b + c) / 3`. -/
noncomputable def projL3 (A : Matrix (Fin 2) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  let s := (A 0 2 - A 0 0 - A 1 1) / 3
  let t := (A 1 2 - A 0 1 + A 1 0) / 3
  !![A 0 0 + s, A 0 1 + t, A 0 2 - s; A 1 0 - t, A 1 1 + s, A 1 2 - t]

/-- The quartic of the proof of Theorem 1.3,
`q_{δ,Λ} (A) = q₃ (π A) + δ (|π A|² + Λ² |π^⊥ A|²)²` on `ℝ^{2×3}`, with `|·|` the Frobenius norm
and `π^⊥ A = A − π A`. -/
noncomputable def qDeltaLambda (δ Λ : ℝ) (A : Matrix (Fin 2) (Fin 3) ℝ) : ℝ :=
  q3 (projL3 A) + δ * (frobSq (projL3 A) + Λ ^ 2 * frobSq (A - projL3 A)) ^ 2

/-- The transposed quartic of Corollary 5.3, `q̂_{δ,Λ} (A) = q_{δ,Λ} (Aᵀ)` on `ℝ^{3×2}`. -/
noncomputable def qHat (δ Λ : ℝ) (A : Matrix (Fin 3) (Fin 2) ℝ) : ℝ :=
  qDeltaLambda δ Λ Aᵀ

-- END SHARED DEFINITIONS

end Cassese

namespace CasseseChallenge

open Cassese

/-- **Theorem 1.2.** For `p ∈ (1, ∞)` there is `m₀ (p)` such that for every `m ≥ m₀ (p)` there is a
`p`-homogeneous, rank-one convex and nowhere quasiconvex integrand `f : ℝ^{2×m} → ℝ`.
Unconditional. -/
theorem theorem1_2 {p : ℝ} (hp : 1 < p) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ f : Matrix (Fin 2) (Fin m) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  sorry

/-- **Theorem 1.3**, first assertion. There is a homogeneous quartic polynomial
`P : ℝ^{2×3} → ℝ` which is rank-one convex but nowhere quasiconvex. -/
theorem theorem1_3_a :
    ∃ P : Matrix (Fin 2) (Fin 3) ℝ → ℝ,
      IsHomogeneousPolynomial 4 P ∧ RankOneConvex P ∧ NowhereQuasiconvex P := by
  sorry

/-- **Theorem 1.3**, second assertion. For `p` sufficiently close to `4` there is a
`p`-homogeneous integrand `P : ℝ^{2×3} → ℝ` which is rank-one convex but nowhere quasiconvex. -/
theorem theorem1_3_b :
    ∃ ε > 0, ∀ p : ℝ, |p - 4| < ε → ∃ f : Matrix (Fin 2) (Fin 3) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  sorry

/-- **Theorem 1.4.** For `p ∈ (1, ∞)` there is `d₀ (p)` such that for every `d ≥ d₀ (p)` there is
a conjugation- and transposition-invariant `p`-homogeneous integrand `f : ℝ^{d×d} → ℝ` which is
rank-one convex but nowhere quasiconvex. Unconditional. -/
theorem theorem1_4 {p : ℝ} (hp : 1 < p) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ f : Matrix (Fin d) (Fin d) ℝ → ℝ,
      IsIntegrand f ∧ IsConjugationInvariant f ∧ IsTranspositionInvariant f ∧
        IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  sorry

/-- **Theorem 1.4 at `p = 4`** (Section 6.3, with Corollary 6.3's `d₀ = 588`). For every
`d ≥ 588` there is a conjugation- and transposition-invariant `4`-homogeneous integrand
`f : ℝ^{d×d} → ℝ` which is rank-one convex but nowhere quasiconvex. Unconditional. -/
theorem theorem1_4_four : ∀ d ≥ 588, ∃ f : Matrix (Fin d) (Fin d) ℝ → ℝ,
    IsIntegrand f ∧ IsConjugationInvariant f ∧ IsTranspositionInvariant f ∧
      IsPHomogeneous 4 f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  sorry

/-- **Theorem 1.5.** For every `p ∈ (1, ∞) ∖ {2}` there is a `p`-homogeneous integrand
`f : ℝ^{4×2} → ℝ` which is rank-one convex but nowhere quasiconvex. Unconditional. -/
theorem theorem1_5 {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) :
    ∃ f : Matrix (Fin 4) (Fin 2) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  sorry

/-- **Corollary 1.6.** There is a `1`-homogeneous rank-one convex integrand
`f : ℝ^{4×4} → [0, ∞)` which is not quasiconvex at a matrix of rank `2`. Unconditional. -/
theorem corollary1_6 :
    ∃ f : Matrix (Fin 4) (Fin 4) ℝ → ℝ, IsIntegrand f ∧ (∀ A, 0 ≤ f A) ∧ IsPHomogeneous 1 f ∧
      RankOneConvex f ∧ ∃ A : Matrix (Fin 4) (Fin 4) ℝ, A.rank = 2 ∧ ¬ QuasiconvexAt f A := by
  sorry

/-- **Corollary 5.3.** For `K` sufficiently large and `δ > 0` sufficiently small, with
`Λ = K/δ`, `q̂_{δ,Λ} (A) = q_{δ,Λ} (Aᵀ)` on `ℝ^{3×2}` is a homogeneous quartic polynomial which is
globally rank-one convex and nowhere quasiconvex. -/
theorem corollary5_3 :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      IsHomogeneousPolynomial 4 (qHat δ (K / δ)) ∧ RankOneConvex (qHat δ (K / δ)) ∧
        NowhereQuasiconvex (qHat δ (K / δ)) := by
  sorry

/-- **The 2 × 2 landscape** (the remark after Theorem 1.3). For `d, m ≥ 2` with
`(d, m) ≠ (2, 2)` there is a rank-one convex integrand on `ℝ^{d×m}` that is not quasiconvex. -/
theorem morrey_landscape {d m : ℕ} (hd : 2 ≤ d)
    (hm : 2 ≤ m) (h22 : ¬ (d = 2 ∧ m = 2)) :
    ∃ f : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand f ∧ RankOneConvex f ∧ ¬ Quasiconvex f := by
  sorry

/-- **The homogeneous landscape** (after Theorem 1.3, and after Corollary 5.3). For `d, m ≥ 2`
with `(d, m) ≠ (2, 2)` there is a `4`-homogeneous rank-one convex integrand on `ℝ^{d×m}` that is
not quasiconvex at `0`: the homogeneous Morrey problem has a negative answer in every nontrivial
dimension except possibly `2 × 2`. -/
theorem homMorrey_landscape {d m : ℕ}
    (hd : 2 ≤ d) (hm : 2 ≤ m) (h22 : ¬ (d = 2 ∧ m = 2)) :
    ∃ f : Matrix (Fin d) (Fin m) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous 4 f ∧ RankOneConvex f ∧ ¬ QuasiconvexAt f 0 := by
  sorry

/-- A check of the definitions of Section 5.2: `projL3` maps into `𝓛₃`. -/
theorem projL3_mem (A : Matrix (Fin 2) (Fin 3) ℝ) : projL3 A ∈ L3 := by
  sorry

end CasseseChallenge
