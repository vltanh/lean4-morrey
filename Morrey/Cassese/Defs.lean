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
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Cassese, arXiv:2608.03488v3: the definitions

G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*, arXiv:2608.03488v3 (16 September
2026). The paper writes integrands `f : ℝ^{d×m} → ℝ` and maps `u : [0, 1]^m → ℝ^d`; here `d × m`
matrices are `Matrix (Fin d) (Fin m) ℝ`, `ℝ^m` is `Fin m → ℝ`, and the gradient of `φ` at `x` is
`jac φ x`, whose rows are the derivatives of the components.

* `IsIntegrand` (Section 1.5): a locally bounded lower semicontinuous function.
* `QuasiconvexAt` (Definition 2.1, `Quasiconvexity`), `Quasiconvex`, `NowhereQuasiconvex`.
* `RankOneConvex` (Definition 2.2, `Rank-one convexity`): convexity on segments whose endpoints
  differ by a rank-one matrix.
* `IsPHomogeneous`: `f (t A) = |t|^p f (A)` for every real `t` (Section 1.3).
* `IsHomogeneousPolynomial`: a homogeneous polynomial in the entries.
* `IsConjugationInvariant`, `IsTranspositionInvariant` (Section 1.3 and Theorem 1.4):
  `f (U A Uᵀ) = f (A)` for orthogonal `U`, and `f (Aᵀ) = f (A)`.
* `unitCube`: the open cube `(0, 1)^m`; a Lipschitz map on `[0, 1]^m` vanishing on the boundary,
  extended by `0`, is a Lipschitz map on `ℝ^m` vanishing outside the open cube.
* The objects of Section 5 that Corollary 5.3 names: the Wirtinger coefficients `wirtAlpha`,
  `wirtBeta` of a `2 × 2` block (Section 4.1), the coordinates `zCoord` and the quartic `quarticQ`
  on `ℝ^{2×4}` (Section 5.1, (23)), the subspaces `calL ⊆ ℝ^{2×4}` ((20)) and
  `L3 = J⁻¹ calL ⊆ ℝ^{2×3}`, the embedding `embedJ` (`J A = (A | 0)`), `q3 = q ∘ J`, the
  orthogonal projection `projL3` onto `L3`, and the quartics `qDeltaLambda` (proof of Theorem 1.3)
  and `qHat` (Corollary 5.3).
* The results of other works on which the main theorems of the Challenge are conditional, as
  propositions named after their sources (`HNVWExtrapolation`, `RandrianantoaninaSchattenUMD`,
  `CoxVeraarDecoupling`, `PisierXuKhintchine`, `KahaneKhintchine`, `HNVWTransference`,
  `DragicevicLowerBound`), and what they need: `pStar`, `p* = max (p, p')`; Rademacher signs on
  the canonical space `Fin N → Bool` (`coin`, `avg`, `IsPredictable`, `mart`, `lpNormWith`); the
  UMD constants of Definition 2.5 (`umdConstWith`); the Schatten norms (`sval`, `schattenNorm`);
  the Beurling–Ahlfors transform and its powers on `ℝ²` and on `𝕋²` (`beurlingSymbol`,
  `beurlingPow`, `beurlingPowNorm`, `trigPoly`, `torusBeurlingPow`, `torusBeurlingPowNorm`). They
  live here, and not in `External/`, because the Challenge states the main theorems with these
  hypotheses and may import only Mathlib.
* After the shared block: Proposition 2.7 (3), (5) (`PisierLpUMD`, `YaroslavtsevComplexUMD`) and
  the constants they need (`umdConst`, `complexUMDConst`), hypotheses of the paper's proof of
  Theorem 1.2 (`theorem1_2_umd`) only.

Representation choices. A Banach space in the hypotheses on UMD spaces is a complete normed space
`E` renormed by an equivalent norm `nrm` (every Banach space is one, with `nrm = ‖·‖`; `S_q^{d×d}`
is `Fin d → Fin d → ℝ` with `nrm = ‖·‖_{S_q}`); the norms of `𝓑^k` are suprema over dense
subspaces (Schwartz functions on `ℝ²`, mean-zero trigonometric polynomials on `𝕋²`).

Everything between the markers below is copied word for word into `palomar/Cassese/Challenge.lean` by
`scripts/sync_challenge_defs.py`.
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

/-! ### Tools for the conditional statements

The main theorems are conditional on results of other works that are out of reach of this
formalization. Each such result is a proposition below, named after its source; the definitions
it needs come first. -/

/-- Burkholder's exponent `p* = max (p, p / (p − 1))`. -/
noncomputable def pStar (p : ℝ) : ℝ := max p (p / (p - 1))

/-- The sign `±1` of a coin. `N` independent Rademacher signs are realised on the canonical space
`Fin N → Bool` with the uniform probability. -/
def coin (b : Bool) : ℝ := if b then 1 else -1

/-- The expectation over `N` independent fair signs: `avg g = 2^{-N} Σ_{ε ∈ {±1}^N} g ε`. -/
noncomputable def avg {N : ℕ} (g : (Fin N → Bool) → ℝ) : ℝ :=
  (∑ ε, g ε) / 2 ^ N

/-- A family `ξ k` of functions of the signs is predictable: `ξ k` depends only on the signs
`ε j` with `j < k`. -/
def IsPredictable {N : ℕ} {E : Type*} (ξ : Fin N → (Fin N → Bool) → E) : Prop :=
  ∀ (k : Fin N) (ε ε' : Fin N → Bool), (∀ j, j < k → ε j = ε' j) → ξ k ε = ξ k ε'

/-- The `L^p` norm `(E N (X)^p)^{1/p}` of a random variable `X` on the signs, measured with the
function `N` (a norm). -/
noncomputable def lpNormWith {N : ℕ} {E : Type*} (nrm : E → ℝ) (p : ℝ)
    (X : (Fin N → Bool) → E) : ℝ :=
  avg (fun ε => nrm (X ε) ^ p) ^ (1 / p)

/-- The Rademacher (Paley–Walsh) martingale `n ↦ Σ_{k < n} ε_k ξ_k` of predictable `ξ`, started
at `0`, at time `n`. -/
noncomputable def mart {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ) (ε : Fin N → Bool) : E :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < n), coin (ε k) • ξ k ε

/-- `β` is a `UMD_p` constant (Definition 2.5) of the complete normed space `E` renormed by
`nrm`: for every probability space and filtration, every `E`-valued martingale `Y` with `Y₀ = 0`
and every sequence of predictable signs `σ_k ∈ {±1}` (`σ_{k+1}` is `ℱ_k`-measurable),
`‖Σ_{k<n} σ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}`, the norms of the values taken with
`nrm`. The probability spaces range over `Type`. -/
def IsUMDBoundWith (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (nrm : E → ℝ) (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (ℱ : MeasureTheory.Filtration ℕ mΩ) (Y : ℕ → Ω → E)
    (σ : ℕ → Ω → ℝ),
    MeasureTheory.Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n ω, σ n ω = 1 ∨ σ n ω = -1) →
      (∀ k, @MeasureTheory.StronglyMeasurable _ _ _ (ℱ k) (σ (k + 1))) →
      ∀ n, MeasureTheory.eLpNorm
          (fun ω => nrm (∑ k ∈ Finset.range n, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)))
          (ENNReal.ofReal p) μ ≤
        β * MeasureTheory.eLpNorm (fun ω => nrm (Y n ω)) (ENNReal.ofReal p) μ

/-- `UMD_p` of `E` renormed by `nrm`: the best constant (`∞` if there is none). -/
noncomputable def umdConstWith (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (nrm : E → ℝ) (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsUMDBoundWith E nrm p β}

/-- The singular values of `A ∈ ℝ^{d×m}`, indexed by the columns: `s_i = √λ_i (Aᵀ A)` (when
`m > d` the extra ones are `0`, which changes no Schatten norm). -/
noncomputable def sval {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin m) : ℝ :=
  √((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The Schatten `q`-norm (Section 1.5): `‖A‖_{S_q} = (Σ s_i^q)^{1/q}` for `q < ∞`,
`‖A‖_{S_∞} = max s_i`. -/
noncomputable def schattenNorm {d m : ℕ} (q : ℝ≥0∞) (A : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  if q = ⊤ then ⨆ i, sval A i else (∑ i, sval A i ^ q.toReal) ^ (1 / q.toReal)

/-- The symbol `m (ξ) = ξ̄ / ξ` of the Beurling–Ahlfors transform `𝓑` (`m (0) = 0`), with `ℝ² ≅ ℂ`
by `(x, y) ↦ x + i y`. With `𝓕 f (w) = ∫ e^{−2πi ⟨v, w⟩} f (v) dv`, `𝓑 (∂̄ f) = ∂ f`. -/
noncomputable def beurlingSymbol (ξ : ℂ) : ℂ := starRingEnd ℂ ξ / ξ

/-- `𝓑^k f = 𝓕⁻¹ (m^k 𝓕 f)` on `ℝ² ≅ ℂ`. -/
noncomputable def beurlingPow (k : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  FourierTransformInv.fourierInv
    (fun ξ : ℂ => beurlingSymbol ξ ^ k • FourierTransform.fourier f ξ)

/-- `‖𝓑^k‖_{L^p (ℝ²) → L^p (ℝ²)}`: the supremum of `‖𝓑^k f‖_p / ‖f‖_p` over the (dense) Schwartz
functions `f`. -/
noncomputable def beurlingPowNorm (k : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ⨆ f : SchwartzMap ℂ ℂ, MeasureTheory.eLpNorm (beurlingPow k f) (ENNReal.ofReal p)
      MeasureTheory.volume /
    MeasureTheory.eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) MeasureTheory.volume

/-- The trigonometric polynomial `x ↦ Σ_n c_n e^{2πi ⟨n, x⟩}` on the torus `𝕋² = ℝ² / ℤ²`. -/
noncomputable def trigPoly (c : (Fin 2 → ℤ) →₀ ℂ) (x : UnitAddTorus (Fin 2)) : ℂ :=
  c.sum fun n a => a * UnitAddTorus.mFourier n x

/-- `𝓑^k` on `𝕋²` (the multiplier `m` at the frequency `n₀ + i n₁`) applied to the trigonometric
polynomial with coefficients `c`. -/
noncomputable def torusBeurlingPow (k : ℕ) (c : (Fin 2 → ℤ) →₀ ℂ) (x : UnitAddTorus (Fin 2)) :
    ℂ :=
  c.sum fun n a => beurlingSymbol ((n 0 : ℂ) + (n 1 : ℂ) * Complex.I) ^ k * a *
    UnitAddTorus.mFourier n x

/-- `‖𝓑^k‖_{L^p_0 (𝕋²) → L^p_0 (𝕋²)}`: the supremum over the (dense) mean-zero trigonometric
polynomials (`c₀ = 0`). -/
noncomputable def torusBeurlingPowNorm (k : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ⨆ (c : (Fin 2 → ℤ) →₀ ℂ) (_ : c 0 = 0),
    MeasureTheory.eLpNorm (torusBeurlingPow k c) (ENNReal.ofReal p) MeasureTheory.volume /
      MeasureTheory.eLpNorm (trigPoly c) (ENNReal.ofReal p) MeasureTheory.volume

/-- **Proposition 2.7 (1)** (`prop:umd`), citing Hytönen–van Neerven–Veraar–Weis, *Analysis in
Banach spaces I* (2016), Theorem 4.2.7: a Banach space that is `UMD_{p₀}` for some
`p₀ ∈ (1, ∞)` is `UMD_p` for every `p ∈ (1, ∞)`; and
`UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 100 p* UMD₂ (X)` for every `p ∈ (1, ∞)`. The Banach spaces are
the complete normed spaces `E` renormed by an equivalent norm `nrm` (every Banach space is one,
with `nrm = ‖·‖`). -/
def HNVWExtrapolation : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (nrm : E → ℝ),
    (∀ x y, nrm (x + y) ≤ nrm x + nrm y) → (∀ (c : ℝ) x, nrm (c • x) = |c| * nrm x) →
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x, a * ‖x‖ ≤ nrm x ∧ nrm x ≤ b * ‖x‖) →
    ((∃ p₀ : ℝ, 1 < p₀ ∧ umdConstWith E nrm p₀ < ⊤) →
        ∀ p : ℝ, 1 < p → umdConstWith E nrm p < ⊤) ∧
      ∀ p : ℝ, 1 < p → umdConstWith E nrm 2 ≤ 200 * umdConstWith E nrm p ∧
        umdConstWith E nrm p ≤ ENNReal.ofReal (100 * pStar p) * umdConstWith E nrm 2

/-- **Proposition 2.7 (2)** (`prop:umd`), citing Randrianantoanina, *Non-commutative martingale
transforms*, J. Funct. Anal. 194 (2002), Corollary 4.5, for the subspaces `S_q^{d×d}` of
`S_q (ℓ₂ (ℕ))`: there is an absolute `C` with `UMD₂ (S_q^{d×d}) ≤ C (q* − 1)` for every
`q ∈ (1, ∞)` and every `d`. (`S_q^{d×d}` is `Fin d → Fin d → ℝ` renormed by `‖·‖_{S_q}`.) -/
def RandrianantoaninaSchattenUMD : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ), 1 < q → ∀ d : ℕ,
    umdConstWith (Fin d → Fin d → ℝ) (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) 2 ≤
      ENNReal.ofReal (C * (pStar q - 1))

/-- **Proposition 2.8** (`cs-prop2.8`), decoupling, citing Cox–Veraar, Electron. Commun. Probab.
12 (2007), and HNVW I, Proposition 4.2.3: for a Banach space `(E, nrm)`, `p ∈ (1, ∞)` and a
Rademacher martingale `dY_n = ε_n ξ_n` with predictable `ξ_n`, and `Ỹ_n = Σ_{k<n} ε̃_k ξ_k` with an
independent copy `ε̃` of the signs,
`UMD_p⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p ‖Ỹ_n‖_{L^p}`. On the canonical space
`{±1}^N × {±1}^N`. -/
def CoxVeraarDecoupling : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (nrm : E → ℝ),
    (∀ x y, nrm (x + y) ≤ nrm x + nrm y) → (∀ (c : ℝ) x, nrm (c • x) = |c| * nrm x) →
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x, a * ‖x‖ ≤ nrm x ∧ nrm x ≤ b * ‖x‖) →
    ∀ p : ℝ, 1 < p → ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → E), IsPredictable ξ → ∀ n : ℕ,
      ENNReal.ofReal (avg (fun ε => avg fun ε' => nrm (mart (fun k _ => ξ k ε) n ε') ^ p) ^ (1 / p))
          ≤ umdConstWith E nrm p * ENNReal.ofReal (lpNormWith nrm p (mart ξ n)) ∧
        ENNReal.ofReal (lpNormWith nrm p (mart ξ n)) ≤ umdConstWith E nrm p *
          ENNReal.ofReal
            (avg (fun ε => avg fun ε' => nrm (mart (fun k _ => ξ k ε) n ε') ^ p) ^ (1 / p))

/-- **Proposition 6.3** (`cs-prop6.3`), non-commutative Khintchine, citing Pisier–Xu,
*Non-commutative `L^p`-spaces* (2003), Theorem 6.1: for `q ∈ [2, ∞)`, normal `d × d` matrices
`x_i` and independent Rademacher `ε_i`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≲ √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`,
with an absolute constant. (`‖B^{1/2}‖_{S_q} = ‖B‖_{S_{q/2}}^{1/2}` for `B = Σ x_i x_iᵀ ⪰ 0`.) -/
def PisierXuKhintchine : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ), 2 ≤ q → ∀ (d n : ℕ) (x : Fin n → Matrix (Fin d) (Fin d) ℝ),
    (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
          lpNormWith (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ∧
        lpNormWith (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
          C * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))

/-- **Proposition 6.4** (`cs-prop6.4`), Kahane–Khintchine, citing HNVW, *Analysis in Banach
spaces II* (2017), Theorem 6.2.4 (TeX lines 2312–2321): there are `k_{p,q}` such that for every
Banach space `X`, every `x₁, …, x_n ∈ X` and independent Rademacher `ε_i`,
`k_{q,p}⁻¹ ‖Σ ε_i x_i‖_{L^q} ≤ ‖Σ ε_i x_i‖_{L^p} ≤ k_{p,q} ‖Σ ε_i x_i‖_{L^q}` for
`p, q ∈ (1, ∞)`; and, quantitatively, `k_{q,p} ≤ √((q − 1) / (p − 1))` for `1 < p ≤ q`.

The quantitative clause. The paper's Proposition 6.4 names only constants `k_{p,q}`, but its route
to Remark 6.3 (TeX lines 2425–2437) and to the case `q = ∞` of Proposition 6.5 (TeX lines
2477–2479: "all the implied multiplicative constants in the above inequalities are at most
polynomial in `q`") uses (31) (TeX lines 2322–2328) with constants that grow at most polynomially
in `q`, which needs `k_{q,p}` to. The paper names no source for this growth. The form assumed is the
standard bound `κ_{q,p} ≤ √((q − 1) / (p − 1))` for `1 < p ≤ q < ∞` (the Kahane–Khintchine
inequality obtained from the hypercontractivity of Banach-valued Rademacher sums, as in HNVW II);
neither HNVW II nor any other source for it was consulted for this formalization.

Generality. It is stated for any seminorm `nrm` on a real vector space `E` (the hypotheses on
`nrm` are the triangle inequality and absolute homogeneity, which give `nrm ≥ 0`), not only for
Banach spaces. This follows from the Banach case: the `x_i` span a finite-dimensional subspace,
whose quotient by the kernel of `nrm` is a finite-dimensional, hence complete, normed space in
which the finite sums `Σ ε_i x_i` have the same norms. -/
def KahaneKhintchine : Prop :=
  ∃ κ : ℝ → ℝ → ℝ, (∀ p q, 0 < κ p q) ∧
    (∀ p q : ℝ, 1 < p → p ≤ q → κ q p ≤ √((q - 1) / (p - 1))) ∧
    ∀ p q : ℝ, 1 < p → 1 < q →
    ∀ (E : Type) [AddCommGroup E] [Module ℝ E] (nrm : E → ℝ),
      (∀ x y, nrm (x + y) ≤ nrm x + nrm y) → (∀ (c : ℝ) x, nrm (c • x) = |c| * nrm x) →
      ∀ (n : ℕ) (x : Fin n → E),
        (κ q p)⁻¹ * lpNormWith nrm q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
            lpNormWith nrm p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ∧
          lpNormWith nrm p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
            κ p q * lpNormWith nrm q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i)

/-- Transference for the powers of the Beurling–Ahlfors transform, citing HNVW I,
Corollary 5.7.6 ("the standard transference identity for homogeneous multipliers", proof of
Proposition 7.2), in the direction used: `‖𝓑^k‖_{L^p (ℝ²)} ≤ ‖𝓑^k‖_{L^p_0 (𝕋²)}` for `k ≥ 1`,
`p ∈ (1, ∞)`. -/
def HNVWTransference : Prop :=
  ∀ (k : ℕ) (p : ℝ), 1 ≤ k → 1 < p → beurlingPowNorm k p ≤ torusBeurlingPowNorm k p

/-- Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
operator*, Arch. Math. 96 (2011), Theorem 1.1, as used in the proof of Theorem 7.1:
`‖𝓑²‖_{L^p (ℝ²) → L^p (ℝ²)} > p* − 1` for `p ∈ (1, ∞)`, `p ≠ 2`. -/
def DragicevicLowerBound : Prop :=
  ∀ p : ℝ, 1 < p → p ≠ 2 → ENNReal.ofReal (pStar p - 1) < beurlingPowNorm 2 p

-- END SHARED DEFINITIONS

/-! ### Hypotheses of the paper's proof of Theorem 1.2

Proposition 2.7 (3), (5) and the constants they need. No statement of the Challenge uses them
(its Theorem 1.2 is the unconditional `theorem1_2`), so they stand after the shared block; the
paper's proof of Theorem 1.2, `theorem1_2_umd`, takes them as hypotheses. -/

/-- `UMD_p (X)` of a real Banach space `X` (Definition 2.5). -/
noncomputable def umdConst (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (p : ℝ) : ℝ≥0∞ :=
  umdConstWith X (fun x => ‖x‖) p

/-- `β` is a complex `UMD_p` constant of the complex Banach space `X` ((5)): for every
`X`-valued martingale `Y` with `Y₀ = 0` and every predictable sequence of unimodular `λ_k ∈ ℂ`,
`‖Σ_{k<n} λ_{k+1} (Y_{k+1} − Y_k)‖_{L^p} ≤ β ‖Y_n‖_{L^p}`. -/
def IsComplexUMDBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (p : ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (ℱ : MeasureTheory.Filtration ℕ mΩ) (Y : ℕ → Ω → X)
    (c : ℕ → Ω → ℂ),
    MeasureTheory.Martingale Y ℱ μ → (∀ ω, Y 0 ω = 0) → (∀ n ω, ‖c n ω‖ = 1) →
      (∀ k, @MeasureTheory.StronglyMeasurable _ _ _ (ℱ k) (c (k + 1))) →
      ∀ n, MeasureTheory.eLpNorm
          (fun ω => ∑ k ∈ Finset.range n, c (k + 1) ω • (Y (k + 1) ω - Y k ω))
          (ENNReal.ofReal p) μ ≤ β * MeasureTheory.eLpNorm (Y n) (ENNReal.ofReal p) μ

/-- `UMD_{ℂ,p} (X)` (Proposition 2.7 (5)): the best complex `UMD_p` constant (`∞` if none). -/
noncomputable def complexUMDConst (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (p : ℝ) : ℝ≥0∞ :=
  sInf {β | IsComplexUMDBound X p β}

/-- **Proposition 2.7 (3)** (`prop:umd`), citing Pisier, *Martingales in Banach spaces* (2016),
Corollary 5.22: for every measure space and `p ∈ (1, ∞)`, the complex `L^p` is a UMD space,
`UMD_p (L^p (μ)) < ∞`. -/
def PisierLpUMD : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ⊤ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω),
      umdConst (MeasureTheory.Lp ℂ p μ) p.toReal < ⊤

/-- **Proposition 2.7 (5)** (`prop:umd`), citing Yaroslavtsev, *Even Fourier multipliers and
martingale transforms in infinite dimensions*, Indag. Math. 29 (2018), Lemma 3.2: for a complex
Banach space `X` and `p ∈ (1, ∞)`, `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`. -/
def YaroslavtsevComplexUMD : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p →
    umdConst X p ≤ complexUMDConst X p ∧
      complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p

end Cassese
