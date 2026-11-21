module

public import Cassese.Toolkit
public import External.Dacorogna.Minors
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Section 5: the problem in dimension `2 × 3`

The objects of Sections 5.1–5.2 that Corollary 5.3 names (`wirtAlpha`, `wirtBeta`, `zCoord`,
`quarticQ`, `calL`, `embedJ`, `L3`, `q3`, `projL3`, `qDeltaLambda`, `qHat`) are in the shared block
of `Cassese/Defs.lean`. In this section `|·|` is the Frobenius norm (`frobNorm`) and
`⟨A, B⟩ = Σ A_{ij} B_{ij}` the Frobenius inner product (`frobInner`).

Lemma 5.1 is stated for a subspace `L` and a map `π` with the defining property of the orthogonal
projection onto `L` (`IsFrobProj`); functions "on `L`" are functions on `ℝ^{d×m}` of which only the
values on `L` matter (every function on `L` is the restriction of one, for instance of `f ∘ π`),
and "`C²` away from the origin" is read on `f ∘ π`, which is `C²` on `{π A ≠ 0}` exactly when
`f|_L` is `C²` on `L ∖ {0}`. An `L`-valued rank-one Rademacher martingale is one whose increments
lie in `L`.

Statements not numbered in the paper: the claims of Sections 5.1–5.2 that `q` and `q₃` are
rank-one convex on `𝓛` and `𝓛₃` (`cs-q-rc`, `cs-q3-rc`); equation (24) (`eq:q-simp`); and two
claims of the proof of Theorem 1.3, that `𝓛₃` satisfies (25) with `κ = 2` (`cs-kappa`, asserted
without proof in the paper) and that `q_{δ, K/δ}` is rank-one convex (`cs-qdl-rc`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-- The Frobenius inner product `⟨A, B⟩ = Σ A_{ij} B_{ij}`. -/
def frobInner (A B : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- The Frobenius norm `|A| = (Σ A_{ij}²)^{1/2}`. -/
noncomputable def frobNorm (A : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  √(frobSq A)

/-- `π` is the orthogonal projection onto `L` for the Frobenius inner product: `π A ∈ L` and
`A − π A ⊥ L` for every `A`. -/
def IsFrobProj (L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ))
    (π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ) : Prop :=
  ∀ A, π A ∈ L ∧ ∀ B ∈ L, frobInner (A - π A) B = 0

/-- Hypothesis (25) of Lemma 5.1: for every rank-one `R` there is a rank-one `R_L ∈ L` with
`|π R − R_L| ≤ κ |π^⊥ R|`. -/
def HasRankOneCorrection (L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ))
    (π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ) (κ : ℝ) : Prop :=
  ∀ R : Matrix (Fin d) (Fin m) ℝ, R.rank = 1 →
    ∃ RL ∈ L, RL.rank = 1 ∧ frobNorm (π R - RL) ≤ κ * frobNorm (R - π R)

/-- `projL3 A` lies in `𝓛₃`. -/
theorem projL3_mem (A : Matrix (Fin 2) (Fin 3) ℝ) : projL3 A ∈ L3 := by
  show wirtBeta (embedJ (projL3 A)) 2 3 = starRingEnd ℂ (wirtAlpha (embedJ (projL3 A)) 0 1)
  simp only [embedJ, projL3, wirtBeta, wirtAlpha, Matrix.of_apply]
  rw [Complex.ext_iff]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  norm_num
  constructor <;> ring

/-- `A − projL3 A` is orthogonal to `𝓛₃`: `projL3` is the orthogonal projection onto `𝓛₃`. -/
theorem projL3_orthogonal (A B : Matrix (Fin 2) (Fin 3) ℝ) (hB : B ∈ L3) :
    frobInner (A - projL3 A) B = 0 := by
  change wirtBeta (embedJ B) 2 3 = starRingEnd ℂ (wirtAlpha (embedJ B) 0 1) at hB
  simp only [embedJ, wirtBeta, wirtAlpha, Matrix.of_apply] at hB
  rw [Complex.ext_iff] at hB
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im] at hB
  norm_num at hB
  obtain ⟨h1, h2⟩ := hB
  simp [frobInner, projL3, Fin.sum_univ_succ]
  linear_combination (A 0 2 - A 0 0 - A 1 1) / 3 * h1 + 2 * ((A 1 2 - A 0 1 + A 1 0) / 3) * h2

/-- `A = (a b e; c d f)` lies in `𝓛₃` exactly when `e = a + d` and `f = b − c`. -/
theorem mem_L3_iff (A : Matrix (Fin 2) (Fin 3) ℝ) :
    A ∈ L3 ↔ A 0 2 = A 0 0 + A 1 1 ∧ A 1 2 = A 0 1 - A 1 0 := by
  change wirtBeta (embedJ A) 2 3 = starRingEnd ℂ (wirtAlpha (embedJ A) 0 1) ↔ _
  simp only [embedJ, wirtBeta, wirtAlpha, Matrix.of_apply]
  rw [Complex.ext_iff]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  constructor
  · rintro ⟨h1, h2⟩
    norm_num at h1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    norm_num
    constructor <;> linarith

/-- The subspace `𝓛₃` as a submodule of `ℝ^{2×3}`, with carrier `L3` (`coe_L3Submodule`), so
that Lemma 5.1, which takes a submodule, applies to it. -/
def L3Submodule : Submodule ℝ (Matrix (Fin 2) (Fin 3) ℝ) where
  carrier := L3
  add_mem' {A B} hA hB := by
    rw [mem_L3_iff] at hA hB ⊢
    simp only [Matrix.add_apply]
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  zero_mem' := by
    rw [mem_L3_iff]
    simp
  smul_mem' c A hA := by
    rw [mem_L3_iff] at hA ⊢
    simp only [Matrix.smul_apply, smul_eq_mul, hA.1, hA.2]
    constructor <;> ring

/-- The carrier of `L3Submodule` is `L3`. -/
theorem coe_L3Submodule : (L3Submodule : Set (Matrix (Fin 2) (Fin 3) ℝ)) = L3 := rfl

theorem mem_L3Submodule {A : Matrix (Fin 2) (Fin 3) ℝ} : A ∈ L3Submodule ↔ A ∈ L3 := Iff.rfl

/-- `projL3` is the orthogonal projection onto `𝓛₃`, in the sense of Lemma 5.1. -/
theorem isFrobProj_projL3 : IsFrobProj L3Submodule projL3 :=
  fun A => ⟨projL3_mem A, fun B hB => projL3_orthogonal A B hB⟩

/-- **Section 5.1** (`cs-q-rc`, lines 1550–1555): `q` is globally rank-one convex on `𝓛`: for
`A ∈ 𝓛` and rank-one `R ∈ 𝓛`, `t ↦ q (A + t R)` is convex. -/
theorem quarticQ_rankOneConvexOn_calL (A R : Matrix (Fin 2) (Fin 4) ℝ) (hA : A ∈ calL)
    (hR : R ∈ calL) (hR1 : R.rank = 1) :
    ConvexOn ℝ Set.univ fun t : ℝ => quarticQ (A + t • R) := by
  sorry

/-- **Section 5.2** (`cs-q3-rc`, lines 1573–1574): `q₃` is globally rank-one convex on `𝓛₃`. -/
theorem q3_rankOneConvexOn_L3 (A R : Matrix (Fin 2) (Fin 3) ℝ) (hA : A ∈ L3) (hR : R ∈ L3)
    (hR1 : R.rank = 1) :
    ConvexOn ℝ Set.univ fun t : ℝ => q3 (A + t • R) := by
  sorry

/-- **Equation (24)** (`eq:q-simp`): on `𝓛₃`, `q₃ (A) = −det (A diag (1, 1, −1) Aᵀ)`. -/
theorem equation24 (A : Matrix (Fin 2) (Fin 3) ℝ) (hA : A ∈ L3) :
    q3 A = -(A * Matrix.diagonal (![1, 1, -1] : Fin 3 → ℝ) * Aᵀ).det := by
  sorry

/-- **Proposition 5.1** (`cs-prop5.1`): a polynomial `P : ℝ^{d×m} → ℝ` of degree at most `3` that
is rank-one convex at `0` is quasiconvex. Conditional on Dacorogna's Theorem 5.20 (rank-one
affine functions are affine combinations of minors), which its proof uses. -/
theorem proposition5_1 (hD : External.Dacorogna.RankOneAffineMinors)
    (P : MvPolynomial (Fin d × Fin m) ℝ) (hP : P.totalDegree ≤ 3)
    (hrc : RankOneConvexAt (fun A => MvPolynomial.eval (fun ij => A ij.1 ij.2) P) 0) :
    Quasiconvex fun A : Matrix (Fin d) (Fin m) ℝ =>
      MvPolynomial.eval (fun ij => A ij.1 ij.2) P := by
  sorry

/-- **Proposition 5.2** (`prop:qc-witness`, an (almost) quasiconvexity witness): there is a smooth
bounded `u : ℝ³ → ℝ²` with `∇u (x) ∈ 𝓛₃` and `q₃ (∇u (x)) < 0` for every `x`,
`q₃ (∇u) ∈ L¹ (ℝ³)`, and `∫_{B_R} |∇u|⁴ ≲ log (2 + R)` (Euclidean balls `B_R`, `R ≥ 0`). -/
theorem proposition5_2 :
    ∃ u : (Fin 3 → ℝ) → Fin 2 → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧
      (∃ M : ℝ, ∀ x, ‖u x‖ ≤ M) ∧ (∀ x, jac u x ∈ L3) ∧ (∀ x, q3 (jac u x) < 0) ∧
      Integrable (fun x => q3 (jac u x)) ∧
      ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
        ∫ x in {x : Fin 3 → ℝ | ∑ i, x i ^ 2 < R ^ 2}, frobSq (jac u x) ^ 2 ≤
          C * Real.log (2 + R) := by
  sorry

/-- **Lemma 5.1 (1)** (`lem:extension-from-subspace`, extension from a subspace): let `π` be the
orthogonal projection onto a subspace `L ⊆ ℝ^{d×m}` satisfying (25) for some `κ`. Let `p > 1` and
let `g` be continuous and positively `p`-homogeneous on `L`, with `E g (M_n) ≥ η E |M_n|^p` for
some `η > 0` and every `L`-valued rank-one Rademacher martingale started at `0`. Then for `Λ`
large enough, `A ↦ g (π A) + Λ^p |π^⊥ A|^p` is rank-one convex at `0`. Conditional on Burkholder's
inequality (Theorem 2.3), which gives (27). -/
theorem lemma5_1_part1 (hB : BurkholderInequality)
    (L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ))
    (π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ) (hπ : IsFrobProj L π) (κ : ℝ)
    (hκ : HasRankOneCorrection L π κ) {p : ℝ} (hp : 1 < p) (g : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (hgc : ContinuousOn g L) (hgh : ∀ t : ℝ, 0 < t → ∀ X ∈ L, g (t • X) = t ^ p * g X)
    {η : ℝ} (hη : 0 < η)
    (hcoer : ∀ (N : ℕ) (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ),
      IsRankOneIncrements A → (∀ k ε, A k ε ∈ L) →
        η * avg (fun ε => frobNorm (radMart 0 A N ε) ^ p) ≤
          avg fun ε => g (radMart 0 A N ε)) :
    ∃ Λ₀ : ℝ, ∀ Λ ≥ Λ₀, RankOneConvexAt (fun A => g (π A) + Λ ^ p * frobNorm (A - π A) ^ p) 0 := by
  sorry

/-- **Lemma 5.1 (2)** (`lem:extension-from-subspace`): with `L`, `π`, `κ` as in (1), let `p ≥ 2`
and let `f` be globally rank-one convex on `L`, `p`-homogeneous, and `C²` away from the origin.
Then there is `c₀ = c₀ (f, L)` such that for every `δ ∈ (0, 1)` and every `Λ ≥ c₀ / δ`, the map
(26) `A ↦ f (π A) + δ (|π A|² + Λ² |π^⊥ A|²)^{p/2}` is globally rank-one convex. Conditional on
Burkholder's inequality (Theorem 2.3), which gives (27). -/
theorem lemma5_1_part2 (hB : BurkholderInequality)
    (L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ))
    (π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ) (hπ : IsFrobProj L π) (κ : ℝ)
    (hκ : HasRankOneCorrection L π κ) {p : ℝ} (hp : 2 ≤ p) (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (hrc : ∀ X ∈ L, ∀ R ∈ L, R.rank = 1 → ConvexOn ℝ Set.univ fun t : ℝ => f (X + t • R))
    (hhom : ∀ (t : ℝ), ∀ X ∈ L, f (t • X) = |t| ^ p * f X)
    (hC2 : ContDiffOn ℝ 2 (fun X : Fin d → Fin m → ℝ => f (π (Matrix.of X)))
      {X | π (Matrix.of X) ≠ 0}) :
    ∃ c₀ : ℝ, ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ Λ : ℝ, c₀ / δ ≤ Λ →
      RankOneConvex fun A =>
        f (π A) + δ * (frobSq (π A) + Λ ^ 2 * frobSq (A - π A)) ^ (p / 2) := by
  sorry

/-- **Proof of Theorem 1.3** (`cs-kappa`, line 1978): `𝓛₃` satisfies hypothesis (25) of Lemma 5.1
with `κ = 2`. Asserted without proof in the paper (inventory E5; numerically the best `κ` is about
`1.054`). -/
theorem L3_rankOneCorrection (R : Matrix (Fin 2) (Fin 3) ℝ) (hR : R.rank = 1) :
    ∃ RL ∈ L3, RL.rank = 1 ∧ frobNorm (projL3 R - RL) ≤ 2 * frobNorm (R - projL3 R) := by
  sorry

/-- `𝓛₃` satisfies hypothesis (25) of Lemma 5.1 with `κ = 2`, as a submodule (from
`L3_rankOneCorrection`). -/
theorem hasRankOneCorrection_L3 : HasRankOneCorrection L3Submodule projL3 2 :=
  fun R hR => L3_rankOneCorrection R hR

/-- **Proof of Theorem 1.3** (`cs-qdl-rc`, lines 1980–1991): for a sufficiently large fixed `K`
and every `0 < δ ≤ 1`, `q_{δ, K/δ}` is a globally rank-one convex homogeneous quartic polynomial
(from Lemma 5.1 (2) applied to `q₃` on `𝓛₃`). Conditional on Burkholder's inequality, through
Lemma 5.1. (The text has `0 < δ ≤ 1`; Lemma 5.1 (2) is stated for `δ ∈ (0, 1)`.) -/
theorem qDeltaLambda_rankOneConvex (hB : BurkholderInequality) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K ≥ K₀, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      IsHomogeneousPolynomial 4 (qDeltaLambda δ (K / δ)) ∧
        RankOneConvex (qDeltaLambda δ (K / δ)) := by
  sorry

/-- **Corollary 5.3** (`cor:transp`): for `K` sufficiently large and `δ > 0` sufficiently small,
with `Λ = K/δ`, `q̂_{δ,Λ} (A) = q_{δ,Λ} (Aᵀ)` on `ℝ^{3×2}` is a homogeneous quartic polynomial
which is globally rank-one convex and nowhere quasiconvex. Conditional on Burkholder's inequality
(through the rank-one convexity of `q_{δ,Λ}`, Lemma 5.1 (2)). -/
theorem corollary5_3 (hB : BurkholderInequality) :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      IsHomogeneousPolynomial 4 (qHat δ (K / δ)) ∧ RankOneConvex (qHat δ (K / δ)) ∧
        NowhereQuasiconvex (qHat δ (K / δ)) := by
  sorry

/-- The matrix `B = (1 0 1; 0 1 0)` of Corollary 5.4. -/
def hessB : Matrix (Fin 2) (Fin 3) ℝ := !![1, 0, 1; 0, 1, 0]

/-- **Corollary 5.4** (`cor:hessian-quartic`): for `K` sufficiently large and `δ > 0` sufficiently
small, with `Λ = K/δ`, `h (A) = q_{δ,Λ} (B A)` on `ℝ^{3×3}` is rank-one convex but not Hessian
quasiconvex at `0`. Conditional on Burkholder's inequality (through Lemma 5.1 (2)). -/
theorem corollary5_4 (hB : BurkholderInequality) :
    ∃ K₀ : ℝ, ∀ K ≥ K₀, ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      RankOneConvex (fun A : Matrix (Fin 3) (Fin 3) ℝ => qDeltaLambda δ (K / δ) (hessB * A)) ∧
        ¬ HessianQuasiconvexAt
          (fun A : Matrix (Fin 3) (Fin 3) ℝ => qDeltaLambda δ (K / δ) (hessB * A)) 0 := by
  sorry

end Cassese
