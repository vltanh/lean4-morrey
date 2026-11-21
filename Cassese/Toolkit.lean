module

public import Cassese.Defs
public import External.KinderlehrerPedregal.Formula
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Section 2: the toolkit

The definitions of Section 2 that the paper's statements use, and the paper's statements of
Section 2 that are not quoted from the literature. The results that Section 2 quotes are stated
where their statements can live:

* Lemma 2.1 (`cs-lem2.1`): `External.Rindler.lemma5_6` (to be proved);
* Lemma 2.2 (`cs-lem2.2`): `External.Rindler.rankOneConvex_of_quasiconvex`,
  `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic` (to be
  proved);
* Proposition 2.2 (`cs-prop2.2`): `External.KinderlehrerPedregal.DacorognaFormula` (hypothesis);
* Theorem 2.3 (`cs-thm2.3`): `BurkholderInequality`, `BurkholderSquareFunction` (hypotheses, in
  the shared block of `Cassese/Defs.lean`, because the main theorems assume them);
* Proposition 2.6 (`cs-prop2.6`): `External.Osekowski.HilbertCharacterization` (context only);
* Definition 2.5: `umdConst`, `umdConstWith`, `complexUMDConst` (shared block);
* Proposition 2.7 (`prop:umd`): `HNVWExtrapolation` (1), `RandrianantoaninaSchattenUMD` (2),
  `PisierLpUMD` (3), `YaroslavtsevComplexUMD` (5) (hypotheses, shared block), and
  `HNVWDyadicUMD` (4), `HNVWZigZag` (6) (here; used only in Remark 4.1);
* Proposition 2.8 (`cs-prop2.8`): `CoxVeraarDecoupling` (hypothesis, shared block).

Definitions here:

* `IsPosPHomogeneous`: `f (t A) = t^p f (A)` for `t > 0` (Section 1.3);
* `RankOneConvexAt` (Definition 2.2): a rank-one convex integrand `g ≤ f` with `g (A₀) = f (A₀)`;
* `rcEnvelope`, `qcEnvelope` (Definition 2.3), with values in `EReal` (`⊥` when there is no
  minorant, the paper's "identically `−∞`");
* `IsPrelaminate`, `IsDyadicPrelaminate` (Definition 2.4) and `IsBarycentre`;
* rank-one Rademacher martingales (Section 2.2): `IsRankOneIncrements` and `radMart`; a
  martingale of horizon `N` is given by its start `M₀` and predictable increments
  `dM_{k+1} = ε_k A_k (ε₀, …, ε_{k−1})` of rank at most one, on the canonical space of `N` fair
  signs; `Rad₁ (A)` is the set of those with `M₀ = A`;
* `rcThreshold`, `qcThreshold`: the thresholds `C^{rc}`, `C^{qc}` of a family `C ↦ f_C` (Sections 1
  and 3): the infimum, in `[0, ∞]`, of the `C ≥ 0` for which `f_C` is rank-one convex
  (quasiconvex) at `0`;
* `hessian`, `HessianQuasiconvexAt` (Corollaries 5.4 and 6.1; the paper does not define the
  notion, see the docstring).

Reading of Definition 2.4 (inventory E10): the splitting rule applies to any decomposition
`μ = c δ_{A₀} + ν` of a prelaminate, repeated atoms allowed (`c` need not be the whole mass of
`μ` at `A₀`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-- Positive `p`-homogeneity (Section 1.3): `f (t A) = t^p f (A)` for every `t > 0`. -/
def IsPosPHomogeneous (p : ℝ) (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ A : Matrix (Fin d) (Fin m) ℝ, f (t • A) = t ^ p * f A

/-- Rank-one convexity at a matrix `A₀` (Definition 2.2): there is a rank-one convex integrand
`g ≤ f` with `g (A₀) = f (A₀)`. -/
def RankOneConvexAt (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A₀ : Matrix (Fin d) (Fin m) ℝ) : Prop :=
  ∃ g : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand g ∧ RankOneConvex g ∧ (∀ B, g B ≤ f B) ∧
    g A₀ = f A₀

/-- The rank-one convex envelope (Definition 2.3): `f^{rc} (A) = sup {g (A) : g ≤ f, g rank-one
convex}`, over rank-one convex integrands `g`; `⊥` when there is no such `g`. -/
noncomputable def rcEnvelope (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    EReal :=
  ⨆ (g : Matrix (Fin d) (Fin m) ℝ → ℝ) (_ : IsIntegrand g ∧ RankOneConvex g ∧ ∀ B, g B ≤ f B),
    (g A : EReal)

/-- The quasiconvex envelope (Definition 2.3): `f^{qc} (A) = sup {g (A) : g ≤ f, g quasiconvex}`,
over quasiconvex integrands `g`; `⊥` when there is no such `g`. -/
noncomputable def qcEnvelope (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    EReal :=
  ⨆ (g : Matrix (Fin d) (Fin m) ℝ → ℝ) (_ : IsIntegrand g ∧ Quasiconvex g ∧ ∀ B, g B ≤ f B),
    (g A : EReal)

/-- Prelaminates (Definition 2.4): the smallest family of probability measures on `ℝ^{d×m}`
that contains every Dirac mass and is closed under splitting an atom: if `μ = c δ_{A₀} + ν` is a
prelaminate, `R` has rank one and `t ∈ (0, 1)`, then
`t c δ_{A₀ + (1−t) R} + (1 − t) c δ_{A₀ − t R} + ν` is a prelaminate. -/
inductive IsPrelaminate : Measure (Matrix (Fin d) (Fin m) ℝ) → Prop
  | dirac (A : Matrix (Fin d) (Fin m) ℝ) : IsPrelaminate (Measure.dirac A)
  | split {μ ν : Measure (Matrix (Fin d) (Fin m) ℝ)} {c : ℝ≥0∞} {A₀ R : Matrix (Fin d) (Fin m) ℝ}
      {t : ℝ} : IsPrelaminate μ → μ = c • Measure.dirac A₀ + ν → R.rank = 1 → 0 < t → t < 1 →
      IsPrelaminate (ENNReal.ofReal t • c • Measure.dirac (A₀ + (1 - t) • R) +
        ENNReal.ofReal (1 - t) • c • Measure.dirac (A₀ - t • R) + ν)

/-- Dyadic prelaminates (Definition 2.4): obtained from a Dirac mass by splittings with
`t = 1/2`. -/
inductive IsDyadicPrelaminate : Measure (Matrix (Fin d) (Fin m) ℝ) → Prop
  | dirac (A : Matrix (Fin d) (Fin m) ℝ) : IsDyadicPrelaminate (Measure.dirac A)
  | split {μ ν : Measure (Matrix (Fin d) (Fin m) ℝ)} {c : ℝ≥0∞} {A₀ R : Matrix (Fin d) (Fin m) ℝ} :
      IsDyadicPrelaminate μ → μ = c • Measure.dirac A₀ + ν → R.rank = 1 →
      IsDyadicPrelaminate (ENNReal.ofReal (1 / 2) • c • Measure.dirac (A₀ + (1 / 2 : ℝ) • R) +
        ENNReal.ofReal (1 / 2) • c • Measure.dirac (A₀ - (1 / 2 : ℝ) • R) + ν)

/-- `A` is the barycentre of `μ`: `∫ X dμ (X) = A`, entrywise. -/
def IsBarycentre (μ : Measure (Matrix (Fin d) (Fin m) ℝ)) (A : Matrix (Fin d) (Fin m) ℝ) :
    Prop :=
  ∀ i j, ∫ X, X i j ∂μ = A i j

/-- Increments of a rank-one Rademacher martingale of horizon `N` (Section 2.2): predictable
(`A k` depends only on the signs `ε j`, `j < k`) and of rank at most one. -/
def IsRankOneIncrements {N : ℕ} (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ) :
    Prop :=
  IsPredictable A ∧ ∀ k ε, (A k ε).rank ≤ 1

/-- The rank-one Rademacher martingale with start `M₀` and increments `A` at time `n`:
`M_n = M₀ + Σ_{k<n} ε_k A_k`. -/
noncomputable def radMart {N : ℕ} (M₀ : Matrix (Fin d) (Fin m) ℝ)
    (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ) (n : ℕ) (ε : Fin N → Bool) :
    Matrix (Fin d) (Fin m) ℝ :=
  M₀ + mart A n ε

/-- The threshold `C^{rc}` of a family `C ↦ f_C` for rank-one convexity at `0`: the infimum of
the `C ≥ 0` for which `f_C` is rank-one convex at `0` (`∞` if there is none). -/
noncomputable def rcThreshold (F : ℝ → Matrix (Fin d) (Fin m) ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ (C : ℝ) (_ : 0 ≤ C ∧ RankOneConvexAt (F C) 0), ENNReal.ofReal C

/-- The threshold `C^{qc}` of a family `C ↦ f_C` for quasiconvexity at `0`: the infimum of the
`C ≥ 0` for which `f_C` is quasiconvex at `0` (`∞` if there is none). -/
noncomputable def qcThreshold (F : ℝ → Matrix (Fin d) (Fin m) ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ (C : ℝ) (_ : 0 ≤ C ∧ QuasiconvexAt (F C) 0), ENNReal.ofReal C

/-- The Hessian matrix `D²φ (x)` of `φ : ℝ^n → ℝ`. -/
noncomputable def hessian {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fun y => fderiv ℝ φ y (Pi.single j 1)) x (Pi.single i 1)

/-- Hessian quasiconvexity at `A` (Corollaries 5.4 and 6.1). The paper does not define it; it
cites Šverák 1992, Faraco–Zhong 2003, Dal Maso–Fonseca–Leoni–Morini 2004 and Guerra 2026. Reading:
`F (A) ≤ ∫_{(0,1)^n} F (A + D²φ)` for every smooth `φ` with compact support in the open unit cube
for which the integral exists (the second-order analogue of Definition 2.1). -/
def HessianQuasiconvexAt {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ unitCube n → IntegrableOn (fun x => F (A + hessian φ x)) (unitCube n) →
      F A ≤ ∫ x in unitCube n, F (A + hessian φ x)

/-- **Proposition 2.1** (`prop:rk1envelope`): for a continuous integrand `f`,
`f^{rc} (A) = inf_{μ ∈ 𝒫ℒ(A)} ∫ f dμ`, the infimum over the prelaminates with barycentre `A`.
Quoted from Pedregal 1993 (Section 4) and Dacorogna 2008 (Theorem 6.10), whose proofs assume `f`
bounded below; Remark 2.1 removes the assumption and notes that the proposition also follows from
Proposition 2.4. -/
theorem proposition2_1 {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    rcEnvelope f A =
      ⨅ (μ : Measure (Matrix (Fin d) (Fin m) ℝ)) (_ : IsPrelaminate μ ∧ IsBarycentre μ A),
        ((∫ X, f X ∂μ : ℝ) : EReal) := by
  sorry

/-- **Consequence of Proposition 2.2** (`cs-qc-minorant`, line 559): for a continuous integrand
`f`, quasiconvexity at `A` is equivalent to the existence of a quasiconvex minorant `g ≤ f` with
`g (A) = f (A)`. Conditional on Dacorogna's formula (Kinderlehrer–Pedregal). -/
theorem quasiconvexAt_iff_exists_minorant
    (hKP : External.KinderlehrerPedregal.DacorognaFormula)
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) (A : Matrix (Fin d) (Fin m) ℝ) :
    QuasiconvexAt f A ↔
      ∃ g : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand g ∧ Quasiconvex g ∧ (∀ B, g B ≤ f B) ∧
        g A = f A := by
  sorry

/-- **Proposition 2.3 (a)** (`prop:envelope`): for `p ∈ (1, ∞)` and a continuous `f` that is
`p`-homogeneous or positively `p`-homogeneous, each of `f^{rc}`, `f^{qc}` is either identically
`−∞` or finite-valued, and in the second case it has the same type of homogeneity as `f`. -/
theorem proposition2_3_a {p : ℝ} (hp : 1 < p) {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Continuous f) (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) :
    ((∀ A, rcEnvelope f A = ⊥) ∨
      ((∀ A, rcEnvelope f A ≠ ⊥ ∧ rcEnvelope f A ≠ ⊤) ∧
        (IsPHomogeneous p f → IsPHomogeneous p fun A => (rcEnvelope f A).toReal) ∧
        (IsPosPHomogeneous p f → IsPosPHomogeneous p fun A => (rcEnvelope f A).toReal))) ∧
    ((∀ A, qcEnvelope f A = ⊥) ∨
      ((∀ A, qcEnvelope f A ≠ ⊥ ∧ qcEnvelope f A ≠ ⊤) ∧
        (IsPHomogeneous p f → IsPHomogeneous p fun A => (qcEnvelope f A).toReal) ∧
        (IsPosPHomogeneous p f → IsPosPHomogeneous p fun A => (qcEnvelope f A).toReal))) := by
  sorry

/-- **Proposition 2.3 (b)** (`prop:envelope`): for `p ∈ (1, ∞)` and a continuous `f` on
`ℝ^{d×d}` that is `p`-homogeneous or positively `p`-homogeneous, both envelopes preserve
conjugation invariance, and the rank-one convex envelope preserves transposition invariance. -/
theorem proposition2_3_b {p : ℝ} (hp : 1 < p) {f : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hf : Continuous f) (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) :
    (IsConjugationInvariant f →
      (∀ U ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∀ A, rcEnvelope f (U * A * Uᵀ) = rcEnvelope f A) ∧
      (∀ U ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∀ A, qcEnvelope f (U * A * Uᵀ) = qcEnvelope f A)) ∧
    (IsTranspositionInvariant f → ∀ A, rcEnvelope f Aᵀ = rcEnvelope f A) := by
  sorry

/-- **Proposition 2.3 (c)** (`prop:envelope`): for `p ∈ (1, ∞)` and a continuous `f` that is
`p`-homogeneous or positively `p`-homogeneous and rank-one convex at `0`, `f^{rc}` is
quasiconvex at `0` if and only if `f` is. Conditional on Dacorogna's formula, which the
implication "`f` quasiconvex at `0` ⇒ `f^{rc}` quasiconvex at `0`" needs (line 559); the other
implication is `proposition2_3_c_left`. (`f^{rc}` is finite when `f` is rank-one convex at `0`,
and is read through `EReal.toReal`.) -/
theorem proposition2_3_c (hKP : External.KinderlehrerPedregal.DacorognaFormula) {p : ℝ}
    (hp : 1 < p) {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) (hrc : RankOneConvexAt f 0) :
    QuasiconvexAt (fun A => (rcEnvelope f A).toReal) 0 ↔ QuasiconvexAt f 0 := by
  sorry

/-- **Proposition 2.3 (c)** (`prop:envelope`), the implication that the main theorems use: if `f`
is rank-one convex at `0` and `f^{rc}` is quasiconvex at `0`, then so is `f`. -/
theorem proposition2_3_c_left {p : ℝ} (hp : 1 < p) {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Continuous f) (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f)
    (hrc : RankOneConvexAt f 0) (hqc : QuasiconvexAt (fun A => (rcEnvelope f A).toReal) 0) :
    QuasiconvexAt f 0 := by
  sorry

/-- **Consequence of Proposition 2.3** (`cs-envelope-cons`, lines 573–575): for `p ∈ (1, ∞)` and a
continuous `f` that is `p`-homogeneous or positively `p`-homogeneous,
`f^{rc} (0), f^{qc} (0) ∈ {0, −∞}`. -/
theorem envelope_zero {p : ℝ} (hp : 1 < p) {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Continuous f) (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) :
    (rcEnvelope f 0 = 0 ∨ rcEnvelope f 0 = ⊥) ∧ (qcEnvelope f 0 = 0 ∨ qcEnvelope f 0 = ⊥) := by
  sorry

/-- **Consequence of Proposition 2.3** (`cs-envelope-cons`, lines 577–578): for `p ∈ (1, ∞)` and a
continuous `f` that is `p`-homogeneous or positively `p`-homogeneous, rank-one convexity at any
matrix implies rank-one convexity at `0`. -/
theorem rankOneConvexAt_zero_of_rankOneConvexAt {p : ℝ} (hp : 1 < p)
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) {A : Matrix (Fin d) (Fin m) ℝ}
    (hA : RankOneConvexAt f A) : RankOneConvexAt f 0 := by
  sorry

/-- **Consequence of Proposition 2.3** (`cs-envelope-cons`, lines 577–578 and 206–209): for
`p ∈ (1, ∞)` and a continuous `f` that is `p`-homogeneous or positively `p`-homogeneous,
quasiconvexity at any matrix implies quasiconvexity at `0`. Stated without the hypothesis of
Dacorogna's formula, through which the paper's envelope argument would pass: the scaling
argument `∫ f (A + λ∇φ) = λ^p ∫ f (A/λ + ∇φ)` does not need it. -/
theorem quasiconvexAt_zero_of_quasiconvexAt {p : ℝ} (hp : 1 < p)
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) {A : Matrix (Fin d) (Fin m) ℝ}
    (hA : QuasiconvexAt f A) : QuasiconvexAt f 0 := by
  sorry

/-- **Consequence of Proposition 2.3** (`cs-envelope-cons`, lines 206–209): for continuous
(positively) homogeneous integrands, failure of quasiconvexity at `0` implies failure at every
matrix. -/
theorem nowhereQuasiconvex_of_not_quasiconvexAt_zero {p : ℝ} (hp : 1 < p)
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) (h0 : ¬ QuasiconvexAt f 0) :
    NowhereQuasiconvex f := by
  sorry

/-- **Proposition 2.4** (`prop:rk1rad`): for a continuous integrand `f` and every `A`,
`inf_{μ ∈ 𝒫ℒ_{dyad}(A)} ⟨f, μ⟩ = f^{rc} (A)` (both sides may be `−∞`). -/
theorem proposition2_4 {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    ⨅ (μ : Measure (Matrix (Fin d) (Fin m) ℝ)) (_ : IsDyadicPrelaminate μ ∧ IsBarycentre μ A),
        ((∫ X, f X ∂μ : ℝ) : EReal) = rcEnvelope f A := by
  sorry

/-- **Proposition 2.5** (`prop:rankonerademacher`): a continuous integrand `f` is rank-one convex
at `0` if and only if `f (0) ≤ E f (M_N)` for every finite rank-one Rademacher martingale `M`
started at `0`. -/
theorem proposition2_5 {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) :
    RankOneConvexAt f 0 ↔
      ∀ (N : ℕ) (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ),
        IsRankOneIncrements A → f 0 ≤ avg fun ε => f (radMart 0 A N ε) := by
  sorry

/-- `β` bounds the `±1`-transforms of dyadic (Paley–Walsh) martingales with values in the
Banach space `X`: `‖Σ_{k<n} σ_k ε_k ξ_k‖_{L^p} ≤ β ‖Σ_{k<n} ε_k ξ_k‖_{L^p}` for predictable `ξ_k`
and predictable signs `σ_k`. -/
def IsDyadicUMDBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (p : ℝ)
    (β : ℝ≥0∞) : Prop :=
  ∀ (N : ℕ) (ξ : Fin N → (Fin N → Bool) → X) (σ : Fin N → (Fin N → Bool) → ℝ),
    IsPredictable ξ → IsPredictable σ → (∀ k ε, σ k ε = 1 ∨ σ k ε = -1) → ∀ n : ℕ,
      ENNReal.ofReal (lpNormWith (fun x => ‖x‖) p (mart (fun k ε => σ k ε • ξ k ε) n)) ≤
        β * ENNReal.ofReal (lpNormWith (fun x => ‖x‖) p (mart ξ n))

/-- The dyadic `UMD_p` constant `UMD_p^{dyad} (X)`. -/
noncomputable def dyadicUMDConst (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (p : ℝ) :
    ℝ≥0∞ :=
  sInf {β | IsDyadicUMDBound X p β}

/-- **Proposition 2.7 (4)** (`prop:umd`), citing HNVW I, Theorem 4.2.5: restricting (4) to dyadic
martingales gives the same optimal constant, `UMD_p^{dyad} (X) = UMD_p (X)`. Used only in
Remark 4.1; a proposition with no proof (class X), a hypothesis of no statement. -/
def HNVWDyadicUMD : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (p : ℝ), 1 < p →
    dyadicUMDConst X p = umdConst X p

/-- `U : X × X → ℝ` is zig-zag concave for the obstacle `‖y‖^p − β^p ‖x‖^p` (real scalars):
`z ↦ U (x + z, y + ε z)` is concave for every `ε ∈ [−1, 1]`, `U (0, 0) = 0`, and
`U (x, y) ≥ ‖y‖^p − β^p ‖x‖^p`. -/
def IsZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (p β : ℝ)
    (U : X → X → ℝ) : Prop :=
  (∀ (x y : X) (ε : ℝ), |ε| ≤ 1 → ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + ε • z)) ∧
    U 0 0 = 0 ∧ ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y

/-- The complex version: `ε` ranges over the closed unit disc. -/
def IsComplexZigZagConcave {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (p β : ℝ)
    (U : X → X → ℝ) : Prop :=
  (∀ (x y : X) (ε : ℂ), ‖ε‖ ≤ 1 → ConcaveOn ℝ Set.univ fun z : X => U (x + z) (y + ε • z)) ∧
    U 0 0 = 0 ∧ ∀ x y : X, ‖y‖ ^ p - β ^ p * ‖x‖ ^ p ≤ U x y

/-- **Proposition 2.7 (6)** (`prop:umd`), citing HNVW I, Theorem 4.5.6, and Yaroslavtsev,
Proposition 3.7: a Banach space `X` is `UMD_p` if and only if there is a zig-zag concave `U` for
some `β > 0`; then `β ≥ UMD_p (X)`, and `β ≥ UMD_{ℂ,p} (X)` when `X` is complex and `U` is
zig-zag concave in the complex sense. Not used in any proof; a proposition with no proof
(class X), a hypothesis of no statement. -/
def HNVWZigZag : Prop :=
  (∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (p : ℝ), 1 < p →
    (umdConst X p < ⊤ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsZigZagConcave p β U) ∧
    ∀ (β : ℝ) (U : X → X → ℝ), 0 < β → IsZigZagConcave p β U →
      umdConst X p ≤ ENNReal.ofReal β) ∧
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p →
    ∀ (β : ℝ) (U : X → X → ℝ), 0 < β → IsComplexZigZagConcave p β U →
      complexUMDConst X p ≤ ENNReal.ofReal β

end Cassese
