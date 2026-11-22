module

public import Morrey.Cassese.Defs
public import Morrey.Cassese.Rademacher
public import Morrey.Common.External.KinderlehrerPedregal.Formula
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Matrix.Basis
public import Morrey.Common.External.Rindler.Lemmas
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Section 2: the toolkit

The definitions of Section 2 that the paper's statements use, and the paper's statements of
Section 2 that are not quoted from the literature. The results that Section 2 quotes are stated
where their statements can live:

* Lemma 2.1 (`cs-lem2.1`): `External.Rindler.lemma5_6` (proved);
* Lemma 2.2 (`cs-lem2.2`): `External.Rindler.rankOneConvex_of_quasiconvex`,
  `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic`;
* Proposition 2.2 (`cs-prop2.2`): `External.KinderlehrerPedregal.DacorognaFormula` (proved,
  `External.KinderlehrerPedregal.dacorognaFormula_holds`);
* Theorem 2.3 (`cs-thm2.3`): `BurkholderInequality`, `BurkholderSquareFunction` (proved, in
  `Morrey/Cassese/Hypotheses.lean`: `burkholderInequality_holds`,
  `burkholderSquareFunction_holds`);
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

Proofs (after the definitions; the private helpers are prefixed `tk`):

* prelaminates are probability measures for which every function is integrable, their barycentre
  is preserved by the splittings, and rank-one convex functions satisfy Jensen's inequality on them
  (`tk_prelaminate`); dyadic prelaminates are prelaminates and can be glued (`tk_dyadic_glue`,
  `tk_dyadic_mid`);
* Proposition 2.4 by the paper's argument (`tk_midpoint_principle`, with the Bernstein–Doetsch
  theorem `tk_convex_of_midpoint` and Lemma 2.1 for continuity); it is stated before
  Proposition 2.1, which Remark 2.1 derives from it;
* the envelopes as the largest minorants (`tk_rc_cases`, `tk_qc_cases`), and their transformations
  (`tk_rc_transform`, `tk_qc_scale`) for Proposition 2.3 and its consequences;
* public helpers that the later sections share: integrands, derivative matrices and the unit cube
  (`isIntegrand_of_continuous`, `abs_jac_le`, `measurable_jac`, `integrableOn_comp_jac`,
  `volume_unitCube`), the bridges that line 559 needs (`cov_quasiconvexAtOn_unitCube_iff`,
  `cov_qcEnvelope_eq`, see `Bridges`), ranks (`eq_zero_of_rank_eq_zero`, `rank_single_eq_one`),
  the threshold `C^{qc}` (`not_quasiconvexAt_of_lt_qcThreshold`) and homogeneous polynomials
  (`IsHomogeneousPolynomial.add`, `IsHomogeneousPolynomial.continuous`, …);
* rank-one Rademacher martingales: conditioning on the first sign (`tk_avg_cons`,
  `tk_radMart_cons`), the law of `M_N` as a dyadic prelaminate (`tk_law`), and gluing
  (`tk_martVals_mid`) for Proposition 2.5.
-/

@[expose] public section

open MeasureTheory Set
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

/-! ## Proofs

The proofs of Section 2. Helpers are private, with the prefix `tk`. -/

/-! ### Finite combinations of Dirac masses -/

/-- A probability measure on `ℝ^{d×m}` for which every real function is integrable (true of the
finite combinations of Dirac masses, such as the prelaminates). -/
private def tkGood (μ : Measure (Matrix (Fin d) (Fin m) ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ g : Matrix (Fin d) (Fin m) ℝ → ℝ, Integrable g μ

/-- The barycentre `∫ X dμ (X)`, entrywise. -/
private noncomputable def tkBary (μ : Measure (Matrix (Fin d) (Fin m) ℝ)) :
    Matrix (Fin d) (Fin m) ℝ :=
  Matrix.of fun i j => ∫ X, X i j ∂μ

private lemma tk_isBarycentre_iff {μ : Measure (Matrix (Fin d) (Fin m) ℝ)}
    {A : Matrix (Fin d) (Fin m) ℝ} : IsBarycentre μ A ↔ tkBary μ = A := by
  rw [IsBarycentre, ← Matrix.ext_iff]
  rfl

private lemma tk_good_dirac (A : Matrix (Fin d) (Fin m) ℝ) : tkGood (Measure.dirac A) :=
  ⟨inferInstance, fun _ => integrable_dirac enorm_lt_top⟩

private lemma tk_bary_dirac (A : Matrix (Fin d) (Fin m) ℝ) : tkBary (Measure.dirac A) = A := by
  ext i j
  simp [tkBary, integral_dirac]

/-- Splitting part of an atom: the new measure is good, and its integrals. -/
private lemma tk_good_split {μ ν : Measure (Matrix (Fin d) (Fin m) ℝ)} {c : ℝ≥0∞}
    {A₀ A₁ A₂ : Matrix (Fin d) (Fin m) ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hμ : tkGood μ) (he : μ = c • Measure.dirac A₀ + ν) :
    tkGood (ENNReal.ofReal a • c • Measure.dirac A₁ + ENNReal.ofReal b • c • Measure.dirac A₂ +
        ν) ∧
      ∀ g : Matrix (Fin d) (Fin m) ℝ → ℝ,
        ∫ X, g X ∂(ENNReal.ofReal a • c • Measure.dirac A₁ +
            ENNReal.ofReal b • c • Measure.dirac A₂ + ν) =
          ∫ X, g X ∂μ + c.toReal * (a * g A₁ + b * g A₂ - g A₀) := by
  obtain ⟨hprob, hint⟩ := hμ
  have huniv : μ Set.univ = c + ν Set.univ := by
    rw [he]; simp
  have hc : c ≠ ⊤ := by
    have h1 : c ≤ 1 := by
      rw [← measure_univ (μ := μ), huniv]; exact le_self_add
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h1
  have hνle : ν ≤ μ := he ▸ Measure.le_add_left le_rfl
  have hintν : ∀ g : Matrix (Fin d) (Fin m) ℝ → ℝ, Integrable g ν :=
    fun g => (hint g).mono_measure hνle
  have hdir : ∀ (e : ℝ≥0∞) (A : Matrix (Fin d) (Fin m) ℝ) (g : Matrix (Fin d) (Fin m) ℝ → ℝ),
      e ≠ ⊤ → Integrable g (e • c • Measure.dirac A) := fun e A g he' =>
    ((integrable_dirac enorm_lt_top).smul_measure hc).smul_measure he'
  have hint' : ∀ g : Matrix (Fin d) (Fin m) ℝ → ℝ, Integrable g (ENNReal.ofReal a • c •
      Measure.dirac A₁ + ENNReal.ofReal b • c • Measure.dirac A₂ + ν) := fun g =>
    ((hdir _ _ g ENNReal.ofReal_ne_top).add_measure (hdir _ _ g ENNReal.ofReal_ne_top)).add_measure
      (hintν g)
  have hsum : ENNReal.ofReal a * c + ENNReal.ofReal b * c = c := by
    rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]
  refine ⟨⟨⟨?_⟩, hint'⟩, fun g => ?_⟩
  · simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [hsum, ← huniv, measure_univ]
  · have hdi : ∀ (e : ℝ≥0∞) (A : Matrix (Fin d) (Fin m) ℝ),
        ∫ X, g X ∂(e • c • Measure.dirac A) = e.toReal * (c.toReal * g A) := by
      intro e A
      rw [integral_smul_measure, integral_smul_measure, integral_dirac, smul_eq_mul, smul_eq_mul]
    rw [integral_add_measure ((hdir _ _ g ENNReal.ofReal_ne_top).add_measure
      (hdir _ _ g ENNReal.ofReal_ne_top)) (hintν g), integral_add_measure
      (hdir _ _ g ENNReal.ofReal_ne_top) (hdir _ _ g ENNReal.ofReal_ne_top), hdi, hdi,
      ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, he,
      integral_add_measure ((integrable_dirac enorm_lt_top).smul_measure hc) (hintν g),
      integral_smul_measure, integral_dirac, smul_eq_mul]
    ring

/-- The splitting inequality of a rank-one convex function:
`g (A₀) ≤ t g (A₀ + (1 − t) R) + (1 − t) g (A₀ − t R)` for `R` of rank one. -/
private lemma tk_rankOne_split {g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hg : RankOneConvex g)
    {A₀ R : Matrix (Fin d) (Fin m) ℝ} (hR : R.rank = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    g A₀ ≤ t * g (A₀ + (1 - t) • R) + (1 - t) * g (A₀ - t • R) := by
  have hPQ : (A₀ + (1 - t) • R) - (A₀ - t • R) = R := by module
  have key := (hg (A₀ + (1 - t) • R) (A₀ - t • R) (by rw [hPQ]; exact hR)).2
    (x := 1) (y := 0) ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ ht0 (sub_nonneg.2 ht1)
    (by ring)
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero, sub_zero, one_smul, zero_smul,
    sub_self, zero_add] at key
  convert key using 2
  module

/-- Every prelaminate is good, its barycentre is preserved by the splittings, and a rank-one
convex `g` satisfies Jensen's inequality `g (bary μ) ≤ ∫ g dμ` on it (by induction on the
splittings). -/
private lemma tk_prelaminate {μ : Measure (Matrix (Fin d) (Fin m) ℝ)} (h : IsPrelaminate μ) :
    tkGood μ ∧ ∀ g : Matrix (Fin d) (Fin m) ℝ → ℝ, RankOneConvex g →
      g (tkBary μ) ≤ ∫ X, g X ∂μ := by
  induction h with
  | dirac A =>
    refine ⟨tk_good_dirac A, fun g _ => ?_⟩
    rw [tk_bary_dirac, integral_dirac]
  | @split μ ν c A₀ R t hμ he hR ht0 ht1 ih =>
    obtain ⟨hgood, hjen⟩ := ih
    obtain ⟨hgood', hint⟩ := tk_good_split ht0.le (sub_nonneg.2 ht1.le) (by ring) hgood he
      (A₁ := A₀ + (1 - t) • R) (A₂ := A₀ - t • R)
    refine ⟨hgood', fun g hg => ?_⟩
    have hbary : tkBary (ENNReal.ofReal t • c • Measure.dirac (A₀ + (1 - t) • R) +
        ENNReal.ofReal (1 - t) • c • Measure.dirac (A₀ - t • R) + ν) = tkBary μ := by
      ext i j
      simp only [tkBary, Matrix.of_apply]
      rw [hint]
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hbary, hint]
    have h1 := hjen g hg
    have h2 := tk_rankOne_split hg hR ht0.le ht1.le (A₀ := A₀)
    have hc : 0 ≤ c.toReal := ENNReal.toReal_nonneg
    nlinarith

/-- A dyadic prelaminate is a prelaminate (the splittings with `t = 1/2`). -/
private lemma tk_isPrelaminate_of_dyadic {μ : Measure (Matrix (Fin d) (Fin m) ℝ)}
    (h : IsDyadicPrelaminate μ) : IsPrelaminate μ := by
  induction h with
  | dirac A => exact .dirac A
  | split hμ he hR ih =>
    have := IsPrelaminate.split (t := 1 / 2) ih he hR (by norm_num) (by norm_num)
    rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this

/-- Jensen's inequality on prelaminates: for a rank-one convex `h ≤ f` and a prelaminate `μ` with
barycentre `A`, `h (A) ≤ ∫ f dμ`. -/
private lemma tk_jensen {μ : Measure (Matrix (Fin d) (Fin m) ℝ)} (hμ : IsPrelaminate μ)
    {A : Matrix (Fin d) (Fin m) ℝ} (hA : IsBarycentre μ A) {h f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hh : RankOneConvex h) (hhf : ∀ B, h B ≤ f B) : h A ≤ ∫ X, f X ∂μ := by
  obtain ⟨⟨_, hint⟩, hjen⟩ := tk_prelaminate hμ
  rw [tk_isBarycentre_iff] at hA
  rw [← hA]
  exact (hjen h hh).trans (integral_mono (hint h) (hint f) hhf)

/-- The integral against `½ μ + ½ ν` of good measures. -/
private lemma tk_integral_half {μ ν : Measure (Matrix (Fin d) (Fin m) ℝ)} (hμ : tkGood μ)
    (hν : tkGood ν) (g : Matrix (Fin d) (Fin m) ℝ → ℝ) :
    ∫ X, g X ∂(ENNReal.ofReal (1 / 2) • μ + ENNReal.ofReal (1 / 2) • ν) =
      (∫ X, g X ∂μ + ∫ X, g X ∂ν) / 2 := by
  rw [integral_add_measure ((hμ.2 g).smul_measure ENNReal.ofReal_ne_top)
    ((hν.2 g).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by norm_num), smul_eq_mul, smul_eq_mul]
  ring

private lemma tk_good_half {μ ν : Measure (Matrix (Fin d) (Fin m) ℝ)} (hμ : tkGood μ)
    (hν : tkGood ν) : tkGood (ENNReal.ofReal (1 / 2) • μ + ENNReal.ofReal (1 / 2) • ν) := by
  refine ⟨⟨?_⟩, fun g => ((hμ.2 g).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((hν.2 g).smul_measure ENNReal.ofReal_ne_top)⟩
  have h1 := hμ.1.measure_univ
  have h2 := hν.1.measure_univ
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, h1, h2,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Gluing: if `s δ_B + ρ` is a dyadic prelaminate and `μ` is a dyadic prelaminate with
barycentre `B`, then `s μ + ρ` is a dyadic prelaminate (perform the splittings of `μ` on the part
`s δ_B`; repeated atoms are allowed, inventory E10). -/
private lemma tk_dyadic_glue {μ : Measure (Matrix (Fin d) (Fin m) ℝ)}
    (h : IsDyadicPrelaminate μ) :
    ∀ (s : ℝ≥0∞) (ρ : Measure (Matrix (Fin d) (Fin m) ℝ)),
      IsDyadicPrelaminate (s • Measure.dirac (tkBary μ) + ρ) → IsDyadicPrelaminate (s • μ + ρ) := by
  induction h with
  | dirac A =>
    intro s ρ hρ
    rwa [tk_bary_dirac] at hρ
  | @split μ ν c A₀ R hμ he hR ih =>
    intro s ρ hρ
    have hgood := (tk_prelaminate (tk_isPrelaminate_of_dyadic hμ)).1
    obtain ⟨_, hint⟩ := tk_good_split (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) hgood he (A₁ := A₀ + (1 / 2 : ℝ) • R) (A₂ := A₀ - (1 / 2 : ℝ) • R)
    have hbary : tkBary (ENNReal.ofReal (1 / 2) • c • Measure.dirac (A₀ + (1 / 2 : ℝ) • R) +
        ENNReal.ofReal (1 / 2) • c • Measure.dirac (A₀ - (1 / 2 : ℝ) • R) + ν) = tkBary μ := by
      ext i j
      simp only [tkBary, Matrix.of_apply]
      rw [hint]
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hbary] at hρ
    have h1 := ih s ρ hρ
    rw [he, smul_add, smul_smul, add_assoc] at h1
    have h3 := IsDyadicPrelaminate.split h1 rfl hR
    convert h3 using 1
    simp only [smul_add, smul_smul, add_assoc]
    rw [show s * (ENNReal.ofReal (1 / 2) * c) = ENNReal.ofReal (1 / 2) * (s * c) by ring]

/-- A matrix of rank `0` is `0`. -/
theorem eq_zero_of_rank_eq_zero {A : Matrix (Fin d) (Fin m) ℝ} (h : A.rank = 0) :
    A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun F => F (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply] using this

/-- Two half masses at `B` and `C` with `rank (B − C) ≤ 1` form a dyadic prelaminate (a midpoint
split of `δ_{(B+C)/2}` along `B − C`, or nothing to split when `B = C`). -/
private lemma tk_dyadic_two_point {B C : Matrix (Fin d) (Fin m) ℝ} (hBC : (B - C).rank ≤ 1) :
    IsDyadicPrelaminate (ENNReal.ofReal (1 / 2) • Measure.dirac B +
      ENNReal.ofReal (1 / 2) • Measure.dirac C) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hBC with h0 | h1
  · obtain rfl : B = C := sub_eq_zero.1 (eq_zero_of_rank_eq_zero h0)
    rw [← add_smul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
    exact .dirac B
  · set M := (1 / 2 : ℝ) • (B + C)
    have h0 := IsDyadicPrelaminate.split (IsDyadicPrelaminate.dirac M)
      (by simp : Measure.dirac M = (1 : ℝ≥0∞) • Measure.dirac M + 0) h1
    rwa [show M + (1 / 2 : ℝ) • (B - C) = B by simp only [M]; module,
      show M - (1 / 2 : ℝ) • (B - C) = C by simp only [M]; module, one_smul, one_smul,
      add_zero] at h0

/-- The midpoint gluing: `½ μ_B + ½ μ_C` is a dyadic prelaminate with barycentre `(B + C)/2`
when `rank (B − C) ≤ 1` (a midpoint split of `δ_{(B+C)/2}`, followed by the splittings of `μ_B`
and `μ_C`). -/
private lemma tk_dyadic_mid {B C : Matrix (Fin d) (Fin m) ℝ} (hBC : (B - C).rank ≤ 1)
    {μB μC : Measure (Matrix (Fin d) (Fin m) ℝ)} (hB : IsDyadicPrelaminate μB)
    (hbB : tkBary μB = B) (hC : IsDyadicPrelaminate μC) (hbC : tkBary μC = C) :
    IsDyadicPrelaminate (ENNReal.ofReal (1 / 2) • μB + ENNReal.ofReal (1 / 2) • μC) ∧
      tkBary (ENNReal.ofReal (1 / 2) • μB + ENNReal.ofReal (1 / 2) • μC) =
        (1 / 2 : ℝ) • (B + C) := by
  have h0 := tk_dyadic_two_point hBC
  have h1 := tk_dyadic_glue hB (ENNReal.ofReal (1 / 2)) (ENNReal.ofReal (1 / 2) • Measure.dirac C)
    (hbB ▸ h0)
  rw [add_comm] at h1
  have h2 := tk_dyadic_glue hC (ENNReal.ofReal (1 / 2)) (ENNReal.ofReal (1 / 2) • μB)
    (hbC ▸ h1)
  rw [add_comm] at h2
  refine ⟨h2, ?_⟩
  have gB := (tk_prelaminate (tk_isPrelaminate_of_dyadic hB)).1
  have gC := (tk_prelaminate (tk_isPrelaminate_of_dyadic hC)).1
  ext i j
  simp only [tkBary, Matrix.of_apply]
  rw [tk_integral_half gB gC]
  have eB : ∫ X, X i j ∂μB = B i j := by rw [← hbB]; rfl
  have eC : ∫ X, X i j ∂μC = C i j := by rw [← hbC]; rfl
  rw [eB, eC]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-! ### Midpoint convexity -/

/-- A midpoint convex function on `ℝ` bounded above by a continuous function is continuous
(Bernstein–Doetsch): `|φ (x₀ + v) − φ (x₀)| ≤ 2^{-n} (M − φ (x₀))` for `|v| ≤ 2^{-n}`. -/
private lemma tk_continuous_of_midpoint {φ ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hle : ∀ t, φ t ≤ ψ t) (hmid : ∀ s t, φ ((s + t) / 2) ≤ (φ s + φ t) / 2) :
    Continuous φ := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := x₀ - 1) (b := x₀ + 1)).bddAbove_image hψ.continuousOn
  have hMb : ∀ y ∈ Icc (x₀ - 1) (x₀ + 1), φ y ≤ M := fun y hy =>
    (hle y).trans (hM ⟨y, hy, rfl⟩)
  have hM0 : φ x₀ ≤ M := hMb x₀ ⟨by linarith, by linarith⟩
  have key : ∀ n : ℕ, ∀ u : ℝ, |u| ≤ 1 → φ (x₀ + u / 2 ^ n) - φ x₀ ≤ (M - φ x₀) / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro u hu
      have := hMb (x₀ + u) ⟨by linarith [(abs_le.1 hu).1], by linarith [(abs_le.1 hu).2]⟩
      simp only [pow_zero, div_one]
      linarith
    | succ n ih =>
      intro u hu
      have h1 := hmid x₀ (x₀ + u / 2 ^ n)
      have e : (x₀ + (x₀ + u / 2 ^ n)) / 2 = x₀ + u / 2 ^ (n + 1) := by
        rw [pow_succ]; field_simp; ring
      rw [e] at h1
      have h2 := ih u hu
      have e2 : (M - φ x₀) / 2 ^ (n + 1) = (M - φ x₀) / 2 ^ n / 2 := by
        rw [pow_succ, div_div]
      rw [e2]
      linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((M - φ x₀) / ε) (by norm_num : (1 : ℝ) < 2)
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hsmall : (M - φ x₀) / 2 ^ n < ε := by
    rw [div_lt_iff₀ hpos]; rw [div_lt_iff₀ hε] at hn; linarith
  refine ⟨1 / 2 ^ n, by positivity, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  set u := (y - x₀) * 2 ^ n
  have hu : |u| ≤ 1 := by
    rw [abs_mul, abs_of_pos hpos]
    rw [lt_div_iff₀ hpos] at hy
    linarith
  have hy' : y = x₀ + u / 2 ^ n := by simp only [u]; field_simp; ring
  have up := key n u hu
  have hnu : |-u| ≤ 1 := by rwa [abs_neg]
  have low1 := key n (-u) hnu
  have low2 := hmid (x₀ + u / 2 ^ n) (x₀ + -u / 2 ^ n)
  rw [show (x₀ + u / 2 ^ n + (x₀ + -u / 2 ^ n)) / 2 = x₀ by ring] at low2
  rw [← hy'] at up low2
  rw [abs_lt]
  constructor <;> linarith

/-- A midpoint convex function on `ℝ` bounded above by a continuous function is convex (the
Bernstein–Doetsch theorem: it is continuous, and a continuous midpoint convex function is convex,
by the maximum principle for `φ` minus its chord). -/
private lemma tk_convex_of_midpoint {φ ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hle : ∀ t, φ t ≤ ψ t) (hmid : ∀ s t, φ ((s + t) / 2) ≤ (φ s + φ t) / 2) :
    ConvexOn ℝ univ φ := by
  have hc := tk_continuous_of_midpoint hψ hle hmid
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  set h : ℝ → ℝ := fun l => φ (l * x + (1 - l) * y) - (l * φ x + (1 - l) * φ y) with hh
  have hcont : Continuous h := by
    simp only [hh]
    exact (hc.comp (by fun_prop)).sub (by fun_prop)
  have hmid' : ∀ s t, h ((s + t) / 2) ≤ (h s + h t) / 2 := by
    intro s t
    simp only [hh]
    have := hmid (s * x + (1 - s) * y) (t * x + (1 - t) * y)
    rw [show (s + t) / 2 * x + (1 - (s + t) / 2) * y =
      (s * x + (1 - s) * y + (t * x + (1 - t) * y)) / 2 by ring]
    linarith
  have h0 : h 0 = 0 := by simp [hh]
  have h1 : h 1 = 0 := by simp [hh]
  have hneg : ∀ l ∈ Icc (0 : ℝ) 1, h l ≤ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨l₁, hl₁, hpos⟩ := hcon
    obtain ⟨l₀, hl₀K, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
      hcont.continuousOn
    set Mx := h l₀
    have hMx : 0 < Mx := hpos.trans_le (hmax hl₁)
    have hT : IsCompact (Icc (0 : ℝ) 1 ∩ h ⁻¹' {Mx}) :=
      isCompact_Icc.inter_right (isClosed_singleton.preimage hcont)
    obtain ⟨l₂, ⟨hl₂K, hl₂eq⟩, hl₂least⟩ := hT.exists_isLeast ⟨l₀, hl₀K, rfl⟩
    have hl₂eq' : h l₂ = Mx := hl₂eq
    have hl₂0 : l₂ ≠ 0 := by rintro rfl; rw [h0] at hl₂eq'; linarith
    have hl₂1 : l₂ ≠ 1 := by rintro rfl; rw [h1] at hl₂eq'; linarith
    have hlo : 0 < l₂ := lt_of_le_of_ne hl₂K.1 (Ne.symm hl₂0)
    have hhi : l₂ < 1 := lt_of_le_of_ne hl₂K.2 hl₂1
    set δ := min l₂ (1 - l₂)
    have hδ : 0 < δ := lt_min hlo (by linarith)
    have hδ1 : δ ≤ l₂ := min_le_left _ _
    have hδ2 : δ ≤ 1 - l₂ := min_le_right _ _
    have hm := hmid' (l₂ - δ) (l₂ + δ)
    rw [show (l₂ - δ + (l₂ + δ)) / 2 = l₂ by ring] at hm
    have hA : h (l₂ - δ) < Mx := by
      have hle' : h (l₂ - δ) ≤ Mx := hmax ⟨by linarith, by linarith⟩
      refine lt_of_le_of_ne hle' fun heq => ?_
      have := hl₂least ⟨⟨by linarith, by linarith⟩, heq⟩
      linarith
    have hB : h (l₂ + δ) ≤ Mx := hmax ⟨by linarith, by linarith⟩
    linarith
  obtain rfl : b = 1 - a := by linarith
  have := hneg a ⟨ha, by linarith⟩
  simp only [hh, smul_eq_mul] at this ⊢
  linarith

/-! ### Rank-one convexity along lines -/

/-- The textbook rank-one convexity (`t ↦ f (A + t B)` convex for rank-one `B`) gives Cassese's
Definition 2.2 (the argument of `Cassese.rankOneConvex_iff` in `Bridges`, which imports this
file). -/
private lemma tk_rankOneConvex_of_cov {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : CalculusOfVariations.RankOneConvex f) : RankOneConvex f := by
  intro A B hAB
  have := (hf B (A - B) hAB).subset (Set.subset_univ _) (convex_Icc 0 1)
  convert this using 2 with t
  congr 1
  module

/-- Cassese's rank-one convexity gives the textbook one. -/
private lemma tk_cov_of_rankOneConvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (h : RankOneConvex f) : CalculusOfVariations.RankOneConvex f := by
  intro A B hB
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  rcases eq_or_ne x y with rfl | hxy
  · simp only [smul_eq_mul]
    rw [show a * x + (1 - a) * x = x by ring, show a * f (A + x • B) + (1 - a) * f (A + x • B) =
      f (A + x • B) by ring]
  · have hr : ((A + x • B) - (A + y • B)).rank = 1 := by
      rw [show (A + x • B) - (A + y • B) = (x - y) • B by module,
        Matrix.rank_smul_of_mem_nonZeroDivisors _
          (mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.2 hxy)), hB]
    have key := (h _ _ hr).2 (x := 1) (y := 0) ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ ha hb
      hab
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero, sub_self, zero_smul, one_smul,
      sub_zero, add_zero, zero_add] at key
    convert key using 2
    module

/-- A continuous function is an integrand. -/
theorem isIntegrand_of_continuous {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hg : Continuous g) : IsIntegrand g := by
  refine ⟨hg.lowerSemicontinuous, fun A => ⟨g ⁻¹' Ioo (g A - 1) (g A + 1),
    hg.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), |g A| + 1,
    fun B hB => ?_⟩⟩
  obtain ⟨h1, h2⟩ := hB
  rw [abs_le]
  constructor <;> linarith [abs_le.1 (le_refl |g A|), neg_abs_le (g A), le_abs_self (g A)]

/-- A rank-one convex function is continuous (Lemma 2.1, `External.Rindler.lemma5_6`). -/
private lemma tk_continuous_of_rankOneConvex {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hg : RankOneConvex g) : Continuous g :=
  (External.Rindler.lemma5_6 (tk_cov_of_rankOneConvex hg)).continuous

/-- A matrix unit `c E_{ij}`, `c ≠ 0`, has rank one. -/
theorem rank_single_eq_one {i : Fin d} {j : Fin m} {c : ℝ} (hc : c ≠ 0) :
    (Matrix.single i j c).rank = 1 := by
  rw [show Matrix.single i j c = c • Matrix.single i j 1 by simp [Matrix.smul_single],
    Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)]
  apply le_antisymm
  · rw [Matrix.single_eq_single_vecMulVec_single]; exact Matrix.rank_vecMulVec_le _ _
  · rw [Nat.one_le_iff_ne_zero]; intro h
    have := congrArg (fun M => M i j) (eq_zero_of_rank_eq_zero h)
    simp at this

/-- The argument of the proof of Proposition 2.4, for any family `S (A)` of real numbers (the
values `⟨f, μ⟩` over some class of measures with barycentre `A`) that contains a value `≤ f (A)`
and is closed under midpoint gluing along rank-one segments. Let `G (A) = inf S (A)`. Either
`G ≡ −∞` (if `G (A₀) = −∞` and `rank (B − A₀) = 1`, the midpoint inequality at `B = (A₀ + C)/2`,
`C = 2 B − A₀`, gives `G (B) = −∞`, and any two matrices are joined by a rank-one chain), or `G`
is finite, rank-one midpoint convex and bounded above by the continuous `f`, hence rank-one
convex (Bernstein–Doetsch) and, by Lemma 2.1, continuous. -/
private lemma tk_midpoint_principle {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (S : Matrix (Fin d) (Fin m) ℝ → Set ℝ) (hle : ∀ A, ∃ v ∈ S A, v ≤ f A)
    (hmid : ∀ B C : Matrix (Fin d) (Fin m) ℝ, (B - C).rank = 1 → ∀ v ∈ S B, ∀ w ∈ S C,
      ∃ u ∈ S ((1 / 2 : ℝ) • (B + C)), u ≤ (v + w) / 2) :
    (∀ A, ¬ BddBelow (S A)) ∨
      ∃ g : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand g ∧ RankOneConvex g ∧ (∀ A, g A ≤ f A) ∧
        ∀ A, IsGLB (S A) (g A) := by
  by_cases hall : ∀ A, BddBelow (S A)
  · right
    have hne : ∀ A, (S A).Nonempty := fun A => let ⟨v, hv, _⟩ := hle A; ⟨v, hv⟩
    set g : Matrix (Fin d) (Fin m) ℝ → ℝ := fun A => sInf (S A)
    have hglb : ∀ A, IsGLB (S A) (g A) := fun A => isGLB_csInf (hne A) (hall A)
    have hgf : ∀ A, g A ≤ f A := fun A =>
      let ⟨v, hv, hvf⟩ := hle A; (csInf_le (hall A) hv).trans hvf
    have hgmid : ∀ B C, (B - C).rank = 1 → g ((1 / 2 : ℝ) • (B + C)) ≤ (g B + g C) / 2 := by
      intro B C hBC
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨v, hv, hvlt⟩ := exists_lt_of_csInf_lt (hne B) (lt_add_of_pos_right (g B) hε)
      obtain ⟨w, hw, hwlt⟩ := exists_lt_of_csInf_lt (hne C) (lt_add_of_pos_right (g C) hε)
      obtain ⟨u, hu, hule⟩ := hmid B C hBC v hv w hw
      have := csInf_le (hall _) hu
      change g _ ≤ u at this
      linarith
    have hcov : CalculusOfVariations.RankOneConvex g := by
      intro A R hR
      refine tk_convex_of_midpoint (ψ := fun t => f (A + t • R)) (by fun_prop)
        (fun t => hgf _) fun s t => ?_
      rcases eq_or_ne s t with rfl | hst
      · rw [show (s + s) / 2 = s by ring]; linarith
      · have hr : ((A + s • R) - (A + t • R)).rank = 1 := by
          rw [show (A + s • R) - (A + t • R) = (s - t) • R by module,
            Matrix.rank_smul_of_mem_nonZeroDivisors _
              (mem_nonZeroDivisors_of_ne_zero (sub_ne_zero.2 hst)), hR]
        have := hgmid _ _ hr
        rwa [show (1 / 2 : ℝ) • (A + s • R + (A + t • R)) = A + ((s + t) / 2) • R by module]
          at this
    have hrc := tk_rankOneConvex_of_cov hcov
    exact ⟨g, isIntegrand_of_continuous (tk_continuous_of_rankOneConvex hrc), hrc, hgf,
      hglb⟩
  · left
    push Not at hall
    obtain ⟨A₀, hA₀⟩ := hall
    have hprop : ∀ X B, ¬ BddBelow (S X) → (B - X).rank = 1 → ¬ BddBelow (S B) := by
      intro X B hX hBX hB
      obtain ⟨r, hr⟩ := hB
      set C := (2 : ℝ) • B - X
      have hXC : (X - C).rank = 1 := by
        rw [show X - C = (-2 : ℝ) • (B - X) by simp only [C]; module,
          Matrix.rank_smul_of_mem_nonZeroDivisors _
            (mem_nonZeroDivisors_of_ne_zero (by norm_num)), hBX]
      obtain ⟨w, hw, _⟩ := hle C
      obtain ⟨v, hv, hvlt⟩ := not_bddBelow_iff.1 hX (2 * r - w - 1)
      obtain ⟨u, hu, hule⟩ := hmid X C hXC v hv w hw
      rw [show (1 / 2 : ℝ) • (X + C) = B by simp only [C]; module] at hu
      have := hr hu
      linarith
    have hstep : ∀ M : Matrix (Fin d) (Fin m) ℝ, ∀ X, ¬ BddBelow (S X) → ¬ BddBelow (S (X + M)) := by
      intro M
      induction M using Matrix.induction_on' with
      | h_zero => intro X hX; rwa [add_zero]
      | h_add p q hp hq => intro X hX; rw [← add_assoc]; exact hq _ (hp X hX)
      | h_std_basis i j c =>
        intro X hX
        rcases eq_or_ne c 0 with rfl | hc
        · rwa [Matrix.single_zero, add_zero]
        · exact hprop X _ hX (by rw [add_sub_cancel_left]; exact rank_single_eq_one hc)
    intro A
    have := hstep (A - A₀) A₀ hA₀
    rwa [add_sub_cancel] at this

/-! ### Infima in `EReal` and the rank-one convex envelope -/

private lemma tk_iInf_eq_of_isGLB {α : Type*} {P : α → Prop} {v : α → ℝ} {g : ℝ}
    (h : IsGLB {x | ∃ a, P a ∧ v a = x} g) : ⨅ (a : α) (_ : P a), (v a : EReal) = g := by
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    obtain ⟨r, hgr, hrI⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hgr' : g < r := EReal.coe_lt_coe_iff.1 hgr
    obtain ⟨a, ha, hx⟩ : ∃ a, P a ∧ v a < r := by
      by_contra hcon
      push Not at hcon
      exact absurd (h.2 fun x ⟨a, ha, hax⟩ => hax ▸ hcon a ha) (not_le.2 hgr')
    have h1 : ⨅ (a : α) (_ : P a), (v a : EReal) ≤ v a := iInf₂_le a ha
    exact absurd (hrI.trans_le h1) (not_lt.2 (EReal.coe_le_coe_iff.2 hx.le))
  · exact le_iInf₂ fun a ha => EReal.coe_le_coe_iff.2 (h.1 ⟨a, ha, rfl⟩)

private lemma tk_iInf_eq_bot {α : Type*} {P : α → Prop} {v : α → ℝ}
    (h : ¬ BddBelow {x | ∃ a, P a ∧ v a = x}) : ⨅ (a : α) (_ : P a), (v a : EReal) = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro r
  obtain ⟨x, ⟨a, ha, rfl⟩, hx⟩ := not_bddBelow_iff.1 h r
  exact (iInf₂_le a ha).trans_lt (EReal.coe_lt_coe_iff.2 hx)

/-- If `g` is a rank-one convex integrand `≤ f` above every other, `f^{rc} = g`. -/
private lemma tk_rcEnvelope_eq {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hg : IsIntegrand g ∧ RankOneConvex g ∧ ∀ B, g B ≤ f B)
    (hmax : ∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand h → RankOneConvex h →
      (∀ B, h B ≤ f B) → ∀ A, h A ≤ g A) (A : Matrix (Fin d) (Fin m) ℝ) :
    rcEnvelope f A = g A :=
  le_antisymm (iSup₂_le fun h hh => EReal.coe_le_coe_iff.2 (hmax h hh.1 hh.2.1 hh.2.2 A))
    (le_iSup₂_of_le (f := fun (h : Matrix (Fin d) (Fin m) ℝ → ℝ)
      (_ : IsIntegrand h ∧ RankOneConvex h ∧ ∀ B, h B ≤ f B) => (h A : EReal)) g hg le_rfl)

/-- If there is no rank-one convex integrand `≤ f`, `f^{rc} ≡ −∞`. -/
private lemma tk_rcEnvelope_eq_bot {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hno : ∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand h → RankOneConvex h →
      (∀ B, h B ≤ f B) → False) (A : Matrix (Fin d) (Fin m) ℝ) : rcEnvelope f A = ⊥ :=
  iSup₂_eq_bot.2 fun h hh => (hno h hh.1 hh.2.1 hh.2.2).elim

/-- The proof of Proposition 2.4 as a dichotomy: either there is no rank-one convex integrand
`≤ f` and the infimum over dyadic prelaminates is `−∞` everywhere, or the infimum is a rank-one
convex integrand `G ≤ f`, the largest one, equal to `f^{rc}`. -/
private lemma tk_prop2_4_cases {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) :
    ((∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand h → RankOneConvex h →
        (∀ B, h B ≤ f B) → False) ∧
      ∀ A, ¬ BddBelow {x | ∃ μ, (IsDyadicPrelaminate μ ∧ IsBarycentre μ A) ∧
        ∫ X, f X ∂μ = x}) ∨
    ∃ G : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand G ∧ RankOneConvex G ∧ (∀ B, G B ≤ f B) ∧
      (∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand h → RankOneConvex h →
        (∀ B, h B ≤ f B) → ∀ A, h A ≤ G A) ∧
      ∀ A, IsGLB {x | ∃ μ, (IsDyadicPrelaminate μ ∧ IsBarycentre μ A) ∧ ∫ X, f X ∂μ = x}
        (G A) := by
  set S : Matrix (Fin d) (Fin m) ℝ → Set ℝ := fun A =>
    {x | ∃ μ, (IsDyadicPrelaminate μ ∧ IsBarycentre μ A) ∧ ∫ X, f X ∂μ = x}
  -- `G ≤ f`: the Dirac mass
  have hle : ∀ A, ∃ v ∈ S A, v ≤ f A := fun A =>
    ⟨f A, ⟨Measure.dirac A, ⟨.dirac A, tk_isBarycentre_iff.2 (tk_bary_dirac A)⟩,
      integral_dirac _ _⟩, le_rfl⟩
  -- the midpoint inequality: a midpoint split followed by the splittings of `μ_B`, `μ_C`
  have hmid : ∀ B C : Matrix (Fin d) (Fin m) ℝ, (B - C).rank = 1 → ∀ v ∈ S B, ∀ w ∈ S C,
      ∃ u ∈ S ((1 / 2 : ℝ) • (B + C)), u ≤ (v + w) / 2 := by
    rintro B C hBC v ⟨μB, ⟨hB, hbB⟩, rfl⟩ w ⟨μC, ⟨hC, hbC⟩, rfl⟩
    rw [tk_isBarycentre_iff] at hbB hbC
    obtain ⟨hD, hbD⟩ := tk_dyadic_mid hBC.le hB hbB hC hbC
    refine ⟨_, ⟨_, ⟨hD, tk_isBarycentre_iff.2 hbD⟩, rfl⟩, le_of_eq ?_⟩
    exact tk_integral_half (tk_prelaminate (tk_isPrelaminate_of_dyadic hB)).1
      (tk_prelaminate (tk_isPrelaminate_of_dyadic hC)).1 f
  -- Jensen: `h (A) ≤ ⟨h, μ⟩ ≤ ⟨f, μ⟩` for a rank-one convex `h ≤ f`
  have hjen : ∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, RankOneConvex h → (∀ B, h B ≤ f B) →
      ∀ A, h A ∈ lowerBounds (S A) := by
    rintro h hh hhf A x ⟨μ, ⟨hμ, hb⟩, rfl⟩
    exact tk_jensen (tk_isPrelaminate_of_dyadic hμ) hb hh hhf
  rcases tk_midpoint_principle hf S hle hmid with hbot | ⟨G, hGI, hGR, hGf, hglb⟩
  · left
    exact ⟨fun h _ hR hhf => hbot 0 ⟨h 0, hjen h hR hhf 0⟩, hbot⟩
  · right
    exact ⟨G, hGI, hGR, hGf, fun h _ hR hhf A => (hglb A).2 (hjen h hR hhf A), hglb⟩

/-- **Proposition 2.4** (`prop:rk1rad`): for a continuous integrand `f` and every `A`,
`inf_{μ ∈ 𝒫ℒ_{dyad}(A)} ⟨f, μ⟩ = f^{rc} (A)` (both sides may be `−∞`). 

Proof: the paper's (lines 622–659), through `tk_prop2_4_cases`. `G (A) = inf ⟨f, μ⟩` over the dyadic
prelaminates with barycentre `A` satisfies `G ≤ f` (Dirac masses) and, for `rank (B − C) = 1`,
`G ((B + C)/2) ≤ (G (B) + G (C))/2` (a midpoint split of `δ_{(B+C)/2}` followed by the splittings
of `μ_B` and `μ_C`, `tk_dyadic_mid`; repeated atoms are allowed, inventory E10). If `G (A₀) = −∞`
and `rank (B − A₀) = 1`, the midpoint inequality with `C = 2 B − A₀` gives `G (B) = −∞`, and any
two matrices are joined by a chain of rank-one steps (through the matrix units), so `G ≡ −∞` or `G`
is finite. A finite `G` is midpoint convex along rank-one lines and bounded above by the
continuous `f`, hence rank-one convex (Bernstein–Doetsch, which the paper uses without citation;
proved here, `tk_convex_of_midpoint`). Jensen's inequality along the splittings
(`tk_prelaminate`) gives `h ≤ G` for every rank-one convex `h ≤ f`, so `f^{rc} ≤ G`, with equality
when `G` is finite and `≡ −∞` otherwise. A step the paper leaves implicit: for `G` to be one of the
minorants of Definition 2.3 it must be an integrand; it is continuous by Lemma 2.1
(`External.Rindler.lemma5_6`).

Placed before Proposition 2.1, whose proof (Remark 2.1) uses it.-/
theorem proposition2_4 {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    ⨅ (μ : Measure (Matrix (Fin d) (Fin m) ℝ)) (_ : IsDyadicPrelaminate μ ∧ IsBarycentre μ A),
        ((∫ X, f X ∂μ : ℝ) : EReal) = rcEnvelope f A := by
  rcases tk_prop2_4_cases hf with ⟨hno, hbot⟩ | ⟨G, hGI, hGR, hGf, hmax, hglb⟩
  · rw [tk_iInf_eq_bot (hbot A), tk_rcEnvelope_eq_bot hno]
  · rw [tk_iInf_eq_of_isGLB (hglb A), tk_rcEnvelope_eq ⟨hGI, hGR, hGf⟩ hmax]

/-- **Proposition 2.1** (`prop:rk1envelope`): for a continuous integrand `f`,
`f^{rc} (A) = inf_{μ ∈ 𝒫ℒ(A)} ∫ f dμ`, the infimum over the prelaminates with barycentre `A`.
Quoted from Pedregal 1993 (Section 4) and Dacorogna 2008 (Theorem 6.10), whose proofs assume `f`
bounded below; Remark 2.1 removes the assumption and notes that the proposition also follows from
Proposition 2.4. 

Proof: Remark 2.1's second route, from Proposition 2.4. Jensen's inequality along the splittings
gives `g (A) ≤ ⟨g, μ⟩ ≤ ⟨f, μ⟩` for every rank-one convex minorant `g` and every `μ ∈ 𝒫ℒ (A)`, so
`f^{rc} (A) ≤ inf_{𝒫ℒ (A)} ⟨f, μ⟩`; dyadic prelaminates are prelaminates, so the infimum is at most
`inf_{𝒫ℒ_dyad (A)} ⟨f, μ⟩ = f^{rc} (A)` (Proposition 2.4). No boundedness from below is needed.-/
theorem proposition2_1 {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    rcEnvelope f A =
      ⨅ (μ : Measure (Matrix (Fin d) (Fin m) ℝ)) (_ : IsPrelaminate μ ∧ IsBarycentre μ A),
        ((∫ X, f X ∂μ : ℝ) : EReal) := by
  apply le_antisymm
  · -- Jensen's inequality on prelaminates, for every rank-one convex minorant
    exact iSup₂_le fun h hh => le_iInf₂ fun μ hμ =>
      EReal.coe_le_coe_iff.2 (tk_jensen hμ.1 hμ.2 hh.2.1 hh.2.2)
  · -- dyadic prelaminates are prelaminates, and Proposition 2.4
    rw [← proposition2_4 hf A]
    exact le_iInf₂ fun μ hμ => iInf₂_le μ ⟨tk_isPrelaminate_of_dyadic hμ.1, hμ.2⟩

/-! ### The envelopes as integrands -/

/-- For continuous `f`, either `f^{rc} ≡ −∞` (and there is no rank-one convex minorant), or
`f^{rc}` is the largest rank-one convex integrand `G ≤ f` (Proposition 2.4's proof). -/
private lemma tk_rc_cases {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) :
    ((∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand h → RankOneConvex h →
        (∀ B, h B ≤ f B) → False) ∧ ∀ A, rcEnvelope f A = ⊥) ∨
    ∃ G : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand G ∧ RankOneConvex G ∧ (∀ B, G B ≤ f B) ∧
      (∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand h → RankOneConvex h →
        (∀ B, h B ≤ f B) → ∀ A, h A ≤ G A) ∧ ∀ A, rcEnvelope f A = G A := by
  rcases tk_prop2_4_cases hf with ⟨hno, _⟩ | ⟨G, hGI, hGR, hGf, hmax, _⟩
  · exact Or.inl ⟨hno, tk_rcEnvelope_eq_bot hno⟩
  · exact Or.inr ⟨G, hGI, hGR, hGf, hmax, tk_rcEnvelope_eq ⟨hGI, hGR, hGf⟩ hmax⟩

/-- `|∂_k φ_i| ≤ K` for a `K`-Lipschitz `φ`. -/
theorem abs_jac_le {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (x : Fin m → ℝ) (i : Fin d) (k : Fin m) : |jac φ x i k| ≤ K := by
  have hi : LipschitzWith K (fun y => φ y i) := by
    have h := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hφ
    rw [one_mul] at h
    exact h
  simp only [jac, Matrix.of_apply]
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ (fun y => φ y i) x (Pi.single k 1)‖
      ≤ ‖fderiv ℝ (fun y => φ y i) x‖ * ‖(Pi.single k 1 : Fin m → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * 1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ hi
        · rw [Pi.norm_single, norm_one]
    _ = K := mul_one _

/-- The derivative matrix of any map is measurable. -/
theorem measurable_jac (φ : (Fin m → ℝ) → Fin d → ℝ) :
    Measurable (jac φ) :=
  Measurable.of_eval_matrix _ fun i _ => measurable_fderiv_apply_const ℝ (fun y => φ y i) _

/-- An integrand is bounded on compact sets. -/
private lemma tk_bdd_of_compact {g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hg : IsIntegrand g)
    {K : Set (Matrix (Fin d) (Fin m) ℝ)} (hK : IsCompact K) : ∃ C, ∀ M ∈ K, |g M| ≤ C := by
  choose U hU C hC using hg.2
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  refine ⟨∑ x ∈ t, |C x|, fun M hM => ?_⟩
  obtain ⟨x, hx, hMx⟩ := Set.mem_iUnion₂.1 (hcover hM)
  exact (hC x M hMx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) hx))

private lemma tk_isCompact_box (B : Matrix (Fin d) (Fin m) ℝ) (K : ℝ) :
    IsCompact {M : Matrix (Fin d) (Fin m) ℝ | ∀ i k, |M i k - B i k| ≤ K} := by
  have : {M : Matrix (Fin d) (Fin m) ℝ | ∀ i k, |M i k - B i k| ≤ K} =
      Set.pi univ fun i => Set.pi univ fun k => Icc (B i k - K) (B i k + K) := by
    ext M
    constructor
    · intro h i _ k _
      exact ⟨by linarith [(abs_le.1 (h i k)).1], by linarith [(abs_le.1 (h i k)).2]⟩
    · intro h i k
      have := h i (Set.mem_univ _) k (Set.mem_univ _)
      exact abs_le.2 ⟨by linarith [this.1], by linarith [this.2]⟩
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun k => isCompact_Icc

/-- For an integrand `g` and a Lipschitz `φ`, `x ↦ g (B + ∇φ (x))` is integrable on every set of
finite measure (it is measurable and bounded). -/
private lemma tk_integrableOn_comp {g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hg : IsIntegrand g)
    (B : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) {s : Set (Fin m → ℝ)} (hs : volume s < ⊤) :
    IntegrableOn (fun x => g (B + jac φ x)) s := by
  obtain ⟨C, hC⟩ := tk_bdd_of_compact hg (tk_isCompact_box B K)
  refine IntegrableOn.of_bound hs ?_ C (Filter.Eventually.of_forall fun x => ?_)
  · have hm : Measurable fun x => B + jac φ x := Measurable.of_eval_matrix _ fun i k => by
      simp only [Matrix.add_apply, jac, Matrix.of_apply]
      exact measurable_const.add (measurable_fderiv_apply_const ℝ (fun y => φ y i) _)
    exact (hg.1.measurable.comp hm).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    apply hC
    intro i k
    simp only [Matrix.add_apply, add_sub_cancel_left]
    exact abs_jac_le hφ x i k

/-- The unit cube has volume `1`. -/
theorem volume_unitCube (m : ℕ) : volume (unitCube m) = 1 := by
  simp [unitCube, Real.volume_pi_Ioo]

/-- For a continuous `g` and a Lipschitz `φ`, `x ↦ g (B + ∇φ (x))` is integrable on the unit
cube. -/
theorem integrableOn_comp_jac {g : Matrix (Fin d) (Fin m) ℝ → ℝ} (hg : Continuous g)
    (B : Matrix (Fin d) (Fin m) ℝ) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) : IntegrableOn (fun x => g (B + jac φ x)) (unitCube m) :=
  tk_integrableOn_comp (isIntegrand_of_continuous hg) B hφ
    (by rw [volume_unitCube]; exact ENNReal.one_lt_top)

private lemma tk_jac_smul (c : ℝ) (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) :
    jac (fun y => c • φ y) x = c • jac φ x := by
  ext i k
  simp only [jac, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  have : (fun y => c * φ y i) = c • (fun y => φ y i) := rfl
  rw [this, fderiv_const_smul_field]
  rfl

/-- For continuous `f`, either `f^{qc} ≡ −∞` (and there is no quasiconvex minorant), or `f^{qc}`
is the largest quasiconvex integrand `Q ≤ f`: the supremum of quasiconvex integrands is lower
semicontinuous, locally bounded between one of them and `f`, and quasiconvex. -/
private lemma tk_qc_cases {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) :
    ((∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand h → Quasiconvex h →
        (∀ B, h B ≤ f B) → False) ∧ ∀ A, qcEnvelope f A = ⊥) ∨
    ∃ Q : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand Q ∧ Quasiconvex Q ∧ (∀ B, Q B ≤ f B) ∧
      (∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand h → Quasiconvex h →
        (∀ B, h B ≤ f B) → ∀ A, h A ≤ Q A) ∧ ∀ A, qcEnvelope f A = Q A := by
  by_cases hex : ∃ g₀ : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand g₀ ∧ Quasiconvex g₀ ∧
      ∀ B, g₀ B ≤ f B
  swap
  · exact Or.inl ⟨fun h a b c => hex ⟨h, a, b, c⟩, fun A =>
      iSup₂_eq_bot.2 fun h hh => (hex ⟨h, hh⟩).elim⟩
  right
  obtain ⟨g₀, hg₀I, hg₀Q, hg₀f⟩ := hex
  set P : (Matrix (Fin d) (Fin m) ℝ → ℝ) → Prop := fun h =>
    IsIntegrand h ∧ Quasiconvex h ∧ ∀ B, h B ≤ f B
  have hge : ∀ h, P h → ∀ A, (h A : EReal) ≤ qcEnvelope f A := fun h hh A =>
    le_iSup₂ (f := fun (h : Matrix (Fin d) (Fin m) ℝ → ℝ) (_ : P h) => (h A : EReal)) h hh
  have hle : ∀ A, qcEnvelope f A ≤ f A := fun A =>
    iSup₂_le fun h hh => EReal.coe_le_coe_iff.2 (hh.2.2 A)
  set Q : Matrix (Fin d) (Fin m) ℝ → ℝ := fun A => (qcEnvelope f A).toReal
  have hfin : ∀ A, qcEnvelope f A = Q A := fun A =>
    (EReal.coe_toReal ((hle A).trans_lt (EReal.coe_lt_top _)).ne
      (((EReal.bot_lt_coe _).trans_le (hge g₀ ⟨hg₀I, hg₀Q, hg₀f⟩ A)).ne')).symm
  have hmax : ∀ h, P h → ∀ A, h A ≤ Q A := fun h hh A =>
    EReal.coe_le_coe_iff.1 ((hge h hh A).trans_eq (hfin A))
  have hQf : ∀ A, Q A ≤ f A := fun A => EReal.coe_le_coe_iff.1 ((hfin A).symm.trans_le (hle A))
  have happrox : ∀ A, ∀ y : ℝ, y < Q A → ∃ h, P h ∧ y < h A := by
    intro A y hy
    rw [← EReal.coe_lt_coe_iff, ← hfin A] at hy
    obtain ⟨h, hh⟩ := lt_iSup_iff.1 hy
    obtain ⟨hP, hlt⟩ := lt_iSup_iff.1 hh
    exact ⟨h, hP, EReal.coe_lt_coe_iff.1 hlt⟩
  have hQI : IsIntegrand Q := by
    refine ⟨fun A y hy => ?_, fun A => ?_⟩
    · obtain ⟨h, hP, hlt⟩ := happrox A y hy
      filter_upwards [hP.1.1 A y hlt] with B hB
      exact hB.trans_le (hmax h hP B)
    · obtain ⟨U, hU, C, hC⟩ := hg₀I.2 A
      obtain ⟨V, hV, D, hD⟩ := (isIntegrand_of_continuous hf).2 A
      refine ⟨U ∩ V, Filter.inter_mem hU hV, max C D, fun B hB => abs_le.2 ⟨?_, ?_⟩⟩
      · have h1 := (abs_le.1 (hC B hB.1)).1
        have h2 := hmax g₀ ⟨hg₀I, hg₀Q, hg₀f⟩ B
        linarith [le_max_left C D]
      · have h1 := (abs_le.1 (hD B hB.2)).2
        linarith [hQf B, le_max_right C D]
  have hQQ : Quasiconvex Q := by
    intro A φ K hφ h0 hint
    refine le_of_forall_lt fun y hy => ?_
    obtain ⟨h, hP, hlt⟩ := happrox A y hy
    have h1 := hP.2.1 A φ K hφ h0 (tk_integrableOn_comp hP.1 A hφ (by
      rw [volume_unitCube]; exact ENNReal.one_lt_top))
    have h2 : ∫ x in unitCube m, h (A + jac φ x) ≤ ∫ x in unitCube m, Q (A + jac φ x) :=
      setIntegral_mono (tk_integrableOn_comp hP.1 A hφ (by
        rw [volume_unitCube]; exact ENNReal.one_lt_top)) hint fun x => hmax h hP _
    linarith
  exact ⟨Q, hQI, hQQ, hQf, fun h a b c => hmax h ⟨a, b, c⟩, hfin⟩

/-! ### Transformations of minorants -/

/-- Precomposing a rank-one convex `G` with a linear map that preserves the rank, and scaling by
`c ≥ 0`, gives a rank-one convex function. -/
private lemma tk_rankOneConvex_comp {G : Matrix (Fin d) (Fin m) ℝ → ℝ} (hG : RankOneConvex G)
    (L : Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin m) ℝ) (hL : ∀ X, (L X).rank = X.rank)
    {c : ℝ} (hc : 0 ≤ c) : RankOneConvex (fun A => c * G (L A)) := by
  intro A B hAB
  have h := (hG (L A) (L B) (by rw [← map_sub, hL, hAB])).smul hc
  convert h using 2 with t
  simp only [map_add, map_smul, smul_eq_mul]

/-- If `G` is the largest rank-one convex integrand below `f`, `L` is a rank-preserving linear
map and `c f (L B) ≤ f (B)`, then `c G (L A) ≤ G (A)`. -/
private lemma tk_rc_transform {f G : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hG : IsIntegrand G ∧ RankOneConvex G ∧ ∀ B, G B ≤ f B)
    (hmax : ∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand h → RankOneConvex h →
      (∀ B, h B ≤ f B) → ∀ A, h A ≤ G A)
    (L : Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin m) ℝ) (hL : ∀ X, (L X).rank = X.rank)
    {c : ℝ} (hc : 0 ≤ c) (hfL : ∀ B, c * f (L B) ≤ f B) (A : Matrix (Fin d) (Fin m) ℝ) :
    c * G (L A) ≤ G A := by
  have hrc := tk_rankOneConvex_comp hG.2.1 L hL hc
  refine hmax _ (isIntegrand_of_continuous (tk_continuous_of_rankOneConvex hrc)) hrc
    (fun B => (mul_le_mul_of_nonneg_left (hG.2.2 _) hc).trans (hfL B)) A

/-- If `Q` is the largest quasiconvex integrand below `f`, `s ≠ 0` and `c f (s⁻¹ B) ≤ f (B)` with
`c > 0`, then `c Q (s⁻¹ A) ≤ Q (A)`: `A ↦ c Q (s⁻¹ A)` is a quasiconvex integrand, since
`s⁻¹ (A + ∇φ) = s⁻¹ A + ∇ (s⁻¹ φ)`. -/
private lemma tk_qc_scale {f Q : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hQ : IsIntegrand Q ∧ Quasiconvex Q ∧ ∀ B, Q B ≤ f B)
    (hmax : ∀ h : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand h → Quasiconvex h →
      (∀ B, h B ≤ f B) → ∀ A, h A ≤ Q A)
    {s c : ℝ} (hc : 0 < c) (hfL : ∀ B, c * f (s⁻¹ • B) ≤ f B)
    (A : Matrix (Fin d) (Fin m) ℝ) : c * Q (s⁻¹ • A) ≤ Q A := by
  obtain ⟨hQI, hQQ, hQf⟩ := hQ
  have hI : IsIntegrand fun A => c * Q (s⁻¹ • A) := by
    refine ⟨?_, fun A => ?_⟩
    · have h1 : LowerSemicontinuous fun A : Matrix (Fin d) (Fin m) ℝ => Q (s⁻¹ • A) :=
        hQI.1.comp (continuous_const_smul _)
      have hcont : Continuous fun x : ℝ => c * x := continuous_const.mul continuous_id
      exact hcont.comp_lowerSemicontinuous h1 fun a b hab => mul_le_mul_of_nonneg_left hab hc.le
    · obtain ⟨U, hU, C, hC⟩ := hQI.2 (s⁻¹ • A)
      refine ⟨(fun B => s⁻¹ • B) ⁻¹' U, (continuous_const_smul _).continuousAt.preimage_mem_nhds hU,
        c * C, fun B hB => ?_⟩
      rw [abs_mul, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left (hC _ hB) hc.le
  have hq : Quasiconvex fun A => c * Q (s⁻¹ • A) := by
    intro B φ K hφ h0 _
    have hψ : LipschitzWith (‖s⁻¹‖₊ * K) (fun y => s⁻¹ • φ y) := (lipschitzWith_smul s⁻¹).comp hφ
    have h0' : ∀ x ∉ unitCube m, (fun y => s⁻¹ • φ y) x = 0 := fun x hx => by
      simp [h0 x hx]
    have key := hQQ (s⁻¹ • B) _ _ hψ h0' (tk_integrableOn_comp hQI _ hψ (by
      rw [volume_unitCube]; exact ENNReal.one_lt_top))
    have e : ∀ x, s⁻¹ • (B + jac φ x) = s⁻¹ • B + jac (fun y => s⁻¹ • φ y) x := fun x => by
      rw [tk_jac_smul, smul_add]
    simp only [e]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left key hc.le
  exact hmax _ hI hq (fun B => (mul_le_mul_of_nonneg_left (hQf _) hc.le).trans (hfL B)) A

/-- The homogeneity of a maximal minorant: if `|s|^p G (s⁻¹ A) ≤ G (A)` whenever `f` is
homogeneous under `s`, then `G (s A) = |s|^p G (A)` for every such `s`. -/
private lemma tk_hom_core {p : ℝ} {f G : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hprin : ∀ s : ℝ, s ≠ 0 → (∀ B, f (s • B) = |s| ^ p * f B) →
      ∀ A, |s| ^ p * G (s⁻¹ • A) ≤ G A)
    {s : ℝ} (hs : s ≠ 0) (hfs : ∀ B, f (s • B) = |s| ^ p * f B) (A : Matrix (Fin d) (Fin m) ℝ) :
    G (s • A) = |s| ^ p * G A := by
  have hsp : 0 < |s| ^ p := Real.rpow_pos_of_pos (abs_pos.2 hs) p
  have hinv : |s⁻¹| ^ p = (|s| ^ p)⁻¹ := by rw [abs_inv, Real.inv_rpow (abs_nonneg s)]
  have hfs' : ∀ B, f (s⁻¹ • B) = |s⁻¹| ^ p * f B := by
    intro B
    have := hfs (s⁻¹ • B)
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul] at this
    rw [hinv, this]
    field_simp
  apply le_antisymm
  · have := hprin s⁻¹ (inv_ne_zero hs) hfs' A
    rw [inv_inv, hinv] at this
    rw [← mul_le_mul_iff_of_pos_left (inv_pos.2 hsp)]
    rw [← mul_assoc, inv_mul_cancel₀ hsp.ne', one_mul]
    exact this
  · have := hprin s hs hfs (s • A)
    rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at this

/-- A function homogeneous under `2` with `2^p ≠ 1` vanishes at `0`. -/
private lemma tk_zero_of_hom {p : ℝ} (hp : 0 < p) {G : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (h : G ((2 : ℝ) • 0) = |(2 : ℝ)| ^ p * G 0) : G 0 = 0 := by
  rw [smul_zero, abs_of_pos two_pos] at h
  have h2 : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow (by norm_num) hp
  nlinarith [h]

/-- The two homogeneity types, for a maximal minorant `G` of a homogeneous `f`. -/
private lemma tk_hom_types {p : ℝ} (hp : 0 < p) {f G : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hprin : ∀ s : ℝ, s ≠ 0 → (∀ B, f (s • B) = |s| ^ p * f B) →
      ∀ A, |s| ^ p * G (s⁻¹ • A) ≤ G A) :
    (IsPHomogeneous p f → IsPHomogeneous p G) ∧ (IsPosPHomogeneous p f → IsPosPHomogeneous p G) := by
  refine ⟨fun hf t A => ?_, fun hf t ht A => ?_⟩
  · rcases eq_or_ne t 0 with rfl | ht
    · rw [zero_smul, abs_zero, Real.zero_rpow hp.ne', zero_mul]
      exact tk_zero_of_hom hp (tk_hom_core hprin two_ne_zero (fun B => hf 2 B) 0)
    · exact tk_hom_core hprin ht (fun B => hf t B) A
  · have := tk_hom_core hprin ht.ne' (fun B => by rw [hf t ht, abs_of_pos ht]) A
    rwa [abs_of_pos ht] at this

private lemma tk_smul_linear_rank {s : ℝ} (hs : s ≠ 0) (X : Matrix (Fin d) (Fin m) ℝ) :
    ((s • LinearMap.id : Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin m) ℝ) X).rank =
      X.rank := by
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hs)

/-- The scaling inequality `|s|^p f (s⁻¹ B) ≤ f (B)` from the homogeneity of `f` under `s`. -/
private lemma tk_scale_f {p : ℝ} {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {s : ℝ} (hs : s ≠ 0)
    (hfs : ∀ B, f (s • B) = |s| ^ p * f B) (B : Matrix (Fin d) (Fin m) ℝ) :
    |s| ^ p * f (s⁻¹ • B) ≤ f B := by
  rw [← hfs, smul_smul, mul_inv_cancel₀ hs, one_smul]

/-! ### Cassese's quasiconvexity and the textbook one -/

/-- The textbook quasiconvexity at `A` on the unit cube (`|Ω| f (A) ≤ ∫_Ω f (A + ∇φ)` with
`Ω = (0, 1)^m`, `|Ω| = 1`) is Cassese's Definition 2.1 (a bridge of `Bridges`, stated here because
line 559 needs it). -/
theorem cov_quasiconvexAtOn_unitCube_iff (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    CalculusOfVariations.QuasiconvexAtOn (CalculusOfVariations.unitCube m) f A ↔
      QuasiconvexAt f A := by
  have hv : (volume (CalculusOfVariations.unitCube m)).toReal = 1 := by
    rw [show CalculusOfVariations.unitCube m = unitCube m from rfl, volume_unitCube,
      ENNReal.toReal_one]
  simp only [CalculusOfVariations.QuasiconvexAtOn, hv, one_mul]
  rfl

/-- The textbook quasiconvex envelope (over lower semicontinuous, locally bounded, quasiconvex
minorants, the form of Dacorogna's formula in `External.KinderlehrerPedregal`) is Cassese's
(Definition 2.3, over quasiconvex integrands); a bridge of `Bridges`, stated here because line 559
needs it. -/
theorem cov_qcEnvelope_eq (f : Matrix (Fin d) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    CalculusOfVariations.qcEnvelope f A = qcEnvelope f A := by
  refine iSup_congr fun g => iSup_congr_Prop ?_ fun _ => rfl
  rw [show CalculusOfVariations.Quasiconvex g ↔ Quasiconvex g from
    forall_congr' fun A => cov_quasiconvexAtOn_unitCube_iff g A]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

private lemma tk_unitBall_isOpen : IsOpen (CalculusOfVariations.unitBall m) :=
  isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2) continuous_const

private lemma tk_unitBall_isBounded : Bornology.IsBounded (CalculusOfVariations.unitBall m) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨1, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have hx' : ∑ j, x j ^ 2 < 1 := hx
  rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
  linarith

private lemma tk_unitBall_nonempty : (CalculusOfVariations.unitBall m).Nonempty :=
  ⟨0, by simp [CalculusOfVariations.unitBall]⟩

/-- **Consequence of Proposition 2.2** (`cs-qc-minorant`, line 559): for a continuous integrand
`f`, quasiconvexity at `A` is equivalent to the existence of a quasiconvex minorant `g ≤ f` with
`g (A) = f (A)`. By Dacorogna's formula (Kinderlehrer–Pedregal,
`External.KinderlehrerPedregal.dacorognaFormula_holds`).

Proof. If `g` is such a minorant, `f (A) = g (A) ≤ ∫ g (A + ∇φ) ≤ ∫ f (A + ∇φ)`. Conversely, if `f`
is quasiconvex at `A`, then `f` is quasiconvex at `A` on the unit ball (Lemma 2.2, domain
independence, `External.Rindler.quasiconvexAtOn_iff`: Definition 2.1 tests on the unit cube and
Dacorogna's formula averages over the unit ball, a passage the paper makes silently), so every
average in Dacorogna's formula is at least `f (A)` and `f^{qc} (A) = f (A)`; and `f^{qc}` is itself
a quasiconvex integrand (the supremum of the quasiconvex integrands below the continuous `f`,
`tk_qc_cases`), the required minorant.-/
theorem quasiconvexAt_iff_exists_minorant
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) (A : Matrix (Fin d) (Fin m) ℝ) :
    QuasiconvexAt f A ↔
      ∃ g : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand g ∧ Quasiconvex g ∧ (∀ B, g B ≤ f B) ∧
        g A = f A := by
  have hfI := isIntegrand_of_continuous hf
  have hvol : volume (unitCube m) < ⊤ := by rw [volume_unitCube]; exact ENNReal.one_lt_top
  constructor
  · intro hA
    -- Dacorogna's formula is an infimum over the unit ball; Definition 2.1 is on the unit cube,
    -- and Lemma 2.2 passes from one to the other
    have hball : CalculusOfVariations.QuasiconvexAtOn (CalculusOfVariations.unitBall m) f A :=
      (External.Rindler.quasiconvexAtOn_iff hf.lowerSemicontinuous hfI.2 A tk_unitBall_isOpen
        tk_unitBall_isBounded tk_unitBall_nonempty).1
        ((cov_quasiconvexAtOn_unitCube_iff f A).2 hA)
    have hBfin : volume (CalculusOfVariations.unitBall m) < ⊤ :=
      tk_unitBall_isBounded.measure_lt_top
    have hBpos : 0 < (volume (CalculusOfVariations.unitBall m)).toReal :=
      ENNReal.toReal_pos (tk_unitBall_isOpen.measure_pos volume tk_unitBall_nonempty).ne' hBfin.ne
    -- so every average in Dacorogna's formula is at least `f (A)`: `f^{qc} (A) ≥ f (A)`
    have hge : (f A : EReal) ≤ qcEnvelope f A := by
      rw [← cov_qcEnvelope_eq, External.KinderlehrerPedregal.dacorognaFormula_holds d m f hf A]
      refine le_iInf₂ fun φ hφ => ?_
      obtain ⟨⟨K, hK⟩, h0⟩ := hφ
      have := hball φ K hK h0 (tk_integrableOn_comp hfI A hK hBfin)
      rw [EReal.coe_le_coe_iff, le_inv_mul_iff₀ hBpos]
      exact this
    -- and `f^{qc}` is a quasiconvex minorant, equal to `f` at `A`
    rcases tk_qc_cases hf with ⟨_, hbot⟩ | ⟨Q, hQI, hQQ, hQf, _, hQe⟩
    · rw [hbot A] at hge
      exact absurd hge (not_le.2 (EReal.bot_lt_coe _))
    · refine ⟨Q, hQI, hQQ, hQf, le_antisymm (hQf A) ?_⟩
      rw [hQe] at hge
      exact EReal.coe_le_coe_iff.1 hge
  · rintro ⟨g, hgI, hgQ, hgf, hgA⟩ φ K hφ h0 hint
    rw [← hgA]
    exact (hgQ A φ K hφ h0 (tk_integrableOn_comp hgI A hφ hvol)).trans
      (setIntegral_mono (tk_integrableOn_comp hgI A hφ hvol) hint fun x => hgf _)

-- The proof does not use all of the paper's hypotheses (see the docstring).
set_option linter.unusedVariables false in
/-- **Proposition 2.3 (a)** (`prop:envelope`): for `p ∈ (1, ∞)` and a continuous `f` that is
`p`-homogeneous or positively `p`-homogeneous, each of `f^{rc}`, `f^{qc}` is either identically
`−∞` or finite-valued, and in the second case it has the same type of homogeneity as `f`. 

Proof. The paper gives none ("follows directly from the dual envelope formulas above"). The
formal proof argues with the definitions of the envelopes. Each envelope is `≡ −∞` when there is no
minorant of its kind; otherwise it is the largest one (for `f^{rc}` by the proof of Proposition 2.4,
`tk_rc_cases`; for `f^{qc}`, the supremum of quasiconvex integrands below `f` is one, `tk_qc_cases`),
finite. For `s ≠ 0` under which `f` is homogeneous, `A ↦ |s|^p g (s⁻¹ A)` is again a minorant of the
same kind (it is rank-one convex, resp. quasiconvex since `s⁻¹ (A + ∇φ) = s⁻¹ A + ∇ (s⁻¹ φ)`), which
gives the homogeneity of the largest minorant (`tk_hom_core`), and the value `0` at `0` from
`s = 2`. Dacorogna's formula, the dual formula for `f^{qc}`, is not a hypothesis here and is not
used. The hypothesis `hhom` is not used (each homogeneity is concluded under its own hypothesis),
and `1 < p` is used only as `0 < p`.-/
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
  have hp0 : 0 < p := by linarith
  refine ⟨?_, ?_⟩
  · rcases tk_rc_cases hf with ⟨_, hbot⟩ | ⟨G, hGI, hGR, hGf, hmax, hGe⟩
    · exact Or.inl hbot
    · right
      have hval : (fun A => (rcEnvelope f A).toReal) = G := funext fun A => by
        rw [hGe]; rfl
      rw [hval]
      refine ⟨fun A => by rw [hGe]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩,
        tk_hom_types hp0 fun s hs hfs A => ?_⟩
      exact tk_rc_transform ⟨hGI, hGR, hGf⟩ hmax _ (tk_smul_linear_rank (inv_ne_zero hs))
        (Real.rpow_nonneg (abs_nonneg s) p) (tk_scale_f hs hfs) A
  · rcases tk_qc_cases hf with ⟨_, hbot⟩ | ⟨Q, hQI, hQQ, hQf, hmax, hQe⟩
    · exact Or.inl hbot
    · right
      have hval : (fun A => (qcEnvelope f A).toReal) = Q := funext fun A => by
        rw [hQe]; rfl
      rw [hval]
      refine ⟨fun A => by rw [hQe]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩,
        tk_hom_types hp0 fun s hs hfs A => ?_⟩
      exact tk_qc_scale ⟨hQI, hQQ, hQf⟩ hmax (Real.rpow_pos_of_pos (abs_pos.2 hs) p)
        (tk_scale_f hs hfs) A

/-- Matrix multiplication by an orthogonal matrix preserves Lebesgue measure. -/
private lemma tk_measurePreserving_orth {V : Matrix (Fin d) (Fin d) ℝ}
    (hV : V ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    MeasurePreserving (Matrix.toLin' V : (Fin d → ℝ) →ₗ[ℝ] Fin d → ℝ) volume volume := by
  have hdet : (Matrix.toLin' V).det = V.det := LinearMap.det_toLin' V
  have h1 : V.det * V.det = 1 := by
    have := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hV)
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have habs : |(LinearMap.det (Matrix.toLin' V))⁻¹| = 1 := by
    rw [hdet, abs_inv]
    have : |V.det| * |V.det| = 1 := by rw [← abs_mul, h1, abs_one]
    have h0 : 0 ≤ |V.det| := abs_nonneg _
    have : |V.det| = 1 := by nlinarith
    rw [this, inv_one]
  refine ⟨(Matrix.toLin' V).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; intro h; simp [h] at h1),
    habs, ENNReal.ofReal_one, one_smul]

/-- The chain rule for `ψ = V φ (Vᵀ ·)`: `∇ψ (y) = V ∇φ (Vᵀ y) Vᵀ` where `φ` is differentiable at
`Vᵀ y`. -/
private lemma tk_grad_conj {φ : (Fin d → ℝ) → Fin d → ℝ} (V : Matrix (Fin d) (Fin d) ℝ)
    (y : Fin d → ℝ) (hdiff : DifferentiableAt ℝ φ (Vᵀ *ᵥ y)) :
    jac (fun z => V *ᵥ φ (Vᵀ *ᵥ z)) y = V * jac φ (Vᵀ *ᵥ y) * Vᵀ := by
  set L : (Fin d → ℝ) →L[ℝ] Fin d → ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' V)
  set Lt : (Fin d → ℝ) →L[ℝ] Fin d → ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' Vᵀ)
  set D := fderiv ℝ φ (Vᵀ *ᵥ y)
  have hLt : ∀ z, Lt z = Vᵀ *ᵥ z := fun z => rfl
  have hL : ∀ z, L z = V *ᵥ z := fun z => rfl
  have hψ : HasFDerivAt (fun z => V *ᵥ φ (Vᵀ *ᵥ z)) (L.comp (D.comp Lt)) y := by
    have h1 : HasFDerivAt (fun z => φ (Lt z)) (D.comp Lt) y :=
      hdiff.hasFDerivAt.comp y Lt.hasFDerivAt
    exact L.hasFDerivAt.comp y h1
  have hcomp : ∀ (w : Fin d → ℝ) (a : Fin d) (v : Fin d → ℝ),
      DifferentiableAt ℝ φ w → fderiv ℝ (fun z => φ z a) w v = fderiv ℝ φ w v a :=
    fun w a v hw => by rw [(hasFDerivAt_pi'.1 hw.hasFDerivAt a).fderiv]; rfl
  ext i k
  simp only [jac, Matrix.of_apply]
  rw [(hasFDerivAt_pi'.1 hψ i).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, hL, hLt]
  have hcol : Vᵀ *ᵥ (Pi.single k 1 : Fin d → ℝ) = ∑ b, V k b • (Pi.single b 1 : Fin d → ℝ) := by
    ext c
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.transpose_apply, Finset.sum_apply]
  rw [hcol, map_sum]
  simp only [map_smul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [hcomp _ _ _ hdiff, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.of_apply]
  ring

/-- Conjugation by an orthogonal `V` preserves quasiconvexity: with `ψ (y) = V φ (Vᵀ y)`, which
vanishes off the rotated cube `V ((0, 1)^d)`, `∫_{(0,1)^d} g (V (B + ∇φ) Vᵀ) = ∫_{V (0,1)^d}
g (V B Vᵀ + ∇ψ)` (orthogonal change of variables), and `g` is quasiconvex on the rotated cube
(Lemma 2.2, domain independence). -/
private lemma tk_quasiconvex_conj {g : Matrix (Fin d) (Fin d) ℝ → ℝ} (hgI : IsIntegrand g)
    (hgQ : Quasiconvex g) {V : Matrix (Fin d) (Fin d) ℝ}
    (hV : V ∈ Matrix.orthogonalGroup (Fin d) ℝ) : Quasiconvex fun B => g (V * B * Vᵀ) := by
  intro B φ K hφ h0 _
  have hVV : Vᵀ * V = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).1 hV
  have hVV' : V * Vᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).1 hV
  have hVt : Vᵀ ∈ Matrix.orthogonalGroup (Fin d) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff (Fin d) ℝ, Matrix.transpose_transpose]; exact hVV
  set L : (Fin d → ℝ) →L[ℝ] Fin d → ℝ := LinearMap.toContinuousLinearMap (Matrix.toLin' V)
  set Lt : (Fin d → ℝ) →L[ℝ] Fin d → ℝ := LinearMap.toContinuousLinearMap (Matrix.toLin' Vᵀ)
  have hL : ∀ z, L z = V *ᵥ z := fun z => rfl
  have hLt : ∀ z, Lt z = Vᵀ *ᵥ z := fun z => rfl
  have hLLt : ∀ z, Lt (L z) = z := fun z => by
    rw [hL, hLt, Matrix.mulVec_mulVec, hVV, Matrix.one_mulVec]
  have hmpL : MeasurePreserving L volume volume := tk_measurePreserving_orth hV
  have hmpLt : MeasurePreserving Lt volume volume := tk_measurePreserving_orth hVt
  set ψ : (Fin d → ℝ) → Fin d → ℝ := fun z => V *ᵥ φ (Vᵀ *ᵥ z)
  have hψ : LipschitzWith (‖L‖₊ * (K * ‖Lt‖₊)) ψ :=
    L.lipschitzWith.comp (hφ.comp Lt.lipschitzWith)
  set Ω : Set (Fin d → ℝ) := Lt ⁻¹' unitCube d
  have hΩm : MeasurableSet Ω :=
    Lt.continuous.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  have hΩb : Bornology.IsBounded Ω := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨‖L‖, fun y hy => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖Lt y‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have := hy i (Set.mem_univ _)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [this.1], this.2.le⟩
    calc ‖y‖ = ‖L (Lt y)‖ := by
          rw [hL, hLt, Matrix.mulVec_mulVec, hVV', Matrix.one_mulVec]
      _ ≤ ‖L‖ * ‖Lt y‖ := L.le_opNorm _
      _ ≤ ‖L‖ * 1 := by gcongr
      _ = ‖L‖ := mul_one _
  have hΩvol : volume Ω = 1 := by
    show volume (Lt ⁻¹' unitCube d) = 1
    rw [hmpLt.measure_preimage (s := unitCube d)
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet]
    exact volume_unitCube d
  have hΩfin : volume Ω < ⊤ := by rw [hΩvol]; exact ENNReal.one_lt_top
  have hψ0 : ∀ y ∉ Ω, ψ y = 0 := fun y hy => by
    have hy' : Vᵀ *ᵥ y ∉ unitCube d := hy
    simp only [ψ, h0 _ hy', Matrix.mulVec_zero]
  -- quasiconvexity of `g` at `V B Vᵀ` on the rotated cube
  have hgΩ := External.Rindler.rd_quasiconvexAtOn_of_unitCube hgI.1 hgI.2 hΩb hΩm
    ((cov_quasiconvexAtOn_unitCube_iff g (V * B * Vᵀ)).2 (hgQ _))
  have key := hgΩ ψ _ hψ hψ0 (tk_integrableOn_comp hgI _ hψ hΩfin)
  rw [hΩvol, ENNReal.toReal_one, one_mul] at key
  -- change of variables `y = V x`
  have hLtL : ∀ z, L (Lt z) = z := fun z => by
    rw [hL, hLt, Matrix.mulVec_mulVec, hVV', Matrix.one_mulVec]
  let e : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
    { toFun := L, invFun := Lt, left_inv := hLLt, right_inv := hLtL,
      measurable_toFun := L.continuous.measurable, measurable_invFun := Lt.continuous.measurable }
  have hcv := hmpL.setIntegral_preimage_emb e.measurableEmbedding
    (fun y => g (V * B * Vᵀ + CalculusOfVariations.grad ψ y)) Ω
  have hpre : (L : (Fin d → ℝ) → Fin d → ℝ) ⁻¹' Ω = unitCube d := by
    ext x; simp only [Ω, Set.mem_preimage, hLLt]
  change (L : (Fin d → ℝ) → Fin d → ℝ) ⁻¹' Ω = _ at hpre
  rw [hpre] at hcv
  rw [← hcv] at key
  refine key.trans (le_of_eq (setIntegral_congr_ae
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo) ?_))
  filter_upwards [hφ.ae_differentiableAt] with x hx _
  have hgrad := tk_grad_conj (φ := φ) V (L x) (by rw [← hLt, hLLt]; exact hx)
  rw [← hLt, hLLt] at hgrad
  show g (V * B * Vᵀ + jac ψ (L x)) = g (V * (B + jac φ x) * Vᵀ)
  rw [hgrad, Matrix.mul_add, Matrix.add_mul]

-- The proof does not use all of the paper's hypotheses (see the docstring).
set_option linter.unusedVariables false in
/-- **Proposition 2.3 (b)** (`prop:envelope`): for `p ∈ (1, ∞)` and a continuous `f` on
`ℝ^{d×d}` that is `p`-homogeneous or positively `p`-homogeneous, both envelopes preserve
conjugation invariance, and the rank-one convex envelope preserves transposition invariance. 

Proof. The paper gives none. For `f^{rc}`: conjugation `A ↦ V A Vᵀ` by an orthogonal `V` and
transposition are linear and preserve the rank, so `A ↦ f^{rc} (V A Vᵀ)` and `A ↦ f^{rc} (Aᵀ)` are
rank-one convex minorants of `f` (`tk_rc_transform`); hence `f^{rc} (V A Vᵀ) ≤ f^{rc} (A)` for every
`V ∈ O (d)`, and equality follows by applying this to `Vᵀ`; the same for transposition. For `f^{qc}`
the same argument, with the fact that `A ↦ g (V A Vᵀ)` is quasiconvex for a quasiconvex `g`
(`tk_quasiconvex_conj`): with `ψ (y) = V φ (Vᵀ y)`, an orthogonal change of variables turns
`∫_{(0,1)^d} g (V (B + ∇φ) Vᵀ)` into an integral over the rotated cube `V ((0, 1)^d)`, on which `g`
is quasiconvex by Lemma 2.2 (domain independence,
`External.Rindler.rd_quasiconvexAtOn_of_unitCube`); this is the use of Lemma 2.2 (ii) that the
inventory notes (E8). The hypotheses `hp`, `hhom` are not used.-/
theorem proposition2_3_b {p : ℝ} (hp : 1 < p) {f : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hf : Continuous f) (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) :
    (IsConjugationInvariant f →
      (∀ U ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∀ A, rcEnvelope f (U * A * Uᵀ) = rcEnvelope f A) ∧
      (∀ U ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∀ A, qcEnvelope f (U * A * Uᵀ) = qcEnvelope f A)) ∧
    (IsTranspositionInvariant f → ∀ A, rcEnvelope f Aᵀ = rcEnvelope f A) := by
  -- conjugation by an orthogonal `V` and transposition are linear and preserve the rank
  let conjL : Matrix (Fin d) (Fin d) ℝ → (Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ) :=
    fun V => { toFun := fun X => V * X * Vᵀ
               map_add' := fun X Y => by simp [Matrix.mul_add, Matrix.add_mul]
               map_smul' := fun c X => by simp }
  have hconjL : ∀ V ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∀ X, (conjL V X).rank = X.rank := by
    intro V hV X
    have h1 : IsUnit V.det := Matrix.isUnit_det_of_left_inverse ((Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).1 hV)
    have h2 : IsUnit Vᵀ.det := by rw [Matrix.det_transpose]; exact h1
    change (V * X * Vᵀ).rank = X.rank
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ h2, Matrix.rank_mul_eq_right_of_isUnit_det _ _ h1]
  have horth : ∀ V ∈ Matrix.orthogonalGroup (Fin d) ℝ, Vᵀ ∈ Matrix.orthogonalGroup (Fin d) ℝ := by
    intro V hV
    rw [Matrix.mem_orthogonalGroup_iff (Fin d) ℝ, Matrix.transpose_transpose]
    exact (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).1 hV
  have hback : ∀ V ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∀ X, Vᵀ * (V * X * Vᵀ) * Vᵀᵀ = X := by
    intro V hV X
    rw [Matrix.transpose_transpose]
    have h1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).1 hV
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  let trL : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ :=
    { toFun := Matrix.transpose
      map_add' := Matrix.transpose_add
      map_smul' := fun c X => Matrix.transpose_smul c X }
  refine ⟨fun hconj => ⟨fun U hU A => ?_, fun U hU A => ?_⟩, fun htr A => ?_⟩
  · -- `f^{rc}`: `A ↦ f^{rc} (V A Vᵀ)` is a rank-one convex minorant
    rcases tk_rc_cases hf with ⟨_, hbot⟩ | ⟨G, hGI, hGR, hGf, hmax, hGe⟩
    · rw [hbot, hbot]
    · have h1 : ∀ V ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∀ X, G (V * X * Vᵀ) ≤ G X := by
        intro V hV X
        have := tk_rc_transform ⟨hGI, hGR, hGf⟩ hmax (conjL V) (hconjL V hV) zero_le_one
          (fun B => by rw [one_mul]; exact (hconj V hV B).le) X
        simpa [conjL] using this
      rw [hGe, hGe, EReal.coe_eq_coe_iff]
      refine le_antisymm (h1 U hU A) ?_
      have := h1 Uᵀ (horth U hU) (U * A * Uᵀ)
      rwa [hback U hU A] at this
  · -- `f^{qc}`: conjugation of a quasiconvex minorant, on the rotated cube (Lemma 2.2)
    rcases tk_qc_cases hf with ⟨_, hbot⟩ | ⟨Q, hQI, hQQ, hQf, hmax, hQe⟩
    · rw [hbot, hbot]
    · have h1 : ∀ V ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∀ X, Q (V * X * Vᵀ) ≤ Q X := by
        intro V hV X
        have hc : Continuous fun B : Matrix (Fin d) (Fin d) ℝ => V * B * Vᵀ :=
          (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
        have hI : IsIntegrand fun B => Q (V * B * Vᵀ) := by
          refine ⟨hQI.1.comp hc, fun A => ?_⟩
          obtain ⟨W, hW, C, hC⟩ := hQI.2 (V * A * Vᵀ)
          exact ⟨_, hc.continuousAt.preimage_mem_nhds hW, C, fun B hB => hC _ hB⟩
        exact hmax _ hI (tk_quasiconvex_conj hQI hQQ hV)
          (fun B => (hQf _).trans (hconj V hV B).le) X
      rw [hQe, hQe, EReal.coe_eq_coe_iff]
      refine le_antisymm (h1 U hU A) ?_
      have := h1 Uᵀ (horth U hU) (U * A * Uᵀ)
      rwa [hback U hU A] at this
  · -- `f^{rc}`: `A ↦ f^{rc} (Aᵀ)` is a rank-one convex minorant
    rcases tk_rc_cases hf with ⟨_, hbot⟩ | ⟨G, hGI, hGR, hGf, hmax, hGe⟩
    · rw [hbot, hbot]
    · have h1 : ∀ X, G Xᵀ ≤ G X := by
        intro X
        have := tk_rc_transform ⟨hGI, hGR, hGf⟩ hmax trL (fun X => Matrix.rank_transpose X)
          zero_le_one (fun B => by rw [one_mul]; exact (htr B).le) X
        simpa [trL] using this
      rw [hGe, hGe, EReal.coe_eq_coe_iff]
      refine le_antisymm (h1 A) ?_
      have := h1 Aᵀ
      rwa [Matrix.transpose_transpose] at this

/-- Both homogeneity types give `f (t B) = t^p f (B)` for `t > 0`. -/
private lemma tk_pos_hom {p : ℝ} {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) :
    ∀ t : ℝ, 0 < t → ∀ B, f (t • B) = t ^ p * f B := by
  rcases hhom with h | h
  · intro t ht B; rw [h, abs_of_pos ht]
  · exact h

private lemma tk_f_zero {p : ℝ} (hp : 0 < p) {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) : f 0 = 0 :=
  tk_zero_of_hom hp (by rw [abs_of_pos two_pos]; exact tk_pos_hom hhom 2 two_pos 0)

/-- The proof of `proposition2_3_c_left`: `f^{rc} ≤ f` with equality at `0`. -/
private lemma tk_c_left {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hrc : RankOneConvexAt f 0) (hqc : QuasiconvexAt (fun A => (rcEnvelope f A).toReal) 0) :
    QuasiconvexAt f 0 := by
  have hvol : volume (unitCube m) < ⊤ := by rw [volume_unitCube]; exact ENNReal.one_lt_top
  obtain ⟨g, hgI, hgR, hgf, hg0⟩ := hrc
  rcases tk_rc_cases hf with ⟨hno, _⟩ | ⟨G, hGI, hGR, hGf, hmax, hGe⟩
  · exact (hno g hgI hgR hgf).elim
  · have hval : (fun A => (rcEnvelope f A).toReal) = G := funext fun A => by rw [hGe]; rfl
    rw [hval] at hqc
    have hG0 : G 0 = f 0 := le_antisymm (hGf 0) (hg0 ▸ hmax g hgI hgR hgf 0)
    intro φ K hφ h0 hint
    have h1 := hqc φ K hφ h0 (tk_integrableOn_comp hGI 0 hφ hvol)
    rw [hG0] at h1
    exact h1.trans (setIntegral_mono (tk_integrableOn_comp hGI 0 hφ hvol) hint fun x => hGf _)

-- The proof does not use all of the paper's hypotheses (see the docstring).
set_option linter.unusedVariables false in
/-- **Proposition 2.3 (c)** (`prop:envelope`): for `p ∈ (1, ∞)` and a continuous `f` that is
`p`-homogeneous or positively `p`-homogeneous and rank-one convex at `0`, `f^{rc}` is
quasiconvex at `0` if and only if `f` is. Dacorogna's formula
(`External.KinderlehrerPedregal.dacorognaFormula_holds`) gives the implication "`f` quasiconvex
at `0` ⇒ `f^{rc}` quasiconvex at `0`" (line 559); the other implication is
`proposition2_3_c_left`. (`f^{rc}` is finite when `f` is rank-one convex at `0`,
and is read through `EReal.toReal`.) 

Proof. "`f^{rc}` quasiconvex at `0` ⇒ `f` quasiconvex at `0`" is `proposition2_3_c_left`. Conversely,
line 559 gives a quasiconvex minorant `g ≤ f` with `g (0) = f (0)`; `g` is rank-one convex
(Lemma 2.2, `External.Rindler.rankOneConvex_of_quasiconvex`), so `g ≤ f^{rc} ≤ f`, and
`∫ f^{rc} (∇φ) ≥ ∫ g (∇φ) ≥ g (0) = f^{rc} (0)`. The hypotheses `hp`, `hhom` are not used.-/
theorem proposition2_3_c {p : ℝ}
    (hp : 1 < p) {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) (hrc : RankOneConvexAt f 0) :
    QuasiconvexAt (fun A => (rcEnvelope f A).toReal) 0 ↔ QuasiconvexAt f 0 := by
  have hvol : volume (unitCube m) < ⊤ := by rw [volume_unitCube]; exact ENNReal.one_lt_top
  refine ⟨tk_c_left hf hrc, fun hqc => ?_⟩
  -- line 559: a quasiconvex minorant `g ≤ f` with `g (0) = f (0)`; it is rank-one convex
  -- (Lemma 2.2), so `g ≤ f^{rc} ≤ f`
  obtain ⟨g, hgI, hgQ, hgf, hg0⟩ := (quasiconvexAt_iff_exists_minorant hf 0).1 hqc
  have hgR : RankOneConvex g := tk_rankOneConvex_of_cov
    (External.Rindler.rankOneConvex_of_quasiconvex hgI.1 hgI.2
      fun A => (cov_quasiconvexAtOn_unitCube_iff g A).2 (hgQ A))
  rcases tk_rc_cases hf with ⟨hno, _⟩ | ⟨G, hGI, hGR, hGf, hmax, hGe⟩
  · exact (hno g hgI hgR hgf).elim
  · have hval : (fun A => (rcEnvelope f A).toReal) = G := funext fun A => by rw [hGe]; rfl
    rw [hval]
    have hgG := hmax g hgI hgR hgf
    have hG0 : G 0 = f 0 := le_antisymm (hGf 0) (hg0 ▸ hgG 0)
    intro φ K hφ h0 hint
    rw [hG0, ← hg0]
    exact (hgQ 0 φ K hφ h0 (tk_integrableOn_comp hgI 0 hφ hvol)).trans
      (setIntegral_mono (tk_integrableOn_comp hgI 0 hφ hvol) hint fun x => hgG _)

-- The proof does not use all of the paper's hypotheses (see the docstring).
set_option linter.unusedVariables false in
/-- **Proposition 2.3 (c)** (`prop:envelope`), the implication that the main theorems use: if `f`
is rank-one convex at `0` and `f^{rc}` is quasiconvex at `0`, then so is `f`. 

Proof. Rank-one convexity at `0` gives `f^{rc} (0) = f (0)` and makes `f^{rc}` a rank-one convex
integrand `≤ f`, continuous by Lemma 2.1 (`tk_rc_cases`); then
`∫ f (∇φ) ≥ ∫ f^{rc} (∇φ) ≥ f^{rc} (0) = f (0)`. The hypotheses `hp`, `hhom` are not used.-/
theorem proposition2_3_c_left {p : ℝ} (hp : 1 < p) {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Continuous f) (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f)
    (hrc : RankOneConvexAt f 0) (hqc : QuasiconvexAt (fun A => (rcEnvelope f A).toReal) 0) :
    QuasiconvexAt f 0 := by
  exact tk_c_left hf hrc hqc

/-- **Consequence of Proposition 2.3** (`cs-envelope-cons`, lines 573–575): for `p ∈ (1, ∞)` and a
continuous `f` that is `p`-homogeneous or positively `p`-homogeneous,
`f^{rc} (0), f^{qc} (0) ∈ {0, −∞}`. 

Proof: by Proposition 2.3 (a), a finite envelope `F` is homogeneous of one of the two types, so
`F (0) = F (2 · 0) = 2^p F (0)`, and `F (0) = 0`.-/
theorem envelope_zero {p : ℝ} (hp : 1 < p) {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Continuous f) (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) :
    (rcEnvelope f 0 = 0 ∨ rcEnvelope f 0 = ⊥) ∧ (qcEnvelope f 0 = 0 ∨ qcEnvelope f 0 = ⊥) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hrc, hqc⟩ := proposition2_3_a hp hf hhom
  have key : ∀ E : Matrix (Fin d) (Fin m) ℝ → EReal, ((∀ A, E A = ⊥) ∨
      ((∀ A, E A ≠ ⊥ ∧ E A ≠ ⊤) ∧
        (IsPHomogeneous p f → IsPHomogeneous p fun A => (E A).toReal) ∧
        (IsPosPHomogeneous p f → IsPosPHomogeneous p fun A => (E A).toReal))) →
      E 0 = 0 ∨ E 0 = ⊥ := by
    intro E h
    rcases h with h | ⟨hfin, h1, h2⟩
    · exact Or.inr (h 0)
    · left
      have h2' : (fun A => (E A).toReal) ((2 : ℝ) • 0) =
          |(2 : ℝ)| ^ p * (fun A => (E A).toReal) 0 := by
        rcases hhom with hh | hh
        · exact h1 hh 2 0
        · rw [abs_of_pos two_pos]; exact h2 hh 2 two_pos 0
      have h0 : (E 0).toReal = 0 := tk_zero_of_hom (G := fun A => (E A).toReal) hp0 h2'
      rw [← EReal.coe_toReal (hfin 0).2 (hfin 0).1, h0]
      rfl
  exact ⟨key _ hrc, key _ hqc⟩

/-- **Consequence of Proposition 2.3** (`cs-envelope-cons`, lines 577–578): for `p ∈ (1, ∞)` and a
continuous `f` that is `p`-homogeneous or positively `p`-homogeneous, rank-one convexity at any
matrix implies rank-one convexity at `0`. 

Proof (lines 577–578): a rank-one convex minorant exists, so `f^{rc}` is finite and is the largest
rank-one convex integrand below `f` (`tk_rc_cases`); `f^{rc} (0) = 0 = f (0)` by `envelope_zero` and
the homogeneity of `f`, so `f^{rc}` witnesses rank-one convexity at `0`.-/
theorem rankOneConvexAt_zero_of_rankOneConvexAt {p : ℝ} (hp : 1 < p)
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) {A : Matrix (Fin d) (Fin m) ℝ}
    (hA : RankOneConvexAt f A) : RankOneConvexAt f 0 := by
  obtain ⟨g, hgI, hgR, hgf, -⟩ := hA
  rcases tk_rc_cases hf with ⟨hno, _⟩ | ⟨G, hGI, hGR, hGf, _, hGe⟩
  · exact (hno g hgI hgR hgf).elim
  · have h0 : G 0 = 0 := by
      rcases (envelope_zero hp hf hhom).1 with h | h
      · rw [hGe] at h; exact_mod_cast h
      · rw [hGe] at h; exact absurd h (EReal.coe_ne_bot _)
    exact ⟨G, hGI, hGR, hGf, h0.trans (tk_f_zero (by linarith) hhom).symm⟩

/-- **Consequence of Proposition 2.3** (`cs-envelope-cons`, lines 577–578 and 206–209): for
`p ∈ (1, ∞)` and a continuous `f` that is `p`-homogeneous or positively `p`-homogeneous,
quasiconvexity at any matrix implies quasiconvexity at `0`. 

Proof (lines 559 and 573–578): quasiconvexity at `A` gives a quasiconvex minorant `g ≤ f` (line 559,
`quasiconvexAt_iff_exists_minorant`, by Dacorogna's formula), so `f^{qc}` is finite and is the
largest quasiconvex integrand below `f` (`tk_qc_cases`); `f^{qc} (0) = 0 = f (0)` by
`envelope_zero` and the homogeneity of `f`, so `f^{qc}` is a quasiconvex minorant equal to `f` at
`0`, and `f` is quasiconvex at `0` by line 559 again.-/
theorem quasiconvexAt_zero_of_quasiconvexAt {p : ℝ} (hp : 1 < p)
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) {A : Matrix (Fin d) (Fin m) ℝ}
    (hA : QuasiconvexAt f A) : QuasiconvexAt f 0 := by
  -- line 559: a quasiconvex minorant of `f`, so `f^{qc}` is the largest one
  obtain ⟨g, hgI, hgQ, hgf, -⟩ := (quasiconvexAt_iff_exists_minorant hf A).1 hA
  rcases tk_qc_cases hf with ⟨hno, _⟩ | ⟨Q, hQI, hQQ, hQf, _, hQe⟩
  · exact (hno g hgI hgQ hgf).elim
  · -- `f^{qc} (0) ∈ {0, −∞}` and `f^{qc}` is finite, so `f^{qc} (0) = 0 = f (0)`
    have h0 : Q 0 = 0 := by
      rcases (envelope_zero hp hf hhom).2 with h | h
      · rw [hQe] at h; exact_mod_cast h
      · rw [hQe] at h; exact absurd h (EReal.coe_ne_bot _)
    -- line 559 again, with the minorant `f^{qc}`
    exact (quasiconvexAt_iff_exists_minorant hf 0).2
      ⟨Q, hQI, hQQ, hQf, h0.trans (tk_f_zero (by linarith) hhom).symm⟩

/-- **Consequence of Proposition 2.3** (`cs-envelope-cons`, lines 206–209): for continuous
(positively) homogeneous integrands, failure of quasiconvexity at `0` implies failure at every
matrix. 

Proof: the contrapositive of `quasiconvexAt_zero_of_quasiconvexAt`.-/
theorem nowhereQuasiconvex_of_not_quasiconvexAt_zero {p : ℝ} (hp : 1 < p)
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hhom : IsPHomogeneous p f ∨ IsPosPHomogeneous p f) (h0 : ¬ QuasiconvexAt f 0) :
    NowhereQuasiconvex f :=
  fun _ hA => h0 (quasiconvexAt_zero_of_quasiconvexAt hp hf hhom hA)

/-! ### Helpers shared by the later sections -/

/-- `C < C^{qc}` (with `C ≥ 0`) makes `F_C` fail to be quasiconvex at `0`: the definition of
`C^{qc}`. -/
theorem not_quasiconvexAt_of_lt_qcThreshold {F : ℝ → Matrix (Fin d) (Fin m) ℝ → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (h : ENNReal.ofReal C < qcThreshold F) : ¬ QuasiconvexAt (F C) 0 :=
  fun hq => h.not_ge (iInf₂_le (f := fun (C : ℝ) (_ : 0 ≤ C ∧ QuasiconvexAt (F C) 0) =>
    ENNReal.ofReal C) C ⟨hC, hq⟩)

theorem IsHomogeneousPolynomial.congr {n : ℕ} {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : IsHomogeneousPolynomial n f) (h : ∀ A, f A = g A) : IsHomogeneousPolynomial n g := by
  obtain ⟨P, hP, hPf⟩ := hf
  exact ⟨P, hP, fun A => (h A).symm.trans (hPf A)⟩

theorem IsHomogeneousPolynomial.add {n : ℕ} {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : IsHomogeneousPolynomial n f) (hg : IsHomogeneousPolynomial n g) :
    IsHomogeneousPolynomial n fun A => f A + g A := by
  obtain ⟨P, hP, hPf⟩ := hf
  obtain ⟨Q, hQ, hQg⟩ := hg
  exact ⟨P + Q, hP.add hQ, fun A => by simp only [hPf A, hQg A, MvPolynomial.eval_add]⟩

theorem IsHomogeneousPolynomial.mul {n k : ℕ} {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : IsHomogeneousPolynomial n f) (hg : IsHomogeneousPolynomial k g) :
    IsHomogeneousPolynomial (n + k) fun A => f A * g A := by
  obtain ⟨P, hP, hPf⟩ := hf
  obtain ⟨Q, hQ, hQg⟩ := hg
  exact ⟨P * Q, hP.mul hQ, fun A => by simp only [hPf A, hQg A, MvPolynomial.eval_mul]⟩

theorem IsHomogeneousPolynomial.const_mul {n : ℕ} {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : IsHomogeneousPolynomial n f) (c : ℝ) :
    IsHomogeneousPolynomial n fun A => c * f A := by
  obtain ⟨P, hP, hPf⟩ := hf
  exact ⟨MvPolynomial.C c * P, hP.C_mul c, fun A => by
    simp only [hPf A, MvPolynomial.eval_mul, MvPolynomial.eval_C]⟩

/-- A polynomial is continuous. -/
theorem IsHomogeneousPolynomial.continuous {n : ℕ} {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : IsHomogeneousPolynomial n f) : Continuous f := by
  obtain ⟨P, -, hP⟩ := hf
  rw [show f = fun A => MvPolynomial.eval (fun ij : Fin d × Fin m => A ij.1 ij.2) P from
    funext hP]
  exact (MvPolynomial.continuous_eval P).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

/-! ### Rank-one Rademacher martingales -/

/-- The sum over `N + 1` signs, split by the first sign. -/
private lemma tk_sum_cons {N : ℕ} {E : Type*} [AddCommMonoid E] (g : (Fin (N + 1) → Bool) → E) :
    ∑ ε, g ε = ∑ ε', g (Fin.cons true ε') + ∑ ε', g (Fin.cons false ε') := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

/-- The expectation over `N + 1` signs, conditioned on the first sign. -/
private lemma tk_avg_cons {N : ℕ} (g : (Fin (N + 1) → Bool) → ℝ) :
    avg g = (avg (fun ε' => g (Fin.cons true ε')) + avg (fun ε' => g (Fin.cons false ε'))) / 2 := by
  simp only [avg]
  rw [tk_sum_cons, pow_succ]
  field_simp

private lemma tk_avg_zero (g : (Fin 0 → Bool) → ℝ) (ε₀ : Fin 0 → Bool) : avg g = g ε₀ := by
  simp only [avg, pow_zero, div_one]
  rw [Fintype.sum_unique]
  congr 1
  exact Subsingleton.elim _ _

private lemma tk_radMart_zero (M₀ : Matrix (Fin d) (Fin m) ℝ)
    (A : Fin 0 → (Fin 0 → Bool) → Matrix (Fin d) (Fin m) ℝ) (ε : Fin 0 → Bool) :
    radMart M₀ A 0 ε = M₀ := by
  simp [radMart, rad_mart_top]

/-- A martingale of horizon `N + 1`, conditioned on the first sign `b`: a martingale of horizon
`N` started at `M₀ + b A₀`. -/
private lemma tk_radMart_cons {N : ℕ} (M₀ : Matrix (Fin d) (Fin m) ℝ)
    (A : Fin (N + 1) → (Fin (N + 1) → Bool) → Matrix (Fin d) (Fin m) ℝ) (b : Bool)
    (ε' : Fin N → Bool) :
    radMart M₀ A (N + 1) (Fin.cons b ε') =
      radMart (M₀ + coin b • A 0 (Fin.cons b ε')) (fun k ε' => A k.succ (Fin.cons b ε')) N ε' := by
  simp only [radMart, rad_mart_top, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  abel

/-- The first increment of a predictable sequence is deterministic. -/
private lemma tk_inc_zero {N : ℕ} {A : Fin (N + 1) → (Fin (N + 1) → Bool) → Matrix (Fin d) (Fin m) ℝ}
    (hA : IsPredictable A) (ε : Fin (N + 1) → Bool) : A 0 ε = A 0 (fun _ => true) :=
  hA 0 ε _ fun j hj => absurd hj (Fin.not_lt_zero j)

/-- Conditioned on the first sign, the increments are again predictable of rank `≤ 1`. -/
private lemma tk_isRankOne_tail {N : ℕ}
    {A : Fin (N + 1) → (Fin (N + 1) → Bool) → Matrix (Fin d) (Fin m) ℝ}
    (hA : IsRankOneIncrements A) (b : Bool) :
    IsRankOneIncrements (fun (k : Fin N) ε' => A k.succ (Fin.cons b ε')) := by
  refine ⟨fun k ε ε' h => hA.1 k.succ _ _ fun j hj => ?_, fun k ε => hA.2 _ _⟩
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp only [Fin.cons_succ]; exact h j (Fin.succ_lt_succ_iff.1 hj)

/-- A martingale of horizon `N + 1` from a first increment `A₀` and, for each first sign `b`,
increments `I b` of horizon `N` on the remaining signs. -/
private def tkCons {N : ℕ} (A₀ : Matrix (Fin d) (Fin m) ℝ)
    (I : Bool → Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ) :
    Fin (N + 1) → (Fin (N + 1) → Bool) → Matrix (Fin d) (Fin m) ℝ :=
  fun k ε => Fin.cases (motive := fun _ => Matrix (Fin d) (Fin m) ℝ) A₀
    (fun k' => I (ε 0) k' (Fin.tail ε)) k

private lemma tk_isRankOne_tkCons {N : ℕ} {A₀ : Matrix (Fin d) (Fin m) ℝ}
    {I : Bool → Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ} (h₀ : A₀.rank ≤ 1)
    (hI : ∀ b, IsRankOneIncrements (I b)) : IsRankOneIncrements (tkCons A₀ I) := by
  refine ⟨fun k ε ε' h => ?_, fun k ε => ?_⟩
  · induction k using Fin.cases with
    | zero => rfl
    | succ k =>
      simp only [tkCons, Fin.cases_succ]
      have h0 : ε 0 = ε' 0 := h 0 (Fin.succ_pos k)
      rw [h0]
      exact (hI (ε' 0)).1 k _ _ fun j hj => h j.succ (Fin.succ_lt_succ_iff.2 hj)
  · induction k using Fin.cases with
    | zero => exact h₀
    | succ k => exact (hI _).2 _ _

private lemma tk_radMart_tkCons {N : ℕ} (M₀ A₀ : Matrix (Fin d) (Fin m) ℝ)
    (I : Bool → Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ) (b : Bool)
    (ε' : Fin N → Bool) :
    radMart M₀ (tkCons A₀ I) (N + 1) (Fin.cons b ε') = radMart (M₀ + coin b • A₀) (I b) N ε' := by
  rw [tk_radMart_cons]
  simp [tkCons]

/-- The law of the terminal value `M_N`, by conditioning on the first sign: `δ_{M₀}` for `N = 0`,
and `½ law (M | ε₀ = 1) + ½ law (M | ε₀ = −1)`. -/
private noncomputable def tkLaw : (N : ℕ) → Matrix (Fin d) (Fin m) ℝ →
    (Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ) → Measure (Matrix (Fin d) (Fin m) ℝ)
  | 0, M₀, _ => Measure.dirac M₀
  | N + 1, M₀, A =>
    ENNReal.ofReal (1 / 2) •
        tkLaw N (M₀ + A 0 (fun _ => true)) (fun k ε' => A k.succ (Fin.cons true ε')) +
      ENNReal.ofReal (1 / 2) •
        tkLaw N (M₀ - A 0 (fun _ => true)) (fun k ε' => A k.succ (Fin.cons false ε'))

/-- The law of the terminal value of a rank-one Rademacher martingale started at `M₀` is a dyadic
prelaminate with barycentre `M₀`, and `⟨g, law⟩ = E g (M_N)` (lines 661–677: the representation
of a martingale by splittings with `t = 1/2`). -/
private lemma tk_law {N : ℕ} : ∀ (M₀ : Matrix (Fin d) (Fin m) ℝ)
    (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ), IsRankOneIncrements A →
      IsDyadicPrelaminate (tkLaw N M₀ A) ∧ tkBary (tkLaw N M₀ A) = M₀ ∧
        ∀ g : Matrix (Fin d) (Fin m) ℝ → ℝ,
          ∫ X, g X ∂(tkLaw N M₀ A) = avg (fun ε => g (radMart M₀ A N ε)) := by
  induction N with
  | zero =>
    intro M₀ A _
    refine ⟨.dirac M₀, tk_bary_dirac M₀, fun g => ?_⟩
    simp only [tkLaw, integral_dirac]
    rw [tk_avg_zero _ (fun k => k.elim0), tk_radMart_zero]
  | succ N ih =>
    intro M₀ A hA
    set A₀ := A 0 (fun _ => true)
    obtain ⟨hD₁, hb₁, hi₁⟩ := ih (M₀ + A₀) _ (tk_isRankOne_tail hA true)
    obtain ⟨hD₂, hb₂, hi₂⟩ := ih (M₀ - A₀) _ (tk_isRankOne_tail hA false)
    have hrk : ((M₀ + A₀) - (M₀ - A₀)).rank ≤ 1 := by
      rw [show (M₀ + A₀) - (M₀ - A₀) = (2 : ℝ) • A₀ by module,
        Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero two_ne_zero)]
      exact hA.2 0 _
    obtain ⟨hD, hb⟩ := tk_dyadic_mid hrk hD₁ hb₁ hD₂ hb₂
    rw [show (1 / 2 : ℝ) • (M₀ + A₀ + (M₀ - A₀)) = M₀ by module] at hb
    refine ⟨hD, hb, fun g => ?_⟩
    have g₁ := (tk_prelaminate (tk_isPrelaminate_of_dyadic hD₁)).1
    have g₂ := (tk_prelaminate (tk_isPrelaminate_of_dyadic hD₂)).1
    simp only [tkLaw]
    rw [tk_integral_half g₁ g₂, hi₁, hi₂, tk_avg_cons (fun ε => g (radMart M₀ A (N + 1) ε))]
    simp only [tk_radMart_cons, tk_inc_zero hA.1 (Fin.cons _ _)]
    simp only [coin, ite_true, one_smul, Bool.false_eq_true, ite_false, neg_one_smul,
      ← sub_eq_add_neg]
    rfl

/-- The values `E f (M_N)` over the rank-one Rademacher martingales started at `A`. -/
private def tkMartVals (f : Matrix (Fin d) (Fin m) ℝ → ℝ) (A : Matrix (Fin d) (Fin m) ℝ) :
    Set ℝ :=
  {x | ∃ (N : ℕ) (I : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ),
    IsRankOneIncrements I ∧ avg (fun ε => f (radMart A I N ε)) = x}

/-- A value at horizon `N` is a value at every larger horizon (zero increments in front). -/
private lemma tk_martVals_pad {f : Matrix (Fin d) (Fin m) ℝ → ℝ} {A : Matrix (Fin d) (Fin m) ℝ}
    {N : ℕ} {I : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ} (hI : IsRankOneIncrements I)
    {N' : ℕ} (hN : N ≤ N') :
    ∃ J : Fin N' → (Fin N' → Bool) → Matrix (Fin d) (Fin m) ℝ,
      IsRankOneIncrements J ∧
        avg (fun ε => f (radMart A J N' ε)) = avg (fun ε => f (radMart A I N ε)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero => exact ⟨I, hI, rfl⟩
  | succ k ih =>
    obtain ⟨J, hJ, hJv⟩ := ih (Nat.le_add_right N k)
    refine ⟨tkCons 0 (fun _ => J), tk_isRankOne_tkCons (by rw [Matrix.rank_zero]; exact zero_le_one)
      fun _ => hJ, ?_⟩
    show avg (fun ε => f (radMart A (tkCons 0 fun _ => J) (N + k + 1) ε)) = _
    rw [← hJv, tk_avg_cons (fun ε => f (radMart A (tkCons 0 fun _ => J) (N + k + 1) ε))]
    simp only [tk_radMart_tkCons, smul_zero, add_zero]
    ring

/-- Midpoint gluing of martingales: first increment `±(B − C)/2`, then the martingale from `B`
or from `C`, padded to a common horizon. -/
private lemma tk_martVals_mid {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    {B C : Matrix (Fin d) (Fin m) ℝ} (hBC : (B - C).rank = 1) {v w : ℝ}
    (hv : v ∈ tkMartVals f B) (hw : w ∈ tkMartVals f C) :
    (v + w) / 2 ∈ tkMartVals f ((1 / 2 : ℝ) • (B + C)) := by
  obtain ⟨N₁, I₁, hI₁, rfl⟩ := hv
  obtain ⟨N₂, I₂, hI₂, rfl⟩ := hw
  obtain ⟨J₁, hJ₁, hJ₁v⟩ := tk_martVals_pad (f := f) (A := B) hI₁ (le_max_left N₁ N₂)
  obtain ⟨J₂, hJ₂, hJ₂v⟩ := tk_martVals_pad (f := f) (A := C) hI₂ (le_max_right N₁ N₂)
  let I : Bool → Fin (max N₁ N₂) → (Fin (max N₁ N₂) → Bool) → Matrix (Fin d) (Fin m) ℝ :=
    fun b => if b = true then J₁ else J₂
  have hI : ∀ b, IsRankOneIncrements (I b) := fun b => by
    cases b
    · exact hJ₂
    · exact hJ₁
  have h₀ : ((1 / 2 : ℝ) • (B - C)).rank ≤ 1 := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (by norm_num)), hBC]
  refine ⟨max N₁ N₂ + 1, tkCons ((1 / 2 : ℝ) • (B - C)) I, tk_isRankOne_tkCons h₀ hI, ?_⟩
  rw [tk_avg_cons, ← hJ₁v, ← hJ₂v]
  simp only [tk_radMart_tkCons, coin, ite_true, one_smul, Bool.false_eq_true, ite_false,
    neg_one_smul, I]
  rw [show (1 / 2 : ℝ) • (B + C) + (1 / 2 : ℝ) • (B - C) = B by module,
    show (1 / 2 : ℝ) • (B + C) + -((1 / 2 : ℝ) • (B - C)) = C by module]

/-- **Proposition 2.5** (`prop:rankonerademacher`): a continuous integrand `f` is rank-one convex
at `0` if and only if `f (0) ≤ E f (M_N)` for every finite rank-one Rademacher martingale `M`
started at `0`. 

Proof. "⇒" is the paper's (lines 661–688): the law of `M_N` is a dyadic prelaminate with
barycentre `0` (`tk_law`: conditioning on the first sign, a splitting with `t = 1/2`, lines
661–677), so for a rank-one convex minorant `g` with `g (0) = f (0)`, Proposition 2.4 gives
`f (0) = g (0) ≤ f^{rc} (0) ≤ ⟨f, law (M_N)⟩ = E f (M_N)`.
"⇐": Departure from the paper. The paper deduces it from Proposition 2.4 and the representation of
every dyadic prelaminate by a rank-one Rademacher martingale (lines 661–663). Under the reading of
Definition 2.4 used here (inventory E10: a splitting may take any part `c` of the mass of an
atom), a dyadic prelaminate can have weights that are not dyadic (split a third of `δ₀`), and then
it is the law of no martingale on the uniform binary tree; the step fails in this representation
(reasons 1 and 3). The formal proof runs the paper's argument for Proposition 2.4 on the infimum
`G (A) = inf E f (M_N)` over `Rad₁ (A)` instead (`tk_midpoint_principle` with `tkMartVals`:
martingales are glued at a midpoint by a first increment `±(B − C)/2`, after padding to a common
horizon), which gives a rank-one convex integrand `G ≤ f` with `G (0) ≥ f (0)` under the
hypothesis.-/
theorem proposition2_5 {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f) :
    RankOneConvexAt f 0 ↔
      ∀ (N : ℕ) (A : Fin N → (Fin N → Bool) → Matrix (Fin d) (Fin m) ℝ),
        IsRankOneIncrements A → f 0 ≤ avg fun ε => f (radMart 0 A N ε) := by
  constructor
  · -- the law of `M_N` is a dyadic prelaminate centred at `0` (lines 661–677), and Proposition 2.4
    rintro ⟨g, hgI, hgR, hgf, hg0⟩ N A hA
    obtain ⟨hD, hb, hi⟩ := tk_law 0 A hA
    have h1 : ((g 0 : ℝ) : EReal) ≤ rcEnvelope f 0 :=
      le_iSup₂_of_le (f := fun (h : Matrix (Fin d) (Fin m) ℝ → ℝ)
        (_ : IsIntegrand h ∧ RankOneConvex h ∧ ∀ B, h B ≤ f B) => (h 0 : EReal)) g
        ⟨hgI, hgR, hgf⟩ le_rfl
    rw [← proposition2_4 hf 0] at h1
    have h2 := h1.trans (iInf₂_le (tkLaw N 0 A) ⟨hD, tk_isBarycentre_iff.2 hb⟩)
    rw [hi f, hg0] at h2
    exact EReal.coe_le_coe_iff.1 h2
  · -- the argument of Proposition 2.4, run on the infimum over rank-one Rademacher martingales
    intro hmart
    have hle : ∀ A, ∃ v ∈ tkMartVals f A, v ≤ f A := fun A =>
      ⟨f A, ⟨0, fun k => k.elim0, ⟨fun k => k.elim0, fun k => k.elim0⟩, by
        rw [tk_avg_zero _ (fun k => k.elim0), tk_radMart_zero]⟩, le_rfl⟩
    rcases tk_midpoint_principle hf (tkMartVals f) hle
        (fun B C hBC v hv w hw => ⟨_, tk_martVals_mid hBC hv hw, le_rfl⟩) with
      hbot | ⟨G, hGI, hGR, hGf, hglb⟩
    · exact absurd ⟨f 0, fun x ⟨N, A, hA, hx⟩ => hx ▸ hmart N A hA⟩ (hbot 0)
    · exact ⟨G, hGI, hGR, hGf, le_antisymm (hGf 0)
        ((hglb 0).2 fun x ⟨N, A, hA, hx⟩ => hx ▸ hmart N A hA)⟩

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
