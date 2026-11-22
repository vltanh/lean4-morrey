module

public import Morrey.Cassese.Toolkit
public import Morrey.Common.External.Osekowski.Inequality
public import Morrey.Common.External.Dragicevic.LowerBound
public import Morrey.Common.External.HNVW.Transference
public import Morrey.Common.External.HNVW.Extrapolation
public import Morrey.Common.External.HNVW.DyadicUMD
public import Morrey.Common.External.HNVW.ZigZag
public import Morrey.Common.External.HNVW.KahaneKhintchine
public import Morrey.Common.External.CoxVeraar.Decoupling
public import Morrey.Common.External.Pisier.LpUMD
public import Morrey.Common.External.Yaroslavtsev.ComplexUMD
public import Morrey.Common.External.Randrianantoanina.SchattenUMD
public import Morrey.Common.External.PisierXu.Khintchine

/-!
# Cassese, arXiv:2608.03488v3: the cited results, stated in the paper's terms and proved

The results of other works that the paper's proofs cite, stated as propositions named after their
sources, in the paper's terms, and proved from `Morrey/Common/External`, where each is stated in
its source's terms and proved from the packages `BanachProbability` (Sections 2, 4, 6) and
`HarmonicAnalysis` (Section 7). No statement of the library or of the Challenge takes them as
hypotheses: the proofs use them through the theorems `…_holds` below.

Section 2 (Theorem 2.3, Propositions 2.7, 2.8):

* Theorem 2.3 (`cs-thm2.3`), inequality (1): `burkholderInequality_holds : BurkholderInequality`,
  from `External.Osekowski.inequality` (Osękowski 2012, Theorem 3.5);
* Theorem 2.3 (`cs-thm2.3`), inequality (2): `burkholderSquareFunction_holds :
  BurkholderSquareFunction`, from `External.Osekowski.squareFunction` (Osękowski 2012,
  Theorem 8.6). Each follows from the result of `External/Osekowski` by unfolding
  `pStar p = max p (p / (p − 1))`.
* Proposition 2.7 (`prop:umd`): (1) `hnvwExtrapolation_holds : HNVWExtrapolation` (HNVW I,
  Theorem 4.2.7); (2) `randrianantoaninaSchattenUMD_holds : RandrianantoaninaSchattenUMD`
  (Randrianantoanina 2002, Corollary 4.5); (3) `pisierLpUMD_holds : PisierLpUMD` (Pisier 2016,
  Corollary 5.22); (4) `hnvwDyadicUMD_holds : HNVWDyadicUMD` (HNVW I, Theorem 4.2.5); (5)
  `yaroslavtsevComplexUMD_holds : YaroslavtsevComplexUMD` (Yaroslavtsev 2018, Lemma 3.2); (6)
  `hnvwZigZag_holds : HNVWZigZag` (HNVW I, Theorem 4.5.6; Yaroslavtsev 2018, Proposition 3.7).
* Proposition 2.8 (`cs-prop2.8`): `coxVeraarDecoupling_holds : CoxVeraarDecoupling` (Cox–Veraar
  2007; HNVW I, Proposition 4.2.3).

Section 6 (Propositions 6.3, 6.4, and the bound on the constants of 6.4 that Remark 6.3 and
Proposition 6.5 at `q = ∞` use; the paper's Proposition 6.4 leaves it out, and the theorem that it
cites states it, inventory E27):

* `pisierXuKhintchine_holds : PisierXuKhintchine` (Pisier–Xu 2003, Theorem 6.1);
* `kahaneKhintchine_holds : KahaneKhintchine` (HNVW II, Theorem 6.2.4);
* `kahaneKhintchineHypercontractive_holds : KahaneKhintchineHypercontractive` (HNVW II,
  Theorem 6.2.4).

Section 7 (the Beurling–Ahlfors transform): `hnvwTransference_holds : HNVWTransference` (HNVW I,
Corollary 5.7.6), `dragicevicLowerBound_holds : DragicevicLowerBound` and
`dragicevicL4Bound_holds : DragicevicL4Bound` (Dragičević 2011, Theorem 1.1).

Since no statement takes them as hypotheses, they are defined here, outside the shared block of
`Morrey/Cassese/Defs.lean` that the Challenge copies.

Bridges to the packages. The definitions of `Morrey/Cassese/Defs.lean` and `Toolkit.lean` that
the propositions use are the package `BanachProbability`'s, definitionally (`pStar`, `coin`,
`avg`, `IsPredictable`, `lpNormWith`, `mart`, `umdConst`, `complexUMDConst`, `dyadicUMDConst`,
`schattenNorm`, `IsZigZagConcave`, `IsComplexZigZagConcave`; `…_eq_banachProbability`), and
`beurlingPowNorm`, `torusBeurlingPowNorm`, `pStar` are the package `HarmonicAnalysis`'s. The UMD
constant `umdConstWith E nrm p` of `E` renormed by `nrm` is the package's `umdConst` of any
Banach space `F` with a continuous linear equivalence `e : E ≃L[ℝ] F` such that `‖e x‖ = nrm x`
(`umdConstWith_eq_umdConst`): martingales map to martingales under `e` and `e.symm`. Two such
`F`: the type synonym `Renormed E nrm`, `E` with the norm `nrm` (`umdConstWith_eq_renormed`), for
the general statements; and `BanachProbability.SchattenSpace q (Fin d) (Fin d)` for
`S_q^{d×d}` (`umdConstWith_schatten_eq`).
-/

@[expose] public section

open scoped Matrix ENNReal

namespace Cassese

/-- **Theorem 2.3** (`cs-thm2.3`), inequality (1), citing Osękowski, *Sharp martingale and
semimartingale inequalities* (2012), Theorem 3.5 (Burkholder): if `X`, `Y` are martingales with
values in a separable Hilbert space, started at `0`, with `‖dX_n‖ ≤ ‖dY_n‖` almost surely for
`n > 0`, then `‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}` for `p ∈ (1, ∞)`. -/
def BurkholderInequality : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (ℱ : MeasureTheory.Filtration ℕ mΩ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (X Y : ℕ → Ω → H) (p : ℝ), 1 < p →
    MeasureTheory.Martingale X ℱ μ → MeasureTheory.Martingale Y ℱ μ → (∀ ω, X 0 ω = 0) →
    (∀ ω, Y 0 ω = 0) → (∀ n, ∀ᵐ ω ∂μ, ‖X (n + 1) ω - X n ω‖ ≤ ‖Y (n + 1) ω - Y n ω‖) →
    ∀ n, MeasureTheory.eLpNorm (X n) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (pStar p - 1) * MeasureTheory.eLpNorm (Y n) (ENNReal.ofReal p) μ

/-- **Theorem 2.3** (`cs-thm2.3`), inequality (2), citing Osękowski (2012), Theorem 8.6
(Burkholder's square function inequality): for a martingale `X` with values in a separable Hilbert
space, started at `0`, `p ∈ (1, ∞)` and `𝒮_n X = (Σ_{k ≤ n} ‖dX_k‖²)^{1/2}`,
`(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}`. -/
def BurkholderSquareFunction : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (ℱ : MeasureTheory.Filtration ℕ mΩ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (X : ℕ → Ω → H) (p : ℝ), 1 < p →
    MeasureTheory.Martingale X ℱ μ → (∀ ω, X 0 ω = 0) →
    ∀ n, MeasureTheory.eLpNorm
          (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (pStar p - 1) * MeasureTheory.eLpNorm (X n) (ENNReal.ofReal p) μ ∧
      MeasureTheory.eLpNorm (X n) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (pStar p - 1) * MeasureTheory.eLpNorm
          (fun ω => √(∑ k ∈ Finset.range n, ‖X (k + 1) ω - X k ω‖ ^ 2)) (ENNReal.ofReal p) μ

/-- **Theorem 2.3 (1)** (`cs-thm2.3`, `eq:burk`): Burkholder's inequality
`‖X_n‖_{L^p} ≤ (p* − 1) ‖Y_n‖_{L^p}` for differentially subordinate martingales with values in a
separable Hilbert space, started at `0`. Proved here, from External/Osekowski
(`External.Osekowski.inequality`, by the integration method of Osękowski 2012, proof of
Theorem 3.5). -/
theorem burkholderInequality_holds : BurkholderInequality := by
  intro Ω mΩ μ _ ℱ H _ _ _ _ X Y p hp hX hY hX0 hY0 hsub n
  exact External.Osekowski.inequality hp hX hY hX0 hY0 hsub n

/-- **Theorem 2.3 (2)** (`cs-thm2.3`, `eq:sq`): Burkholder's square function inequality
`(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}` for martingales with values in a
separable Hilbert space, started at `0`. Proved here, from External/Osekowski
(`External.Osekowski.squareFunction`, from Burkholder's inequality applied to `X` and the
`ℓ²`-valued martingale `Σ_k dX_k e_k`, each differentially subordinate to the other). -/
theorem burkholderSquareFunction_holds : BurkholderSquareFunction := by
  intro Ω mΩ μ _ ℱ H _ _ _ _ X p hp hX hX0 n
  exact External.Osekowski.squareFunction hp hX hX0 n

/-! ### Section 7: the Beurling–Ahlfors transform -/

/-- Transference for the powers of the Beurling–Ahlfors transform, citing HNVW I,
Corollary 5.7.6 ("the standard transference identity for homogeneous multipliers", proof of
Proposition 7.2), in the direction used: `‖𝓑^k‖_{L^p (ℝ²)} ≤ ‖𝓑^k‖_{L^p_0 (𝕋²)}` for `k ≥ 1`,
`p ∈ (1, ∞)`. Proved by `hnvwTransference_holds`. -/
def HNVWTransference : Prop :=
  ∀ (k : ℕ) (p : ℝ), 1 ≤ k → 1 < p → beurlingPowNorm k p ≤ torusBeurlingPowNorm k p

/-- Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
operator*, Arch. Math. 96 (2011), Theorem 1.1, as used in the proof of Theorem 7.1:
`‖𝓑²‖_{L^p (ℝ²) → L^p (ℝ²)} > p* − 1` for `p ∈ (1, ∞)`, `p ≠ 2`. Proved by
`dragicevicLowerBound_holds`. -/
def DragicevicLowerBound : Prop :=
  ∀ p : ℝ, 1 < p → p ≠ 2 → ENNReal.ofReal (pStar p - 1) < beurlingPowNorm 2 p

/-- Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
operator*, Arch. Math. 96 (2011), Theorem 1.1, as used in the proof of Corollary 7.2:
`‖𝓑²‖_{L⁴ (ℝ²) → L⁴ (ℝ²)} ≥ 21 / 5`, Dragičević's constant `κ₂ (4) = (3/4 · 7/4) / (1/4 · 5/4)`.
Proved by `dragicevicL4Bound_holds`, from `External.Dragicevic.theorem1_1_two`. -/
def DragicevicL4Bound : Prop :=
  ENNReal.ofReal (21 / 5) ≤ beurlingPowNorm 2 4

/-- `‖𝓑^k‖_{L^p (ℝ²)}` of `Morrey/Cassese/Defs.lean` is the package's. -/
theorem beurlingPowNorm_eq_harmonicAnalysis (k : ℕ) (p : ℝ) :
    beurlingPowNorm k p = HarmonicAnalysis.beurlingPowNorm k p :=
  rfl

/-- `‖𝓑^k‖_{L^p_0 (𝕋²)}` of `Morrey/Cassese/Defs.lean` is the package's. -/
theorem torusBeurlingPowNorm_eq_harmonicAnalysis (k : ℕ) (p : ℝ) :
    torusBeurlingPowNorm k p = HarmonicAnalysis.torusBeurlingPowNorm k p :=
  rfl

/-- `p* = max (p, p / (p − 1))` of `Morrey/Cassese/Defs.lean` is the package's. -/
theorem pStar_eq_harmonicAnalysis (p : ℝ) : pStar p = HarmonicAnalysis.pStar p :=
  rfl

/-- Transference (proof of Proposition 7.2, citing HNVW I, Corollary 5.7.6):
`‖𝓑^k‖_{L^p (ℝ²)} ≤ ‖𝓑^k‖_{L^p_0 (𝕋²)}` for `k ≥ 1`, `p ∈ (1, ∞)`. From
`External.HNVW.transference_beurlingPow`, HNVW's argument. -/
theorem hnvwTransference_holds : HNVWTransference := by
  intro k p _ hp
  rw [beurlingPowNorm_eq_harmonicAnalysis, torusBeurlingPowNorm_eq_harmonicAnalysis]
  exact External.HNVW.transference_beurlingPow k hp

/-- Dragičević's lower bound (proof of Theorem 7.1, citing Dragičević 2011, Theorem 1.1):
`‖𝓑²‖_{L^p (ℝ²)} > p* − 1` for `p ∈ (1, ∞)`, `p ≠ 2`. From
`External.Dragicevic.theorem1_1_two_pStar`, `‖𝓑²‖_p ≥ κ₂ (p*)`, and `κ₂ (p*) > p* − 1`. -/
theorem dragicevicLowerBound_holds : DragicevicLowerBound := by
  intro p hp hp2
  rw [beurlingPowNorm_eq_harmonicAnalysis, pStar_eq_harmonicAnalysis]
  have h := HarmonicAnalysis.pStar_sub_one_lt_beurlingKappa_two hp hp2
  refine lt_of_lt_of_le ?_ (External.Dragicevic.theorem1_1_two_pStar hp)
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [HarmonicAnalysis.two_lt_pStar hp hp2])).mpr h

/-- Dragičević's bound at `p = 4` (proof of Corollary 7.2): `‖𝓑²‖_{L⁴ (ℝ²)} ≥ κ₂ (4) = 21 / 5`.
From `External.Dragicevic.theorem1_1_two`. -/
theorem dragicevicL4Bound_holds : DragicevicL4Bound := by
  unfold DragicevicL4Bound
  rw [beurlingPowNorm_eq_harmonicAnalysis, ← HarmonicAnalysis.beurlingKappa_two_four]
  exact External.Dragicevic.theorem1_1_two (by norm_num)

/-! ### Bridges to the package `BanachProbability` -/

section Bridges

open MeasureTheory BanachProbability.SignCube

/-- `p* = max (p, p / (p − 1))` of `Morrey/Cassese/Defs.lean` is the package
`BanachProbability`'s. -/
theorem pStar_eq_banachProbability (p : ℝ) : pStar p = BanachProbability.pStar p :=
  rfl

/-- The signs of `Morrey/Cassese/Defs.lean` are the package's. -/
theorem coin_eq_banachProbability (b : Bool) : coin b = BanachProbability.SignCube.coin b :=
  rfl

/-- The cube average of `Morrey/Cassese/Defs.lean` is the package's. -/
theorem avg_eq_banachProbability {N : ℕ} (g : (Fin N → Bool) → ℝ) :
    avg g = BanachProbability.SignCube.avg g :=
  rfl

/-- Predictability on the cube, as in the package. -/
theorem isPredictable_iff_banachProbability {N : ℕ} {E : Type*}
    (ξ : Fin N → (Fin N → Bool) → E) :
    IsPredictable ξ ↔ BanachProbability.SignCube.IsPredictable ξ :=
  Iff.rfl

/-- The `L^p` norms on the cube of `Morrey/Cassese/Defs.lean` are the package's. -/
theorem lpNormWith_eq_banachProbability {N : ℕ} {E : Type*} (nrm : E → ℝ) (p : ℝ)
    (X : (Fin N → Bool) → E) : lpNormWith nrm p X = BanachProbability.SignCube.lpNorm nrm p X :=
  rfl

/-- The Paley–Walsh martingales of `Morrey/Cassese/Defs.lean` are the package's. -/
theorem mart_eq_banachProbability {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin N → (Fin N → Bool) → E) (n : ℕ) : mart ξ n = paleyWalsh ξ n :=
  rfl

/-- `UMD_p (X)` of `Morrey/Cassese/Defs.lean` is the package's. -/
theorem umdConst_eq_banachProbability (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (p : ℝ) : umdConst X p = BanachProbability.umdConst X p :=
  rfl

/-- `UMD_{ℂ,p} (X)` of `Morrey/Cassese/Defs.lean` is the package's. -/
theorem complexUMDConst_eq_banachProbability (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] (p : ℝ) : complexUMDConst X p = BanachProbability.complexUMDConst X p :=
  rfl

/-- The dyadic `UMD_p` constant of `Morrey/Cassese/Toolkit.lean` is the package's. -/
theorem dyadicUMDConst_eq_banachProbability (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : ℝ) : dyadicUMDConst X p = BanachProbability.dyadicUMDConst X p :=
  rfl

/-- The Schatten norms of `Morrey/Cassese/Defs.lean` are the package's. -/
theorem schattenNorm_eq_banachProbability {d m : ℕ} (q : ℝ≥0∞) (A : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm q A = BanachProbability.schattenNorm q A :=
  rfl

/-- Zig-zag concavity, as in the package. -/
theorem isZigZagConcave_iff_banachProbability {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (p β : ℝ) (U : X → X → ℝ) :
    IsZigZagConcave p β U ↔ BanachProbability.IsZigZagConcave p β U :=
  Iff.rfl

/-- Complex zig-zag concavity, as in the package. -/
theorem isComplexZigZagConcave_iff_banachProbability {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] (p β : ℝ) (U : X → X → ℝ) :
    IsComplexZigZagConcave p β U ↔ BanachProbability.IsComplexZigZagConcave p β U :=
  Iff.rfl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A `UMD_p` constant of `E` renormed by `nrm` is one of `F`, and conversely, for a continuous
linear equivalence `e : E ≃L[ℝ] F` with `‖e x‖ = nrm x`: martingales and their transforms map to
each other under `e` and `e.symm`. -/
theorem isUMDBoundWith_iff_isUMDBound (e : E ≃L[ℝ] F) {nrm : E → ℝ} (he : ∀ x, ‖e x‖ = nrm x)
    (p : ℝ) (β : ℝ≥0∞) : IsUMDBoundWith E nrm p β ↔ BanachProbability.IsUMDBound F p β := by
  constructor
  · intro h Ω mΩ μ hμ ℱ Y σ hY hY0 hσ hσm n
    have hY' : Martingale (fun m ω => e.symm (Y m ω)) ℱ μ :=
      BanachProbability.martingale_map_continuousLinearMap hY (e.symm : F →L[ℝ] E)
    have h1 := h Ω mΩ μ ℱ (fun m ω => e.symm (Y m ω)) σ hY' (by simp [hY0]) hσ hσm n
    have h2 : (fun ω => nrm (e.symm (Y n ω))) = fun ω => ‖Y n ω‖ := by
      funext ω; rw [← he]; simp
    have h3 : (fun ω => nrm (∑ k ∈ Finset.range n,
        σ (k + 1) ω • (e.symm (Y (k + 1) ω) - e.symm (Y k ω)))) =
        fun ω => ‖∑ k ∈ Finset.range n, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)‖ := by
      funext ω; rw [← he]; simp [map_sum, map_smul, map_sub]
    simp only [h2, h3] at h1
    exact h1
  · intro h Ω mΩ μ hμ ℱ Y σ hY hY0 hσ hσm n
    have hY' : Martingale (fun m ω => e (Y m ω)) ℱ μ :=
      BanachProbability.martingale_map_continuousLinearMap hY (e : E →L[ℝ] F)
    have h1 := h Ω mΩ μ ℱ (fun m ω => e (Y m ω)) σ hY' (by simp [hY0]) hσ hσm n
    have h2 : (fun ω => ‖e (Y n ω)‖) = fun ω => nrm (Y n ω) := by
      funext ω; rw [he]
    have h3 : (fun ω => ‖∑ k ∈ Finset.range n, σ (k + 1) ω • (e (Y (k + 1) ω) - e (Y k ω))‖) =
        fun ω => nrm (∑ k ∈ Finset.range n, σ (k + 1) ω • (Y (k + 1) ω - Y k ω)) := by
      funext ω; rw [← he]; simp [map_sum, map_smul, map_sub]
    simp only [h2, h3] at h1
    exact h1

/-- `umdConstWith E nrm p = umdConst F p` for a continuous linear equivalence `e : E ≃L[ℝ] F`
with `‖e x‖ = nrm x`. -/
theorem umdConstWith_eq_umdConst (e : E ≃L[ℝ] F) {nrm : E → ℝ} (he : ∀ x, ‖e x‖ = nrm x)
    (p : ℝ) : umdConstWith E nrm p = BanachProbability.umdConst F p := by
  unfold umdConstWith BanachProbability.umdConst
  congr 1
  ext β
  exact isUMDBoundWith_iff_isUMDBound e he p β

end Bridges

/-- The hypotheses on `nrm` in the propositions on UMD spaces: a norm equivalent to the norm of
`E` (the triangle inequality, absolute homogeneity, and `a ‖x‖ ≤ nrm x ≤ b ‖x‖`). -/
structure IsEquivNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (nrm : E → ℝ) :
    Prop where
  add_le : ∀ x y, nrm (x + y) ≤ nrm x + nrm y
  smul : ∀ (c : ℝ) x, nrm (c • x) = |c| * nrm x
  equiv : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x, a * ‖x‖ ≤ nrm x ∧ nrm x ≤ b * ‖x‖

/-- `E` with the norm `nrm` (a type synonym; a normed space when `nrm` is an equivalent norm). -/
def Renormed (E : Type*) (_nrm : E → ℝ) : Type _ := E

namespace Renormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {nrm : E → ℝ}

instance : AddCommGroup (Renormed E nrm) := inferInstanceAs (AddCommGroup E)

instance : Module ℝ (Renormed E nrm) := inferInstanceAs (Module ℝ E)

instance : Norm (Renormed E nrm) := ⟨fun x => nrm x⟩

theorem nrm_zero (h : IsEquivNorm nrm) : nrm (0 : E) = 0 := by
  have := h.smul 0 0
  rwa [zero_smul, abs_zero, zero_mul] at this

theorem nrm_neg (h : IsEquivNorm nrm) (x : E) : nrm (-x) = nrm x := by
  have := h.smul (-1) x
  rwa [neg_one_smul, abs_neg, abs_one, one_mul] at this

theorem nrm_nonneg (h : IsEquivNorm nrm) (x : E) : 0 ≤ nrm x := by
  have := h.add_le x (-x)
  rw [add_neg_cancel, nrm_zero h, nrm_neg h] at this
  linarith

theorem nrm_eq_zero (h : IsEquivNorm nrm) (x : E) : nrm x = 0 ↔ x = 0 := by
  obtain ⟨a, b, ha, hb, hab⟩ := h.equiv
  constructor
  · intro hx
    have h1 := (hab x).1
    rw [hx] at h1
    have : ‖x‖ = 0 := le_antisymm (by nlinarith [norm_nonneg x]) (norm_nonneg _)
    exact norm_eq_zero.1 this
  · rintro rfl
    exact nrm_zero h

/-- The normed-space structure of `Renormed E nrm`. -/
theorem core (h : IsEquivNorm nrm) : NormedSpace.Core ℝ (Renormed E nrm) where
  norm_nonneg x := nrm_nonneg h x
  norm_smul c x := (h.smul c x).trans (by rw [Real.norm_eq_abs]; rfl)
  norm_triangle x y := h.add_le x y
  norm_eq_zero_iff x := nrm_eq_zero h x

noncomputable instance [hn : Fact (IsEquivNorm nrm)] : NormedAddCommGroup (Renormed E nrm) :=
  NormedAddCommGroup.ofCore (core hn.out)

noncomputable instance [hn : Fact (IsEquivNorm nrm)] : NormedSpace ℝ (Renormed E nrm) :=
  NormedSpace.ofCore (core hn.out)

theorem norm_def [Fact (IsEquivNorm nrm)] (x : Renormed E nrm) : ‖x‖ = nrm x :=
  rfl

/-- The identity `E → Renormed E nrm`, as a linear equivalence. -/
def linEquiv : E ≃ₗ[ℝ] Renormed E nrm :=
  LinearEquiv.refl ℝ E

/-- The identity `E → Renormed E nrm`, as a continuous linear equivalence. -/
noncomputable def equiv [hn : Fact (IsEquivNorm nrm)] : E ≃L[ℝ] Renormed E nrm :=
  linEquiv.toContinuousLinearEquivOfBounds
    (Classical.choose (Classical.choose_spec hn.out.equiv))
    (Classical.choose hn.out.equiv)⁻¹
    (fun x => (Classical.choose_spec (Classical.choose_spec hn.out.equiv)).2.2 x |>.2)
    (fun x => by
      have ha := (Classical.choose_spec (Classical.choose_spec hn.out.equiv)).1
      have h1 := ((Classical.choose_spec (Classical.choose_spec hn.out.equiv)).2.2 x).1
      exact (le_inv_mul_iff₀ ha).2 h1)

theorem norm_equiv [Fact (IsEquivNorm nrm)] (x : E) : ‖(equiv x : Renormed E nrm)‖ = nrm x :=
  rfl

instance [CompleteSpace E] [Fact (IsEquivNorm nrm)] : CompleteSpace (Renormed E nrm) :=
  (UniformEquiv.completeSpace_iff
    ⟨(equiv : E ≃L[ℝ] Renormed E nrm).toLinearEquiv.toEquiv,
      (equiv : E ≃L[ℝ] Renormed E nrm).toContinuousLinearMap.uniformContinuous,
      (equiv : E ≃L[ℝ] Renormed E nrm).symm.toContinuousLinearMap.uniformContinuous⟩).1
    inferInstance

end Renormed

/-- `umdConstWith E nrm p = umdConst (Renormed E nrm) p`. -/
theorem umdConstWith_eq_renormed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {nrm : E → ℝ} [Fact (IsEquivNorm nrm)] (p : ℝ) :
    umdConstWith E nrm p = BanachProbability.umdConst (Renormed E nrm) p :=
  umdConstWith_eq_umdConst Renormed.equiv Renormed.norm_equiv p

/-- `UMD_p (S_q^{d×d}) = UMD_p (BanachProbability.SchattenSpace q (Fin d) (Fin d))`: the
Schatten norm of `Morrey/Cassese/Defs.lean` on `Fin d → Fin d → ℝ` is the package's norm. -/
theorem umdConstWith_schatten_eq {q : ℝ≥0∞} [Fact (1 ≤ q)] (d : ℕ) (p : ℝ) :
    umdConstWith (Fin d → Fin d → ℝ) (fun X => schattenNorm q (Matrix.of X)) p =
      BanachProbability.umdConst (BanachProbability.SchattenSpace q (Fin d) (Fin d)) p := by
  let e : (Fin d → Fin d → ℝ) ≃L[ℝ] BanachProbability.SchattenSpace q (Fin d) (Fin d) :=
    ((Matrix.ofLinearEquiv ℝ).trans
      BanachProbability.SchattenSpace.ofMatrix).toContinuousLinearEquiv
  exact umdConstWith_eq_umdConst e (nrm := fun X => schattenNorm q (Matrix.of X)) (fun X => rfl) p

/-- A seminorm given by the two axioms of the propositions on Rademacher sums, as a `Seminorm`. -/
def seminormOf {E : Type*} [AddCommGroup E] [Module ℝ E] (nrm : E → ℝ)
    (h1 : ∀ x y, nrm (x + y) ≤ nrm x + nrm y) (h2 : ∀ (c : ℝ) x, nrm (c • x) = |c| * nrm x) :
    Seminorm ℝ E :=
  Seminorm.of nrm h1 (fun c x => by rw [h2, Real.norm_eq_abs])

/-! ### Section 2: Proposition 2.7 (UMD spaces) and Proposition 2.8 (decoupling) -/

/-- **Proposition 2.7 (1)** (`prop:umd`), citing Hytönen–van Neerven–Veraar–Weis, *Analysis in
Banach spaces I* (2016), Theorem 4.2.7: a Banach space that is `UMD_{p₀}` for some
`p₀ ∈ (1, ∞)` is `UMD_p` for every `p ∈ (1, ∞)`; and
`UMD₂ (X) / 200 ≤ UMD_p (X) ≤ 100 p* UMD₂ (X)` for every `p ∈ (1, ∞)`. The Banach spaces are
the complete normed spaces `E` renormed by an equivalent norm `nrm` (every Banach space is one,
with `nrm = ‖·‖`). Proved by `hnvwExtrapolation_holds`, from `External.HNVW.theorem4_2_7`. -/
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
`q ∈ (1, ∞)` and every `d`. (`S_q^{d×d}` is `Fin d → Fin d → ℝ` renormed by `‖·‖_{S_q}`.) Proved by
`randrianantoaninaSchattenUMD_holds`, from `External.Randrianantoanina.remark4_6`. -/
def RandrianantoaninaSchattenUMD : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ), 1 < q → ∀ d : ℕ,
    umdConstWith (Fin d → Fin d → ℝ) (fun X => schattenNorm (ENNReal.ofReal q) (Matrix.of X)) 2 ≤
      ENNReal.ofReal (C * (pStar q - 1))

/-- **Proposition 2.7 (3)** (`prop:umd`), citing Pisier, *Martingales in Banach spaces* (2016),
Corollary 5.22: for every measure space and `p ∈ (1, ∞)`, the complex `L^p` is a UMD space,
`UMD_p (L^p (μ)) < ∞`. Proved by `pisierLpUMD_holds`, from `External.Pisier.corollary5_22`. -/
def PisierLpUMD : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ⊤ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω),
      umdConst (MeasureTheory.Lp ℂ p μ) p.toReal < ⊤

/-- **Proposition 2.7 (4)** (`prop:umd`), citing HNVW I, Theorem 4.2.5: restricting (4) to dyadic
martingales gives the same optimal constant, `UMD_p^{dyad} (X) = UMD_p (X)`. Used only in
Remark 4.1 (no proof uses it). Proved by `hnvwDyadicUMD_holds`, from
`External.HNVW.theorem4_2_5`. -/
def HNVWDyadicUMD : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (p : ℝ), 1 < p →
    dyadicUMDConst X p = umdConst X p

/-- **Proposition 2.7 (5)** (`prop:umd`), citing Yaroslavtsev, *Even Fourier multipliers and
martingale transforms in infinite dimensions*, Indag. Math. 29 (2018), Lemma 3.2: for a complex
Banach space `X` and `p ∈ (1, ∞)`, `UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`. Proved by
`yaroslavtsevComplexUMD_holds`, from `External.Yaroslavtsev.lemma3_2`. -/
def YaroslavtsevComplexUMD : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p →
    umdConst X p ≤ complexUMDConst X p ∧
      complexUMDConst X p ≤ ENNReal.ofReal (Real.pi / 2) * umdConst X p

/-- **Proposition 2.7 (6)** (`prop:umd`), citing HNVW I, Theorem 4.5.6, and Yaroslavtsev,
Proposition 3.7: a Banach space `X` is `UMD_p` if and only if there is a zig-zag concave `U` for
some `β > 0`; then `β ≥ UMD_p (X)`, and `β ≥ UMD_{ℂ,p} (X)` when `X` is complex and `U` is
zig-zag concave in the complex sense. Not used in any proof. Proved by `hnvwZigZag_holds`,
from `External.HNVW.theorem4_5_6` and `External.Yaroslavtsev.proposition3_7`. -/
def HNVWZigZag : Prop :=
  (∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (p : ℝ), 1 < p →
    (umdConst X p < ⊤ ↔ ∃ β : ℝ, 0 < β ∧ ∃ U : X → X → ℝ, IsZigZagConcave p β U) ∧
    ∀ (β : ℝ) (U : X → X → ℝ), 0 < β → IsZigZagConcave p β U →
      umdConst X p ≤ ENNReal.ofReal β) ∧
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (p : ℝ), 1 < p →
    ∀ (β : ℝ) (U : X → X → ℝ), 0 < β → IsComplexZigZagConcave p β U →
      complexUMDConst X p ≤ ENNReal.ofReal β

/-- **Proposition 2.8** (`cs-prop2.8`), decoupling, citing Cox–Veraar, Electron. Commun. Probab.
12 (2007), and HNVW I, Proposition 4.2.3: for a Banach space `(E, nrm)`, `p ∈ (1, ∞)` and a
Rademacher martingale `dY_n = ε_n ξ_n` with predictable `ξ_n`, and `Ỹ_n = Σ_{k<n} ε̃_k ξ_k` with an
independent copy `ε̃` of the signs,
`UMD_p⁻¹ ‖Ỹ_n‖_{L^p} ≤ ‖Y_n‖_{L^p} ≤ UMD_p ‖Ỹ_n‖_{L^p}`. On the canonical space
`{±1}^N × {±1}^N`. Proved by `coxVeraarDecoupling_holds`, from
`External.CoxVeraar.decoupling`. -/
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

/-- **Proposition 2.7 (1)** (`prop:umd`), HNVW I, Theorem 4.2.7: extrapolation, for every Banach
space `(E, nrm)`. From `External.HNVW.theorem4_2_7` for `Renormed E nrm`
(`umdConstWith_eq_renormed`). -/
theorem hnvwExtrapolation_holds : HNVWExtrapolation := by
  intro E _ _ _ nrm h1 h2 h3
  have : Fact (IsEquivNorm nrm) := ⟨⟨h1, h2, h3⟩⟩
  simp only [umdConstWith_eq_renormed]
  exact External.HNVW.theorem4_2_7

/-- **Proposition 2.7 (2)** (`prop:umd`), Randrianantoanina (2002), Corollary 4.5:
`UMD₂ (S_q^{d×d}) ≤ C (q* − 1)` uniformly in `q ∈ (1, ∞)` and `d`. From
`External.Randrianantoanina.remark4_6` for `BanachProbability.SchattenSpace q (Fin d) (Fin d)`
(`umdConstWith_schatten_eq`). -/
theorem randrianantoaninaSchattenUMD_holds : RandrianantoaninaSchattenUMD := by
  obtain ⟨C, hC, h⟩ := External.Randrianantoanina.remark4_6
  refine ⟨C, hC, fun q hq d => ?_⟩
  have hq1 : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨hq1⟩
  have hq' : 1 < ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hq
  rw [umdConstWith_schatten_eq]
  have := h (ENNReal.ofReal q) hq' ENNReal.ofReal_ne_top (Fin d)
  rwa [ENNReal.toReal_ofReal (by linarith)] at this

/-- **Proposition 2.7 (3)** (`prop:umd`), Pisier (2016), Corollary 5.22: the complex `L^p (μ)` is
`UMD_p`, for every measure space. From `External.Pisier.corollary5_22`. -/
theorem pisierLpUMD_holds : PisierLpUMD := by
  intro p _ hp hpt Ω _ μ
  exact External.Pisier.corollary5_22 μ p hp hpt

/-- **Proposition 2.7 (4)** (`prop:umd`), HNVW I, Theorem 4.2.5: `UMD_p^{dyad} = UMD_p`. From
`External.HNVW.theorem4_2_5`. -/
theorem hnvwDyadicUMD_holds : HNVWDyadicUMD := by
  intro X _ _ _ p hp
  exact External.HNVW.theorem4_2_5 hp

/-- **Proposition 2.7 (5)** (`prop:umd`), Yaroslavtsev (2018), Lemma 3.2:
`UMD_p (X) ≤ UMD_{ℂ,p} (X) ≤ (π / 2) UMD_p (X)`. From `External.Yaroslavtsev.lemma3_2`. -/
theorem yaroslavtsevComplexUMD_holds : YaroslavtsevComplexUMD := by
  intro X _ _ _ p hp
  exact External.Yaroslavtsev.lemma3_2 hp

/-- **Proposition 2.7 (6)** (`prop:umd`), HNVW I, Theorem 4.5.6, and Yaroslavtsev (2018),
Proposition 3.7: the characterisation of `UMD_p` by zig-zag concave functions. From
`External.HNVW.theorem4_5_6` (real) and `External.Yaroslavtsev.proposition3_7` (complex). -/
theorem hnvwZigZag_holds : HNVWZigZag :=
  ⟨fun _X _ _ _ _p hp => External.HNVW.theorem4_5_6 hp,
    fun _X _ _ _ _p hp _β _U hβ hU => External.Yaroslavtsev.proposition3_7 hp hβ hU⟩

/-- **Proposition 2.8** (`cs-prop2.8`), decoupling (Cox–Veraar 2007; HNVW I, Proposition 4.2.3),
for every Banach space `(E, nrm)`. From `External.CoxVeraar.decoupling` for `Renormed E nrm`
(`umdConstWith_eq_renormed`; the Paley–Walsh martingales and their `L^p` norms map through the
identity `E → Renormed E nrm`). -/
theorem coxVeraarDecoupling_holds : CoxVeraarDecoupling := by
  intro E _ _ _ nrm h1 h2 h3 p hp N ξ hξ n
  have : Fact (IsEquivNorm nrm) := ⟨⟨h1, h2, h3⟩⟩
  rw [umdConstWith_eq_renormed]
  let ζ : Fin N → (Fin N → Bool) → Renormed E nrm := fun k ε => Renormed.equiv (ξ k ε)
  have hζ : BanachProbability.SignCube.IsPredictable ζ := fun k ε ε' h => by
    simp only [ζ]; rw [hξ k ε ε' h]
  have hmap : ∀ (η : Fin N → (Fin N → Bool) → E) (ε : Fin N → Bool),
      BanachProbability.SignCube.paleyWalsh
          (fun k ε => (Renormed.equiv (η k ε) : Renormed E nrm)) n ε =
        Renormed.equiv (mart η n ε) := fun η ε =>
    (BanachProbability.SignCube.map_paleyWalsh
      (Renormed.equiv : E ≃L[ℝ] Renormed E nrm).toLinearEquiv.toLinearMap η n ε).symm
  have hdec : BanachProbability.decoupledLpNorm p ζ n =
      avg (fun ε => avg fun ε' => nrm (mart (fun k _ => ξ k ε) n ε') ^ p) ^ (1 / p) := by
    unfold BanachProbability.decoupledLpNorm
    simp only [ζ, hmap (fun k _ => ξ k _), Renormed.norm_equiv]
    rfl
  have hlp : BanachProbability.SignCube.lpNorm (fun x : Renormed E nrm => ‖x‖) p
      (BanachProbability.SignCube.paleyWalsh ζ n) = lpNormWith nrm p (mart ξ n) := by
    unfold BanachProbability.SignCube.lpNorm lpNormWith
    simp only [ζ, hmap ξ, Renormed.norm_equiv]
    rfl
  have := External.CoxVeraar.decoupling hp ζ hζ n
  rw [hdec, hlp] at this
  exact this

/-! ### Section 6: the Khintchine inequalities (Propositions 6.3, 6.4) -/

/-- **Proposition 6.3** (`cs-prop6.3`), non-commutative Khintchine, citing Pisier–Xu,
*Non-commutative `L^p`-spaces* (2003), Theorem 6.1: for `q ∈ [2, ∞)`, normal `d × d` matrices
`x_i` and independent Rademacher `ε_i`,
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q} ≤ (E ‖Σ ε_i x_i‖_{S_q}^q)^{1/q} ≲ √q ‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`,
with an absolute constant. Stated with `√‖Σ x_i x_iᵀ‖_{S_{q/2}}` in place of the paper's
`‖(Σ x_i x_iᵀ)^{1/2}‖_{S_q}`: the two are equal, since `‖B^{1/2}‖_{S_q}² = ‖B‖_{S_{q/2}}` for
`B = Σ x_i x_iᵀ ⪰ 0` and `q ≥ 2` (`schattenNorm_sqrt_sq` in `Morrey/Cassese/Square.lean`: fact (1),
`‖A²‖_{S_{q/2}} = ‖A‖_{S_q}²`, applied to the positive semidefinite square root `A = B^{1/2}`). Proved by `pisierXuKhintchine_holds`, from `External.PisierXu.theorem6_1`. -/
def PisierXuKhintchine : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ), 2 ≤ q → ∀ (d n : ℕ) (x : Fin n → Matrix (Fin d) (Fin d) ℝ),
    (∀ i, x i * (x i)ᵀ = (x i)ᵀ * x i) →
      √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ)) ≤
          lpNormWith (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ∧
        lpNormWith (schattenNorm (ENNReal.ofReal q)) q
            (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
          C * √q * √(schattenNorm (ENNReal.ofReal (q / 2)) (∑ i, x i * (x i)ᵀ))

/-- **Proposition 6.4** (`cs-prop6.4`), Kahane–Khintchine, citing HNVW, *Analysis in Banach spaces
II* (2017), Theorem 6.2.4 (TeX lines 2312–2321): for `p, q ∈ (1, ∞)` there are constants `k_{p,q}`
such that for every Banach space `X`, every `x₁, …, x_n ∈ X` and independent Rademacher `ε_i`,
`k_{q,p}⁻¹ ‖Σ ε_i x_i‖_{L^q} ≤ ‖Σ ε_i x_i‖_{L^p} ≤ k_{p,q} ‖Σ ε_i x_i‖_{L^q}`. The paper's
statement, with no bound on the constants: the bound `k_{q,p} ≤ √((q − 1)/(p − 1))` of the cited
theorem, which the paper leaves out and which Remark 6.3 and the case `q = ∞` of Proposition 6.5
need, is the separate proposition `KahaneKhintchineHypercontractive`, used only by the proofs that
need it.

Generality. It is stated for any seminorm `nrm` on a real vector space `E` (the hypotheses on
`nrm` are the triangle inequality and absolute homogeneity, which give `nrm ≥ 0`), not only for
Banach spaces; the proof (hypercontractivity) needs no completeness. Proved by
`kahaneKhintchine_holds`, from `External.HNVW.theorem6_2_4_seminorm`. -/
def KahaneKhintchine : Prop :=
  ∃ κ : ℝ → ℝ → ℝ, (∀ p q, 0 < κ p q) ∧
    ∀ p q : ℝ, 1 < p → 1 < q →
    ∀ (E : Type) [AddCommGroup E] [Module ℝ E] (nrm : E → ℝ),
      (∀ x y, nrm (x + y) ≤ nrm x + nrm y) → (∀ (c : ℝ) x, nrm (c • x) = |c| * nrm x) →
      ∀ (n : ℕ) (x : Fin n → E),
        (κ q p)⁻¹ * lpNormWith nrm q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
            lpNormWith nrm p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ∧
          lpNormWith nrm p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
            κ p q * lpNormWith nrm q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i)

/-- The Kahane–Khintchine inequality with the constant of the cited theorem, HNVW II, Theorem 6.2.4
(`κ_{q,p} ≤ √((q − 1) / (p − 1))` for real signs): for `1 < p ≤ q < ∞`, every seminorm `nrm` on a
real vector space `E` and `x₁, …, x_n ∈ E`,
`‖Σ ε_i x_i‖_{L^q} ≤ √((q − 1) / (p − 1)) ‖Σ ε_i x_i‖_{L^p}`, that is,
`k_{q,p} ≤ √((q − 1) / (p − 1))` in Proposition 6.4 (`KahaneKhintchine`).

How the paper uses it. The paper's Proposition 6.4 names only constants `k_{p,q}`, but its route
to Remark 6.3 (TeX lines 2425–2437) and to the case `q = ∞` of Proposition 6.5 (TeX lines
2477–2479: "all the implied multiplicative constants in the above inequalities are at most
polynomial in `q`") uses (31) (TeX lines 2322–2328) with constants that grow at most polynomially
in `q`, which needs `k_{q,p}` to (inventory E27). The theorem that Proposition 6.4 cites says so.
Proved by `kahaneKhintchineHypercontractive_holds`, from
`External.HNVW.theorem6_2_4_hypercontractive`; used by the proofs of `remark6_3`,
`proposition6_5_infty` and `proposition6_5` only (through their helpers `square_eq31_two`,
`square_eq31_q`). As `KahaneKhintchine`, it is stated for seminorms. -/
def KahaneKhintchineHypercontractive : Prop :=
  ∀ p q : ℝ, 1 < p → p ≤ q →
    ∀ (E : Type) [AddCommGroup E] [Module ℝ E] (nrm : E → ℝ),
      (∀ x y, nrm (x + y) ≤ nrm x + nrm y) → (∀ (c : ℝ) x, nrm (c • x) = |c| * nrm x) →
      ∀ (n : ℕ) (x : Fin n → E),
        lpNormWith nrm q (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) ≤
          √((q - 1) / (p - 1)) * lpNormWith nrm p (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i)

/-- **Proposition 6.3** (`cs-prop6.3`), Pisier–Xu (2003), Theorem 6.1: the non-commutative
Khintchine inequality for normal `d × d` matrices and `q ∈ [2, ∞)`, lower constant `1`, upper
constant `C √q`. From `External.PisierXu.theorem6_1` (`C = √2`). -/
theorem pisierXuKhintchine_holds : PisierXuKhintchine := by
  obtain ⟨C, hC, h⟩ := External.PisierXu.theorem6_1
  exact ⟨C, hC, fun q hq d n x hx => h q hq (Fin d) n x hx⟩

/-- **Proposition 6.4** (`cs-prop6.4`), HNVW II, Theorem 6.2.4: the Kahane–Khintchine inequality
for every seminorm, with `κ_{p,q} = max (1, √((p − 1) / (q − 1)))`. From
`External.HNVW.theorem6_2_4_seminorm`, applied in both directions. -/
theorem kahaneKhintchine_holds : KahaneKhintchine := by
  refine ⟨BanachProbability.kahaneKhintchineConst, BanachProbability.kahaneKhintchineConst_pos,
    ?_⟩
  intro p q hp hq E _ _ nrm h1 h2 n x
  have hS : ∀ r : ℝ, lpNormWith nrm r (fun ε : Fin n → Bool => ∑ i, coin (ε i) • x i) =
      BanachProbability.SignCube.lpNorm (seminormOf nrm h1 h2) r
        (fun ε : Fin n → Bool => ∑ i, BanachProbability.SignCube.coin (ε i) • x i) :=
    fun r => rfl
  rw [hS, hS]
  refine ⟨?_, External.HNVW.theorem6_2_4_seminorm (seminormOf nrm h1 h2) hp hq x⟩
  rw [inv_mul_le_iff₀ (BanachProbability.kahaneKhintchineConst_pos q p)]
  exact External.HNVW.theorem6_2_4_seminorm (seminormOf nrm h1 h2) hq hp x

/-- The bound `k_{q,p} ≤ √((q − 1) / (p − 1))`, `1 < p ≤ q`, on the constants of Kahane–Khintchine,
for every seminorm (HNVW II, Theorem 6.2.4; inventory E27). From
`External.HNVW.theorem6_2_4_hypercontractive`. -/
theorem kahaneKhintchineHypercontractive_holds : KahaneKhintchineHypercontractive := by
  intro p q hp hpq E _ _ nrm h1 h2 n x
  exact External.HNVW.theorem6_2_4_hypercontractive (seminormOf nrm h1 h2) hp hpq x

end Cassese
