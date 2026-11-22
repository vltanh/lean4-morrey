module

public import Morrey.Cassese.Defs
public import Morrey.Common.External.Burkholder.Inequality
public import Morrey.Common.External.Dragicevic.LowerBound
public import Morrey.Common.External.HNVW.Transference

/-!
# Cassese, arXiv:2608.03488v3: the cited results that are proved

The paper's Theorem 2.3 is Burkholder's pair of inequalities for Hilbert-space-valued
martingales, which the paper cites. This file states them in the paper's terms, as the
propositions `BurkholderInequality` and `BurkholderSquareFunction`, and proves them:

* Theorem 2.3 (`cs-thm2.3`), inequality (1): `burkholderInequality_holds : BurkholderInequality`,
  from `External.Burkholder.inequality` (Burkholder 1984; Osękowski 2012, Theorem 3.5);
* Theorem 2.3 (`cs-thm2.3`), inequality (2): `burkholderSquareFunction_holds :
  BurkholderSquareFunction`, from `External.Burkholder.squareFunction` (Osękowski 2012,
  Theorem 8.6).

Each follows from the result of `External/Burkholder` by unfolding `pStar p = max p (p / (p − 1))`.

The library's proofs use them through these two theorems. Earlier they were hypotheses of the
statements that use them; they left the shared block of `Morrey/Cassese/Defs.lean`, which the
Challenge copies, when no statement took them any more.

The three results of Section 7 on the Beurling–Ahlfors transform, still hypotheses of the
statements that use them, are derived here from `External/HNVW` and `External/Dragicevic`, whose
proofs are those of the package `HarmonicAnalysis`:

* `hnvwTransference_holds : HNVWTransference` (proof of Proposition 7.2, citing HNVW I,
  Corollary 5.7.6), from `External.HNVW.transference_beurlingPow`;
* `dragicevicLowerBound_holds : DragicevicLowerBound` (proof of Theorem 7.1, citing Dragičević
  2011, Theorem 1.1), from `External.Dragicevic.theorem1_1_two_pStar` and
  `κ₂ (p*) = (p* − 1)(2p* − 1) / (p* + 1) > p* − 1` for `p ≠ 2`;
* `dragicevicL4Bound_holds : DragicevicL4Bound` (proof of Corollary 7.2), from
  `External.Dragicevic.theorem1_1_two` at `p = 4`, `κ₂ (4) = 21/5`.

The shared definitions `beurlingPowNorm`, `torusBeurlingPowNorm` and `pStar` of
`Morrey/Cassese/Defs.lean` are the package's, definitionally
(`beurlingPowNorm_eq_harmonicAnalysis`, `torusBeurlingPowNorm_eq_harmonicAnalysis`,
`pStar_eq_harmonicAnalysis`).
-/

@[expose] public section

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
separable Hilbert space, started at `0`. Proved here, from External/Burkholder
(`External.Burkholder.inequality`, by Burkholder's method as in Osękowski 2012, Theorem 3.5). -/
theorem burkholderInequality_holds : BurkholderInequality := by
  intro Ω mΩ μ _ ℱ H _ _ _ _ X Y p hp hX hY hX0 hY0 hsub n
  exact External.Burkholder.inequality hp hX hY hX0 hY0 hsub n

/-- **Theorem 2.3 (2)** (`cs-thm2.3`, `eq:sq`): Burkholder's square function inequality
`(p* − 1)⁻¹ ‖𝒮_n X‖_{L^p} ≤ ‖X_n‖_{L^p} ≤ (p* − 1) ‖𝒮_n X‖_{L^p}` for martingales with values in a
separable Hilbert space, started at `0`. Proved here, from External/Burkholder
(`External.Burkholder.squareFunction`, from Burkholder's inequality applied to `X` and the
`ℓ²`-valued martingale `Σ_k dX_k e_k`, each differentially subordinate to the other). -/
theorem burkholderSquareFunction_holds : BurkholderSquareFunction := by
  intro Ω mΩ μ _ ℱ H _ _ _ _ X p hp hX hX0 n
  exact External.Burkholder.squareFunction hp hX hX0 n

/-! ### Section 7: the Beurling–Ahlfors transform -/

/-- Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
operator*, Arch. Math. 96 (2011), Theorem 1.1, as used in the proof of Corollary 7.2:
`‖𝓑²‖_{L⁴ (ℝ²) → L⁴ (ℝ²)} ≥ 21 / 5`, Dragičević's constant `κ₂ (4) = (3/4 · 7/4) / (1/4 · 5/4)`.
A hypothesis of `corollary7_2`. It is stated with the shared definitions of
`Morrey/Cassese/Defs.lean`, like `DragicevicLowerBound`, but is not used by the Challenge, so it
stands here rather than in the shared block. `dragicevicL4Bound_holds` derives it from
`External.Dragicevic.theorem1_1_two`. -/
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
`External.HNVW.transference_beurlingPow`, de Leeuw's argument. -/
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

end Cassese
