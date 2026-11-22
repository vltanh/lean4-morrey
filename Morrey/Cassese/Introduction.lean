module

public import Morrey.Cassese.Sverak
public import Morrey.Cassese.TwoByM
public import Morrey.Cassese.TwoByThree
public import Morrey.Cassese.Square
public import Morrey.Cassese.FourByTwo
public import Morrey.Common.External.Rindler.Lemmas
public import Morrey.Common.Basic.Analysis.Calculus.BumpFunction.Mollify
public import Morrey.Cassese.Lifting
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Section 1: Morrey's problem, the main theorems and the landscape

The main theorems of the paper, as stated in the introduction (Theorem 1.1 is Kirchheim and
Kristensen's, quoted for context: `External.KirchheimKristensen.Theorem1_1`), and the claims of
the introduction about the landscape of Morrey's problem:

* `MorreyPositive d m`: Morrey's problem has a positive answer in `d × m` (every rank-one convex
  integrand on `ℝ^{d×m}` is quasiconvex); `HomMorreyPositive p d m`: the homogeneous Morrey problem
  (Kirchheim–Kristensen) has a positive answer in `d × m` at the exponent `p` (every `p`-homogeneous
  rank-one convex integrand is quasiconvex at `0`);
* the monotonicity of both problems in the dimensions (lines 105–107 and 209–210), and the
  triviality of the case `min (d, m) ≤ 1` (lines 108–109);
* Theorems 1.2–1.5 and Corollary 1.6; Theorem 1.2 twice: by the paper's proof, conditional on
  Proposition 2.7 (1), (3), (5) (`theorem1_2_umd`), and unconditionally, by the route of
  Remark 4.5 (`theorem1_2`, from `theorem1_2_elementary`);
* the combined statement of lines 251–254: with Šverák's example (`Cassese.sverak_example`),
  Theorem 1.3 leaves `2 × 2` as the only nontrivial dimension in which Morrey's problem may have a
  positive answer (`morrey_landscape`); and, with Corollary 5.3, the same for the homogeneous
  problem at `p = 4` (lines 254–256 and 2137–2142, `homMorrey_landscape`).

Conditional statements. The results of other works that are out of reach of this project are
hypotheses, named after their sources, of every statement whose proof uses them: Theorem 1.4 for
general `p` and the paper's proof of Theorem 1.2 (see each docstring). The others, Theorem 1.5 and
Corollary 1.6 included, are unconditional: the cited results that their proofs use are proved
(`Morrey/Cassese/Hypotheses.lean`, `Morrey/Common/External`).

Tools (helpers, prefixed `intro_`): Jensen's inequality along test maps
(`intro_quasiconvexAt_of_convexOn`); the rank-one convex envelope step
of the main theorems (`intro_envelope`) and the families `C ↦ C^p N₁^p − N₂^p` with their thresholds
(`intro_family`, `intro_rankOneConvexAt_of_rcThreshold_lt`, with
`not_quasiconvexAt_of_lt_qcThreshold` from `Toolkit`, `intro_blockF`, `intro_kornF`); the integrand
`G` of Corollary 1.6 and its three properties (`intro_corG`, `intro_corG_basic`,
`intro_corG_rankOneConvex`, `intro_corG_not_quasiconvexAt`). The lifting of integrands and
witnesses from `ℝ^{d'×m'}` to `ℝ^{d×m}` (`lift_trunc`, `lift_quasiconvexAt_of_comp_trunc`) is in
`Morrey/Cassese/Lifting.lean`.
-/

@[expose] public section

open scoped Matrix

namespace Cassese

/-! ### Tools: Jensen along test maps, homogeneous polynomials

Helpers for the claims of the introduction (prefix `intro_`): test maps have mean-zero gradient
and Jensen's inequality along them (`intro_integral_fderiv_eq_zero`,
`intro_quasiconvexAt_of_convexOn`), and homogeneous polynomials are homogeneous functions
(`intro_isPHomogeneous_of_isHomogeneousPolynomial`); and the rank-one matrices when `min (d, m) = 1`
(`intro_rank_eq_one_of_min`). The lifting of integrands and periodic test
maps from `ℝ^{d'×m'}` to `ℝ^{d×m}` (`lift_trunc`, `lift_quasiconvexAt_of_comp_trunc`) is in
`Morrey/Cassese/Lifting.lean`. -/

open MeasureTheory

section Jensen

variable {d m : ℕ}

/-- A function vanishing off the open unit cube has zero derivative at every point off the cube:
such a point lies in a closed half-space disjoint from the cube, on which the function vanishes. -/
theorem intro_fderiv_eq_zero_of_notMem {u : (Fin m → ℝ) → ℝ}
    (h0 : ∀ x ∉ unitCube m, u x = 0) {x : Fin m → ℝ} (hx : x ∉ unitCube m) :
    fderiv ℝ u x = 0 := by
  by_cases hdiff : DifferentiableAt ℝ u x
  swap
  · exact fderiv_zero_of_not_differentiableAt hdiff
  simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, not_forall, Set.mem_Ioo,
    not_and_or, not_lt] at hx
  obtain ⟨j, hj⟩ := hx
  have hlin : IsLinearMap ℝ fun y : Fin m → ℝ => y j := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨s, hsc, hsi, hxs, hs0⟩ : ∃ s : Set (Fin m → ℝ), Convex ℝ s ∧ (interior s).Nonempty ∧
      x ∈ s ∧ ∀ y ∈ s, u y = 0 := by
    rcases hj with hj | hj
    · refine ⟨{y | y j ≤ x j}, convex_halfSpace_le hlin _, ⟨x - Pi.single j 1, ?_⟩,
        le_refl (x j), fun y hy => h0 y ?_⟩
      · have hsub : {y : Fin m → ℝ | y j < x j} ⊆ {y | y j ≤ x j} := fun y (hy : y j < x j) =>
          show y j ≤ x j from hy.le
        refine interior_maximal hsub (isOpen_lt (continuous_apply j) continuous_const) ?_
        show (x - Pi.single j 1 : Fin m → ℝ) j < x j
        simp
      · simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, not_forall, Set.mem_Ioo]
        exact ⟨j, fun h => by have hy' : y j ≤ x j := hy; linarith [h.1]⟩
    · refine ⟨{y | x j ≤ y j}, convex_halfSpace_ge hlin _, ⟨x + Pi.single j 1, ?_⟩,
        le_refl (x j), fun y hy => h0 y ?_⟩
      · have hsub : {y : Fin m → ℝ | x j < y j} ⊆ {y | x j ≤ y j} := fun y (hy : x j < y j) =>
          show x j ≤ y j from hy.le
        refine interior_maximal hsub (isOpen_lt continuous_const (continuous_apply j)) ?_
        show x j < (x + Pi.single j 1 : Fin m → ℝ) j
        simp
      · simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies, not_forall, Set.mem_Ioo]
        exact ⟨j, fun h => by have hy' : x j ≤ y j := hy; linarith [h.2]⟩
  have h1 : HasFDerivWithinAt u (fderiv ℝ u x) s x := hdiff.hasFDerivAt.hasFDerivWithinAt
  have h2 : HasFDerivWithinAt u (0 : (Fin m → ℝ) →L[ℝ] ℝ) s x :=
    (hasFDerivWithinAt_const (0 : ℝ) x s).congr (fun y hy => hs0 y hy) (hs0 x hxs)
  exact (uniqueDiffWithinAt_convex hsc hsi (subset_closure hxs)).eq h1 h2

/-- The derivative of a Lipschitz function vanishing off the unit cube integrates to `0` over the
cube: integration by parts against `1` (`LipschitzWith.integral_lineDeriv_mul_eq`, the step of
Rademacher's theorem), and Rademacher's theorem. -/
theorem intro_integral_fderiv_eq_zero {u : (Fin m → ℝ) → ℝ} {K : NNReal} (hu : LipschitzWith K u)
    (h0 : ∀ x ∉ unitCube m, u x = 0) (v : Fin m → ℝ) :
    ∫ x in unitCube m, fderiv ℝ u x v = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [intro_fderiv_eq_zero_of_notMem h0 hx]; rfl]
  have hcs : HasCompactSupport u :=
    HasCompactSupport.intro (K := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1)
      (isCompact_univ_pi fun _ => isCompact_Icc) fun x hx =>
        h0 x fun h => hx (Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self) h)
  have hc : LipschitzWith 0 (fun _ : Fin m → ℝ => (1 : ℝ)) := LipschitzWith.const 1
  have key := hc.integral_lineDeriv_mul_eq (μ := volume) hu hcs (-v)
  have hl : ∀ x, lineDeriv ℝ (fun _ : Fin m → ℝ => (1 : ℝ)) x (-v) = 0 := fun x => by
    rw [((hasFDerivAt_const (1 : ℝ) x).hasLineDerivAt (-v)).lineDeriv]
    rfl
  simp only [hl, zero_mul, integral_zero, neg_neg, mul_one] at key
  rw [integral_congr_ae (hu.ae_differentiableAt.mono fun x hx => hx.lineDeriv_eq_fderiv.symm)]
  exact key.symm

/-- Jensen along test maps (lines 108–109): a convex function is quasiconvex at every matrix,
since the gradient of a test map has mean `0` over the cube (`intro_integral_fderiv_eq_zero`). -/
theorem intro_quasiconvexAt_of_convexOn {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (A : Matrix (Fin d) (Fin m) ℝ) : QuasiconvexAt f A := by
  intro φ K hK h0 hint
  have : IsProbabilityMeasure (volume.restrict (unitCube m)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_unitCube]⟩
  set g : (Fin d → Fin m → ℝ) → ℝ := fun X => f (Matrix.of X) with hgdef
  have hg : ConvexOn ℝ Set.univ g := hf
  have hgc : Continuous g := hg.locallyLipschitz.continuous
  have hKi : ∀ i, LipschitzWith K fun y => φ y i := fun i => by
    have h := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hK
    rw [one_mul] at h
    exact h
  have hent : ∀ i k, Integrable (fun x => fderiv ℝ (fun y => φ y i) x (Pi.single k 1))
      (volume.restrict (unitCube m)) := fun i k =>
    Integrable.of_bound (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable
      (K * ‖(Pi.single k 1 : Fin m → ℝ)‖) (ae_of_all _ fun x =>
        ((fderiv ℝ (fun y => φ y i) x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hKi i)) (norm_nonneg _)))
  let F : (Fin m → ℝ) → (Fin d → Fin m → ℝ) := fun x i k =>
    A i k + fderiv ℝ (fun y => φ y i) x (Pi.single k 1)
  have hFik : ∀ i k, Integrable (fun x => F x i k) (volume.restrict (unitCube m)) := fun i k =>
    (integrable_const (A i k)).add (hent i k)
  have hFi : ∀ i, Integrable (fun x => F x i) (volume.restrict (unitCube m)) := fun i =>
    Integrable.of_eval (hFik i)
  have hF : Integrable F (volume.restrict (unitCube m)) := Integrable.of_eval hFi
  have hmean : ∫ x in unitCube m, F x = A := by
    funext i k
    have e1 : (∫ x in unitCube m, F x) i = ∫ x in unitCube m, F x i := eval_integral hFi i
    have e2 : (∫ x in unitCube m, F x i) k = ∫ x in unitCube m, F x i k :=
      eval_integral (hFik i) k
    rw [e1, e2]
    show ∫ x in unitCube m, (A i k + fderiv ℝ (fun y => φ y i) x (Pi.single k 1)) = A i k
    rw [integral_add (integrable_const _) (hent i k), intro_integral_fderiv_eq_zero (hKi i)
        (fun x hx => by rw [h0 x hx]; rfl), integral_const]
    simp [Measure.real]
  have key := hg.map_integral_le hgc.continuousOn isClosed_univ (ae_of_all _ fun _ => trivial) hF
    hint
  rw [hmean] at key
  exact key

end Jensen

section Polynomials

variable {d m : ℕ}

/-- A homogeneous polynomial of degree `n` satisfies `Q (t x) = t^n Q (x)`. -/
theorem intro_eval_smul {σ : Type*} {Q : MvPolynomial σ ℝ} {n : ℕ} (hQ : Q.IsHomogeneous n)
    (t : ℝ) (x : σ → ℝ) : MvPolynomial.eval (t • x) Q = t ^ n * MvPolynomial.eval x Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  simp only [map_sum, Finset.mul_sum, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : ∑ i ∈ s.support, s i = n := by
    have := hQ (MvPolynomial.mem_support_iff.1 hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- A homogeneous quartic polynomial is `4`-homogeneous. -/
theorem intro_isPHomogeneous_of_isHomogeneousPolynomial {P : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hP : IsHomogeneousPolynomial 4 P) : IsPHomogeneous 4 P := by
  obtain ⟨Q, hQ, hev⟩ := hP
  intro t A
  rw [hev, hev]
  have : (fun ij : Fin d × Fin m => (t • A) ij.1 ij.2) = t • fun ij => A ij.1 ij.2 := rfl
  rw [this, intro_eval_smul hQ]
  congr 1
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Even.pow_abs ⟨2, rfl⟩]

end Polynomials

/-- A matrix with one row or one column has rank one unless it is `0`. -/
theorem intro_rank_eq_one_of_min {d m : ℕ} (h : min d m = 1) {A : Matrix (Fin d) (Fin m) ℝ}
    (hA : A ≠ 0) : A.rank = 1 := by
  have h1 : A.rank ≤ 1 := by
    rcases min_choice d m with h' | h'
    · rw [h'] at h; exact h ▸ A.rank_le_height
    · rw [h'] at h; exact h ▸ A.rank_le_width
  have h0 : A.rank ≠ 0 := fun h0 => hA (eq_zero_of_rank_eq_zero h0)
  omega


/-! ### Tools: the rank-one convex envelope and the families `C ↦ f_C`

The proofs of Theorems 1.2, 1.3 (b), 1.4 and 1.5 choose `C` strictly between the thresholds
`C^{rc}` and `C^{qc}` of a family `f_C = C^p N₁^p − N₂^p`, and take the rank-one convex envelope of
`f_C` (Proposition 2.3). -/

section Envelope

variable {d m : ℕ}

/-- The envelope step (Proposition 2.3 and its consequences, Lemma 2.1): for `p ∈ (1, ∞)`
and a continuous `p`-homogeneous `g` which is rank-one convex but not quasiconvex at `0`, the
rank-one convex envelope `f = g^{rc}` is finite, and it is a continuous `p`-homogeneous
rank-one convex integrand which is nowhere quasiconvex. Finiteness and homogeneity are
Proposition 2.3 (a); rank-one convexity holds because a supremum of rank-one convex functions is
rank-one convex; continuity is Lemma 2.1 (`External.Rindler.lemma5_6`); `f` is not quasiconvex at
`0` by Proposition 2.3 (c) (`proposition2_3_c_left`), hence nowhere quasiconvex
(`nowhereQuasiconvex_of_not_quasiconvexAt_zero`). -/
theorem intro_envelope {p : ℝ} (hp : 1 < p) {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hg : Continuous g) (hhom : IsPHomogeneous p g) (hrc : RankOneConvexAt g 0)
    (hqc : ¬ QuasiconvexAt g 0) :
    (∀ A, (((rcEnvelope g A).toReal : ℝ) : EReal) = rcEnvelope g A) ∧
      Continuous (fun A => (rcEnvelope g A).toReal) ∧
      IsIntegrand (fun A => (rcEnvelope g A).toReal) ∧
      IsPHomogeneous p (fun A => (rcEnvelope g A).toReal) ∧
      RankOneConvex (fun A => (rcEnvelope g A).toReal) ∧
      NowhereQuasiconvex (fun A => (rcEnvelope g A).toReal) := by
  obtain ⟨g₀, hg₀I, hg₀R, hg₀le, -⟩ := id hrc
  have hmin : ∀ (h : Matrix (Fin d) (Fin m) ℝ → ℝ),
      IsIntegrand h ∧ RankOneConvex h ∧ (∀ B, h B ≤ g B) → ∀ A, (h A : EReal) ≤ rcEnvelope g A :=
    fun h hh A => le_iSup₂ (f := fun (h : Matrix (Fin d) (Fin m) ℝ → ℝ)
      (_ : IsIntegrand h ∧ RankOneConvex h ∧ ∀ B, h B ≤ g B) => (h A : EReal)) h hh
  obtain ⟨hA, -⟩ := proposition2_3_a hp hg (Or.inl hhom)
  rcases hA with hbot | ⟨hfin, hhomE, -⟩
  · exfalso
    have := hmin g₀ ⟨hg₀I, hg₀R, hg₀le⟩ 0
    rw [hbot 0] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
  have hcoe : ∀ A, (((rcEnvelope g A).toReal : ℝ) : EReal) = rcEnvelope g A := fun A =>
    EReal.coe_toReal (hfin A).2 (hfin A).1
  set f : Matrix (Fin d) (Fin m) ℝ → ℝ := fun A => (rcEnvelope g A).toReal with hfdef
  have hle : ∀ (h : Matrix (Fin d) (Fin m) ℝ → ℝ),
      IsIntegrand h ∧ RankOneConvex h ∧ (∀ B, h B ≤ g B) → ∀ A, h A ≤ f A := fun h hh A => by
    have := hmin h hh A
    rw [← hcoe] at this
    exact EReal.coe_le_coe_iff.1 this
  -- a supremum of rank-one convex functions is rank-one convex
  have hR : RankOneConvex f := by
    intro A B hAB
    refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
    have key : (f ((a • x + b • y) • A + (1 - (a • x + b • y)) • B) : EReal) ≤
        ((a • f (x • A + (1 - x) • B) + b • f (y • A + (1 - y) • B) : ℝ) : EReal) := by
      rw [hfdef, hcoe]
      refine iSup₂_le fun h hh => EReal.coe_le_coe_iff.2 ?_
      refine ((hh.2.1 A B hAB).2 hx hy ha hb hab).trans ?_
      simp only [smul_eq_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hle h hh _) ha)
        (mul_le_mul_of_nonneg_left (hle h hh _) hb)
    exact EReal.coe_le_coe_iff.1 key
  have hcont : Continuous f :=
    (External.Rindler.lemma5_6 ((cov_rankOneConvex_iff f).2 hR)).continuous
  have hhf : IsPHomogeneous p f := hhomE hhom
  have hnq0 : ¬ QuasiconvexAt f 0 := fun h =>
    hqc (proposition2_3_c_left hp hg (Or.inl hhom) hrc h)
  exact ⟨hcoe, hcont, isIntegrand_of_continuous hcont, hhf, hR,
    nowhereQuasiconvex_of_not_quasiconvexAt_zero hp hcont (Or.inl hhf) hnq0⟩

/-- A family `f_C = C^p N₁^p − N₂^p` built from nonnegative absolutely homogeneous `N₁`, `N₂`
(`N (t A) = |t| N (A)`): each `f_C` is `p`-homogeneous, vanishes at `0`, and `f_C` increases with
`C ≥ 0`. -/
theorem intro_family {p : ℝ} (hp : 0 < p) {N₁ N₂ : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (h₁ : ∀ A, 0 ≤ N₁ A) (h₂ : ∀ A, 0 ≤ N₂ A) (hh₁ : ∀ (t : ℝ) A, N₁ (t • A) = |t| * N₁ A)
    (hh₂ : ∀ (t : ℝ) A, N₂ (t • A) = |t| * N₂ A) :
    (∀ C, IsPHomogeneous p fun A => C ^ p * N₁ A ^ p - N₂ A ^ p) ∧
      (∀ C, C ^ p * N₁ 0 ^ p - N₂ 0 ^ p = 0) ∧
      ∀ C C' : ℝ, 0 ≤ C' → C' ≤ C → ∀ A,
        C' ^ p * N₁ A ^ p - N₂ A ^ p ≤ C ^ p * N₁ A ^ p - N₂ A ^ p := by
  have hz : ∀ N : Matrix (Fin d) (Fin m) ℝ → ℝ, (∀ (t : ℝ) A, N (t • A) = |t| * N A) → N 0 = 0 :=
    fun N hN => by simpa using hN 0 0
  refine ⟨fun C t A => ?_, fun C => ?_, fun C C' hC' hCC' A => ?_⟩
  · simp only [hh₁, hh₂, Real.mul_rpow (abs_nonneg t) (h₁ A), Real.mul_rpow (abs_nonneg t) (h₂ A)]
    ring
  · rw [hz N₁ hh₁, hz N₂ hh₂, Real.zero_rpow hp.ne']
    ring
  · have := Real.rpow_le_rpow hC' hCC' hp.le
    have h1 := Real.rpow_nonneg (h₁ A) p
    nlinarith

/-- `C^{rc} < C` makes `f_C` rank-one convex at `0`, for a family increasing in `C ≥ 0` whose
members vanish at `0`: a minorant of some `f_{C'}`, `C' < C`, touching it at `0`, is one of
`f_C`. -/
theorem intro_rankOneConvexAt_of_rcThreshold_lt {F : ℝ → Matrix (Fin d) (Fin m) ℝ → ℝ}
    (h0 : ∀ C, F C 0 = 0) (hmono : ∀ C C', 0 ≤ C' → C' ≤ C → ∀ A, F C' A ≤ F C A) {C : ℝ}
    (h : rcThreshold F < ENNReal.ofReal C) : RankOneConvexAt (F C) 0 := by
  unfold rcThreshold at h
  obtain ⟨C', hC'⟩ := iInf_lt_iff.1 h
  obtain ⟨⟨hC'0, g, hgI, hgR, hgle, hg0⟩, hlt⟩ := iInf_lt_iff.1 hC'
  have hCC' : C' ≤ C := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1.le
  exact ⟨g, hgI, hgR, fun B => (hgle B).trans (hmono C C' hC'0 hCC' B), by rw [hg0, h0, h0]⟩

/-- A nonnegative function `N` with `N (A + B) ≤ N A + N B`, `N (−A) = N A` and
`N A ≤ c ‖A‖` (sup norm of the entries) is continuous. -/
theorem intro_continuous_of_seminorm {N : Matrix (Fin d) (Fin m) ℝ → ℝ} {c : ℝ}
    (hadd : ∀ A B, N (A + B) ≤ N A + N B) (hneg : ∀ A, N (-A) = N A)
    (hle : ∀ X : Fin d → Fin m → ℝ, N (Matrix.of X) ≤ c * ‖X‖) : Continuous N := by
  have hL : LipschitzWith (Real.toNNReal c) fun X : Fin d → Fin m → ℝ => N (Matrix.of X) := by
    refine LipschitzWith.of_dist_le_mul fun X Y => ?_
    have h1 := hadd (Matrix.of (X - Y)) (Matrix.of Y)
    have h2 := hadd (Matrix.of (Y - X)) (Matrix.of X)
    have e1 : Matrix.of (X - Y) + Matrix.of Y = Matrix.of X := by ext; simp
    have e2 : Matrix.of (Y - X) + Matrix.of X = Matrix.of Y := by ext; simp
    have e3 : N (Matrix.of (Y - X)) = N (Matrix.of (X - Y)) := by
      rw [← hneg]; congr 1; ext; simp
    rw [e1] at h1
    rw [e2, e3] at h2
    have h3 := hle (X - Y)
    rw [Real.dist_eq, dist_eq_norm, abs_le]
    have : c ≤ Real.toNNReal c := Real.le_coe_toNNReal c
    have hn : 0 ≤ ‖X - Y‖ := norm_nonneg _
    constructor <;> nlinarith
  exact hL.continuous

end Envelope

section Schatten

variable {d m : ℕ}

/-- The singular values do not change under orthogonal conjugation: `(U A Uᵀ)ᵀ (U A Uᵀ) =
U (Aᵀ A) Uᵀ` has the characteristic polynomial of `Aᵀ A`. -/
theorem intro_sval_conj {U : Matrix (Fin d) (Fin d) ℝ} (hU : U ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) : sval (U * A * Uᵀ) = sval A := by
  have hUU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).1 hU
  have heq : (U * A * Uᵀ)ᴴ * (U * A * Uᵀ) = U * (Aᴴ * A * Uᵀ) := by
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hUU, Matrix.one_mul]
  have hc : ((U * A * Uᵀ)ᴴ * (U * A * Uᵀ)).charpoly = (Aᴴ * A).charpoly := by
    rw [heq, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hUU, Matrix.mul_one]
  have := (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
    (Matrix.isHermitian_conjTranspose_mul_self (U * A * Uᵀ))
    (Matrix.isHermitian_conjTranspose_mul_self A)).2 hc
  funext i
  simp only [sval, this]

/-- The Schatten norms are invariant under orthogonal conjugation. -/
theorem intro_schattenNorm_conj (q : ENNReal) {U : Matrix (Fin d) (Fin d) ℝ}
    (hU : U ∈ Matrix.orthogonalGroup (Fin d) ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    schattenNorm q (U * A * Uᵀ) = schattenNorm q A := by
  simp only [schattenNorm, intro_sval_conj hU]

/-- The Schatten norms are continuous. -/
theorem intro_continuous_schattenNorm {q : ENNReal} (hq : 1 ≤ q) :
    Continuous (schattenNorm q : Matrix (Fin d) (Fin m) ℝ → ℝ) :=
  intro_continuous_of_seminorm (schattenNorm_add_le hq) (fun A => by
    rw [← neg_one_smul ℝ A, schattenNorm_smul hq]; simp) (schattenNorm_le_norm hq)

end Schatten

/-- Morrey's problem has a positive answer in `d × m`: every rank-one convex integrand
`f : ℝ^{d×m} → ℝ` is quasiconvex. -/
def MorreyPositive (d m : ℕ) : Prop :=
  ∀ f : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand f → RankOneConvex f → Quasiconvex f

/-- The homogeneous Morrey problem has a positive answer in `d × m` at the exponent `p`: every
`p`-homogeneous rank-one convex integrand `f : ℝ^{d×m} → ℝ` is quasiconvex at `0`. -/
def HomMorreyPositive (p : ℝ) (d m : ℕ) : Prop :=
  ∀ f : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand f → IsPHomogeneous p f → RankOneConvex f →
    QuasiconvexAt f 0

/-- **Monotonicity of Morrey's problem** (`cs-monotone`, lines 105–107): a positive answer in
`d × m` implies a positive answer in `d' × m'` whenever `d' ≤ d` and `m' ≤ m` (equivalently,
failure propagates upwards).

Proof (the paper gives none): an integrand `f` on `ℝ^{d'×m'}` lifts to `f ∘ T` on `ℝ^{d×m}`, `T A`
the upper left block, which is a rank-one convex integrand with `f` (`lift_rankOneConvex_comp`);
quasiconvexity of `f ∘ T` at the padded matrix gives that of `f`
(`lift_quasiconvexAt_of_comp_trunc`): a periodic test map `φ` of `ℝ^{m'}` lifts to the periodic
test map `x ↦ (φ (x₁, …, x_{m'}), 0, …, 0)`, through the periodic form of quasiconvexity
(Lemma 2.2, `External.Rindler.quasiconvexAtOn_iff_periodic`). Rows and columns are added in one
step this way. -/
theorem morreyPositive_mono {d m d' m' : ℕ} (hd : d' ≤ d) (hm : m' ≤ m)
    (h : MorreyPositive d m) : MorreyPositive d' m' := by
  intro f hf hR A
  have hq := h _ (lift_isIntegrand_comp hd hm hf) (lift_rankOneConvex_comp hd hm hR)
    (lift_pad hd hm A)
  have := lift_quasiconvexAt_of_comp_trunc hd hm hf hq
  rwa [lift_trunc_pad] at this

/-- **Monotonicity of the homogeneous Morrey problem** (`cs-hom-monotone`, lines 209–210): as in
the original problem, failure propagates upwards in the dimensions; that is, a positive answer in
`d × m` implies one in `d' × m'` for `d' ≤ d`, `m' ≤ m`.

Proof as for `morreyPositive_mono`; `f ∘ T` is `p`-homogeneous with `f`, and `T 0 = 0`. The
hypothesis `1 < p` is not used. -/
theorem homMorreyPositive_mono {p : ℝ} (hp : 1 < p) {d m d' m' : ℕ} (hd : d' ≤ d) (hm : m' ≤ m)
    (h : HomMorreyPositive p d m) : HomMorreyPositive p d' m' := by
  have _ := hp  -- the exponent plays no role in the lifting
  intro f hf hhom hR
  have hq := h _ (lift_isIntegrand_comp hd hm hf) (lift_isPHomogeneous_comp hd hm hhom)
    (lift_rankOneConvex_comp hd hm hR)
  have := lift_quasiconvexAt_of_comp_trunc hd hm hf hq
  rwa [lift_trunc_zero] at this

/-- **Both notions reduce to convexity when min {d, m} = 1** (`cs-min-one`, lines 108–109):
rank-one convexity is convexity. Proof: a nonzero matrix with one row or one column has rank one
(`intro_rank_eq_one_of_min`). -/
theorem rankOneConvex_iff_convexOn_of_min_eq_one {d m : ℕ} (h : min d m = 1)
    (f : Matrix (Fin d) (Fin m) ℝ → ℝ) : RankOneConvex f ↔ ConvexOn ℝ Set.univ f := by
  constructor
  · -- every two distinct matrices differ by a rank-one matrix
    intro hR
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    obtain rfl : b = 1 - a := by linarith
    rcases eq_or_ne x y with rfl | hxy
    · rw [← add_smul, hab, one_smul, smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul]
    · have key := (hR x y (intro_rank_eq_one_of_min h (sub_ne_zero.2 hxy))).2 (x := 1) (y := 0)
        ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ ha hb hab
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero, one_smul, sub_self, zero_smul,
        sub_zero, zero_add] at key
      simpa only [smul_eq_mul] using key
  · -- a convex function is convex on every segment
    intro hf A B _
    refine ⟨convex_Icc 0 1, fun s _ t _ a b ha hb hab => ?_⟩
    have key := hf.2 (Set.mem_univ (s • A + (1 - s) • B)) (Set.mem_univ (t • A + (1 - t) • B))
      ha hb hab
    obtain rfl : b = 1 - a := by linarith
    convert key using 2
    simp only [smul_eq_mul]
    module

/-- **Both notions reduce to convexity when min {d, m} = 1** (`cs-min-one`, lines 108–109):
quasiconvexity of an integrand is convexity. Proof: quasiconvexity implies rank-one convexity
(Lemma 2.2, `External.Rindler.rankOneConvex_of_quasiconvex`), which is convexity here; conversely,
Jensen's inequality along test maps (`intro_quasiconvexAt_of_convexOn`: the gradient of a
Lipschitz map vanishing off the cube has mean `0`, by integration by parts against `1`). -/
theorem quasiconvex_iff_convexOn_of_min_eq_one {d m : ℕ} (h : min d m = 1)
    {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : IsIntegrand f) :
    Quasiconvex f ↔ ConvexOn ℝ Set.univ f := by
  constructor
  · -- quasiconvex ⇒ rank-one convex (Lemma 2.2) ⇒ convex
    intro hq
    have := External.Rindler.rankOneConvex_of_quasiconvex hf.1 hf.2 ((cov_quasiconvex_iff f).2 hq)
    exact (rankOneConvex_iff_convexOn_of_min_eq_one h f).1 ((cov_rankOneConvex_iff f).1 this)
  · -- Jensen along test maps
    exact fun hc A => intro_quasiconvexAt_of_convexOn hc A

/-- **Only min {d, m} ≥ 2 is nontrivial** (`cs-min-one`, lines 108–109): Morrey's problem has a
positive answer in `d × m` when `min {d, m} ≤ 1`. Proof: a rank-one convex `f` is convex
(`rankOneConvex_iff_convexOn_of_min_eq_one`; for `min {d, m} = 0` there is one matrix), hence
quasiconvex by Jensen (`intro_quasiconvexAt_of_convexOn`). -/
theorem morreyPositive_of_min_le_one {d m : ℕ} (h : min d m ≤ 1) : MorreyPositive d m := by
  intro f _ hR
  have hc : ConvexOn ℝ Set.univ f := by
    rcases Nat.lt_or_ge (min d m) 1 with h0 | h1
    · -- `min d m = 0`: there is only one matrix
      have hsub : Subsingleton (Matrix (Fin d) (Fin m) ℝ) := by
        rcases Nat.min_eq_zero_iff.1 (show min d m = 0 by omega) with hd | hm
        · subst hd; exact ⟨fun A B => Matrix.ext fun i _ => i.elim0⟩
        · subst hm; exact ⟨fun A B => Matrix.ext fun _ j => j.elim0⟩
      refine ⟨convex_univ, fun x _ y _ a b _ _ hab => ?_⟩
      rw [Subsingleton.elim (a • x + b • y) x, Subsingleton.elim y x, smul_eq_mul, smul_eq_mul,
        ← add_mul, hab, one_mul]
    · exact (rankOneConvex_iff_convexOn_of_min_eq_one (by omega) f).1 hR
  exact fun A => intro_quasiconvexAt_of_convexOn hc A


/-! ### The families of the main theorems

The integrands `F_{n,p,q,C}` of (7) (Section 4), `f_{p,q,C}` of (30) (Section 6) and the integrand
of Theorem 7.1 are of the form `C^p N₁^p − N₂^p` (`intro_family`); their continuity and the
homogeneity of `N₁`, `N₂` are checked here. -/

section Families

/-- `α (t A) = t α (A)`. -/
theorem intro_wirtAlpha_smul {m : ℕ} (t : ℝ) (A : Matrix (Fin 2) (Fin m) ℝ) (k l : Fin m) :
    wirtAlpha (t • A) k l = (t : ℂ) * wirtAlpha A k l := by
  simp only [wirtAlpha, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- `β (t A) = t β (A)`. -/
theorem intro_wirtBeta_smul {m : ℕ} (t : ℝ) (A : Matrix (Fin 2) (Fin m) ℝ) (k l : Fin m) :
    wirtBeta (t • A) k l = (t : ℂ) * wirtBeta A k l := by
  simp only [wirtBeta, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem intro_continuous_wirtAlpha {m : ℕ} (k l : Fin m) :
    Continuous fun A : Matrix (Fin 2) (Fin m) ℝ => wirtAlpha A k l := by
  have he : ∀ i j, Continuous fun A : Matrix (Fin 2) (Fin m) ℝ => A i j := fun i j =>
    continuous_id.matrix_elem i j
  exact (Complex.continuous_ofReal.comp (((he 0 k).add (he 1 l)).div_const 2)).add
    ((Complex.continuous_ofReal.comp (((he 1 k).sub (he 0 l)).div_const 2)).mul continuous_const)

theorem intro_continuous_wirtBeta {m : ℕ} (k l : Fin m) :
    Continuous fun A : Matrix (Fin 2) (Fin m) ℝ => wirtBeta A k l := by
  have he : ∀ i j, Continuous fun A : Matrix (Fin 2) (Fin m) ℝ => A i j := fun i j =>
    continuous_id.matrix_elem i j
  exact (Complex.continuous_ofReal.comp (((he 0 k).sub (he 1 l)).div_const 2)).add
    ((Complex.continuous_ofReal.comp (((he 1 k).add (he 0 l)).div_const 2)).mul continuous_const)

/-- `‖t z‖_{ℓ_q} = |t| ‖z‖_{ℓ_q}`. -/
theorem intro_lqNorm_smul {n : ℕ} {q : ℝ} (hq : 0 < q) (t : ℝ) (z : Fin n → ℂ) :
    lqNorm q (fun j => (t : ℂ) * z j) = |t| * lqNorm q z := by
  unfold lqNorm
  simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg t) (norm_nonneg _)]
  rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg t) _)
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _), ← Real.rpow_mul
    (abs_nonneg t), mul_one_div_cancel hq.ne', Real.rpow_one]

/-- The integrand (7), `F_{n,p,q,C}`: continuous, `p`-homogeneous, `0` at `0`, increasing in
`C ≥ 0`. -/
theorem intro_blockF {n : ℕ} {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∀ C, Continuous (blockF n p q C)) ∧ (∀ C, IsPHomogeneous p (blockF n p q C)) ∧
      (∀ C, blockF n p q C 0 = 0) ∧
      ∀ C C' : ℝ, 0 ≤ C' → C' ≤ C → ∀ A, blockF n p q C' A ≤ blockF n p q C A := by
  have hP : ∀ (t : ℝ) A, lqNorm q (wirtP (t • A)) = |t| * lqNorm q (wirtP (n := n) A) :=
    fun t A => by
      rw [← intro_lqNorm_smul hq]
      congr 1
      funext j
      exact intro_wirtAlpha_smul t A _ _
  have hQ : ∀ (t : ℝ) A, lqNorm q (wirtQ (t • A)) = |t| * lqNorm q (wirtQ (n := n) A) :=
    fun t A => by
      rw [← intro_lqNorm_smul hq]
      congr 1
      funext j
      exact intro_wirtBeta_smul t A _ _
  obtain ⟨hh, h0, hmono⟩ := intro_family hp (fun A => twoByM_lqNorm_nonneg q _)
    (fun A => twoByM_lqNorm_nonneg q _) hP hQ
  have hcP : Continuous fun A : Matrix (Fin 2) (Fin (2 * n)) ℝ => lqNorm q (wirtP A) :=
    (twoByM_continuous_lqNorm hq).comp (continuous_pi fun j => intro_continuous_wirtAlpha _ _)
  have hcQ : Continuous fun A : Matrix (Fin 2) (Fin (2 * n)) ℝ => lqNorm q (wirtQ A) :=
    (twoByM_continuous_lqNorm hq).comp (continuous_pi fun j => intro_continuous_wirtBeta _ _)
  refine ⟨fun C => ?_, hh, h0, hmono⟩
  exact continuous_const.mul (hcP.rpow_const fun _ => Or.inr hp.le) |>.sub
    (hcQ.rpow_const fun _ => Or.inr hp.le)

/-- `Sym (t A) = t Sym (A)`, `Skew (t A) = t Skew (A)`. -/
theorem intro_symPart_smul {d : ℕ} (t : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    symPart (t • A) = t • symPart A := by
  simp only [symPart, Matrix.transpose_smul, ← smul_add, smul_comm t]

theorem intro_skewPart_smul {d : ℕ} (t : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    skewPart (t • A) = t • skewPart A := by
  simp only [skewPart, Matrix.transpose_smul, ← smul_sub, smul_comm t]

theorem intro_symPart_conj {d : ℕ} (U A : Matrix (Fin d) (Fin d) ℝ) :
    symPart (U * A * Uᵀ) = U * symPart A * Uᵀ := by
  simp only [symPart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem intro_skewPart_conj {d : ℕ} (U A : Matrix (Fin d) (Fin d) ℝ) :
    skewPart (U * A * Uᵀ) = U * skewPart A * Uᵀ := by
  simp only [skewPart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

theorem intro_symPart_transpose {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    symPart Aᵀ = symPart A := by
  simp only [symPart, Matrix.transpose_transpose, add_comm]

theorem intro_skewPart_transpose {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    skewPart Aᵀ = (-1 : ℝ) • skewPart A := by
  ext i j
  simp only [skewPart, Matrix.transpose_transpose, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.transpose_apply, smul_eq_mul]
  ring

/-- The integrand (30), `f_{p,q,C}`, for `q ∈ [1, ∞]`: continuous, `p`-homogeneous, `0` at `0`,
increasing in `C ≥ 0`, conjugation and transposition invariant. -/
theorem intro_kornF {d : ℕ} {p : ℝ} (hp : 0 < p) {q : ENNReal} (hq : 1 ≤ q) :
    (∀ C, Continuous (kornF d p q C)) ∧ (∀ C, IsPHomogeneous p (kornF d p q C)) ∧
      (∀ C, kornF d p q C 0 = 0) ∧
      (∀ C C' : ℝ, 0 ≤ C' → C' ≤ C → ∀ A, kornF d p q C' A ≤ kornF d p q C A) ∧
      (∀ C, IsConjugationInvariant (kornF d p q C)) ∧
      ∀ C, IsTranspositionInvariant (kornF d p q C) := by
  obtain ⟨hh, h0, hmono⟩ := intro_family (N₁ := fun A => schattenNorm q (symPart A))
    (N₂ := fun A => schattenNorm q (skewPart A)) hp (fun A => schattenNorm_nonneg q _)
    (fun A => schattenNorm_nonneg q _)
    (fun t A => by simp only [intro_symPart_smul, schattenNorm_smul hq])
    (fun t A => by simp only [intro_skewPart_smul, schattenNorm_smul hq])
  have hT : Continuous fun A : Matrix (Fin d) (Fin d) ℝ => Aᵀ := continuous_id.matrix_transpose
  have hS : Continuous fun A : Matrix (Fin d) (Fin d) ℝ => symPart A :=
    continuous_const.smul (continuous_id.add hT) (f := fun _ => (1 / 2 : ℝ))
  have hK : Continuous fun A : Matrix (Fin d) (Fin d) ℝ => skewPart A :=
    continuous_const.smul (continuous_id.sub hT) (f := fun _ => (1 / 2 : ℝ))
  have hcS : Continuous fun A : Matrix (Fin d) (Fin d) ℝ => schattenNorm q (symPart A) :=
    (intro_continuous_schattenNorm hq).comp hS
  have hcK : Continuous fun A : Matrix (Fin d) (Fin d) ℝ => schattenNorm q (skewPart A) :=
    (intro_continuous_schattenNorm hq).comp hK
  refine ⟨fun C => ?_, hh, h0, hmono, fun C U hU A => ?_, fun C A => ?_⟩
  · exact continuous_const.mul (hcS.rpow_const fun _ => Or.inr hp.le) |>.sub
      (hcK.rpow_const fun _ => Or.inr hp.le)
  · simp only [kornF, intro_symPart_conj, intro_skewPart_conj, intro_schattenNorm_conj q hU]
  · simp only [kornF, intro_symPart_transpose, intro_skewPart_transpose, schattenNorm_smul hq]
    norm_num

end Families

/-! ### The integrand of Corollary 1.6

`A = (X, Y) ∈ ℝ^{4×4}` with `X`, `Y ∈ ℝ^{4×2}` the first and the last two columns,
`q (Y) = det (Yᵀ Y)` and `G (A) = Λ ‖A‖_{S₂} + q (Y) ‖A‖_{S₂}^{−p−3} F (X)` (TeX lines 2913–2955). -/

section Corollary16

/-- `‖A‖_{S₂} = |A|` (Frobenius). -/
theorem intro_schattenNorm_two {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm 2 A = √(frobSq A) := by
  have hev := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A
  have htr := (Matrix.isHermitian_conjTranspose_mul_self A).trace_eq_sum_eigenvalues
  have htr' : (Aᴴ * A).trace = frobSq A := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, frobSq, Matrix.conjTranspose_apply,
      star_trivial, sq]
    rw [Finset.sum_comm]
  unfold schattenNorm
  split_ifs with h
  · exact absurd h (by simp)
  rw [Real.sqrt_eq_rpow, ENNReal.toReal_ofNat]
  congr 1
  rw [← htr', htr]
  simp only [sval, RCLike.ofReal_real_eq_id, id, Real.rpow_two, Real.sq_sqrt (hev _)]

/-- The entries are bounded by the Frobenius norm: `‖A‖_∞ ≤ |A|`. -/
theorem intro_norm_le_sqrt_frobSq {d m : ℕ} (X : Fin d → Fin m → ℝ) :
    ‖X‖ ≤ √(frobSq (Matrix.of X)) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  calc X i j ^ 2 ≤ ∑ j', X i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => X i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ frobSq (Matrix.of X) :=
        Finset.single_le_sum (f := fun i' => ∑ j', X i' j' ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- A continuous `p`-homogeneous `F` satisfies `|F (X)| ≤ C ‖X‖_∞^p`. -/
theorem intro_abs_le_of_isPHomogeneous {d m : ℕ} {p : ℝ} (hp : 0 < p)
    {F : Matrix (Fin d) (Fin m) ℝ → ℝ} (hF : Continuous F) (hh : IsPHomogeneous p F) :
    ∃ C, 0 ≤ C ∧ ∀ X : Fin d → Fin m → ℝ, |F (Matrix.of X)| ≤ C * ‖X‖ ^ p := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Fin d → Fin m → ℝ) 1).exists_bound_of_continuousOn
    (f := fun X => F (Matrix.of X)) hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun X => ?_⟩
  have hF0 : F 0 = 0 := by
    have := hh 0 0
    rw [zero_smul, abs_zero, Real.zero_rpow hp.ne', zero_mul] at this
    exact this
  rcases eq_or_ne X 0 with rfl | hX
  · have : Matrix.of (0 : Fin d → Fin m → ℝ) = 0 := rfl
    rw [this, hF0, abs_zero]
    positivity
  · have hn : 0 < ‖X‖ := norm_pos_iff.2 hX
    have hXe : Matrix.of X = ‖X‖ • Matrix.of (‖X‖⁻¹ • X) := by
      ext i j
      simp [hn.ne']
    have hs : ‖X‖⁻¹ • X ∈ Metric.sphere (0 : Fin d → Fin m → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 := hC _ hs
    rw [Real.norm_eq_abs] at h1
    rw [hXe, hh, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), abs_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) (by positivity)

/-- The first two columns `X` of `A = (X, Y) ∈ ℝ^{4×4}`. -/
def intro_Xc (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  Matrix.of fun i j => A i ⟨j.val, by omega⟩

/-- The last two columns `Y` of `A = (X, Y) ∈ ℝ^{4×4}`. -/
def intro_Yc (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  Matrix.of fun i j => A i ⟨j.val + 2, by omega⟩

/-- The integrand of the proof of Corollary 1.6,
`G (A) = Λ ‖A‖_{S₂} + q (Y) ‖A‖_{S₂}^{−p−3} F (X)` with `q (Y) = det (Yᵀ Y)`, `A = (X, Y)`; at
`A = 0` the formula gives `G (0) = 0` (`0^{−p−3} = 0` in Mathlib's convention). -/
noncomputable def intro_corG (Λ p : ℝ) (F : Matrix (Fin 4) (Fin 2) ℝ → ℝ)
    (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Λ * schattenNorm 2 A + ((intro_Yc A)ᵀ * intro_Yc A).det * schattenNorm 2 A ^ (-p - 3) *
    F (intro_Xc A)

theorem intro_frobSq_Xc_Yc (A : Matrix (Fin 4) (Fin 4) ℝ) :
    frobSq A = frobSq (intro_Xc A) + frobSq (intro_Yc A) := by
  simp only [frobSq, intro_Xc, intro_Yc, Matrix.of_apply, Fin.sum_univ_four, Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.zero_eta, Fin.mk_one, zero_add,
    Nat.reduceAdd, Fin.reduceFinMk]
  ring

theorem intro_det_gram (Y : Matrix (Fin 4) (Fin 2) ℝ) :
    0 ≤ (Yᵀ * Y).det ∧ (Yᵀ * Y).det ≤ frobSq Y ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, frobSq, Fin.sum_univ_two]
  constructor
  · nlinarith [sq_nonneg (Y 0 0 * Y 1 1 - Y 1 0 * Y 0 1), sq_nonneg (Y 0 0 * Y 2 1 - Y 2 0 * Y 0 1),
      sq_nonneg (Y 0 0 * Y 3 1 - Y 3 0 * Y 0 1), sq_nonneg (Y 1 0 * Y 2 1 - Y 2 0 * Y 1 1),
      sq_nonneg (Y 1 0 * Y 3 1 - Y 3 0 * Y 1 1), sq_nonneg (Y 2 0 * Y 3 1 - Y 3 0 * Y 2 1)]
  · nlinarith [sq_nonneg (Y 0 0 * Y 0 1 + Y 1 0 * Y 1 1 + Y 2 0 * Y 2 1 + Y 3 0 * Y 3 1),
      sq_nonneg (Y 0 0), sq_nonneg (Y 1 0), sq_nonneg (Y 2 0), sq_nonneg (Y 3 0),
      sq_nonneg (Y 0 1), sq_nonneg (Y 1 1), sq_nonneg (Y 2 1), sq_nonneg (Y 3 1)]

theorem intro_continuous_frobSq {d m : ℕ} : Continuous (frobSq : Matrix (Fin d) (Fin m) ℝ → ℝ) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).pow 2

theorem intro_Xc_smul (t : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    intro_Xc (t • A) = t • intro_Xc A := rfl

theorem intro_Yc_smul (t : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    intro_Yc (t • A) = t • intro_Yc A := rfl

theorem intro_frobSq_Xc_le (A : Matrix (Fin 4) (Fin 4) ℝ) : frobSq (intro_Xc A) ≤ frobSq A := by
  rw [intro_frobSq_Xc_Yc A]; linarith [tbt_frobSq_nonneg (intro_Yc A)]

theorem intro_frobSq_Yc_le (A : Matrix (Fin 4) (Fin 4) ℝ) : frobSq (intro_Yc A) ≤ frobSq A := by
  rw [intro_frobSq_Xc_Yc A]; linarith [tbt_frobSq_nonneg (intro_Xc A)]

/-- The second term of `G` is bounded by `C ‖A‖`: `|q (Y)| ≤ |A|⁴` and `|F (X)| ≤ C |A|^p`. -/
theorem intro_corG_bound {p : ℝ} (hp : 0 < p) {F : Matrix (Fin 4) (Fin 2) ℝ → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ X : Fin 4 → Fin 2 → ℝ, |F (Matrix.of X)| ≤ C * ‖X‖ ^ p)
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    |((intro_Yc A)ᵀ * intro_Yc A).det * √(frobSq A) ^ (-p - 3) * F (intro_Xc A)| ≤
      C * √(frobSq A) := by
  set ν := √(frobSq A) with hν
  have hν0 : 0 ≤ ν := Real.sqrt_nonneg _
  rcases hν0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith), mul_zero, zero_mul, abs_zero, mul_zero]
  obtain ⟨hq0, hq1⟩ := intro_det_gram (intro_Yc A)
  have hfr : frobSq A = ν ^ 2 := (Real.sq_sqrt (tbt_frobSq_nonneg A)).symm
  have hq : ((intro_Yc A)ᵀ * intro_Yc A).det ≤ ν ^ (4 : ℝ) := by
    calc _ ≤ frobSq (intro_Yc A) ^ 2 := hq1
      _ ≤ frobSq A ^ 2 := pow_le_pow_left₀ (tbt_frobSq_nonneg _) (intro_frobSq_Yc_le A) 2
      _ = ν ^ (4 : ℝ) := by rw [hfr, ← pow_mul]; norm_cast
  have hF : |F (intro_Xc A)| ≤ C * ν ^ p := by
    refine (hC _).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) ?_ hp.le) hC0)
    exact (intro_norm_le_sqrt_frobSq _).trans (Real.sqrt_le_sqrt (intro_frobSq_Xc_le A))
  rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg (Real.rpow_nonneg hν0 _)]
  calc ((intro_Yc A)ᵀ * intro_Yc A).det * ν ^ (-p - 3) * |F (intro_Xc A)|
      ≤ ν ^ (4 : ℝ) * ν ^ (-p - 3) * (C * ν ^ p) := by gcongr
    _ = C * ν ^ ((4 : ℝ) + (-p - 3) + p) := by
        rw [Real.rpow_add hpos, Real.rpow_add hpos]; ring
    _ = C * ν := by rw [show (4 : ℝ) + (-p - 3) + p = 1 by ring, Real.rpow_one]

/-- Proof of Corollary 1.6, first claim: `G` is continuous and `1`-homogeneous, and
nonnegative for `Λ` large. -/
theorem intro_corG_basic {p : ℝ} (hp : 1 < p) {F : Matrix (Fin 4) (Fin 2) ℝ → ℝ}
    (hFc : Continuous F) (hFh : IsPHomogeneous p F) :
    (∀ Λ, Continuous (intro_corG Λ p F)) ∧ (∀ Λ, IsPHomogeneous 1 (intro_corG Λ p F)) ∧
      ∃ Λ₀, ∀ Λ ≥ Λ₀, ∀ A, 0 ≤ intro_corG Λ p F A := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C, hC0, hC⟩ := intro_abs_le_of_isPHomogeneous hp0 hFc hFh
  have hG : ∀ Λ A, intro_corG Λ p F A = Λ * √(frobSq A) +
      ((intro_Yc A)ᵀ * intro_Yc A).det * √(frobSq A) ^ (-p - 3) * F (intro_Xc A) := by
    intro Λ A; simp only [intro_corG, intro_schattenNorm_two]
  have hν : Continuous fun A : Matrix (Fin 4) (Fin 4) ℝ => √(frobSq A) :=
    intro_continuous_frobSq.sqrt
  have hY : Continuous fun A : Matrix (Fin 4) (Fin 4) ℝ => ((intro_Yc A)ᵀ * intro_Yc A).det := by
    refine Continuous.matrix_det (Continuous.matrix_mul ?_ ?_)
    · exact (continuous_pi fun i => continuous_pi fun j =>
        continuous_id.matrix_elem _ _).matrix_transpose
    · exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem _ _
  have hX : Continuous fun A : Matrix (Fin 4) (Fin 4) ℝ => F (intro_Xc A) :=
    hFc.comp (continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem _ _)
  refine ⟨fun Λ => ?_, fun Λ t A => ?_, ⟨C, fun Λ hΛ A => ?_⟩⟩
  · -- continuity: away from `0` by the formula, at `0` by the bound `|G| ≤ (|Λ| + C) ‖A‖`
    rw [show intro_corG Λ p F = fun A => Λ * √(frobSq A) +
      ((intro_Yc A)ᵀ * intro_Yc A).det * √(frobSq A) ^ (-p - 3) * F (intro_Xc A) from
        funext (hG Λ)]
    refine continuous_iff_continuousAt.2 fun A => ?_
    rcases (Real.sqrt_nonneg (frobSq A)).eq_or_lt with h0 | hpos
    · have hval : Λ * √(frobSq A) + ((intro_Yc A)ᵀ * intro_Yc A).det * √(frobSq A) ^ (-p - 3) *
          F (intro_Xc A) = 0 := by
        rw [← h0, Real.zero_rpow (by linarith)]; ring
      unfold ContinuousAt
      simp only
      rw [hval]
      have hlim : Filter.Tendsto (fun B : Matrix (Fin 4) (Fin 4) ℝ => (|Λ| + C) * √(frobSq B))
          (nhds A) (nhds 0) := by
        have := ((hν.tendsto A).const_mul (|Λ| + C))
        rwa [← h0, mul_zero] at this
      refine squeeze_zero_norm (fun B => ?_) hlim
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [intro_corG_bound hp0 hC0 hC B, Real.sqrt_nonneg (frobSq B)]
    · exact (continuousAt_const.mul hν.continuousAt).add ((hY.continuousAt.mul
        (hν.continuousAt.rpow_const (Or.inl hpos.ne'))).mul hX.continuousAt)
  · -- `1`-homogeneity: `q (t Y) = t⁴ q (Y)`, `‖t A‖ = |t| ‖A‖`, `F (t X) = |t|^p F (X)`
    rw [hG, hG, tbt_frobSq_smul, intro_Yc_smul, intro_Xc_smul, hFh,
      Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, Real.rpow_one, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.det_smul, Fintype.card_fin]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · have hta : 0 < |t| := abs_pos.2 ht
      rw [Real.mul_rpow hta.le (Real.sqrt_nonneg _)]
      have h4 : (t * t) ^ 2 * |t| ^ (-p - 3) * |t| ^ p = |t| := by
        have : (t * t) ^ 2 = |t| ^ (4 : ℝ) := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
            Even.pow_abs ⟨2, rfl⟩]
          ring
        rw [this, ← Real.rpow_add hta, ← Real.rpow_add hta,
          show (4 : ℝ) + (-p - 3) + p = 1 by ring, Real.rpow_one]
      linear_combination (((intro_Yc A)ᵀ * intro_Yc A).det * √(frobSq A) ^ (-p - 3) *
        F (intro_Xc A)) * h4
  · -- nonnegativity for `Λ ≥ C`
    rw [hG]
    have h1 := (abs_le.1 (intro_corG_bound hp0 hC0 hC A)).1
    nlinarith [Real.sqrt_nonneg (frobSq A)]

/-- Bernoulli: `(1 + u)^{−a} ≥ 1 − a u` for `u ≥ 0`, `a ≥ 1`. -/
theorem intro_one_sub_le_rpow_neg {u a : ℝ} (hu : 0 ≤ u) (ha : 1 ≤ a) :
    1 - a * u ≤ (1 + u) ^ (-a) := by
  have h1 : 0 < 1 + u := by linarith
  have key := one_add_mul_self_le_rpow_one_add (s := (1 + u)⁻¹ - 1)
    (by have := inv_pos.2 h1; linarith) ha
  rw [add_sub_cancel, Real.inv_rpow h1.le, ← Real.rpow_neg h1.le] at key
  refine le_trans ?_ key
  have : (1 + u)⁻¹ - 1 = -(u / (1 + u)) := by field_simp; ring
  rw [this]
  have h2 : u / (1 + u) ≤ u := div_le_self hu (by linarith)
  nlinarith

/-- The pointwise expansion of the witness of Corollary 1.6: with `s = |M|²`, `v = F (M)` and
`0 ≤ q ≤ 1`, `Λ √(1 + ε² s) + q (1 + ε² s)^{−(p+3)/2} ε^p v = Λ + ε^p q v + O (ε²)`, with the
constant `|Λ| S₀ + (p + 3) S₀ V / 2` for `s ≤ S₀`, `|v| ≤ V` and `ε ≤ 1`. -/
theorem intro_witness_est {Λ p q s v S₀ V ε : ℝ} (hp : 0 < p) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hs : 0 ≤ s) (hsS : s ≤ S₀) (hv : |v| ≤ V) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    |Λ * √(1 + ε ^ 2 * s) + q * √(1 + ε ^ 2 * s) ^ (-p - 3) * (ε ^ p * v) - Λ -
      ε ^ p * (q * v)| ≤ ε ^ 2 * (|Λ| * S₀ + (p + 3) / 2 * S₀ * V) := by
  have hV : 0 ≤ V := (abs_nonneg v).trans hv
  have hx : 0 ≤ ε ^ 2 * s := by positivity
  have hεs : ε ^ 2 * s ≤ ε ^ 2 * S₀ := mul_le_mul_of_nonneg_left hsS (by positivity)
  -- the norm term: `|Λ (√(1 + x) − 1)| ≤ |Λ| x`
  have hΛ : |Λ * (√(1 + ε ^ 2 * s) - 1)| ≤ |Λ| * (ε ^ 2 * s) := by
    have h2 : 1 ≤ √(1 + ε ^ 2 * s) := Real.one_le_sqrt.2 (by linarith)
    have h3 : √(1 + ε ^ 2 * s) ≤ 1 + ε ^ 2 * s := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ √(1 + ε ^ 2 * s) - 1)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg Λ)
  -- the power term: `√(1 + x)^{−p−3} = (1 + x)^{−a}` with `a = (p + 3)/2`, and
  -- `1 − a x ≤ (1 + x)^{−a} ≤ 1`
  set a := (p + 3) / 2 with ha
  have hpow : √(1 + ε ^ 2 * s) ^ (-p - 3) = (1 + ε ^ 2 * s) ^ (-a) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]; congr 1; ring
  rw [hpow]
  set w := (1 + ε ^ 2 * s) ^ (-a) with hw
  have hw1 : w ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by rw [ha]; linarith)
  have hw0 : 1 - a * (ε ^ 2 * s) ≤ w := intro_one_sub_le_rpow_neg hx (by rw [ha]; linarith)
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε0 p
  have hεp1 : ε ^ p ≤ 1 := Real.rpow_le_one hε0.le hε1 hp.le
  -- `|q w ε^p v − q ε^p v| = q ε^p |v| (1 − w) ≤ a ε² S₀ V`
  have hdiff : |q * w * (ε ^ p * v) - ε ^ p * (q * v)| ≤ a * (ε ^ 2 * S₀) * V := by
    have e : q * w * (ε ^ p * v) - ε ^ p * (q * v) = q * ε ^ p * v * (w - 1) := by ring
    rw [e, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ q * ε ^ p),
      abs_of_nonpos (by linarith : w - 1 ≤ 0)]
    have h1 : q * ε ^ p ≤ 1 := by nlinarith
    have h2 : |v| * -(w - 1) ≤ V * (a * (ε ^ 2 * s)) :=
      mul_le_mul hv (by linarith) (by linarith) hV
    have h3 : V * (a * (ε ^ 2 * s)) ≤ a * (ε ^ 2 * S₀) * V := by
      have : 0 ≤ a := by rw [ha]; linarith
      calc V * (a * (ε ^ 2 * s)) = a * (ε ^ 2 * s) * V := by ring
        _ ≤ a * (ε ^ 2 * S₀) * V := by gcongr
    have h5 : 0 ≤ |v| * -(w - 1) := mul_nonneg (abs_nonneg _) (by linarith)
    calc q * ε ^ p * |v| * -(w - 1) = q * ε ^ p * (|v| * -(w - 1)) := by ring
      _ ≤ 1 * (|v| * -(w - 1)) := mul_le_mul_of_nonneg_right h1 h5
      _ ≤ _ := by linarith
  have e : Λ * √(1 + ε ^ 2 * s) + q * w * (ε ^ p * v) - Λ - ε ^ p * (q * v) =
      Λ * (√(1 + ε ^ 2 * s) - 1) + (q * w * (ε ^ p * v) - ε ^ p * (q * v)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hεs (abs_nonneg Λ)]

/-- The matrix `B = (0, Y₀)` of the proof of Corollary 1.6 (TeX lines 2945–2946): `X = 0`, and
`Y₀` has the columns `e₁ / √2`, `e₂ / √2`; `|B| = 1`, `rank Y₀ = 2` and
`q (Y₀) = det (Y₀ᵀ Y₀) = 1/4` (`intro_rank_B`, `intro_Xc_B`, `intro_Yc_B`). -/
noncomputable def intro_B : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 3) then (√2)⁻¹ else 0

theorem intro_rank_B : intro_B.rank = 2 := by
  apply le_antisymm
  · -- `B = U V` with `V` of two rows
    have : intro_B =
        (Matrix.of fun (i : Fin 4) (k : Fin 2) => if i.val = k.val then (√2)⁻¹ else 0) *
        Matrix.of fun (k : Fin 2) (j : Fin 4) => if j.val = k.val + 2 then (1 : ℝ) else 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [intro_B, Matrix.mul_apply, Fin.sum_univ_two]
    rw [this]
    exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_height _)
  · -- the block in rows `0, 1` and columns `2, 3` is `(√2)⁻¹ • 1`, invertible
    have hsub : intro_B.submatrix (fun i : Fin 2 => (⟨i.val, by omega⟩ : Fin 4))
        (fun j : Fin 2 => (⟨j.val + 2, by omega⟩ : Fin 4)) = (√2)⁻¹ • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [intro_B]
    have hu : IsUnit ((√2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, isUnit_iff_ne_zero]
      positivity
    have := Matrix.rank_submatrix_le intro_B (fun i : Fin 2 => (⟨i.val, by omega⟩ : Fin 4))
      (fun j : Fin 2 => (⟨j.val + 2, by omega⟩ : Fin 4))
    rw [hsub, Matrix.rank_of_isUnit _ hu, Fintype.card_fin] at this
    exact this

theorem intro_Xc_add (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    intro_Xc (A + B) = intro_Xc A + intro_Xc B := rfl

theorem intro_Yc_add (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    intro_Yc (A + B) = intro_Yc A + intro_Yc B := rfl

theorem intro_Xc_B : intro_Xc intro_B = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intro_Xc, intro_B]

/-- `q (Y₀) = det (Y₀ᵀ Y₀) = 1/4` and `|Y₀|² = 1`. -/
theorem intro_Yc_B : ((intro_Yc intro_B)ᵀ * intro_Yc intro_B).det = 1 / 4 ∧
    frobSq (intro_Yc intro_B) = 1 := by
  have h2 : (√2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num), one_div]
  constructor
  · rw [Matrix.det_fin_two]
    simp only [intro_Yc, intro_B, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply,
      Matrix.of_apply]
    simp
    nlinarith [h2]
  · simp only [frobSq, Fin.sum_univ_four, Fin.sum_univ_two, intro_Yc, intro_B, Matrix.of_apply]
    norm_num

/-- `fderiv (ε g) = ε fderiv g`. -/
theorem intro_fderiv_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ε : ℝ}
    (hε : ε ≠ 0) (g : E → ℝ) (x : E) :
    fderiv ℝ (fun y => ε * g y) x = ε • fderiv ℝ g x := by
  by_cases h : DifferentiableAt ℝ g x
  · exact fderiv_const_mul h ε
  · have h' : ¬ DifferentiableAt ℝ (fun y => ε * g y) x := fun h' => h (by
      have := h'.const_mul ε⁻¹
      simp only [← mul_assoc, inv_mul_cancel₀ hε, one_mul] at this
      exact this)
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h', smul_zero]

/-- The entries of the derivative matrix of a `K`-Lipschitz map are bounded by `K`. -/
theorem intro_abs_jac_le {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hK : LipschitzWith K φ) (y : Fin m → ℝ) (i : Fin d) (k : Fin m) : |jac φ y i k| ≤ K := by
  have hKi : LipschitzWith K fun y => φ y i := by
    have h := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hK
    rw [one_mul] at h
    exact h
  have h1 := (fderiv ℝ (fun z => φ z i) y).le_opNorm (Pi.single k 1)
  have h2 := norm_fderiv_le_of_lipschitz ℝ hKi (x₀ := y)
  have h3 : ‖(Pi.single k (1 : ℝ) : Fin m → ℝ)‖ ≤ 1 := by
    rw [Pi.norm_single, norm_one]
  rw [← Real.norm_eq_abs]
  calc ‖jac φ y i k‖ ≤ ‖fderiv ℝ (fun z => φ z i) y‖ * ‖(Pi.single k 1 : Fin m → ℝ)‖ := h1
    _ ≤ K * 1 := mul_le_mul h2 h3 (norm_nonneg _) K.2
    _ = K := mul_one _

open Filter Topology in
open scoped Convolution ContDiff in
/-- The smooth periodic witness of the proof of Corollary 1.6 (TeX lines 2946–2947), a density
step that the paper does not state: if a `K`-Lipschitz `ℤ^m`-periodic `φ` has
`∫_{(0,1)^m} F (∇φ) < 0` for a continuous `F` (the periodic form of quasiconvexity, Lemma 2.2,
gives such a `φ`), then so has a smooth one, still `K`-Lipschitz and periodic.

Proof, by mollification: the mollifications `φ_k = ρ_k ⋆ φ` (componentwise, `ρ_k` the normed bump
of radius `1 / (k + 1)`, `ContDiffBump.ofRadius`) are smooth (`contDiff_normed_convolution`),
`K`-Lipschitz (`normed_convolution_lipschitzWith`) and periodic (`normed_convolution_add_right`),
and `∇φ_k → ∇φ` almost everywhere (`ae_tendsto_fderiv_normed_convolution`, with the radii in the
ratio `2`); the entries of `∇φ_k` are bounded by `K` (`intro_abs_jac_le`) and `F` is bounded on
that bounded set, so `∫ F (∇φ_k) → ∫ F (∇φ) < 0` by dominated convergence. -/
theorem intro_smooth_periodic_witness {d m : ℕ} {F : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hFc : Continuous F) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hK : LipschitzWith K φ)
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (hlt : ∫ y in CalculusOfVariations.unitCube m, F (jac φ y) < 0) :
    ∃ ψ : (Fin m → ℝ) → Fin d → ℝ, ContDiff ℝ ∞ ψ ∧ LipschitzWith K ψ ∧
      (∀ (x : Fin m → ℝ) (z : Fin m → ℤ), ψ (x + fun i => (z i : ℝ)) = ψ x) ∧
      IntegrableOn (fun y => F (jac ψ y)) (CalculusOfVariations.unitCube m) ∧
      ∫ y in CalculusOfVariations.unitCube m, F (jac ψ y) < 0 := by
  -- the components of `φ` are `K`-Lipschitz
  have hKi : ∀ i, LipschitzWith K fun y => φ y i := fun i => by
    have h := (LipschitzWith.eval (α := fun _ : Fin d => ℝ) i).comp hK
    rw [one_mul] at h
    exact h
  -- the mollifiers `ρ_k` of radius `1 / (k + 1)` and the mollifications `φ_k = ρ_k ⋆ φ`
  set b : ℕ → ContDiffBump (0 : Fin m → ℝ) := fun k =>
    ContDiffBump.ofRadius (Nat.one_div_pos_of_nat (n := k)) with hb
  set ψ : ℕ → (Fin m → ℝ) → Fin d → ℝ := fun k x i =>
    ((b k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun y => φ y i) x with hψ
  have hψs : ∀ k, ContDiff ℝ ∞ (ψ k) := fun k =>
    contDiff_pi.2 fun i => (b k).contDiff_normed_convolution (hKi i).continuous.locallyIntegrable
  have hψK : ∀ k, LipschitzWith K (ψ k) := fun k =>
    LipschitzWith.of_dist_le_mul fun x y => (dist_pi_le_iff (by positivity)).2 fun i =>
      ((b k).normed_convolution_lipschitzWith (μ := volume) (hKi i)).dist_le_mul x y
  have hψper : ∀ k (x : Fin m → ℝ) (z : Fin m → ℤ), ψ k (x + fun i => (z i : ℝ)) = ψ k x :=
    fun k x z => funext fun i => (b k).normed_convolution_add_right (fun y => by rw [hper]) x
  -- `∇φ_k → ∇φ` almost everywhere
  have hrad : Tendsto (fun k => (b k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hrat : ∀ᶠ k in atTop, (b k).rOut ≤ 2 * (b k).rIn := Eventually.of_forall fun k => by
    simp only [hb, ContDiffBump.ofRadius_rOut, ContDiffBump.ofRadius_rIn]
    linarith
  have hae : ∀ᵐ y ∂volume, Tendsto (fun k => jac (ψ k) y) atTop (𝓝 (jac φ y)) := by
    have h : ∀ i j, ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)),
        Tendsto (fun k => jac (ψ k) y i j) atTop (𝓝 (jac φ y i j)) := fun i j =>
      ContDiffBump.ae_tendsto_fderiv_normed_convolution hrad hrat (hKi i) (Pi.single j 1)
    have h' : ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)), ∀ i j,
        Tendsto (fun k => jac (ψ k) y i j) atTop (𝓝 (jac φ y i j)) := by
      rw [ae_all_iff]
      exact fun i => ae_all_iff.2 (h i)
    filter_upwards [h'] with y hy
    exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hy i j
  -- `F (∇φ_k)` is bounded: `|∇φ_k| ≤ K`, and `F` is bounded on the ball of radius `K`
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin d → Fin m → ℝ) K).exists_bound_of_continuousOn
    (f := fun X => F (Matrix.of X)) hFc.continuousOn
  have hbd : ∀ k y, ‖F (jac (ψ k) y)‖ ≤ C := fun k y => by
    have hm : Matrix.of.symm (jac (ψ k) y) ∈ Metric.closedBall (0 : Fin d → Fin m → ℝ) K := by
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg K.2).2 fun i => (pi_norm_le_iff_of_nonneg K.2).2 fun j => by
        rw [Real.norm_eq_abs]; exact intro_abs_jac_le (hψK k) y i j
    simpa using hC _ hm
  have hFm : ∀ u : (Fin m → ℝ) → Fin d → ℝ, AEStronglyMeasurable (fun y => F (jac u y))
      (volume.restrict (CalculusOfVariations.unitCube m)) := fun u => by
    have hjm : Measurable fun y => Matrix.of.symm (jac u y) :=
      Measurable.of_eval fun i => Measurable.of_eval fun k => measurable_fderiv_apply_const ℝ _ _
    exact ((show Continuous fun X : Fin d → Fin m → ℝ => F (Matrix.of X) from hFc).measurable.comp
      hjm).aestronglyMeasurable
  have : IsFiniteMeasure (volume.restrict (CalculusOfVariations.unitCube m)) :=
    ⟨by rw [Measure.restrict_apply_univ, unitCube_eq_cov, volume_unitCube]
        exact ENNReal.one_lt_top⟩
  -- dominated convergence: `∫ F (∇φ_k) → ∫ F (∇φ) < 0`
  have hlim := tendsto_integral_of_dominated_convergence (fun _ => C) (fun k => hFm (ψ k))
    (integrable_const C) (fun k => ae_of_all _ (hbd k))
    (ae_restrict_of_ae (hae.mono fun y hy => (hFc.tendsto _).comp hy))
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hlt)).exists
  exact ⟨ψ k, hψs k, hψK k, hψper k, Integrable.of_bound (hFm _) C (ae_of_all _ (hbd k)), hk⟩

/-- Proof of Corollary 1.6, the witness (TeX lines 2945–2954): `G` is not quasiconvex at
`B = (0, Y₀)`, `|B| = 1`, `rank Y₀ = 2`. Take a smooth periodic `φ : 𝕋² → ℝ⁴` with
`∫_{𝕋²} F (∇φ) < 0` (`intro_smooth_periodic_witness`, from the Lipschitz periodic witness of the
periodic form of quasiconvexity, Lemma 2.2) and `Ψ_ε (x, y) = ε φ (x)`. Then
`G (B + ∇Ψ_ε) = Λ √(1 + ε² |∇φ|²) + q (Y₀) (1 + ε² |∇φ|²)^{−(p+3)/2} ε^p F (∇φ)` and `G (B) = Λ`,
so `∫_{𝕋⁴} [G (B + ∇Ψ_ε) − G (B)] = ε^p q (Y₀) ∫_{𝕋²} F (∇φ) + O (ε²)` (`intro_witness_est`,
`∇φ` is bounded), which is `< 0` for small `ε > 0` since `p < 2`; this contradicts the periodic
form of quasiconvexity of `G` at `B` (Lemma 2.2), `Ψ_ε` being Lipschitz and periodic. -/
theorem intro_corG_not_quasiconvexAt {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    {F : Matrix (Fin 4) (Fin 2) ℝ → ℝ} (hFc : Continuous F) (hFh : IsPHomogeneous p F)
    (hFq : ¬ QuasiconvexAt F 0) (Λ : ℝ) : ¬ QuasiconvexAt (intro_corG Λ p F) intro_B := by
  have hp0 : 0 < p := by linarith
  have h24 : 2 ≤ 4 := by norm_num
  obtain ⟨hGc, -, -⟩ := intro_corG_basic hp hFc hFh
  have hFI := isIntegrand_of_continuous hFc
  have hGI := isIntegrand_of_continuous (hGc Λ)
  have hF0 : F 0 = 0 := by
    have := hFh 0 0
    rwa [zero_smul, abs_zero, Real.zero_rpow hp0.ne', zero_mul] at this
  obtain ⟨hdet, hfr⟩ := intro_Yc_B
  -- a Lipschitz periodic witness for `F` at `0` (Lemma 2.2), and from it a smooth periodic `φ`
  -- with `∫_{(0,1)²} F (∇φ) < 0`
  have hFper : ¬ CalculusOfVariations.QuasiconvexAtPeriodic F 0 := fun h =>
    hFq ((cov_quasiconvexAtOn_unitCube_iff F 0).1
      ((External.Rindler.quasiconvexAtOn_iff_periodic hFI.1 hFI.2 0).2 h))
  simp only [CalculusOfVariations.QuasiconvexAtPeriodic, not_forall, not_le] at hFper
  obtain ⟨φ₀, K, hK₀, hper₀, -, hlt₀⟩ := hFper
  simp only [zero_add, hF0, grad_eq] at hlt₀
  obtain ⟨φ, -, hK, hper, hint, hlt⟩ := intro_smooth_periodic_witness hFc hK₀ hper₀ hlt₀
  set I := ∫ y in CalculusOfVariations.unitCube 2, F (jac φ y) with hIdef
  -- bounds on `∇φ` and `F (∇φ)`
  have hent : ∀ y i k, |jac φ y i k| ≤ K := intro_abs_jac_le hK
  have hnorm : ∀ y, ‖Matrix.of.symm (jac φ y)‖ ≤ K := fun y =>
    (pi_norm_le_iff_of_nonneg K.2).2 fun i => (pi_norm_le_iff_of_nonneg K.2).2 fun k => by
      rw [Real.norm_eq_abs]; exact hent y i k
  have hS : ∀ y, frobSq (jac φ y) ≤ 8 * (K : ℝ) ^ 2 := fun y => by
    calc frobSq (jac φ y) ≤ ∑ _i : Fin 4, ∑ _k : Fin 2, (K : ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hent y i k) 2
      _ = 8 * (K : ℝ) ^ 2 := by simp; ring
  obtain ⟨CF, hCF0, hCF⟩ := intro_abs_le_of_isPHomogeneous hp0 hFc hFh
  have hFb : ∀ y, |F (jac φ y)| ≤ CF * (K : ℝ) ^ p := fun y =>
    ((show |F (jac φ y)| ≤ CF * ‖Matrix.of.symm (jac φ y)‖ ^ p by
      simpa using hCF (Matrix.of.symm (jac φ y))).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hnorm y) hp0.le) hCF0))
  -- the constants, and `ε` with `ε^{2−p} E < c`
  set S₀ : ℝ := 8 * (K : ℝ) ^ 2 with hS₀
  set V : ℝ := CF * (K : ℝ) ^ p with hV
  set E : ℝ := |Λ| * S₀ + (p + 3) / 2 * S₀ * V with hE
  have hE0 : 0 ≤ E := by positivity
  set c : ℝ := 1 / 4 * (-I) with hc
  have hc0 : 0 < c := mul_pos (by norm_num) (by linarith)
  set ε : ℝ := min 1 ((c / (E + 1)) ^ (1 / (2 - p))) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεE : ε ^ (2 - p) * E < c := by
    have h1 : ε ^ (2 - p) ≤ c / (E + 1) := by
      calc ε ^ (2 - p) ≤ ((c / (E + 1)) ^ (1 / (2 - p))) ^ (2 - p) :=
            Real.rpow_le_rpow hε0.le (min_le_right _ _) (by linarith)
        _ = c / (E + 1) := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith), Real.rpow_one]
    calc ε ^ (2 - p) * E ≤ c / (E + 1) * E := mul_le_mul_of_nonneg_right h1 hE0
      _ < c := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
  -- the test map `Ψ_ε (x) = ε φ (x₁, x₂)` on `𝕋⁴`
  set Ψ : (Fin 4 → ℝ) → Fin 4 → ℝ := fun x i => ε * φ (lift_projX h24 x) i with hΨ
  have hΨeq : Ψ = (ε • ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) ∘ φ ∘ lift_projX h24 := by
    funext x i
    simp [hΨ]
  have hΨK : LipschitzWith (‖ε • ContinuousLinearMap.id ℝ (Fin 4 → ℝ)‖₊ * (K *
      ‖lift_projX h24‖₊)) Ψ := by
    rw [hΨeq]
    exact (ε • ContinuousLinearMap.id ℝ (Fin 4 → ℝ)).lipschitzWith.comp
      (hK.comp (lift_projX h24).lipschitzWith)
  have hΨper : ∀ (x : Fin 4 → ℝ) (z : Fin 4 → ℤ), Ψ (x + fun i => (z i : ℝ)) = Ψ x := by
    intro x z
    have hz : lift_projX h24 (fun i => (z i : ℝ)) =
        fun j => ((z (Fin.castLE h24 j) : ℤ) : ℝ) := rfl
    simp only [hΨ, map_add, hz, hper]
  -- its gradient: `∇Ψ_ε = (ε ∇φ, 0)`
  have hjac : ∀ x i k, jac Ψ x i k =
      ε * fderiv ℝ (fun z => φ z i) (lift_projX h24 x) (lift_projX h24 (Pi.single k 1)) := by
    intro x i k
    simp only [jac, Matrix.of_apply, hΨ]
    rw [intro_fderiv_const_mul hε0.ne' (fun y => φ (lift_projX h24 y) i)]
    simp only [smul_apply, smul_eq_mul]
    rw [show (fun y => φ (lift_projX h24 y) i) = (fun z => φ z i) ∘ lift_projX h24 from rfl,
      lift_fderiv_comp_projX]
  have hjX : ∀ x, intro_Xc (jac Ψ x) = ε • jac φ (lift_projX h24 x) := fun x => by
    ext i j
    rw [intro_Xc, Matrix.of_apply, hjac, Matrix.smul_apply, smul_eq_mul,
      show (⟨j.val, by omega⟩ : Fin 4) = Fin.castLE h24 j from rfl, lift_projX_single]
    rfl
  have hjY : ∀ x, intro_Yc (jac Ψ x) = 0 := fun x => by
    ext i j
    simp only [intro_Yc, Matrix.of_apply, hjac, Matrix.zero_apply]
    have : lift_projX h24 (Pi.single (⟨j.val + 2, by omega⟩ : Fin 4) 1) = 0 := by
      funext j'
      simp only [lift_projX_apply, Pi.single_apply, Pi.zero_apply]
      split_ifs with h
      · have := congrArg Fin.val h
        simp at this
        omega
      · rfl
    rw [this, map_zero, mul_zero]
  -- `G (B + ∇Ψ_ε (x)) = g (∇φ (x₁, x₂))`, with `|B + ∇Ψ_ε|² = 1 + ε² |∇φ|²`, and `G (B) = Λ`
  set g : Matrix (Fin 4) (Fin 2) ℝ → ℝ := fun M => Λ * √(1 + ε ^ 2 * frobSq M) +
    1 / 4 * √(1 + ε ^ 2 * frobSq M) ^ (-p - 3) * (ε ^ p * F M) with hgdef
  have hGg : ∀ x, intro_corG Λ p F (intro_B + jac Ψ x) = g (jac φ (lift_projX h24 x)) := by
    intro x
    simp only [intro_corG, intro_schattenNorm_two, intro_Xc_add, intro_Yc_add, hjX, hjY,
      intro_Xc_B, add_zero, zero_add, hdet, hgdef]
    rw [intro_frobSq_Xc_Yc, intro_Xc_add, intro_Yc_add, hjX, hjY, intro_Xc_B, zero_add, add_zero,
      hfr, tbt_frobSq_smul, hFh, abs_of_pos hε0, add_comm (ε ^ 2 * _) 1]
  have hGB : intro_corG Λ p F intro_B = Λ := by
    simp only [intro_corG, intro_schattenNorm_two, hdet]
    rw [intro_frobSq_Xc_Yc, intro_Xc_B, hfr, hF0]
    simp [frobSq]
  -- `g ∘ ∇φ` is integrable on the unit square
  have hgc : Continuous g := by
    have hs : Continuous fun M : Matrix (Fin 4) (Fin 2) ℝ => √(1 + ε ^ 2 * frobSq M) :=
      (continuous_const.add (continuous_const.mul intro_continuous_frobSq)).sqrt
    refine (continuous_const.mul hs).add
      ((continuous_const.mul (hs.rpow_const fun M => Or.inl ?_)).mul (continuous_const.mul hFc))
    exact (Real.sqrt_pos.2 (by positivity [tbt_frobSq_nonneg M])).ne'
  have hjm : Measurable fun y => Matrix.of.symm (jac φ y) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun k => ?_
    exact measurable_fderiv_apply_const ℝ _ _
  have hgm : AEStronglyMeasurable (fun y => g (jac φ y)) (volume.restrict (unitCube 2)) :=
    ((show Continuous fun X : Fin 4 → Fin 2 → ℝ => g (Matrix.of X) from hgc).measurable.comp
      hjm).aestronglyMeasurable
  have hgb : ∀ y, |g (jac φ y)| ≤ |Λ| * √(1 + S₀) + V := fun y => by
    have hν1 : 1 ≤ √(1 + ε ^ 2 * frobSq (jac φ y)) :=
      Real.one_le_sqrt.2 (by nlinarith [tbt_frobSq_nonneg (jac φ y)])
    have hν2 : √(1 + ε ^ 2 * frobSq (jac φ y)) ≤ √(1 + S₀) := Real.sqrt_le_sqrt (by
      have := hS y
      have : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1
      nlinarith [tbt_frobSq_nonneg (jac φ y)])
    have hpw : √(1 + ε ^ 2 * frobSq (jac φ y)) ^ (-p - 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hν1 (by linarith)
    have hpw0 : 0 ≤ √(1 + ε ^ 2 * frobSq (jac φ y)) ^ (-p - 3) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hεp : ε ^ p ≤ 1 := Real.rpow_le_one hε0.le hε1 hp0.le
    simp only [hgdef]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left hν2 (abs_nonneg _)
    · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4),
        abs_of_nonneg hpw0, abs_of_nonneg (Real.rpow_nonneg hε0.le p)]
      calc _ ≤ 1 * (1 * V) := mul_le_mul (by linarith)
            (mul_le_mul hεp (hFb y) (abs_nonneg _) zero_le_one)
            (mul_nonneg (Real.rpow_nonneg hε0.le _) (abs_nonneg _)) zero_le_one
        _ = V := by ring
  have hfin : IsFiniteMeasure (volume.restrict (unitCube 2)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_unitCube]; exact ENNReal.one_lt_top⟩
  have hfin' : IsFiniteMeasure (volume.restrict (CalculusOfVariations.unitCube 2)) := hfin
  have hgi : IntegrableOn (fun y => g (jac φ y)) (CalculusOfVariations.unitCube 2) := by
    exact Integrable.of_bound hgm _ (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hgb y)
  -- `∫_{𝕋⁴} [G (B + ∇Ψ_ε) − G (B)] = ∫_{(0,1)²} [g (∇φ) − Λ]`: `Ψ_ε` depends on `x₁, x₂` only
  have hmp := lift_measurePreserving_projX h24
  have hfun : (fun x => intro_corG Λ p F (intro_B + CalculusOfVariations.grad Ψ x)) =
      (fun y => g (jac φ y)) ∘ lift_projX h24 := funext fun x => hGg x
  have hint' : IntegrableOn (fun x => intro_corG Λ p F (intro_B + CalculusOfVariations.grad Ψ x))
      (CalculusOfVariations.unitCube 4) := by
    rw [hfun]
    exact (hmp.integrable_comp hgm).2 hgi
  have hvol : ∀ n, volume.real (CalculusOfVariations.unitCube n) = 1 := fun n => by
    rw [Measure.real, unitCube_eq_cov, volume_unitCube, ENNReal.toReal_one]
  have heq : ∫ x in CalculusOfVariations.unitCube 4,
      (intro_corG Λ p F (intro_B + CalculusOfVariations.grad Ψ x) - intro_corG Λ p F intro_B) =
      ∫ y in CalculusOfVariations.unitCube 2, (g (jac φ y) - Λ) := by
    have hfin4 : IsFiniteMeasure (volume.restrict (CalculusOfVariations.unitCube 4)) :=
      ⟨by rw [Measure.restrict_apply_univ, unitCube_eq_cov, volume_unitCube]
          exact ENNReal.one_lt_top⟩
    rw [integral_sub hint' (integrable_const _), integral_sub hgi (integrable_const _),
      setIntegral_const, setIntegral_const, hvol, hvol, hfun, hGB]
    congr 1
    change ∫ x, g (jac φ (lift_projX h24 x)) ∂(volume.restrict (unitCube 4)) =
      ∫ y, g (jac φ y) ∂(volume.restrict (unitCube 2))
    rw [← integral_map (f := fun y => g (jac φ y)) hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hgm), hmp.map_eq]
  -- the expansion `∫_{𝕋⁴} [G (B + ∇Ψ_ε) − G (B)] = ε^p q (Y₀) ∫ F (∇φ) + O (ε²)`
  have hexp : |(∫ x in CalculusOfVariations.unitCube 4,
      (intro_corG Λ p F (intro_B + CalculusOfVariations.grad Ψ x) - intro_corG Λ p F intro_B)) -
      ε ^ p * (1 / 4 * I)| ≤ ε ^ 2 * E := by
    have hF' : Integrable (fun y => ε ^ p * (1 / 4 * F (jac φ y)))
        (volume.restrict (CalculusOfVariations.unitCube 2)) := (hint.const_mul _).const_mul _
    have hgΛ : Integrable (fun y => g (jac φ y) - Λ)
        (volume.restrict (CalculusOfVariations.unitCube 2)) := hgi.sub (integrable_const _)
    have e : (∫ y in CalculusOfVariations.unitCube 2, (g (jac φ y) - Λ)) - ε ^ p * (1 / 4 * I) =
        ∫ y in CalculusOfVariations.unitCube 2,
          (g (jac φ y) - Λ - ε ^ p * (1 / 4 * F (jac φ y))) := by
      rw [integral_sub hgΛ hF', integral_const_mul, integral_const_mul]
    rw [heq, e, ← Real.norm_eq_abs]
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := CalculusOfVariations.unitCube 2) (C := ε ^ 2 * E)
      (f := fun y => g (jac φ y) - Λ - ε ^ p * (1 / 4 * F (jac φ y)))
      (by rw [unitCube_eq_cov, volume_unitCube]; exact ENNReal.one_lt_top) fun y _ => by
        rw [Real.norm_eq_abs]
        exact intro_witness_est hp0 (by norm_num) (by norm_num) (tbt_frobSq_nonneg (jac φ y))
          (hS y) (hFb y) hε0 hε1
    rwa [hvol, mul_one] at hb
  -- `ε^p q (Y₀) ∫ F (∇φ) + O (ε²) < 0` for small `ε`, since `p < 2`
  have hneg : ε ^ p * (1 / 4 * I) + ε ^ 2 * E < 0 := by
    have h1 : ε ^ (2 : ℝ) = ε ^ p * ε ^ (2 - p) := by
      rw [← Real.rpow_add hε0]; congr 1; ring
    rw [show ε ^ 2 = ε ^ (2 : ℝ) by norm_cast, h1]
    have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε0 p
    have : ε ^ p * (1 / 4 * I) + ε ^ p * ε ^ (2 - p) * E =
        ε ^ p * (ε ^ (2 - p) * E - c) := by rw [hc]; ring
    rw [this]
    exact mul_neg_of_pos_of_neg hεp (by linarith)
  have hlt' : (∫ x in CalculusOfVariations.unitCube 4,
      (intro_corG Λ p F (intro_B + CalculusOfVariations.grad Ψ x) - intro_corG Λ p F intro_B)) <
      0 := by
    linarith [(abs_le.1 hexp).2]
  -- the periodic form of quasiconvexity of `G` at `B`, tested with `Ψ_ε`:
  -- `0 ≤ ∫_{𝕋⁴} [G (B + ∇Ψ_ε) − G (B)]`
  intro hq
  have hper' := (External.Rindler.quasiconvexAtOn_iff_periodic hGI.1 hGI.2 intro_B).1
    ((cov_quasiconvexAtOn_unitCube_iff _ _).2 hq)
  have key := hper' Ψ _ hΨK hΨper hint'
  have hfin4 : IsFiniteMeasure (volume.restrict (CalculusOfVariations.unitCube 4)) :=
    ⟨by rw [Measure.restrict_apply_univ, unitCube_eq_cov, volume_unitCube]
        exact ENNReal.one_lt_top⟩
  rw [integral_sub hint' (integrable_const _), setIntegral_const, hvol, one_smul] at hlt'
  linarith

end Corollary16

/-! ### Rank-one convexity of the integrand of Corollary 1.6

The paper's distributional inequality `(G ∘ A)'' ≥ (Λ − C) r^{−3} dt` along normalized rank-one
lines, in the form of second differences (`f = F ∘ X` is only convex): local midpoint convexity
(`intro_line_midpoint`) and a maximum principle (`intro_convexOn_of_local_midpoint`). -/

section Corollary16RankOne

open Set

/-- Local midpoint convexity (maximum principle): a continuous `φ : ℝ → ℝ` with
`2 φ (t) ≤ φ (t − δ) + φ (t + δ)` for every `t` and every `δ ∈ (0, δ₀]` is convex. -/
theorem intro_convexOn_of_local_midpoint {φ : ℝ → ℝ} (hφ : Continuous φ) {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) (h : ∀ t δ, 0 < δ → δ ≤ δ₀ → 2 * φ t ≤ φ (t - δ) + φ (t + δ)) :
    ConvexOn ℝ univ φ := by
  -- below every chord: `ψ = φ − ℓ ≤ 0` on `[x, z]`
  have key : ∀ x z, x < z → ∀ y ∈ Icc x z,
      φ y ≤ φ x + (φ z - φ x) / (z - x) * (y - x) := by
    intro x z hxz
    set ψ : ℝ → ℝ := fun t => φ t - (φ x + (φ z - φ x) / (z - x) * (t - x)) with hψ
    have hψc : Continuous ψ := hφ.sub (by fun_prop)
    have hψx : ψ x = 0 := by simp [hψ]
    have hψz : ψ z = 0 := by simp only [hψ]; field_simp; ring_nf
    have hψm : ∀ t δ, 0 < δ → δ ≤ δ₀ → 2 * ψ t ≤ ψ (t - δ) + ψ (t + δ) := fun t δ hδ hδ' => by
      have := h t δ hδ hδ'
      simp only [hψ]
      nlinarith
    obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hxz.le)
      hψc.continuousOn
    intro y hy
    suffices hM : ψ t₀ ≤ 0 by
      have := hmax hy
      have h' : ψ y ≤ ψ t₀ := this
      simp only [hψ] at h' hM
      linarith
    by_contra hpos
    rw [not_le] at hpos
    set S := {t ∈ Icc x z | ψ t = ψ t₀} with hSdef
    have hSc : IsClosed S := isClosed_Icc.inter (isClosed_eq hψc continuous_const)
    have hSb : BddAbove S := ⟨z, fun t ht => ht.1.2⟩
    have hSn : S.Nonempty := ⟨t₀, ht₀, rfl⟩
    set t' := sSup S
    have ht' : t' ∈ S := hSc.csSup_mem hSn hSb
    have hxt : x < t' := lt_of_le_of_ne ht'.1.1 fun h' => by
      have := ht'.2; rw [← h', hψx] at this; linarith
    have htz : t' < z := lt_of_le_of_ne ht'.1.2 fun h' => by
      have := ht'.2; rw [h', hψz] at this; linarith
    set δ := min δ₀ (min (z - t') (t' - x)) with hδ
    have hδ0 : 0 < δ := lt_min hδ₀ (lt_min (by linarith) (by linarith))
    have hδ1 : δ ≤ z - t' := (min_le_right _ _).trans (min_le_left _ _)
    have hδ2 : δ ≤ t' - x := (min_le_right _ _).trans (min_le_right _ _)
    have h1 := hψm t' δ hδ0 (min_le_left _ _)
    have h2 : ψ (t' - δ) ≤ ψ t₀ := hmax ⟨by linarith, by linarith⟩
    have h3 : ψ (t' + δ) ≤ ψ t₀ := hmax ⟨by linarith, by linarith⟩
    rw [ht'.2] at h1
    have h4 : ψ (t' + δ) = ψ t₀ := le_antisymm h3 (by linarith)
    have h5 : t' + δ ∈ S := ⟨⟨by linarith, by linarith⟩, h4⟩
    have := le_csSup hSb h5
    linarith
  refine ⟨convex_univ, fun x _ z _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  obtain rfl : a = 1 - b := by linarith
  rcases lt_trichotomy x z with hxz | rfl | hxz
  · have hy : (1 - b) * x + b * z ∈ Icc x z := ⟨by nlinarith, by nlinarith⟩
    have := key x z hxz _ hy
    have e : (1 - b) * x + b * z - x = b * (z - x) := by ring
    rw [e] at this
    have e2 : (φ z - φ x) / (z - x) * (b * (z - x)) = b * (φ z - φ x) := by
      field_simp
    rw [e2] at this
    linarith
  · ring_nf; rfl
  · have hy : (1 - b) * x + b * z ∈ Icc z x := ⟨by nlinarith, by nlinarith⟩
    have := key z x hxz _ hy
    have e : (1 - b) * x + b * z - z = (1 - b) * (x - z) := by ring
    rw [e] at this
    have e2 : (φ x - φ z) / (x - z) * ((1 - b) * (x - z)) = (1 - b) * (φ x - φ z) := by
      field_simp
    rw [e2] at this
    linarith

/-- `g'' ≥ m` on `[t − δ, t + δ]` gives `g (t − δ) + g (t + δ) − 2 g (t) ≥ m δ²` (convexity of
`g − m s² / 2`). -/
theorem intro_second_diff_ge {g g' g'' : ℝ → ℝ} (h1 : ∀ s, HasDerivAt g (g' s) s)
    (h2 : ∀ s, HasDerivAt g' (g'' s) s) {t δ m : ℝ} (hδ : 0 ≤ δ)
    (hm : ∀ s ∈ Icc (t - δ) (t + δ), m ≤ g'' s) :
    m * δ ^ 2 ≤ g (t - δ) + g (t + δ) - 2 * g t := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun s => (h1 s).continuousAt
  have hc : ConvexOn ℝ (Icc (t - δ) (t + δ)) fun s => g s - m / 2 * s ^ 2 := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) (f' := fun s => g' s - m * s)
      (f'' := fun s => g'' s - m) (hgc.sub (by fun_prop)).continuousOn (fun x _ => ?_)
      (fun x _ => ?_) (fun x hx => ?_)
    · have := ((h1 x).sub ((hasDerivAt_pow 2 x).const_mul (m / 2))).hasDerivWithinAt
        (s := interior (Icc (t - δ) (t + δ)))
      convert this using 1
      push_cast; ring
    · have := ((h2 x).sub ((hasDerivAt_id' x).const_mul m)).hasDerivWithinAt
        (s := interior (Icc (t - δ) (t + δ)))
      convert this using 1
      ring
    · rw [interior_Icc] at hx
      have := hm x ⟨hx.1.le, hx.2.le⟩
      linarith
  have := hc.2 (show t - δ ∈ Icc (t - δ) (t + δ) from ⟨le_rfl, by linarith⟩)
    (show t + δ ∈ Icc (t - δ) (t + δ) from ⟨by linarith, le_rfl⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at this
  have e : 1 / 2 * (t - δ) + 1 / 2 * (t + δ) = t := by ring
  rw [e] at this
  nlinarith

/-- `|g'| ≤ M` on `[t − δ, t + δ]` gives `|g (t ± δ) − g (t)| ≤ M δ`. -/
theorem intro_first_diff_le {g g' : ℝ → ℝ} (h1 : ∀ s, HasDerivAt g (g' s) s) {t δ M : ℝ}
    (hδ : 0 ≤ δ) (hM : ∀ s ∈ Icc (t - δ) (t + δ), |g' s| ≤ M) :
    |g (t + δ) - g t| ≤ M * δ ∧ |g (t - δ) - g t| ≤ M * δ := by
  have key : ∀ y ∈ Icc (t - δ) (t + δ), ‖g y - g t‖ ≤ M * ‖y - t‖ := fun y hy =>
    (convex_Icc (t - δ) (t + δ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ => (h1 s).hasDerivWithinAt) (fun s hs => by rw [Real.norm_eq_abs]; exact hM s hs)
      ⟨by linarith, by linarith⟩ hy
  have h1' := key (t + δ) ⟨by linarith, le_rfl⟩
  have h2' := key (t - δ) ⟨le_rfl, by linarith⟩
  simp only [Real.norm_eq_abs, add_sub_cancel_left, sub_sub_cancel_left, abs_neg,
    abs_of_nonneg hδ] at h1' h2'
  exact ⟨h1', h2'⟩

/-- `u (s) = 1 + s²` is comparable on `[t − 1, t + 1]`: `u (t) ≤ 3 u (s)` and `u (s) ≤ 3 u (t)`. -/
theorem intro_u_comp {t s : ℝ} (hs : |s - t| ≤ 1) :
    1 + t ^ 2 ≤ 3 * (1 + s ^ 2) ∧ 1 + s ^ 2 ≤ 3 * (1 + t ^ 2) := by
  have := abs_le.1 hs
  constructor <;> nlinarith [sq_nonneg (s - t), sq_nonneg (s + t), sq_nonneg (2 * s - t),
    sq_nonneg (2 * t - s)]

/-- The powers `P_b (t) = (1 + t²)^b`: derivatives. -/
theorem intro_hasDerivAt_P (b t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t ^ 2) ^ b) (2 * b * t * (1 + t ^ 2) ^ (b - 1)) t := by
  have h0 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  convert h0.rpow_const (p := b) (Or.inl (by positivity)) using 1
  ring

theorem intro_hasDerivAt_P' (b t : ℝ) :
    HasDerivAt (fun t : ℝ => 2 * b * t * (1 + t ^ 2) ^ (b - 1))
      (2 * b * (1 + t ^ 2) ^ (b - 1) + 4 * b * (b - 1) * t ^ 2 * (1 + t ^ 2) ^ (b - 2)) t := by
  have h := ((hasDerivAt_id t).const_mul (2 * b)).mul (intro_hasDerivAt_P (b - 1) t)
  convert h using 1
  · funext s; simp only [Pi.mul_apply, id]
  · simp only [id, mul_one]
    rw [show b - 1 - 1 = b - 2 by ring]
    ring

/-- Comparability of the powers of `u = 1 + s²` on `[t − 1, t + 1]`:
`u (s)^c ≤ 3^{|c|} u (t)^c`. -/
theorem intro_u_pow_comp {t s : ℝ} (hs : |s - t| ≤ 1) (c : ℝ) :
    (1 + s ^ 2) ^ c ≤ 3 ^ |c| * (1 + t ^ 2) ^ c := by
  obtain ⟨h1, h2⟩ := intro_u_comp hs
  have hu : 0 < 1 + t ^ 2 := by positivity
  have hv : 0 < 1 + s ^ 2 := by positivity
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc, ← Real.mul_rpow (by norm_num) hu.le]
    exact Real.rpow_le_rpow hv.le h2 hc
  · rw [abs_of_neg hc]
    have : (1 + t ^ 2) / 3 ≤ 1 + s ^ 2 := by linarith
    calc (1 + s ^ 2) ^ c ≤ ((1 + t ^ 2) / 3) ^ c :=
          Real.rpow_le_rpow_of_nonpos (by positivity) this hc.le
      _ = 3 ^ (-c) * (1 + t ^ 2) ^ c := by
          rw [Real.div_rpow hu.le (by norm_num), Real.rpow_neg (by norm_num)]
          field_simp

/-- The bounds of the derivatives of `P_b = (1 + t²)^b`:
`|P_b'| ≤ 2 |b| u^{b − 1/2}`, `|P_b''| ≤ (2 |b| + 4 |b| |b − 1|) u^{b − 1}`. -/
theorem intro_P_bounds (b t : ℝ) :
    |2 * b * t * (1 + t ^ 2) ^ (b - 1)| ≤ 2 * |b| * (1 + t ^ 2) ^ (b - 1 / 2) ∧
      |2 * b * (1 + t ^ 2) ^ (b - 1) + 4 * b * (b - 1) * t ^ 2 * (1 + t ^ 2) ^ (b - 2)| ≤
        (2 * |b| + 4 * |b| * |b - 1|) * (1 + t ^ 2) ^ (b - 1) := by
  have hu : 0 < 1 + t ^ 2 := by positivity
  have ht : |t| ≤ (1 + t ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have hpos : ∀ c : ℝ, 0 < (1 + t ^ 2) ^ c := fun c => Real.rpow_pos_of_pos hu c
  constructor
  · rw [abs_mul, abs_mul, abs_mul, abs_of_pos (hpos _), abs_two]
    calc 2 * |b| * |t| * (1 + t ^ 2) ^ (b - 1)
        ≤ 2 * |b| * (1 + t ^ 2) ^ (1 / 2 : ℝ) * (1 + t ^ 2) ^ (b - 1) := by gcongr
      _ = 2 * |b| * (1 + t ^ 2) ^ (b - 1 / 2) := by
          rw [mul_assoc, ← Real.rpow_add hu]; ring_nf
  · have ht2 : t ^ 2 * (1 + t ^ 2) ^ (b - 2) ≤ (1 + t ^ 2) ^ (b - 1) := by
      calc t ^ 2 * (1 + t ^ 2) ^ (b - 2) ≤ (1 + t ^ 2) ^ (1 : ℝ) * (1 + t ^ 2) ^ (b - 2) := by
            rw [Real.rpow_one]; gcongr; linarith
        _ = (1 + t ^ 2) ^ (b - 1) := by rw [← Real.rpow_add hu]; ring_nf
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (hpos _), abs_mul, abs_mul, abs_mul,
      abs_of_pos (hpos _), abs_of_nonneg (sq_nonneg t)]
    norm_num
    nlinarith [hpos (b - 1), abs_nonneg b, abs_nonneg (b - 1),
      mul_nonneg (abs_nonneg b) (abs_nonneg (b - 1)), hpos (b - 2)]

/-- The constant of the second-difference estimate of the proof of Corollary 1.6. -/
noncomputable def intro_K (p CF CL Cq : ℝ) : ℝ :=
  let a := (p + 3) / 2
  3 ^ (3 / 2 : ℝ) * (2 * ((3 + 6 * a) * Cq * 3 ^ (a - 1 / 2)) * CL +
    CF * ((2 + 12 * a + 3 * (2 * a + 4 * a * (a + 1))) * Cq * 3 ^ a))

/-- The second-difference estimate of the proof of Corollary 1.6 (TeX lines 2925–2941), in
one variable: on a normalized rank-one line, `φ = Λ r + h f` with `r = u^{1/2}`, `u = 1 + t²`,
`h = q u^{−(p+3)/2}`, `q ≥ 0` quadratic, `f` convex with `|f| ≲ u^{p/2}` and Lipschitz constant
`≲ u^{(p−1)/2}`; then `2 φ (t) ≤ φ (t − δ) + φ (t + δ)` for `δ ∈ (0, 1]` once
`Λ ≥ intro_K`. This is the paper's `(G ∘ A)'' = h f'' + (Λ r^{−3} + 2 h' f' + h'' f) dt ≥ 0` in
the form of second differences (`f` is only convex). -/
theorem intro_line_midpoint {p CF CL Cq c₀ c₁ c₂ Λ : ℝ} (hp : 1 < p) (hCF : 0 ≤ CF)
    (hCL : 0 ≤ CL) (hCq : 0 ≤ Cq) (hc₀ : |c₀| ≤ Cq) (hc₁ : |c₁| ≤ Cq) (hc₂ : |c₂| ≤ Cq)
    (hq : ∀ s, 0 ≤ c₀ + c₁ * s + c₂ * s ^ 2) {f : ℝ → ℝ}
    (hfc : ∀ t δ, 2 * f t ≤ f (t - δ) + f (t + δ))
    (hfb : ∀ t, |f t| ≤ CF * (1 + t ^ 2) ^ (p / 2))
    (hfl : ∀ t s, |s - t| ≤ 1 → |f s - f t| ≤ CL * (1 + t ^ 2) ^ ((p - 1) / 2) * |s - t|)
    (hΛ : intro_K p CF CL Cq ≤ Λ) (t δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * (Λ * (1 + t ^ 2) ^ (1 / 2 : ℝ) + (c₀ + c₁ * t + c₂ * t ^ 2) *
        (1 + t ^ 2) ^ (-((p + 3) / 2)) * f t) ≤
      (Λ * (1 + (t - δ) ^ 2) ^ (1 / 2 : ℝ) + (c₀ + c₁ * (t - δ) + c₂ * (t - δ) ^ 2) *
        (1 + (t - δ) ^ 2) ^ (-((p + 3) / 2)) * f (t - δ)) +
      (Λ * (1 + (t + δ) ^ 2) ^ (1 / 2 : ℝ) + (c₀ + c₁ * (t + δ) + c₂ * (t + δ) ^ 2) *
        (1 + (t + δ) ^ 2) ^ (-((p + 3) / 2)) * f (t + δ)) := by
  set a := (p + 3) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set u := 1 + t ^ 2 with hu
  have hu0 : 0 < u := by positivity
  have hpw : ∀ c : ℝ, 0 < u ^ c := fun c => Real.rpow_pos_of_pos hu0 c
  -- the interval
  have hI : ∀ s ∈ Icc (t - δ) (t + δ), |s - t| ≤ 1 := fun s hs => by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  -- `r = P_{1/2}`: `r'' = u^{−3/2} ≥ 3^{−3/2} u (t)^{−3/2}`
  have hr := intro_second_diff_ge (g := fun s : ℝ => (1 + s ^ 2) ^ (1 / 2 : ℝ))
    (fun s => intro_hasDerivAt_P (1 / 2) s) (fun s => intro_hasDerivAt_P' (1 / 2) s) hδ.le
    (t := t) (m := 3 ^ (-(3 / 2) : ℝ) * u ^ (-(3 / 2) : ℝ)) (fun s hs => by
      have hv : 0 < 1 + s ^ 2 := by positivity
      have e : 2 * (1 / 2 : ℝ) * (1 + s ^ 2) ^ ((1 / 2 : ℝ) - 1) + 4 * (1 / 2) * (1 / 2 - 1) *
          s ^ 2 * (1 + s ^ 2) ^ ((1 / 2 : ℝ) - 2) = (1 + s ^ 2) ^ (-(3 / 2) : ℝ) := by
        have h1 : (1 + s ^ 2) ^ ((1 / 2 : ℝ) - 1) = (1 + s ^ 2) * (1 + s ^ 2) ^ (-(3 / 2) : ℝ) := by
          rw [show (1 / 2 : ℝ) - 1 = 1 + (-(3 / 2)) by norm_num, Real.rpow_add hv, Real.rpow_one]
        rw [h1, show (1 / 2 : ℝ) - 2 = -(3 / 2) by norm_num]
        ring
      rw [e]
      have := intro_u_pow_comp (hI s hs) (-(3 / 2))
      have h3 : (1 + t ^ 2) ^ (-(3 / 2) : ℝ) ≤ 3 ^ (3 / 2 : ℝ) * (1 + s ^ 2) ^ (-(3 / 2) : ℝ) := by
        have := intro_u_pow_comp (t := s) (s := t) (by rw [abs_sub_comm]; exact hI s hs) (-(3 / 2))
        rwa [show |(-(3 / 2) : ℝ)| = 3 / 2 by norm_num] at this
      have h4 : (3 : ℝ) ^ (-(3 / 2) : ℝ) * 3 ^ (3 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      calc 3 ^ (-(3 / 2) : ℝ) * u ^ (-(3 / 2) : ℝ)
          ≤ 3 ^ (-(3 / 2) : ℝ) * (3 ^ (3 / 2 : ℝ) * (1 + s ^ 2) ^ (-(3 / 2) : ℝ)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (1 + s ^ 2) ^ (-(3 / 2) : ℝ) := by rw [← mul_assoc, h4, one_mul])
  -- `h = q P_{−a}` and its derivatives
  set B₂ := 2 * a + 4 * a * (a + 1) with hB₂
  set q : ℝ → ℝ := fun s => c₀ + c₁ * s + c₂ * s ^ 2 with hqdef
  set h : ℝ → ℝ := fun s => q s * (1 + s ^ 2) ^ (-a) with hhdef
  set h' : ℝ → ℝ := fun s => (c₁ + 2 * c₂ * s) * (1 + s ^ 2) ^ (-a) +
    q s * (2 * (-a) * s * (1 + s ^ 2) ^ (-a - 1)) with hh'def
  set h'' : ℝ → ℝ := fun s => 2 * c₂ * (1 + s ^ 2) ^ (-a) +
    2 * ((c₁ + 2 * c₂ * s) * (2 * (-a) * s * (1 + s ^ 2) ^ (-a - 1))) +
    q s * (2 * (-a) * (1 + s ^ 2) ^ (-a - 1) +
      4 * (-a) * (-a - 1) * s ^ 2 * (1 + s ^ 2) ^ (-a - 2)) with hh''def
  have hqd : ∀ s, HasDerivAt q (c₁ + 2 * c₂ * s) s := fun s => by
    have := ((hasDerivAt_id' s).const_mul c₁).add ((hasDerivAt_pow 2 s).const_mul c₂)
    convert (this.const_add c₀) using 1
    · funext x; simp [hqdef]; ring
    · simp; ring
  have hqd' : ∀ s, HasDerivAt (fun s => c₁ + 2 * c₂ * s) (2 * c₂) s := fun s => by
    simpa using ((hasDerivAt_id' s).const_mul (2 * c₂)).const_add c₁
  have hd1 : ∀ s, HasDerivAt h (h' s) s := fun s => by
    have := (hqd s).mul (intro_hasDerivAt_P (-a) s)
    convert this using 1
  have hd2 : ∀ s, HasDerivAt h' (h'' s) s := fun s => by
    have := ((hqd' s).mul (intro_hasDerivAt_P (-a) s)).add ((hqd s).mul (intro_hasDerivAt_P' (-a) s))
    convert this using 1
    simp only [hh''def]
    ring
  -- bounds on `q`, `q'`
  have hqb : ∀ s, |q s| ≤ 3 * Cq * (1 + s ^ 2) := fun s => by
    simp only [hqdef]
    have h1 : |s| ≤ 1 + s ^ 2 := by nlinarith [abs_nonneg s, sq_abs s]
    calc |c₀ + c₁ * s + c₂ * s ^ 2| ≤ |c₀ + c₁ * s| + |c₂ * s ^ 2| := abs_add_le _ _
      _ ≤ |c₀| + |c₁ * s| + |c₂ * s ^ 2| := by linarith [abs_add_le c₀ (c₁ * s)]
      _ = |c₀| + |c₁| * |s| + |c₂| * s ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg s)]
      _ ≤ Cq + Cq * (1 + s ^ 2) + Cq * (1 + s ^ 2) := by
          have e1 := mul_le_mul hc₁ h1 (abs_nonneg _) hCq
          have e2 := mul_le_mul hc₂ (by linarith : s ^ 2 ≤ 1 + s ^ 2) (sq_nonneg _) hCq
          linarith
      _ ≤ 3 * Cq * (1 + s ^ 2) := by nlinarith [sq_nonneg s]
  have hsq : ∀ s : ℝ, |s| ≤ (1 + s ^ 2) ^ (1 / 2 : ℝ) := fun s => by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have hone : ∀ s : ℝ, 1 ≤ (1 + s ^ 2) ^ (1 / 2 : ℝ) := fun s =>
    Real.one_le_rpow (by nlinarith [sq_nonneg s]) (by norm_num)
  have hq'b : ∀ s, |c₁ + 2 * c₂ * s| ≤ 3 * Cq * (1 + s ^ 2) ^ (1 / 2 : ℝ) := fun s => by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_two]
    have := hsq s
    have := hone s
    nlinarith [abs_nonneg c₂, abs_nonneg s]
  -- bounds on `h'`, `h''` at `s`
  have hh'b : ∀ s, |h' s| ≤ (3 + 6 * a) * Cq * (1 + s ^ 2) ^ (1 / 2 - a) := fun s => by
    have hv : 0 < 1 + s ^ 2 := by positivity
    obtain ⟨hP1, -⟩ := intro_P_bounds (-a) s
    rw [abs_neg, abs_of_pos ha0] at hP1
    have e1 : (1 + s ^ 2) ^ (1 / 2 : ℝ) * (1 + s ^ 2) ^ (-a) = (1 + s ^ 2) ^ (1 / 2 - a) := by
      rw [← Real.rpow_add hv]; ring_nf
    have e2 : (1 + s ^ 2) * (1 + s ^ 2) ^ (-a - 1 / 2) = (1 + s ^ 2) ^ (1 / 2 - a) := by
      rw [show (1 / 2 : ℝ) - a = 1 + (-a - 1 / 2) by ring, Real.rpow_add hv, Real.rpow_one]
    simp only [hh'def]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hv _)]
    calc |c₁ + 2 * c₂ * s| * (1 + s ^ 2) ^ (-a) + |q s| * |2 * -a * s * (1 + s ^ 2) ^ (-a - 1)|
        ≤ 3 * Cq * (1 + s ^ 2) ^ (1 / 2 : ℝ) * (1 + s ^ 2) ^ (-a) +
          3 * Cq * (1 + s ^ 2) * (2 * a * (1 + s ^ 2) ^ (-a - 1 / 2)) := by
          gcongr
          · exact hq'b s
          · exact hqb s
      _ = (3 + 6 * a) * Cq * (1 + s ^ 2) ^ (1 / 2 - a) := by
          rw [mul_assoc (3 * Cq), e1]
          rw [show 3 * Cq * (1 + s ^ 2) * (2 * a * (1 + s ^ 2) ^ (-a - 1 / 2)) =
            6 * a * Cq * ((1 + s ^ 2) * (1 + s ^ 2) ^ (-a - 1 / 2)) by ring, e2]
          ring
  have hh''b : ∀ s, |h'' s| ≤ (2 + 12 * a + 3 * B₂) * Cq * (1 + s ^ 2) ^ (-a) := fun s => by
    have hv : 0 < 1 + s ^ 2 := by positivity
    obtain ⟨hP1, hP2⟩ := intro_P_bounds (-a) s
    rw [abs_neg, abs_of_pos ha0] at hP1 hP2
    rw [show -a - 1 = -(a + 1) by ring, abs_neg, abs_of_pos (by linarith : 0 < a + 1),
      show -(a + 1) = -a - 1 by ring] at hP2
    have e1 : (1 + s ^ 2) ^ (1 / 2 : ℝ) * (1 + s ^ 2) ^ (-a - 1 / 2) = (1 + s ^ 2) ^ (-a) := by
      rw [← Real.rpow_add hv]; ring_nf
    have e2 : (1 + s ^ 2) * (1 + s ^ 2) ^ (-a - 1) = (1 + s ^ 2) ^ (-a) := by
      rw [show (-a : ℝ) = 1 + (-a - 1) by ring, Real.rpow_add hv, Real.rpow_one]
      ring_nf
    simp only [hh''def]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    have a1 : |2 * c₂ * (1 + s ^ 2) ^ (-a)| = 2 * |c₂| * (1 + s ^ 2) ^ (-a) := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos (Real.rpow_pos_of_pos hv _)]
    have a2 : ∀ X Y : ℝ, |2 * (X * Y)| = 2 * (|X| * |Y|) := fun X Y => by
      rw [abs_mul, abs_mul, abs_two]
    rw [a1, a2, abs_mul (q s)]
    have hc2 : |c₂| ≤ Cq := hc₂
    calc 2 * |c₂| * (1 + s ^ 2) ^ (-a) + 2 * (|c₁ + 2 * c₂ * s| * |2 * -a * s *
          (1 + s ^ 2) ^ (-a - 1)|) + |q s| * |2 * -a * (1 + s ^ 2) ^ (-a - 1) +
          4 * -a * (-a - 1) * s ^ 2 * (1 + s ^ 2) ^ (-a - 2)|
        ≤ 2 * Cq * (1 + s ^ 2) ^ (-a) + 2 * (3 * Cq * (1 + s ^ 2) ^ (1 / 2 : ℝ) *
          (2 * a * (1 + s ^ 2) ^ (-a - 1 / 2))) + 3 * Cq * (1 + s ^ 2) *
          (B₂ * (1 + s ^ 2) ^ (-a - 1)) := by
          gcongr
          all_goals first
            | exact hq'b s
            | exact hqb s
      _ = (2 + 12 * a + 3 * B₂) * Cq * (1 + s ^ 2) ^ (-a) := by
          rw [show 2 * (3 * Cq * (1 + s ^ 2) ^ (1 / 2 : ℝ) * (2 * a * (1 + s ^ 2) ^ (-a - 1 / 2))) =
            12 * a * Cq * ((1 + s ^ 2) ^ (1 / 2 : ℝ) * (1 + s ^ 2) ^ (-a - 1 / 2)) by ring, e1,
            show 3 * Cq * (1 + s ^ 2) * (B₂ * (1 + s ^ 2) ^ (-a - 1)) =
            3 * B₂ * Cq * ((1 + s ^ 2) * (1 + s ^ 2) ^ (-a - 1)) by ring, e2]
          ring
  -- the constants at `t`
  have ha2 : 1 / 2 < a := by rw [ha]; linarith
  set H₁ := (3 + 6 * a) * Cq * 3 ^ (a - 1 / 2) * u ^ (1 / 2 - a) with hH₁
  set H₂ := (2 + 12 * a + 3 * B₂) * Cq * 3 ^ a * u ^ (-a) with hH₂
  have hH₁0 : 0 ≤ H₁ := by positivity
  have hH₂0 : 0 ≤ H₂ := by positivity
  have hH1 : ∀ s ∈ Icc (t - δ) (t + δ), |h' s| ≤ H₁ := fun s hs => by
    have hc := intro_u_pow_comp (hI s hs) (1 / 2 - a)
    rw [abs_of_neg (by linarith : (1 / 2 : ℝ) - a < 0), neg_sub] at hc
    calc |h' s| ≤ (3 + 6 * a) * Cq * (1 + s ^ 2) ^ (1 / 2 - a) := hh'b s
      _ ≤ (3 + 6 * a) * Cq * (3 ^ (a - 1 / 2) * u ^ (1 / 2 - a)) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = H₁ := by rw [hH₁]; ring
  have hH2 : ∀ s ∈ Icc (t - δ) (t + δ), |h'' s| ≤ H₂ := fun s hs => by
    have hc := intro_u_pow_comp (hI s hs) (-a)
    rw [abs_neg, abs_of_pos ha0] at hc
    calc |h'' s| ≤ (2 + 12 * a + 3 * B₂) * Cq * (1 + s ^ 2) ^ (-a) := hh''b s
      _ ≤ (2 + 12 * a + 3 * B₂) * Cq * (3 ^ a * u ^ (-a)) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = H₂ := by rw [hH₂]; ring
  -- differences of `h`
  obtain ⟨hΔp, hΔm⟩ := intro_first_diff_le hd1 hδ.le hH1
  have hD2lo := intro_second_diff_ge hd1 hd2 hδ.le (t := t) (m := -H₂) fun s hs => by
    have := hH2 s hs; linarith [neg_abs_le (h'' s)]
  have hD2hi := intro_second_diff_ge (g := fun s => -h s) (g' := fun s => -h' s)
    (g'' := fun s => -h'' s) (fun s => (hd1 s).neg) (fun s => (hd2 s).neg) hδ.le (t := t)
    (m := -H₂) fun s hs => by
      have := hH2 s hs; linarith [le_abs_self (h'' s)]
  -- differences of `f`
  have hfp := hfl t (t + δ) (by rw [add_sub_cancel_left, abs_of_pos hδ]; exact hδ1)
  have hfm := hfl t (t - δ) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ]; exact hδ1)
  rw [add_sub_cancel_left, abs_of_pos hδ] at hfp
  rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ] at hfm
  have hf0 := hfb t
  have hfΔ := hfc t δ
  have hht : 0 ≤ h t := mul_nonneg (hq t) (Real.rpow_nonneg hu0.le _)
  -- the products
  set Lf := CL * u ^ ((p - 1) / 2) with hLf
  have hLf0 : 0 ≤ Lf := by positivity
  have hprod : ∀ X Y A B : ℝ, |X| ≤ A → |Y| ≤ B → -(A * B) ≤ X * Y := fun X Y A B hX hY => by
    have := mul_le_mul hX hY (abs_nonneg _) ((abs_nonneg _).trans hX)
    rw [← abs_mul] at this
    linarith [neg_abs_le (X * Y)]
  have p1 := hprod _ _ _ _ hΔp hfp
  have p2 := hprod _ _ _ _ hΔm hfm
  have p3 : -(CF * u ^ (p / 2) * (H₂ * δ ^ 2)) ≤
      f t * (h (t - δ) + h (t + δ) - 2 * h t) := by
    refine hprod _ _ _ _ hf0 ?_
    rw [abs_le]; constructor <;> linarith
  -- the exponents: `u^{1/2 − a} u^{(p−1)/2} = u^{p/2} u^{−a} = u^{−3/2}`
  have e1 : u ^ (1 / 2 - a) * u ^ ((p - 1) / 2) = u ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hu0, ha]; ring_nf
  have e2 : u ^ (p / 2) * u ^ (-a) = u ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hu0, ha]; ring_nf
  have hK0 : 0 ≤ intro_K p CF CL Cq := by unfold intro_K; positivity
  have hΛ0 : 0 ≤ Λ := hK0.trans hΛ
  have hKeq : 3 ^ (-(3 / 2) : ℝ) * intro_K p CF CL Cq * u ^ (-(3 / 2) : ℝ) =
      2 * (H₁ * Lf) + CF * u ^ (p / 2) * H₂ := by
    have h33 : (3 : ℝ) ^ (-(3 / 2) : ℝ) * 3 ^ (3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    rw [hH₁, hLf, hH₂]
    unfold intro_K
    simp only
    rw [← ha, ← hB₂]
    calc 3 ^ (-(3 / 2) : ℝ) * (3 ^ (3 / 2 : ℝ) * (2 * ((3 + 6 * a) * Cq * 3 ^ (a - 1 / 2)) * CL +
          CF * ((2 + 12 * a + 3 * B₂) * Cq * 3 ^ a))) * u ^ (-(3 / 2) : ℝ)
        = (2 * ((3 + 6 * a) * Cq * 3 ^ (a - 1 / 2)) * CL +
          CF * ((2 + 12 * a + 3 * B₂) * Cq * 3 ^ a)) * u ^ (-(3 / 2) : ℝ) := by
          rw [← mul_assoc, h33, one_mul]
      _ = 2 * ((3 + 6 * a) * Cq * 3 ^ (a - 1 / 2)) * CL * u ^ (-(3 / 2) : ℝ) +
          CF * ((2 + 12 * a + 3 * B₂) * Cq * 3 ^ a) * u ^ (-(3 / 2) : ℝ) := by ring
      _ = 2 * ((3 + 6 * a) * Cq * 3 ^ (a - 1 / 2)) * CL * (u ^ (1 / 2 - a) * u ^ ((p - 1) / 2)) +
          CF * ((2 + 12 * a + 3 * B₂) * Cq * 3 ^ a) * (u ^ (p / 2) * u ^ (-a)) := by
          rw [e1, e2]
      _ = _ := by ring
  -- `Λ Δ²r + Δ²(h f) ≥ δ² u^{−3/2} (3^{−3/2} Λ − 3^{−3/2} K) ≥ 0`
  have hid : h (t - δ) * f (t - δ) + h (t + δ) * f (t + δ) - 2 * (h t * f t) =
      h t * (f (t - δ) + f (t + δ) - 2 * f t) + (h (t + δ) - h t) * (f (t + δ) - f t) +
      (h (t - δ) - h t) * (f (t - δ) - f t) + f t * (h (t - δ) + h (t + δ) - 2 * h t) := by ring
  have hr' := mul_le_mul_of_nonneg_left hr hΛ0
  have hhf : 0 ≤ h t * (f (t - δ) + f (t + δ) - 2 * f t) := mul_nonneg hht (by linarith)
  have hm0 : 0 ≤ (3 : ℝ) ^ (-(3 / 2) : ℝ) * u ^ (-(3 / 2) : ℝ) * δ ^ 2 := by positivity
  have hKΛ : 3 ^ (-(3 / 2) : ℝ) * intro_K p CF CL Cq * u ^ (-(3 / 2) : ℝ) * δ ^ 2 ≤
      Λ * (3 ^ (-(3 / 2) : ℝ) * u ^ (-(3 / 2) : ℝ) * δ ^ 2) := by
    have := mul_le_mul_of_nonneg_right hΛ hm0
    calc 3 ^ (-(3 / 2) : ℝ) * intro_K p CF CL Cq * u ^ (-(3 / 2) : ℝ) * δ ^ 2
        = intro_K p CF CL Cq * (3 ^ (-(3 / 2) : ℝ) * u ^ (-(3 / 2) : ℝ) * δ ^ 2) := by ring
      _ ≤ _ := this
  rw [hKeq] at hKΛ
  have q1 : H₁ * δ * (Lf * δ) = H₁ * Lf * δ ^ 2 := by ring
  have q2 : CF * u ^ (p / 2) * (H₂ * δ ^ 2) = CF * u ^ (p / 2) * H₂ * δ ^ 2 := by ring
  have q3 : (2 * (H₁ * Lf) + CF * u ^ (p / 2) * H₂) * δ ^ 2 =
      2 * (H₁ * Lf * δ ^ 2) + CF * u ^ (p / 2) * H₂ * δ ^ 2 := by ring
  have q4 : Λ * (3 ^ (-(3 / 2) : ℝ) * u ^ (-(3 / 2) : ℝ) * δ ^ 2) =
      Λ * (3 ^ (-(3 / 2) : ℝ) * u ^ (-(3 / 2) : ℝ) * δ ^ 2) := rfl
  rw [q1] at p1 p2
  rw [q2] at p3
  rw [q3] at hKΛ
  have hmain : 0 ≤ Λ * ((1 + (t - δ) ^ 2) ^ (1 / 2 : ℝ) + (1 + (t + δ) ^ 2) ^ (1 / 2 : ℝ) -
      2 * u ^ (1 / 2 : ℝ)) +
      (h (t - δ) * f (t - δ) + h (t + δ) * f (t + δ) - 2 * (h t * f t)) := by
    rw [hid]
    linarith
  simp only [hhdef, hqdef] at hmain
  linarith

/-- Lagrange's identity for `Y ∈ ℝ^{4×2}`: `det (Yᵀ Y) = ½ Σ_{i,j} (Y_{i0} Y_{j1} − Y_{j0} Y_{i1})²`. -/
theorem intro_lagrange (Y : Matrix (Fin 4) (Fin 2) ℝ) :
    (Yᵀ * Y).det = 1 / 2 * ∑ i, ∑ j, (Y i 0 * Y j 1 - Y j 0 * Y i 1) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  ring

/-- A `2 × 2` minor of a matrix of rank at most one vanishes. -/
theorem intro_minor_eq_zero {Y : Matrix (Fin 4) (Fin 2) ℝ} (hY : Y.rank ≤ 1) (i j : Fin 4) :
    Y i 0 * Y j 1 - Y j 0 * Y i 1 = 0 := by
  by_contra hne
  have hM : (Y.submatrix ![i, j] id).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa [Matrix.submatrix_apply, mul_comm] using hne
  have hu : IsUnit (Y.submatrix ![i, j] id) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hM)
  have h2 := Matrix.rank_of_isUnit _ hu
  have h3 := Matrix.rank_submatrix_le Y ![i, j] id
  rw [h2, Fintype.card_fin] at h3
  omega

theorem intro_abs_entry_le {d m : ℕ} {A : Matrix (Fin d) (Fin m) ℝ} (hA : frobSq A ≤ 1)
    (i : Fin d) (j : Fin m) : |A i j| ≤ 1 := by
  have h1 := intro_norm_le_sqrt_frobSq (Matrix.of.symm A)
  have h2 : √(frobSq A) ≤ 1 := by rw [Real.sqrt_le_one]; exact hA
  have h3 : ‖A i j‖ ≤ ‖Matrix.of.symm A‖ :=
    (norm_le_pi_norm (Matrix.of.symm A i) j).trans (norm_le_pi_norm (Matrix.of.symm A) i)
  rw [Real.norm_eq_abs] at h3
  simp only [Equiv.apply_symm_apply] at h1
  linarith

/-- On a line `Y₁ + t Y₂` with `rank Y₂ ≤ 1` (entries in `[−1, 1]`), `q (t) = det (Yᵀ Y)` is a
nonnegative quadratic with coefficients bounded by `128`: the minors of `Y₁ + t Y₂` are affine in
`t`, since those of `Y₂` vanish. -/
theorem intro_gram_quadratic {Y₁ Y₂ : Matrix (Fin 4) (Fin 2) ℝ} (h : Y₂.rank ≤ 1)
    (hb1 : ∀ i k, |Y₁ i k| ≤ 1) (hb2 : ∀ i k, |Y₂ i k| ≤ 1) :
    ∃ c₀ c₁ c₂ : ℝ, |c₀| ≤ 128 ∧ |c₁| ≤ 128 ∧ |c₂| ≤ 128 ∧
      ∀ t : ℝ, ((Y₁ + t • Y₂)ᵀ * (Y₁ + t • Y₂)).det = c₀ + c₁ * t + c₂ * t ^ 2 := by
  set α : Fin 4 → Fin 4 → ℝ := fun i j => Y₁ i 0 * Y₁ j 1 - Y₁ j 0 * Y₁ i 1
  set β : Fin 4 → Fin 4 → ℝ := fun i j =>
    Y₁ i 0 * Y₂ j 1 + Y₂ i 0 * Y₁ j 1 - Y₁ j 0 * Y₂ i 1 - Y₂ j 0 * Y₁ i 1
  have hα : ∀ i j, |α i j| ≤ 2 := fun i j => by
    have := abs_sub (Y₁ i 0 * Y₁ j 1) (Y₁ j 0 * Y₁ i 1)
    rw [abs_mul, abs_mul] at this
    have h1 := mul_le_mul (hb1 i 0) (hb1 j 1) (abs_nonneg _) zero_le_one
    have h2 := mul_le_mul (hb1 j 0) (hb1 i 1) (abs_nonneg _) zero_le_one
    simp only [α]; linarith
  have hβ : ∀ i j, |β i j| ≤ 4 := fun i j => by
    have e : ∀ x y z w : ℝ, |x + y - z - w| ≤ |x| + |y| + |z| + |w| := fun x y z w => by
      have := abs_sub (x + y - z) w; have := abs_sub (x + y) z; have := abs_add_le x y
      linarith
    have := e (Y₁ i 0 * Y₂ j 1) (Y₂ i 0 * Y₁ j 1) (Y₁ j 0 * Y₂ i 1) (Y₂ j 0 * Y₁ i 1)
    simp only [abs_mul] at this
    have h1 := mul_le_mul (hb1 i 0) (hb2 j 1) (abs_nonneg _) zero_le_one
    have h2 := mul_le_mul (hb2 i 0) (hb1 j 1) (abs_nonneg _) zero_le_one
    have h3 := mul_le_mul (hb1 j 0) (hb2 i 1) (abs_nonneg _) zero_le_one
    have h4 := mul_le_mul (hb2 j 0) (hb1 i 1) (abs_nonneg _) zero_le_one
    simp only [β]; linarith
  refine ⟨1 / 2 * ∑ i, ∑ j, α i j ^ 2, ∑ i, ∑ j, α i j * β i j, 1 / 2 * ∑ i, ∑ j, β i j ^ 2,
    ?_, ?_, ?_, fun t => ?_⟩
  · have : ∀ i j, |α i j ^ 2| ≤ 4 := fun i j => by
      rw [abs_pow]; nlinarith [hα i j, abs_nonneg (α i j)]
    calc |1 / 2 * ∑ i, ∑ j, α i j ^ 2| ≤ 1 / 2 * ∑ i : Fin 4, ∑ j : Fin 4, (4 : ℝ) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => this i j))
      _ ≤ 128 := by simp; norm_num
  · have : ∀ i j, |α i j * β i j| ≤ 8 := fun i j => by
      rw [abs_mul]; nlinarith [hα i j, hβ i j, abs_nonneg (α i j), abs_nonneg (β i j)]
    calc |∑ i, ∑ j, α i j * β i j| ≤ ∑ i : Fin 4, ∑ j : Fin 4, (8 : ℝ) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => this i j))
      _ ≤ 128 := by simp; norm_num
  · have : ∀ i j, |β i j ^ 2| ≤ 16 := fun i j => by
      rw [abs_pow]; nlinarith [hβ i j, abs_nonneg (β i j)]
    calc |1 / 2 * ∑ i, ∑ j, β i j ^ 2| ≤ 1 / 2 * ∑ i : Fin 4, ∑ j : Fin 4, (16 : ℝ) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => this i j))
      _ ≤ 128 := by simp; norm_num
  · rw [intro_lagrange]
    have hm : ∀ i j, (Y₁ + t • Y₂) i 0 * (Y₁ + t • Y₂) j 1 - (Y₁ + t • Y₂) j 0 * (Y₁ + t • Y₂) i 1 =
        α i j + β i j * t := fun i j => by
      have := intro_minor_eq_zero h i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, α, β]
      linear_combination t ^ 2 * this
    have e : ∀ i j, (α i j + β i j * t) ^ 2 =
        α i j ^ 2 + 2 * (α i j * β i j) * t + β i j ^ 2 * t ^ 2 := fun i j => by ring
    simp only [hm, e, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    ring

/-- Lemma 2.1 and homogeneity (the bound `|f'| ≲ r^{p−1}` of the proof of Corollary 1.6): a
rank-one convex `p`-homogeneous `F` satisfies `|F (X) − F (X')| ≤ L ρ^{p−1} ‖X − X'‖` when
`‖X‖, ‖X'‖ ≤ ρ` (sup norms). -/
theorem intro_lipschitz_of_hom {d m : ℕ} {p : ℝ} {F : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hFh : IsPHomogeneous p F) (hFR : RankOneConvex F) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ρ : ℝ, 0 < ρ → ∀ X X' : Fin d → Fin m → ℝ, ‖X‖ ≤ ρ → ‖X'‖ ≤ ρ →
      |F (Matrix.of X) - F (Matrix.of X')| ≤ L * ρ ^ (p - 1) * ‖X - X'‖ := by
  have hloc := External.Rindler.lemma5_6 ((cov_rankOneConvex_iff F).2 hFR)
  obtain ⟨K, hK⟩ := (hloc.locallyLipschitzOn (s := Metric.closedBall 0 1)).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall 0 1)
  refine ⟨K, K.2, fun ρ hρ X X' hX hX' => ?_⟩
  have hball : ∀ Y : Fin d → Fin m → ℝ, ‖Y‖ ≤ ρ → ρ⁻¹ • Y ∈ Metric.closedBall 0 1 := fun Y hY => by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hρ.le]
    exact (inv_mul_le_one₀ hρ).2 hY
  have h1 := hK.dist_le_mul _ (hball X hX) _ (hball X' hX')
  rw [Real.dist_eq, dist_eq_norm, ← smul_sub, norm_smul, norm_inv,
    Real.norm_of_nonneg hρ.le] at h1
  have e : ∀ Y : Fin d → Fin m → ℝ, F (Matrix.of Y) = ρ ^ p * F (Matrix.of (ρ⁻¹ • Y)) := fun Y => by
    have := hFh ρ (Matrix.of (ρ⁻¹ • Y))
    rw [abs_of_pos hρ] at this
    rw [← this]
    congr 1
    ext i j
    simp [hρ.ne']
  rw [e X, e X', ← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hρ p)]
  calc ρ ^ p * |F (Matrix.of (ρ⁻¹ • X)) - F (Matrix.of (ρ⁻¹ • X'))|
      ≤ ρ ^ p * (K * (ρ⁻¹ * ‖X - X'‖)) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hρ.le p)
    _ = K * ρ ^ (p - 1) * ‖X - X'‖ := by
        rw [Real.rpow_sub_one hρ.ne']; field_simp

theorem intro_frobSq_line (E R : Matrix (Fin 4) (Fin 4) ℝ) (hE : frobSq E = 1) (hR : frobSq R = 1)
    (hER : frobInner E R = 0) (t : ℝ) : frobSq (E + t • R) = 1 + t ^ 2 := by
  have : frobSq (E + t • R) = frobSq E + 2 * t * frobInner E R + t ^ 2 * frobSq R := by
    simp only [frobSq, frobInner, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sq,
      Finset.sum_add_distrib, Finset.mul_sum, mul_pow]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  rw [this, hE, hR, hER]; ring

/-- Proof of Corollary 1.6, rank-one convexity on a normalized line (TeX lines 2925–2941):
for `|E| = |R| = 1`, `E ⊥ R`, `rank R = 1`, `t ↦ G (E + t R)` is convex once `Λ` is large; the
threshold depends only on `F` and `p`. -/
theorem intro_corG_line {p : ℝ} (hp : 1 < p) {F : Matrix (Fin 4) (Fin 2) ℝ → ℝ}
    (hFc : Continuous F) (hFh : IsPHomogeneous p F) (hFR : RankOneConvex F) :
    ∃ Λ₀ : ℝ, ∀ Λ ≥ Λ₀, ∀ E R : Matrix (Fin 4) (Fin 4) ℝ, frobSq E = 1 → frobSq R = 1 →
      frobInner E R = 0 → R.rank = 1 →
        ConvexOn ℝ univ fun t : ℝ => intro_corG Λ p F (E + t • R) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨CF, hCF0, hCF⟩ := intro_abs_le_of_isPHomogeneous hp0 hFc hFh
  obtain ⟨L, hL0, hL⟩ := intro_lipschitz_of_hom hFh hFR
  set CL := L * 3 ^ ((p - 1) / 2) with hCL
  refine ⟨intro_K p CF CL 128, fun Λ hΛ E R hE hR hER hR1 => ?_⟩
  obtain ⟨hGc, -, -⟩ := intro_corG_basic hp hFc hFh
  -- the line in coordinates: `X (t) = X_E + t X_R`, `Y (t) = Y_E + t Y_R`
  have hRle : frobSq R ≤ 1 := hR.le
  have hYr : (intro_Yc R).rank ≤ 1 :=
    hR1 ▸ Matrix.rank_submatrix_le R id (fun j : Fin 2 => (⟨j.val + 2, by omega⟩ : Fin 4))
  have hXr : (intro_Xc R).rank ≤ 1 :=
    hR1 ▸ Matrix.rank_submatrix_le R id (fun j : Fin 2 => (⟨j.val, by omega⟩ : Fin 4))
  obtain ⟨c₀, c₁, c₂, hc₀, hc₁, hc₂, hq⟩ := intro_gram_quadratic hYr
    (fun i k => intro_abs_entry_le ((intro_frobSq_Yc_le E).trans hE.le) i k)
    (fun i k => intro_abs_entry_le ((intro_frobSq_Yc_le R).trans hRle) i k)
  set f : ℝ → ℝ := fun t => F (intro_Xc E + t • intro_Xc R) with hfdef
  have hline : (fun t => intro_corG Λ p F (E + t • R)) = fun t =>
      Λ * (1 + t ^ 2) ^ (1 / 2 : ℝ) + (c₀ + c₁ * t + c₂ * t ^ 2) *
        (1 + t ^ 2) ^ (-((p + 3) / 2)) * f t := by
    funext t
    have hfr := intro_frobSq_line E R hE hR hER t
    simp only [intro_corG, intro_schattenNorm_two, hfr, intro_Yc_add, intro_Yc_smul,
      intro_Xc_add, intro_Xc_smul, hq t, hfdef]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    congr 3
    ring_nf
  rw [hline]
  -- the hypotheses of the second-difference estimate
  have hfconv : ConvexOn ℝ univ f := by
    by_cases h0 : intro_Xc R = 0
    · simp only [hfdef, h0, smul_zero, add_zero]
      exact convexOn_const _ convex_univ
    · have h1 : (intro_Xc R).rank = 1 := by
        have : (intro_Xc R).rank ≠ 0 := fun h => h0 (eq_zero_of_rank_eq_zero h)
        omega
      exact (cov_rankOneConvex_iff F).2 hFR _ _ h1
  have hfc : ∀ t δ, 2 * f t ≤ f (t - δ) + f (t + δ) := fun t δ => by
    have := hfconv.2 (mem_univ (t - δ)) (mem_univ (t + δ)) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at this
    rw [show 1 / 2 * (t - δ) + 1 / 2 * (t + δ) = t by ring] at this
    linarith
  have hnX : ∀ t, ‖Matrix.of.symm (intro_Xc E + t • intro_Xc R)‖ ≤ (1 + t ^ 2) ^ (1 / 2 : ℝ) :=
    fun t => by
      have h1 := intro_norm_le_sqrt_frobSq (Matrix.of.symm (intro_Xc E + t • intro_Xc R))
      simp only [Equiv.apply_symm_apply] at h1
      refine h1.trans ?_
      rw [← Real.sqrt_eq_rpow, ← intro_frobSq_line E R hE hR hER t]
      exact Real.sqrt_le_sqrt (by
        rw [← intro_Xc_smul, ← intro_Xc_add]; exact intro_frobSq_Xc_le _)
  have hfb : ∀ t, |f t| ≤ CF * (1 + t ^ 2) ^ (p / 2) := fun t => by
    have h1 : |f t| ≤ CF * ‖Matrix.of.symm (intro_Xc E + t • intro_Xc R)‖ ^ p := by
      simpa [hfdef] using hCF (Matrix.of.symm (intro_Xc E + t • intro_Xc R))
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCF0)
    calc ‖Matrix.of.symm (intro_Xc E + t • intro_Xc R)‖ ^ p ≤ ((1 + t ^ 2) ^ (1 / 2 : ℝ)) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) (hnX t) hp0.le
      _ = (1 + t ^ 2) ^ (p / 2) := by rw [← Real.rpow_mul (by positivity)]; ring_nf
  have hXR : ‖Matrix.of.symm (intro_Xc R)‖ ≤ 1 := by
    have h1 := intro_norm_le_sqrt_frobSq (Matrix.of.symm (intro_Xc R))
    simp only [Equiv.apply_symm_apply] at h1
    refine h1.trans ?_
    rw [Real.sqrt_le_one]
    exact (intro_frobSq_Xc_le R).trans hRle
  have hfl : ∀ t s, |s - t| ≤ 1 →
      |f s - f t| ≤ CL * (1 + t ^ 2) ^ ((p - 1) / 2) * |s - t| := fun t s hst => by
    have hu0 : 0 < 1 + t ^ 2 := by positivity
    set ρ := (3 * (1 + t ^ 2)) ^ (1 / 2 : ℝ) with hρ
    have hρ0 : 0 < ρ := by positivity
    obtain ⟨h1, h2⟩ := intro_u_comp hst
    have hs : ‖Matrix.of.symm (intro_Xc E + s • intro_Xc R)‖ ≤ ρ :=
      (hnX s).trans (Real.rpow_le_rpow (by positivity) h2 (by norm_num))
    have ht : ‖Matrix.of.symm (intro_Xc E + t • intro_Xc R)‖ ≤ ρ :=
      (hnX t).trans (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num))
    have key := hL ρ hρ0 _ _ hs ht
    simp only [Equiv.apply_symm_apply] at key
    have hd : ‖Matrix.of.symm (intro_Xc E + s • intro_Xc R) -
        Matrix.of.symm (intro_Xc E + t • intro_Xc R)‖ ≤ |s - t| := by
      have : Matrix.of.symm (intro_Xc E + s • intro_Xc R) -
          Matrix.of.symm (intro_Xc E + t • intro_Xc R) = (s - t) • Matrix.of.symm (intro_Xc R) := by
        ext i j; simp; ring
      rw [this, norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) hXR
    have hρp : ρ ^ (p - 1) = 3 ^ ((p - 1) / 2) * (1 + t ^ 2) ^ ((p - 1) / 2) := by
      rw [hρ, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hu0.le]; ring_nf
    calc |f s - f t| ≤ L * ρ ^ (p - 1) * ‖Matrix.of.symm (intro_Xc E + s • intro_Xc R) -
          Matrix.of.symm (intro_Xc E + t • intro_Xc R)‖ := key
      _ ≤ L * ρ ^ (p - 1) * |s - t| :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = CL * (1 + t ^ 2) ^ ((p - 1) / 2) * |s - t| := by rw [hρp, hCL]; ring
  have hqnn : ∀ s, 0 ≤ c₀ + c₁ * s + c₂ * s ^ 2 := fun s => by
    rw [← hq s]; exact (intro_det_gram _).1
  -- local midpoint convexity, hence convexity
  refine intro_convexOn_of_local_midpoint ?_ one_pos fun t δ hδ hδ1 =>
    intro_line_midpoint hp hCF0 (by positivity) (by norm_num) hc₀ hc₁ hc₂ hqnn hfc hfb hfl hΛ
      t δ hδ hδ1
  rw [← hline]
  exact (hGc Λ).comp (continuous_const.add (continuous_id.smul continuous_const))

/-- A convex function composed with an affine map and multiplied by a nonnegative constant is
convex. -/
theorem intro_convexOn_affine {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) {c α β : ℝ} (hc : 0 ≤ c) :
    ConvexOn ℝ univ fun t => c * φ (α * t + β) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have := hφ.2 (mem_univ (α * x + β)) (mem_univ (α * y + β)) ha hb hab
  have e : α * (a • x + b • y) + β = a • (α * x + β) + b • (α * y + β) := by
    simp only [smul_eq_mul]; linear_combination β * hab.symm
  simp only [smul_eq_mul] at this ⊢
  rw [show α * (a * x + b * y) + β = a * (α * x + β) + b * (α * y + β) by
    simpa [smul_eq_mul] using e]
  nlinarith [mul_le_mul_of_nonneg_left this hc]

/-- Proof of Corollary 1.6, rank-one convexity (TeX lines 2925–2941): for `Λ` large, `G` is
rank-one convex. By homogeneity a rank-one line `A + t R` is reduced to a normalized one,
`E + t R̂` with `|E| = |R̂| = 1`, `E ⊥ R̂` (`intro_corG_line`); on rank-one lines through `0`,
`G (t R) = |t| G (R)` with `G ≥ 0`, so `t ↦ G (A + t R)` is `|t + s₀| G (R)`, convex. (The paper's
reason, TeX lines 2942–2943: on such a line `G = Λ |·|`, since `q (Y) = det (YᵀY) = 0` when `Y` has rank
at most one; the proof uses only `1`-homogeneity and `G ≥ 0`, which give convexity without
computing `G (R)`.) -/
theorem intro_corG_rankOneConvex {p : ℝ} (hp : 1 < p) {F : Matrix (Fin 4) (Fin 2) ℝ → ℝ}
    (hFc : Continuous F) (hFh : IsPHomogeneous p F) (hFR : RankOneConvex F) :
    ∃ Λ₀ : ℝ, ∀ Λ ≥ Λ₀, RankOneConvex (intro_corG Λ p F) := by
  obtain ⟨Λ₁, hΛ₁⟩ := intro_corG_line hp hFc hFh hFR
  obtain ⟨-, hGh, Λ₂, hΛ₂⟩ := intro_corG_basic hp hFc hFh
  refine ⟨max Λ₁ Λ₂, fun Λ hΛ => ?_⟩
  have hnn := hΛ₂ Λ ((le_max_right _ _).trans hΛ)
  have hline := hΛ₁ Λ ((le_max_left _ _).trans hΛ)
  have hG1 : ∀ (t : ℝ) A, intro_corG Λ p F (t • A) = |t| * intro_corG Λ p F A := fun t A => by
    rw [hGh Λ t A, Real.rpow_one]
  rw [← cov_rankOneConvex_iff]
  intro A R hR1
  have hR0 : R ≠ 0 := fun h => by rw [h, Matrix.rank_zero] at hR1; exact zero_ne_one hR1
  have hRpos : 0 < frobSq R :=
    lt_of_le_of_ne (tbt_frobSq_nonneg R) fun h => hR0 (tbt_eq_zero_of_frobSq_eq_zero h.symm)
  set s₀ := frobInner A R / frobSq R with hs₀
  set E' := A - s₀ • R with hE'
  have hinner : ∀ (X : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ),
      frobInner (X - c • R) R = frobInner X R - c * frobSq R := fun X c => by
    simp only [frobInner, frobSq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, Finset.mul_sum, sq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hE'R : frobInner E' R = 0 := by
    rw [hE', hinner, hs₀]; field_simp; ring_nf
  have hA : ∀ t : ℝ, A + t • R = E' + (s₀ + t) • R := fun t => by
    rw [hE', add_smul]; abel
  by_cases hE0 : E' = 0
  · -- a line through `0`: `G (A + t R) = |s₀ + t| G (R)`
    have : (fun t : ℝ => intro_corG Λ p F (A + t • R)) =
        fun t => intro_corG Λ p F R * |1 * t + s₀| := funext fun t => by
      rw [hA, hE0, zero_add, hG1]; ring_nf
    rw [this]
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have h1 : |1 * (a * x + b * y) + s₀| ≤ a * |1 * x + s₀| + b * |1 * y + s₀| := by
      have e : 1 * (a * x + b * y) + s₀ = a * (1 * x + s₀) + b * (1 * y + s₀) := by
        linear_combination s₀ * hab.symm
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    nlinarith [mul_le_mul_of_nonneg_left h1 (hnn R)]
  · -- a line off `0`: normalize
    have hE'pos : 0 < frobSq E' :=
      lt_of_le_of_ne (tbt_frobSq_nonneg E') fun h => hE0 (tbt_eq_zero_of_frobSq_eq_zero h.symm)
    set e := √(frobSq E') with he
    set ρ := √(frobSq R) with hρ
    have he0 : 0 < e := Real.sqrt_pos.2 hE'pos
    have hρ0 : 0 < ρ := Real.sqrt_pos.2 hRpos
    have hE1 : frobSq (e⁻¹ • E') = 1 := by
      rw [tbt_frobSq_smul, inv_pow, he, Real.sq_sqrt hE'pos.le, inv_mul_cancel₀ hE'pos.ne']
    have hR1' : frobSq (ρ⁻¹ • R) = 1 := by
      rw [tbt_frobSq_smul, inv_pow, hρ, Real.sq_sqrt hRpos.le, inv_mul_cancel₀ hRpos.ne']
    have hER' : frobInner (e⁻¹ • E') (ρ⁻¹ • R) = 0 := by
      have : frobInner (e⁻¹ • E') (ρ⁻¹ • R) = e⁻¹ * ρ⁻¹ * frobInner E' R := by
        simp only [frobInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [this, hE'R, mul_zero]
    have hrank : (ρ⁻¹ • R).rank = 1 := by
      rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero hρ0.ne')), hR1]
    have hφ := hline _ _ hE1 hR1' hER' hrank
    have : (fun t : ℝ => intro_corG Λ p F (A + t • R)) = fun t => e *
        intro_corG Λ p F (e⁻¹ • E' + ((ρ / e) * t + s₀ * ρ / e) • (ρ⁻¹ • R)) :=
      funext fun t => by
        have hrw : A + t • R = e • (e⁻¹ • E' + ((ρ / e) * t + s₀ * ρ / e) • (ρ⁻¹ • R)) := by
          rw [hA, smul_add, smul_smul, smul_smul, smul_smul, mul_inv_cancel₀ he0.ne', one_smul]
          congr 1
          congr 1
          field_simp
          ring_nf
        rw [hrw, hG1, abs_of_pos he0]
    rw [this]
    exact intro_convexOn_affine (φ := fun t => intro_corG Λ p F (e⁻¹ • E' + t • (ρ⁻¹ • R)))
      hφ he0.le


end Corollary16RankOne

/-- **Theorem 1.2** (`thm:morrey`), by the paper's proof: for `p ∈ (1, ∞)` there is `m₀ (p)` such
that for every `m ≥ m₀ (p)` there is a `p`-homogeneous, rank-one convex and nowhere quasiconvex
integrand `f : ℝ^{2×m} → ℝ`. Conditional on Proposition 2.7 (1) (UMD extrapolation, HNVW), (3)
(`L^p` is UMD, Pisier) and (5) (complex UMD, Yaroslavtsev), through the finiteness of
`UMD_{ℂ,p} (ℓ_q)`. The unconditional statement, `theorem1_2`, is proved by the route of
Remark 4.5 (`theorem1_2_elementary`).

Proof (the paper's, Section 4.4): `q = p + 3 > p + 2`; `C` above `UMD_{ℂ,p} (ℓ_q)`
(`umdEllq_lt_top`), which bounds `C^{rc} (p, q, n)` for every `n` (10) (`equation10`); by (12)
(`lemma4_2`) and the lower bound of `C^{qc}` by the ratio of the test map `u_n`
(`twoByM_ratio_le_qcThreshold`, the limiting argument of Section 4.3), `C < C^{qc} (p, q, n₀)` for
some `n₀`; so `F_{n₀,p,q,C}` is rank-one convex but not
quasiconvex at `0`, and its rank-one convex envelope (Proposition 2.3, `intro_envelope`) is the
integrand for `m₀ = 2 n₀`; for `m ≥ m₀` it is lifted by the projection onto the first `m₀`
columns, witnesses lifting by Lemma 2.2 (`lift_quasiconvexAt_of_comp_trunc`). -/
theorem theorem1_2_umd (hP : PisierLpUMD) (hH : HNVWExtrapolation)
    (hY : YaroslavtsevComplexUMD) {p : ℝ} (hp : 1 < p) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ f : Matrix (Fin 2) (Fin m) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  -- `q > p + 2`, and `C` above `UMD_{ℂ,p} (ℓ_q) ≥ C^{rc} (p, q, n)` (10)
  set q := p + 3 with hqdef
  have hq : 1 < q := by linarith
  have hU := umdEllq_lt_top hP hH hY hp hq
  set C := (umdEllq p q).toReal + 1 with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hUC : umdEllq p q < ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hU.ne]
    exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, by positivity⟩
  -- by (12), `n₀` with `C < C^{qc} (p, q, n₀)`
  obtain ⟨n₀, hn₀⟩ := ((lemma4_2 (q := q) hp (by linarith)).eventually
    (lt_mem_nhds (ENNReal.ofReal_lt_top (r := C)))).exists
  obtain ⟨hcont, hhom, h0, hmono⟩ := intro_blockF (n := n₀) (by linarith : (0 : ℝ) < p)
    (by linarith : (0 : ℝ) < q)
  have hrc : RankOneConvexAt (blockF n₀ p q C) 0 :=
    intro_rankOneConvexAt_of_rcThreshold_lt h0 hmono ((equation10 hp hq n₀).trans_lt hUC)
  have hnq : ¬ QuasiconvexAt (blockF n₀ p q C) 0 :=
    not_quasiconvexAt_of_lt_qcThreshold (F := fun C => blockF n₀ p q C) hC0
      (hn₀.trans_le (twoByM_ratio_le_qcThreshold hp hq n₀))
  -- `f = F_{n₀,p,q,C}^{rc}` (Proposition 2.3), lifted to `ℝ^{2×m}` by the projection
  obtain ⟨-, -, hI, hH', hR, hN⟩ := intro_envelope hp (hcont C) (hhom C) hrc hnq
  refine ⟨2 * n₀, fun m hm => ⟨fun A => (rcEnvelope (blockF n₀ p q C)
    (lift_trunc le_rfl hm A)).toReal, lift_isIntegrand_comp le_rfl hm hI,
    lift_isPHomogeneous_comp le_rfl hm hH', lift_rankOneConvex_comp le_rfl hm hR,
    fun A hA => hN _ (lift_quasiconvexAt_of_comp_trunc le_rfl hm hI hA)⟩⟩

/-- **Theorem 1.2** (`thm:morrey`): for `p ∈ (1, ∞)` there is `m₀ (p)` such that for every
`m ≥ m₀ (p)` there is a `p`-homogeneous, rank-one convex and nowhere quasiconvex integrand
`f : ℝ^{2×m} → ℝ`. Unconditional.

Departure from the paper (approved by the user; reason 2): proved by the route of the paper's
Remark 4.5, `theorem1_2_elementary` (Burkholder's scalar function `u_q` in place of the UMD
constants), because the UMD estimates of the paper's proof (Proposition 2.7 (1), (3), (5)) are out
of reach. The paper's proof is formalized too, as `theorem1_2_umd`, conditional on those three
results. -/
theorem theorem1_2 {p : ℝ} (hp : 1 < p) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ f : Matrix (Fin 2) (Fin m) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f :=
  theorem1_2_elementary hp

/-- **Theorem 1.3**, first assertion (`thm:2x4`): there is a homogeneous quartic polynomial
`P : ℝ^{2×3} → ℝ` which is rank-one convex but nowhere quasiconvex.

Proof (the paper's, after Remark 5.2): `q_{δ, K/δ}` is a rank-one convex homogeneous quartic
(`qDeltaLambda_rankOneConvex`, Lemma 5.1 (2) for `q₃` on `𝓛₃`); the cutoff `u_R` of the witness
of Proposition 5.2 with `R = δ^{−4}` shows that it is not quasiconvex at `0` for `δ` small
(`twoByThree_not_quasiconvexAt_qDeltaLambda`, the cutoff estimates of the proof); homogeneity
makes it nowhere quasiconvex
(`nowhereQuasiconvex_of_not_quasiconvexAt_zero`). -/
theorem theorem1_3_a :
    ∃ P : Matrix (Fin 2) (Fin 3) ℝ → ℝ,
      IsHomogeneousPolynomial 4 P ∧ RankOneConvex P ∧ NowhereQuasiconvex P := by
  -- `q_{δ, K/δ}` is a rank-one convex homogeneous quartic (Lemma 5.1 (2) for `q₃` on `𝓛₃`)
  obtain ⟨K₀, -, hrc⟩ := qDeltaLambda_rankOneConvex
  -- the cutoff of the witness of Proposition 5.2 shows that it is not quasiconvex at `0`
  obtain ⟨δ₀, hδ₀, hnq⟩ := twoByThree_not_quasiconvexAt_qDeltaLambda K₀
  set δ := min (δ₀ / 2) 1 with hδdef
  have hδ : 0 < δ := by positivity
  have hδ₁ : δ < δ₀ := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨hP, hR⟩ := hrc K₀ le_rfl δ hδ (min_le_right _ _)
  -- homogeneity makes it nowhere quasiconvex
  exact ⟨_, hP, hR, nowhereQuasiconvex_of_not_quasiconvexAt_zero (by norm_num : (1 : ℝ) < 4)
    hP.continuous
    (Or.inl (intro_isPHomogeneous_of_isHomogeneousPolynomial hP)) (hnq δ hδ hδ₁)⟩

/-- **Theorem 1.3**, second assertion (`thm:2x4`): for `p` sufficiently close to `4` there is a
`p`-homogeneous integrand `P : ℝ^{2×3} → ℝ` which is rank-one convex but nowhere quasiconvex.
The proof uses Burkholder's inequality (Theorem 2.3, `burkholderInequality_holds`).

Proof: the paper's last step, the rank-one convex envelope (Proposition 2.3, `intro_envelope`),
applied to the integrand `g = f_{r,δ,C} ∘ π + Λ^p |π^⊥ ·|^p` of the proof, rank-one convex but not
quasiconvex at `0` for `p` near `4` (`twoByThree_theorem1_3_b_witness`; the paper's argument for
it has the gap E4 of the inventory, the uniformity in `p` of the constant `Λ` of Lemma 5.1 (1),
which that proof fills with the explicit constants of `lemma5_1_part1_quant`). -/
theorem theorem1_3_b :
    ∃ ε > 0, ∀ p : ℝ, |p - 4| < ε → ∃ f : Matrix (Fin 2) (Fin 3) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  obtain ⟨ε, hε, h⟩ := twoByThree_theorem1_3_b_witness
  refine ⟨min ε 1, by positivity, fun p hp => ?_⟩
  have hp1 : 1 < p := by
    have := abs_lt.1 (hp.trans_le (min_le_right _ _))
    linarith
  obtain ⟨g, hg, hgh, hrc, hnq⟩ := h p (hp.trans_le (min_le_left _ _))
  -- the rank-one convex envelope (Proposition 2.3)
  obtain ⟨-, -, hI, hH, hR, hN⟩ := intro_envelope hp1 hg hgh hrc hnq
  exact ⟨_, hI, hH, hR, hN⟩

/-- **Theorem 1.4** (`thm:main`): for `p ∈ (1, ∞)` there is `d₀ (p)` such that for every
`d ≥ d₀ (p)` there is a conjugation- and transposition-invariant, `p`-homogeneous integrand
`f : ℝ^{d×d} → ℝ` which is rank-one convex but nowhere quasiconvex. Conditional on
Proposition 2.7 (1), (2) (UMD extrapolation, HNVW; the UMD constant of `S_q`, Randrianantoanina),
Proposition 2.8 (decoupling, Cox–Veraar), Proposition 6.3 (non-commutative Khintchine, Pisier–Xu),
Proposition 6.4 (Kahane–Khintchine, HNVW), which the proofs of Propositions 6.2 and 6.5 use
(Proposition 6.5 also uses Burkholder's square function inequality, Theorem 2.3 (2), which is
proved, `burkholderSquareFunction_holds`). For `p = 4` the unconditional `theorem1_4_four`.
The hypothesis `KahaneKhintchine` is the paper's Proposition 6.4, with no bound on its constants:
the proof uses Proposition 6.5 only for `q = 4 < ∞` (`proposition6_5_finite`), which does not
need the hypercontractive bound (`KahaneKhintchineHypercontractive`).

Proof (the paper's, running text after Propositions 6.2 and 6.5, "the same proof as
Theorem 1.2"): with the Schatten exponent `q = 4`, `C^{qc} (S_4^{d×d}, p) ≳ d^{3/4} / min (√(d p), d)
≥ d^{1/4} / √p` (Proposition 6.1) and `C^{rc} (S_4^{d×d}, p) ≲ d^{1/8}` (Proposition 6.2 for `p = 2`,
Proposition 6.5 for general `p`), so for `d ≥ d₀` some `C` lies strictly between them; `f_{p,4,C}`
is rank-one convex but not quasiconvex at `0`, and conjugation and transposition invariant
(`intro_kornF`; `‖U A Uᵀ‖_{S_q} = ‖A‖_{S_q}`, `intro_schattenNorm_conj`); its rank-one convex
envelope (Proposition 2.3 (a)–(c), `intro_envelope`) keeps the invariances (Proposition 2.3 (b)). -/
theorem theorem1_4 (hH : HNVWExtrapolation)
    (hR : RandrianantoaninaSchattenUMD) (hCV : CoxVeraarDecoupling)
    (hPX : PisierXuKhintchine) (hKK : KahaneKhintchine)
    {p : ℝ} (hp : 1 < p) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ f : Matrix (Fin d) (Fin d) ℝ → ℝ,
      IsIntegrand f ∧ IsConjugationInvariant f ∧ IsTranspositionInvariant f ∧
        IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  -- the Schatten exponent `q = 4 ∈ (2, ∞)`
  set q : ENNReal := ENNReal.ofReal 4 with hqdef
  have hq1 : (1 : ENNReal) ≤ q := by
    rw [hqdef, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hq2 : (2 : ENNReal) ≤ q := by
    rw [hqdef, show (2 : ENNReal) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hqr : q.toReal = 4 := by rw [hqdef, ENNReal.toReal_ofReal (by norm_num)]
  -- `C^{qc} ≳ d^{3/4} / min (√(d p), d)` (Proposition 6.1), `C^{rc} ≲ d^{1/8}` (Proposition 6.2
  -- for `p = 2`, Proposition 6.5 for general `p`)
  obtain ⟨c, hc, hqc⟩ := proposition6_1 q hq2
  obtain ⟨Cr, hCr, hrc⟩ : ∃ Cr : ℝ, 0 < Cr ∧ ∀ d : ℕ, 2 ≤ d →
      rcThreshold (kornF d p q) ≤ ENNReal.ofReal (Cr * (d : ℝ) ^ (1 / 4 - 1 / (2 * 4) : ℝ)) := by
    rcases eq_or_ne p 2 with rfl | -
    · exact proposition6_2 hR hCV hPX hKK 4 (by norm_num)
    · exact proposition6_5_finite hH hR hCV hPX hKK 4 (by norm_num) p hp
  set M : ℝ := Cr * √p / c with hMdef
  have hM : 0 ≤ M := by positivity
  refine ⟨⌈M ^ 8⌉₊ + 2, fun d hd => ?_⟩
  have hd2 : 2 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by positivity
  have hd8 : M ^ 8 < d := by
    have := Nat.le_ceil (M ^ 8)
    have : ((⌈M ^ 8⌉₊ + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at this
    linarith
  -- `M < d^{1/8}`
  have hMd : M < (d : ℝ) ^ (1 / 8 : ℝ) := by
    have h := Real.rpow_lt_rpow (by positivity) hd8 (by norm_num : (0 : ℝ) < 1 / 8)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hM, show ((8 : ℕ) : ℝ) * (1 / 8) = 1 by norm_num,
      Real.rpow_one] at h
  set e : ℝ := (d : ℝ) ^ (1 / 8 : ℝ) with hedef
  have he : 0 < e := by positivity
  have hsqd : √(d : ℝ) = e ^ 4 := by
    rw [Real.sqrt_eq_rpow, hedef, ← Real.rpow_natCast, ← Real.rpow_mul hdpos.le]; norm_num
  have hd34 : (d : ℝ) ^ (1 - 1 / q.toReal) = e ^ 6 := by
    rw [hqr, hedef, ← Real.rpow_natCast, ← Real.rpow_mul hdpos.le]; norm_num
  have hd18 : (d : ℝ) ^ (1 / 4 - 1 / (2 * 4) : ℝ) = e := by rw [hedef]; norm_num
  set a : ℝ := Cr * (d : ℝ) ^ (1 / 4 - 1 / (2 * 4) : ℝ) with hadef
  set b : ℝ := c * (d : ℝ) ^ (1 - 1 / q.toReal) / min (√((d : ℝ) * p)) d with hbdef
  have hsp : 0 < √p := Real.sqrt_pos.2 (by linarith)
  have hmin : 0 < min (√((d : ℝ) * p)) d := lt_min (Real.sqrt_pos.2 (by positivity)) hdpos
  have hminle : min (√((d : ℝ) * p)) d ≤ e ^ 4 * √p := by
    rw [← hsqd, ← Real.sqrt_mul hdpos.le]; exact min_le_left _ _
  have ha : 0 < a := by rw [hadef, hd18]; positivity
  have hab : a < b := by
    rw [hadef, hbdef, hd18, hd34, lt_div_iff₀ hmin]
    calc Cr * e * min (√((d : ℝ) * p)) d ≤ Cr * e * (e ^ 4 * √p) :=
          mul_le_mul_of_nonneg_left hminle (by positivity)
      _ = (M * c) * e ^ 5 := by rw [hMdef]; field_simp
      _ < (e * c) * e ^ 5 := by gcongr
      _ = c * e ^ 6 := by ring
  -- `C` strictly between `C^{rc}` and `C^{qc}`
  set C := (a + b) / 2 with hCdef
  have hrcC : rcThreshold (kornF d p q) < ENNReal.ofReal C :=
    (hrc d hd2).trans_lt (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, by linarith⟩)
  have hqcC : ENNReal.ofReal C < qcThreshold (kornF d p q) :=
    (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, by linarith⟩).trans_le (hqc d hd2 p hp.le)
  obtain ⟨hcont, hhom, h0, hmono, hconj, htr⟩ := intro_kornF (d := d) (by linarith : (0 : ℝ) < p)
    hq1
  have hrc0 : RankOneConvexAt (kornF d p q C) 0 :=
    intro_rankOneConvexAt_of_rcThreshold_lt h0 hmono hrcC
  have hnq : ¬ QuasiconvexAt (kornF d p q C) 0 :=
    not_quasiconvexAt_of_lt_qcThreshold (by linarith) hqcC
  -- the envelope (Proposition 2.3), with its invariances (Proposition 2.3 (b))
  obtain ⟨-, -, hI, hH', hR', hN⟩ := intro_envelope hp (hcont C) (hhom C) hrc0 hnq
  obtain ⟨hb1, hb2⟩ := proposition2_3_b hp (hcont C) (Or.inl (hhom C))
  exact ⟨_, hI, fun U hU A => by simp only [(hb1 (hconj C)).1 U hU A],
    fun A => by simp only [hb2 (htr C) A], hH', hR', hN⟩

/-- **Theorem 1.5** (`thm:lowdim`): for every `p ∈ (1, ∞) ∖ {2}` there is a `p`-homogeneous
integrand `f : ℝ^{4×2} → ℝ` which is rank-one convex but nowhere quasiconvex. Unconditional: the
results it rests on through Theorem 7.1 are proved, transference for homogeneous multipliers
(HNVW I, Corollary 5.7.6, through Proposition 7.2), Dragičević's lower bound
`‖𝓑²‖_{L^p} > p* − 1` and Burkholder's inequality (Theorem 2.3, through Proposition 7.1).

Proof (the paper's, running text after Theorem 7.1): the integrand of Theorem 7.1 is continuous
and `p`-homogeneous, rank-one convex but not quasiconvex at `0`; its rank-one convex envelope
(Proposition 2.3, `intro_envelope`) is the integrand. -/
theorem theorem1_5 {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) :
    ∃ f : Matrix (Fin 4) (Fin 2) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  -- Theorem 7.1: `C (p)^p ‖P_p (A)‖_{S₂}^p − ‖Q_p (A)‖^p` is rank-one convex, not quasiconvex, at `0`
  obtain ⟨P, Q, C, -, hrc, hnq⟩ := theorem7_1 hp hp2
  have hp0 : (0 : ℝ) < p := by linarith
  have h2 : (1 : ENNReal) ≤ 2 := one_le_two
  obtain ⟨hh, -, -⟩ := intro_family (N₁ := fun A => schattenNorm 2 (P A))
    (N₂ := fun A => √(∑ i, Q A i ^ 2)) hp0 (fun A => schattenNorm_nonneg 2 _)
    (fun A => Real.sqrt_nonneg _)
    (fun t A => by simp only [map_smul, schattenNorm_smul h2])
    (fun t A => by
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs])
  have hcP : Continuous fun A => schattenNorm 2 (P A) :=
    (intro_continuous_schattenNorm h2).comp (LinearMap.continuous_of_finiteDimensional P)
  have hcQ : Continuous fun A => √(∑ i, Q A i ^ 2) :=
    (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp
      (LinearMap.continuous_of_finiteDimensional Q)).pow 2).sqrt
  have hcont : Continuous fun A => C ^ p * schattenNorm 2 (P A) ^ p - √(∑ i, Q A i ^ 2) ^ p :=
    continuous_const.mul (hcP.rpow_const fun _ => Or.inr hp0.le) |>.sub
      (hcQ.rpow_const fun _ => Or.inr hp0.le)
  -- the rank-one convex envelope (Proposition 2.3)
  obtain ⟨-, -, hI, hH, hR, hN⟩ := intro_envelope hp hcont (hh C) hrc hnq
  exact ⟨_, hI, hH, hR, hN⟩

/-- **Corollary 1.6** (`cor:1-hom`): there is a `1`-homogeneous rank-one convex integrand
`f : ℝ^{4×4} → [0, ∞)` which is not quasiconvex at a matrix of rank `2`. Unconditional, as
Theorem 1.5, which its proof uses (at some `p ∈ (1, 2)`).

Proof (the paper's, end of Section 7): `p = 3/2`, `F` from Theorem 1.5 (continuous by Lemma 2.1),
`G (A) = Λ ‖A‖_{S₂} + q (Y) ‖A‖_{S₂}^{−p−3} F (X)` (`intro_corG`): continuous, `1`-homogeneous and
nonnegative for `Λ` large (`intro_corG_basic`), rank-one convex for `Λ` large
(`intro_corG_rankOneConvex`), not quasiconvex at `B = (0, Y₀)` with `|B| = 1` and `rank Y₀ = 2`
(`intro_corG_not_quasiconvexAt`, `intro_rank_B`): for a smooth periodic `φ : 𝕋² → ℝ⁴` with
`∫_{𝕋²} F (∇φ) < 0` and `Ψ_ε (x, y) = ε φ (x)`,
`∫_{𝕋⁴} [G (B + ∇Ψ_ε) − G (B)] = ε^p q (Y₀) ∫_{𝕋²} F (∇φ) + O (ε²) < 0` for small `ε > 0`.

Gap filled (TeX lines 2946–2947): the paper takes a smooth periodic `φ` with `∫_{𝕋²} F (∇φ) < 0`
without saying where it comes from. The periodic form of quasiconvexity (Lemma 2.2) gives a
Lipschitz periodic one; its mollifications are smooth, Lipschitz and periodic, and by dominated
convergence one of them still has `∫_{𝕋²} F (∇φ) < 0` (`intro_smooth_periodic_witness`).

Departure from the paper (rank-one convexity): the paper bounds the distributional second
derivative, `(G ∘ A)'' = h f'' + (Λ r^{−3} + 2 h' f' + h'' f) dt ≥ (Λ − C) r^{−3} dt`, with `f = F ∘ X`
only convex. Mathlib has no distributional derivatives of convex functions, nor the criterion
"distributional second derivative `≥ 0` implies convex" (reason 2: mathematics that Lean lacks);
the formalization proves the same inequality for second differences,
`Δ²_δ (G ∘ A) ≥ δ² (Λ − C) r^{−3} / 3^{3/2}` for `δ ≤ 1` (`intro_line_midpoint`, from the same
bounds `|h^{(j)}| ≲ r^{−p−1−j}`, `|f| + r |f'| ≲ r^p`), and concludes by the maximum principle for
locally midpoint convex continuous functions (`intro_convexOn_of_local_midpoint`). -/
theorem corollary1_6 :
    ∃ f : Matrix (Fin 4) (Fin 4) ℝ → ℝ, IsIntegrand f ∧ (∀ A, 0 ≤ f A) ∧ IsPHomogeneous 1 f ∧
      RankOneConvex f ∧ ∃ A : Matrix (Fin 4) (Fin 4) ℝ, A.rank = 2 ∧ ¬ QuasiconvexAt f A := by
  -- `p = 3/2 ∈ (1, 2)` and `F` from Theorem 1.5; `F` is continuous by Lemma 2.1
  have hp : (1 : ℝ) < 3 / 2 := by norm_num
  have hp2 : (3 / 2 : ℝ) < 2 := by norm_num
  obtain ⟨F, -, hFh, hFR, hFN⟩ := theorem1_5 hp (by norm_num)
  have hFc : Continuous F :=
    (External.Rindler.lemma5_6 ((cov_rankOneConvex_iff F).2 hFR)).continuous
  -- `G` for `Λ` large
  obtain ⟨hGc, hGh, Λ₁, hΛ₁⟩ := intro_corG_basic hp hFc hFh
  obtain ⟨Λ₂, hΛ₂⟩ := intro_corG_rankOneConvex hp hFc hFh hFR
  set Λ := max Λ₁ Λ₂
  exact ⟨intro_corG Λ (3 / 2) F, isIntegrand_of_continuous (hGc Λ),
    hΛ₁ Λ (le_max_left _ _), hGh Λ, hΛ₂ Λ (le_max_right _ _), intro_B, intro_rank_B,
    intro_corG_not_quasiconvexAt hp hp2 hFc hFh (hFN 0) Λ⟩

/-- **The 2 × 2 landscape** (`cs-landscape`, lines 251–254): "this result [Theorem 1.3] complements
Šverák's to prove that the only nontrivial instance in which Morrey's problem may have a positive
answer is `2 × 2`": for `d, m ≥ 2` with `(d, m) ≠ (2, 2)` there is a rank-one convex integrand on
`ℝ^{d×m}` that is not quasiconvex. Unconditional.

Proof: otherwise Morrey's problem has a positive answer in `d × m`, hence in `3 × 2` if `d ≥ 3`
(`morreyPositive_mono`), contradicting Šverák's example (`sverak_example`), and in `2 × 3` if
`d = 2`, `m ≥ 3`, contradicting the quartic of Theorem 1.3 (a polynomial is an integrand, and
nowhere quasiconvex implies not quasiconvex). -/
theorem morrey_landscape {d m : ℕ} (hd : 2 ≤ d)
    (hm : 2 ≤ m) (h22 : ¬ (d = 2 ∧ m = 2)) :
    ∃ f : Matrix (Fin d) (Fin m) ℝ → ℝ, IsIntegrand f ∧ RankOneConvex f ∧ ¬ Quasiconvex f := by
  by_contra hne
  have hpos : MorreyPositive d m := fun f hf hR => by
    by_contra hq
    exact hne ⟨f, hf, hR, hq⟩
  rcases Nat.lt_or_ge 2 d with h3 | h2
  · -- `d ≥ 3`: Šverák's example in `3 × 2`
    obtain ⟨ε₀, hε₀, hS⟩ := sverak_example
    obtain ⟨k, -, hR, hq⟩ := hS ε₀ hε₀ le_rfl
    exact hq (morreyPositive_mono h3 hm hpos _
      (isIntegrand_of_continuous (Sverak.thm_sverakF_continuous ε₀ k)) hR 0)
  · -- `d = 2`, `m ≥ 3`: the quartic of Theorem 1.3 in `2 × 3`
    have hm3 : 3 ≤ m := by omega
    obtain ⟨P, hP, hR, hnq⟩ := theorem1_3_a
    exact hnq 0 (morreyPositive_mono hd hm3 hpos P
      (isIntegrand_of_continuous hP.continuous) hR 0)

/-- **The homogeneous landscape** (`cs-hom-landscape`, lines 254–256 and 2137–2142): with
Corollary 5.3, the homogeneous Morrey problem (at `p = 4`) has a negative answer in every
nontrivial dimension except possibly `2 × 2`: for `d, m ≥ 2` with `(d, m) ≠ (2, 2)` there is a
`4`-homogeneous rank-one convex integrand on `ℝ^{d×m}` that is not quasiconvex at `0`.
Unconditional.

Proof: as for `morrey_landscape`, with `homMorreyPositive_mono`, the quartic of Corollary 5.3 in
`3 × 2` (for `d ≥ 3`) and that of Theorem 1.3 in `2 × 3` (for `d = 2`, `m ≥ 3`); a homogeneous
quartic is `4`-homogeneous. -/
theorem homMorrey_landscape {d m : ℕ}
    (hd : 2 ≤ d) (hm : 2 ≤ m) (h22 : ¬ (d = 2 ∧ m = 2)) :
    ∃ f : Matrix (Fin d) (Fin m) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous 4 f ∧ RankOneConvex f ∧ ¬ QuasiconvexAt f 0 := by
  by_contra hne
  have hpos : HomMorreyPositive 4 d m := fun f hf hh hR => by
    by_contra hq
    exact hne ⟨f, hf, hh, hR, hq⟩
  have h14 : (1 : ℝ) < 4 := by norm_num
  rcases Nat.lt_or_ge 2 d with h3 | h2
  · -- `d ≥ 3`: the transposed quartic of Corollary 5.3 in `3 × 2`
    obtain ⟨K₀, hK₀⟩ := corollary5_3
    obtain ⟨δ₀, hδ₀, hδ⟩ := hK₀ K₀ le_rfl
    obtain ⟨hP, hR, hnq⟩ := hδ (δ₀ / 2) (by positivity) (by linarith)
    exact hnq 0 (homMorreyPositive_mono h14 h3 hm hpos _
      (isIntegrand_of_continuous hP.continuous)
      (intro_isPHomogeneous_of_isHomogeneousPolynomial hP) hR)
  · -- `d = 2`, `m ≥ 3`: the quartic of Theorem 1.3 in `2 × 3`
    have hm3 : 3 ≤ m := by omega
    obtain ⟨P, hP, hR, hnq⟩ := theorem1_3_a
    exact hnq 0 (homMorreyPositive_mono h14 hd hm3 hpos P
      (isIntegrand_of_continuous hP.continuous)
      (intro_isPHomogeneous_of_isHomogeneousPolynomial hP) hR)

end Cassese
