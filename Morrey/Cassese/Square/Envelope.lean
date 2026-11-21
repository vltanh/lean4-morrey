module

public import Morrey.Cassese.Toolkit
public import Morrey.Cassese.Bridges
public import Morrey.Cassese.Square.Hessian
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The rank-one convex envelope and Hessian quasiconvexity (proof of Corollary 6.1)

Two ingredients of the proof of Corollary 6.1 (`cor:symm`, TeX lines 2489–2520):

* `square_env_rc`: for a continuous `p`-homogeneous `f` that is rank-one convex at `0`, the
  paper's `f^{rc}` (Definition 2.3, `rcEnvelope`) is finite, continuous, an integrand, convex
  along every rank-one line, `≤ f`, `0` at `0` and `p`-homogeneous. It is the supremum of the
  rank-one convex minorants of `f`; one of them exists (rank-one convexity at `0`), so the
  supremum is finite, and it is convex along rank-one lines as a supremum of such functions; it
  is continuous by Lemma 2.1 (`External.Rindler.lemma5_6`) and `p`-homogeneous by
  Proposition 2.3 (a) (`proposition2_3_a`).
* `square_not_hessianQuasiconvexAt_of_zero`: the paper's "hence is nowhere Hessian-quasiconvex",
  for a continuous integrand on `ℝ^{n×n}` that is `p`-homogeneous on symmetric matrices: the
  Hessian analogue of `quasiconvexAt_zero_of_quasiconvexAt` (scaling `φ ↦ λ φ` and dominated
  convergence).

Helpers have the prefix `square_env_`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Matrix

namespace Cassese

/-! ### The rank-one convex envelope -/

section Env

variable {d : ℕ}

theorem square_env_le_f (f : Matrix (Fin d) (Fin d) ℝ → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    rcEnvelope f A ≤ (f A : EReal) :=
  iSup₂_le fun _ hh => EReal.coe_le_coe_iff.2 (hh.2.2 A)

theorem square_env_le {f h : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hh : IsIntegrand h ∧ RankOneConvex h ∧ ∀ B, h B ≤ f B) (A : Matrix (Fin d) (Fin d) ℝ) :
    (h A : EReal) ≤ rcEnvelope f A :=
  le_iSup₂ (f := fun (h : Matrix (Fin d) (Fin d) ℝ → ℝ)
    (_ : IsIntegrand h ∧ RankOneConvex h ∧ ∀ B, h B ≤ f B) => (h A : EReal)) h hh

/-- With one rank-one convex minorant, `f^{rc}` is finite. -/
theorem square_env_coe_toReal {f g : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hg : IsIntegrand g ∧ RankOneConvex g ∧ ∀ B, g B ≤ f B) (A : Matrix (Fin d) (Fin d) ℝ) :
    (((rcEnvelope f A).toReal : ℝ) : EReal) = rcEnvelope f A := by
  have h1 : rcEnvelope f A ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (square_env_le_f f A)
  have h2 : rcEnvelope f A ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (square_env_le hg A)
  exact EReal.coe_toReal h1 h2

/-- Every rank-one convex minorant is `≤ (f^{rc}).toReal`. -/
theorem square_env_ge {f g h : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hg : IsIntegrand g ∧ RankOneConvex g ∧ ∀ B, g B ≤ f B)
    (hh : IsIntegrand h ∧ RankOneConvex h ∧ ∀ B, h B ≤ f B) (A : Matrix (Fin d) (Fin d) ℝ) :
    h A ≤ (rcEnvelope f A).toReal := by
  have := square_env_le hh A
  rw [← square_env_coe_toReal hg A] at this
  exact_mod_cast this

/-- `(f^{rc}).toReal ≤ c` once every rank-one convex minorant is `≤ c`. -/
theorem square_env_le_of {f g : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hg : IsIntegrand g ∧ RankOneConvex g ∧ ∀ B, g B ≤ f B) {A : Matrix (Fin d) (Fin d) ℝ}
    {c : ℝ} (hc : ∀ h : Matrix (Fin d) (Fin d) ℝ → ℝ,
      (IsIntegrand h ∧ RankOneConvex h ∧ ∀ B, h B ≤ f B) → h A ≤ c) :
    (rcEnvelope f A).toReal ≤ c := by
  have : rcEnvelope f A ≤ (c : EReal) := iSup₂_le fun h hh => EReal.coe_le_coe_iff.2 (hc h hh)
  rw [← square_env_coe_toReal hg A] at this
  exact_mod_cast this

theorem square_env_eq_zero_of_rank {R : Matrix (Fin d) (Fin d) ℝ} (h : R.rank = 0) : R = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply] using this

/-- **The rank-one convex envelope** `f^{rc}` (Definition 2.3) of a continuous `p`-homogeneous
`f` that is rank-one convex at `0`: it is finite, continuous, an integrand, convex along every
rank-one line, `≤ f`, `0` at `0`, and `p`-homogeneous.

Proof. `f^{rc}` is the supremum of the rank-one convex minorants `h ≤ f`; the minorant `g` given
by rank-one convexity at `0` makes it finite (`g ≤ f^{rc} ≤ f`). Along a rank-one line each `h`
is convex, so their supremum is (`h ≤ a h + b h ≤ a f^{rc} + b f^{rc}`). It is therefore rank-one
convex, hence continuous by Lemma 2.1 (`External.Rindler.lemma5_6`), hence an integrand. At `0`,
`f (0) = g (0) ≤ f^{rc} (0) ≤ f (0)` and `f (0) = 0` by homogeneity. Homogeneity is
Proposition 2.3 (a) (`proposition2_3_a`). -/
theorem square_env_rc {d : ℕ} {p : ℝ} (hp : 1 < p) {f : Matrix (Fin d) (Fin d) ℝ → ℝ}
    (hf : Continuous f) (hhom : IsPHomogeneous p f) (hrc : RankOneConvexAt f 0) :
    (∀ A, (((rcEnvelope f A).toReal : ℝ) : EReal) = rcEnvelope f A) ∧
      Continuous (fun A => (rcEnvelope f A).toReal) ∧
      IsIntegrand (fun A => (rcEnvelope f A).toReal) ∧
      (∀ A R : Matrix (Fin d) (Fin d) ℝ, R.rank ≤ 1 →
        ConvexOn ℝ Set.univ fun t : ℝ => (rcEnvelope f (A + t • R)).toReal) ∧
      (∀ B, (rcEnvelope f B).toReal ≤ f B) ∧ (rcEnvelope f 0).toReal = 0 ∧
      IsPHomogeneous p (fun A => (rcEnvelope f A).toReal) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨g, hgI, hgR, hgf, hg0⟩ := hrc
  have hg : IsIntegrand g ∧ RankOneConvex g ∧ ∀ B, g B ≤ f B := ⟨hgI, hgR, hgf⟩
  set G : Matrix (Fin d) (Fin d) ℝ → ℝ := fun A => (rcEnvelope f A).toReal with hGdef
  -- convexity along rank-one lines
  have hline : ∀ A R : Matrix (Fin d) (Fin d) ℝ, R.rank ≤ 1 →
      ConvexOn ℝ Set.univ fun t : ℝ => G (A + t • R) := by
    intro A R hR
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hR with h0 | h1
    · rw [square_env_eq_zero_of_rank h0]
      simp only [smul_zero, add_zero]
      exact convexOn_const _ convex_univ
    · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => square_env_le_of hg fun h hh => ?_⟩
      have hconv := (cov_rankOneConvex_iff h).2 hh.2.1 A R h1
      have key := hconv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
      simp only [smul_eq_mul] at key ⊢
      calc h (A + (a * x + b * y) • R) ≤ a * h (A + x • R) + b * h (A + y • R) := key
        _ ≤ a * G (A + x • R) + b * G (A + y • R) :=
            add_le_add (mul_le_mul_of_nonneg_left (square_env_ge hg hh _) ha)
              (mul_le_mul_of_nonneg_left (square_env_ge hg hh _) hb)
  -- continuity (Lemma 2.1)
  have hcov : CalculusOfVariations.RankOneConvex G := fun A R hR => hline A R hR.le
  have hGc : Continuous G := (External.Rindler.lemma5_6 hcov).continuous
  -- `G` is an integrand
  have hGI : IsIntegrand G := by
    refine ⟨hGc.lowerSemicontinuous, fun A => ⟨G ⁻¹' Set.Ioo (G A - 1) (G A + 1),
      hGc.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), |G A| + 1,
      fun B hB => ?_⟩⟩
    obtain ⟨h1, h2⟩ := hB
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (G A), le_abs_self (G A)]
  -- `G ≤ f`
  have hGf : ∀ B, G B ≤ f B := fun B => square_env_le_of hg fun h hh => hh.2.2 B
  -- `f (0) = 0` and `G (0) = 0`
  have hf0 : f 0 = 0 := by
    have h := hhom 2 0
    rw [smul_zero, abs_of_pos two_pos] at h
    have h2 : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow (by norm_num) hp0
    have : (2 ^ p - 1) * f 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · linarith
    · exact h3
  have hG0 : G 0 = 0 := by
    refine le_antisymm ((hGf 0).trans hf0.le) ?_
    have := square_env_ge hg hg 0
    rw [hg0, hf0] at this
    exact this
  -- homogeneity (Proposition 2.3 (a))
  have hGhom : IsPHomogeneous p G := by
    rcases (proposition2_3_a hp hf (Or.inl hhom)).1 with hbot | ⟨_, h1, _⟩
    · exact absurd (hbot 0) (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (square_env_le hg 0))
    · exact h1 hhom
  exact ⟨square_env_coe_toReal hg, hGc, hGI, hline, hGf, hG0, hGhom⟩

end Env

/-! ### Failure of Hessian quasiconvexity at `0` propagates -/

section Hess

variable {n : ℕ}

/-- The Hessian of a `C²` function is symmetric. -/
theorem square_env_hessian_isSymm {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (x : Fin n → ℝ) :
    (hessian φ x).IsSymm := by
  have hs : IsSymmSndFDerivAt ℝ φ x := hφ.contDiffAt.isSymmSndFDerivAt (by simp)
  ext i j
  rw [Matrix.transpose_apply, square_hess_hessian_apply hφ, square_hess_hessian_apply hφ,
    iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact hs _ _

/-- `D² (λ φ) = λ D²φ`. -/
theorem square_env_hessian_const_mul {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (l : ℝ)
    (x : Fin n → ℝ) : hessian (fun y => l * φ y) x = l • hessian φ x := by
  have hψ : ContDiff ℝ 2 fun y => l * φ y := contDiff_const.mul hφ
  ext i j
  rw [square_hess_hessian_apply hψ, Matrix.smul_apply, square_hess_hessian_apply hφ]
  have e : (fun y => l * φ y) = fun y => l • φ y := rfl
  rw [e, iteratedFDeriv_const_smul_apply' hφ.contDiffAt]
  rfl

/-- **Failure of Hessian quasiconvexity at `0` propagates** (proof of Corollary 6.1, "and hence
is nowhere Hessian-quasiconvex"): for a continuous `F` on `ℝ^{n×n}` with `F (t H) = |t|^p F (H)`
for symmetric `H` (`p > 0`), if `F` is not Hessian quasiconvex at `0` it is not Hessian
quasiconvex at any symmetric `A`.

Proof: the Hessian analogue of `quasiconvexAt_zero_of_quasiconvexAt`. `F (0) = 0` by
homogeneity. For a test map `φ` and `λ > 0`, Hessian quasiconvexity at `A` tested with `λ φ`
gives `F (A) ≤ ∫ F (A + λ D²φ) = λ^p ∫ F (λ⁻¹ A + D²φ)` (`A + λ D²φ = λ (λ⁻¹ A + D²φ)` is
symmetric, `square_env_hessian_isSymm`); as `λ → ∞`, `λ^{−p} F (A) → 0` and
`∫ F (λ⁻¹ A + D²φ) → ∫ F (D²φ)` by dominated convergence (`D²φ` is bounded: it is continuous with
compact support), so `∫ F (D²φ) ≥ 0 = F (0)`: `F` would be Hessian quasiconvex at `0`. -/
theorem square_not_hessianQuasiconvexAt_of_zero {n : ℕ} {p : ℝ} (hp : 0 < p)
    {F : Matrix (Fin n) (Fin n) ℝ → ℝ} (hF : Continuous F)
    (hhom : ∀ (t : ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm → F (t • H) = |t| ^ p * F H)
    (h0 : ¬ HessianQuasiconvexAt F 0) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ¬ HessianQuasiconvexAt F A := by
  intro hqA
  apply h0
  -- `F (0) = 0`
  have hF0 : F 0 = 0 := by
    have h := hhom 2 0 Matrix.isSymm_zero
    rw [smul_zero, abs_of_pos two_pos] at h
    have h2 : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow (by norm_num) hp
    have : (2 ^ p - 1) * F 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · linarith
    · exact h3
  intro φ hφ hc hs _
  rw [hF0]
  simp only [zero_add]
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le square_hess_two_le_top
  set H := hessian φ with hHdef
  have hHc : Continuous H := square_hess_continuous_hessian hφ
  have hHs : ∀ x, (H x).IsSymm := square_env_hessian_isSymm hφ2
  have hvol : volume (unitCube n) < ⊤ := by rw [volume_unitCube]; exact ENNReal.one_lt_top
  set Φ : ℝ → ℝ := fun s => ∫ x in unitCube n, F (s • A + H x) with hΦ
  -- `F (A) ≤ ∫ F (A + D² (λ φ)) = λ^p ∫ F (λ⁻¹ A + D²φ)`
  have hscale : ∀ l : ℝ, 0 < l → (l ^ p)⁻¹ * F A ≤ Φ l⁻¹ := by
    intro l hl
    have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => l * φ y := contDiff_const.mul hφ
    have hψc : HasCompactSupport fun y => l * φ y := hc.mul_left (f := fun _ => l)
    have hψs : tsupport (fun y => l * φ y) ⊆ unitCube n :=
      (tsupport_mul_subset_right (f := fun _ => l)).trans hs
    have hHψ : ∀ x, hessian (fun y => l * φ y) x = l • H x := fun x =>
      square_env_hessian_const_mul hφ2 l x
    have hint : IntegrableOn (fun x => F (A + hessian (fun y => l * φ y) x)) (unitCube n) := by
      simp_rw [hHψ]
      exact Sverak.gen_integrableOn_unitCube
        (hF.comp (continuous_const.add (hHc.const_smul l)))
    have key := hqA _ hψ hψc hψs hint
    have e : ∀ x, F (A + hessian (fun y => l * φ y) x) = l ^ p * F (l⁻¹ • A + H x) := fun x => by
      rw [hHψ, show A + l • H x = l • (l⁻¹ • A + H x) by
        rw [smul_add, smul_smul, mul_inv_cancel₀ hl.ne', one_smul],
        hhom l _ ((hA.smul _).add (hHs x)), abs_of_pos hl]
    simp only [e] at key
    rw [integral_const_mul] at key
    rw [inv_mul_le_iff₀ (Real.rpow_pos_of_pos hl p)]
    exact key
  -- `s ↦ ∫ F (s A + D²φ)` is continuous at `0` (dominated convergence)
  have hcont : ContinuousAt Φ 0 := by
    obtain ⟨M, hM⟩ := (hφ.continuous_iteratedFDeriv (square_hess_nat_le_top 2)).bounded_above_of_compact_support
      (hc.iteratedFDeriv 2)
    set R := (∑ i, ∑ j, |A i j|) + M
    set S : Set (Matrix (Fin n) (Fin n) ℝ) :=
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-R) R
    have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
    have : IsFiniteMeasure (volume.restrict (unitCube n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hvol⟩
    refine continuousAt_of_dominated (bound := fun _ => C)
      (Filter.Eventually.of_forall fun s =>
        (hF.comp (continuous_const.add hHc)).aestronglyMeasurable) ?_ (integrable_const C)
      (Filter.Eventually.of_forall fun x => ?_)
    · filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) one_pos] with s hs
      refine Filter.Eventually.of_forall fun x => hC _ ?_
      intro i _ j _
      have h1 : |A i j| ≤ ∑ i, ∑ j, |A i j| :=
        (Finset.single_le_sum (f := fun j' => |A i j'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i' => ∑ j', |A i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
      have h2 : |H x i j| ≤ M := (square_hess_abs_hessian_le hφ2 x i j).trans (hM x)
      have h3 : |s| ≤ 1 := abs_le.2 ⟨hs.1.le, hs.2.le⟩
      have h4 : |(s • A + H x) i j| ≤ R := by
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        calc |s * A i j + H x i j| ≤ |s * A i j| + |H x i j| := abs_add_le _ _
          _ ≤ 1 * |A i j| + M := by rw [abs_mul]; gcongr
          _ ≤ R := by linarith
      exact abs_le.1 h4
    · exact (hF.comp ((continuous_id.smul continuous_const).add continuous_const)).continuousAt
  have ht1 : Tendsto (fun l : ℝ => Φ l⁻¹) atTop (𝓝 (Φ 0)) :=
    hcont.tendsto.comp tendsto_inv_atTop_zero
  have ht2 : Tendsto (fun l : ℝ => (l ^ p)⁻¹ * F A) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hp)).mul_const (F A)
    simpa using this
  have := le_of_tendsto_of_tendsto ht2 ht1
    ((eventually_gt_atTop 0).mono fun l hl => hscale l hl)
  simpa [hΦ] using this

end Hess

end Cassese
