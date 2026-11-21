module

public import Morrey.Cassese.Toolkit
public import Morrey.Cassese.Bridges
public import Morrey.Common.External.Rindler.Lemmas
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Morrey.Common.Basic.Analysis.Fourier.TorusLipschitz

/-!
# Section 7: another example, `ℝ^{4×2}`

`ℝ^{2(N+1)×2}` is identified with the real-linear maps `ℂ → ℂ^{N+1}`: `A = (A₀, …, A_N)` stacked
by rows, block `j` (from `0`) formed by the rows `2j` and `2j + 1` (`rowBlock`), and
`A_j z = α_j z + β_j z̄` (`alphaRow`, `betaRow`; same formulas as in Section 4). For `ρ > 0`,
`P_ρ (A) = (β₀, β₁ − ρ α₀, …, β_N − ρ α_{N−1})` (`chainP`), `Q (A) = α_N` (`chainQ`), and
`chainF N p ρ C (A) = C^p ‖P_ρ (A)‖_{ℓ₂}^p − |Q (A)|^p`, with thresholds
`C^{rc} (p, N, ρ) = rcThreshold (chainF N p ρ)` and `C^{qc} (p, N, ρ) = qcThreshold (chainF N p ρ)`.

`chainOpNorm N p ρ` is the norm of `(h₀, …, h_N) ↦ Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j` from
`L^p_0 (𝕋²; ℓ₂^{N+1})` to `L^p_0 (𝕋²)`, computed on the dense subspace of mean-zero trigonometric
polynomials (`trigPoly`, `torusBeurlingPow` in `Morrey/Cassese/Defs.lean`).

The helpers (prefix `fourByTwo_`) package the steps of the paper's proofs:

* Proposition 7.1: linearity of `α_j`, `β_j`, `P_ρ`, `Q`; the rank-one estimate
  `|Q (R)|² ≤ (Σ_k ρ^{2k}) ‖P_ρ (R)‖²` (`fourByTwo_rankOne_bound`); Rademacher martingales on
  `{±1}^n` as martingales of Mathlib (`fourByTwo_filtration`, `fourByTwo_martingale`), and
  Burkholder's inequality for their linear images (`fourByTwo_burkholder`).
* Proposition 7.2: the periodic lift `Σ w_n e_n` of a trigonometric polynomial and its derivative
  (`fourByTwo_tp`), the test map `u` solving `∂̄u_j = h_j + ρ ∂u_{j−1}` (`fourByTwo_testMap`,
  `fourByTwo_uCoeff`), the identities `P_ρ (∇u) = h`, `Q (∇u) = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j`
  (`fourByTwo_chainP_testMap`, `fourByTwo_chainQ_testMap`), integrals over `𝕋²` as integrals over
  `(0, 1)²` (`fourByTwo_lintegral_torus`), and the inequality `C^{qc} ≥ chainOpNorm`
  (`fourByTwo_chainOpNorm_le_qcThreshold`), through periodic test maps (Lemma 2.2,
  `External.Rindler.quasiconvexAtOn_iff_periodic`). For the inequality `C^{qc} ≤ chainOpNorm`
  (`fourByTwo_qcThreshold_le_chainOpNorm`): the coefficients `ĥ_j` of `P_ρ (∇u)_j` for every
  trigonometric test map `u` (`fourByTwo_hOf`), the identities `P_ρ (∇u) = h`,
  `Q (∇u) = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j` (`fourByTwo_chainP_eq_hOf`, `fourByTwo_chainQ_eq_hOf`, by
  the induction `fourByTwo_telescope`), the inequality `∫ f (∇u) ≥ 0` for these `u`
  (`fourByTwo_integral_chainF_testMap_nonneg`), and its extension to Lipschitz periodic `φ`
  through the Fejér means of `φ` (`fourByTwo_fejerW`, `fourByTwo_pd_fejerW`,
  `fourByTwo_integral_chainF_nonneg_of_periodic`), with the general facts of
  `Morrey.Common.Basic.Analysis.Fourier.TorusLipschitz`.
* Theorem 7.1: `‖·‖_{S₂}` is the Frobenius norm, the maps `P_p`, `Q_p` (`fourByTwo_P`,
  `fourByTwo_Q`), monotonicity of `f_{p,ρ,C}` in `C`.
* Corollary 7.2: homogeneous polynomials, the function `U` and its zig-zag concavity, the quartic
  `𝒫` (`fourByTwo_quartic`), and the passage from `f` to a minorant
  (`fourByTwo_not_quasiconvexAt_of_le`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace Cassese

/-- The row `2j + k` of `ℝ^{2(N+1)×2}`: row `k` of block `j`. -/
def rowBlock {N : ℕ} (j : Fin (N + 1)) (k : Fin 2) : Fin (2 * (N + 1)) :=
  ⟨2 * j.val + k.val, by omega⟩

/-- `α_j (A)` for the block `A_j = (a b; c d)` (rows `2j`, `2j + 1`): `(a + d + i (c − b)) / 2`. -/
noncomputable def alphaRow {N : ℕ} (A : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) (j : Fin (N + 1)) :
    ℂ :=
  (((A (rowBlock j 0) 0 + A (rowBlock j 1) 1) / 2 : ℝ) : ℂ) +
    (((A (rowBlock j 1) 0 - A (rowBlock j 0) 1) / 2 : ℝ) : ℂ) * Complex.I

/-- `β_j (A) = (a − d + i (c + b)) / 2` for the block `A_j = (a b; c d)`. -/
noncomputable def betaRow {N : ℕ} (A : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) (j : Fin (N + 1)) :
    ℂ :=
  (((A (rowBlock j 0) 0 - A (rowBlock j 1) 1) / 2 : ℝ) : ℂ) +
    (((A (rowBlock j 1) 0 + A (rowBlock j 0) 1) / 2 : ℝ) : ℂ) * Complex.I

/-- `P_ρ (A) = (β₀, β₁ − ρ α₀, …, β_N − ρ α_{N−1})`. -/
noncomputable def chainP {N : ℕ} (ρ : ℝ) (A : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ)
    (j : Fin (N + 1)) : ℂ :=
  if h : j.val = 0 then betaRow A j
  else betaRow A j - (ρ : ℂ) * alphaRow A ⟨j.val - 1, by omega⟩

/-- `Q (A) = α_N`. -/
noncomputable def chainQ {N : ℕ} (A : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) : ℂ :=
  alphaRow A (Fin.last N)

/-- `f_{p,ρ,C} (A) = C^p ‖P_ρ (A)‖_{ℓ₂}^p − |Q (A)|^p`. -/
noncomputable def chainF (N : ℕ) (p ρ C : ℝ) (A : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) : ℝ :=
  C ^ p * √(∑ j, ‖chainP ρ A j‖ ^ 2) ^ p - ‖chainQ A‖ ^ p

/-- `‖(ρ^N 𝓑^{N+1}, ρ^{N−1} 𝓑^N, …, ρ 𝓑², 𝓑)‖_{L^p_0 (𝕋²; ℓ₂^{N+1}) → L^p_0 (𝕋²)}`, on mean-zero
trigonometric polynomials `h_j`. -/
noncomputable def chainOpNorm (N : ℕ) (p ρ : ℝ) : ℝ≥0∞ :=
  ⨆ (c : Fin (N + 1) → ((Fin 2 → ℤ) →₀ ℂ)) (_ : ∀ j, c j 0 = 0),
    eLpNorm (fun x => ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
        torusBeurlingPow (N + 1 - j.val) (c j) x) (ENNReal.ofReal p) volume /
      eLpNorm (fun x => √(∑ j, ‖trigPoly (c j) x‖ ^ 2)) (ENNReal.ofReal p) volume

/-- Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
operator*, Arch. Math. 96 (2011), Theorem 1.1, as used in the proof of Corollary 7.2:
`‖𝓑²‖_{L⁴ (ℝ²) → L⁴ (ℝ²)} ≥ 21 / 5`. Out of reach (class X of the inventory): a proposition with
no proof, a hypothesis of every statement whose proof uses it. It is defined here rather than in
`External/` because it is stated with the shared definitions of `Morrey/Cassese/Defs.lean`, like
`DragicevicLowerBound`; the source's own formulation could not be consulted. -/
def DragicevicL4Bound : Prop :=
  ENNReal.ofReal (21 / 5) ≤ beurlingPowNorm 2 4

/-! ### The coefficients `α_j`, `β_j`, `P_ρ`, `Q` are real-linear -/

/-- `A ↦ α_j (A)` as a real-linear map. -/
noncomputable def fourByTwo_alphaLin {N : ℕ} (j : Fin (N + 1)) :
    Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ →ₗ[ℝ] ℂ where
  toFun A := alphaRow A j
  map_add' A B := by apply Complex.ext <;> simp [alphaRow] <;> ring
  map_smul' c A := by apply Complex.ext <;> simp [alphaRow] <;> ring

/-- `A ↦ β_j (A)` as a real-linear map. -/
noncomputable def fourByTwo_betaLin {N : ℕ} (j : Fin (N + 1)) :
    Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ →ₗ[ℝ] ℂ where
  toFun A := betaRow A j
  map_add' A B := by apply Complex.ext <;> simp [betaRow] <;> ring
  map_smul' c A := by apply Complex.ext <;> simp [betaRow] <;> ring

/-- `A ↦ P_ρ (A)_j` as a real-linear map. -/
noncomputable def fourByTwo_PLin {N : ℕ} (ρ : ℝ) (j : Fin (N + 1)) :
    Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ →ₗ[ℝ] ℂ where
  toFun A := chainP ρ A j
  map_add' A B := by
    unfold chainP
    split_ifs <;> apply Complex.ext <;> simp [betaRow, alphaRow] <;> ring
  map_smul' c A := by
    unfold chainP
    split_ifs <;> apply Complex.ext <;> simp [betaRow, alphaRow] <;> ring

/-- `A ↦ Q (A)` as a real-linear map. -/
noncomputable def fourByTwo_QLin (N : ℕ) : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ →ₗ[ℝ] ℂ :=
  fourByTwo_alphaLin (Fin.last N)

theorem fourByTwo_PLin_apply {N : ℕ} (ρ : ℝ) (j : Fin (N + 1))
    (A : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) : fourByTwo_PLin ρ j A = chainP ρ A j := rfl

theorem fourByTwo_QLin_apply {N : ℕ} (A : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) :
    fourByTwo_QLin N A = chainQ A := rfl

theorem fourByTwo_continuous_chainF (N : ℕ) {p : ℝ} (hp : 0 ≤ p) (ρ C : ℝ) :
    Continuous (chainF N p ρ C) := by
  have hP : ∀ j, Continuous fun A : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ => chainP ρ A j :=
    fun j => (fourByTwo_PLin ρ j).continuous_of_finiteDimensional
  have hQ : Continuous fun A : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ => chainQ A :=
    (fourByTwo_QLin N).continuous_of_finiteDimensional
  unfold chainF
  refine Continuous.sub (continuous_const.mul ?_) ?_
  · exact (Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
      ((hP j).norm.pow 2))).rpow_const fun _ => Or.inr hp
  · exact hQ.norm.rpow_const fun _ => Or.inr hp

/-! ### Rank-one matrices: Proposition 7.1's algebra -/

/-- A matrix with two columns and rank at most one has a nonzero kernel vector. -/
theorem fourByTwo_exists_ker {n : ℕ} (R : Matrix (Fin n) (Fin 2) ℝ) (h : R.rank ≤ 1) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ i, R i 0 * v 0 + R i 1 * v 1 = 0 := by
  have hsum := R.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker R.mulVecLin) := by
    rw [Matrix.rank] at h
    omega
  obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  refine ⟨v, fun h0 => hv0 (Subtype.ext h0), fun i => ?_⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  have := congrFun hv i
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this

/-- If `A` has rank (at most) one, then `β_j w = w̄ α_j` for all `j`, for one `w ≠ 0`: so
`β_j = ω α_j` with the unimodular `ω = w̄ / w` (proof of Proposition 7.1). -/
theorem fourByTwo_beta_eq {N : ℕ} (R : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) (hR : R.rank ≤ 1) :
    ∃ w : ℂ, w ≠ 0 ∧ ∀ j, betaRow R j * w = starRingEnd ℂ w * alphaRow R j := by
  obtain ⟨v, hv0, hv⟩ := fourByTwo_exists_ker R hR
  refine ⟨(v 1 : ℂ) + (v 0 : ℂ) * Complex.I, ?_, fun j => ?_⟩
  · intro h
    apply hv0
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    ext i
    fin_cases i <;> simp [h1, h2]
  · have e0 := hv (rowBlock j 0)
    have e1 := hv (rowBlock j 1)
    apply Complex.ext <;> simp [betaRow, alphaRow]
    · linear_combination (-1 : ℝ) * e1
    · linear_combination e0

/-- The rank-one estimate of the proof of Proposition 7.1: if `A` has rank at most one, then
`|Q (A)|² ≤ (Σ_{k=0}^N ρ^{2k}) ‖P_ρ (A)‖²_{ℓ₂}`. The paper's argument: `β_j = ω α_j` with
`|ω| = 1`; with `γ₀ = α₀`, `γ_j = α_j − ρ ω̄ α_{j−1}`, `‖P_ρ (A)‖² = Σ |γ_j|²` and
`α_N = Σ_j (ρ ω̄)^{N−j} γ_j`; then Cauchy–Schwarz. -/
theorem fourByTwo_rankOne_bound {N : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (R : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) (hR : R.rank ≤ 1) :
    ‖chainQ R‖ ^ 2 ≤ (∑ k ∈ Finset.range (N + 1), ρ ^ (2 * k)) * ∑ j, ‖chainP ρ R j‖ ^ 2 := by
  obtain ⟨w, hw0, hw⟩ := fourByTwo_beta_eq R hR
  set ω : ℂ := starRingEnd ℂ w / w with hωdef
  have hwn : (‖w‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hω : ‖ω‖ = 1 := by
    rw [hωdef, norm_div, Complex.norm_conj, div_self hwn]
  have hωω : ω * starRingEnd ℂ ω = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hω]; simp
  have hβ : ∀ j, betaRow R j = ω * alphaRow R j := by
    intro j
    rw [hωdef, div_mul_eq_mul_div, eq_div_iff hw0, hw j]
  -- the `ℕ`-indexed `α` and `γ`
  set a : ℕ → ℂ := fun j => if h : j < N + 1 then alphaRow R ⟨j, h⟩ else 0 with ha
  set c : ℂ := (ρ : ℂ) * starRingEnd ℂ ω with hc
  set γ : ℕ → ℂ := fun j => if j = 0 then a 0 else a j - c * a (j - 1) with hγ
  have hP : ∀ j : Fin (N + 1), chainP ρ R j = ω * γ j := by
    intro j
    unfold chainP
    split_ifs with h
    · have hj : j = ⟨0, Nat.succ_pos N⟩ := Fin.ext h
      rw [hj]
      simp [hγ, ha, hβ]
    · have h1 : j.val - 1 < N + 1 := by omega
      simp only [hγ, h, ha, j.isLt, h1, hβ, hc, ↓reduceIte, ↓reduceDIte]
      linear_combination (ρ : ℂ) * alphaRow R ⟨j.val - 1, h1⟩ * hωω
  have hnorm : ∀ j : Fin (N + 1), ‖chainP ρ R j‖ = ‖γ j‖ := by
    intro j; rw [hP, norm_mul, hω, one_mul]
  have htel : ∀ M, ∑ j ∈ Finset.range (M + 1), c ^ (M - j) * γ j = a M := by
    intro M
    induction M with
    | zero => simp [hγ]
    | succ M ih =>
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
      have : ∑ j ∈ Finset.range (M + 1), c ^ (M + 1 - j) * γ j =
          c * ∑ j ∈ Finset.range (M + 1), c ^ (M - j) * γ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [show M + 1 - j = (M - j) + 1 by omega, pow_succ]
        ring
      rw [this, ih]
      simp only [hγ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      ring
  have hcn : ‖c‖ = ρ := by
    rw [hc, norm_mul, Complex.norm_conj, hω, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ]
  have hQ : chainQ R = a N := by simp [chainQ, ha, Fin.last]
  have h1 : ‖chainQ R‖ ≤ ∑ j ∈ Finset.range (N + 1), ρ ^ (N - j) * ‖γ j‖ := by
    rw [hQ, ← htel N]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [norm_mul, norm_pow, hcn]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + 1)) (fun j => ρ ^ (N - j))
    fun j => ‖γ j‖
  have h3 : ∑ j ∈ Finset.range (N + 1), (ρ ^ (N - j)) ^ 2 =
      ∑ k ∈ Finset.range (N + 1), ρ ^ (2 * k) := by
    rw [← Finset.sum_range_reflect (fun k => ρ ^ (2 * k)) (N + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← pow_mul, show N + 1 - 1 - j = N - j by omega, mul_comm]
  have h4 : ∑ j ∈ Finset.range (N + 1), ‖γ j‖ ^ 2 = ∑ j, ‖chainP ρ R j‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => ‖γ j‖ ^ 2) (N + 1)]
    exact Finset.sum_congr rfl fun j _ => by rw [hnorm]
  rw [← h3, ← h4]
  calc ‖chainQ R‖ ^ 2 ≤ (∑ j ∈ Finset.range (N + 1), ρ ^ (N - j) * ‖γ j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-! ### Rademacher martingales on the canonical space are martingales

The setting in which Burkholder's inequality (`BurkholderInequality`) is applied to rank-one
Rademacher martingales: the space `Fin n → Bool` of `n` signs with the uniform probability
(`ProbabilityTheory.uniformOn Set.univ`), and the natural filtration
`ℱ_k = σ (ε₀, …, ε_{k−1})` (`fourByTwo_filtration`). -/

/-- The truncation `ε ↦ (ε₀, …, ε_{k−1}, false, …, false)`. -/
def fourByTwo_trunc {n : ℕ} (k : ℕ) (ε : Fin n → Bool) : Fin n → Bool :=
  fun j => if j.val < k then ε j else false

theorem fourByTwo_trunc_trunc {n : ℕ} {k k' : ℕ} (h : k ≤ k') (ε : Fin n → Bool) :
    fourByTwo_trunc k (fourByTwo_trunc k' ε) = fourByTwo_trunc k ε := by
  funext j
  simp only [fourByTwo_trunc]
  split_ifs <;> first | rfl | omega

/-- The natural filtration of the signs: `ℱ_k = σ (ε₀, …, ε_{k−1})`. -/
noncomputable def fourByTwo_filtration (n : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin n → Bool)) where
  seq k := MeasurableSpace.comap (fourByTwo_trunc k) inferInstance
  mono' k k' h := by
    show MeasurableSpace.comap (fourByTwo_trunc k) _ ≤ MeasurableSpace.comap (fourByTwo_trunc k') _
    rw [show (fourByTwo_trunc k : (Fin n → Bool) → (Fin n → Bool)) =
        fourByTwo_trunc k ∘ fourByTwo_trunc k' from
        funext fun ε => (fourByTwo_trunc_trunc h ε).symm, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono fun s _ => MeasurableSet.of_discrete
  le' _ := fun _ _ => MeasurableSet.of_discrete

theorem fourByTwo_mart_trunc {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin n → (Fin n → Bool) → E) (hξ : IsPredictable ξ) (k : ℕ) (ε : Fin n → Bool) :
    mart ξ k (fourByTwo_trunc k ε) = mart ξ k ε := by
  unfold mart
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rw [hξ j (fourByTwo_trunc k ε) ε fun i hi => by
    have : i.val < k := lt_trans (Fin.lt_def.mp hi) hj
    simp [fourByTwo_trunc, this]]
  simp [fourByTwo_trunc, hj]

theorem fourByTwo_mart_succ {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin n → (Fin n → Bool) → E) (k : ℕ) (ε : Fin n → Bool) :
    mart ξ (k + 1) ε = mart ξ k ε + if h : k < n then coin (ε ⟨k, h⟩) • ξ ⟨k, h⟩ ε else 0 := by
  unfold mart
  split_ifs with h
  · rw [show Finset.univ.filter (fun j : Fin n => j.val < k + 1) =
        insert ⟨k, h⟩ (Finset.univ.filter (fun j : Fin n => j.val < k)) from ?_,
      Finset.sum_insert (by simp)]
    · abel
    · ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
  · rw [add_zero]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem fourByTwo_mart_zero {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin n → (Fin n → Bool) → E) (ε : Fin n → Bool) : mart ξ 0 ε = 0 := by
  simp [mart]

theorem fourByTwo_coin_not (b : Bool) : coin (!b) = -coin b := by
  cases b <;> simp [coin]

theorem fourByTwo_uniformOn_singleton {n : ℕ} (ε : Fin n → Bool) :
    (ProbabilityTheory.uniformOn (Set.univ : Set (Fin n → Bool))).real {ε} = 1 / 2 ^ n := by
  rw [Measure.real, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
  simp [Fintype.card_bool]

/-- A Rademacher (Paley–Walsh) martingale `k ↦ Σ_{j<k} ε_j ξ_j` with predictable `ξ` is a
martingale for the natural filtration of the signs and the uniform probability. -/
theorem fourByTwo_martingale {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ξ : Fin n → (Fin n → Bool) → E) (hξ : IsPredictable ξ) :
    Martingale (fun k => mart ξ k) (fourByTwo_filtration n)
      (ProbabilityTheory.uniformOn Set.univ) := by
  refine martingale_of_setIntegral_eq_succ (fun k => ?_) (fun k => Integrable.of_finite)
    (fun k s hs => ?_)
  · have : (mart ξ k) = (mart ξ k) ∘ fourByTwo_trunc k :=
      funext fun ε => (fourByTwo_mart_trunc ξ hξ k ε).symm
    show StronglyMeasurable[MeasurableSpace.comap (fourByTwo_trunc k) inferInstance] (mart ξ k)
    rw [this]
    exact StronglyMeasurable.of_discrete.comp_measurable (comap_measurable _)
  · obtain ⟨t, -, rfl⟩ := hs
    simp_rw [fourByTwo_mart_succ ξ k]
    rw [integral_add Integrable.of_finite.integrableOn Integrable.of_finite.integrableOn,
      left_eq_add]
    split_ifs with h
    swap
    · simp
    rw [← integral_indicator MeasurableSet.of_discrete, integral_fintype Integrable.of_finite]
    simp_rw [fourByTwo_uniformOn_singleton]
    rw [← Finset.smul_sum]
    -- the flip of the `k`-th sign
    set σ : (Fin n → Bool) ≃ (Fin n → Bool) :=
      { toFun := fun ε => Function.update ε ⟨k, h⟩ (!ε ⟨k, h⟩)
        invFun := fun ε => Function.update ε ⟨k, h⟩ (!ε ⟨k, h⟩)
        left_inv := fun ε => by funext j; by_cases hj : j = ⟨k, h⟩ <;> simp [hj]
        right_inv := fun ε => by funext j; by_cases hj : j = ⟨k, h⟩ <;> simp [hj] } with hσ
    set g := (fourByTwo_trunc k ⁻¹' t).indicator
      (fun ε => coin (ε ⟨k, h⟩) • ξ ⟨k, h⟩ ε) with hg
    have hflip : ∀ ε, g (σ ε) = -g ε := by
      intro ε
      have htr : fourByTwo_trunc k (σ ε) = fourByTwo_trunc k ε := by
        funext j
        simp only [fourByTwo_trunc, hσ, Equiv.coe_fn_mk]
        split_ifs with hj
        · rw [Function.update_of_ne]
          intro hjk
          rw [hjk] at hj
          exact lt_irrefl _ hj
        · rfl
      have hξσ : ξ ⟨k, h⟩ (σ ε) = ξ ⟨k, h⟩ ε := hξ _ _ _ fun i hi => by
        simp only [hσ, Equiv.coe_fn_mk]
        exact Function.update_of_ne (ne_of_lt hi) _ _
      have hmem : σ ε ∈ fourByTwo_trunc k ⁻¹' t ↔ ε ∈ fourByTwo_trunc k ⁻¹' t := by
        simp only [Set.mem_preimage, htr]
      by_cases hε : ε ∈ fourByTwo_trunc k ⁻¹' t
      · rw [hg, Set.indicator_of_mem (hmem.mpr hε), Set.indicator_of_mem hε, hξσ]
        simp [hσ, fourByTwo_coin_not, neg_smul]
      · rw [hg, Set.indicator_of_notMem (fun h' => hε (hmem.mp h')),
          Set.indicator_of_notMem hε, neg_zero]
    have hsum : ∑ ε, g ε = -∑ ε, g ε := by
      conv_lhs => rw [← Equiv.sum_comp σ g]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun ε _ => hflip ε
    have h2 : (2 : ℝ) • ∑ ε, g ε = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hsum]
      exact add_neg_cancel _
    rw [smul_eq_zero.mp h2 |>.resolve_left two_ne_zero, smul_zero]

/-- On the signs with the uniform probability,
`‖f‖_{L^p} = (2^{−n} Σ_ε ‖f (ε)‖^p)^{1/p}`. -/
theorem fourByTwo_eLpNorm_uniform {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : (Fin n → Bool) → E) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) (ProbabilityTheory.uniformOn Set.univ) =
      ENNReal.ofReal (((∑ ε, ‖f ε‖ ^ p) / 2 ^ n) ^ (1 / p)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    AEStronglyMeasurable.of_discrete, ENNReal.toReal_ofReal hp.le, lintegral_fintype]
  have hμ : ∀ ε : Fin n → Bool,
      (ProbabilityTheory.uniformOn (Set.univ : Set (Fin n → Bool))) {ε} =
        ENNReal.ofReal (1 / 2 ^ n) := fun ε => by
    rw [← fourByTwo_uniformOn_singleton ε, ofReal_measureReal]
  have hsum : 0 ≤ (∑ ε, ‖f ε‖ ^ p) / 2 ^ n :=
    div_nonneg (Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  rw [← ENNReal.ofReal_rpow_of_nonneg hsum (by positivity)]
  congr 1
  have hterm : ∀ ε, ‖f ε‖ₑ ^ p * (ProbabilityTheory.uniformOn Set.univ) {ε} =
      ENNReal.ofReal (‖f ε‖ ^ p * (1 / 2 ^ n)) := by
    intro ε
    rw [hμ, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [Finset.sum_congr rfl fun ε _ => hterm ε, ← ENNReal.ofReal_sum_of_nonneg fun ε _ =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by positivity), ← Finset.sum_mul]
  congr 1
  ring

/-- The results of [Cassese 2025] used in the proof of Proposition 7.1, through Burkholder's
inequality (Theorem 2.3): if two linear maps `L_X`, `L_Y` into a separable Hilbert space satisfy
`‖L_X (R)‖ ≤ ‖L_Y (R)‖` on the matrices of rank at most one, then for every rank-one Rademacher
martingale `M` started at `0`, the martingale `L_X (M)` is differentially subordinate to
`L_Y (M)`, so `E ‖L_X (M_n)‖^p ≤ (p* − 1)^p E ‖L_Y (M_n)‖^p`. -/
theorem fourByTwo_burkholder (hB : BurkholderInequality) {d m : ℕ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (LX LY : Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ] H)
    (hXY : ∀ R : Matrix (Fin d) (Fin m) ℝ, R.rank ≤ 1 → ‖LX R‖ ≤ ‖LY R‖) {p : ℝ} (hp : 1 < p)
    (n : ℕ) (A : Fin n → (Fin n → Bool) → Matrix (Fin d) (Fin m) ℝ)
    (hA : IsRankOneIncrements A) :
    ∑ ε, ‖LX (radMart 0 A n ε)‖ ^ p ≤ (pStar p - 1) ^ p * ∑ ε, ‖LY (radMart 0 A n ε)‖ ^ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 ≤ pStar p - 1 := by
    have : p ≤ pStar p := le_max_left _ _
    linarith
  set ξX : Fin n → (Fin n → Bool) → H := fun k ε => LX (A k ε) with hξX
  set ξY : Fin n → (Fin n → Bool) → H := fun k ε => LY (A k ε) with hξY
  have hpX : IsPredictable ξX := fun k ε ε' h => by simp only [hξX, hA.1 k ε ε' h]
  have hpY : IsPredictable ξY := fun k ε ε' h => by simp only [hξY, hA.1 k ε ε' h]
  have hmX : ∀ k ε, mart ξX k ε = LX (radMart 0 A k ε) := by
    intro k ε; simp [hξX, radMart, mart, map_sum, map_smul]
  have hmY : ∀ k ε, mart ξY k ε = LY (radMart 0 A k ε) := by
    intro k ε; simp [hξY, radMart, mart, map_sum, map_smul]
  have hsub : ∀ k (ε : Fin n → Bool),
      ‖mart ξX (k + 1) ε - mart ξX k ε‖ ≤ ‖mart ξY (k + 1) ε - mart ξY k ε‖ := by
    intro k ε
    rw [fourByTwo_mart_succ, fourByTwo_mart_succ, add_sub_cancel_left, add_sub_cancel_left]
    split_ifs with h
    · rw [norm_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (hXY _ (hA.2 _ _)) (norm_nonneg _)
    · simp
  have key := hB (Fin n → Bool) inferInstance (ProbabilityTheory.uniformOn Set.univ)
    (fourByTwo_filtration n) H (fun k => mart ξX k) (fun k => mart ξY k) p hp
    (fourByTwo_martingale ξX hpX) (fourByTwo_martingale ξY hpY) (fourByTwo_mart_zero ξX)
    (fourByTwo_mart_zero ξY) (fun k => ae_of_all _ (hsub k)) n
  rw [fourByTwo_eLpNorm_uniform _ hp0, fourByTwo_eLpNorm_uniform _ hp0,
    ← ENNReal.ofReal_mul hp1] at key
  have hX0 : 0 ≤ (∑ ε, ‖mart ξX n ε‖ ^ p) / 2 ^ n :=
    div_nonneg (Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  have hY0 : 0 ≤ (∑ ε, ‖mart ξY n ε‖ ^ p) / 2 ^ n :=
    div_nonneg (Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hp1 (Real.rpow_nonneg hY0 _))] at key
  have key2 := Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) key hp0.le
  rw [Real.mul_rpow hp1 (Real.rpow_nonneg hY0 _), one_div, Real.rpow_inv_rpow hX0 hp0.ne',
    Real.rpow_inv_rpow hY0 hp0.ne'] at key2
  simp_rw [hmX, hmY] at key2
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ h2, mul_div_assoc', div_mul_cancel₀ _ h2.ne'] at key2
  exact key2

/-- **Proposition 7.1** (`prop:rcbound`): for every `p ∈ (1, ∞)`,
`C^{rc} (p, N, ρ) ≤ (p* − 1) (Σ_{k=0}^N ρ^{2k})^{1/2}`. Conditional on Burkholder's inequality
(Theorem 2.3), through "the results of [Cassese 2025]".

Proof (the paper's). By Proposition 2.5 (`proposition2_5`), `f_{p,ρ,K}` with
`K = (p* − 1) (Σ ρ^{2k})^{1/2}` is rank-one convex at `0` once `E |Q (M_n)|^p ≤ K^p E ‖P_ρ (M_n)‖^p`
for every rank-one Rademacher martingale `M` started at `0`. "The results of [Cassese 2025]"
(`C^{rc} ≤ (p* − 1) sup_{A ∈ ℛ₁} |Q (A)| / ‖P_ρ (A)‖`) are used in the form
`fourByTwo_burkholder`, proved by their standard argument: `Q (M)` and `√S P_ρ (M)` are martingales
in `ℂ^{N+1}` (`fourByTwo_martingale`) and the first is differentially subordinate to the second
when `|Q| ≤ √S ‖P_ρ‖` on rank-one matrices, so Burkholder's inequality applies. That bound, with
`√S = (Σ_{k=0}^N ρ^{2k})^{1/2}`, is the paper's computation (`fourByTwo_rankOne_bound`:
`β_j = ω α_j`, `γ_j = α_j − ρ ω̄ α_{j−1}`, Cauchy–Schwarz). -/
theorem proposition7_1 (hB : BurkholderInequality) (N : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) {p : ℝ} (hp : 1 < p) :
    rcThreshold (chainF N p ρ) ≤
      ENNReal.ofReal ((pStar p - 1) * √(∑ k ∈ Finset.range (N + 1), ρ ^ (2 * k))) := by
  set S := ∑ k ∈ Finset.range (N + 1), ρ ^ (2 * k) with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => pow_nonneg hρ.le _
  have hp0 : 0 < p := by linarith
  have hp1 : 0 ≤ pStar p - 1 := by
    have : p ≤ pStar p := le_max_left _ _
    linarith
  set K := (pStar p - 1) * √S with hKdef
  have hK : 0 ≤ K := mul_nonneg hp1 (Real.sqrt_nonneg _)
  refine iInf₂_le K ⟨hK, ?_⟩
  -- Proposition 2.5: test `f_{p,ρ,K}` on rank-one Rademacher martingales started at `0`
  rw [proposition2_5 (fourByTwo_continuous_chainF N hp0.le ρ K)]
  intro n A hA
  -- Burkholder's inequality for `X = Q (M)` and `Y = √S P_ρ (M)`, in `ℂ^{N+1}`
  set H := EuclideanSpace ℂ (Fin (N + 1))
  set toE : (Fin (N + 1) → ℂ) →ₗ[ℝ] H := (WithLp.linearEquiv 2 ℝ (Fin (N + 1) → ℂ)).symm.toLinearMap
  set LX : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ →ₗ[ℝ] H :=
    toE ∘ₗ LinearMap.pi fun j => if j = 0 then fourByTwo_QLin N else 0 with hLX
  set LY : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ →ₗ[ℝ] H :=
    √S • (toE ∘ₗ LinearMap.pi fun j => fourByTwo_PLin ρ j) with hLY
  have hnX : ∀ R, ‖LX R‖ = ‖chainQ R‖ := by
    intro R
    rw [EuclideanSpace.norm_eq]
    simp [hLX, toE, ite_apply, apply_ite, fourByTwo_QLin_apply]
  have hnY : ∀ R, ‖LY R‖ = √S * √(∑ j, ‖chainP ρ R j‖ ^ 2) := by
    intro R
    rw [hLY, LinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      EuclideanSpace.norm_eq]
    simp [toE, fourByTwo_PLin_apply]
  have hXY : ∀ R : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ, R.rank ≤ 1 → ‖LX R‖ ≤ ‖LY R‖ := by
    intro R hR
    rw [hnX, hnY, ← Real.sqrt_mul hS]
    exact Real.le_sqrt_of_sq_le (fourByTwo_rankOne_bound hρ.le R hR)
  have key := fourByTwo_burkholder hB LX LY hXY hp n A hA
  simp_rw [hnX, hnY] at key
  -- conclude: `0 = f (0) ≤ E f (M_n)`
  have h0 : chainF N p ρ K 0 = 0 := by
    have hP0 : ∀ j, chainP ρ (0 : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) j = 0 :=
      fun j => (fourByTwo_PLin ρ j).map_zero
    have hQ0 : chainQ (0 : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) = 0 := (fourByTwo_QLin N).map_zero
    simp [chainF, hP0, hQ0, Real.zero_rpow hp0.ne']
  rw [h0, avg]
  refine div_nonneg ?_ (by positivity)
  simp only [chainF]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sub_nonneg]
  refine key.trans (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [hKdef, Real.mul_rpow hp1 (Real.sqrt_nonneg _),
    Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  ring

/-! ### Test maps: integrability -/

/-- `f_{p,ρ,C}` vanishes at `0`. -/
theorem fourByTwo_chainF_zero (N : ℕ) {p : ℝ} (hp : 0 < p) (ρ C : ℝ) :
    chainF N p ρ C 0 = 0 := by
  have hP0 : ∀ j, chainP ρ (0 : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) j = 0 :=
    fun j => (fourByTwo_PLin ρ j).map_zero
  have hQ0 : chainQ (0 : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ) = 0 := (fourByTwo_QLin N).map_zero
  simp [chainF, hP0, hQ0, Real.zero_rpow hp.ne']

theorem fourByTwo_measurable_jac {d m : ℕ} (φ : (Fin m → ℝ) → Fin d → ℝ) :
    Measurable (jac φ) := by
  unfold jac
  exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k =>
    measurable_fderiv_apply_const ℝ (fun y => φ y i) (Pi.single k 1)

theorem fourByTwo_jac_bound {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (x : Fin m → ℝ) (i : Fin d) (k : Fin m) : |jac φ x i k| ≤ K := by
  have hi : LipschitzWith K (fun y => φ y i) := by
    simpa [Function.comp_def, Function.eval] using (LipschitzWith.eval i).comp hφ
  have h1 := norm_fderiv_le_of_lipschitz ℝ hi (x₀ := x)
  calc |jac φ x i k| = ‖fderiv ℝ (fun y => φ y i) x (Pi.single k 1)‖ := by
        simp [jac, Real.norm_eq_abs]
    _ ≤ ‖fderiv ℝ (fun y => φ y i) x‖ * ‖(Pi.single k 1 : Fin m → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fun y => φ y i) x‖ := by rw [Pi.norm_single, norm_one, mul_one]
    _ ≤ K := h1

/-- For a continuous `g` and a Lipschitz `φ`, `x ↦ g (∇φ (x))` is integrable on the unit cube. -/
theorem fourByTwo_integrableOn_comp_jac {d m : ℕ} {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hg : Continuous g) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) :
    IntegrableOn (fun x => g (0 + jac φ x)) (unitCube m) := by
  obtain ⟨M, hM⟩ := (isCompact_univ_pi fun _ : Fin d => isCompact_univ_pi fun _ : Fin m =>
    isCompact_Icc (a := -(K : ℝ)) (b := K)).exists_bound_of_continuousOn hg.continuousOn
  simp only [zero_add]
  refine Measure.integrableOn_of_bounded (M := M) ?_
    (hg.measurable.comp (fourByTwo_measurable_jac φ)).aestronglyMeasurable
    (ae_of_all _ fun x => hM _ ?_)
  · rw [unitCube, Real.volume_pi_Ioo]
    simp
  · exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun k =>
      abs_le.mp (fourByTwo_jac_bound hφ x i k)

/-! ### Proposition 7.2: trigonometric polynomials on `ℝ²`

A trigonometric polynomial on the torus `𝕋² = ℝ² / ℤ²` is lifted to the `ℤ²`-periodic function
`x ↦ Σ_n w_n e_n (x)` on `ℝ²`, with `e_n (x) = exp (2πi ⟨n, x⟩)` (`fourByTwo_E`), whose
derivative is explicit. -/

/-- `θ_n (x) = 2π ⟨n, x⟩`. -/
noncomputable def fourByTwo_θ (n : Fin 2 → ℤ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ∑ i, (2 * Real.pi * (n i : ℝ)) • ContinuousLinearMap.proj i

theorem fourByTwo_θ_apply (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    fourByTwo_θ n x = ∑ i, 2 * Real.pi * (n i : ℝ) * x i := by
  simp [fourByTwo_θ]

/-- `e_n (x) = exp (2πi ⟨n, x⟩)` on `ℝ²`. -/
noncomputable def fourByTwo_E (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) : ℂ :=
  Complex.exp (Complex.I * (fourByTwo_θ n x : ℂ))

/-- `e_n` is the monomial `mFourier n` of the torus, composed with the projection `ℝ² → 𝕋²`. -/
theorem fourByTwo_E_eq (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    fourByTwo_E n x = UnitAddTorus.mFourier n (fun i => (x i : UnitAddCircle)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply, fourByTwo_E,
    fourByTwo_θ_apply, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem fourByTwo_E_hasFDerivAt (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    HasFDerivAt (fourByTwo_E n)
      (fourByTwo_E n x • (Complex.I • (Complex.ofRealCLM.comp (fourByTwo_θ n)))) x := by
  have h1 : HasFDerivAt (fun y => Complex.I * (fourByTwo_θ n y : ℂ))
      (Complex.I • (Complex.ofRealCLM.comp (fourByTwo_θ n))) x :=
    ((Complex.ofRealCLM.comp (fourByTwo_θ n)).hasFDerivAt (x := x)).const_mul Complex.I
  exact h1.cexp

theorem fourByTwo_norm_E (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) : ‖fourByTwo_E n x‖ = 1 := by
  rw [fourByTwo_E, mul_comm, Complex.norm_exp_ofReal_mul_I]

theorem fourByTwo_dist_E (n : Fin 2 → ℤ) (x y : Fin 2 → ℝ) :
    dist (fourByTwo_E n x) (fourByTwo_E n y) ≤ ‖fourByTwo_θ n‖ * dist x y := by
  rw [dist_eq_norm]
  have h : fourByTwo_E n x - fourByTwo_E n y = fourByTwo_E n y *
      (Complex.exp (Complex.I * ((fourByTwo_θ n x - fourByTwo_θ n y : ℝ) : ℂ)) - 1) := by
    rw [fourByTwo_E, fourByTwo_E, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, fourByTwo_norm_E, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := fourByTwo_θ n x - fourByTwo_θ n y)).trans ?_
  rw [← map_sub, dist_eq_norm]
  exact (fourByTwo_θ n).le_opNorm _

/-- `e_n` is `ℤ²`-periodic. -/
theorem fourByTwo_E_periodic (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) (z : Fin 2 → ℤ) :
    fourByTwo_E n (x + fun i => (z i : ℝ)) = fourByTwo_E n x := by
  rw [fourByTwo_E_eq, fourByTwo_E_eq]
  congr 1
  funext i
  simp only [Pi.add_apply, AddCircle.coe_add, add_eq_left]
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z i, by simp⟩

/-- The periodic lift `x ↦ Σ_{n ∈ S} w_n e_n (x)` of a trigonometric polynomial. -/
noncomputable def fourByTwo_tp (S : Finset (Fin 2 → ℤ)) (w : (Fin 2 → ℤ) → ℂ)
    (x : Fin 2 → ℝ) : ℂ :=
  ∑ n ∈ S, w n * fourByTwo_E n x

theorem fourByTwo_tp_hasFDerivAt (S : Finset (Fin 2 → ℤ)) (w : (Fin 2 → ℤ) → ℂ)
    (x : Fin 2 → ℝ) :
    HasFDerivAt (fourByTwo_tp S w) (∑ n ∈ S, w n •
      (fourByTwo_E n x • (Complex.I • (Complex.ofRealCLM.comp (fourByTwo_θ n))))) x := by
  unfold fourByTwo_tp
  exact HasFDerivAt.fun_sum fun n _ => (fourByTwo_E_hasFDerivAt n x).const_mul (w n)

/-- The partial derivatives: `∂_k (Σ w_n e_n) = Σ w_n e_n · 2πi n_k`. -/
theorem fourByTwo_tp_partial (S : Finset (Fin 2 → ℤ)) (w : (Fin 2 → ℤ) → ℂ) (x : Fin 2 → ℝ)
    (k : Fin 2) :
    (∑ n ∈ S, w n • (fourByTwo_E n x • (Complex.I • (Complex.ofRealCLM.comp (fourByTwo_θ n)))))
        (Pi.single k 1) =
      ∑ n ∈ S, w n * fourByTwo_E n x * (2 * Real.pi * Complex.I * (n k : ℂ)) := by
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, fourByTwo_θ_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
  simp only [Pi.single_eq_same, mul_one]
  push_cast
  ring

theorem fourByTwo_tp_lipschitz (S : Finset (Fin 2 → ℤ)) (w : (Fin 2 → ℤ) → ℂ) :
    LipschitzWith (∑ n ∈ S, ‖w n‖₊ * ‖fourByTwo_θ n‖₊) (fourByTwo_tp S w) := by
  refine lipschitzWith_iff_dist_le_mul.mpr fun x y => ?_
  rw [dist_eq_norm, fourByTwo_tp, fourByTwo_tp, ← Finset.sum_sub_distrib]
  push_cast
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [← mul_sub, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact fourByTwo_dist_E n x y)
    (norm_nonneg _)

theorem fourByTwo_tp_periodic (S : Finset (Fin 2 → ℤ)) (w : (Fin 2 → ℤ) → ℂ)
    (x : Fin 2 → ℝ) (z : Fin 2 → ℤ) :
    fourByTwo_tp S w (x + fun i => (z i : ℝ)) = fourByTwo_tp S w x := by
  simp only [fourByTwo_tp, fourByTwo_E_periodic]

/-- The frequency `ξ = n₀ + i n₁ ∈ ℂ` of `n ∈ ℤ²` (as in `torusBeurlingPow`). -/
noncomputable def fourByTwo_ξ (n : Fin 2 → ℤ) : ℂ := (n 0 : ℂ) + (n 1 : ℂ) * Complex.I

theorem fourByTwo_conj_ξ (n : Fin 2 → ℤ) :
    starRingEnd ℂ (fourByTwo_ξ n) = (n 0 : ℂ) - (n 1 : ℂ) * Complex.I := by
  simp [fourByTwo_ξ, sub_eq_add_neg]

theorem fourByTwo_ξ_eq_zero {n : Fin 2 → ℤ} (h : fourByTwo_ξ n = 0) : n = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [fourByTwo_ξ] at h1 h2
  funext i
  fin_cases i <;> simp [h1, h2]

/-- The test map of the proof of Proposition 7.2: `u = (u₀, …, u_N)`, `u_j = Σ_{n ∈ S} w_j (n) e_n`,
as a map `ℝ² → ℝ^{2(N+1)}` (row `2j` is `Re u_j`, row `2j + 1` is `Im u_j`). -/
noncomputable def fourByTwo_testMap (N : ℕ) (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) (x : Fin 2 → ℝ) : Fin (2 * (N + 1)) → ℝ :=
  fun r => if r.val % 2 = 0 then (fourByTwo_tp S (w (r.val / 2)) x).re
    else (fourByTwo_tp S (w (r.val / 2)) x).im

/-- The partial derivative `∂_k u (x) = Σ w_n e_n (x) 2πi n_k`. -/
noncomputable def fourByTwo_pd (S : Finset (Fin 2 → ℤ)) (w : (Fin 2 → ℤ) → ℂ) (x : Fin 2 → ℝ)
    (k : Fin 2) : ℂ :=
  ∑ n ∈ S, w n * fourByTwo_E n x * (2 * Real.pi * Complex.I * (n k : ℂ))

theorem fourByTwo_jac_testMap {N : ℕ} (S : Finset (Fin 2 → ℤ)) (w : ℕ → (Fin 2 → ℤ) → ℂ)
    (x : Fin 2 → ℝ) (j : Fin (N + 1)) (k : Fin 2) :
    jac (fourByTwo_testMap N S w) x (rowBlock j 0) k = (fourByTwo_pd S (w j) x k).re ∧
      jac (fourByTwo_testMap N S w) x (rowBlock j 1) k = (fourByTwo_pd S (w j) x k).im := by
  have h0 : (fun y => fourByTwo_testMap N S w y (rowBlock j 0)) =
      fun y => Complex.reCLM (fourByTwo_tp S (w j) y) := by
    funext y
    simp [fourByTwo_testMap, rowBlock]
  have h1 : (fun y => fourByTwo_testMap N S w y (rowBlock j 1)) =
      fun y => Complex.imCLM (fourByTwo_tp S (w j) y) := by
    funext y
    have e1 : (2 * j.val + 1) % 2 = 1 := by omega
    have e2 : (2 * j.val + 1) / 2 = j.val := by omega
    simp [fourByTwo_testMap, rowBlock, e1, e2]
  have hD := fourByTwo_tp_hasFDerivAt S (w j) x
  refine ⟨?_, ?_⟩
  · have hc : HasFDerivAt (fun y => Complex.reCLM (fourByTwo_tp S (w j) y))
        (Complex.reCLM.comp _) x := Complex.reCLM.hasFDerivAt.comp x hD
    simp only [jac, Matrix.of_apply]
    rw [h0, hc.fderiv, ContinuousLinearMap.comp_apply, fourByTwo_tp_partial]
    rfl
  · have hc : HasFDerivAt (fun y => Complex.imCLM (fourByTwo_tp S (w j) y))
        (Complex.imCLM.comp _) x := Complex.imCLM.hasFDerivAt.comp x hD
    simp only [jac, Matrix.of_apply]
    rw [h1, hc.fderiv, ContinuousLinearMap.comp_apply, fourByTwo_tp_partial]
    rfl

/-- `α_j (∇u) = ∂u_j = Σ w_j (n) π i ξ̄_n e_n` and `β_j (∇u) = ∂̄u_j = Σ w_j (n) π i ξ_n e_n`. -/
theorem fourByTwo_alpha_beta_testMap {N : ℕ} (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) (x : Fin 2 → ℝ) (j : Fin (N + 1)) :
    alphaRow (jac (fourByTwo_testMap N S w) x) j = ∑ n ∈ S, w j n *
        (Real.pi * Complex.I * starRingEnd ℂ (fourByTwo_ξ n)) * fourByTwo_E n x ∧
      betaRow (jac (fourByTwo_testMap N S w) x) j = ∑ n ∈ S, w j n *
        (Real.pi * Complex.I * fourByTwo_ξ n) * fourByTwo_E n x := by
  obtain ⟨h00, h10⟩ := fourByTwo_jac_testMap (N := N) S w x j 0
  obtain ⟨h01, h11⟩ := fourByTwo_jac_testMap (N := N) S w x j 1
  have hα : alphaRow (jac (fourByTwo_testMap N S w) x) j =
      (fourByTwo_pd S (w j) x 0 - Complex.I * fourByTwo_pd S (w j) x 1) / 2 := by
    rw [alphaRow, h00, h10, h01, h11]
    apply Complex.ext <;> simp
  have hβ : betaRow (jac (fourByTwo_testMap N S w) x) j =
      (fourByTwo_pd S (w j) x 0 + Complex.I * fourByTwo_pd S (w j) x 1) / 2 := by
    rw [betaRow, h00, h10, h01, h11]
    apply Complex.ext <;> simp; ring
  refine ⟨?_, ?_⟩
  · rw [hα, fourByTwo_pd, fourByTwo_pd, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [fourByTwo_conj_ξ]
    ring_nf
  · rw [hβ, fourByTwo_pd, fourByTwo_pd, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [fourByTwo_ξ]
    ring_nf

/-- The coefficients of `u_j` in the proof of Proposition 7.2, solving `∂̄u_j = h_j + ρ ∂u_{j−1}`
(`∂u_{−1} = 0`) frequency by frequency (`∂̄` has the symbol `π i ξ`, `∂` the symbol `π i ξ̄`, and
`∂̄` is invertible on mean-zero functions): `û_j (n) = ĥ_j (n) / (π i ξ_n) + ρ m (ξ_n) û_{j−1} (n)`,
with `m (ξ) = ξ̄ / ξ`. -/
noncomputable def fourByTwo_uCoeff (ρ : ℝ) (hc : ℕ → (Fin 2 → ℤ) → ℂ) :
    ℕ → (Fin 2 → ℤ) → ℂ
  | 0 => fun n => hc 0 n / (Real.pi * Complex.I * fourByTwo_ξ n)
  | j + 1 => fun n => hc (j + 1) n / (Real.pi * Complex.I * fourByTwo_ξ n) +
      ρ * beurlingSymbol (fourByTwo_ξ n) * fourByTwo_uCoeff ρ hc j n

theorem fourByTwo_piIξ_ne {n : Fin 2 → ℤ} (h : fourByTwo_ξ n ≠ 0) :
    (Real.pi : ℂ) * Complex.I * fourByTwo_ξ n ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero) h

/-- The recursion `∂̄u₀ = h₀`, `∂̄u_{j+1} = h_{j+1} + ρ ∂u_j` at the frequency `n ≠ 0`. -/
theorem fourByTwo_uCoeff_rec (ρ : ℝ) (hc : ℕ → (Fin 2 → ℤ) → ℂ) {n : Fin 2 → ℤ}
    (h : fourByTwo_ξ n ≠ 0) :
    (Real.pi * Complex.I * fourByTwo_ξ n) * fourByTwo_uCoeff ρ hc 0 n = hc 0 n ∧
      ∀ j, (Real.pi * Complex.I * fourByTwo_ξ n) * fourByTwo_uCoeff ρ hc (j + 1) n =
        hc (j + 1) n + ρ * (Real.pi * Complex.I * starRingEnd ℂ (fourByTwo_ξ n)) *
          fourByTwo_uCoeff ρ hc j n := by
  have hne := fourByTwo_piIξ_ne h
  refine ⟨?_, fun j => ?_⟩
  · simp only [fourByTwo_uCoeff]
    field_simp
  · simp only [fourByTwo_uCoeff, beurlingSymbol]
    field_simp

/-- `∂u_j = Σ_{i ≤ j} ρ^{j−i} 𝓑^{j+1−i} h_i` at the frequency `n` (the induction of the proof of
Proposition 7.2, from `𝓑 (∂̄w) = ∂w`). -/
theorem fourByTwo_uCoeff_closed (ρ : ℝ) (hc : ℕ → (Fin 2 → ℤ) → ℂ) (n : Fin 2 → ℤ) (j : ℕ) :
    (Real.pi * Complex.I * starRingEnd ℂ (fourByTwo_ξ n)) * fourByTwo_uCoeff ρ hc j n =
      ∑ i ∈ Finset.range (j + 1), (ρ : ℂ) ^ (j - i) *
        beurlingSymbol (fourByTwo_ξ n) ^ (j + 1 - i) * hc i n := by
  by_cases h : fourByTwo_ξ n = 0
  · rw [h, map_zero, mul_zero, zero_mul]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    rw [Finset.mem_range] at hi
    rw [beurlingSymbol, map_zero, zero_div, zero_pow (by omega), mul_zero, zero_mul]
  · have hne := fourByTwo_piIξ_ne h
    have hm : (Real.pi * Complex.I * starRingEnd ℂ (fourByTwo_ξ n)) =
        beurlingSymbol (fourByTwo_ξ n) * (Real.pi * Complex.I * fourByTwo_ξ n) := by
      rw [beurlingSymbol]; field_simp
    induction j with
    | zero =>
      rw [hm, mul_assoc, (fourByTwo_uCoeff_rec ρ hc h).1]
      simp
    | succ j ih =>
      rw [hm, mul_assoc, (fourByTwo_uCoeff_rec ρ hc h).2 j, Finset.sum_range_succ,
        Nat.sub_self, pow_zero, one_mul, show j + 1 + 1 - (j + 1) = 1 by omega, pow_one,
        mul_assoc (ρ : ℂ), ih]
      have hs : beurlingSymbol (fourByTwo_ξ n) * ((ρ : ℂ) * ∑ i ∈ Finset.range (j + 1),
          (ρ : ℂ) ^ (j - i) * beurlingSymbol (fourByTwo_ξ n) ^ (j + 1 - i) * hc i n) =
          ∑ i ∈ Finset.range (j + 1), (ρ : ℂ) ^ (j + 1 - i) *
            beurlingSymbol (fourByTwo_ξ n) ^ (j + 1 + 1 - i) * hc i n := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [show j + 1 + 1 - i = (j - i) + 2 by omega, show j + 1 - i = (j - i) + 1 by omega,
          pow_add, pow_add]
        ring
      rw [mul_add, hs]
      ring

/-- The coefficients `ĥ_j (n)` of the tuple `c`, extended by `0` to all `j ∈ ℕ`. -/
noncomputable def fourByTwo_hc {N : ℕ} (c : Fin (N + 1) → (Fin 2 → ℤ) →₀ ℂ) (i : ℕ)
    (n : Fin 2 → ℤ) : ℂ :=
  if h : i < N + 1 then c ⟨i, h⟩ n else 0

/-- The frequencies of the tuple `c`. -/
noncomputable def fourByTwo_supp {N : ℕ} (c : Fin (N + 1) → (Fin 2 → ℤ) →₀ ℂ) :
    Finset (Fin 2 → ℤ) :=
  Finset.univ.biUnion fun j => (c j).support

theorem fourByTwo_support_subset {N : ℕ} (c : Fin (N + 1) → (Fin 2 → ℤ) →₀ ℂ)
    (j : Fin (N + 1)) : (c j).support ⊆ fourByTwo_supp c :=
  Finset.subset_biUnion_of_mem (fun j => (c j).support) (Finset.mem_univ j)

/-- The projection `ℝ² → 𝕋²`. -/
def fourByTwo_proj (x : Fin 2 → ℝ) : UnitAddTorus (Fin 2) := fun i => (x i : UnitAddCircle)

theorem fourByTwo_continuous_proj : Continuous fourByTwo_proj :=
  continuous_pi fun i => (AddCircle.continuous_mk' 1).comp (continuous_apply i)

theorem fourByTwo_trigPoly_eq {N : ℕ} (c : Fin (N + 1) → (Fin 2 → ℤ) →₀ ℂ) (j : Fin (N + 1))
    (x : Fin 2 → ℝ) :
    trigPoly (c j) (fourByTwo_proj x) = ∑ n ∈ fourByTwo_supp c, c j n * fourByTwo_E n x := by
  rw [trigPoly, Finsupp.sum_of_support_subset (c j) (fourByTwo_support_subset c j)
    (fun n a => a * UnitAddTorus.mFourier n (fourByTwo_proj x)) fun n _ => zero_mul _]
  exact Finset.sum_congr rfl fun n _ => by rw [fourByTwo_E_eq]; rfl

theorem fourByTwo_torusBeurlingPow_eq {N : ℕ} (c : Fin (N + 1) → (Fin 2 → ℤ) →₀ ℂ)
    (j : Fin (N + 1)) (k : ℕ) (x : Fin 2 → ℝ) :
    torusBeurlingPow k (c j) (fourByTwo_proj x) = ∑ n ∈ fourByTwo_supp c,
      beurlingSymbol (fourByTwo_ξ n) ^ k * c j n * fourByTwo_E n x := by
  rw [torusBeurlingPow, Finsupp.sum_of_support_subset _ (fourByTwo_support_subset c j) _
    fun n _ => by simp]
  exact Finset.sum_congr rfl fun n _ => by rw [fourByTwo_E_eq]; rfl

/-- `P_ρ (∇u) = (h₀, …, h_N)` for the test map built from a mean-zero tuple `c` (proof of
Proposition 7.2). -/
theorem fourByTwo_chainP_testMap {N : ℕ} (ρ : ℝ) (c : Fin (N + 1) → (Fin 2 → ℤ) →₀ ℂ)
    (hc0 : ∀ j, c j 0 = 0) (x : Fin 2 → ℝ) (j : Fin (N + 1)) :
    chainP ρ (jac (fourByTwo_testMap N (fourByTwo_supp c)
        (fourByTwo_uCoeff ρ (fourByTwo_hc c))) x) j = trigPoly (c j) (fourByTwo_proj x) := by
  set w := fourByTwo_uCoeff ρ (fourByTwo_hc c) with hw
  rw [fourByTwo_trigPoly_eq]
  have hzero : ∀ n, fourByTwo_ξ n = 0 → c j n = 0 := fun n h => by
    rw [fourByTwo_ξ_eq_zero h]; exact hc0 j
  unfold chainP
  split_ifs with hj
  · rw [(fourByTwo_alpha_beta_testMap (N := N) _ w x j).2]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hξ : fourByTwo_ξ n = 0
    · rw [hzero n hξ, hξ]; ring
    · have := (fourByTwo_uCoeff_rec ρ (fourByTwo_hc c) hξ).1
      have hj0 : j = ⟨0, Nat.succ_pos N⟩ := Fin.ext hj
      subst hj0
      simp only [fourByTwo_hc, Nat.succ_pos N, ↓reduceDIte] at this
      rw [hw, mul_comm (fourByTwo_uCoeff ρ (fourByTwo_hc c) _ n)]
      exact congrArg (· * fourByTwo_E n x) this
  · rw [(fourByTwo_alpha_beta_testMap (N := N) _ w x j).2,
      (fourByTwo_alpha_beta_testMap (N := N) _ w x ⟨j.val - 1, by omega⟩).1, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hξ : fourByTwo_ξ n = 0
    · rw [hzero n hξ, hξ, map_zero]; ring
    · have := (fourByTwo_uCoeff_rec ρ (fourByTwo_hc c) hξ).2 (j.val - 1)
      rw [show j.val - 1 + 1 = j.val by omega] at this
      simp only [fourByTwo_hc, j.isLt, ↓reduceDIte] at this
      have hw' : w j n * (Real.pi * Complex.I * fourByTwo_ξ n) =
          c j n + ρ * (Real.pi * Complex.I * starRingEnd ℂ (fourByTwo_ξ n)) * w (j.val - 1) n := by
        rw [hw, mul_comm, this]
      rw [hw']
      ring

/-- `Q (∇u) = ∂u_N = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j` for the test map (proof of Proposition 7.2). -/
theorem fourByTwo_chainQ_testMap {N : ℕ} (ρ : ℝ) (c : Fin (N + 1) → (Fin 2 → ℤ) →₀ ℂ)
    (x : Fin 2 → ℝ) :
    chainQ (jac (fourByTwo_testMap N (fourByTwo_supp c)
        (fourByTwo_uCoeff ρ (fourByTwo_hc c))) x) =
      ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
        torusBeurlingPow (N + 1 - j.val) (c j) (fourByTwo_proj x) := by
  rw [chainQ, (fourByTwo_alpha_beta_testMap (N := N) _ _ x (Fin.last N)).1]
  simp only [Fin.val_last]
  have h1 : ∀ n, fourByTwo_uCoeff ρ (fourByTwo_hc c) N n *
      (Real.pi * Complex.I * starRingEnd ℂ (fourByTwo_ξ n)) * fourByTwo_E n x =
      ∑ i ∈ Finset.range (N + 1), (ρ : ℂ) ^ (N - i) *
        (beurlingSymbol (fourByTwo_ξ n) ^ (N + 1 - i) * fourByTwo_hc c i n * fourByTwo_E n x) :=
    fun n => by
      rw [mul_comm (fourByTwo_uCoeff _ _ _ _), fourByTwo_uCoeff_closed, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [h1]
  rw [Finset.sum_comm, ← Fin.sum_univ_eq_sum_range (fun i => ∑ n ∈ fourByTwo_supp c,
    (ρ : ℂ) ^ (N - i) * (beurlingSymbol (fourByTwo_ξ n) ^ (N + 1 - i) * fourByTwo_hc c i n *
      fourByTwo_E n x)) (N + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fourByTwo_torusBeurlingPow_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [fourByTwo_hc, j.isLt, ↓reduceDIte, Fin.eta]
  push_cast
  ring

/-! ### Proposition 7.2: the torus and the unit cube -/

/-- Integrals over the torus `𝕋² = ℝ² / ℤ²` (normalised Haar measure) are integrals of the lifts
over the unit cube. -/
theorem fourByTwo_lintegral_torus (f : UnitAddTorus (Fin 2) → ℝ≥0∞) :
    ∫⁻ z, f z = ∫⁻ x in unitCube 2, f (fourByTwo_proj x) := by
  have hvol : (volume : Measure (UnitAddTorus (Fin 2))) =
      @volume _ (@MeasureSpace.pi (Fin 2) _ (fun _ => UnitAddCircle)
        fun _ => instMeasureSpaceUnitAddCircle) := by
    show Measure.pi (fun _ => (volume : Measure UnitAddCircle)) =
      Measure.pi (fun _ => AddCircle.haarAddCircle)
    congr 1
    funext i
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hvol, UnitAddTorus.lintegral_preimage f 0]
  have h1 : {x : Fin 2 → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i + 1)} =
      Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1 := by
    ext x; simp
  rw [h1, unitCube]
  exact setLIntegral_congr (Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ioo_ae_eq_Icc.symm)

theorem fourByTwo_integrableOn_cube {g : (Fin 2 → ℝ) → ℝ} (hg : Continuous g) :
    IntegrableOn g (unitCube 2) :=
  (hg.integrableOn_Icc (a := 0) (b := 1)).mono_set fun _ hx =>
    ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩

/-- `‖F‖_{L^p (𝕋²)} = (∫_{(0,1)²} ‖F (x)‖^p dx)^{1/p}` for continuous `F`. -/
theorem fourByTwo_eLpNorm_torus {E : Type*} [NormedAddCommGroup E]
    {F : UnitAddTorus (Fin 2) → E} (hF : Continuous F) {p : ℝ} (hp : 0 < p) :
    eLpNorm F (ENNReal.ofReal p) volume =
      ENNReal.ofReal ((∫ x in unitCube 2, ‖F (fourByTwo_proj x)‖ ^ p) ^ (1 / p)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    hF.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le, fourByTwo_lintegral_torus]
  have hc : Continuous fun x => ‖F (fourByTwo_proj x)‖ ^ p :=
    (hF.comp fourByTwo_continuous_proj).norm.rpow_const fun _ => Or.inr hp.le
  have hnn : 0 ≤ ∫ x in unitCube 2, ‖F (fourByTwo_proj x)‖ ^ p :=
    setIntegral_nonneg (by simp [unitCube, MeasurableSet.univ_pi, measurableSet_Ioo])
      fun x _ => by positivity
  rw [← ENNReal.ofReal_rpow_of_nonneg hnn (by positivity),
    ofReal_integral_eq_lintegral_ofReal (fourByTwo_integrableOn_cube hc)
      (ae_of_all _ fun x => by positivity)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]

theorem fourByTwo_continuous_trigPoly (c : (Fin 2 → ℤ) →₀ ℂ) : Continuous (trigPoly c) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (UnitAddTorus.mFourier n).continuous

theorem fourByTwo_continuous_torusBeurlingPow (k : ℕ) (c : (Fin 2 → ℤ) →₀ ℂ) :
    Continuous (torusBeurlingPow k c) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (UnitAddTorus.mFourier n).continuous

theorem fourByTwo_isLocallyBounded {d m : ℕ} {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Continuous f) : CalculusOfVariations.IsLocallyBounded f := by
  intro A
  refine ⟨f ⁻¹' Metric.ball (f A) 1, hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _
    one_pos), |f A| + 1, fun B hB => ?_⟩
  have := abs_sub_abs_le_abs_sub (f B) (f A)
  rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hB
  linarith

/-- The test map is Lipschitz. -/
theorem fourByTwo_testMap_lipschitz (N : ℕ) (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) : ∃ K, LipschitzWith K (fourByTwo_testMap N S w) := by
  set K : NNReal := ∑ j ∈ Finset.range (2 * (N + 1)), ∑ n ∈ S, ‖w j n‖₊ * ‖fourByTwo_θ n‖₊
  refine ⟨K, lipschitzWith_iff_dist_le_mul.mpr fun x y => ?_⟩
  refine (dist_pi_le_iff (by positivity)).mpr fun r => ?_
  have hj : r.val / 2 ∈ Finset.range (2 * (N + 1)) := by
    rw [Finset.mem_range]; omega
  have hK : (∑ n ∈ S, ‖w (r.val / 2) n‖₊ * ‖fourByTwo_θ n‖₊ : NNReal) ≤ K :=
    Finset.single_le_sum (f := fun j => ∑ n ∈ S, ‖w j n‖₊ * ‖fourByTwo_θ n‖₊)
      (fun _ _ => zero_le) hj
  have htp := lipschitzWith_iff_dist_le_mul.mp (fourByTwo_tp_lipschitz S (w (r.val / 2))) x y
  have hle : dist (fourByTwo_testMap N S w x r) (fourByTwo_testMap N S w y r) ≤
      dist (fourByTwo_tp S (w (r.val / 2)) x) (fourByTwo_tp S (w (r.val / 2)) y) := by
    simp only [fourByTwo_testMap]
    rw [dist_eq_norm, dist_eq_norm]
    split_ifs
    · rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    · rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  refine hle.trans (htp.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg))
  exact_mod_cast hK

theorem fourByTwo_testMap_periodic (N : ℕ) (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) (x : Fin 2 → ℝ) (z : Fin 2 → ℤ) :
    fourByTwo_testMap N S w (x + fun i => (z i : ℝ)) = fourByTwo_testMap N S w x := by
  funext r
  simp only [fourByTwo_testMap, fourByTwo_tp_periodic]

/-- The inequality `C^{qc} (p, N, ρ) ≥ ‖(ρ^N 𝓑^{N+1}, …, ρ 𝓑², 𝓑)‖_{L^p_0 (𝕋²; ℓ₂^{N+1}) →
L^p_0 (𝕋²)}` of Proposition 7.2, by the paper's argument ("conversely, every smooth mean-zero
tuple is obtained by solving recursively …", TeX lines 2822–2832), for the mean-zero
trigonometric polynomials of the definition of `chainOpNorm`: every mean-zero tuple `(h_j)` of
trigonometric polynomials is `P_ρ (∇u)` for the periodic `u` obtained by solving
`∂̄u_j = h_j + ρ ∂u_{j−1}`, and then `Q (∇u) = ∂u_N = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j`;
quasiconvexity at `0`, tested with periodic maps
(Lemma 2.2, `External.Rindler.quasiconvexAtOn_iff_periodic`), gives
`‖Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j‖_p ≤ C ‖(h_j)‖_p`. -/
theorem fourByTwo_chainOpNorm_le_qcThreshold (N : ℕ) (ρ : ℝ) {p : ℝ} (hp : 1 < p) :
    chainOpNorm N p ρ ≤ qcThreshold (chainF N p ρ) := by
  have hp0 : 0 < p := by linarith
  refine le_iInf₂ fun C hC => iSup₂_le fun c hc0 => ?_
  obtain ⟨hC0, hqc⟩ := hC
  -- Lemma 2.2: quasiconvexity at `0` with periodic test maps
  have hcont := fourByTwo_continuous_chainF N hp0.le ρ C
  have hper : CalculusOfVariations.QuasiconvexAtPeriodic (chainF N p ρ C) 0 :=
    (External.Rindler.quasiconvexAtOn_iff_periodic hcont.lowerSemicontinuous
      (fourByTwo_isLocallyBounded hcont) 0).mp
      ((cov_quasiconvexAtOn_unitCube_iff _ _).mpr hqc)
  set φ := fourByTwo_testMap N (fourByTwo_supp c) (fourByTwo_uCoeff ρ (fourByTwo_hc c)) with hφ
  obtain ⟨K, hK⟩ := fourByTwo_testMap_lipschitz N (fourByTwo_supp c)
    (fourByTwo_uCoeff ρ (fourByTwo_hc c))
  have key := hper φ K hK (fourByTwo_testMap_periodic _ _ _)
    (fourByTwo_integrableOn_comp_jac hcont hK)
  -- the integrand is `C^p ‖(h_j)‖^p − |Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j|^p`
  set h : UnitAddTorus (Fin 2) → ℝ := fun z => √(∑ j, ‖trigPoly (c j) z‖ ^ 2) with hh
  set T : UnitAddTorus (Fin 2) → ℂ := fun z => ∑ j : Fin (N + 1),
    ((ρ ^ (N - j.val) : ℝ) : ℂ) * torusBeurlingPow (N + 1 - j.val) (c j) z with hT
  have hpt : ∀ x, chainF N p ρ C (0 + CalculusOfVariations.grad φ x) =
      C ^ p * ‖h (fourByTwo_proj x)‖ ^ p - ‖T (fourByTwo_proj x)‖ ^ p := by
    intro x
    rw [zero_add, grad_eq, chainF, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simp only [hφ, fourByTwo_chainP_testMap ρ c hc0, fourByTwo_chainQ_testMap, hT]
  simp only [hpt] at key
  rw [fourByTwo_chainF_zero N hp0] at key
  have hcT : Continuous T := continuous_finsetSum _ fun j _ =>
    continuous_const.mul (fourByTwo_continuous_torusBeurlingPow _ _)
  have hch : Continuous h := Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
    ((fourByTwo_continuous_trigPoly (c j)).norm.pow 2))
  have iT : IntegrableOn (fun x => ‖T (fourByTwo_proj x)‖ ^ p) (unitCube 2) :=
    fourByTwo_integrableOn_cube ((hcT.comp fourByTwo_continuous_proj).norm.rpow_const
      fun _ => Or.inr hp0.le)
  have ih : IntegrableOn (fun x => ‖h (fourByTwo_proj x)‖ ^ p) (unitCube 2) :=
    fourByTwo_integrableOn_cube ((hch.comp fourByTwo_continuous_proj).norm.rpow_const
      fun _ => Or.inr hp0.le)
  rw [unitCube_eq_cov] at key
  rw [integral_sub (ih.const_mul _) iT, integral_const_mul, sub_nonneg] at key
  -- back to `L^p (𝕋²)` norms
  refine ENNReal.div_le_of_le_mul ?_
  rw [fourByTwo_eLpNorm_torus hcT hp0, fourByTwo_eLpNorm_torus hch hp0,
    ← ENNReal.ofReal_mul hC0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnn : 0 ≤ ∫ x in unitCube 2, ‖h (fourByTwo_proj x)‖ ^ p :=
    setIntegral_nonneg (by simp [unitCube, MeasurableSet.univ_pi, measurableSet_Ioo])
      fun x _ => by positivity
  have hnnT : 0 ≤ ∫ x in unitCube 2, ‖T (fourByTwo_proj x)‖ ^ p :=
    setIntegral_nonneg (by simp [unitCube, MeasurableSet.univ_pi, measurableSet_Ioo])
      fun x _ => by positivity
  calc (∫ x in unitCube 2, ‖T (fourByTwo_proj x)‖ ^ p) ^ (1 / p)
      ≤ (C ^ p * ∫ x in unitCube 2, ‖h (fourByTwo_proj x)‖ ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow hnnT key (by positivity)
    _ = C * (∫ x in unitCube 2, ‖h (fourByTwo_proj x)‖ ^ p) ^ (1 / p) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hC0 _) hnn, one_div,
          Real.rpow_rpow_inv hC0 hp0.ne']

/-! ### Proposition 7.2: the identity `Q (∇u) = Σ_j ρ^{N−j} 𝓑^{N+1−j} P_ρ (∇u)_j`

The paper's first claim (TeX lines 2808–2821), for every trigonometric test map
`u = fourByTwo_testMap N S w`: with `h_j = P_ρ (∇u)_j = ∂̄u_j − ρ ∂u_{j−1}` (`∂u_{−1} = 0`),
`Q (∇u) = ∂u_N = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j`, by induction from `𝓑 (∂̄w) = ∂w`. At the frequency
`n`, `∂̄` has the symbol `π i ξ_n` and `∂` the symbol `π i ξ̄_n`
(`fourByTwo_alpha_beta_testMap`). -/

/-- `ĥ_j (n) = π i ξ_n ŵ_j (n) − ρ π i ξ̄_n ŵ_{j−1} (n)` (no second term for `j = 0`). -/
noncomputable def fourByTwo_hVal (ρ : ℝ) (w : ℕ → (Fin 2 → ℤ) → ℂ) (j : ℕ) (n : Fin 2 → ℤ) : ℂ :=
  Real.pi * Complex.I * fourByTwo_ξ n * w j n -
    if j = 0 then 0 else (ρ : ℂ) * (Real.pi * Complex.I * starRingEnd ℂ (fourByTwo_ξ n) * w (j - 1) n)

/-- The coefficients of `h_j = P_ρ (∇u)_j` for the test map `u = fourByTwo_testMap N S w`, as a
finitely supported function. -/
noncomputable def fourByTwo_hOf (N : ℕ) (ρ : ℝ) (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) (j : Fin (N + 1)) : (Fin 2 → ℤ) →₀ ℂ :=
  Finsupp.onFinset S (fun n => if n ∈ S then fourByTwo_hVal ρ w j.val n else 0)
    fun n hn => by by_contra h; exact hn (ite_eq_right h)

theorem fourByTwo_hOf_apply (N : ℕ) (ρ : ℝ) (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) (j : Fin (N + 1)) (n : Fin 2 → ℤ) :
    fourByTwo_hOf N ρ S w j n = if n ∈ S then fourByTwo_hVal ρ w j.val n else 0 :=
  Finsupp.onFinset_apply

theorem fourByTwo_ξ_zero : fourByTwo_ξ 0 = 0 := by simp [fourByTwo_ξ]

/-- The tuple `(h_j)` has mean zero. -/
theorem fourByTwo_hOf_zero (N : ℕ) (ρ : ℝ) (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) (j : Fin (N + 1)) : fourByTwo_hOf N ρ S w j 0 = 0 := by
  rw [fourByTwo_hOf_apply]
  split_ifs <;> simp [fourByTwo_hVal, fourByTwo_ξ_zero]

theorem fourByTwo_trigPoly_hOf (N : ℕ) (ρ : ℝ) (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) (j : Fin (N + 1)) (x : Fin 2 → ℝ) :
    trigPoly (fourByTwo_hOf N ρ S w j) (fourByTwo_proj x) =
      ∑ n ∈ S, fourByTwo_hVal ρ w j.val n * fourByTwo_E n x := by
  rw [trigPoly, fourByTwo_hOf, Finsupp.onFinset_sum _ fun n => zero_mul _]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [ite_eq_left hn, fourByTwo_E_eq]; rfl

theorem fourByTwo_torusBeurlingPow_hOf (N : ℕ) (ρ : ℝ) (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) (j : Fin (N + 1)) (k : ℕ) (x : Fin 2 → ℝ) :
    torusBeurlingPow k (fourByTwo_hOf N ρ S w j) (fourByTwo_proj x) =
      ∑ n ∈ S, beurlingSymbol (fourByTwo_ξ n) ^ k * fourByTwo_hVal ρ w j.val n *
        fourByTwo_E n x := by
  rw [torusBeurlingPow, fourByTwo_hOf, Finsupp.onFinset_sum _ fun n => by simp]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [ite_eq_left hn, fourByTwo_E_eq]; rfl

/-- `P_ρ (∇u)_j = h_j` for every trigonometric test map `u`. -/
theorem fourByTwo_chainP_eq_hOf {N : ℕ} (ρ : ℝ) (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) (x : Fin 2 → ℝ) (j : Fin (N + 1)) :
    chainP ρ (jac (fourByTwo_testMap N S w) x) j =
      trigPoly (fourByTwo_hOf N ρ S w j) (fourByTwo_proj x) := by
  rw [fourByTwo_trigPoly_hOf]
  unfold chainP
  split_ifs with hj
  · rw [(fourByTwo_alpha_beta_testMap (N := N) S w x j).2]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [fourByTwo_hVal, hj, ↓reduceIte, sub_zero]
    ring
  · rw [(fourByTwo_alpha_beta_testMap (N := N) S w x j).2,
      (fourByTwo_alpha_beta_testMap (N := N) S w x ⟨j.val - 1, by omega⟩).1, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [fourByTwo_hVal, hj, ↓reduceIte]
    ring

/-- The induction of the proof of Proposition 7.2 at one frequency: with `m a_j = b_j`
(`𝓑 (∂̄u_j) = ∂u_j`), `c₀ = a₀` and `c_j = a_j − ρ b_{j−1}`,
`Σ_{j ≤ K} ρ^{K−j} m^{K+1−j} c_j = b_K`. -/
theorem fourByTwo_telescope (ρ m : ℂ) (a b : ℕ → ℂ) (hab : ∀ j, m * a j = b j) (K : ℕ) :
    ∑ j ∈ Finset.range (K + 1), ρ ^ (K - j) * m ^ (K + 1 - j) *
      (a j - if j = 0 then 0 else ρ * b (j - 1)) = b K := by
  induction K with
  | zero => simp [hab]
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have h1 : ∑ j ∈ Finset.range (K + 1), ρ ^ (K + 1 - j) * m ^ (K + 1 + 1 - j) *
        (a j - if j = 0 then 0 else ρ * b (j - 1)) =
        ρ * m * ∑ j ∈ Finset.range (K + 1), ρ ^ (K - j) * m ^ (K + 1 - j) *
          (a j - if j = 0 then 0 else ρ * b (j - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show K + 1 + 1 - j = (K - j) + 2 by omega, show K + 1 - j = (K - j) + 1 by omega,
        pow_add, pow_add]
      ring
    rw [h1, ih, Nat.sub_self, pow_zero, one_mul, show K + 1 + 1 - (K + 1) = 1 by omega, pow_one,
      ite_eq_right (Nat.succ_ne_zero K), Nat.add_sub_cancel, ← hab (K + 1)]
    ring

/-- `m (ξ) · π i ξ = π i ξ̄`, that is, `𝓑 ∂̄ = ∂` at every frequency (also at `ξ = 0`). -/
theorem fourByTwo_beurlingSymbol_mul (ξ : ℂ) :
    beurlingSymbol ξ * (Real.pi * Complex.I * ξ) = Real.pi * Complex.I * starRingEnd ℂ ξ := by
  by_cases h : ξ = 0
  · simp [h, beurlingSymbol]
  · rw [beurlingSymbol]; field_simp

/-- `Q (∇u) = ∂u_N = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j` for every trigonometric test map `u`. -/
theorem fourByTwo_chainQ_eq_hOf {N : ℕ} (ρ : ℝ) (S : Finset (Fin 2 → ℤ))
    (w : ℕ → (Fin 2 → ℤ) → ℂ) (x : Fin 2 → ℝ) :
    chainQ (jac (fourByTwo_testMap N S w) x) =
      ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
        torusBeurlingPow (N + 1 - j.val) (fourByTwo_hOf N ρ S w j) (fourByTwo_proj x) := by
  rw [chainQ, (fourByTwo_alpha_beta_testMap (N := N) S w x (Fin.last N)).1]
  simp only [Fin.val_last, fourByTwo_torusBeurlingPow_hOf, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have ht := fourByTwo_telescope (ρ : ℂ) (beurlingSymbol (fourByTwo_ξ n))
    (fun j => Real.pi * Complex.I * fourByTwo_ξ n * w j n)
    (fun j => Real.pi * Complex.I * starRingEnd ℂ (fourByTwo_ξ n) * w j n)
    (fun j => by rw [← mul_assoc, fourByTwo_beurlingSymbol_mul]) N
  rw [Fin.sum_univ_eq_sum_range (fun j => ((ρ ^ (N - j) : ℝ) : ℂ) *
    (beurlingSymbol (fourByTwo_ξ n) ^ (N + 1 - j) * fourByTwo_hVal ρ w j n * fourByTwo_E n x))
    (N + 1)]
  have e : ∀ j ∈ Finset.range (N + 1), ((ρ ^ (N - j) : ℝ) : ℂ) *
      (beurlingSymbol (fourByTwo_ξ n) ^ (N + 1 - j) * fourByTwo_hVal ρ w j n * fourByTwo_E n x) =
      ((ρ : ℂ) ^ (N - j) * beurlingSymbol (fourByTwo_ξ n) ^ (N + 1 - j) *
        (Real.pi * Complex.I * fourByTwo_ξ n * w j n - if j = 0 then 0 else
          (ρ : ℂ) * (Real.pi * Complex.I * starRingEnd ℂ (fourByTwo_ξ n) * w (j - 1) n))) *
        fourByTwo_E n x := fun j _ => by
    rw [fourByTwo_hVal]; push_cast; ring
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul, ht]
  ring

/-- The inequality `∫_{(0,1)²} f_{p,ρ,C} (∇u) ≥ 0` for every trigonometric test map `u`, with
`C = ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖` (the definition of `chainOpNorm`, applied to the mean-zero tuple
`h = P_ρ (∇u)`, whose image is `Q (∇u)`). -/
theorem fourByTwo_integral_chainF_testMap_nonneg (N : ℕ) (ρ : ℝ) {p : ℝ} (hp : 1 < p)
    (hfin : chainOpNorm N p ρ ≠ ⊤) (S : Finset (Fin 2 → ℤ)) (w : ℕ → (Fin 2 → ℤ) → ℂ) :
    0 ≤ ∫ x in unitCube 2,
      chainF N p ρ (chainOpNorm N p ρ).toReal (jac (fourByTwo_testMap N S w) x) := by
  have hp0 : 0 < p := by linarith
  set K := (chainOpNorm N p ρ).toReal with hKdef
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hK : ENNReal.ofReal K = chainOpNorm N p ρ := ENNReal.ofReal_toReal hfin
  set c := fourByTwo_hOf N ρ S w with hc
  have hc0 : ∀ j, c j 0 = 0 := fun j => fourByTwo_hOf_zero N ρ S w j
  set h : UnitAddTorus (Fin 2) → ℝ := fun z => √(∑ j, ‖trigPoly (c j) z‖ ^ 2) with hh
  set T : UnitAddTorus (Fin 2) → ℂ := fun z => ∑ j : Fin (N + 1),
    ((ρ ^ (N - j.val) : ℝ) : ℂ) * torusBeurlingPow (N + 1 - j.val) (c j) z with hT
  have hpt : ∀ x, chainF N p ρ K (jac (fourByTwo_testMap N S w) x) =
      K ^ p * ‖h (fourByTwo_proj x)‖ ^ p - ‖T (fourByTwo_proj x)‖ ^ p := by
    intro x
    rw [chainF, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simp only [hT, hc, fourByTwo_chainP_eq_hOf ρ S w x, fourByTwo_chainQ_eq_hOf ρ S w x]
  simp only [hpt]
  have hcT : Continuous T := continuous_finsetSum _ fun j _ =>
    continuous_const.mul (fourByTwo_continuous_torusBeurlingPow _ _)
  have hch : Continuous h := Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
    ((fourByTwo_continuous_trigPoly (c j)).norm.pow 2))
  have iT : IntegrableOn (fun x => ‖T (fourByTwo_proj x)‖ ^ p) (unitCube 2) :=
    fourByTwo_integrableOn_cube ((hcT.comp fourByTwo_continuous_proj).norm.rpow_const
      fun _ => Or.inr hp0.le)
  have ih : IntegrableOn (fun x => ‖h (fourByTwo_proj x)‖ ^ p) (unitCube 2) :=
    fourByTwo_integrableOn_cube ((hch.comp fourByTwo_continuous_proj).norm.rpow_const
      fun _ => Or.inr hp0.le)
  rw [integral_sub (ih.const_mul _) iT, integral_const_mul, sub_nonneg]
  -- the definition of `chainOpNorm`, for the mean-zero tuple `c`
  have hratio : eLpNorm T (ENNReal.ofReal p) volume / eLpNorm h (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal K := by
    rw [hK]
    exact le_iSup₂ (f := fun (c : Fin (N + 1) → (Fin 2 → ℤ) →₀ ℂ) (_ : ∀ j, c j 0 = 0) =>
      eLpNorm (fun x => ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
        torusBeurlingPow (N + 1 - j.val) (c j) x) (ENNReal.ofReal p) volume /
      eLpNorm (fun x => √(∑ j, ‖trigPoly (c j) x‖ ^ 2)) (ENNReal.ofReal p) volume) c hc0
  rw [fourByTwo_eLpNorm_torus hcT hp0, fourByTwo_eLpNorm_torus hch hp0,
    ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul hK0] at hratio
  have hnn : 0 ≤ ∫ x in unitCube 2, ‖h (fourByTwo_proj x)‖ ^ p :=
    setIntegral_nonneg (by simp [unitCube, MeasurableSet.univ_pi, measurableSet_Ioo])
      fun x _ => by positivity
  have hnnT : 0 ≤ ∫ x in unitCube 2, ‖T (fourByTwo_proj x)‖ ^ p :=
    setIntegral_nonneg (by simp [unitCube, MeasurableSet.univ_pi, measurableSet_Ioo])
      fun x _ => by positivity
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 (Real.rpow_nonneg hnn _))] at hratio
  have key := Real.rpow_le_rpow (Real.rpow_nonneg hnnT _) hratio hp0.le
  rw [Real.mul_rpow hK0 (Real.rpow_nonneg hnn _), one_div, Real.rpow_inv_rpow hnnT hp0.ne',
    Real.rpow_inv_rpow hnn hp0.ne'] at key
  exact key

/-! ### Proposition 7.2: Lipschitz periodic test maps

The paper proves the identity for smooth `u`; quasiconvexity is tested with Lipschitz periodic
maps `φ` (Lemma 2.2), and the passage between the two is left implicit. It is filled here with
the Fejér means `u_M` of `φ` (`UnitAddTorus.fejerMean`): trigonometric test maps whose gradients
are `σ_M (∇φ)` (the Fourier coefficients of `∇φ` are `2πi n φ̂ (n)`,
`UnitAddTorus.cubeFourierCoeff_fderiv`), bounded by `2 Lip (φ)`, and converging to `∇φ` in `L²`
(`UnitAddTorus.tendsto_integral_norm_fejerMean_sub_sq`), hence almost everywhere along a
subsequence; dominated convergence then passes `∫ f (∇u_M) ≥ 0` to the limit. -/

/-- `jac φ` is periodic when `φ` is. -/
theorem fourByTwo_jac_periodic {d : ℕ} {φ : (Fin 2 → ℝ) → Fin d → ℝ}
    (hper : ∀ (x : Fin 2 → ℝ) (z : Fin 2 → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (x : Fin 2 → ℝ) (z : Fin 2 → ℤ) : jac φ (x + fun i => (z i : ℝ)) = jac φ x := by
  ext r k
  simp only [jac, Matrix.of_apply]
  rw [← fderiv_comp_add_right]
  have : (fun y => φ (y + fun i => (z i : ℝ)) r) = fun y => φ y r :=
    funext fun y => by rw [hper]
  rw [this]

/-- `∂_k φ_j = ∂_k φ_{2j} + i ∂_k φ_{2j+1}` (rows `2j`, `2j + 1` of `∇φ`). -/
noncomputable def fourByTwo_dφ {N : ℕ} (φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ)
    (j : Fin (N + 1)) (k : Fin 2) (x : Fin 2 → ℝ) : ℂ :=
  (jac φ x (rowBlock j 0) k : ℂ) + Complex.I * (jac φ x (rowBlock j 1) k : ℂ)

/-- The Fourier coefficients of `φ_j = φ_{2j} + i φ_{2j+1}`. -/
noncomputable def fourByTwo_φHat {N : ℕ} (φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ)
    (j : Fin (N + 1)) (n : Fin 2 → ℤ) : ℂ :=
  UnitAddTorus.cubeFourierCoeff (fun x => (φ x (rowBlock j 0) : ℂ)) n +
    Complex.I * UnitAddTorus.cubeFourierCoeff (fun x => (φ x (rowBlock j 1) : ℂ)) n

theorem fourByTwo_measurable_jac_apply {d : ℕ} (φ : (Fin 2 → ℝ) → Fin d → ℝ) (r : Fin d)
    (k : Fin 2) : Measurable fun x => jac φ x r k :=
  measurable_fderiv_apply_const ℝ (fun y => φ y r) (Pi.single k 1)

theorem fourByTwo_measurable_dφ {N : ℕ} (φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ)
    (j : Fin (N + 1)) (k : Fin 2) : Measurable (fourByTwo_dφ φ j k) :=
  (Complex.measurable_ofReal.comp (fourByTwo_measurable_jac_apply φ _ k)).add
    (measurable_const.mul (Complex.measurable_ofReal.comp (fourByTwo_measurable_jac_apply φ _ k)))

theorem fourByTwo_norm_dφ_le {N : ℕ} {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ} {L : NNReal}
    (hφ : LipschitzWith L φ) (j : Fin (N + 1)) (k : Fin 2) (x : Fin 2 → ℝ) :
    ‖fourByTwo_dφ φ j k x‖ ≤ 2 * L := by
  unfold fourByTwo_dφ
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  linarith [fourByTwo_jac_bound hφ x (rowBlock j 0) k, fourByTwo_jac_bound hφ x (rowBlock j 1) k]

theorem fourByTwo_dφ_isPeriodic {N : ℕ} {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    (hper : ∀ (x : Fin 2 → ℝ) (z : Fin 2 → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (j : Fin (N + 1)) (k : Fin 2) : UnitAddTorus.IsPeriodic (fourByTwo_dφ φ j k) := by
  intro x z
  simp only [fourByTwo_dφ, fourByTwo_jac_periodic hper]

/-- The Fourier coefficients of `∂_k φ_j` are `2πi n_k φ̂_j (n)`. -/
theorem fourByTwo_cubeFourierCoeff_dφ {N : ℕ} {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    {L : NNReal} (hφ : LipschitzWith L φ)
    (hper : ∀ (x : Fin 2 → ℝ) (z : Fin 2 → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (j : Fin (N + 1)) (k : Fin 2) (n : Fin 2 → ℤ) :
    UnitAddTorus.cubeFourierCoeff (fourByTwo_dφ φ j k) n =
      2 * Real.pi * Complex.I * (n k : ℂ) * fourByTwo_φHat φ j n := by
  have hlip : ∀ r, LipschitzWith L fun y => φ y r := fun r => by
    simpa [Function.comp_def, Function.eval] using (LipschitzWith.eval r).comp hφ
  have hperr : ∀ r, UnitAddTorus.IsPeriodic fun y => φ y r := fun r x z => by
    simp only [hper]
  have hmeas : ∀ r, AEStronglyMeasurable fun x => (jac φ x r k : ℂ) := fun r =>
    (Complex.measurable_ofReal.comp (fourByTwo_measurable_jac_apply φ r k)).aestronglyMeasurable
  have hbd : ∀ r x, ‖(jac φ x r k : ℂ)‖ ≤ L := fun r x => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact fourByTwo_jac_bound hφ x r k
  have hsum : ∑ i, (n i : ℂ) * (((Pi.single k (1 : ℝ) : Fin 2 → ℝ) i : ℝ) : ℂ) = n k := by
    fin_cases k <;> simp [Fin.sum_univ_two]
  have hd : ∀ r, UnitAddTorus.cubeFourierCoeff (fun x => (jac φ x r k : ℂ)) n =
      2 * Real.pi * Complex.I * (n k : ℂ) *
        UnitAddTorus.cubeFourierCoeff (fun x => (φ x r : ℂ)) n := by
    intro r
    have := UnitAddTorus.cubeFourierCoeff_fderiv (hlip r) (hperr r) (Pi.single k 1) n
    rw [hsum] at this
    exact this
  unfold fourByTwo_dφ fourByTwo_φHat
  rw [UnitAddTorus.cubeFourierCoeff_add (hmeas _) (hbd _) ((hmeas _).const_mul Complex.I)
    (D := L) (fun x => by rw [norm_mul, Complex.norm_I, one_mul]; exact hbd _ x),
    UnitAddTorus.cubeFourierCoeff_const_mul, hd, hd]
  ring

/-- The coefficients of the Fejér means `u_M` of `φ` (component `j`). -/
noncomputable def fourByTwo_fejerW (N : ℕ) (φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ) (M : ℕ) :
    ℕ → (Fin 2 → ℤ) → ℂ :=
  fun j n => if h : j < N + 1 then (UnitAddTorus.fejerWeight M n : ℂ) * fourByTwo_φHat φ ⟨j, h⟩ n
    else 0

/-- `∂_k u_{M,j} = σ_M (∂_k φ_j)`. -/
theorem fourByTwo_pd_fejerW {N : ℕ} {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ} {L : NNReal}
    (hφ : LipschitzWith L φ)
    (hper : ∀ (x : Fin 2 → ℝ) (z : Fin 2 → ℤ), φ (x + fun i => (z i : ℝ)) = φ x) (M : ℕ)
    (j : Fin (N + 1)) (k : Fin 2) (x : Fin 2 → ℝ) :
    fourByTwo_pd (UnitAddTorus.fejerSupport M) (fourByTwo_fejerW N φ M j) x k =
      UnitAddTorus.fejerMean M (fourByTwo_dφ φ j k) x := by
  unfold fourByTwo_pd UnitAddTorus.fejerMean
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [fourByTwo_cubeFourierCoeff_dφ hφ hper, fourByTwo_E_eq]
  simp only [fourByTwo_fejerW, j.isLt, ↓reduceDIte, Fin.eta]
  rw [show (fun i => (x i : UnitAddCircle)) = UnitAddTorus.ofPi x from rfl]
  ring

/-- Every row of `ℝ^{2(N+1)×2}` is row `0` or row `1` of a block. -/
theorem fourByTwo_row_cases {N : ℕ} (r : Fin (2 * (N + 1))) :
    ∃ j : Fin (N + 1), r = rowBlock j 0 ∨ r = rowBlock j 1 := by
  refine ⟨⟨r.val / 2, by omega⟩, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one r.val with h | h
  · left; ext; simp only [rowBlock, Fin.val_zero, add_zero]; omega
  · right; ext; simp only [rowBlock, Fin.val_one]; omega

open Filter Topology in
/-- A Lipschitz `ℤ²`-periodic test map `φ` satisfies `∫_{(0,1)²} f_{p,ρ,C} (∇φ) ≥ 0` with
`C = ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖`: through the Fejér means `u_M` of `φ`, trigonometric test maps
(`fourByTwo_integral_chainF_testMap_nonneg`) with `∇u_M → ∇φ` almost everywhere along a
subsequence and `|∇u_M| ≤ 2 Lip (φ)`. -/
theorem fourByTwo_integral_chainF_nonneg_of_periodic (N : ℕ) (ρ : ℝ) {p : ℝ} (hp : 1 < p)
    (hfin : chainOpNorm N p ρ ≠ ⊤) {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ} {L : NNReal}
    (hφ : LipschitzWith L φ)
    (hper : ∀ (x : Fin 2 → ℝ) (z : Fin 2 → ℤ), φ (x + fun i => (z i : ℝ)) = φ x) :
    0 ≤ ∫ x in unitCube 2, chainF N p ρ (chainOpNorm N p ρ).toReal (jac φ x) := by
  have hp0 : 0 < p := by linarith
  set G := chainF N p ρ (chainOpNorm N p ρ).toReal with hG
  have hGc : Continuous G := fourByTwo_continuous_chainF N hp0.le ρ _
  set u : ℕ → (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ := fun M =>
    fourByTwo_testMap N (UnitAddTorus.fejerSupport M) (fourByTwo_fejerW N φ M) with hu
  have hjac : ∀ M x (j : Fin (N + 1)) k,
      jac (u M) x (rowBlock j 0) k = (UnitAddTorus.fejerMean M (fourByTwo_dφ φ j k) x).re ∧
        jac (u M) x (rowBlock j 1) k = (UnitAddTorus.fejerMean M (fourByTwo_dφ φ j k) x).im := by
    intro M x j k
    have h := fourByTwo_jac_testMap (N := N) (UnitAddTorus.fejerSupport M)
      (fourByTwo_fejerW N φ M) x j k
    rw [fourByTwo_pd_fejerW hφ hper] at h
    exact h
  have hfm_bd : ∀ M x j k, ‖UnitAddTorus.fejerMean M (fourByTwo_dφ φ j k) x‖ ≤ 2 * L :=
    fun M x j k => UnitAddTorus.norm_fejerMean_le M
      (fourByTwo_measurable_dφ φ j k).aestronglyMeasurable (fourByTwo_norm_dφ_le hφ j k) x
  have hu_bd : ∀ M x r k, |jac (u M) x r k| ≤ 2 * L := by
    intro M x r k
    obtain ⟨j, hr | hr⟩ := fourByTwo_row_cases r <;> subst hr
    · rw [(hjac M x j k).1]; exact (Complex.abs_re_le_norm _).trans (hfm_bd M x j k)
    · rw [(hjac M x j k).2]; exact (Complex.abs_im_le_norm _).trans (hfm_bd M x j k)
  -- a bound for `f` on the matrices with entries in `[−2L, 2L]`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ A : Matrix (Fin (2 * (N + 1))) (Fin 2) ℝ,
      (∀ r k, |A r k| ≤ 2 * L) → ‖G A‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_univ_pi fun _ : Fin (2 * (N + 1)) =>
      isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc (a := -(2 * (L : ℝ))) (b := 2 * L)
      ).exists_bound_of_continuousOn hGc.continuousOn
    exact ⟨B, fun A hA => hB A (Set.mem_univ_pi.mpr fun r => Set.mem_univ_pi.mpr fun k =>
      abs_le.mp (hA r k))⟩
  -- the `L²` error of the Fejér means of the entries of `∇φ`
  set E : ℕ → (Fin 2 → ℝ) → ℝ := fun M x => ∑ j : Fin (N + 1), ∑ k : Fin 2,
    ‖UnitAddTorus.fejerMean M (fourByTwo_dφ φ j k) x - fourByTwo_dφ φ j k x‖ ^ 2 with hE
  have hterm_int : ∀ M (j : Fin (N + 1)) (k : Fin 2), IntegrableOn (fun x =>
      ‖UnitAddTorus.fejerMean M (fourByTwo_dφ φ j k) x - fourByTwo_dφ φ j k x‖ ^ 2)
      (unitCube 2) := by
    intro M j k
    refine UnitAddTorus.integrableOn_cube_of_bound (((UnitAddTorus.continuous_fejerMean M _
      ).measurable.sub (fourByTwo_measurable_dφ φ j k)).norm.pow_const 2).aestronglyMeasurable
      (C := (2 * L + 2 * L) ^ 2) fun x => ?_
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
      (add_le_add (hfm_bd M x j k) (fourByTwo_norm_dφ_le hφ j k x))) 2
  have hE_int : ∀ M, IntegrableOn (E M) (unitCube 2) := fun M =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hterm_int M j k
  have hE_nn : ∀ M x, 0 ≤ E M x := fun M x =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
  have hE_tend : Tendsto (fun M => ∫ x in unitCube 2, E M x) atTop (𝓝 0) := by
    have h : ∀ M, ∫ x in unitCube 2, E M x = ∑ j : Fin (N + 1), ∑ k : Fin 2,
        ∫ x in unitCube 2,
          ‖UnitAddTorus.fejerMean M (fourByTwo_dφ φ j k) x - fourByTwo_dφ φ j k x‖ ^ 2 := by
      intro M
      rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hterm_int M j k]
      exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hterm_int M j k
    simp_rw [h]
    rw [show (0 : ℝ) = ∑ _j : Fin (N + 1), ∑ _k : Fin 2, (0 : ℝ) by simp]
    exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ =>
      UnitAddTorus.tendsto_integral_norm_fejerMean_sub_sq (fourByTwo_measurable_dφ φ j k)
        (fourByTwo_norm_dφ_le hφ j k) (fourByTwo_dφ_isPeriodic hper j k)
  -- convergence in measure, and a subsequence converging almost everywhere
  have hmeas : TendstoInMeasure (volume.restrict (unitCube 2)) E atTop fun _ => 0 := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero ?_
    have h : ∀ M, eLpNorm (E M - fun _ => 0) 1 (volume.restrict (unitCube 2)) =
        ENNReal.ofReal (∫ x in unitCube 2, E M x) := by
      intro M
      have h0 : (E M - fun _ => (0 : ℝ)) = E M := by funext x; simp
      rw [h0, eLpNorm_one_eq_lintegral_enorm,
        ofReal_integral_eq_lintegral_ofReal (hE_int M) (ae_of_all _ (hE_nn M))]
      all_goals first
        | exact lintegral_congr fun x => Real.enorm_eq_ofReal (hE_nn M x)
        | exact (hE_int M).aestronglyMeasurable
    simp_rw [h]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal hE_tend
  obtain ⟨ns, -, hns⟩ := hmeas.exists_seq_tendsto_ae
  -- pointwise convergence of `f (∇u_M)`
  have hconv : ∀ᵐ x ∂(volume.restrict (unitCube 2)),
      Tendsto (fun i => G (jac (u (ns i)) x)) atTop (𝓝 (G (jac φ x))) := by
    filter_upwards [hns] with x hx
    refine (hGc.tendsto _).comp ?_
    have hd : ∀ (j : Fin (N + 1)) (k : Fin 2), Tendsto (fun i =>
        UnitAddTorus.fejerMean (ns i) (fourByTwo_dφ φ j k) x - fourByTwo_dφ φ j k x) atTop
        (𝓝 0) := by
      intro j k
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hs : Tendsto (fun i => √(E (ns i) x)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp hx
        rw [Real.sqrt_zero] at this
        exact this
      refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hs
      refine Real.le_sqrt_of_sq_le ?_
      simp only [hE]
      refine le_trans ?_ (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun k _ =>
        by positivity) (Finset.mem_univ j))
      exact Finset.single_le_sum (f := fun k => ‖UnitAddTorus.fejerMean (ns i)
        (fourByTwo_dφ φ j k) x - fourByTwo_dφ φ j k x‖ ^ 2) (fun k _ => by positivity)
        (Finset.mem_univ k)
    refine tendsto_pi_nhds.mpr fun r => tendsto_pi_nhds.mpr fun k => ?_
    obtain ⟨j, hr | hr⟩ := fourByTwo_row_cases r <;> subst hr
    · have h := (Complex.continuous_re.tendsto 0).comp (hd j k)
      simp only [Function.comp_def, Complex.sub_re, Complex.zero_re] at h
      have e : ∀ i, jac (u (ns i)) x (rowBlock j 0) k =
          (UnitAddTorus.fejerMean (ns i) (fourByTwo_dφ φ j k) x).re -
            (fourByTwo_dφ φ j k x).re + jac φ x (rowBlock j 0) k := fun i => by
        rw [(hjac (ns i) x j k).1]; simp [fourByTwo_dφ]
      simp_rw [e]
      simpa using h.add_const (jac φ x (rowBlock j 0) k)
    · have h := (Complex.continuous_im.tendsto 0).comp (hd j k)
      simp only [Function.comp_def, Complex.sub_im, Complex.zero_im] at h
      have e : ∀ i, jac (u (ns i)) x (rowBlock j 1) k =
          (UnitAddTorus.fejerMean (ns i) (fourByTwo_dφ φ j k) x).im -
            (fourByTwo_dφ φ j k x).im + jac φ x (rowBlock j 1) k := fun i => by
        rw [(hjac (ns i) x j k).2]; simp [fourByTwo_dφ]
      simp_rw [e]
      simpa using h.add_const (jac φ x (rowBlock j 1) k)
  -- dominated convergence
  have hlim : Tendsto (fun i => ∫ x in unitCube 2, G (jac (u (ns i)) x)) atTop
      (𝓝 (∫ x in unitCube 2, G (jac φ x))) :=
    tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun i => (hGc.measurable.comp (fourByTwo_measurable_jac _)).aestronglyMeasurable)
      (integrableOn_const (by rw [volume_unitCube]; exact ENNReal.one_ne_top))
      (fun i => ae_of_all _ fun x => hB _ (hu_bd _ x))
      hconv
  exact ge_of_tendsto' hlim fun i =>
    fourByTwo_integral_chainF_testMap_nonneg N ρ hp hfin _ _

/-- The inequality `C^{qc} (p, N, ρ) ≤ ‖(ρ^N 𝓑^{N+1}, …, ρ 𝓑², 𝓑)‖_{L^p_0 (𝕋²; ℓ₂^{N+1}) →
L^p_0 (𝕋²)}` of Proposition 7.2, by the paper's argument (TeX lines 2808–2821): with
`C = ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖`, the identity `Q (∇u) = Σ_j ρ^{N−j} 𝓑^{N+1−j} P_ρ (∇u)_j`
(`fourByTwo_chainP_eq_hOf`, `fourByTwo_chainQ_eq_hOf`) gives `∫ f_{p,ρ,C} (∇u) ≥ 0` for every
periodic `u`, that is, `f_{p,ρ,C}` is quasiconvex at `0` (Lemma 2.2,
`External.Rindler.quasiconvexAtOn_iff_periodic`).

Departure from the paper (reason 3 of the rules: the representation). The paper states the
identity for smooth periodic `u`; the norm `chainOpNorm` is computed on trigonometric
polynomials, so the identity is proved for every trigonometric test map, by the paper's induction
frequency by frequency. Implicit step filled: Lemma 2.2 tests quasiconvexity with Lipschitz
periodic maps, and the paper passes from its smooth `u` to these without comment; here a
Lipschitz periodic `φ` is reached through its Fejér means
(`fourByTwo_integral_chainF_nonneg_of_periodic`). -/
theorem fourByTwo_qcThreshold_le_chainOpNorm (N : ℕ) (ρ : ℝ) {p : ℝ} (hp : 1 < p) :
    qcThreshold (chainF N p ρ) ≤ chainOpNorm N p ρ := by
  by_cases hfin : chainOpNorm N p ρ = ⊤
  · rw [hfin]; exact le_top
  have hp0 : 0 < p := by linarith
  set K := (chainOpNorm N p ρ).toReal with hKdef
  have hK : ENNReal.ofReal K = chainOpNorm N p ρ := ENNReal.ofReal_toReal hfin
  have hcont := fourByTwo_continuous_chainF N hp0.le ρ K
  have hper : CalculusOfVariations.QuasiconvexAtPeriodic (chainF N p ρ K) 0 := by
    intro φ L hφ hφper _
    rw [fourByTwo_chainF_zero N hp0]
    simp only [zero_add, grad_eq]
    rw [unitCube_eq_cov]
    exact fourByTwo_integral_chainF_nonneg_of_periodic N ρ hp hfin hφ hφper
  have hqc : QuasiconvexAt (chainF N p ρ K) 0 :=
    (cov_quasiconvexAtOn_unitCube_iff _ _).mp
      ((External.Rindler.quasiconvexAtOn_iff_periodic hcont.lowerSemicontinuous
        (fourByTwo_isLocallyBounded hcont) 0).mpr hper)
  rw [← hK]
  exact iInf₂_le K ⟨ENNReal.toReal_nonneg, hqc⟩

-- The proof does not use the paper's hypothesis `0 < ρ` (see the docstring).
set_option linter.unusedVariables false in
/-- **Proposition 7.2** (`prop:qcbound`): for every `p ∈ (1, ∞)`,
`C^{qc} (p, N, ρ) = ‖(ρ^N 𝓑^{N+1}, …, ρ 𝓑², 𝓑)‖_{L^p_0 (𝕋²; ℓ₂^{N+1}) → L^p_0 (𝕋²)}`.

Proof (the paper's, TeX lines 2807–2832). For a periodic `u`, `h_j = ∂̄u_j − ρ ∂u_{j−1}` gives
`P_ρ (∇u) = (h₀, …, h_N)` and `Q (∇u) = ∂u_N = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j` (induction from
`𝓑 (∂̄w) = ∂w`), so `C^{qc} ≤ ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖` (`fourByTwo_qcThreshold_le_chainOpNorm`);
conversely every mean-zero tuple `(h_j)` is `P_ρ (∇u)` for the `u` obtained by solving
`∂̄u_j = h_j + ρ ∂u_{j−1}`, since `∂̄` is invertible on mean-zero functions, so
`C^{qc} ≥ ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖` (`fourByTwo_chainOpNorm_le_qcThreshold`).

Departure from the paper (reason 3 of the rules: the representation), in the inequality `≤`.
The paper states the identity for smooth periodic `u`; here the norm is computed on mean-zero
trigonometric polynomials (`chainOpNorm`), so the identity is proved for every trigonometric test
map, by the paper's induction frequency by frequency (`fourByTwo_chainQ_eq_hOf`). Implicit step
filled: quasiconvexity is tested with Lipschitz periodic maps (Lemma 2.2), and the paper passes
from smooth `u` to these without comment; the step is made with Fejér means
(`fourByTwo_integral_chainF_nonneg_of_periodic`, with the general facts of
`Morrey.Common.Basic.Analysis.Fourier.TorusLipschitz`: the Fourier coefficients of the gradient
of a Lipschitz periodic function, Parseval's identity, and the Fejér kernel). No `L^p` bound for
Fourier multipliers is needed. The hypothesis `0 < ρ` of the paper's setting is not used. -/
theorem proposition7_2 (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {p : ℝ} (hp : 1 < p) :
    qcThreshold (chainF N p ρ) = chainOpNorm N p ρ :=
  le_antisymm (fourByTwo_qcThreshold_le_chainOpNorm N ρ hp)
    (fourByTwo_chainOpNorm_le_qcThreshold N ρ hp)

/-- **Proposition 7.2** (`prop:qcbound`), "in particular":
`C^{qc} (p, N, ρ) ≥ ρ^N ‖𝓑^{N+1}‖_{L^p (ℝ²) → L^p (ℝ²)}`. Conditional on transference for
homogeneous multipliers (HNVW I, Corollary 5.7.6).

Proof (the paper's): take `(h₀, …, h_N) = (h, 0, …, 0)` in the identity of Proposition 7.2, whose
inequality `C^{qc} ≥ ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖` is `fourByTwo_chainOpNorm_le_qcThreshold`; this gives
`C^{qc} ≥ ρ^N ‖𝓑^{N+1}‖_{L^p_0 (𝕋²)}`, and transference (`HNVWTransference`) compares the torus
norm with the norm on `ℝ²`. -/
theorem proposition7_2_lower (hT : HNVWTransference) (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (ρ ^ N) * beurlingPowNorm (N + 1) p ≤ qcThreshold (chainF N p ρ) := by
  refine le_trans ?_ (fourByTwo_chainOpNorm_le_qcThreshold N ρ hp)
  -- transference: `‖𝓑^{N+1}‖_{L^p (ℝ²)} ≤ ‖𝓑^{N+1}‖_{L^p_0 (𝕋²)}`
  refine (mul_le_mul_right (hT (N + 1) p (by omega) hp) _).trans ?_
  -- the tuples `(h, 0, …, 0)`
  rw [torusBeurlingPowNorm, ENNReal.mul_iSup]
  refine iSup_le fun c => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hc => ?_
  set C : Fin (N + 1) → (Fin 2 → ℤ) →₀ ℂ := fun j => if j = 0 then c else 0 with hCdef
  have hC0 : ∀ j, C j 0 = 0 := fun j => by
    by_cases hj : j = 0 <;> simp [hCdef, hj, hc]
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (C : Fin (N + 1) → (Fin 2 → ℤ) →₀ ℂ)
    (_ : ∀ j, C j 0 = 0) => eLpNorm (fun x => ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
        torusBeurlingPow (N + 1 - j.val) (C j) x) (ENNReal.ofReal p) volume /
      eLpNorm (fun x => √(∑ j, ‖trigPoly (C j) x‖ ^ 2)) (ENNReal.ofReal p) volume) C hC0)
  have hnum : (fun x => ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
      torusBeurlingPow (N + 1 - j.val) (C j) x) =
      ((ρ ^ N : ℝ) : ℂ) • torusBeurlingPow (N + 1) c := by
    funext x
    rw [Finset.sum_eq_single (0 : Fin (N + 1))]
    · simp [hCdef]
    · intro j _ hj
      simp [hCdef, hj, torusBeurlingPow]
    · simp
  have hden : (fun x => √(∑ j, ‖trigPoly (C j) x‖ ^ 2)) = fun x => ‖trigPoly c x‖ := by
    funext x
    rw [Finset.sum_eq_single (0 : Fin (N + 1))]
    · simp [hCdef, Real.sqrt_sq (norm_nonneg _)]
    · intro j _ hj
      simp [hCdef, hj, trigPoly]
    · simp
  rw [hnum, hden, eLpNorm_const_smul, eLpNorm_norm _
    (fourByTwo_continuous_trigPoly c).aestronglyMeasurable, ← ofReal_norm, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg hρ.le _), mul_div_assoc]

/-! ### Theorem 7.1: the standard identifications and the threshold argument -/

/-- `‖M‖_{S₂}` is the Frobenius norm. -/
theorem fourByTwo_schattenNorm_two {d m : ℕ} (M : Matrix (Fin d) (Fin m) ℝ) :
    schattenNorm 2 M = √(∑ i, ∑ j, M i j ^ 2) := by
  have hpsd := Matrix.posSemidef_conjTranspose_mul_self M
  have hsv : ∀ i, sval M i ^ ((2 : ℝ≥0∞).toReal) =
      (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i := by
    intro i
    rw [sval, ENNReal.toReal_ofNat, Real.rpow_two,
      Real.sq_sqrt (Matrix.PosSemidef.eigenvalues_nonneg hpsd i)]
  have htr := (Matrix.isHermitian_conjTranspose_mul_self M).trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id] at htr
  simp only [schattenNorm, ENNReal.ofNat_ne_top, ↓reduceIte]
  rw [Finset.sum_congr rfl fun i _ => hsv i, ← htr,
    ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow, Finset.sum_comm]
  congr 1
  simp [Matrix.trace, Matrix.mul_apply, sq]

/-- The map `P_ρ : ℝ^{4×2} → ℝ^{2×2} ≅ ℂ²` of Theorem 7.1 (`N = 1`): row `j` of `P (A)` is
`(Re (P_ρ (A)_j), Im (P_ρ (A)_j))`. -/
noncomputable def fourByTwo_P (ρ : ℝ) :
    Matrix (Fin 4) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun A := Matrix.of fun j k =>
    if k = 0 then (fourByTwo_PLin (N := 1) ρ j A).re else (fourByTwo_PLin (N := 1) ρ j A).im
  map_add' A B := by
    ext j k
    simp only [map_add, Complex.add_re, Complex.add_im, Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> rfl
  map_smul' c A := by
    ext j k
    simp only [map_smul, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    split_ifs <;> rfl

/-- The map `Q : ℝ^{4×2} → ℝ² ≅ ℂ` of Theorem 7.1: `(Re Q (A), Im Q (A))`. -/
noncomputable def fourByTwo_Q : Matrix (Fin 4) (Fin 2) ℝ →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun A := ![(fourByTwo_QLin 1 A).re, (fourByTwo_QLin 1 A).im]
  map_add' A B := by
    ext k
    fin_cases k <;> simp
  map_smul' c A := by
    ext k
    fin_cases k <;> simp

/-- Under the identifications of Theorem 7.1, its integrand is `f_{p,ρ,C}` with `N = 1`. -/
theorem fourByTwo_integrand_eq (p ρ C : ℝ) :
    (fun A => C ^ p * schattenNorm 2 (fourByTwo_P ρ A) ^ p -
        √(∑ i, fourByTwo_Q A i ^ 2) ^ p) = chainF 1 p ρ C := by
  funext A
  rw [fourByTwo_schattenNorm_two, chainF]
  congr 3
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
    simp [fourByTwo_P, sq]
    rfl
  · rw [Fin.sum_univ_two, Complex.norm_eq_sqrt_sq_add_sq]
    simp [fourByTwo_Q]
    rfl

/-- `f_{p,ρ,C}` is increasing in `C ≥ 0`, so rank-one convexity at `0` passes to larger `C`. -/
theorem fourByTwo_rankOneConvexAt_mono (N : ℕ) {p : ℝ} (hp : 0 < p) (ρ : ℝ) {C C' : ℝ}
    (hC' : 0 ≤ C') (hCC : C' ≤ C) (h : RankOneConvexAt (chainF N p ρ C') 0) :
    RankOneConvexAt (chainF N p ρ C) 0 := by
  obtain ⟨g, hg, hgrc, hle, heq⟩ := h
  refine ⟨g, hg, hgrc, fun B => (hle B).trans ?_, ?_⟩
  · simp only [chainF]
    gcongr
  · rw [heq, fourByTwo_chainF_zero N hp, fourByTwo_chainF_zero N hp]

/-- If `C^{rc} < C` then `f_{p,ρ,C}` is rank-one convex at `0`. -/
theorem fourByTwo_rankOneConvexAt_of_lt (N : ℕ) {p : ℝ} (hp : 0 < p) (ρ : ℝ) {C : ℝ}
    (h : rcThreshold (chainF N p ρ) < ENNReal.ofReal C) : RankOneConvexAt (chainF N p ρ C) 0 := by
  rw [rcThreshold] at h
  obtain ⟨C', hC'⟩ := iInf_lt_iff.mp h
  obtain ⟨⟨h0, hrc⟩, hlt⟩ := iInf_lt_iff.mp hC'
  exact fourByTwo_rankOneConvexAt_mono N hp ρ h0
    ((ENNReal.ofReal_lt_ofReal_iff'.mp hlt).1.le) hrc

/-- If `C < C^{qc}` (and `C ≥ 0`) then `f_{p,ρ,C}` is not quasiconvex at `0`. -/
theorem fourByTwo_not_quasiconvexAt_of_lt {d m : ℕ} (F : ℝ → Matrix (Fin d) (Fin m) ℝ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (h : ENNReal.ofReal C < qcThreshold F) : ¬ QuasiconvexAt (F C) 0 :=
  fun hqc => (iInf₂_le C ⟨hC, hqc⟩ : qcThreshold F ≤ _).not_gt h

/-- **Theorem 7.1** (`cs-thm7.1`): for `p ∈ (1, 2) ∪ (2, ∞)` there are linear maps
`P_p : ℝ^{4×2} → ℝ^{2×2}`, `Q_p : ℝ^{4×2} → ℝ²` and `C (p) > 0` such that
`A ↦ C (p)^p ‖P_p (A)‖_{S₂}^p − ‖Q_p (A)‖_{ℓ₂}^p` is rank-one convex at `0` but not quasiconvex
at `0`. Conditional on Burkholder's inequality (Proposition 7.1), transference (Proposition 7.2)
and Dragičević's lower bound `‖𝓑²‖_p > p* − 1`.

Proof (the paper's): `N = 1`, with `ℝ^{4×2} ≅ Lin (ℂ, ℂ²)` and `ℝ^{2×2} ≅ ℂ²` (row `j` of `P_p (A)`
is `(Re, Im)` of `P_ρ (A)_j`, `Q_p (A) = (Re, Im)` of `Q (A)`, so that the integrand is
`f_{p,ρ,C}`: `fourByTwo_integrand_eq`). Propositions 7.1 and 7.2 give
`C^{rc} (p, 1, ρ) ≤ (p* − 1) √(1 + ρ²)` and `C^{qc} (p, 1, ρ) ≥ ρ ‖𝓑²‖_p`; by Dragičević,
`ρ ‖𝓑²‖_p > (p* − 1) √(1 + ρ²)` for large `ρ` (explicitly `ρ = (p* − 1) / (‖𝓑²‖_p − p* + 1) + 1`,
or `ρ = 1` if `‖𝓑²‖_p = ∞`), and `C` is chosen strictly between. Since `f_{p,ρ,C}` increases with
`C`, `C > C^{rc}` gives rank-one convexity at `0` and `C < C^{qc}` its failure of quasiconvexity. -/
theorem theorem7_1 (hB : BurkholderInequality)
    (hT : HNVWTransference) (hD : DragicevicLowerBound) {p : ℝ}
    (hp : 1 < p) (hp2 : p ≠ 2) :
    ∃ (P : Matrix (Fin 4) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
      (Q : Matrix (Fin 4) (Fin 2) ℝ →ₗ[ℝ] (Fin 2 → ℝ)) (C : ℝ), 0 < C ∧
      RankOneConvexAt
        (fun A => C ^ p * schattenNorm 2 (P A) ^ p - √(∑ i, Q A i ^ 2) ^ p) 0 ∧
      ¬ QuasiconvexAt
        (fun A => C ^ p * schattenNorm 2 (P A) ^ p - √(∑ i, Q A i ^ 2) ^ p) 0 := by
  have hp0 : 0 < p := by linarith
  set a := pStar p - 1 with ha
  have ha0 : 0 < a := by
    have : p ≤ pStar p := le_max_left _ _
    linarith
  -- Dragičević: `‖𝓑²‖_p > p* − 1`; so `ρ ‖𝓑²‖_p > (p* − 1) √(1 + ρ²)` for large `ρ`, and we
  -- choose `C` strictly between them
  obtain ⟨ρ, C, hρ, hC1, hC2⟩ : ∃ ρ C : ℝ, 0 < ρ ∧ a * √(1 + ρ ^ 2) < C ∧
      ENNReal.ofReal C < ENNReal.ofReal ρ * beurlingPowNorm 2 p := by
    by_cases hb : beurlingPowNorm 2 p = ⊤
    · refine ⟨1, a * √(1 + 1 ^ 2) + 1, one_pos, by linarith, ?_⟩
      rw [hb, ENNReal.mul_top (by simp)]
      exact ENNReal.ofReal_lt_top
    · set b := (beurlingPowNorm 2 p).toReal with hbdef
      have hab : a < b := by
        have h := hD p hp hp2
        rw [← ENNReal.ofReal_toReal hb] at h
        exact (ENNReal.ofReal_lt_ofReal_iff'.mp h).1
      set ρ := a / (b - a) + 1 with hρdef
      have hba : 0 < b - a := by linarith
      have hρ : 0 < ρ := by positivity
      have key : a * (1 + ρ) < ρ * b := by
        have : ρ * (b - a) = a + (b - a) := by
          rw [hρdef, add_mul, div_mul_cancel₀ _ hba.ne', one_mul]
        nlinarith
      have hsq : √(1 + ρ ^ 2) ≤ 1 + ρ := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith
      refine ⟨ρ, (a * (1 + ρ) + ρ * b) / 2, hρ, ?_, ?_⟩
      · have := mul_le_mul_of_nonneg_left hsq ha0.le
        linarith
      · rw [← ENNReal.ofReal_toReal hb, ← ENNReal.ofReal_mul hρ.le]
        exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos hρ (by linarith))).mpr (by linarith)
  have hC0 : 0 < C := lt_of_le_of_lt (mul_nonneg ha0.le (Real.sqrt_nonneg _)) hC1
  refine ⟨fourByTwo_P ρ, fourByTwo_Q, C, hC0, ?_, ?_⟩
  · -- Proposition 7.1: `C^{rc} (p, 1, ρ) ≤ (p* − 1) √(1 + ρ²) < C`
    rw [fourByTwo_integrand_eq]
    apply fourByTwo_rankOneConvexAt_of_lt 1 hp0 ρ
    refine lt_of_le_of_lt (proposition7_1 hB 1 hρ hp) ?_
    rw [show ∑ k ∈ Finset.range (1 + 1), ρ ^ (2 * k) = 1 + ρ ^ 2 by
      simp [Finset.sum_range_succ]]
    exact (ENNReal.ofReal_lt_ofReal_iff hC0).mpr hC1
  · -- Proposition 7.2: `C^{qc} (p, 1, ρ) ≥ ρ ‖𝓑²‖_p > C`
    rw [fourByTwo_integrand_eq]
    apply fourByTwo_not_quasiconvexAt_of_lt _ hC0.le
    refine lt_of_lt_of_le hC2 ?_
    have h72 := proposition7_2_lower hT 1 hρ hp
    rw [pow_one] at h72
    exact h72

/-! ### Corollary 7.2: homogeneous polynomials -/

section HomPoly

variable {d m : ℕ}

theorem fourByTwo_isHomPoly_congr {n : ℕ} {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (h : ∀ A, f A = g A) (hf : IsHomogeneousPolynomial n f) : IsHomogeneousPolynomial n g := by
  obtain ⟨P, hP, hPf⟩ := hf
  exact ⟨P, hP, fun A => (h A).symm.trans (hPf A)⟩

/-- A linear form in the entries is a homogeneous polynomial of degree one. -/
theorem fourByTwo_isHomPoly_linear (ℓ : Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ] ℝ) :
    IsHomogeneousPolynomial 1 ℓ := by
  refine ⟨∑ ij : Fin d × Fin m, MvPolynomial.C (ℓ (Matrix.single ij.1 ij.2 1)) *
      MvPolynomial.X ij,
    MvPolynomial.IsHomogeneous.sum _ _ _ fun ij _ => MvPolynomial.isHomogeneous_C_mul_X _ _,
    fun A => ?_⟩
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]

theorem fourByTwo_isHomPoly_mul {a b : ℕ} {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : IsHomogeneousPolynomial a f) (hg : IsHomogeneousPolynomial b g) :
    IsHomogeneousPolynomial (a + b) fun A => f A * g A := by
  obtain ⟨P, hP, hPf⟩ := hf
  obtain ⟨Q, hQ, hQg⟩ := hg
  exact ⟨P * Q, hP.mul hQ, fun A => by rw [map_mul, ← hPf, ← hQg]⟩

theorem fourByTwo_isHomPoly_add {n : ℕ} {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : IsHomogeneousPolynomial n f) (hg : IsHomogeneousPolynomial n g) :
    IsHomogeneousPolynomial n fun A => f A + g A := by
  obtain ⟨P, hP, hPf⟩ := hf
  obtain ⟨Q, hQ, hQg⟩ := hg
  exact ⟨P + Q, hP.add hQ, fun A => by rw [map_add, ← hPf, ← hQg]⟩

theorem fourByTwo_isHomPoly_const_mul {n : ℕ} (c : ℝ) {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : IsHomogeneousPolynomial n f) : IsHomogeneousPolynomial n fun A => c * f A := by
  obtain ⟨P, hP, hPf⟩ := hf
  exact ⟨MvPolynomial.C c * P, hP.C_mul c, fun A => by
    rw [map_mul, MvPolynomial.eval_C, ← hPf]⟩

/-- `A ↦ |ℓ (A)|²` is a homogeneous quadratic polynomial for a real-linear `ℓ` with complex
values. -/
theorem fourByTwo_isHomPoly_normSq (ℓ : Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ] ℂ) :
    IsHomogeneousPolynomial 2 fun A => ‖ℓ A‖ ^ 2 := by
  have hre := fourByTwo_isHomPoly_linear (Complex.reLm.comp ℓ)
  have him := fourByTwo_isHomPoly_linear (Complex.imLm.comp ℓ)
  refine fourByTwo_isHomPoly_congr (fun A => ?_)
    (fourByTwo_isHomPoly_add (fourByTwo_isHomPoly_mul hre hre) (fourByTwo_isHomPoly_mul him him))
  simp [Complex.sq_norm, Complex.normSq_apply]

end HomPoly

/-! ### Corollary 7.2: the function `U` and the quartic `𝒫` -/

/-- The core inequality behind the zig-zag concavity of `U`: if `α² ≤ X H`, `β² ≤ Y K` and
`0 ≤ K ≤ H`, then `8 β² + 4 K Y − 20 H Y − 80 α β − 20 K X − 120 α² − 60 H X ≤ 0` (this is the
second derivative of `t ↦ U (x + t h, y + t k)` with `X = |x|²`, `Y = |y|²`,
`α = Re ⟨x, h⟩`, `β = Re (y k̄)`, `H = |h|²`, `K = |k|²`). -/
theorem fourByTwo_U_core {X Y α β H K : ℝ} (hY : 0 ≤ Y) (hα : α ^ 2 ≤ X * H)
    (hβ : β ^ 2 ≤ Y * K) (hK : 0 ≤ K) (hKH : K ≤ H) :
    8 * β ^ 2 + 4 * K * Y - 20 * H * Y - 80 * α * β - 20 * K * X - 120 * α ^ 2 -
      60 * H * X ≤ 0 := by
  rcases hK.eq_or_lt with hK0 | hK0
  · subst hK0
    have hβ0 : β = 0 := by nlinarith [sq_nonneg β]
    subst hβ0
    nlinarith [sq_nonneg α, mul_nonneg hY (hKH : (0 : ℝ) ≤ H)]
  · have hH : 0 < H := lt_of_lt_of_le hK0 hKH
    set Gq := α ^ 2 * (180 * H * K + 20 * K ^ 2) + 80 * H * K * α * β +
      β ^ 2 * (20 * H ^ 2 - 12 * H * K) with hGq
    have hc : 0 < 180 * H * K + 20 * K ^ 2 := by positivity
    have hGq0 : 0 ≤ Gq := by
      have hid : (180 * H * K + 20 * K ^ 2) * Gq = ((180 * H * K + 20 * K ^ 2) * α +
          40 * H * K * β) ^ 2 + 240 * H * K * (15 * H + K) * (H - K) * β ^ 2 := by
        rw [hGq]; ring
      have h2 : 0 ≤ ((180 * H * K + 20 * K ^ 2) * α + 40 * H * K * β) ^ 2 +
          240 * H * K * (15 * H + K) * (H - K) * β ^ 2 := by
        have : 0 ≤ H - K := by linarith
        positivity
      rw [← hid] at h2
      exact (mul_nonneg_iff_of_pos_left hc).mp h2
    have hid : H * K * -(8 * β ^ 2 + 4 * K * Y - 20 * H * Y - 80 * α * β - 20 * K * X -
        120 * α ^ 2 - 60 * H * X) = (20 * H - 4 * K) * H * (Y * K - β ^ 2) +
        (20 * K + 60 * H) * K * (X * H - α ^ 2) + Gq := by
      rw [hGq]; ring
    have h3 : 0 ≤ (20 * H - 4 * K) * H * (Y * K - β ^ 2) +
        (20 * K + 60 * H) * K * (X * H - α ^ 2) + Gq := by
      have h1 : 0 ≤ 20 * H - 4 * K := by linarith
      have h2 : 0 ≤ Y * K - β ^ 2 := by linarith
      have h4 : 0 ≤ X * H - α ^ 2 := by linarith
      positivity
    rw [← hid] at h3
    have := (mul_nonneg_iff_of_pos_left (mul_pos hH hK0)).mp h3
    linarith

open Polynomial in
/-- The quartic `t ↦ Y(t)² − 10 X(t) Y(t) − 15 X(t)²` with `X(t) = X + 2 a t + H t²`,
`Y(t) = Y + 2 b t + K t²` is concave when `a² ≤ X H`, `b² ≤ Y K` and `0 ≤ K ≤ H`: its second
derivative is `≤ 0` everywhere (`fourByTwo_U_core` at the shifted point). -/
theorem fourByTwo_concave_quartic {x0 y0 a b H K : ℝ} (hY : 0 ≤ y0)
    (ha : a ^ 2 ≤ x0 * H) (hb : b ^ 2 ≤ y0 * K) (hK : 0 ≤ K) (hKH : K ≤ H) :
    ConcaveOn ℝ Set.univ fun t : ℝ =>
      (y0 + 2 * b * t + K * t ^ 2) ^ 2 -
        10 * (x0 + 2 * a * t + H * t ^ 2) * (y0 + 2 * b * t + K * t ^ 2) -
        15 * (x0 + 2 * a * t + H * t ^ 2) ^ 2 := by
  set c0 := y0 ^ 2 - 10 * x0 * y0 - 15 * x0 ^ 2
  set c1 := 4 * b * y0 - 10 * (2 * a * y0 + 2 * b * x0) - 60 * a * x0
  set c2 := 4 * b ^ 2 + 2 * K * y0 - 10 * (H * y0 + 4 * a * b + K * x0) -
    15 * (4 * a ^ 2 + 2 * H * x0)
  set c3 := 4 * b * K - 10 * (2 * a * K + 2 * b * H) - 60 * a * H
  set c4 := K ^ 2 - 10 * H * K - 15 * H ^ 2
  set P : ℝ[X] := C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 with hP
  have hfun : (fun t : ℝ => (y0 + 2 * b * t + K * t ^ 2) ^ 2 -
      10 * (x0 + 2 * a * t + H * t ^ 2) * (y0 + 2 * b * t + K * t ^ 2) -
      15 * (x0 + 2 * a * t + H * t ^ 2) ^ 2) = fun t => P.eval t := by
    funext t
    simp only [hP, eval_add, eval_C, eval_mul, eval_X, eval_pow]
    ring
  have hd : deriv (fun t => P.eval t) = fun t => P.derivative.eval t :=
    funext fun t => Polynomial.deriv P
  rw [hfun]
  refine concaveOn_univ_of_deriv2_nonpos (Polynomial.differentiable P) ?_ fun t => ?_
  · rw [hd]; exact Polynomial.differentiable _
  · have h2 : deriv^[2] (fun t => P.eval t) t = P.derivative.derivative.eval t := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, hd]
      exact Polynomial.deriv _
    rw [h2]
    have hcalc : P.derivative.derivative.eval t =
        8 * (b + K * t) ^ 2 + 4 * K * (y0 + 2 * b * t + K * t ^ 2) -
          20 * H * (y0 + 2 * b * t + K * t ^ 2) - 80 * (a + H * t) * (b + K * t) -
          20 * K * (x0 + 2 * a * t + H * t ^ 2) - 120 * (a + H * t) ^ 2 -
          60 * H * (x0 + 2 * a * t + H * t ^ 2) := by
      simp only [hP, derivative_add, derivative_C, derivative_C_mul_X, derivative_C_mul_X_pow,
        eval_add, eval_C, eval_mul, eval_X, eval_pow, zero_add]
      simp only [c2, c3, c4]
      push_cast
      ring
    rw [hcalc]
    have hYt : 0 ≤ y0 + 2 * b * t + K * t ^ 2 := by
      rcases hK.eq_or_lt with h0 | h0
      · subst h0
        have : b = 0 := by nlinarith [sq_nonneg b]
        subst this; simpa using hY
      · nlinarith [sq_nonneg (K * t + b)]
    exact fourByTwo_U_core hYt (by nlinarith) (by nlinarith) hK hKH

/-- `U (x, y) = |y|⁴ − 10 |x|² |y|² − 15 |x|⁴` on `ℂ² × ℂ` (proof of Corollary 7.2). -/
noncomputable def fourByTwo_U (x : Fin 2 → ℂ) (y : ℂ) : ℝ :=
  ‖y‖ ^ 4 - 10 * (∑ j, ‖x j‖ ^ 2) * ‖y‖ ^ 2 - 15 * (∑ j, ‖x j‖ ^ 2) ^ 2

/-- `2 U (x, y) ≥ |y|⁴ − 130 |x|⁴` (proof of Corollary 7.2). -/
theorem fourByTwo_U_bound (x : Fin 2 → ℂ) (y : ℂ) :
    ‖y‖ ^ 4 - 130 * (∑ j, ‖x j‖ ^ 2) ^ 2 ≤ 2 * fourByTwo_U x y := by
  unfold fourByTwo_U
  nlinarith [sq_nonneg (‖y‖ ^ 2 - 10 * ∑ j, ‖x j‖ ^ 2)]

theorem fourByTwo_norm_add_mul_sq (z w : ℂ) (t : ℝ) :
    ‖z + t * w‖ ^ 2 = ‖z‖ ^ 2 + 2 * (z * starRingEnd ℂ w).re * t + ‖w‖ ^ 2 * t ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- `U` is zig-zag concave (proof of Corollary 7.2): `t ↦ U (x + t h, y + t k)` is concave
whenever `|k| ≤ |h|`. -/
theorem fourByTwo_U_zigzag (x h : Fin 2 → ℂ) (y k : ℂ) (hkh : ‖k‖ ^ 2 ≤ ∑ j, ‖h j‖ ^ 2) :
    ConcaveOn ℝ Set.univ fun t : ℝ => fourByTwo_U (fun j => x j + t * h j) (y + t * k) := by
  set x0 := ∑ j, ‖x j‖ ^ 2 with hx0
  set H := ∑ j, ‖h j‖ ^ 2 with hH
  set a := ∑ j, (x j * starRingEnd ℂ (h j)).re with ha
  set b := (y * starRingEnd ℂ k).re with hb
  have hXt : ∀ t : ℝ, ∑ j, ‖x j + t * h j‖ ^ 2 = x0 + 2 * a * t + H * t ^ 2 := by
    intro t
    simp only [fourByTwo_norm_add_mul_sq, Finset.sum_add_distrib, hx0, ha, hH,
      ← Finset.sum_mul, ← Finset.mul_sum]
  have hYt : ∀ t : ℝ, ‖y + t * k‖ ^ 2 = ‖y‖ ^ 2 + 2 * b * t + ‖k‖ ^ 2 * t ^ 2 := fun t => by
    rw [fourByTwo_norm_add_mul_sq]
  have hfun : (fun t : ℝ => fourByTwo_U (fun j => x j + t * h j) (y + t * k)) = fun t =>
      (‖y‖ ^ 2 + 2 * b * t + ‖k‖ ^ 2 * t ^ 2) ^ 2 -
        10 * (x0 + 2 * a * t + H * t ^ 2) * (‖y‖ ^ 2 + 2 * b * t + ‖k‖ ^ 2 * t ^ 2) -
        15 * (x0 + 2 * a * t + H * t ^ 2) ^ 2 := by
    funext t
    unfold fourByTwo_U
    rw [hXt t, show ‖y + t * k‖ ^ 4 = (‖y + t * k‖ ^ 2) ^ 2 by ring, hYt t]
  rw [hfun]
  refine fourByTwo_concave_quartic (sq_nonneg _) ?_ ?_ (sq_nonneg _) hkh
  · -- `a² ≤ |x|² |h|²` (Cauchy–Schwarz)
    have h1 : |a| ≤ ∑ j, ‖x j‖ * ‖h j‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
      rw [norm_mul, Complex.norm_conj]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖x j‖) fun j => ‖h j‖
    calc a ^ 2 = |a| ^ 2 := (sq_abs a).symm
      _ ≤ (∑ j, ‖x j‖ * ‖h j‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ _ := h2
  · -- `b² ≤ |y|² |k|²`
    have h1 : |b| ≤ ‖y‖ * ‖k‖ := by
      refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
      rw [norm_mul, Complex.norm_conj]
    calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      _ ≤ (‖y‖ * ‖k‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = ‖y‖ ^ 2 * ‖k‖ ^ 2 := by ring

/-- The quartic `𝒫 (A) = −2 U (√3 P_{√2} (A), Q (A))` on `ℝ^{4×2}` (proof of Corollary 7.2;
`N = 1`). -/
noncomputable def fourByTwo_quartic (A : Matrix (Fin 4) (Fin 2) ℝ) : ℝ :=
  -2 * fourByTwo_U (fun j => ((√3 : ℝ) : ℂ) * chainP (N := 1) (√2) A j) (chainQ (N := 1) A)

theorem fourByTwo_quartic_continuous : Continuous fourByTwo_quartic := by
  have hP : ∀ j, Continuous fun A : Matrix (Fin 4) (Fin 2) ℝ => chainP (N := 1) (√2) A j :=
    fun j => (fourByTwo_PLin (N := 1) (√2) j).continuous_of_finiteDimensional
  have hQ : Continuous fun A : Matrix (Fin 4) (Fin 2) ℝ => chainQ (N := 1) A :=
    (fourByTwo_QLin 1).continuous_of_finiteDimensional
  unfold fourByTwo_quartic fourByTwo_U
  fun_prop

/-- `𝒫` is a homogeneous polynomial of degree four. -/
theorem fourByTwo_quartic_isHomPoly : IsHomogeneousPolynomial 4 fourByTwo_quartic := by
  have hℓ : ∀ j, IsHomogeneousPolynomial 2 fun A : Matrix (Fin 4) (Fin 2) ℝ =>
      ‖((√3 : ℝ) : ℂ) * chainP (N := 1) (√2) A j‖ ^ 2 := fun j =>
    fourByTwo_isHomPoly_congr (fun A => by simp [Complex.real_smul]; rfl)
      (fourByTwo_isHomPoly_normSq ((√3 : ℝ) • fourByTwo_PLin (N := 1) (√2) j))
  have hX : IsHomogeneousPolynomial 2 fun A : Matrix (Fin 4) (Fin 2) ℝ =>
      ∑ j, ‖((√3 : ℝ) : ℂ) * chainP (N := 1) (√2) A j‖ ^ 2 :=
    fourByTwo_isHomPoly_congr (fun A => (Fin.sum_univ_two _).symm)
      (fourByTwo_isHomPoly_add (hℓ 0) (hℓ 1))
  have hY : IsHomogeneousPolynomial 2 fun A : Matrix (Fin 4) (Fin 2) ℝ =>
      ‖chainQ (N := 1) A‖ ^ 2 :=
    fourByTwo_isHomPoly_normSq (fourByTwo_QLin 1)
  refine fourByTwo_isHomPoly_congr (fun A => ?_)
    (fourByTwo_isHomPoly_add (fourByTwo_isHomPoly_const_mul (-2) (fourByTwo_isHomPoly_mul hY hY))
      (fourByTwo_isHomPoly_add (fourByTwo_isHomPoly_const_mul 20 (fourByTwo_isHomPoly_mul hX hY))
        (fourByTwo_isHomPoly_const_mul 30 (fourByTwo_isHomPoly_mul hX hX))))
  simp only [fourByTwo_quartic, fourByTwo_U]
  ring

/-- `𝒫` is rank-one convex: on a rank-one line `B + t R`, `𝒫 = −2 U (x + t h, y + t k)` with
`|k| = |Q (R)| ≤ √3 ‖P_{√2} (R)‖ = |h|` (the rank-one estimate of Proposition 7.1, `N = 1`,
`ρ = √2`), and `U` is zig-zag concave. -/
theorem fourByTwo_quartic_rankOneConvex : RankOneConvex fourByTwo_quartic := by
  intro A B hAB
  set R : Matrix (Fin 4) (Fin 2) ℝ := A - B with hR
  have hrel := fourByTwo_rankOne_bound (N := 1) (Real.sqrt_nonneg 2) R hAB.le
  have h3 : ∑ k ∈ Finset.range (1 + 1), (√2) ^ (2 * k) = 3 := by
    simp [Finset.sum_range_succ, pow_mul]
    norm_num
  rw [h3] at hrel
  set x : Fin 2 → ℂ := fun j => ((√3 : ℝ) : ℂ) * chainP (N := 1) (√2) B j with hx
  set h : Fin 2 → ℂ := fun j => ((√3 : ℝ) : ℂ) * chainP (N := 1) (√2) R j with hh
  have hkh : ‖chainQ (N := 1) R‖ ^ 2 ≤ ∑ j, ‖h j‖ ^ 2 := by
    simp only [hh, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), ← Finset.mul_sum]
    exact hrel
  have hconc := fourByTwo_U_zigzag x h (chainQ (N := 1) B) (chainQ (N := 1) R) hkh
  have hconv := (hconc.smul (by norm_num : (0 : ℝ) ≤ 2)).neg
  have hfun : (fun t : ℝ => fourByTwo_quartic (t • A + (1 - t) • B)) = fun t =>
      -((2 : ℝ) • fun t : ℝ => fourByTwo_U (fun j => x j + t * h j)
        (chainQ (N := 1) B + t * chainQ (N := 1) R)) t := by
    funext t
    have hM : t • A + (1 - t) • B = B + t • R := by rw [hR]; module
    simp only [Pi.smul_apply, smul_eq_mul, fourByTwo_quartic, hM]
    have hP : ∀ j, chainP (N := 1) (√2) (B + t • R) j =
        chainP (N := 1) (√2) B j + t * chainP (N := 1) (√2) R j := fun j => by
      change fourByTwo_PLin (N := 1) (√2) j (B + t • R) = _
      rw [map_add, map_smul, Complex.real_smul]; rfl
    have hQ : chainQ (N := 1) (B + t • R) = chainQ (N := 1) B + t * chainQ (N := 1) R := by
      change fourByTwo_QLin 1 (B + t • R) = _
      rw [map_add, map_smul, Complex.real_smul]; rfl
    rw [hQ, neg_mul]
    congr 3
    funext j
    rw [hP, hx, hh]
    ring
  rw [hfun]
  exact hconv.subset (Set.subset_univ _) (convex_Icc 0 1)

/-! ### Corollary 7.2: from `f_{p,ρ,C}` to its minorant `𝒫` -/

/-- A continuous minorant `g ≤ f` with `g (0) = f (0)` of an integrand `f` that is not
quasiconvex at `0` is not quasiconvex at `0`. -/
theorem fourByTwo_not_quasiconvexAt_of_le {d m : ℕ} {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hg : Continuous g) (hle : ∀ A, g A ≤ f A) (h0 : g 0 = f 0) (hf : ¬ QuasiconvexAt f 0) :
    ¬ QuasiconvexAt g 0 := by
  intro hqc
  refine hf fun φ K hφ hφ0 hint => ?_
  have hint' := fourByTwo_integrableOn_comp_jac hg hφ
  calc f 0 = g 0 := h0.symm
    _ ≤ ∫ x in unitCube m, g (0 + jac φ x) := hqc φ K hφ hφ0 hint'
    _ ≤ ∫ x in unitCube m, f (0 + jac φ x) := integral_mono hint' hint fun x => hle _

/-- **Corollary 7.2** (`cs-cor7.2`): there is a homogeneous polynomial `𝒫 : ℝ^{4×2} → ℝ` of degree
four which is rank-one convex but not quasiconvex at `0`. Conditional on transference
(Proposition 7.2) and Dragičević's bound `‖𝓑²‖_{L⁴} ≥ 21/5`.

Proof (the paper's): `U (x, y) = |y|⁴ − 10 |x|² |y|² − 15 |x|⁴` on `ℂ² × ℂ` (`fourByTwo_U`)
satisfies `2U (x, y) ≥ |y|⁴ − 130 |x|⁴` (`fourByTwo_U_bound`) and is zig-zag concave:
`t ↦ U (x + t h, y + t k)` is concave when `|k| ≤ |h|` (`fourByTwo_U_zigzag`, the "standard
calculation" of its second derivative, `fourByTwo_U_core`). So `𝒫 (A) = −2 U (√3 P_{√2} (A), Q (A))`
(`fourByTwo_quartic`) is a quartic form (`fourByTwo_quartic_isHomPoly`), rank-one convex
because `|Q (R)| ≤ √3 ‖P_{√2} (R)‖` for rank-one `R` (the estimate of Proposition 7.1,
`fourByTwo_rankOne_bound`, with `N = 1`, `ρ = √2`), and a minorant of `f_{4,√2,C₀}`,
`C₀ = 1170^{1/4}`, with the same value `0` at `0`. By Proposition 7.2 and Dragičević,
`C^{qc} (4, 1, √2) ≥ √2 ‖𝓑²‖_{L⁴} ≥ 21 √2 / 5 > C₀`, so `f_{4,√2,C₀}`, and with it its minorant `𝒫`,
is not quasiconvex at `0` (`fourByTwo_not_quasiconvexAt_of_le`). -/
theorem corollary7_2 (hT : HNVWTransference)
    (hD4 : DragicevicL4Bound) :
    ∃ P : Matrix (Fin 4) (Fin 2) ℝ → ℝ, IsHomogeneousPolynomial 4 P ∧ RankOneConvex P ∧
      ¬ QuasiconvexAt P 0 := by
  refine ⟨fourByTwo_quartic, fourByTwo_quartic_isHomPoly, fourByTwo_quartic_rankOneConvex, ?_⟩
  set C0 : ℝ := (1170 : ℝ) ^ ((1 : ℝ) / 4) with hC0def
  have hC0 : 0 < C0 := by positivity
  have hC04 : C0 ^ 4 = 1170 := by
    rw [hC0def, ← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  -- `𝒫 = −2 U (√3 P_{√2}, Q)` is a minorant of `f_{4, √2, C₀}`, since `2U ≥ |y|⁴ − 130 |x|⁴`
  have hle : ∀ A, fourByTwo_quartic A ≤ chainF 1 4 (√2) C0 A := by
    intro A
    have hU := fourByTwo_U_bound (fun j => ((√3 : ℝ) : ℂ) * chainP (N := 1) (√2) A j)
      (chainQ (N := 1) A)
    have h3 : ∑ j, ‖((√3 : ℝ) : ℂ) * chainP (N := 1) (√2) A j‖ ^ 2 =
        3 * ∑ j, ‖chainP (N := 1) (√2) A j‖ ^ 2 := by
      simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), ← Finset.mul_sum]
    rw [h3] at hU
    have hS : 0 ≤ ∑ j, ‖chainP (N := 1) (√2) A j‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    rw [chainF, h4, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast, hC04,
      show √(∑ j, ‖chainP (N := 1) (√2) A j‖ ^ 2) ^ 4 =
        (√(∑ j, ‖chainP (N := 1) (√2) A j‖ ^ 2) ^ 2) ^ 2 by ring, Real.sq_sqrt hS]
    unfold fourByTwo_quartic
    nlinarith [hU]
  have h0 : fourByTwo_quartic 0 = chainF 1 4 (√2) C0 0 := by
    rw [fourByTwo_chainF_zero 1 (by norm_num) (√2) C0]
    have hP0 : ∀ j, chainP (N := 1) (√2) (0 : Matrix (Fin 4) (Fin 2) ℝ) j = 0 :=
      fun j => (fourByTwo_PLin (N := 1) (√2) j).map_zero
    have hQ0 : chainQ (N := 1) (0 : Matrix (Fin 4) (Fin 2) ℝ) = 0 := (fourByTwo_QLin 1).map_zero
    simp [fourByTwo_quartic, fourByTwo_U, hP0, hQ0]
  -- Proposition 7.2 and Dragičević: `C^{qc} (4, 1, √2) ≥ √2 ‖𝓑²‖_{L⁴} ≥ 21 √2 / 5 > C₀`
  have hqc : ENNReal.ofReal C0 < qcThreshold (chainF 1 4 (√2)) := by
    have h72 := proposition7_2_lower hT 1 (Real.sqrt_pos.mpr two_pos) (by norm_num : (1 : ℝ) < 4)
    rw [pow_one] at h72
    refine lt_of_lt_of_le ?_ ((mul_le_mul_right hD4 _).trans h72)
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    refine lt_of_pow_lt_pow_left₀ 4 (by positivity) ?_
    rw [hC04, mul_pow, show (√2 : ℝ) ^ 4 = (√2 ^ 2) ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  exact fourByTwo_not_quasiconvexAt_of_le fourByTwo_quartic_continuous hle h0
    (fourByTwo_not_quasiconvexAt_of_lt _ hC0.le hqc)

end Cassese
