module

public import Morrey.Cassese.Toolkit
public import Morrey.Cassese.Bridges
public import Morrey.Common.External.Rindler.Lemmas
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Convex.Deriv
public import HarmonicAnalysis.BeurlingAhlfors.Periodic
public import CalculusOfVariations.Lipschitz.Mollify
public import Morrey.Cassese.Hypotheses
public import Morrey.Cassese.Rademacher

/-!
# Section 7: another example, `ℝ^{4×2}`

`ℝ^{2(N+1)×2}` is identified with the real-linear maps `ℂ → ℂ^{N+1}`: `A = (A₀, …, A_N)` stacked
by rows, block `j` (from `0`) formed by the rows `2j` and `2j + 1` (`rowBlock`), and
`A_j z = α_j z + β_j z̄` (`alphaRow`, `betaRow`; same formulas as in Section 4). For `ρ > 0`,
`P_ρ (A) = (β₀, β₁ − ρ α₀, …, β_N − ρ α_{N−1})` (`chainP`), `Q (A) = α_N` (`chainQ`), and
`chainF N p ρ C (A) = C^p ‖P_ρ (A)‖_{ℓ₂}^p − |Q (A)|^p`, with thresholds
`C^{rc} (p, N, ρ) = rcThreshold (chainF N p ρ)` and `C^{qc} (p, N, ρ) = qcThreshold (chainF N p ρ)`.

`chainOpNorm N p ρ` is the norm of `(h₀, …, h_N) ↦ Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j` from
`L^p_0 (𝕋²; ℓ₂^{N+1})` to `L^p_0 (𝕋²)`, computed on the dense subspace of smooth mean-zero tuples,
as in the paper's proof: a function on `𝕋² = ℝ² / ℤ²` is a `ℤ²`-periodic function on `ℝ²`, its
`L^p (𝕋²)` norm is the `L^p` norm on the unit square `(0, 1)²`, and `𝓑^k` is the torus multiplier
with symbol `m (n)^k`, `m (n) = ξ̄ / ξ` at `ξ = n₀ + i n₁`, `m (0) = 0`
(`UnitAddTorus.periodicMultiplier`, from the package `HarmonicAnalysis`).

The helpers (prefix `fourByTwo_`) package the steps of the paper's proofs:

* Proposition 7.1: linearity of `α_j`, `β_j`, `P_ρ`, `Q`; the rank-one estimate
  `|Q (R)|² ≤ (Σ_k ρ^{2k}) ‖P_ρ (R)‖²` (`fourByTwo_rankOne_bound`); Rademacher martingales on
  `{±1}^n` as martingales of Mathlib (`rad_filtration`, `rad_martingale`, in
  `Morrey/Cassese/Rademacher.lean`), and
  Burkholder's inequality for their linear images (`fourByTwo_burkholder`).
* Proposition 7.2: for a test map `φ`, the complex components `u_j = φ_{2j} + i φ_{2j+1}`
  (`fourByTwo_u`), with `α_j (∇φ) = ∂u_j`, `β_j (∇φ) = ∂̄u_j` (`fourByTwo_alphaRow_jac`,
  `fourByTwo_betaRow_jac`) and `P_ρ (∇φ)_j = h_j = ∂̄u_j − ρ ∂u_{j−1}` (`fourByTwo_chainP_jac`);
  for smooth `ℤ²`-periodic `φ`, the tuple `(h_j)` is smooth, periodic and mean-zero, and
  `Q (∇φ) = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j` (`fourByTwo_chainQ_jac`, by the induction
  `fourByTwo_telescope` frequency by frequency); `L^p` norms on the unit square
  (`fourByTwo_eLpNorm_cube`, `fourByTwo_integral_nonneg_iff`) and on the torus
  (`fourByTwo_eLpNorm_torus`). The inequality `C^{qc} ≥ chainOpNorm`
  (`fourByTwo_chainOpNorm_le_qcThreshold`): the solution of `∂̄u_j = h_j + ρ ∂u_{j−1}`
  (`fourByTwo_solve`, by the inverse of `∂̄` on mean-zero functions), the real test map with rows
  `Re u_j`, `Im u_j` (`fourByTwo_reIm`), and Lemma 2.2 (periodic test maps,
  `External.Rindler.quasiconvexAtOn_iff_periodic`). The inequality `C^{qc} ≤ chainOpNorm`
  (`fourByTwo_qcThreshold_le_chainOpNorm`): `∫ f (∇u) ≥ 0` for smooth periodic `u`
  (`fourByTwo_integral_chainF_nonneg_of_smooth`), extended to Lipschitz periodic maps by
  mollification and dominated convergence (`fourByTwo_integral_nonneg_of_smooth`; the paper leaves
  this step implicit, inventory item E28, filled here), and Lemma 2.2.
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

open scoped ContDiff in
/-- `‖(ρ^N 𝓑^{N+1}, ρ^{N−1} 𝓑^N, …, ρ 𝓑², 𝓑)‖_{L^p_0 (𝕋²; ℓ₂^{N+1}) → L^p_0 (𝕋²)}`: the supremum
of `‖Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j‖_p / ‖(h_j)‖_{L^p (ℓ₂)}` over the smooth mean-zero tuples
`(h₀, …, h_N)`, which are dense in `L^p_0 (𝕋²; ℓ₂^{N+1})`, as in the paper's proof.

A function on `𝕋² = ℝ² / ℤ²` is a `ℤ²`-periodic function on `ℝ²` (`UnitAddTorus.IsPeriodic`);
its mean and its `L^p (𝕋²)` norm are the integral and the `L^p` norm on the unit square `(0, 1)²`
(`unitCube 2`, of measure `1`). `𝓑^k` is the torus multiplier with symbol `m (n)^k`,
`m (n) = ξ̄ / ξ` at `ξ = n₀ + i n₁` (`HarmonicAnalysis.beurlingSymbol`,
`HarmonicAnalysis.latticePoint`), `m (0) = 0`: `g ↦ Σ_n m (n)^k ĝ (n) e_n`
(`UnitAddTorus.periodicMultiplier`, the series converging absolutely for smooth `g`), which on
smooth functions is the `k`-th power of `𝓑` (`UnitAddTorus.periodicMultiplier_periodicMultiplier`).
-/
noncomputable def chainOpNorm (N : ℕ) (p ρ : ℝ) : ℝ≥0∞ :=
  ⨆ (h : Fin (N + 1) → (Fin 2 → ℝ) → ℂ)
    (_ : ∀ j, ContDiff ℝ ∞ (h j) ∧ UnitAddTorus.IsPeriodic (h j) ∧ ∫ x in unitCube 2, h j x = 0),
    eLpNorm (fun x => ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
        UnitAddTorus.periodicMultiplier (fun n =>
          HarmonicAnalysis.beurlingSymbol (HarmonicAnalysis.latticePoint n) ^ (N + 1 - j.val))
          (h j) x)
      (ENNReal.ofReal p) (volume.restrict (unitCube 2)) /
    eLpNorm (fun x => √(∑ j, ‖h j x‖ ^ 2)) (ENNReal.ofReal p) (volume.restrict (unitCube 2))

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

/-- The results of [Cassese 2025] used in the proof of Proposition 7.1, through Burkholder's
inequality (Theorem 2.3): if two linear maps `L_X`, `L_Y` into a separable Hilbert space satisfy
`‖L_X (R)‖ ≤ ‖L_Y (R)‖` on the matrices of rank at most one, then for every rank-one Rademacher
martingale `M` started at `0`, the martingale `L_X (M)` is differentially subordinate to
`L_Y (M)`, so `E ‖L_X (M_n)‖^p ≤ (p* − 1)^p E ‖L_Y (M_n)‖^p`. -/
theorem fourByTwo_burkholder {d m : ℕ} {H : Type}
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
    rw [rad_mart_succ, rad_mart_succ, add_sub_cancel_left, add_sub_cancel_left]
    split_ifs with h
    · rw [norm_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (hXY _ (hA.2 _ _)) (norm_nonneg _)
    · simp
  have key := burkholderInequality_holds (Fin n → Bool) inferInstance
    (ProbabilityTheory.uniformOn Set.univ)
    (rad_filtration n) H (fun k => mart ξX k) (fun k => mart ξY k) p hp
    (rad_martingale ξX hpX) (rad_martingale ξY hpY) (rad_mart_zero ξX)
    (rad_mart_zero ξY) (fun k => ae_of_all _ (hsub k)) n
  rw [rad_eLpNorm_uniform _ hp0, rad_eLpNorm_uniform _ hp0,
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
`C^{rc} (p, N, ρ) ≤ (p* − 1) (Σ_{k=0}^N ρ^{2k})^{1/2}`. By Burkholder's inequality
(Theorem 2.3), through "the results of [Cassese 2025]".

Proof (the paper's). By Proposition 2.5 (`proposition2_5`), `f_{p,ρ,K}` with
`K = (p* − 1) (Σ ρ^{2k})^{1/2}` is rank-one convex at `0` once `E |Q (M_n)|^p ≤ K^p E ‖P_ρ (M_n)‖^p`
for every rank-one Rademacher martingale `M` started at `0`. "The results of [Cassese 2025]"
(`C^{rc} ≤ (p* − 1) sup_{A ∈ ℛ₁} |Q (A)| / ‖P_ρ (A)‖`; Theorem 2.1 there, stated for the orthogonal
projections onto a subspace and its complement, whose proof carries over) are used in the form
`fourByTwo_burkholder`, proved by their standard argument: `Q (M)` and `√S P_ρ (M)` are martingales
in `ℂ^{N+1}` (`rad_martingale`) and the first is differentially subordinate to the second
when `|Q| ≤ √S ‖P_ρ‖` on rank-one matrices, so Burkholder's inequality applies. That bound, with
`√S = (Σ_{k=0}^N ρ^{2k})^{1/2}`, is the paper's computation (`fourByTwo_rankOne_bound`:
`β_j = ω α_j`, `γ_j = α_j − ρ ω̄ α_{j−1}`, Cauchy–Schwarz). -/
theorem proposition7_1 (N : ℕ) {ρ : ℝ}
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
  have key := fourByTwo_burkholder LX LY hXY hp n A hA
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

/-- For a continuous `g` and a Lipschitz `φ`, `x ↦ g (∇φ (x))` is integrable on the unit cube. -/
theorem fourByTwo_integrableOn_comp_jac {d m : ℕ} {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hg : Continuous g) {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) :
    IntegrableOn (fun x => g (0 + jac φ x)) (unitCube m) := by
  obtain ⟨M, hM⟩ := (isCompact_univ_pi fun _ : Fin d => isCompact_univ_pi fun _ : Fin m =>
    isCompact_Icc (a := -(K : ℝ)) (b := K)).exists_bound_of_continuousOn hg.continuousOn
  simp only [zero_add]
  refine Measure.integrableOn_of_bounded (M := M) ?_
    (hg.measurable.comp (measurable_jac φ)).aestronglyMeasurable
    (ae_of_all _ fun x => hM _ ?_)
  · rw [unitCube, Real.volume_pi_Ioo]
    simp
  · exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun k =>
      abs_le.mp (abs_jac_le hφ x i k)

section Proposition72

open scoped ContDiff

/-! ### Proposition 7.2: smooth periodic test maps

A function on the torus `𝕋² = ℝ² / ℤ²` is a `ℤ²`-periodic function on `ℝ²`
(`UnitAddTorus.IsPeriodic`); its Fourier coefficients `ĝ (n)`, its mean `ĝ (0)` and its
`L^p (𝕋²)` norm are taken over the unit square `(0, 1)²` (`UnitAddTorus.cubeFourierCoeff`,
`unitCube 2`). For a test map `φ : ℝ² → ℝ^{2(N+1)}`, `u_j = φ_{2j} + i φ_{2j+1}` (`fourByTwo_u`),
so that `α_j (∇φ) = ∂u_j` and `β_j (∇φ) = ∂̄u_j`, with the Wirtinger derivatives
`∂ = ½ (∂_x − i ∂_y)` and `∂̄ = ½ (∂_x + i ∂_y)` (`UnitAddTorus.dzPi`, `UnitAddTorus.dzbarPi`),
whose symbols are `πi ν̄` and `πi ν` at the frequency `n`, `ν = n₀ + i n₁`
(`HarmonicAnalysis.latticePoint`). -/

/-- `u_j = φ_{2j} + i φ_{2j+1}`: block `j` of `φ : ℝ² → ℝ^{2(N+1)}` as a complex function. -/
noncomputable def fourByTwo_u {N : ℕ} (φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ)
    (j : Fin (N + 1)) (x : Fin 2 → ℝ) : ℂ :=
  (φ x (rowBlock j 0) : ℂ) + Complex.I * (φ x (rowBlock j 1) : ℂ)

/-- `u_j` is smooth when `φ` is. -/
theorem fourByTwo_contDiff_u {N : ℕ} {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (j : Fin (N + 1)) : ContDiff ℝ ∞ (fourByTwo_u φ j) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_pi.1 hφ _)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_pi.1 hφ _)))

/-- `u_j` is periodic when `φ` is. -/
theorem fourByTwo_isPeriodic_u {N : ℕ} {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    (hper : UnitAddTorus.IsPeriodic φ) (j : Fin (N + 1)) :
    UnitAddTorus.IsPeriodic (fourByTwo_u φ j) :=
  fun x k => by simp only [fourByTwo_u, hper x k]

/-- The partial derivatives of `u_j` are those of `φ_{2j}` and `φ_{2j+1}`. -/
theorem fourByTwo_fderiv_u {N : ℕ} {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    (hφ : Differentiable ℝ φ) (j : Fin (N + 1)) (x v : Fin 2 → ℝ) :
    fderiv ℝ (fourByTwo_u φ j) x v = (fderiv ℝ (fun y => φ y (rowBlock j 0)) x v : ℂ) +
      Complex.I * (fderiv ℝ (fun y => φ y (rowBlock j 1)) x v : ℂ) := by
  have hd : ∀ r, HasFDerivAt (fun y => (φ y r : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun y => φ y r) x)) x := fun r =>
    Complex.ofRealCLM.hasFDerivAt.comp x ((differentiable_pi.1 hφ r) x).hasFDerivAt
  have e : fourByTwo_u φ j =
      fun y => (φ y (rowBlock j 0) : ℂ) + Complex.I * (φ y (rowBlock j 1) : ℂ) := rfl
  rw [e, ((hd _).fun_add ((hd _).const_mul Complex.I)).fderiv]
  simp

/-- `α_j (∇φ) = ∂u_j`. -/
theorem fourByTwo_alphaRow_jac {N : ℕ} {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    (hφ : Differentiable ℝ φ) (x : Fin 2 → ℝ) (j : Fin (N + 1)) :
    alphaRow (jac φ x) j = UnitAddTorus.dzPi (fourByTwo_u φ j) x := by
  rw [UnitAddTorus.dzPi, fourByTwo_fderiv_u hφ, fourByTwo_fderiv_u hφ]
  apply Complex.ext <;> simp [alphaRow, jac] <;> ring

/-- `β_j (∇φ) = ∂̄u_j`. -/
theorem fourByTwo_betaRow_jac {N : ℕ} {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    (hφ : Differentiable ℝ φ) (x : Fin 2 → ℝ) (j : Fin (N + 1)) :
    betaRow (jac φ x) j = UnitAddTorus.dzbarPi (fourByTwo_u φ j) x := by
  rw [UnitAddTorus.dzbarPi, fourByTwo_fderiv_u hφ, fourByTwo_fderiv_u hφ]
  apply Complex.ext <;> simp [betaRow, jac] <;> ring

/-- `P_ρ (∇φ)_j = h_j = ∂̄u_j − ρ ∂u_{j−1}` (`∂u_{−1} = 0`). -/
theorem fourByTwo_chainP_jac {N : ℕ} (ρ : ℝ) {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    (hφ : Differentiable ℝ φ) (x : Fin 2 → ℝ) (j : Fin (N + 1)) :
    chainP ρ (jac φ x) j = UnitAddTorus.dzbarPi (fourByTwo_u φ j) x -
      if j.val = 0 then 0
      else (ρ : ℂ) * UnitAddTorus.dzPi (fourByTwo_u φ ⟨j.val - 1, by omega⟩) x := by
  unfold chainP
  split_ifs <;> simp [fourByTwo_alphaRow_jac hφ, fourByTwo_betaRow_jac hφ]

/-- `∇φ` is periodic when `φ` is. -/
theorem fourByTwo_jac_periodic {d : ℕ} {φ : (Fin 2 → ℝ) → Fin d → ℝ}
    (hper : UnitAddTorus.IsPeriodic φ) (x : Fin 2 → ℝ) (z : Fin 2 → ℤ) :
    jac φ (x + fun i => (z i : ℝ)) = jac φ x := by
  ext r k
  simp only [jac, Matrix.of_apply]
  rw [← fderiv_comp_add_right]
  have : (fun y => φ (y + fun i => (z i : ℝ)) r) = fun y => φ y r :=
    funext fun y => by rw [hper]
  rw [this]

/-- The tuple `h_j = P_ρ (∇φ)_j` of a smooth `φ` is smooth. -/
theorem fourByTwo_contDiff_chainP {N : ℕ} (ρ : ℝ) {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (j : Fin (N + 1)) : ContDiff ℝ ∞ fun x => chainP ρ (jac φ x) j := by
  simp_rw [fourByTwo_chainP_jac ρ (hφ.differentiable (by simp))]
  by_cases hj : j.val = 0
  · simpa only [hj, ↓reduceIte, sub_zero] using
      UnitAddTorus.contDiff_dzbarPi (fourByTwo_contDiff_u hφ j)
  · simp only [hj, ↓reduceIte]
    exact (UnitAddTorus.contDiff_dzbarPi (fourByTwo_contDiff_u hφ j)).sub
      (contDiff_const.mul (UnitAddTorus.contDiff_dzPi (fourByTwo_contDiff_u hφ _)))

/-- The tuple `h_j = P_ρ (∇φ)_j` of a periodic `φ` is periodic. -/
theorem fourByTwo_isPeriodic_chainP {N : ℕ} (ρ : ℝ)
    {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ} (hper : UnitAddTorus.IsPeriodic φ)
    (j : Fin (N + 1)) : UnitAddTorus.IsPeriodic fun x => chainP ρ (jac φ x) j :=
  fun x k => by simp only [fourByTwo_jac_periodic hper]

/-- The mean of `g` over the unit square is its coefficient `ĝ (0)`. -/
theorem fourByTwo_cubeFourierCoeff_zero (g : (Fin 2 → ℝ) → ℂ) :
    UnitAddTorus.cubeFourierCoeff g 0 = ∫ x in unitCube 2, g x := by
  simp only [UnitAddTorus.cubeFourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul]
  rfl

/-- The coefficients of a sum of continuous functions. -/
theorem fourByTwo_cubeFourierCoeff_add {g g' : (Fin 2 → ℝ) → ℂ} (hg : Continuous g)
    (hg' : Continuous g') (n : Fin 2 → ℤ) :
    UnitAddTorus.cubeFourierCoeff (fun x => g x + g' x) n =
      UnitAddTorus.cubeFourierCoeff g n + UnitAddTorus.cubeFourierCoeff g' n := by
  simp only [UnitAddTorus.cubeFourierCoeff, mul_add]
  exact integral_add (UnitAddTorus.integrableOn_cube_of_continuous
    ((UnitAddTorus.continuous_mFourier_ofPi _).mul hg))
    (UnitAddTorus.integrableOn_cube_of_continuous
      ((UnitAddTorus.continuous_mFourier_ofPi _).mul hg'))

/-- The coefficients of a difference of continuous functions. -/
theorem fourByTwo_cubeFourierCoeff_sub {g g' : (Fin 2 → ℝ) → ℂ} (hg : Continuous g)
    (hg' : Continuous g') (n : Fin 2 → ℤ) :
    UnitAddTorus.cubeFourierCoeff (fun x => g x - g' x) n =
      UnitAddTorus.cubeFourierCoeff g n - UnitAddTorus.cubeFourierCoeff g' n := by
  simp only [UnitAddTorus.cubeFourierCoeff, mul_sub]
  exact integral_sub (UnitAddTorus.integrableOn_cube_of_continuous
    ((UnitAddTorus.continuous_mFourier_ofPi _).mul hg))
    (UnitAddTorus.integrableOn_cube_of_continuous
      ((UnitAddTorus.continuous_mFourier_ofPi _).mul hg'))

/-- The coefficients of a finite sum of continuous functions. -/
theorem fourByTwo_cubeFourierCoeff_sum {ι : Type*} (s : Finset ι)
    {g : ι → (Fin 2 → ℝ) → ℂ} (hg : ∀ i ∈ s, Continuous (g i)) (n : Fin 2 → ℤ) :
    UnitAddTorus.cubeFourierCoeff (fun x => ∑ i ∈ s, g i x) n =
      ∑ i ∈ s, UnitAddTorus.cubeFourierCoeff (g i) n := by
  simp only [UnitAddTorus.cubeFourierCoeff, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => UnitAddTorus.integrableOn_cube_of_continuous
    ((UnitAddTorus.continuous_mFourier_ofPi _).mul (hg i hi))

/-- The coefficients of `h_j = ∂̄u_j − ρ ∂u_{j−1}`: `ĥ_j (n) = πi ν û_j (n) − ρ πi ν̄ û_{j−1} (n)`,
`ν = n₀ + i n₁`. -/
theorem fourByTwo_cubeFourierCoeff_chainP {N : ℕ} (ρ : ℝ)
    {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hper : UnitAddTorus.IsPeriodic φ) (j : Fin (N + 1)) (n : Fin 2 → ℤ) :
    UnitAddTorus.cubeFourierCoeff (fun x => chainP ρ (jac φ x) j) n =
      Real.pi * Complex.I * HarmonicAnalysis.latticePoint n *
          UnitAddTorus.cubeFourierCoeff (fourByTwo_u φ j) n -
        if j.val = 0 then 0
        else (ρ : ℂ) * (Real.pi * Complex.I * starRingEnd ℂ (HarmonicAnalysis.latticePoint n) *
          UnitAddTorus.cubeFourierCoeff (fourByTwo_u φ ⟨j.val - 1, by omega⟩) n) := by
  have h1 : ∀ i, ContDiff ℝ 1 (fourByTwo_u φ i) := fun i =>
    (fourByTwo_contDiff_u hφ i).of_le (by exact_mod_cast le_top)
  simp_rw [fourByTwo_chainP_jac ρ (hφ.differentiable (by simp))]
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte, sub_zero]
    exact UnitAddTorus.cubeFourierCoeff_dzbarPi (h1 j) (fourByTwo_isPeriodic_u hper j) n
  · simp only [hj, ↓reduceIte]
    rw [fourByTwo_cubeFourierCoeff_sub (UnitAddTorus.contDiff_dzbarPi
      (fourByTwo_contDiff_u hφ j)).continuous (continuous_const.fun_mul
      (UnitAddTorus.contDiff_dzPi (fourByTwo_contDiff_u hφ _)).continuous),
      UnitAddTorus.cubeFourierCoeff_const_mul,
      UnitAddTorus.cubeFourierCoeff_dzbarPi (h1 j) (fourByTwo_isPeriodic_u hper j),
      UnitAddTorus.cubeFourierCoeff_dzPi (h1 _) (fourByTwo_isPeriodic_u hper _)]

/-- The tuple `h_j = P_ρ (∇φ)_j` of a smooth periodic `φ` has mean zero. -/
theorem fourByTwo_integral_chainP {N : ℕ} (ρ : ℝ)
    {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hper : UnitAddTorus.IsPeriodic φ) (j : Fin (N + 1)) :
    ∫ x in unitCube 2, chainP ρ (jac φ x) j = 0 := by
  rw [← fourByTwo_cubeFourierCoeff_zero, fourByTwo_cubeFourierCoeff_chainP ρ hφ hper]
  simp [HarmonicAnalysis.latticePoint_zero]

/-! ### Proposition 7.2: the identity `Q (∇u) = Σ_j ρ^{N−j} 𝓑^{N+1−j} P_ρ (∇u)_j` -/

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
    HarmonicAnalysis.beurlingSymbol ξ * (Real.pi * Complex.I * ξ) =
      Real.pi * Complex.I * starRingEnd ℂ ξ := by
  by_cases h : ξ = 0
  · simp [h, HarmonicAnalysis.beurlingSymbol]
  · rw [HarmonicAnalysis.beurlingSymbol]; field_simp

/-- The identity of the proof of Proposition 7.2 (TeX lines 2808–2821), for a smooth
`ℤ²`-periodic test map `φ`: with `h_j = P_ρ (∇φ)_j = ∂̄u_j − ρ ∂u_{j−1}`,
`Q (∇φ) = ∂u_N = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j`. The paper's induction from `𝓑 (∂̄w) = ∂w` is made
frequency by frequency (`fourByTwo_telescope`, with `m (ν) πi ν = πi ν̄`), and the two smooth
periodic sides are equal since their coefficients are (`UnitAddTorus.eq_of_cubeFourierCoeff_eq`). -/
theorem fourByTwo_chainQ_jac {N : ℕ} (ρ : ℝ) {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hper : UnitAddTorus.IsPeriodic φ) (x : Fin 2 → ℝ) :
    chainQ (jac φ x) = ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
      UnitAddTorus.periodicMultiplier (fun n =>
        HarmonicAnalysis.beurlingSymbol (HarmonicAnalysis.latticePoint n) ^ (N + 1 - j.val))
        (fun y => chainP ρ (jac φ y) j) x := by
  have h1 : ∀ i, ContDiff ℝ 1 (fourByTwo_u φ i) := fun i =>
    (fourByTwo_contDiff_u hφ i).of_le (by exact_mod_cast le_top)
  have hT : ∀ j : Fin (N + 1), ContDiff ℝ ∞ (UnitAddTorus.periodicMultiplier (fun n =>
      HarmonicAnalysis.beurlingSymbol (HarmonicAnalysis.latticePoint n) ^ (N + 1 - j.val))
      (fun y => chainP ρ (jac φ y) j)) := fun j =>
    UnitAddTorus.contDiff_periodicMultiplier (HarmonicAnalysis.isPolyBounded_beurlingSymbol_pow _)
      (fourByTwo_contDiff_chainP ρ hφ j) (fourByTwo_isPeriodic_chainP ρ hper j)
  rw [chainQ, fourByTwo_alphaRow_jac (hφ.differentiable (by simp))]
  refine congrFun (UnitAddTorus.eq_of_cubeFourierCoeff_eq
    (UnitAddTorus.contDiff_dzPi (fourByTwo_contDiff_u hφ _))
    (UnitAddTorus.isPeriodic_dzPi (fourByTwo_isPeriodic_u hper _))
    (ContDiff.sum fun j _ => contDiff_const.mul (hT j))
    (fun y k => by simp only [UnitAddTorus.isPeriodic_periodicMultiplier _ _ y k])
    fun n => ?_) x
  rw [UnitAddTorus.cubeFourierCoeff_dzPi (h1 _) (fourByTwo_isPeriodic_u hper _),
    fourByTwo_cubeFourierCoeff_sum _ fun j _ => continuous_const.fun_mul (hT j).continuous]
  have e : ∀ j : Fin (N + 1), UnitAddTorus.cubeFourierCoeff (fun y => ((ρ ^ (N - j.val) : ℝ) : ℂ) *
      UnitAddTorus.periodicMultiplier (fun n =>
        HarmonicAnalysis.beurlingSymbol (HarmonicAnalysis.latticePoint n) ^ (N + 1 - j.val))
        (fun y => chainP ρ (jac φ y) j) y) n =
      ((ρ ^ (N - j.val) : ℝ) : ℂ) * (HarmonicAnalysis.beurlingSymbol
        (HarmonicAnalysis.latticePoint n) ^ (N + 1 - j.val) *
        UnitAddTorus.cubeFourierCoeff (fun y => chainP ρ (jac φ y) j) n) := fun j => by
    rw [UnitAddTorus.cubeFourierCoeff_const_mul, UnitAddTorus.cubeFourierCoeff_periodicMultiplier
      (HarmonicAnalysis.isPolyBounded_beurlingSymbol_pow _) (fourByTwo_contDiff_chainP ρ hφ j)
      (fourByTwo_isPeriodic_chainP ρ hper j)]
  simp_rw [e, fourByTwo_cubeFourierCoeff_chainP ρ hφ hper]
  -- the induction, frequency by frequency
  set ν := HarmonicAnalysis.latticePoint n
  set m := HarmonicAnalysis.beurlingSymbol ν
  set c : ℕ → ℂ := fun i => if hi : i < N + 1 then
    UnitAddTorus.cubeFourierCoeff (fourByTwo_u φ ⟨i, hi⟩) n else 0 with hc
  have ht := fourByTwo_telescope (ρ : ℂ) m (fun i => Real.pi * Complex.I * ν * c i)
    (fun i => Real.pi * Complex.I * starRingEnd ℂ ν * c i)
    (fun i => by rw [← mul_assoc, fourByTwo_beurlingSymbol_mul]) N
  have hcN : c N = UnitAddTorus.cubeFourierCoeff (fourByTwo_u φ (Fin.last N)) n := by
    simp [hc, Fin.last]
  rw [← hcN, ← ht, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcj : c j.val = UnitAddTorus.cubeFourierCoeff (fourByTwo_u φ j) n := by
    simp only [hc, j.isLt, ↓reduceDIte, Fin.eta]
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte, sub_zero, ← hcj]
    push_cast
    ring
  · have hcj' : c (j.val - 1) =
        UnitAddTorus.cubeFourierCoeff (fourByTwo_u φ ⟨j.val - 1, by omega⟩) n := by
      simp only [hc, show j.val - 1 < N + 1 by omega, ↓reduceDIte]
    simp only [hj, ↓reduceIte, ← hcj, ← hcj']
    push_cast
    ring

/-! ### Proposition 7.2: `L^p` norms on the unit square and on the torus -/

/-- Continuous functions are integrable on the unit square. -/
theorem fourByTwo_integrableOn_cube {g : (Fin 2 → ℝ) → ℝ} (hg : Continuous g) :
    IntegrableOn g (unitCube 2) :=
  (hg.integrableOn_Icc (a := 0) (b := 1)).mono_set fun _ hx =>
    ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩

/-- `‖F‖_{L^p ((0,1)²)} = (∫_{(0,1)²} ‖F (x)‖^p dx)^{1/p}` for continuous `F`. -/
theorem fourByTwo_eLpNorm_cube {E : Type*} [NormedAddCommGroup E] {F : (Fin 2 → ℝ) → E}
    (hF : Continuous F) {p : ℝ} (hp : 0 < p) :
    eLpNorm F (ENNReal.ofReal p) (volume.restrict (unitCube 2)) =
      ENNReal.ofReal ((∫ x in unitCube 2, ‖F x‖ ^ p) ^ (1 / p)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    hF.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  have hc : Continuous fun x => ‖F x‖ ^ p := hF.norm.rpow_const fun _ => Or.inr hp.le
  have hnn : 0 ≤ ∫ x in unitCube 2, ‖F x‖ ^ p :=
    setIntegral_nonneg (by simp [unitCube, MeasurableSet.univ_pi, measurableSet_Ioo])
      fun x _ => by positivity
  rw [← ENNReal.ofReal_rpow_of_nonneg hnn (by positivity),
    ofReal_integral_eq_lintegral_ofReal (fourByTwo_integrableOn_cube hc)
      (ae_of_all _ fun x => by positivity)]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]

/-- `∫_{(0,1)²} (K^p ‖H‖^p − ‖T‖^p) ≥ 0` if and only if `‖T‖_p ≤ K ‖H‖_p` (norms in
`L^p ((0,1)²)`), for continuous `H`, `T`. -/
theorem fourByTwo_integral_nonneg_iff {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {H : (Fin 2 → ℝ) → E} {T : (Fin 2 → ℝ) → F} (hH : Continuous H) (hT : Continuous T)
    {p K : ℝ} (hp : 0 < p) (hK : 0 ≤ K) :
    0 ≤ ∫ x in unitCube 2, (K ^ p * ‖H x‖ ^ p - ‖T x‖ ^ p) ↔
      eLpNorm T (ENNReal.ofReal p) (volume.restrict (unitCube 2)) ≤
        ENNReal.ofReal K * eLpNorm H (ENNReal.ofReal p) (volume.restrict (unitCube 2)) := by
  have iH : IntegrableOn (fun x => ‖H x‖ ^ p) (unitCube 2) :=
    fourByTwo_integrableOn_cube (hH.norm.rpow_const fun _ => Or.inr hp.le)
  have iT : IntegrableOn (fun x => ‖T x‖ ^ p) (unitCube 2) :=
    fourByTwo_integrableOn_cube (hT.norm.rpow_const fun _ => Or.inr hp.le)
  have hms : MeasurableSet (unitCube 2) := by
    simp [unitCube, MeasurableSet.univ_pi, measurableSet_Ioo]
  have hnH : 0 ≤ ∫ x in unitCube 2, ‖H x‖ ^ p :=
    setIntegral_nonneg hms fun x _ => by positivity
  have hnT : 0 ≤ ∫ x in unitCube 2, ‖T x‖ ^ p :=
    setIntegral_nonneg hms fun x _ => by positivity
  rw [integral_sub (iH.const_mul _) iT, integral_const_mul, sub_nonneg,
    fourByTwo_eLpNorm_cube hT hp, fourByTwo_eLpNorm_cube hH hp, ← ENNReal.ofReal_mul hK,
    ENNReal.ofReal_le_ofReal_iff (by positivity),
    ← Real.rpow_le_rpow_iff (Real.rpow_nonneg hnT _) (by positivity) hp,
    Real.mul_rpow hK (Real.rpow_nonneg hnH _), one_div, Real.rpow_inv_rpow hnT hp.ne',
    Real.rpow_inv_rpow hnH hp.ne']

/-- Integrals over the torus `𝕋² = ℝ² / ℤ²` (normalised Haar measure) are integrals of the lifts
over the unit square. -/
theorem fourByTwo_lintegral_torus (f : UnitAddTorus (Fin 2) → ℝ≥0∞) :
    ∫⁻ z, f z = ∫⁻ x in unitCube 2, f (UnitAddTorus.ofPi x) := by
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

/-- `‖F‖_{L^p (𝕋²)} = ‖F ∘ π‖_{L^p ((0,1)²)}`, `π : ℝ² → 𝕋²` the projection. -/
theorem fourByTwo_eLpNorm_torus {E : Type*} [NormedAddCommGroup E]
    {F : UnitAddTorus (Fin 2) → E} (hF : Continuous F) {p : ℝ} (hp : 0 < p) :
    eLpNorm F (ENNReal.ofReal p) volume =
      eLpNorm (fun x => F (UnitAddTorus.ofPi x)) (ENNReal.ofReal p)
        (volume.restrict (unitCube 2)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    hF.aestronglyMeasurable, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp)
    ENNReal.ofReal_ne_top (hF.comp UnitAddTorus.continuous_ofPi).aestronglyMeasurable (f := fun x =>
      F (UnitAddTorus.ofPi x)),
    fourByTwo_lintegral_torus]

/-- Trigonometric polynomials are continuous on `𝕋²`. -/
theorem fourByTwo_continuous_trigPoly (c : (Fin 2 → ℤ) →₀ ℂ) : Continuous (trigPoly c) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (UnitAddTorus.mFourier n).continuous

/-- `𝓑^k` of a trigonometric polynomial is continuous on `𝕋²`. -/
theorem fourByTwo_continuous_torusBeurlingPow (k : ℕ) (c : (Fin 2 → ℤ) →₀ ℂ) :
    Continuous (torusBeurlingPow k c) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (UnitAddTorus.mFourier n).continuous

/-- A continuous integrand is locally bounded. -/
theorem fourByTwo_isLocallyBounded {d m : ℕ} {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Continuous f) : CalculusOfVariations.IsLocallyBounded f := by
  intro A
  refine ⟨f ⁻¹' Metric.ball (f A) 1, hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _
    one_pos), |f A| + 1, fun B hB => ?_⟩
  have := abs_sub_abs_le_abs_sub (f B) (f A)
  rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hB
  linarith

/-! ### Proposition 7.2: `C^{qc} ≥ ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖`

"Conversely, every smooth mean-zero tuple `(h_j)` is obtained by solving recursively
`∂̄u_j = h_j + ρ ∂u_{j−1}`, which is possible since `∂̄` is invertible on mean-zero functions on the
torus" (TeX lines 2822–2830). -/

/-- The solution of `∂̄u₀ = h₀`, `∂̄u_{j+1} = h_{j+1} + ρ ∂u_j`, by the inverse of `∂̄` on
mean-zero functions: `u_j = ∂̄⁻¹ (h_j + ρ ∂u_{j−1})`, the multiplier with symbol `(πi ν)⁻¹`
(`UnitAddTorus.dzbarInvSymbol`). -/
noncomputable def fourByTwo_solve (ρ : ℝ) (h : ℕ → (Fin 2 → ℝ) → ℂ) :
    ℕ → (Fin 2 → ℝ) → ℂ
  | 0 => UnitAddTorus.periodicMultiplier UnitAddTorus.dzbarInvSymbol (h 0)
  | j + 1 => UnitAddTorus.periodicMultiplier UnitAddTorus.dzbarInvSymbol
      (fun x => h (j + 1) x + ρ * UnitAddTorus.dzPi (fourByTwo_solve ρ h j) x)

/-- For smooth periodic mean-zero `h_j`, the `u_j` are smooth, periodic and solve
`∂̄u_j = h_j + ρ ∂u_{j−1}` (`∂u_{−1} = 0`): `h_j + ρ ∂u_{j−1}` is smooth, periodic and mean-zero,
and `∂̄ ∂̄⁻¹ = id` on such functions (`UnitAddTorus.dzbarPi_periodicMultiplier_dzbarInvSymbol`). -/
theorem fourByTwo_solve_spec (ρ : ℝ) {h : ℕ → (Fin 2 → ℝ) → ℂ}
    (hh : ∀ i, ContDiff ℝ ∞ (h i) ∧ UnitAddTorus.IsPeriodic (h i) ∧
      UnitAddTorus.cubeFourierCoeff (h i) 0 = 0) (j : ℕ) :
    ContDiff ℝ ∞ (fourByTwo_solve ρ h j) ∧ UnitAddTorus.IsPeriodic (fourByTwo_solve ρ h j) ∧
      UnitAddTorus.dzbarPi (fourByTwo_solve ρ h j) = fun x => h j x +
        if j = 0 then 0 else ρ * UnitAddTorus.dzPi (fourByTwo_solve ρ h (j - 1)) x := by
  induction j with
  | zero =>
    obtain ⟨h1, h2, h3⟩ := hh 0
    refine ⟨UnitAddTorus.contDiff_periodicMultiplier UnitAddTorus.isPolyBounded_dzbarInvSymbol
      h1 h2, UnitAddTorus.isPeriodic_periodicMultiplier _ _, ?_⟩
    simp only [fourByTwo_solve, ↓reduceIte, add_zero]
    exact UnitAddTorus.dzbarPi_periodicMultiplier_dzbarInvSymbol h1 h2 h3
  | succ j ih =>
    obtain ⟨u1, u2, -⟩ := ih
    obtain ⟨h1, h2, h3⟩ := hh (j + 1)
    have d1 := UnitAddTorus.contDiff_dzPi u1
    have g1 : ContDiff ℝ ∞ fun x => h (j + 1) x +
        ρ * UnitAddTorus.dzPi (fourByTwo_solve ρ h j) x := h1.add (contDiff_const.mul d1)
    have g2 : UnitAddTorus.IsPeriodic fun x => h (j + 1) x +
        ρ * UnitAddTorus.dzPi (fourByTwo_solve ρ h j) x := fun x k => by
      simp only [h2 x k, UnitAddTorus.isPeriodic_dzPi u2 x k]
    have g3 : UnitAddTorus.cubeFourierCoeff (fun x => h (j + 1) x +
        ρ * UnitAddTorus.dzPi (fourByTwo_solve ρ h j) x) 0 = 0 := by
      rw [fourByTwo_cubeFourierCoeff_add h1.continuous (continuous_const.fun_mul d1.continuous),
        UnitAddTorus.cubeFourierCoeff_const_mul, h3,
        UnitAddTorus.cubeFourierCoeff_dzPi_zero (u1.of_le (by exact_mod_cast le_top)) u2]
      simp
    refine ⟨UnitAddTorus.contDiff_periodicMultiplier UnitAddTorus.isPolyBounded_dzbarInvSymbol
      g1 g2, UnitAddTorus.isPeriodic_periodicMultiplier _ _, ?_⟩
    simp only [fourByTwo_solve, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact UnitAddTorus.dzbarPi_periodicMultiplier_dzbarInvSymbol g1 g2 g3

/-- The real test map `φ : ℝ² → ℝ^{2(N+1)}` of `u = (u₀, …, u_N)`: rows `2j` and `2j + 1` are
`Re u_j` and `Im u_j`. -/
noncomputable def fourByTwo_reIm (N : ℕ) (u : ℕ → (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    Fin (2 * (N + 1)) → ℝ :=
  fun r => if r.val % 2 = 0 then (u (r.val / 2) x).re else (u (r.val / 2) x).im

/-- The complex components of the real test map of `u` are the `u_j`. -/
theorem fourByTwo_u_reIm (N : ℕ) (u : ℕ → (Fin 2 → ℝ) → ℂ) (j : Fin (N + 1)) :
    fourByTwo_u (fourByTwo_reIm N u) j = u j.val := by
  funext x
  have e1 : (2 * j.val + 1) % 2 = 1 := by omega
  have e2 : (2 * j.val + 1) / 2 = j.val := by omega
  have e3 : (2 * j.val) % 2 = 0 := by omega
  have e4 : (2 * j.val) / 2 = j.val := by omega
  apply Complex.ext <;> simp [fourByTwo_u, fourByTwo_reIm, rowBlock, e1, e2, e3, e4]

/-- The real test map of smooth `u_j` is smooth. -/
theorem fourByTwo_contDiff_reIm (N : ℕ) {u : ℕ → (Fin 2 → ℝ) → ℂ}
    (hu : ∀ i, ContDiff ℝ ∞ (u i)) : ContDiff ℝ ∞ (fourByTwo_reIm N u) :=
  contDiff_pi.2 fun r => by
    by_cases h : r.val % 2 = 0
    · simp only [fourByTwo_reIm, h, ↓reduceIte]
      exact Complex.reCLM.contDiff.comp (hu _)
    · simp only [fourByTwo_reIm, h, ↓reduceIte]
      exact Complex.imCLM.contDiff.comp (hu _)

/-- The real test map of periodic `u_j` is periodic. -/
theorem fourByTwo_isPeriodic_reIm (N : ℕ) {u : ℕ → (Fin 2 → ℝ) → ℂ}
    (hu : ∀ i, UnitAddTorus.IsPeriodic (u i)) : UnitAddTorus.IsPeriodic (fourByTwo_reIm N u) :=
  fun x k => by
    funext r
    simp only [fourByTwo_reIm, hu _ x k]

/-- The inequality `C^{qc} (p, N, ρ) ≥ ‖(ρ^N 𝓑^{N+1}, …, ρ 𝓑², 𝓑)‖_{L^p_0 (𝕋²; ℓ₂^{N+1}) →
L^p_0 (𝕋²)}` of Proposition 7.2, by the paper's argument (TeX lines 2822–2832): every smooth
mean-zero tuple `(h_j)` is `P_ρ (∇φ)` for the test map `φ` with rows `Re u_j`, `Im u_j`
(`fourByTwo_reIm`), `u` obtained by solving `∂̄u_j = h_j + ρ ∂u_{j−1}` (`fourByTwo_solve`, by the
inverse of `∂̄` on mean-zero functions); `φ` is smooth and periodic, hence Lipschitz, and by the
identity `Q (∇φ) = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j` (`fourByTwo_chainQ_jac`), quasiconvexity at `0`,
tested with periodic maps (Lemma 2.2, `External.Rindler.quasiconvexAtOn_iff_periodic`), gives
`‖Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j‖_p ≤ C ‖(h_j)‖_p`. -/
theorem fourByTwo_chainOpNorm_le_qcThreshold (N : ℕ) (ρ : ℝ) {p : ℝ} (hp : 1 < p) :
    chainOpNorm N p ρ ≤ qcThreshold (chainF N p ρ) := by
  have hp0 : 0 < p := by linarith
  refine le_iInf₂ fun C hC => iSup₂_le fun h hh => ?_
  obtain ⟨hC0, hqc⟩ := hC
  -- Lemma 2.2: quasiconvexity at `0` with periodic test maps
  have hcont := fourByTwo_continuous_chainF N hp0.le ρ C
  have hper : CalculusOfVariations.QuasiconvexAtPeriodic (chainF N p ρ C) 0 :=
    (External.Rindler.quasiconvexAtOn_iff_periodic hcont.measurable
      (fourByTwo_isLocallyBounded hcont) 0).mp
      ((cov_quasiconvexAtOn_unitCube_iff _ _).mpr hqc)
  -- the tuple, extended by `0`, and the solution `u` of `∂̄u_j = h_j + ρ ∂u_{j−1}`
  set h' : ℕ → (Fin 2 → ℝ) → ℂ := fun i => if hi : i < N + 1 then h ⟨i, hi⟩ else 0 with hh'
  have hh'' : ∀ i, ContDiff ℝ ∞ (h' i) ∧ UnitAddTorus.IsPeriodic (h' i) ∧
      UnitAddTorus.cubeFourierCoeff (h' i) 0 = 0 := by
    intro i
    by_cases hi : i < N + 1
    · obtain ⟨a, b, c⟩ := hh ⟨i, hi⟩
      simp only [hh', hi, ↓reduceDIte]
      exact ⟨a, b, by rw [fourByTwo_cubeFourierCoeff_zero]; exact c⟩
    · simp only [hh', hi, ↓reduceDIte]
      exact ⟨contDiff_const, fun _ _ => rfl, by simp [UnitAddTorus.cubeFourierCoeff]⟩
  have hus := fourByTwo_solve_spec ρ hh''
  have hh'j : ∀ j : Fin (N + 1), h' j.val = h j := fun j => by
    simp only [hh', j.isLt, ↓reduceDIte, Fin.eta]
  -- the test map
  set φ := fourByTwo_reIm N (fourByTwo_solve ρ h') with hφ
  have hφs : ContDiff ℝ ∞ φ := fourByTwo_contDiff_reIm N fun i => (hus i).1
  have hφp : UnitAddTorus.IsPeriodic φ := fourByTwo_isPeriodic_reIm N fun i => (hus i).2.1
  obtain ⟨K, hK⟩ := hφp.exists_lipschitzWith (hφs.of_le (by exact_mod_cast le_top))
  have key := hper φ K hK hφp (fourByTwo_integrableOn_comp_jac hcont hK)
  -- `P_ρ (∇φ) = (h₀, …, h_N)` and `Q (∇φ) = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j`
  have hP : ∀ j x, chainP ρ (jac φ x) j = h j x := by
    intro j x
    rw [fourByTwo_chainP_jac ρ (hφs.differentiable (by simp)), fourByTwo_u_reIm,
      fourByTwo_u_reIm, congrFun (hus j).2.2 x, hh'j]
    by_cases hj : j.val = 0 <;> simp [hj]
  set H : (Fin 2 → ℝ) → ℝ := fun x => √(∑ j, ‖h j x‖ ^ 2) with hH
  set T : (Fin 2 → ℝ) → ℂ := fun x => ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
    UnitAddTorus.periodicMultiplier (fun n =>
      HarmonicAnalysis.beurlingSymbol (HarmonicAnalysis.latticePoint n) ^ (N + 1 - j.val))
      (h j) x with hT
  have hpt : ∀ x, chainF N p ρ C (0 + CalculusOfVariations.grad φ x) =
      C ^ p * ‖H x‖ ^ p - ‖T x‖ ^ p := by
    intro x
    rw [zero_add, grad_eq, chainF, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      fourByTwo_chainQ_jac ρ hφs hφp]
    simp only [hP, hT]
  simp only [hpt] at key
  rw [fourByTwo_chainF_zero N hp0, unitCube_eq_cov] at key
  have hcH : Continuous H := Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
    ((hh j).1.continuous.norm.pow 2))
  have hcT : Continuous T := continuous_finsetSum _ fun j _ => continuous_const.mul
    (UnitAddTorus.contDiff_periodicMultiplier (HarmonicAnalysis.isPolyBounded_beurlingSymbol_pow _)
      (hh j).1 (hh j).2.1).continuous
  refine ENNReal.div_le_of_le_mul ?_
  exact (fourByTwo_integral_nonneg_iff hcH hcT hp0 hC0).1 key

/-! ### Proposition 7.2: `C^{qc} ≤ ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖` -/

/-- For a smooth `ℤ²`-periodic `u`, `∫_{(0,1)²} f_{p,ρ,C} (∇u) ≥ 0` with
`C = ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖`: by the identity `Q (∇u) = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j`
(`fourByTwo_chainQ_jac`) and the definition of `chainOpNorm`, applied to the smooth mean-zero
tuple `h = P_ρ (∇u)` (TeX lines 2808–2821). -/
theorem fourByTwo_integral_chainF_nonneg_of_smooth (N : ℕ) (ρ : ℝ) {p : ℝ} (hp : 1 < p)
    (hfin : chainOpNorm N p ρ ≠ ⊤) {φ : (Fin 2 → ℝ) → Fin (2 * (N + 1)) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hper : UnitAddTorus.IsPeriodic φ) :
    0 ≤ ∫ x in unitCube 2, chainF N p ρ (chainOpNorm N p ρ).toReal (jac φ x) := by
  have hp0 : 0 < p := by linarith
  set K := (chainOpNorm N p ρ).toReal with hKdef
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hK : ENNReal.ofReal K = chainOpNorm N p ρ := ENNReal.ofReal_toReal hfin
  have hh : ∀ j, ContDiff ℝ ∞ (fun x => chainP ρ (jac φ x) j) ∧
      UnitAddTorus.IsPeriodic (fun x => chainP ρ (jac φ x) j) ∧
      ∫ x in unitCube 2, chainP ρ (jac φ x) j = 0 := fun j =>
    ⟨fourByTwo_contDiff_chainP ρ hφ j, fourByTwo_isPeriodic_chainP ρ hper j,
      fourByTwo_integral_chainP ρ hφ hper j⟩
  set H : (Fin 2 → ℝ) → ℝ := fun x => √(∑ j, ‖chainP ρ (jac φ x) j‖ ^ 2) with hH
  set T : (Fin 2 → ℝ) → ℂ := fun x => ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
    UnitAddTorus.periodicMultiplier (fun n =>
      HarmonicAnalysis.beurlingSymbol (HarmonicAnalysis.latticePoint n) ^ (N + 1 - j.val))
      (fun y => chainP ρ (jac φ y) j) x with hT
  have hpt : ∀ x, chainF N p ρ K (jac φ x) = K ^ p * ‖H x‖ ^ p - ‖T x‖ ^ p := by
    intro x
    rw [chainF, Real.norm_of_nonneg (Real.sqrt_nonneg _), fourByTwo_chainQ_jac ρ hφ hper]
  simp only [hpt]
  -- the definition of `chainOpNorm`, for the smooth mean-zero tuple `h = P_ρ (∇φ)`
  have hratio : eLpNorm T (ENNReal.ofReal p) (volume.restrict (unitCube 2)) /
      eLpNorm H (ENNReal.ofReal p) (volume.restrict (unitCube 2)) ≤ ENNReal.ofReal K := by
    rw [hK]
    exact le_iSup₂ (f := fun (h : Fin (N + 1) → (Fin 2 → ℝ) → ℂ)
      (_ : ∀ j, ContDiff ℝ ∞ (h j) ∧ UnitAddTorus.IsPeriodic (h j) ∧
        ∫ x in unitCube 2, h j x = 0) =>
      eLpNorm (fun x => ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
        UnitAddTorus.periodicMultiplier (fun n =>
          HarmonicAnalysis.beurlingSymbol (HarmonicAnalysis.latticePoint n) ^ (N + 1 - j.val))
          (h j) x) (ENNReal.ofReal p) (volume.restrict (unitCube 2)) /
      eLpNorm (fun x => √(∑ j, ‖h j x‖ ^ 2)) (ENNReal.ofReal p) (volume.restrict (unitCube 2)))
      (fun j x => chainP ρ (jac φ x) j) hh
  have hcH : Continuous H := Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
    ((hh j).1.continuous.norm.pow 2))
  have hcT : Continuous T := continuous_finsetSum _ fun j _ => continuous_const.mul
    (UnitAddTorus.contDiff_periodicMultiplier (HarmonicAnalysis.isPolyBounded_beurlingSymbol_pow _)
      (hh j).1 (hh j).2.1).continuous
  rw [fourByTwo_integral_nonneg_iff hcH hcT hp0 hK0]
  refine (ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl ?_)).mp hratio
  rw [fourByTwo_eLpNorm_cube hcH hp0]
  exact ENNReal.ofReal_ne_top

open Filter Topology in
/-- The passage from smooth to Lipschitz periodic test maps. Implicit step filled (E28, a gap
fill): the paper proves the identity for smooth `u`, and Lemma 2.2 tests with Lipschitz periodic
maps; a Lipschitz periodic map is reached by mollification (`CalculusOfVariations.mollifyPi`) and
dominated convergence. The mollifications `u_n = ρ_n ⋆ φ` are smooth, periodic and `K`-Lipschitz,
with `∇u_n → ∇φ` almost everywhere, and `G` is bounded on the matrices with entries in `[−K, K]`.
-/
theorem fourByTwo_integral_nonneg_of_smooth {d : ℕ} {G : Matrix (Fin d) (Fin 2) ℝ → ℝ}
    (hG : Continuous G)
    (hsmooth : ∀ u : (Fin 2 → ℝ) → Fin d → ℝ, ContDiff ℝ ∞ u → UnitAddTorus.IsPeriodic u →
      0 ≤ ∫ x in unitCube 2, G (jac u x))
    {φ : (Fin 2 → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (hper : UnitAddTorus.IsPeriodic φ) :
    0 ≤ ∫ x in unitCube 2, G (jac φ x) := by
  -- a bound for `G` on the matrices with entries in `[−K, K]`
  obtain ⟨B, hB⟩ := (isCompact_univ_pi fun _ : Fin d => isCompact_univ_pi fun _ : Fin 2 =>
    isCompact_Icc (a := -(K : ℝ)) (b := K)).exists_bound_of_continuousOn hG.continuousOn
  have hbd : ∀ n x, ‖G (jac (CalculusOfVariations.mollifyPi n φ) x)‖ ≤ B :=
    fun n x => hB _ (Set.mem_univ_pi.mpr fun r => Set.mem_univ_pi.mpr fun k => abs_le.mp
      (abs_jac_le (CalculusOfVariations.mollifyPi_lipschitzWith hφ n) x r k))
  -- `∇ (ρ_n ⋆ φ) → ∇φ` almost everywhere
  have hconv : ∀ᵐ x ∂(volume.restrict (unitCube 2)),
      Tendsto (fun n => G (jac (CalculusOfVariations.mollifyPi n φ) x)) atTop
        (𝓝 (G (jac φ x))) :=
    ae_restrict_of_ae ((CalculusOfVariations.ae_tendsto_grad_mollifyPi hφ).mono
      fun x hx => (hG.tendsto _).comp hx)
  -- dominated convergence
  have hlim := tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (hG.measurable.comp (measurable_jac _)).aestronglyMeasurable)
    (integrableOn_const (by rw [volume_unitCube]; exact ENNReal.one_ne_top))
    (fun n => ae_of_all _ (hbd n)) hconv
  exact ge_of_tendsto' hlim fun n => hsmooth _
    (CalculusOfVariations.mollifyPi_contDiff hφ.continuous n)
    (CalculusOfVariations.mollifyPi_periodic hper n)

/-- The inequality `C^{qc} (p, N, ρ) ≤ ‖(ρ^N 𝓑^{N+1}, …, ρ 𝓑², 𝓑)‖_{L^p_0 (𝕋²; ℓ₂^{N+1}) →
L^p_0 (𝕋²)}` of Proposition 7.2, by the paper's argument (TeX lines 2808–2821): with
`C = ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖`, for every smooth periodic `u`, `h = P_ρ (∇u)` is a smooth mean-zero
tuple and `Q (∇u) = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j` (`fourByTwo_chainQ_jac`), so
`∫ f_{p,ρ,C} (∇u) ≥ 0` (`fourByTwo_integral_chainF_nonneg_of_smooth`); hence `f_{p,ρ,C}` is
quasiconvex at `0` (Lemma 2.2, `External.Rindler.quasiconvexAtOn_iff_periodic`).

Implicit step filled (E28, a gap fill): the paper proves the identity for smooth `u`, and
Lemma 2.2 tests with Lipschitz periodic maps; a Lipschitz periodic map is reached by mollification
(`CalculusOfVariations.mollifyPi`) and dominated convergence
(`fourByTwo_integral_nonneg_of_smooth`). -/
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
    exact fourByTwo_integral_nonneg_of_smooth hcont
      (fun u hu hup => fourByTwo_integral_chainF_nonneg_of_smooth N ρ hp hfin hu hup) hφ hφper
  have hqc : QuasiconvexAt (chainF N p ρ K) 0 :=
    (cov_quasiconvexAtOn_unitCube_iff _ _).mp
      ((External.Rindler.quasiconvexAtOn_iff_periodic hcont.measurable
        (fourByTwo_isLocallyBounded hcont) 0).mpr hper)
  rw [← hK]
  exact iInf₂_le K ⟨ENNReal.toReal_nonneg, hqc⟩

/-- **Proposition 7.2** (`prop:qcbound`): for every `p ∈ (1, ∞)`,
`C^{qc} (p, N, ρ) = ‖(ρ^N 𝓑^{N+1}, …, ρ 𝓑², 𝓑)‖_{L^p_0 (𝕋²; ℓ₂^{N+1}) → L^p_0 (𝕋²)}`, for every
real `ρ`: the paper's setting has `ρ > 0`, which the proof does not use, so it is not assumed.

Proof (the paper's, TeX lines 2807–2832). For a smooth periodic `u`, `h_j = ∂̄u_j − ρ ∂u_{j−1}`
gives `P_ρ (∇u) = (h₀, …, h_N)` and `Q (∇u) = ∂u_N = Σ_j ρ^{N−j} 𝓑^{N+1−j} h_j` (induction from
`𝓑 (∂̄w) = ∂w`, `fourByTwo_chainQ_jac`), so `C^{qc} ≤ ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖`
(`fourByTwo_qcThreshold_le_chainOpNorm`); conversely every smooth mean-zero tuple `(h_j)` is
`P_ρ (∇u)` for the `u` obtained by solving `∂̄u_j = h_j + ρ ∂u_{j−1}`, since `∂̄` is invertible on
mean-zero functions, so `C^{qc} ≥ ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖`
(`fourByTwo_chainOpNorm_le_qcThreshold`). The norm is the supremum over smooth mean-zero tuples
(`chainOpNorm`), as in the paper's proof.

Implicit step filled (E28, a gap fill): the paper proves the identity for smooth `u`, and
Lemma 2.2 tests with Lipschitz periodic maps; a Lipschitz periodic map is reached by mollification
(`CalculusOfVariations.mollifyPi`) and dominated convergence
(`fourByTwo_integral_nonneg_of_smooth`). No `L^p` bound for Fourier multipliers is needed. -/
theorem proposition7_2 (N : ℕ) {ρ : ℝ} {p : ℝ} (hp : 1 < p) :
    qcThreshold (chainF N p ρ) = chainOpNorm N p ρ :=
  le_antisymm (fourByTwo_qcThreshold_le_chainOpNorm N ρ hp)
    (fourByTwo_chainOpNorm_le_qcThreshold N ρ hp)

/-- **Proposition 7.2** (`prop:qcbound`), "in particular":
`C^{qc} (p, N, ρ) ≥ ρ^N ‖𝓑^{N+1}‖_{L^p (ℝ²) → L^p (ℝ²)}`. Unconditional: transference for
homogeneous multipliers (HNVW I, Corollary 5.7.6) is proved (`hnvwTransference_holds`, from
`External/HNVW`).

Proof (the paper's): take `(h₀, …, h_N) = (h, 0, …, 0)` in the identity of Proposition 7.2, whose
inequality `C^{qc} ≥ ‖(ρ^N 𝓑^{N+1}, …, 𝓑)‖` is `fourByTwo_chainOpNorm_le_qcThreshold`, with `h` a
mean-zero trigonometric polynomial (smooth, and `𝓑^{N+1} h = torusBeurlingPow (N + 1) h`,
`HarmonicAnalysis.periodicMultiplier_trigPoly`); this gives `C^{qc} ≥ ρ^N ‖𝓑^{N+1}‖_{L^p_0 (𝕋²)}`
(`torusBeurlingPowNorm`, a supremum over mean-zero trigonometric polynomials), and transference
(`hnvwTransference_holds`) compares the torus norm with the norm on `ℝ²`. -/
theorem proposition7_2_lower (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (ρ ^ N) * beurlingPowNorm (N + 1) p ≤ qcThreshold (chainF N p ρ) := by
  have hp0 : 0 < p := by linarith
  refine le_trans ?_ (fourByTwo_chainOpNorm_le_qcThreshold N ρ hp)
  -- transference: `‖𝓑^{N+1}‖_{L^p (ℝ²)} ≤ ‖𝓑^{N+1}‖_{L^p_0 (𝕋²)}`
  refine (mul_le_mul_right (hnvwTransference_holds (N + 1) p (by omega) hp) _).trans ?_
  -- the tuples `(h, 0, …, 0)`, `h` a mean-zero trigonometric polynomial
  rw [torusBeurlingPowNorm, ENNReal.mul_iSup]
  refine iSup_le fun c => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun hc => ?_
  set g : (Fin 2 → ℝ) → ℂ := fun x => trigPoly c (UnitAddTorus.ofPi x) with hg
  have hge : g = fun x => ∑ n ∈ c.support,
      c n * UnitAddTorus.mFourier n (UnitAddTorus.ofPi x) := by
    funext x
    simp only [hg, trigPoly, Finsupp.sum]
  have hgs : ContDiff ℝ ∞ g := by
    rw [hge]
    simp_rw [UnitAddTorus.mFourier_ofPi]
    exact ContDiff.sum fun n _ => contDiff_const.mul (Complex.contDiff_exp.comp
      (contDiff_const.mul (ContDiff.sum fun i _ => contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (contDiff_pi.1 contDiff_id i)))))
  have hgp : UnitAddTorus.IsPeriodic g := fun x k => by
    simp only [hg, UnitAddTorus.ofPi_add_int]
  have hg0 : ∫ x in unitCube 2, g x = 0 := by
    rw [← fourByTwo_cubeFourierCoeff_zero, hge, UnitAddTorus.cubeFourierCoeff_trig]
    simp [hc]
  set h : Fin (N + 1) → (Fin 2 → ℝ) → ℂ := fun j => if j = 0 then g else 0 with hh
  have hhj : ∀ j, ContDiff ℝ ∞ (h j) ∧ UnitAddTorus.IsPeriodic (h j) ∧
      ∫ x in unitCube 2, h j x = 0 := by
    intro j
    by_cases hj : j = 0
    · simp only [hh, hj, ↓reduceIte]
      exact ⟨hgs, hgp, hg0⟩
    · simp only [hh, hj, ↓reduceIte]
      exact ⟨contDiff_const, fun _ _ => rfl, by simp⟩
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (h : Fin (N + 1) → (Fin 2 → ℝ) → ℂ)
      (_ : ∀ j, ContDiff ℝ ∞ (h j) ∧ UnitAddTorus.IsPeriodic (h j) ∧
        ∫ x in unitCube 2, h j x = 0) =>
      eLpNorm (fun x => ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
        UnitAddTorus.periodicMultiplier (fun n =>
          HarmonicAnalysis.beurlingSymbol (HarmonicAnalysis.latticePoint n) ^ (N + 1 - j.val))
          (h j) x) (ENNReal.ofReal p) (volume.restrict (unitCube 2)) /
      eLpNorm (fun x => √(∑ j, ‖h j x‖ ^ 2)) (ENNReal.ofReal p) (volume.restrict (unitCube 2)))
      h hhj)
  have hB : UnitAddTorus.periodicMultiplier (fun n =>
      HarmonicAnalysis.beurlingSymbol (HarmonicAnalysis.latticePoint n) ^ (N + 1)) g =
      fun x => torusBeurlingPow (N + 1) c (UnitAddTorus.ofPi x) :=
    HarmonicAnalysis.periodicMultiplier_trigPoly (N + 1) c
  have hnum : (fun x => ∑ j : Fin (N + 1), ((ρ ^ (N - j.val) : ℝ) : ℂ) *
      UnitAddTorus.periodicMultiplier (fun n =>
        HarmonicAnalysis.beurlingSymbol (HarmonicAnalysis.latticePoint n) ^ (N + 1 - j.val))
        (h j) x) =
      ((ρ ^ N : ℝ) : ℂ) • fun x => torusBeurlingPow (N + 1) c (UnitAddTorus.ofPi x) := by
    funext x
    rw [Finset.sum_eq_single (0 : Fin (N + 1))]
    · simp [hh, hB]
    · intro j _ hj
      simp [hh, hj, UnitAddTorus.periodicMultiplier, UnitAddTorus.cubeFourierCoeff]
    · simp
  have hden : (fun x => √(∑ j, ‖h j x‖ ^ 2)) = fun x => ‖g x‖ := by
    funext x
    rw [Finset.sum_eq_single (0 : Fin (N + 1))]
    · simp [hh, Real.sqrt_sq (norm_nonneg _)]
    · intro j _ hj
      simp [hh, hj]
    · simp
  rw [hnum, hden, eLpNorm_const_smul, eLpNorm_norm _ (hgs.continuous.aestronglyMeasurable),
    fourByTwo_eLpNorm_torus (fourByTwo_continuous_torusBeurlingPow _ c) hp0,
    fourByTwo_eLpNorm_torus (fourByTwo_continuous_trigPoly c) hp0, ← ofReal_norm,
    Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hρ.le _), mul_div_assoc]

end Proposition72

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

/-- **Theorem 7.1** (`cs-thm7.1`): for `p ∈ (1, 2) ∪ (2, ∞)` there are linear maps
`P_p : ℝ^{4×2} → ℝ^{2×2}`, `Q_p : ℝ^{4×2} → ℝ²` and `C (p) > 0` such that
`A ↦ C (p)^p ‖P_p (A)‖_{S₂}^p − ‖Q_p (A)‖_{ℓ₂}^p` is rank-one convex at `0` but not quasiconvex
at `0`. Unconditional: transference (Proposition 7.2) and Dragičević's lower bound
`‖𝓑²‖_p > p* − 1` are proved (`hnvwTransference_holds`, `dragicevicLowerBound_holds`), and
Burkholder's inequality (Theorem 2.3) enters through Proposition 7.1.

Proof (the paper's): `N = 1`, with `ℝ^{4×2} ≅ Lin (ℂ, ℂ²)` and `ℝ^{2×2} ≅ ℂ²` (row `j` of `P_p (A)`
is `(Re, Im)` of `P_ρ (A)_j`, `Q_p (A) = (Re, Im)` of `Q (A)`, so that the integrand is
`f_{p,ρ,C}`: `fourByTwo_integrand_eq`). Propositions 7.1 and 7.2 give
`C^{rc} (p, 1, ρ) ≤ (p* − 1) √(1 + ρ²)` and `C^{qc} (p, 1, ρ) ≥ ρ ‖𝓑²‖_p`; by Dragičević,
`ρ ‖𝓑²‖_p > (p* − 1) √(1 + ρ²)` for large `ρ` (explicitly `ρ = (p* − 1) / (‖𝓑²‖_p − p* + 1) + 1`,
or `ρ = 1` if `‖𝓑²‖_p = ∞`), and `C` is chosen strictly between. Since `f_{p,ρ,C}` increases with
`C`, `C > C^{rc}` gives rank-one convexity at `0` and `C < C^{qc}` its failure of quasiconvexity. -/
theorem theorem7_1 {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2) :
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
        have h := dragicevicLowerBound_holds p hp hp2
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
    refine lt_of_le_of_lt (proposition7_1 1 hρ hp) ?_
    rw [show ∑ k ∈ Finset.range (1 + 1), ρ ^ (2 * k) = 1 + ρ ^ 2 by
      simp [Finset.sum_range_succ]]
    exact (ENNReal.ofReal_lt_ofReal_iff hC0).mpr hC1
  · -- Proposition 7.2: `C^{qc} (p, 1, ρ) ≥ ρ ‖𝓑²‖_p > C`
    rw [fourByTwo_integrand_eq]
    apply not_quasiconvexAt_of_lt_qcThreshold hC0.le
    refine lt_of_lt_of_le hC2 ?_
    have h72 := proposition7_2_lower 1 hρ hp
    rw [pow_one] at h72
    exact h72

/-! ### Corollary 7.2: homogeneous polynomials -/

section HomPoly

variable {d m : ℕ}

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

/-- `A ↦ |ℓ (A)|²` is a homogeneous quadratic polynomial for a real-linear `ℓ` with complex
values. -/
theorem fourByTwo_isHomPoly_normSq (ℓ : Matrix (Fin d) (Fin m) ℝ →ₗ[ℝ] ℂ) :
    IsHomogeneousPolynomial 2 fun A => ‖ℓ A‖ ^ 2 := by
  have hre := fourByTwo_isHomPoly_linear (Complex.reLm.comp ℓ)
  have him := fourByTwo_isHomPoly_linear (Complex.imLm.comp ℓ)
  refine ((hre.mul hre).add (him.mul him)).congr fun A => ?_
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
    (fourByTwo_isHomPoly_normSq ((√3 : ℝ) • fourByTwo_PLin (N := 1) (√2) j)).congr
      fun A => by simp [Complex.real_smul]; rfl
  have hX : IsHomogeneousPolynomial 2 fun A : Matrix (Fin 4) (Fin 2) ℝ =>
      ∑ j, ‖((√3 : ℝ) : ℂ) * chainP (N := 1) (√2) A j‖ ^ 2 :=
    ((hℓ 0).add (hℓ 1)).congr fun A =>
      (Fin.sum_univ_two fun j => ‖((√3 : ℝ) : ℂ) * chainP (N := 1) (√2) A j‖ ^ 2).symm
  have hY : IsHomogeneousPolynomial 2 fun A : Matrix (Fin 4) (Fin 2) ℝ =>
      ‖chainQ (N := 1) A‖ ^ 2 :=
    fourByTwo_isHomPoly_normSq (fourByTwo_QLin 1)
  refine (((hY.mul hY).const_mul (-2)).add
    (((hX.mul hY).const_mul 20).add ((hX.mul hX).const_mul 30))).congr fun A => ?_
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
four which is rank-one convex but not quasiconvex at `0`. Unconditional: transference
(Proposition 7.2) and Dragičević's bound `‖𝓑²‖_{L⁴} ≥ 21/5` are proved (`hnvwTransference_holds`,
`dragicevicL4Bound_holds`).

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
theorem corollary7_2 :
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
    have h72 := proposition7_2_lower 1 (Real.sqrt_pos.mpr two_pos) (by norm_num : (1 : ℝ) < 4)
    rw [pow_one] at h72
    refine lt_of_lt_of_le ?_ ((mul_le_mul_right dragicevicL4Bound_holds _).trans h72)
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    refine lt_of_pow_lt_pow_left₀ 4 (by positivity) ?_
    rw [hC04, mul_pow, show (√2 : ℝ) ^ 4 = (√2 ^ 2) ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  exact fourByTwo_not_quasiconvexAt_of_le fourByTwo_quartic_continuous hle h0
    (not_quasiconvexAt_of_lt_qcThreshold hC0.le hqc)

end Cassese
