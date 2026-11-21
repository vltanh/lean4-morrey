module

public import Cassese.Toolkit

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
polynomials (`trigPoly`, `torusBeurlingPow` in `Cassese/Defs.lean`).
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
`External/` because it is stated with the shared definitions of `Cassese/Defs.lean`, like
`DragicevicLowerBound`; the source's own formulation could not be consulted. -/
def DragicevicL4Bound : Prop :=
  ENNReal.ofReal (21 / 5) ≤ beurlingPowNorm 2 4

/-- **Proposition 7.1** (`prop:rcbound`): for every `p ∈ (1, ∞)`,
`C^{rc} (p, N, ρ) ≤ (p* − 1) (Σ_{k=0}^N ρ^{2k})^{1/2}`. Conditional on Burkholder's inequality
(Theorem 2.3), through "the results of [Cassese 2025]". -/
theorem proposition7_1 (hB : BurkholderInequality) (N : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) {p : ℝ} (hp : 1 < p) :
    rcThreshold (chainF N p ρ) ≤
      ENNReal.ofReal ((pStar p - 1) * √(∑ k ∈ Finset.range (N + 1), ρ ^ (2 * k))) := by
  sorry

/-- **Proposition 7.2** (`prop:qcbound`): for every `p ∈ (1, ∞)`,
`C^{qc} (p, N, ρ) = ‖(ρ^N 𝓑^{N+1}, …, ρ 𝓑², 𝓑)‖_{L^p_0 (𝕋²; ℓ₂^{N+1}) → L^p_0 (𝕋²)}`. -/
theorem proposition7_2 (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {p : ℝ} (hp : 1 < p) :
    qcThreshold (chainF N p ρ) = chainOpNorm N p ρ := by
  sorry

/-- **Proposition 7.2** (`prop:qcbound`), "in particular":
`C^{qc} (p, N, ρ) ≥ ρ^N ‖𝓑^{N+1}‖_{L^p (ℝ²) → L^p (ℝ²)}`. Conditional on transference for
homogeneous multipliers (HNVW I, Corollary 5.7.6). -/
theorem proposition7_2_lower (hT : HNVWTransference) (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (ρ ^ N) * beurlingPowNorm (N + 1) p ≤ qcThreshold (chainF N p ρ) := by
  sorry

/-- **Theorem 7.1** (`cs-thm7.1`): for `p ∈ (1, 2) ∪ (2, ∞)` there are linear maps
`P_p : ℝ^{4×2} → ℝ^{2×2}`, `Q_p : ℝ^{4×2} → ℝ²` and `C (p) > 0` such that
`A ↦ C (p)^p ‖P_p (A)‖_{S₂}^p − ‖Q_p (A)‖_{ℓ₂}^p` is rank-one convex at `0` but not quasiconvex
at `0`. Conditional on Burkholder's inequality (Proposition 7.1), transference (Proposition 7.2)
and Dragičević's lower bound `‖𝓑²‖_p > p* − 1`. -/
theorem theorem7_1 (hB : BurkholderInequality)
    (hT : HNVWTransference) (hD : DragicevicLowerBound) {p : ℝ}
    (hp : 1 < p) (hp2 : p ≠ 2) :
    ∃ (P : Matrix (Fin 4) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
      (Q : Matrix (Fin 4) (Fin 2) ℝ →ₗ[ℝ] (Fin 2 → ℝ)) (C : ℝ), 0 < C ∧
      RankOneConvexAt
        (fun A => C ^ p * schattenNorm 2 (P A) ^ p - √(∑ i, Q A i ^ 2) ^ p) 0 ∧
      ¬ QuasiconvexAt
        (fun A => C ^ p * schattenNorm 2 (P A) ^ p - √(∑ i, Q A i ^ 2) ^ p) 0 := by
  sorry

/-- **Corollary 7.2** (`cs-cor7.2`): there is a homogeneous polynomial `𝒫 : ℝ^{4×2} → ℝ` of degree
four which is rank-one convex but not quasiconvex at `0`. Conditional on transference
(Proposition 7.2) and Dragičević's bound `‖𝓑²‖_{L⁴} ≥ 21/5`. -/
theorem corollary7_2 (hT : HNVWTransference)
    (hD4 : DragicevicL4Bound) :
    ∃ P : Matrix (Fin 4) (Fin 2) ℝ → ℝ, IsHomogeneousPolynomial 4 P ∧ RankOneConvex P ∧
      ¬ QuasiconvexAt P 0 := by
  sorry

end Cassese
