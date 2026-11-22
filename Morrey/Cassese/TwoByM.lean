module

public import Morrey.Cassese.Toolkit
public import Morrey.Cassese.Bridges
public import Morrey.Common.External.Burkholder.ScalarFunction
public import Morrey.Cassese.Hypotheses
public import Morrey.Cassese.Lifting
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Probability.UniformOn
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Morrey.Common.Basic.Analysis.Calculus.BumpFunction.Mollify

/-!
# Section 4: Morrey's problem in `ℝ^{2×m}`

`ℝ^{2×2n}` is written as `(A₁ | ⋯ | A_n)` with `2 × 2` blocks; block `j` (from `0`) is formed by
the columns `2j` and `2j + 1` (`blockCol`). With both copies of `ℝ²` identified with `ℂ`, each
block acts as `z ↦ α_j z + β_j z̄`, and `P_n (A) = (α_j)_j`, `Q_n (A) = (β_j)_j ∈ ℂ^n` (`wirtP`,
`wirtQ`). `lqNorm q` is the `ℓ_q^n (ℂ)` norm `(Σ |z_j|^q)^{1/q}`, and
`blockF n p q C (A) = C^p ‖P_n A‖_q^p − ‖Q_n A‖_q^p` is the integrand (7), with thresholds
`C^{rc} (p, q, n) = rcThreshold (fun C => blockF n p q C)` and
`C^{qc} (p, q, n) = qcThreshold (fun C => blockF n p q C)`.

`ℓ_q (ℂ)` is `L^q (ℕ, counting measure; ℂ)`, and `umdEllq p q = UMD_{ℂ,p} (ℓ_q)`.

Expectations and `L^p` norms over a rank-one Rademacher martingale are averages over the signs
(`avg`, `lpNormWith`); `L^p` norms over `ℝ^{2n}` are `eLpNorm` for the
Lebesgue measure. `ℝ^{2n} ≅ ℂ^n` by `ξ ↦ (ξ_{2j} + i ξ_{2j+1})_j` (`blockZ`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Matrix ENNReal ComplexConjugate

namespace Cassese

/-- The column `2j + k` of `ℝ^{2×2n}`: column `k` of block `j`. -/
def blockCol {n : ℕ} (j : Fin n) (k : Fin 2) : Fin (2 * n) :=
  ⟨2 * j.val + k.val, by omega⟩

/-- `P_n (A) = (α₁ (A), …, α_n (A))` (Section 4.1). -/
noncomputable def wirtP {n : ℕ} (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) (j : Fin n) : ℂ :=
  wirtAlpha A (blockCol j 0) (blockCol j 1)

/-- `Q_n (A) = (β₁ (A), …, β_n (A))` (Section 4.1). -/
noncomputable def wirtQ {n : ℕ} (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) (j : Fin n) : ℂ :=
  wirtBeta A (blockCol j 0) (blockCol j 1)

/-- The `ℓ_q^n (ℂ)` norm `(Σ_j |z_j|^q)^{1/q}`. -/
noncomputable def lqNorm {n : ℕ} (q : ℝ) (z : Fin n → ℂ) : ℝ :=
  (∑ j, ‖z j‖ ^ q) ^ (1 / q)

/-- The integrand (7): `F_{n,p,q,C} (A) = C^p ‖P_n A‖_{ℓ_q^n}^p − ‖Q_n A‖_{ℓ_q^n}^p`. -/
noncomputable def blockF (n : ℕ) (p q C : ℝ) (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) : ℝ :=
  C ^ p * lqNorm q (wirtP A) ^ p - lqNorm q (wirtQ A) ^ p

/-- `1 ≤ ofReal q` from `1 ≤ q`. -/
theorem one_le_ofReal_of_one_le {q : ℝ} (h : 1 ≤ q) : 1 ≤ ENNReal.ofReal q := by
  rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h

/-- `UMD_{ℂ,p} (ℓ_q)`, with `ℓ_q (ℂ) = L^q (ℕ, counting measure; ℂ)` (`∞` for `q < 1`). -/
noncomputable def umdEllq (p q : ℝ) : ℝ≥0∞ :=
  if h : 1 ≤ q then
    haveI : Fact (1 ≤ ENNReal.ofReal q) := ⟨one_le_ofReal_of_one_le h⟩
    complexUMDConst (Lp ℂ (ENNReal.ofReal q) (Measure.count : Measure ℕ)) p
  else ⊤

/-! ### Lemma 4.1: the rank-one identity -/

theorem twoByM_wirtP_apply {n : ℕ} (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) (j : Fin n) :
    wirtP A j = (((A 0 (blockCol j 0) + A 1 (blockCol j 1)) / 2 : ℝ) : ℂ) +
      (((A 1 (blockCol j 0) - A 0 (blockCol j 1)) / 2 : ℝ) : ℂ) * Complex.I := rfl

theorem twoByM_wirtQ_apply {n : ℕ} (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) (j : Fin n) :
    wirtQ A j = (((A 0 (blockCol j 0) - A 1 (blockCol j 1)) / 2 : ℝ) : ℂ) +
      (((A 1 (blockCol j 0) + A 0 (blockCol j 1)) / 2 : ℝ) : ℂ) * Complex.I := rfl

theorem twoByM_wirtP_add {n : ℕ} (A B : Matrix (Fin 2) (Fin (2 * n)) ℝ) :
    wirtP (A + B) = wirtP A + wirtP B := by
  funext j; simp only [twoByM_wirtP_apply, Matrix.add_apply, Pi.add_apply]; push_cast; ring

theorem twoByM_wirtQ_add {n : ℕ} (A B : Matrix (Fin 2) (Fin (2 * n)) ℝ) :
    wirtQ (A + B) = wirtQ A + wirtQ B := by
  funext j; simp only [twoByM_wirtQ_apply, Matrix.add_apply, Pi.add_apply]; push_cast; ring

theorem twoByM_wirtP_smul {n : ℕ} (t : ℝ) (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) :
    wirtP (t • A) = fun j => (t : ℂ) * wirtP A j := by
  funext j; simp only [twoByM_wirtP_apply, Matrix.smul_apply, smul_eq_mul]; push_cast; ring

theorem twoByM_wirtQ_smul {n : ℕ} (t : ℝ) (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) :
    wirtQ (t • A) = fun j => (t : ℂ) * wirtQ A j := by
  funext j; simp only [twoByM_wirtQ_apply, Matrix.smul_apply, smul_eq_mul]; push_cast; ring

/-- A matrix of rank at most one is `a ⊗ ξ`: its columns are multiples of one vector. -/
theorem twoByM_rank_le_one {m : ℕ} {R : Matrix (Fin 2) (Fin m) ℝ} (hR : R.rank ≤ 1) :
    ∃ (v : Fin 2 → ℝ) (c : Fin m → ℝ), ∀ i k, R i k = c k * v i := by
  rw [Matrix.rank_eq_finrank_span_cols, finrank_le_one_iff] at hR
  obtain ⟨v, hv⟩ := hR
  have : ∀ k, ∃ c : ℝ, c • (v : Fin 2 → ℝ) = R.col k := fun k => by
    obtain ⟨c, hc⟩ := hv ⟨R.col k, Submodule.subset_span ⟨k, rfl⟩⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose c hc using this
  refine ⟨v, c, fun i k => ?_⟩
  have := congrFun (hc k) i
  simp [Matrix.col_apply] at this
  linarith


/-- `s (R) = Σ_j β_j (R) α_j (R)`; for `R = a ⊗ ξ` it is `a² Σ_j |v_j|² / 4`. -/
noncomputable def twoByM_s {n : ℕ} (R : Matrix (Fin 2) (Fin (2 * n)) ℝ) : ℂ :=
  ∑ j, wirtQ R j * wirtP R j

/-- The unimodular scalar of Lemma 4.1: `s / |s|` (`= a / ā` for `R = a ⊗ ξ ≠ 0`), and `1` when
`s = 0`. -/
noncomputable def twoByM_lam {n : ℕ} (R : Matrix (Fin 2) (Fin (2 * n)) ℝ) : ℂ :=
  if twoByM_s R = 0 then 1 else twoByM_s R / (‖twoByM_s R‖ : ℂ)

theorem twoByM_norm_lam {n : ℕ} (R : Matrix (Fin 2) (Fin (2 * n)) ℝ) : ‖twoByM_lam R‖ = 1 := by
  unfold twoByM_lam
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h)]

theorem twoByM_s_smul {n : ℕ} (t : ℝ) (R : Matrix (Fin 2) (Fin (2 * n)) ℝ) :
    twoByM_s (t • R) = (t : ℂ) ^ 2 * twoByM_s R := by
  simp only [twoByM_s, twoByM_wirtP_smul, twoByM_wirtQ_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem twoByM_lam_smul {n : ℕ} {t : ℝ} (ht : t ≠ 0) (R : Matrix (Fin 2) (Fin (2 * n)) ℝ) :
    twoByM_lam (t • R) = twoByM_lam R := by
  have ht2 : (t : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 ht)
  unfold twoByM_lam
  rw [twoByM_s_smul]
  by_cases h : twoByM_s R = 0
  · simp [h]
  · have hst : (t : ℂ) ^ 2 * twoByM_s R ≠ 0 := mul_ne_zero ht2 h
    simp only [hst, h, ite_false]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    push_cast
    exact mul_div_mul_left _ _ ht2

theorem twoByM_measurable_lam (n : ℕ) :
    Measurable (twoByM_lam : Matrix (Fin 2) (Fin (2 * n)) ℝ → ℂ) := by
  have hs : Continuous (twoByM_s : Matrix (Fin 2) (Fin (2 * n)) ℝ → ℂ) := by
    unfold twoByM_s
    refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ ?_
    · simp only [twoByM_wirtQ_apply]; fun_prop
    · simp only [twoByM_wirtP_apply]; fun_prop
  have hg : Measurable fun z : ℂ => if z = 0 then (1 : ℂ) else z / (‖z‖ : ℂ) :=
    Measurable.ite (measurableSet_singleton 0) measurable_const
      (measurable_id.div (Complex.measurable_ofReal.comp measurable_norm))
  exact hg.comp hs.measurable

theorem twoByM_rank_one_identity {n : ℕ} {R : Matrix (Fin 2) (Fin (2 * n)) ℝ} (hR : R.rank ≤ 1)
    (j : Fin n) : wirtQ R j = twoByM_lam R * conj (wirtP R j) := by
  obtain ⟨v, c, hvc⟩ := twoByM_rank_le_one hR
  set a : ℂ := (v 0 : ℂ) + (v 1 : ℂ) * Complex.I
  set w : Fin n → ℂ := fun j => (c (blockCol j 0) : ℂ) + (c (blockCol j 1) : ℂ) * Complex.I
  have hP : ∀ j, wirtP R j = a * conj (w j) / 2 := fun j => by
    simp only [twoByM_wirtP_apply, hvc, a, w]
    apply Complex.ext <;> simp <;> ring
  have hQ : ∀ j, wirtQ R j = a * w j / 2 := fun j => by
    simp only [twoByM_wirtQ_apply, hvc, a, w]
    apply Complex.ext <;> simp <;> ring
  set S : ℝ := ∑ j, Complex.normSq (w j)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hs : twoByM_s R = a ^ 2 * (S : ℂ) / 4 := by
    simp only [twoByM_s, hP, hQ, S]
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.mul_conj]
    ring
  unfold twoByM_lam
  split_ifs with h
  · -- `s = 0`: then `a = 0` or every `w_j = 0`, and both sides vanish
    rw [hs] at h
    have : a = 0 ∨ S = 0 := by
      rcases mul_eq_zero.1 (div_eq_zero_iff.1 h |>.resolve_right (by norm_num)) with h | h
      · exact Or.inl (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h)
      · exact Or.inr (Complex.ofReal_eq_zero.1 h)
    rcases this with ha | hS
    · simp [hP, hQ, ha]
    · have : w j = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (w j))).1 hS j
          (Finset.mem_univ _)
        exact Complex.normSq_eq_zero.1 this
      simp [hP, hQ, this]
  · have hn : (‖twoByM_s R‖ : ℂ) = (Complex.normSq a : ℂ) * (S : ℂ) / 4 := by
      rw [hs, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0,
        Complex.sq_norm]
      push_cast
      simp
    have hn0 : (‖twoByM_s R‖ : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero, norm_eq_zero]; exact h
    rw [div_mul_eq_mul_div, eq_div_iff hn0, hn, hQ, hP, hs, map_div₀, map_mul, Complex.conj_conj,
      map_ofNat, ← Complex.mul_conj]
    ring


/-- **Lemma 4.1** (`lem:rankonecomplex`, rank-one identity): there is a measurable `λ` such that
for every `R ∈ ℝ^{2×2n}` of rank at most one, `|λ (R)| = 1`, `Q_n R = λ (R) conj (P_n R)`
componentwise (8), and `λ (t R) = λ (R)` for every real `t ≠ 0`.

Proof: the paper's computation. `R = a ⊗ ξ` (`twoByM_rank_le_one`), and with
`v_j = ξ_{2j} + i ξ_{2j+1}`, `α_j (R) = a v̄_j / 2`, `β_j (R) = a v_j / 2`. The paper's
`λ (R) = a / ā` is written as a function of
`R`: `λ (R) = s / |s|` with `s = Σ_j β_j α_j = a² Σ_j |v_j|² / 4` (and `λ = 1` when `s = 0`, which
for rank at most one means `R = 0`); this formula is independent of the factorisation, unimodular,
invariant under `R ↦ t R` (`s (t R) = t² s (R)`), and measurable (`twoByM_lam`). -/
theorem lemma4_1 (n : ℕ) :
    ∃ lam : Matrix (Fin 2) (Fin (2 * n)) ℝ → ℂ, Measurable lam ∧
      ∀ R : Matrix (Fin 2) (Fin (2 * n)) ℝ, R.rank ≤ 1 →
        ‖lam R‖ = 1 ∧ (∀ j, wirtQ R j = lam R * conj (wirtP R j)) ∧
          ∀ t : ℝ, t ≠ 0 → lam (t • R) = lam R :=
  ⟨twoByM_lam, twoByM_measurable_lam n, fun R hR =>
    ⟨twoByM_norm_lam R, twoByM_rank_one_identity hR, fun _ ht => twoByM_lam_smul ht R⟩⟩

/-! ### Proposition 4.1: the uniform laminate bound -/

noncomputable def twoByM_ext {n : ℕ} (z : Fin n → ℂ) (k : ℕ) : ℂ :=
  if h : k < n then z ⟨k, h⟩ else 0

theorem twoByM_eLpNorm_ext {n : ℕ} {q : ℝ} (hq : 0 < q) (z : Fin n → ℂ) :
    eLpNorm (twoByM_ext z) (ENNReal.ofReal q) (Measure.count : Measure ℕ) =
      ENNReal.ofReal (lqNorm q z) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top
    (StronglyMeasurable.of_discrete).aestronglyMeasurable, lintegral_count,
    ENNReal.toReal_ofReal hq.le]
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
    simp [twoByM_ext, Finset.mem_range.not.1 hk, ENNReal.zero_rpow_of_pos hq])]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ‖twoByM_ext z k‖ₑ ^ q)]
  simp only [twoByM_ext, Fin.is_lt, dite_true, Fin.eta]
  unfold lqNorm
  rw [← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le]

theorem twoByM_memLp_ext {n : ℕ} {q : ℝ} (hq : 0 < q) (z : Fin n → ℂ) :
    MemLp (twoByM_ext z) (ENNReal.ofReal q) (Measure.count : Measure ℕ) :=
  by rw [memLp_iff, twoByM_eLpNorm_ext hq]; exact ENNReal.ofReal_lt_top

/-- The isometric embedding `ℓ_q^n ↪ ℓ_q = L^q (ℕ, count)`. -/
noncomputable def twoByM_emb {n : ℕ} (q : ℝ) (hq : 0 < q) (z : Fin n → ℂ) :
    Lp ℂ (ENNReal.ofReal q) (Measure.count : Measure ℕ) :=
  (twoByM_memLp_ext hq z).toLp _

theorem twoByM_norm_emb {n : ℕ} {q : ℝ} (hq : 0 < q) [Fact (1 ≤ ENNReal.ofReal q)]
    (z : Fin n → ℂ) : ‖twoByM_emb q hq z‖ = lqNorm q z := by
  rw [twoByM_emb, Lp.norm_toLp, twoByM_eLpNorm_ext hq, ENNReal.toReal_ofReal]
  unfold lqNorm; exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _

theorem twoByM_emb_add {n : ℕ} {q : ℝ} (hq : 0 < q) (z w : Fin n → ℂ) :
    twoByM_emb q hq (z + w) = twoByM_emb q hq z + twoByM_emb q hq w := by
  unfold twoByM_emb
  rw [← MemLp.toLp_add]
  congr 1
  funext k; simp only [twoByM_ext, Pi.add_apply]; split_ifs <;> simp

theorem twoByM_emb_smul {n : ℕ} {q : ℝ} (hq : 0 < q) [Fact (1 ≤ ENNReal.ofReal q)] (c : ℂ)
    (z : Fin n → ℂ) : twoByM_emb q hq (c • z) = c • twoByM_emb q hq z := by
  unfold twoByM_emb
  rw [← MemLp.toLp_const_smul]
  congr 1
  funext k; simp only [twoByM_ext, Pi.smul_apply]; split_ifs <;> simp

theorem twoByM_emb_sum {n : ℕ} {q : ℝ} (hq : 0 < q) {ι : Type*} (s : Finset ι)
    (z : ι → Fin n → ℂ) : twoByM_emb q hq (∑ i ∈ s, z i) = ∑ i ∈ s, twoByM_emb q hq (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := twoByM_emb_add hq (0 : Fin n → ℂ) 0
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, twoByM_emb_add, ih]


/-! ### The Rademacher martingale on the canonical space -/

section Signs

variable {N : ℕ}

/-- The uniform probability on the signs `Fin N → Bool`. -/
noncomputable abbrev twoByM_μ (N : ℕ) : Measure (Fin N → Bool) :=
  ProbabilityTheory.uniformOn Set.univ

theorem twoByM_μ_singleton (ε : Fin N → Bool) : twoByM_μ N {ε} = ((2 : ℝ≥0∞) ^ N)⁻¹ := by
  rw [ProbabilityTheory.uniformOn_univ, Measure.count_singleton, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  simp

theorem twoByM_μ_real_singleton (ε : Fin N → Bool) : (twoByM_μ N).real {ε} = ((2 : ℝ) ^ N)⁻¹ := by
  rw [measureReal_def, twoByM_μ_singleton]; simp

/-- `L^p` norms on the signs are the averages `lpNormWith`. -/
theorem twoByM_eLpNorm_eq {p : ℝ} (hp : 0 < p) (f : (Fin N → Bool) → ℝ) (hf : ∀ ε, 0 ≤ f ε) :
    eLpNorm f (ENNReal.ofReal p) (twoByM_μ N) =
      ENNReal.ofReal (avg (fun ε => f ε ^ p) ^ (1 / p)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    StronglyMeasurable.of_discrete.aestronglyMeasurable, lintegral_fintype,
    ENNReal.toReal_ofReal hp.le, avg,
    ← ENNReal.ofReal_rpow_of_nonneg (div_nonneg (Finset.sum_nonneg fun ε _ =>
      Real.rpow_nonneg (hf ε) _) (by positivity)) (by positivity)]
  congr 1
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (hf ε) _),
    ENNReal.ofReal_sum_of_nonneg (fun ε _ => Real.rpow_nonneg (hf ε) _), Finset.sum_mul]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [twoByM_μ_singleton, Real.enorm_eq_ofReal (hf ε),
    ENNReal.ofReal_rpow_of_nonneg (hf ε) hp.le, ENNReal.ofReal_inv_of_pos (by positivity)]
  simp

/-- A function of the signs `ε_j`, `j < k`, is `ℱ_k`-strongly measurable. -/
theorem twoByM_stronglyMeasurable {E : Type*} [TopologicalSpace E] {k : ℕ}
    (f : (Fin N → Bool) → E)
    (hf : ∀ ε ε' : Fin N → Bool, (∀ j : Fin N, j.val < k → ε j = ε' j) → f ε = f ε') :
    StronglyMeasurable[rad_filtration N k] f := by
  have h : f = f ∘ rad_trunc k :=
    funext fun ε => hf _ _ fun j hj => by simp [rad_trunc, hj]
  rw [h]
  exact StronglyMeasurable.of_discrete.comp_measurable (comap_measurable _)

/-- Sets of `ℱ_k` are determined by the signs `ε_j`, `j < k`. -/
theorem twoByM_measurableSet {k : ℕ} {s : Set (Fin N → Bool)}
    (hs : MeasurableSet[rad_filtration N k] s)
    {ε ε' : Fin N → Bool} (h : ∀ j : Fin N, j.val < k → ε j = ε' j) : ε ∈ s ↔ ε' ∈ s := by
  obtain ⟨t, -, rfl⟩ := hs
  have : rad_trunc k ε = rad_trunc k ε' := funext fun j => by
    simp only [rad_trunc]; split_ifs with hj
    · exact h j hj
    · rfl
  simp only [Set.mem_preimage, this]

/-- The sum over the signs of `coin (ε_i) • V (ε)`, with `V` independent of `ε_i`, vanishes, and
so does its restriction to a set independent of `ε_i`. -/
theorem twoByM_sum_coin_smul_eq_zero {E : Type*} [AddCommGroup E] [Module ℝ E] (i : Fin N)
    (g : (Fin N → Bool) → E) (hg : ∀ ε, g (rad_flip i ε) = -g ε) : ∑ ε, g ε = 0 := by
  have h := Equiv.sum_comp (Function.Involutive.toPerm _ (rad_flip_involutive i)) g
  simp only [Function.Involutive.coe_toPerm, hg, Finset.sum_neg_distrib] at h
  have h2 : (2 : ℝ) • ∑ ε, g ε = 0 := by rw [two_smul]; nth_rw 1 [← h]; simp
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

end Signs


theorem twoByM_wirtP_zero {n : ℕ} : wirtP (0 : Matrix (Fin 2) (Fin (2 * n)) ℝ) = 0 := by
  funext j; simp [twoByM_wirtP_apply]

theorem twoByM_wirtQ_zero {n : ℕ} : wirtQ (0 : Matrix (Fin 2) (Fin (2 * n)) ℝ) = 0 := by
  funext j; simp [twoByM_wirtQ_apply]

theorem twoByM_wirtP_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin 2) (Fin (2 * n)) ℝ) : wirtP (∑ i ∈ s, A i) = ∑ i ∈ s, wirtP (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [twoByM_wirtP_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, twoByM_wirtP_add, ih]

theorem twoByM_wirtQ_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin 2) (Fin (2 * n)) ℝ) : wirtQ (∑ i ∈ s, A i) = ∑ i ∈ s, wirtQ (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [twoByM_wirtQ_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, twoByM_wirtQ_add, ih]

theorem twoByM_emb_zero {n : ℕ} {q : ℝ} (hq : 0 < q) :
    twoByM_emb q hq (0 : Fin n → ℂ) = 0 := by
  have := twoByM_emb_add hq (0 : Fin n → ℂ) 0
  simpa using this

theorem twoByM_emb_sub {n : ℕ} {q : ℝ} (hq : 0 < q) (z w : Fin n → ℂ) :
    twoByM_emb q hq z - twoByM_emb q hq w = twoByM_emb q hq (z - w) := by
  rw [sub_eq_iff_eq_add, ← twoByM_emb_add, sub_add_cancel]

/-- The increment `M_{k+1} − M_k = ε_k ξ_k`. -/
theorem twoByM_mart_succ_sub {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ξ : Fin N → (Fin N → Bool) → E) (k : ℕ) (ε : Fin N → Bool) :
    mart ξ (k + 1) ε - mart ξ k ε =
      if h : k < N then coin (ε ⟨k, h⟩) • ξ ⟨k, h⟩ ε else 0 := by
  unfold mart
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  have : ∀ k' : Fin N, ((if k'.val < k + 1 then coin (ε k') • ξ k' ε else 0) -
      if k'.val < k then coin (ε k') • ξ k' ε else 0) =
      if k'.val = k then coin (ε k') • ξ k' ε else 0 := fun k' => by
    split_ifs <;> first | omega | simp
  simp only [this]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩ (fun b _ hb => by
      rw [ite_eq_right]; exact fun hb' => hb (Fin.ext hb')) (by simp)]
    simp
  · exact Finset.sum_eq_zero fun k' _ => by rw [ite_eq_right]; omega

theorem twoByM_lqNorm_conj {n : ℕ} (q : ℝ) (z : Fin n → ℂ) :
    lqNorm q (fun j => conj (z j)) = lqNorm q z := by
  simp [lqNorm]

theorem twoByM_lqNorm_nonneg {n : ℕ} (q : ℝ) (z : Fin n → ℂ) : 0 ≤ lqNorm q z :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => by positivity) _

/-- **Proposition 4.1** (`prop:laminate`, uniform laminate bound), inequality (9): for every
rank-one Rademacher martingale `(M_k)_{k ≤ N}` in `ℝ^{2×2n}` (any start `M₀`) and
`p, q ∈ (1, ∞)`,
`‖Q_n (M_N) − Q_n (M₀)‖_{L^p (ℓ_q^n)} ≤ UMD_{ℂ,p} (ℓ_q) ‖P_n (M_N) − P_n (M₀)‖_{L^p (ℓ_q^n)}`.
(The section's standing assumption `q > p + 2` is not used and not assumed.)

Proof: the paper's. With the increments `dM_k = ε_k A_k`, Lemma 4.1 gives the predictable unimodular
`λ_k = λ (A_k)` with `Q_n (dM_k) = λ_k conj (P_n (dM_k))`; the martingale `conj (P_n (M_k − M₀))`,
mapped into `ℓ_q` by the isometric embedding `ℓ_q^n ↪ ℓ_q` (`twoByM_emb`), is a martingale for the
natural filtration of the signs on the canonical space (`rad_filtration`, uniform measure), and (5),
the definition of `UMD_{ℂ,p} (ℓ_q)`, applied to it with the multipliers `λ_k` gives (9). -/
theorem proposition4_1 {p q : ℝ} (hp : 1 < p) (hq : 1 < q) {n N : ℕ}
    (M₀ : Matrix (Fin 2) (Fin (2 * n)) ℝ)
    (A : Fin N → (Fin N → Bool) → Matrix (Fin 2) (Fin (2 * n)) ℝ) (hA : IsRankOneIncrements A) :
    ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtQ (radMart M₀ A N ε) - wirtQ M₀) ≤
      umdEllq p q *
        ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtP (radMart M₀ A N ε) - wirtP M₀) := by
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  rw [umdEllq, dite_eq_left hq.le]
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨one_le_ofReal_of_one_le hq.le⟩
  -- the unimodular `λ` of Lemma 4.1
  obtain ⟨lam, -, hlam⟩ := lemma4_1 n
  set μ := twoByM_μ N
  set ℱ := rad_filtration N
  -- the martingale `conj (P_n (M_k − M_0))`, in `ℓ_q`
  set Y : ℕ → (Fin N → Bool) → Lp ℂ (ENNReal.ofReal q) (Measure.count : Measure ℕ) :=
    fun k ε => twoByM_emb q hq0 fun j => conj (wirtP (mart A k ε) j) with hY
  -- the predictable unimodular multipliers `λ_k = λ (A_k)` of Lemma 4.1
  set c : ℕ → (Fin N → Bool) → ℂ :=
    fun k ε => if h : k - 1 < N then lam (A ⟨k - 1, h⟩ ε) else 1 with hc
  have hcsucc : ∀ k ε, c (k + 1) ε = if h : k < N then lam (A ⟨k, h⟩ ε) else 1 := by
    intro k ε; simp [hc]
  have hradP : ∀ ε, wirtP (radMart M₀ A N ε) - wirtP M₀ = wirtP (mart A N ε) := fun ε => by
    rw [radMart, twoByM_wirtP_add, add_sub_cancel_left]
  have hradQ : ∀ ε, wirtQ (radMart M₀ A N ε) - wirtQ M₀ = wirtQ (mart A N ε) := fun ε => by
    rw [radMart, twoByM_wirtQ_add, add_sub_cancel_left]
  -- the increments `Y_{k+1} − Y_k = ε_k conj (P_n (A_k))`
  have hinc : ∀ (k : ℕ) (hk : k < N) (ε : Fin N → Bool), Y (k + 1) ε - Y k ε =
      (coin (ε ⟨k, hk⟩) : ℂ) • twoByM_emb q hq0 (fun j => conj (wirtP (A ⟨k, hk⟩ ε) j)) := by
    intro k hk ε
    have hm : mart A (k + 1) ε = mart A k ε + coin (ε ⟨k, hk⟩) • A ⟨k, hk⟩ ε := by
      have := twoByM_mart_succ_sub A k ε
      rw [dite_eq_left hk] at this
      rw [← this, add_sub_cancel]
    simp only [hY]
    rw [twoByM_emb_sub, ← twoByM_emb_smul]
    congr 1
    funext j
    simp only [hm, twoByM_wirtP_add, twoByM_wirtP_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, map_add, map_mul, Complex.conj_ofReal]
    ring
  have hinc' : ∀ (k : ℕ), N ≤ k → ∀ ε, Y (k + 1) ε = Y k ε := by
    intro k hk ε
    have := twoByM_mart_succ_sub A k ε
    rw [dite_eq_right (by omega), sub_eq_zero] at this
    simp only [hY, this]
  -- `Y` is a martingale for the natural filtration
  have hmart : Martingale Y ℱ μ := by
    refine martingale_of_setIntegral_eq_succ (fun k => ?_) (fun k => Integrable.of_finite)
      (fun i s hs => ?_)
    · exact twoByM_stronglyMeasurable _ fun ε ε' h => by
        simp only [hY]; rw [rad_mart_congr hA.1 k h]
    · have hs' : MeasurableSet s := ℱ.le i s hs
      rw [← integral_indicator hs', ← integral_indicator hs', integral_fintype Integrable.of_finite,
        integral_fintype Integrable.of_finite]
      simp only [μ, twoByM_μ_real_singleton]
      rw [← Finset.smul_sum, ← Finset.smul_sum]
      congr 1
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
      by_cases hi : i < N
      · refine twoByM_sum_coin_smul_eq_zero ⟨i, hi⟩ _ fun ε => ?_
        have hmem : rad_flip ⟨i, hi⟩ ε ∈ s ↔ ε ∈ s :=
          twoByM_measurableSet hs fun j hj =>
            rad_flip_apply_ne (fun h => by rw [h] at hj; exact lt_irrefl _ hj) ε
        have hD : twoByM_emb q hq0 (fun j => conj (wirtP (A ⟨i, hi⟩ (rad_flip ⟨i, hi⟩ ε)) j)) =
            twoByM_emb q hq0 (fun j => conj (wirtP (A ⟨i, hi⟩ ε) j)) := by
          rw [hA.1 ⟨i, hi⟩ (rad_flip ⟨i, hi⟩ ε) ε fun j hj =>
            rad_flip_apply_ne (ne_of_lt hj) ε]
        have hcoin : coin (rad_flip ⟨i, hi⟩ ε ⟨i, hi⟩) = -coin (ε ⟨i, hi⟩) := by
          simp only [rad_flip, Function.update_self]
          cases ε ⟨i, hi⟩ <;> simp [coin]
        have key : ∀ ε', s.indicator (Y i) ε' - s.indicator (Y (i + 1)) ε' =
            -s.indicator (fun ε'' => (coin (ε'' ⟨i, hi⟩) : ℂ) •
              twoByM_emb q hq0 (fun j => conj (wirtP (A ⟨i, hi⟩ ε'') j))) ε' := by
          intro ε'
          by_cases h : ε' ∈ s
          · simp only [Set.indicator_of_mem h, ← hinc i hi ε']; abel
          · simp [Set.indicator_of_notMem h]
        rw [key, key, neg_inj]
        by_cases h : ε ∈ s
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.2 h), hD, hcoin]
          push_cast; rw [neg_smul]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hmem.1 h), neg_zero]
      · have : Y (i + 1) = Y i := funext (hinc' i (by omega))
        exact Finset.sum_eq_zero fun ε _ => by rw [this, sub_self]
  have hY0 : ∀ ε, Y 0 ε = 0 := fun ε => by
    simp only [hY, rad_mart_zero, twoByM_wirtP_zero, Pi.zero_apply, map_zero]
    exact twoByM_emb_zero hq0
  have hc1 : ∀ k ε, ‖c k ε‖ = 1 := fun k ε => by
    simp only [hc]; split_ifs
    · exact (hlam _ (hA.2 _ _)).1
    · simp
  have hcm : ∀ k, StronglyMeasurable[ℱ k] (c (k + 1)) := fun k => by
    refine twoByM_stronglyMeasurable _ fun ε ε' h => ?_
    simp only [hcsucc]
    split_ifs with hk
    · rw [hA.1 ⟨k, hk⟩ ε ε' fun j hj => h j hj]
    · rfl
  -- the transform `Σ λ_k dY_k = Q_n (M_N) − Q_n (M_0)`
  have htrans : ∀ ε, ∑ k ∈ Finset.range N, c (k + 1) ε • (Y (k + 1) ε - Y k ε) =
      twoByM_emb q hq0 (wirtQ (radMart M₀ A N ε) - wirtQ M₀) := by
    intro ε
    rw [hradQ, rad_mart_top, twoByM_wirtQ_sum, twoByM_emb_sum,
      ← Fin.sum_univ_eq_sum_range (fun k => c (k + 1) ε • (Y (k + 1) ε - Y k ε))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcsucc, dite_eq_left k.isLt, hinc k k.isLt]
    simp only [Fin.eta]
    rw [smul_smul, ← twoByM_emb_smul]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, twoByM_wirtQ_smul, (hlam _ (hA.2 k ε)).2.1 j]
    ring
  -- the two `L^p (ℓ_q)` norms
  have hnormY : eLpNorm (Y N) (ENNReal.ofReal p) μ =
      ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtP (radMart M₀ A N ε) - wirtP M₀) := by
    rw [← eLpNorm_norm _ StronglyMeasurable.of_discrete.aestronglyMeasurable, lpNormWith,
      ← twoByM_eLpNorm_eq hp0 _ fun ε => twoByM_lqNorm_nonneg q _]
    congr 1
    funext ε
    rw [hradP, twoByM_norm_emb hq0, twoByM_lqNorm_conj]
  have hnormT : eLpNorm (fun ε => ∑ k ∈ Finset.range N, c (k + 1) ε • (Y (k + 1) ε - Y k ε))
      (ENNReal.ofReal p) μ =
      ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtQ (radMart M₀ A N ε) - wirtQ M₀) := by
    rw [← eLpNorm_norm _ StronglyMeasurable.of_discrete.aestronglyMeasurable, lpNormWith,
      ← twoByM_eLpNorm_eq hp0 _ fun ε => twoByM_lqNorm_nonneg q _]
    congr 1
    funext ε
    rw [htrans, twoByM_norm_emb hq0]
  -- every complex `UMD_p` constant of `ℓ_q` bounds the ratio
  have hbound : ∀ β ∈ {β | IsComplexUMDBound (Lp ℂ (ENNReal.ofReal q)
      (Measure.count : Measure ℕ)) p β},
      ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtQ (radMart M₀ A N ε) - wirtQ M₀) ≤
        β * ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtP (radMart M₀ A N ε) -
          wirtP M₀) := by
    intro β hβ
    have := hβ (Fin N → Bool) inferInstance μ ℱ Y c hmart hY0 hc1 hcm N
    rwa [hnormT, hnormY] at this
  -- if `P_n (M_N) = P_n (M_0)` then the martingale vanishes, and so does its transform
  have hzero : ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtP (radMart M₀ A N ε) -
      wirtP M₀) = 0 →
      ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtQ (radMart M₀ A N ε) - wirtQ M₀) =
        0 := by
    intro h0
    rw [← hnormY, eLpNorm_eq_zero_iff hpne] at h0
    have hk : ∀ k ≤ N, Y k =ᵐ[μ] 0 := fun k hk =>
      (hmart.2 k N hk).symm.trans ((condExp_congr_ae h0).trans (by rw [condExp_zero]))
    rw [← hnormT, eLpNorm_eq_zero_iff hpne]
    have hall : ∀ᵐ ε ∂μ, ∀ k : Fin (N + 1), Y k ε = 0 :=
      ae_all_iff.2 fun k => hk k (Nat.lt_succ_iff.1 k.isLt)
    filter_upwards [hall] with ε hε
    refine Finset.sum_eq_zero fun k hk' => ?_
    have hk1 := hε ⟨k + 1, by simpa using hk'⟩
    have hk0 := hε ⟨k, by simp at hk'; omega⟩
    simp only at hk1 hk0
    rw [hk1, hk0, sub_self, smul_zero]
  by_cases hR : ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtP (radMart M₀ A N ε) -
      wirtP M₀) = 0
  · rw [hzero hR]; exact zero_le
  · calc _ = ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtQ (radMart M₀ A N ε) -
          wirtQ M₀) / ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtP (radMart M₀ A N ε) -
          wirtP M₀) * ENNReal.ofReal (lpNormWith (lqNorm q) p fun ε => wirtP (radMart M₀ A N ε) -
          wirtP M₀) := (ENNReal.div_mul_cancel hR ENNReal.ofReal_ne_top).symm
      _ ≤ _ := by
        gcongr
        exact le_sInf fun β hβ => ENNReal.div_le_of_le_mul (hbound β hβ)

theorem twoByM_lqNorm_zero {n : ℕ} {q : ℝ} (hq : 0 < q) : lqNorm q (0 : Fin n → ℂ) = 0 := by
  simp [lqNorm, Real.zero_rpow hq.ne', Real.zero_rpow (inv_pos.2 hq).ne']

theorem twoByM_continuous_lqNorm {n : ℕ} {q : ℝ} (hq : 0 < q) :
    Continuous (lqNorm q : (Fin n → ℂ) → ℝ) := by
  unfold lqNorm
  refine Continuous.rpow_const ?_ fun _ => Or.inr (by positivity)
  exact continuous_finsetSum _ fun j _ =>
    (continuous_norm.comp (continuous_apply j)).rpow_const fun _ => Or.inr hq.le

theorem twoByM_continuous_wirtP (n : ℕ) :
    Continuous (wirtP : Matrix (Fin 2) (Fin (2 * n)) ℝ → Fin n → ℂ) :=
  continuous_pi fun j => by simp only [twoByM_wirtP_apply]; fun_prop

theorem twoByM_continuous_wirtQ (n : ℕ) :
    Continuous (wirtQ : Matrix (Fin 2) (Fin (2 * n)) ℝ → Fin n → ℂ) :=
  continuous_pi fun j => by simp only [twoByM_wirtQ_apply]; fun_prop

theorem twoByM_continuous_blockF (n : ℕ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (C : ℝ) :
    Continuous (blockF n p q C) := by
  unfold blockF
  refine (continuous_const.mul ?_).sub ?_
  · exact ((twoByM_continuous_lqNorm hq).comp (twoByM_continuous_wirtP n)).rpow_const
      fun _ => Or.inr hp.le
  · exact ((twoByM_continuous_lqNorm hq).comp (twoByM_continuous_wirtQ n)).rpow_const
      fun _ => Or.inr hp.le

theorem twoByM_blockF_zero (n : ℕ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (C : ℝ) :
    blockF n p q C 0 = 0 := by
  simp [blockF, twoByM_wirtP_zero, twoByM_wirtQ_zero, twoByM_lqNorm_zero hq, Real.zero_rpow hp.ne']


/-- **Proposition 4.1** (`prop:laminate`), final assertion: if `M₀ = 0` and
`C > UMD_{ℂ,p} (ℓ_q)`, then `E F_{n,p,q,C} (M_N) ≥ 0`. -/
theorem proposition4_1_nonneg {p q : ℝ} (hp : 1 < p) (hq : 1 < q) {n N : ℕ}
    (A : Fin N → (Fin N → Bool) → Matrix (Fin 2) (Fin (2 * n)) ℝ) (hA : IsRankOneIncrements A)
    {C : ℝ} (hC : umdEllq p q < ENNReal.ofReal C) :
    0 ≤ avg fun ε => blockF n p q C (radMart 0 A N ε) := by
  have hp0 : 0 < p := by linarith
  have h := proposition4_1 hp hq 0 A hA
  simp only [twoByM_wirtP_zero, twoByM_wirtQ_zero, sub_zero] at h
  have hC0 : 0 < C := by
    by_contra h'
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 h')] at hC
    exact (ENNReal.not_lt_zero hC).elim
  set a := lpNormWith (lqNorm q) p fun ε => wirtP (radMart 0 A N ε) with ha
  set b := lpNormWith (lqNorm q) p fun ε => wirtQ (radMart 0 A N ε) with hb
  have ha0 : 0 ≤ a := Real.rpow_nonneg (rad_avg_nonneg fun ε =>
    Real.rpow_nonneg (twoByM_lqNorm_nonneg q _) _) _
  have hb0 : 0 ≤ b := Real.rpow_nonneg (rad_avg_nonneg fun ε =>
    Real.rpow_nonneg (twoByM_lqNorm_nonneg q _) _) _
  -- `‖Q_n (M_N)‖_{L^p} ≤ C ‖P_n (M_N)‖_{L^p}`
  have hba : b ≤ C * a := by
    have : ENNReal.ofReal b ≤ ENNReal.ofReal (C * a) := by
      rw [ENNReal.ofReal_mul hC0.le]
      exact h.trans (mul_le_mul_left hC.le _)
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0.le ha0)).1 this
  -- raise to the `p`-th power
  have hpow : ∀ (z : (Fin N → Bool) → Fin n → ℂ),
      (lpNormWith (lqNorm q) p z) ^ p = avg fun ε => lqNorm q (z ε) ^ p := fun z => by
    rw [lpNormWith, ← Real.rpow_mul (rad_avg_nonneg fun ε =>
      Real.rpow_nonneg (twoByM_lqNorm_nonneg q _) _), one_div_mul_cancel hp0.ne', Real.rpow_one]
  have : (avg fun ε => blockF n p q C (radMart 0 A N ε)) = C ^ p * a ^ p - b ^ p := by
    rw [ha, hb, hpow, hpow, ← rad_avg_mul_left, ← rad_avg_sub]
    rfl
  rw [this, sub_nonneg, ← Real.mul_rpow hC0.le ha0]
  exact Real.rpow_le_rpow hb0 hba hp0.le

/-- **Equation (10)** (`eq:rank1bound`): `C^{rc} (p, q, n) ≤ UMD_{ℂ,p} (ℓ_q)` for every `n`. -/
theorem equation10 {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (n : ℕ) :
    rcThreshold (fun C => blockF n p q C) ≤ umdEllq p q := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  rcases eq_or_ne c ⊤ with rfl | hctop
  · exact le_top
  have hC : umdEllq p q < ENNReal.ofReal c.toReal := by rwa [ENNReal.ofReal_toReal hctop]
  -- `F_{n,p,q,C}` is rank-one convex at `0` for `C = c > UMD_{ℂ,p} (ℓ_q)` (Proposition 2.5)
  have hrc : RankOneConvexAt (blockF n p q c.toReal) 0 := by
    rw [proposition2_5 (twoByM_continuous_blockF n hp0 hq0 _)]
    intro N A hA
    rw [twoByM_blockF_zero n hp0 hq0]
    exact proposition4_1_nonneg hp hq A hA hC
  calc rcThreshold (fun C => blockF n p q C) ≤ ENNReal.ofReal c.toReal :=
        iInf₂_le c.toReal ⟨ENNReal.toReal_nonneg, hrc⟩
    _ = c := ENNReal.ofReal_toReal hctop

/-- **Finiteness of UMD_{ℂ,p} (ℓ_q)** (`cs-ellq-umd`, lines 991–992, "by Proposition 2.7"):
for `p, q ∈ (1, ∞)`, `UMD_{ℂ,p} (ℓ_q) < ∞`. From Proposition 2.7 (1), (3), (5), which are proved
(`Morrey/Cassese/Hypotheses.lean`): `ℓ_q` is UMD (Pisier, `pisierLpUMD_holds`), hence `UMD_p`
(extrapolation, HNVW, `hnvwExtrapolation_holds`), hence complex `UMD_p` (Yaroslavtsev,
`yaroslavtsevComplexUMD_holds`). -/
theorem umdEllq_lt_top {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    umdEllq p q < ⊤ := by
  rw [umdEllq, dite_eq_left hq.le]
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨one_le_ofReal_of_one_le hq.le⟩
  have hq' : (1 : ℝ≥0∞) < ENNReal.ofReal q := by simpa using hq
  -- Pisier: `ℓ_q` is `UMD_q`
  have h1 := pisierLpUMD_holds (ENNReal.ofReal q) hq' ENNReal.ofReal_ne_top ℕ
    (Measure.count : Measure ℕ)
  rw [ENNReal.toReal_ofReal (by linarith)] at h1
  -- HNVW: hence `UMD_p`
  have h2 := (hnvwExtrapolation_holds (Lp ℂ (ENNReal.ofReal q) (Measure.count : Measure ℕ))
    (fun x => ‖x‖) (fun x y => norm_add_le x y) (fun c x => by rw [norm_smul, Real.norm_eq_abs])
    ⟨1, 1, one_pos, one_pos, fun x => by simp⟩).1 ⟨q, hq, h1⟩ p hp
  -- Yaroslavtsev: hence complex `UMD_p`
  have h3 := (yaroslavtsevComplexUMD_holds (Lp ℂ (ENNReal.ofReal q) (Measure.count : Measure ℕ))
    p hp).2
  calc _ ≤ _ := h3
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2

/-- The point `(ξ_{2j} + i ξ_{2j+1})_j ∈ ℂ^n` of `ξ ∈ ℝ^{2n}`. -/
noncomputable def blockZ {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j : Fin n) : ℂ :=
  (ξ (blockCol j 0) : ℂ) + (ξ (blockCol j 1) : ℂ) * Complex.I

/-- The test map (11): `u_n (z) = (Π_j z̄_j) e^{−|z|²/2}` on `ℂ^n ≅ ℝ^{2n}`, with values in
`ℂ ≅ ℝ²`. -/
noncomputable def testU (n : ℕ) (ξ : Fin (2 * n) → ℝ) : Fin 2 → ℝ :=
  let w : ℂ := (∏ j, conj (blockZ ξ j)) * (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ)
  ![w.re, w.im]

/-! ### Lemma 4.2: the law of large numbers for the tensor-power test map -/

/-- The complex function `w (ξ) = (Π_j conj z_j) e^{−|ξ|²/2}` whose real and imaginary parts are
the components of `u_n`. -/
noncomputable def twoByM_W (n : ℕ) (ξ : Fin (2 * n) → ℝ) : ℂ :=
  (∏ j, conj (blockZ ξ j)) * (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ)

theorem twoByM_testU_apply (n : ℕ) (ξ : Fin (2 * n) → ℝ) :
    testU n ξ 0 = (twoByM_W n ξ).re ∧ testU n ξ 1 = (twoByM_W n ξ).im := by
  simp [testU, twoByM_W]

theorem twoByM_blockCol_inj {n : ℕ} {j j' : Fin n} {i i' : Fin 2} :
    blockCol j i = blockCol j' i' ↔ j = j' ∧ i = i' := by
  constructor
  · intro h
    simp only [blockCol, Fin.mk.injEq] at h
    have hi := i.isLt; have hi' := i'.isLt
    constructor
    · ext; omega
    · ext; omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem twoByM_blockZ_line {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j₀ : Fin n) (i₀ : Fin 2) (s : ℝ)
    (j : Fin n) :
    blockZ (ξ + s • Pi.single (blockCol j₀ i₀) 1) j =
      blockZ ξ j + if j = j₀ then (s : ℂ) * (if i₀ = 0 then 1 else Complex.I) else 0 := by
  simp only [blockZ, Pi.add_apply, Pi.smul_apply, Pi.single_apply, twoByM_blockCol_inj,
    smul_eq_mul]
  by_cases hj : j = j₀
  · subst hj
    fin_cases i₀ <;> simp <;> ring
  · simp [hj]

theorem twoByM_sumsq_line {n : ℕ} (ξ : Fin (2 * n) → ℝ) (k : Fin (2 * n)) (s : ℝ) :
    ∑ l, (ξ + s • (Pi.single k 1 : Fin (2 * n) → ℝ)) l ^ 2 =
      ∑ l, ξ l ^ 2 + 2 * s * ξ k + s ^ 2 := by
  have : ∀ l, (ξ + s • (Pi.single k 1 : Fin (2 * n) → ℝ)) l ^ 2 =
      ξ l ^ 2 + (if l = k then 2 * s * ξ k + s ^ 2 else 0) :=
    fun l => by
      by_cases hl : l = k
      · subst hl; simp; ring
      · simp [hl]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring


theorem twoByM_conj_blockZ {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j : Fin n) :
    conj (blockZ ξ j) = (ξ (blockCol j 0) : ℂ) - (ξ (blockCol j 1) : ℂ) * Complex.I := by
  simp [blockZ, sub_eq_add_neg]

theorem twoByM_differentiable_W (n : ℕ) : Differentiable ℝ (twoByM_W n) := by
  have : twoByM_W n = fun ξ => (∏ j, ((ξ (blockCol j 0) : ℂ) - (ξ (blockCol j 1) : ℂ) *
      Complex.I)) * (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ) := by
    funext ξ; simp only [twoByM_W, twoByM_conj_blockZ]
  rw [this]
  fun_prop

/-- The directional derivative `∂_k w` of `w` along the coordinate `k = blockCol j₀ i₀`:
`(Π_{j ≠ j₀} conj z_j) e^{−|ξ|²/2} (conj d − conj z_{j₀} ξ_k)`, `d = 1` (`i₀ = 0`) or `i`. -/
theorem twoByM_W_line {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j₀ : Fin n) (i₀ : Fin 2) :
    HasDerivAt (fun s : ℝ => twoByM_W n (ξ + s • Pi.single (blockCol j₀ i₀) 1))
      ((∏ j ∈ Finset.univ.erase j₀, conj (blockZ ξ j)) *
        (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ) *
        (conj (if i₀ = 0 then (1 : ℂ) else Complex.I) -
          conj (blockZ ξ j₀) * (ξ (blockCol j₀ i₀) : ℂ))) 0 := by
  classical
  set d : ℂ := if i₀ = 0 then 1 else Complex.I
  set Pr := ∏ j ∈ Finset.univ.erase j₀, conj (blockZ ξ j)
  set S := ∑ k, ξ k ^ 2
  have hfun : (fun s : ℝ => twoByM_W n (ξ + s • Pi.single (blockCol j₀ i₀) 1)) = fun s : ℝ =>
      (conj (blockZ ξ j₀) + (s : ℂ) * conj d) * Pr *
        (Real.exp (-(S + 2 * s * ξ (blockCol j₀ i₀) + s ^ 2) / 2) : ℂ) := by
    funext s
    simp only [twoByM_W]
    rw [twoByM_sumsq_line, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
    have hrest : ∏ j ∈ Finset.univ.erase j₀,
        conj (blockZ (ξ + s • Pi.single (blockCol j₀ i₀) 1) j) = Pr :=
      Finset.prod_congr rfl fun j hj => by
        rw [twoByM_blockZ_line, ite_eq_right (Finset.ne_of_mem_erase hj), add_zero]
    rw [hrest, twoByM_blockZ_line, ite_eq_left rfl, map_add, map_mul, Complex.conj_ofReal]
  rw [hfun]
  have h1 : HasDerivAt (fun s : ℝ => conj (blockZ ξ j₀) + (s : ℂ) * conj d) (conj d) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).ofReal_comp.mul_const (conj d)).const_add (conj (blockZ ξ j₀))
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => (Real.exp (-(S + 2 * s * ξ (blockCol j₀ i₀) + s ^ 2) / 2) : ℂ))
      ((Real.exp (-(S + 2 * 0 * ξ (blockCol j₀ i₀) + 0 ^ 2) / 2) *
        (-(2 * ξ (blockCol j₀ i₀) + 2 * 0) / 2) : ℝ) : ℂ) 0 := by
    refine HasDerivAt.ofReal_comp ?_
    refine HasDerivAt.exp ?_
    have := (((((hasDerivAt_id' (0 : ℝ)).const_mul 2).mul_const
      (ξ (blockCol j₀ i₀))).const_add S).add
      ((hasDerivAt_id' (0 : ℝ)).fun_pow 2)).neg.div_const 2
    convert this using 1
    norm_num
  convert (h1.mul_const Pr).mul h2 using 1
  simp
  ring


theorem twoByM_jac_testU {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j₀ : Fin n) (i₀ : Fin 2) :
    jac (testU n) ξ 0 (blockCol j₀ i₀) =
      ((∏ j ∈ Finset.univ.erase j₀, conj (blockZ ξ j)) *
        (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ) *
        (conj (if i₀ = 0 then (1 : ℂ) else Complex.I) -
          conj (blockZ ξ j₀) * (ξ (blockCol j₀ i₀) : ℂ))).re ∧
    jac (testU n) ξ 1 (blockCol j₀ i₀) =
      ((∏ j ∈ Finset.univ.erase j₀, conj (blockZ ξ j)) *
        (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ) *
        (conj (if i₀ = 0 then (1 : ℂ) else Complex.I) -
          conj (blockZ ξ j₀) * (ξ (blockCol j₀ i₀) : ℂ))).im := by
  set e : Fin (2 * n) → ℝ := Pi.single (blockCol j₀ i₀) 1
  have hW : HasFDerivAt (twoByM_W n) (fderiv ℝ (twoByM_W n) ξ) ξ :=
    (twoByM_differentiable_W n ξ).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => ξ + s • e) e 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const e).const_add ξ
  have hW0 : HasFDerivAt (twoByM_W n) (fderiv ℝ (twoByM_W n) ξ) ((fun s : ℝ => ξ + s • e) 0) := by
    simpa using hW
  have hc := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hW0 hline
  have huniq := hc.unique (twoByM_W_line ξ j₀ i₀)
  have h0 : (fun y => testU n y 0) = fun y => (twoByM_W n y).re :=
    funext fun y => (twoByM_testU_apply n y).1
  have h1 : (fun y => testU n y 1) = fun y => (twoByM_W n y).im :=
    funext fun y => (twoByM_testU_apply n y).2
  constructor
  · simp only [jac, Matrix.of_apply, h0]
    have hre : HasFDerivAt (fun y => (twoByM_W n y).re)
        (Complex.reCLM.comp (fderiv ℝ (twoByM_W n) ξ)) ξ := Complex.reCLM.hasFDerivAt.comp ξ hW
    rw [hre.fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
    exact congrArg Complex.re huniq
  · simp only [jac, Matrix.of_apply, h1]
    have him : HasFDerivAt (fun y => (twoByM_W n y).im)
        (Complex.imCLM.comp (fderiv ℝ (twoByM_W n) ξ)) ξ := Complex.imCLM.hasFDerivAt.comp ξ hW
    rw [him.fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
    exact congrArg Complex.im huniq

/-- `Q_n (∇u_n) = ∂̄ u_n`: `β_j = (Π_{k ≠ j} z̄_k) e^{−|z|²/2} (1 − |z_j|²/2)`. -/
theorem twoByM_wirtQ_jac {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j : Fin n) :
    wirtQ (jac (testU n) ξ) j = (∏ k ∈ Finset.univ.erase j, conj (blockZ ξ k)) *
      (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ) * (1 - (Complex.normSq (blockZ ξ j) : ℂ) / 2) := by
  have ha := twoByM_jac_testU ξ j 0
  have hb := twoByM_jac_testU ξ j 1
  rw [twoByM_wirtQ_apply, ha.1, ha.2, hb.1, hb.2]
  set Pr := ∏ k ∈ Finset.univ.erase j, conj (blockZ ξ k)
  set E : ℂ := (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ)
  have hz : blockZ ξ j = (ξ (blockCol j 0) : ℂ) + (ξ (blockCol j 1) : ℂ) * Complex.I := rfl
  apply Complex.ext <;>
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply, hz, ite_true, Fin.isValue, one_ne_zero, ite_false,
      map_one, Complex.conj_I, Complex.neg_re, Complex.neg_im]
    norm_num
    ring


/-- `P_n (∇u_n) = ∂ u_n`: `α_j = −(Π_{k ≠ j} z̄_k) e^{−|z|²/2} z̄_j² / 2`. -/
theorem twoByM_wirtP_jac {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j : Fin n) :
    wirtP (jac (testU n) ξ) j = -((∏ k ∈ Finset.univ.erase j, conj (blockZ ξ k)) *
      (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ) * (conj (blockZ ξ j) ^ 2 / 2)) := by
  have ha := twoByM_jac_testU ξ j 0
  have hb := twoByM_jac_testU ξ j 1
  rw [twoByM_wirtP_apply, ha.1, ha.2, hb.1, hb.2]
  have hz : blockZ ξ j = (ξ (blockCol j 0) : ℂ) + (ξ (blockCol j 1) : ℂ) * Complex.I := rfl
  apply Complex.ext <;>
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      hz, ite_true, Fin.isValue, one_ne_zero, ite_false, pow_two,
      map_one, Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.normSq_ofNat]
    norm_num
    ring

theorem twoByM_norm_prod_erase {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j : Fin n) :
    ‖∏ k ∈ Finset.univ.erase j, conj (blockZ ξ k)‖ = ∏ k ∈ Finset.univ.erase j, ‖blockZ ξ k‖ := by
  rw [norm_prod]; simp

theorem twoByM_norm_wirtQ_jac {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j : Fin n) :
    ‖wirtQ (jac (testU n) ξ) j‖ = (∏ k ∈ Finset.univ.erase j, ‖blockZ ξ k‖) *
      Real.exp (-(∑ k, ξ k ^ 2) / 2) * |1 - ‖blockZ ξ j‖ ^ 2 / 2| := by
  rw [twoByM_wirtQ_jac, norm_mul, norm_mul, twoByM_norm_prod_erase, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, ← Complex.sq_norm]
  congr 1
  rw [show (1 : ℂ) - ((‖blockZ ξ j‖ ^ 2 : ℝ) : ℂ) / 2 = ((1 - ‖blockZ ξ j‖ ^ 2 / 2 : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_real, Real.norm_eq_abs]

theorem twoByM_norm_wirtP_jac {n : ℕ} (ξ : Fin (2 * n) → ℝ) (j : Fin n) :
    ‖wirtP (jac (testU n) ξ) j‖ = (∏ k ∈ Finset.univ.erase j, ‖blockZ ξ k‖) *
      Real.exp (-(∑ k, ξ k ^ 2) / 2) * (‖blockZ ξ j‖ ^ 2 / 2) := by
  rw [twoByM_wirtP_jac, norm_neg, norm_mul, norm_mul, twoByM_norm_prod_erase, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, norm_div, norm_pow]
  simp



/-- Tonelli for products of functions of one coordinate each, on `Fin n`. -/
theorem twoByM_lintegral_fin_prod {n : ℕ} {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [SigmaFinite μ] (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ x, f i x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc _ = ∫⁻ x : E × (Fin n → E), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
          ∂(μ.prod (Measure.pi fun _ => μ)) := by
          rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
            ).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          refine lintegral_congr fun a => ?_
          rw [Fin.prod_univ_succ]
          simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
      _ = (∫⁻ x, f 0 x ∂μ) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ := by
          rw [← ih (fun i => f i.succ) (fun i => hf _), ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ =>
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂μ := by rw [Fin.prod_univ_succ]

/-- The product of measures with densities is the measure with the product density. -/
theorem twoByM_pi_withDensity {n : ℕ} {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [SigmaFinite μ] {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) [SigmaFinite (μ.withDensity ρ)] :
    Measure.pi (fun _ : Fin n => μ.withDensity ρ) =
      (Measure.pi fun _ : Fin n => μ).withDensity fun x => ∏ i, ρ (x i) := by
  refine Measure.pi_eq (ι := Fin n) (α := fun _ => E) (μ := fun _ => μ.withDensity ρ) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have : (Set.pi Set.univ s).indicator (fun x : Fin n → E => ∏ i, ρ (x i)) =
      fun x => ∏ i, (s i).indicator ρ (x i) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [this, twoByM_lintegral_fin_prod _ fun i => hρ.indicator (hs i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]


/-- The blocks `(j, i) ↦ 2 j + i` enumerate the columns of `ℝ^{2×2n}`. -/
noncomputable def twoByM_σ (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  Equiv.ofBijective (fun p => blockCol p.1 p.2) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun p p' h => ?_, by simp [mul_comm]⟩
    obtain ⟨h1, h2⟩ := twoByM_blockCol_inj.1 h
    exact Prod.ext h1 h2

theorem twoByM_σ_apply {n : ℕ} (p : Fin n × Fin 2) : twoByM_σ n p = blockCol p.1 p.2 := rfl

theorem twoByM_sum_blocks {n : ℕ} (f : Fin (2 * n) → ℝ) :
    ∑ l, f l = ∑ j : Fin n, (f (blockCol j 0) + f (blockCol j 1)) := by
  rw [← (twoByM_σ n).sum_comp, Fintype.sum_prod_type]
  simp [twoByM_σ_apply, Fin.sum_univ_two]

theorem twoByM_sumsq_eq {n : ℕ} (ξ : Fin (2 * n) → ℝ) :
    ∑ l, ξ l ^ 2 = ∑ j, ‖blockZ ξ j‖ ^ 2 := by
  rw [twoByM_sum_blocks]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [blockZ]; ring

/-- Uncurrying `(ℝ^2)^n → ℝ^{n×2}` preserves the Lebesgue measure. -/
theorem twoByM_measurePreserving_uncurry (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin 2) ℝ).symm
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin 2 => (volume : Measure ℝ))
      (Measure.pi fun _ : Fin n × Fin 2 => (volume : Measure ℝ)) := by
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin 2) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (MeasurableEquiv.curry (Fin n) (Fin 2) ℝ).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have : (MeasurableEquiv.curry (Fin n) (Fin 2) ℝ).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun j => Set.pi Set.univ fun i => s (j, i) := by
    ext f
    simp [MeasurableEquiv.curry, Set.mem_pi]
  rw [this, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- `ξ ↦ (ξ_{2j} + i ξ_{2j+1})_j` maps the Lebesgue measure of `ℝ^{2n}` to that of `ℂ^n`. -/
theorem twoByM_measurePreserving_blockZ (n : ℕ) :
    MeasurePreserving (fun ξ : Fin (2 * n) → ℝ => fun j => blockZ ξ j)
      (volume : Measure (Fin (2 * n) → ℝ)) (volume : Measure (Fin n → ℂ)) := by
  have h1 := (volume_measurePreserving_piCongrLeft (fun _ : Fin (2 * n) => ℝ) (twoByM_σ n)).symm
  have h2 := (twoByM_measurePreserving_uncurry n).symm
  have h3 : MeasurePreserving
      (fun (f : Fin n → Fin 2 → ℝ) j => Complex.measurableEquivPi.symm (f j))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin 2 => (volume : Measure ℝ))
      (Measure.pi fun _ : Fin n => (volume : Measure ℂ)) :=
    measurePreserving_pi _ _ fun _ => Complex.volume_preserving_equiv_pi.symm
  have := h3.comp (h2.comp h1)
  have hsymm : ∀ (ξ : Fin (2 * n) → ℝ) (p : Fin n × Fin 2),
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (twoByM_σ n)).symm ξ p = ξ (twoByM_σ n p) :=
    fun ξ p => Equiv.piCongrLeft_symm_apply _ _ _ _
  convert this using 1
  funext ξ j
  simp [blockZ, Complex.measurableEquivPi_symm_apply, MeasurableEquiv.curry, hsymm,
    twoByM_σ_apply]


/-! ### The product structure of the test map -/

/-- `|f (z)|^p` for `f (w) = w̄ e^{−|w|²/2}`. -/
noncomputable def twoByM_a (p : ℝ) (z : ℂ) : ℝ := (‖z‖ * Real.exp (-‖z‖ ^ 2 / 2)) ^ p

/-- `|∂̄f / f (z)|^q = |1/z̄ − z/2|^q = (|1 − |z|²/2| / |z|)^q`. -/
noncomputable def twoByM_GQ (q : ℝ) (z : ℂ) : ℝ := (|1 - ‖z‖ ^ 2 / 2| / ‖z‖) ^ q

/-- `|∂f / f (z)|^q = |z̄/2|^q`. -/
noncomputable def twoByM_GP (q : ℝ) (z : ℂ) : ℝ := (‖z‖ / 2) ^ q

theorem twoByM_exp_split {n : ℕ} (ξ : Fin (2 * n) → ℝ) :
    Real.exp (-(∑ k, ξ k ^ 2) / 2) = ∏ j, Real.exp (-‖blockZ ξ j‖ ^ 2 / 2) := by
  rw [twoByM_sumsq_eq, ← Real.exp_sum, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  simp [neg_div]

theorem twoByM_lq_rpow_eq {n : ℕ} {p q : ℝ} (hq : 0 < q) {M : ℝ} (hM : 0 ≤ M)
    (G : Fin n → ℝ) (hG : ∀ j, 0 ≤ G j) (v : Fin n → ℂ) (hv : ∀ j, ‖v j‖ = M * G j) :
    lqNorm q v ^ p = M ^ p * (∑ j, G j ^ q) ^ (p / q) := by
  have hsum : ∑ j, ‖v j‖ ^ q = M ^ q * ∑ j, G j ^ q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hv, Real.mul_rpow hM (hG j)]
  have hS : 0 ≤ ∑ j, G j ^ q := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hG j) _
  rw [lqNorm, hsum, Real.mul_rpow (Real.rpow_nonneg hM _) hS, ← Real.rpow_mul hM,
    mul_one_div_cancel hq.ne', Real.rpow_one, Real.mul_rpow hM (Real.rpow_nonneg hS _),
    ← Real.rpow_mul hS]
  congr 2; ring

theorem twoByM_prod_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (r : ℝ) : (∏ i ∈ s, f i) ^ r = ∏ i ∈ s, f i ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow (hf a (Finset.mem_insert_self a s))
        (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Away from the coordinate hyperplanes,
`‖Q_n (∇u_n)‖_{ℓ_q}^p = (Π_j |f (z_j)|^p) (Σ_j |∂̄f / f (z_j)|^q)^{p/q}`. -/
theorem twoByM_lqQ_eq {n : ℕ} {p q : ℝ} (hq : 0 < q) (ξ : Fin (2 * n) → ℝ)
    (hz : ∀ j, blockZ ξ j ≠ 0) :
    lqNorm q (wirtQ (jac (testU n) ξ)) ^ p =
      (∏ j, twoByM_a p (blockZ ξ j)) * (∑ j, twoByM_GQ q (blockZ ξ j)) ^ (p / q) := by
  set M := (∏ j, ‖blockZ ξ j‖) * Real.exp (-(∑ k, ξ k ^ 2) / 2)
  have hM : 0 ≤ M := mul_nonneg (Finset.prod_nonneg fun j _ => norm_nonneg _) (Real.exp_pos _).le
  have hG : ∀ j, 0 ≤ |1 - ‖blockZ ξ j‖ ^ 2 / 2| / ‖blockZ ξ j‖ := fun j => by positivity
  rw [twoByM_lq_rpow_eq (p := p) hq hM _ hG _ fun j => ?_]
  · congr 1
    simp only [M]
    rw [twoByM_exp_split, ← Finset.prod_mul_distrib, twoByM_prod_rpow _ _
      (fun j _ => by positivity)]
    rfl
  · simp only [M]
    rw [twoByM_norm_wirtQ_jac, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    have := norm_ne_zero_iff.2 (hz j)
    field_simp

/-- `‖P_n (∇u_n)‖_{ℓ_q}^p = (Π_j |f (z_j)|^p) (Σ_j |∂f / f (z_j)|^q)^{p/q}`. -/
theorem twoByM_lqP_eq {n : ℕ} {p q : ℝ} (hq : 0 < q) (ξ : Fin (2 * n) → ℝ) :
    lqNorm q (wirtP (jac (testU n) ξ)) ^ p =
      (∏ j, twoByM_a p (blockZ ξ j)) * (∑ j, twoByM_GP q (blockZ ξ j)) ^ (p / q) := by
  set M := (∏ j, ‖blockZ ξ j‖) * Real.exp (-(∑ k, ξ k ^ 2) / 2)
  have hM : 0 ≤ M := mul_nonneg (Finset.prod_nonneg fun j _ => norm_nonneg _) (Real.exp_pos _).le
  have hG : ∀ j, 0 ≤ ‖blockZ ξ j‖ / 2 := fun j => by positivity
  rw [twoByM_lq_rpow_eq (p := p) hq hM _ hG _ fun j => ?_]
  · congr 1
    simp only [M]
    rw [twoByM_exp_split, ← Finset.prod_mul_distrib, twoByM_prod_rpow _ _
      (fun j _ => by positivity)]
    rfl
  · simp only [M]
    rw [twoByM_norm_wirtP_jac, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    ring



/-- Radial functions `‖z‖^r e^{−b‖z‖²}` (`r > −2`, `b > 0`) are integrable on `ℂ`. -/
theorem twoByM_integrable_radial {r b : ℝ} (hr : -2 < r) (hb : 0 < b) :
    Integrable (fun z : ℂ => ‖z‖ ^ r * Real.exp (-b * ‖z‖ ^ 2)) := by
  have := (integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun y : ℝ => y ^ r * Real.exp (-b * y ^ 2))).2
  refine this ?_
  rw [Complex.finrank_real_complex]
  refine (integrableOn_rpow_mul_exp_neg_mul_sq hb (s := r + 1) (by linarith)).congr_fun
    (fun y (hy : 0 < y) => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [Real.rpow_add hy, Real.rpow_one]; ring

/-- `‖z‖^r` (`r ≤ −2`) is not integrable on the unit disc. -/
theorem twoByM_not_integrableOn_ball {r : ℝ} (hr : r ≤ -2) :
    ¬ IntegrableOn (fun z : ℂ => ‖z‖ ^ r) (Metric.ball (0 : ℂ) 1) := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ => y ^ r),
    Complex.finrank_real_complex]
  intro h
  have h2 : IntegrableOn (fun y : ℝ => y ^ (r + 1)) (Set.Ioo 0 1) :=
    h.congr_fun (fun y (hy : y ∈ Set.Ioo 0 1) => by
      simp only [smul_eq_mul]; rw [Real.rpow_add hy.1, Real.rpow_one]; ring)
      measurableSet_Ioo
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := r + 1) one_pos).1 h2
  linarith

/-- For a nonnegative measurable `f`, `∫⁻ ofReal f < ∞` iff `f` is integrable. -/
theorem twoByM_lintegral_ofReal_eq_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (h0 : ∀ x, 0 ≤ f x) (hni : ¬ Integrable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ⊤ := by
  by_contra h
  apply hni
  refine ⟨hf, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)]
  exact lt_top_iff_ne_top.2 h


theorem twoByM_a_eq {p : ℝ} (z : ℂ) :
    twoByM_a p z = ‖z‖ ^ p * Real.exp (-(p / 2) * ‖z‖ ^ 2) := by
  rw [twoByM_a, Real.mul_rpow (norm_nonneg _) (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2; ring

theorem twoByM_a_nonneg (p : ℝ) (z : ℂ) : 0 ≤ twoByM_a p z := by unfold twoByM_a; positivity

theorem twoByM_GQ_nonneg (q : ℝ) (z : ℂ) : 0 ≤ twoByM_GQ q z := by unfold twoByM_GQ; positivity

theorem twoByM_GP_nonneg (q : ℝ) (z : ℂ) : 0 ≤ twoByM_GP q z := by unfold twoByM_GP; positivity

theorem twoByM_measurable_a (p : ℝ) : Measurable (twoByM_a p) := by
  unfold twoByM_a; fun_prop

theorem twoByM_measurable_GQ (q : ℝ) : Measurable (twoByM_GQ q) := by
  unfold twoByM_GQ; fun_prop

theorem twoByM_measurable_GP (q : ℝ) : Measurable (twoByM_GP q) := by
  unfold twoByM_GP; fun_prop

theorem twoByM_integrable_a {p : ℝ} (hp : 0 < p) : Integrable (twoByM_a p) := by
  have := twoByM_integrable_radial (r := p) (b := p / 2) (by linarith) (by linarith)
  refine this.congr (Eventually.of_forall fun z => ?_)
  rw [twoByM_a_eq]

theorem twoByM_integrable_aGP {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable fun z => twoByM_a p z * twoByM_GP q z := by
  have := (twoByM_integrable_radial (r := p + q) (b := p / 2) (by linarith)
    (by linarith)).const_mul ((1 / 2) ^ q)
  refine this.congr (Eventually.of_forall fun z => ?_)
  have e1 : (‖z‖ / 2) ^ q = (1 / 2) ^ q * ‖z‖ ^ q := by
    rw [div_eq_mul_one_div, Real.mul_rpow (norm_nonneg _) (by norm_num), mul_comm]
  have e2 : ‖z‖ ^ (p + q) = ‖z‖ ^ p * ‖z‖ ^ q := Real.rpow_add' (norm_nonneg _) (by linarith)
  simp only [twoByM_a_eq, twoByM_GP, e1, e2]
  ring

/-- The divergence of `E_μ |∂̄f / f|^q` for `q ≥ p + 2`: near `0`, `|f|^p |∂̄f / f|^q` is at least
a multiple of `|z|^{p − q}`. -/
theorem twoByM_lintegral_aGQ_eq_top {p q : ℝ} (hp : 0 < p) (hpq : p + 2 ≤ q) :
    ∫⁻ z, ENNReal.ofReal (twoByM_a p z * twoByM_GQ q z) = ⊤ := by
  have hq : 0 < q := by linarith
  set C : ℝ := Real.exp (-(p / 2)) * (1 / 2) ^ q
  have hC : 0 < C := by positivity
  have hle : ∀ z ∈ Metric.ball (0 : ℂ) 1, C * ‖z‖ ^ (p - q) ≤ twoByM_a p z * twoByM_GQ q z := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    rcases eq_or_ne z 0 with rfl | hz0
    · simp only [norm_zero, Real.zero_rpow (by linarith : p - q ≠ 0), mul_zero]
      exact mul_nonneg (twoByM_a_nonneg _ _) (twoByM_GQ_nonneg _ _)
    have hr : 0 < ‖z‖ := norm_pos_iff.2 hz0
    rw [twoByM_a_eq, twoByM_GQ, Real.div_rpow (abs_nonneg _) hr.le, Real.rpow_sub hr]
    have h1 : Real.exp (-(p / 2)) ≤ Real.exp (-(p / 2) * ‖z‖ ^ 2) := by
      apply Real.exp_le_exp.2
      have : ‖z‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have h2 : (1 / 2 : ℝ) ^ q ≤ |1 - ‖z‖ ^ 2 / 2| ^ q := by
      apply Real.rpow_le_rpow (by norm_num) _ hq.le
      rw [abs_of_pos (by nlinarith)]
      nlinarith
    have hpz : 0 < ‖z‖ ^ p := Real.rpow_pos_of_pos hr _
    have hqz : 0 < ‖z‖ ^ q := Real.rpow_pos_of_pos hr _
    calc C * (‖z‖ ^ p / ‖z‖ ^ q) = (‖z‖ ^ p / ‖z‖ ^ q) * Real.exp (-(p / 2)) * (1 / 2) ^ q := by
          simp only [C]; ring
      _ ≤ (‖z‖ ^ p / ‖z‖ ^ q) * Real.exp (-(p / 2) * ‖z‖ ^ 2) * |1 - ‖z‖ ^ 2 / 2| ^ q := by
          gcongr
      _ = _ := by ring
  have htop : ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (C * ‖z‖ ^ (p - q)) = ⊤ := by
    refine twoByM_lintegral_ofReal_eq_top
      (measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable
      (fun z => by positivity) fun h => ?_
    exact twoByM_not_integrableOn_ball (r := p - q) (by linarith)
      ((h.const_mul C⁻¹).congr (Eventually.of_forall fun z => by field_simp))
  refine eq_top_iff.2 (htop.symm.le.trans ?_)
  calc ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (C * ‖z‖ ^ (p - q))
      ≤ ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (twoByM_a p z * twoByM_GQ q z) :=
        setLIntegral_mono ((twoByM_measurable_a p).mul (twoByM_measurable_GQ q)).ennreal_ofReal
          fun z hz => ENNReal.ofReal_le_ofReal (hle z hz)
    _ ≤ _ := setLIntegral_le_lintegral _ _


/-- `ν = |f|^p dA`. -/
noncomputable def twoByM_ν (p : ℝ) : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (twoByM_a p z)

/-- `c = ∫ |f|^p dA`. -/
noncomputable def twoByM_c (p : ℝ) : ℝ≥0∞ := twoByM_ν p Set.univ

/-- The probability measure `μ = c⁻¹ |f|^p dA` of the proof of Lemma 4.2. -/
noncomputable def twoByM_prob (p : ℝ) : Measure ℂ := (twoByM_c p)⁻¹ • twoByM_ν p

theorem twoByM_c_eq (p : ℝ) : twoByM_c p = ∫⁻ z, ENNReal.ofReal (twoByM_a p z) := by
  rw [twoByM_c, twoByM_ν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

theorem twoByM_c_lt_top {p : ℝ} (hp : 0 < p) : twoByM_c p < ⊤ := by
  rw [twoByM_c_eq]; exact (twoByM_integrable_a hp).lintegral_lt_top

theorem twoByM_c_ne_zero (p : ℝ) : twoByM_c p ≠ 0 := by
  rw [twoByM_c_eq]
  intro h
  rw [lintegral_eq_zero_iff (twoByM_measurable_a p).ennreal_ofReal] at h
  have h0 : ∀ᵐ z ∂(volume : Measure ℂ), z = 0 := by
    filter_upwards [h] with z hz
    by_contra hne
    have : 0 < twoByM_a p z := by
      unfold twoByM_a
      exact Real.rpow_pos_of_pos (mul_pos (norm_pos_iff.2 hne) (Real.exp_pos _)) _
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hz
    linarith
  have : (volume : Measure ℂ) Set.univ = 0 := by
    have h1 : (volume : Measure ℂ) {z | ¬ z = 0} = 0 := ae_iff.1 h0
    refine le_antisymm ?_ (zero_le)
    calc (volume : Measure ℂ) Set.univ ≤ volume ({0} ∪ {z | ¬ z = 0}) :=
          measure_mono fun z _ => by by_cases hz : z = 0 <;> simp [hz]
      _ ≤ volume {(0 : ℂ)} + volume {z : ℂ | ¬ z = 0} := measure_union_le _ _
      _ = 0 := by rw [h1, measure_singleton, add_zero]
  exact (Measure.measure_univ_ne_zero.2 (NeZero.ne volume)) this

theorem twoByM_isProbabilityMeasure {p : ℝ} (hp : 0 < p) :
    IsProbabilityMeasure (twoByM_prob p) := by
  constructor
  rw [twoByM_prob, Measure.smul_apply, smul_eq_mul, ← twoByM_c]
  exact ENNReal.inv_mul_cancel (twoByM_c_ne_zero p) (twoByM_c_lt_top hp).ne

theorem twoByM_ν_eq {p : ℝ} (hp : 0 < p) : twoByM_ν p = twoByM_c p • twoByM_prob p := by
  rw [twoByM_prob, smul_smul, ENNReal.mul_inv_cancel (twoByM_c_ne_zero p)
    (twoByM_c_lt_top hp).ne, one_smul]

/-- `∫ g dμ = c⁻¹ ∫ |f|^p g dA`. -/
theorem twoByM_lintegral_prob {p : ℝ} {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z ∂twoByM_prob p =
      (twoByM_c p)⁻¹ * ∫⁻ z, ENNReal.ofReal (twoByM_a p z) * g z := by
  rw [twoByM_prob, lintegral_smul_measure, twoByM_ν,
    lintegral_withDensity_eq_lintegral_mul _ (twoByM_measurable_a p).ennreal_ofReal hg]
  rfl


theorem twoByM_pi_smul {n : ℕ} {E : Type*} [MeasurableSpace E] (m : Measure E) [SigmaFinite m]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    Measure.pi (fun _ : Fin n => c • m) = c ^ n • Measure.pi fun _ : Fin n => m := by
  have : SigmaFinite (c • m) := by
    rw [← ENNReal.coe_toNNReal hc]
    exact SMul.sigmaFinite (μ := m) c.toNNReal
  refine Measure.pi_eq (ι := Fin n) (α := fun _ => E) (μ := fun _ => c • m) fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]


/-- The i.i.d. sequence of the proof of Lemma 4.2: `ℂ^ℕ` with the product of copies of `μ`. -/
noncomputable def twoByM_P (p : ℝ) : Measure (ℕ → ℂ) :=
  Measure.infinitePi fun _ : ℕ => twoByM_prob p

/-- Integrals of `(Π_j |f (z_j)|^p) Φ (z)` over `ℂ^n` are `c^n` times expectations over the first
`n` coordinates of the i.i.d. sequence. -/
theorem twoByM_lintegral_product {n : ℕ} {p : ℝ} (hp : 0 < p) {Φ : (Fin n → ℂ) → ℝ}
    (hΦ : Measurable Φ) :
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal ((∏ j, twoByM_a p (z j)) * Φ z) =
      twoByM_c p ^ n * ∫⁻ ω : ℕ → ℂ, ENNReal.ofReal (Φ fun j => ω j) ∂twoByM_P p := by
  have hP := twoByM_isProbabilityMeasure hp
  have hfin : IsFiniteMeasure (twoByM_ν p) := ⟨by rw [← twoByM_c]; exact twoByM_c_lt_top hp⟩
  have hpi := twoByM_pi_withDensity (n := n) (μ := (volume : Measure ℂ))
    (twoByM_measurable_a p).ennreal_ofReal
  have hsmul := twoByM_pi_smul (n := n) (twoByM_prob p) (twoByM_c_lt_top hp).ne
  have hmap : (twoByM_P p).map (fun ω (j : Fin n) => ω j) =
      Measure.pi fun _ : Fin n => twoByM_prob p := by
    rw [twoByM_P, Measure.map_infinitePi_infinitePi_of_inj (f := (Fin.val : Fin n → ℕ))
      Fin.val_injective, Measure.infinitePi_eq_pi]
  have hmeas : Measurable fun ω : ℕ → ℂ => fun j : Fin n => ω j := by fun_prop
  have hmf : Measurable fun x : Fin n → ℂ => ∏ i, ENNReal.ofReal (twoByM_a p (x i)) :=
    Finset.measurable_prod (f := fun i (x : Fin n → ℂ) => ENNReal.ofReal (twoByM_a p (x i))) _
      fun i _ => (twoByM_measurable_a p).ennreal_ofReal.comp (measurable_pi_apply i)
  calc ∫⁻ z : Fin n → ℂ, ENNReal.ofReal ((∏ j, twoByM_a p (z j)) * Φ z)
      = ∫⁻ z : Fin n → ℂ, (fun z => ∏ j, ENNReal.ofReal (twoByM_a p (z j))) z *
          ENNReal.ofReal (Φ z) := by
        refine lintegral_congr fun z => ?_
        rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => twoByM_a_nonneg p _),
          ENNReal.ofReal_prod_of_nonneg fun j _ => twoByM_a_nonneg p _]
    _ = ∫⁻ z, ENNReal.ofReal (Φ z) ∂Measure.pi fun _ : Fin n => twoByM_ν p := by
        rw [twoByM_ν, hpi, lintegral_withDensity_eq_lintegral_mul _ hmf hΦ.ennreal_ofReal]
        rfl
    _ = twoByM_c p ^ n * ∫⁻ z, ENNReal.ofReal (Φ z) ∂Measure.pi fun _ : Fin n => twoByM_prob p := by
        rw [twoByM_ν_eq hp, hsmul, lintegral_smul_measure, smul_eq_mul]
    _ = _ := by
        rw [← hmap, lintegral_map hΦ.ennreal_ofReal hmeas]


open ProbabilityTheory in
/-- The law of large numbers for the truncations `min (G, M)` of `G ≥ 0`, with Fatou's lemma:
`(E min (G, M))^s ≤ liminf_n E (n⁻¹ Σ_{j<n} G (Z_j))^s` for an i.i.d. sequence `Z_j ∼ ν`. -/
theorem twoByM_lln_lower {ν : Measure ℂ} [IsProbabilityMeasure ν] {G : ℂ → ℝ}
    (hG : Measurable G) (hG0 : ∀ z, 0 ≤ G z) {s : ℝ} (hs : 0 < s) (M : ℕ) :
    ENNReal.ofReal (∫ z, min (G z) M ∂ν) ^ s ≤ liminf (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal
      (((∑ j ∈ Finset.range n, G (ω j)) / n) ^ s) ∂(Measure.infinitePi fun _ : ℕ => ν)) atTop := by
  have hXm : Measurable fun z => min (G z) (M : ℝ) := hG.min measurable_const
  have hX0 : ∀ z, 0 ≤ min (G z) (M : ℝ) := fun z => le_min (hG0 z) (Nat.cast_nonneg M)
  have hXint : Integrable (fun z => min (G z) (M : ℝ)) ν :=
    (integrable_const (M : ℝ)).mono' hXm.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_of_nonneg (hX0 z)]; exact min_le_right _ _)
  have hev : ∀ i, MeasurePreserving (Function.eval i) (Measure.infinitePi fun _ : ℕ => ν) ν :=
    fun i => measurePreserving_eval_infinitePi (fun _ : ℕ => ν) i
  set Y : ℕ → (ℕ → ℂ) → ℝ := fun i ω => min (G (ω i)) M
  have hind : iIndepFun Y (Measure.infinitePi fun _ : ℕ => ν) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ z => min (G z) (M : ℝ)) fun _ => hXm
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) (Measure.infinitePi fun _ : ℕ => ν)
      (Measure.infinitePi fun _ : ℕ => ν) := by
    intro i
    refine ⟨(hXm.comp (measurable_pi_apply i)).aemeasurable,
      (hXm.comp (measurable_pi_apply 0)).aemeasurable, ?_⟩
    show Measure.map ((fun z => min (G z) (M : ℝ)) ∘ (Function.eval i : (ℕ → ℂ) → ℂ)) _ =
      Measure.map ((fun z => min (G z) (M : ℝ)) ∘ (Function.eval 0 : (ℕ → ℂ) → ℂ)) _
    rw [← Measure.map_map hXm (measurable_pi_apply i),
      ← Measure.map_map hXm (measurable_pi_apply 0),
      (hev i).map_eq, (hev 0).map_eq]
  have hint0 : Integrable (Y 0) (Measure.infinitePi fun _ : ℕ => ν) :=
    (hev 0).integrable_comp_of_integrable hXint
  have hlaw := strong_law_ae_real Y hint0 (fun i j hij => hind.indepFun hij) hident
  have hmean : ∫ ω, Y 0 ω ∂(Measure.infinitePi fun _ : ℕ => ν) = ∫ z, min (G z) M ∂ν := by
    have := integral_map (μ := Measure.infinitePi fun _ : ℕ => ν) (hev 0).measurable.aemeasurable
      (f := fun z => min (G z) (M : ℝ)) (by rw [(hev 0).map_eq]; exact hXm.aestronglyMeasurable)
    rw [(hev 0).map_eq] at this
    exact this.symm
  rw [hmean] at hlaw
  have hcont : Continuous fun x : ℝ => ENNReal.ofReal (x ^ s) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_rpow_const hs.le)
  have hmeas : ∀ n : ℕ, Measurable fun ω : ℕ → ℂ => ENNReal.ofReal
      (((∑ j ∈ Finset.range n, G (ω j)) / n) ^ s) := fun n => by
    refine (Measurable.pow_const ?_ _).ennreal_ofReal
    exact (Finset.measurable_sum _ fun j _ => hG.comp (measurable_pi_apply j)).div_const _
  calc ENNReal.ofReal (∫ z, min (G z) M ∂ν) ^ s
      = ∫⁻ _ω, ENNReal.ofReal ((∫ z, min (G z) M ∂ν) ^ s) ∂(Measure.infinitePi fun _ : ℕ => ν) := by
        rw [lintegral_const, measure_univ, mul_one,
          ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hX0) hs.le]
    _ ≤ ∫⁻ ω, liminf (fun n : ℕ => ENNReal.ofReal
        (((∑ j ∈ Finset.range n, G (ω j)) / n) ^ s)) atTop
          ∂(Measure.infinitePi fun _ : ℕ => ν) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hlaw] with ω hω
        have ht := (hcont.tendsto _).comp hω
        rw [← ht.liminf_eq]
        refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
        simp only [Function.comp]
        refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ?_ ?_ hs.le)
        · exact div_nonneg (Finset.sum_nonneg fun j _ => hX0 _) (Nat.cast_nonneg n)
        · exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => min_le_left _ _)
            (Nat.cast_nonneg n)
    _ ≤ _ := lintegral_liminf_le hmeas


/-- The numerator of the proof of Lemma 4.2: `E (n⁻¹ Σ_{j<n} |∂̄f/f (Z_j)|^q)^{p/q} → ∞`, by the
law of large numbers for the truncations and Fatou's lemma (`twoByM_lln_lower`), since
`E |∂̄f/f (Z)|^q = ∞` for `q ≥ p + 2`. -/
theorem twoByM_numerator_tendsto {p q : ℝ} (hp : 0 < p) (hpq : p + 2 ≤ q) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal
      (((∑ j ∈ Finset.range n, twoByM_GQ q (ω j)) / n) ^ (p / q)) ∂twoByM_P p) atTop (𝓝 ⊤) := by
  have hP := twoByM_isProbabilityMeasure hp
  have hq : 0 < q := by linarith
  have hs : 0 < p / q := div_pos hp hq
  -- `E |∂̄f/f|^q = ∞`
  have hE : ∫⁻ z, ENNReal.ofReal (twoByM_GQ q z) ∂twoByM_prob p = ⊤ := by
    rw [twoByM_lintegral_prob (twoByM_measurable_GQ q).ennreal_ofReal]
    have : ∫⁻ z, ENNReal.ofReal (twoByM_a p z) * ENNReal.ofReal (twoByM_GQ q z) = ⊤ := by
      rw [← twoByM_lintegral_aGQ_eq_top hp hpq]
      exact lintegral_congr fun z => (ENNReal.ofReal_mul (twoByM_a_nonneg p z)).symm
    rw [this, ENNReal.mul_top (ENNReal.inv_ne_zero.2 (twoByM_c_lt_top hp).ne)]
  -- the truncated means `m M = E min (|∂̄f/f|^q, M)` tend to `∞` (monotone convergence)
  set m : ℕ → ℝ := fun M => ∫ z, min (twoByM_GQ q z) M ∂twoByM_prob p
  have hm : ∀ M : ℕ, ENNReal.ofReal (m M) =
      ∫⁻ z, ENNReal.ofReal (min (twoByM_GQ q z) M) ∂twoByM_prob p := fun M => by
    refine ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun z =>
      le_min (twoByM_GQ_nonneg q z) (Nat.cast_nonneg M))
    exact (integrable_const (M : ℝ)).mono'
      ((twoByM_measurable_GQ q).min measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (le_min (twoByM_GQ_nonneg q z) (Nat.cast_nonneg M))]
        exact min_le_right _ _)
  have hsup : ⨆ M : ℕ, ENNReal.ofReal (m M) = ⊤ := by
    simp_rw [hm]
    rw [← lintegral_iSup (fun M => ((twoByM_measurable_GQ q).min measurable_const).ennreal_ofReal)
      (fun M M' hMM' z => ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.2 hMM'))),
      ← hE]
    refine lintegral_congr fun z => ?_
    refine le_antisymm (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
    obtain ⟨M, hM⟩ := exists_nat_ge (twoByM_GQ q z)
    exact le_iSup_of_le M (le_of_eq (by rw [min_eq_left hM]))
  refine tendsto_order.2 ⟨fun B hB => ?_, fun B hB => (not_top_lt hB).elim⟩
  have : B ^ (1 / (p / q)) < ⨆ M : ℕ, ENNReal.ofReal (m M) := by
    rw [hsup]; exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hB.ne
  obtain ⟨M, hM⟩ := lt_iSup_iff.1 this
  have hBM : B < ENNReal.ofReal (m M) ^ (p / q) := by
    have := ENNReal.rpow_lt_rpow hM hs
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hs.ne', ENNReal.rpow_one] at this
  exact eventually_lt_of_lt_liminf (hBM.trans_le
    (twoByM_lln_lower (twoByM_measurable_GQ q) (twoByM_GQ_nonneg q) hs M))


/-- Jensen's inequality for the concave `t ↦ t^s`, `0 < s < 1`, on a probability space (here
from Hölder's inequality with the exponents `1/s` and `1/(1 − s)`). -/
theorem twoByM_lintegral_rpow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ≥0∞} (hY : AEMeasurable Y P) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) : ∫⁻ ω, Y ω ^ s ∂P ≤ (∫⁻ ω, Y ω ∂P) ^ s := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P (Real.HolderConjugate.inv_one_sub_inv hs0 hs1)
    (f := fun ω => Y ω ^ s) (g := 1) (hY.pow_const s) aemeasurable_const
  simp only [Pi.mul_apply, Pi.one_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    measure_univ, one_div, inv_inv] at h
  simp only [← ENNReal.rpow_mul, mul_inv_cancel₀ hs0.ne', ENNReal.rpow_one] at h
  exact h

/-- The denominator of the proof of Lemma 4.2:
`E (n⁻¹ Σ_{j<n} |∂f/f (Z_j)|^q)^{p/q} ≤ (E |∂f/f (Z)|^q)^{p/q}` (Jensen, `p/q < 1`). -/
theorem twoByM_denominator_le {p q : ℝ} (hp : 0 < p) (hpq : p < q) {n : ℕ} (hn : 0 < n) :
    ∫⁻ ω, ENNReal.ofReal (((∑ j ∈ Finset.range n, twoByM_GP q (ω j)) / n) ^ (p / q))
      ∂twoByM_P p ≤ (∫⁻ z, ENNReal.ofReal (twoByM_GP q z) ∂twoByM_prob p) ^ (p / q) := by
  have hP := twoByM_isProbabilityMeasure hp
  have hPP : IsProbabilityMeasure (twoByM_P p) := by unfold twoByM_P; infer_instance
  have hq : 0 < q := by linarith
  have hs0 : 0 < p / q := div_pos hp hq
  have hs1 : p / q < 1 := (div_lt_one hq).2 hpq
  have hev : ∀ i, MeasurePreserving (Function.eval i) (twoByM_P p) (twoByM_prob p) := fun i =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => twoByM_prob p) i
  have hnn : ∀ ω : ℕ → ℂ, 0 ≤ (∑ j ∈ Finset.range n, twoByM_GP q (ω j)) / n := fun ω =>
    div_nonneg (Finset.sum_nonneg fun j _ => twoByM_GP_nonneg q _) (Nat.cast_nonneg n)
  have hmeasj : ∀ j, Measurable fun ω : ℕ → ℂ => ENNReal.ofReal (twoByM_GP q (ω j)) := fun j =>
    ((twoByM_measurable_GP q).comp (measurable_pi_apply j)).ennreal_ofReal
  calc ∫⁻ ω, ENNReal.ofReal (((∑ j ∈ Finset.range n, twoByM_GP q (ω j)) / n) ^ (p / q))
        ∂twoByM_P p
      = ∫⁻ ω, ENNReal.ofReal ((∑ j ∈ Finset.range n, twoByM_GP q (ω j)) / n) ^ (p / q)
          ∂twoByM_P p :=
        lintegral_congr fun ω => (ENNReal.ofReal_rpow_of_nonneg (hnn ω) hs0.le).symm
    _ ≤ (∫⁻ ω, ENNReal.ofReal ((∑ j ∈ Finset.range n, twoByM_GP q (ω j)) / n)
          ∂twoByM_P p) ^ (p / q) := by
        refine twoByM_lintegral_rpow_le ?_ hs0 hs1
        exact ((Finset.measurable_sum _ fun j _ => (twoByM_measurable_GP q).comp
          (measurable_pi_apply j)).div_const _).ennreal_ofReal.aemeasurable
    _ = _ := by
        congr 1
        have hn' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
        calc ∫⁻ ω, ENNReal.ofReal ((∑ j ∈ Finset.range n, twoByM_GP q (ω j)) / n) ∂twoByM_P p
            = ∫⁻ ω, (∑ j ∈ Finset.range n, ENNReal.ofReal (twoByM_GP q (ω j))) * (n : ℝ≥0∞)⁻¹
                ∂twoByM_P p := by
              refine lintegral_congr fun ω => ?_
              rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn),
                ENNReal.ofReal_sum_of_nonneg fun j _ => twoByM_GP_nonneg q _,
                ENNReal.ofReal_natCast, div_eq_mul_inv]
          _ = (∑ j ∈ Finset.range n, ∫⁻ ω, ENNReal.ofReal (twoByM_GP q (ω j)) ∂twoByM_P p) *
                (n : ℝ≥0∞)⁻¹ := by
              rw [lintegral_mul_const _ (Finset.measurable_sum _ fun j _ => hmeasj j),
                lintegral_finsetSum _ fun j _ => hmeasj j]
          _ = (n : ℝ≥0∞) * (∫⁻ z, ENNReal.ofReal (twoByM_GP q z) ∂twoByM_prob p) *
                (n : ℝ≥0∞)⁻¹ := by
              congr 1
              rw [Finset.sum_congr rfl fun j _ => ?_, Finset.sum_const, Finset.card_range,
                nsmul_eq_mul]
              exact (hev j).lintegral_comp ((twoByM_measurable_GP q).ennreal_ofReal)
          _ = _ := by
              rw [mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel hn' (ENNReal.natCast_ne_top n),
                one_mul]


theorem twoByM_continuous_blockZ {n : ℕ} (j : Fin n) :
    Continuous fun ξ : Fin (2 * n) → ℝ => blockZ ξ j := by
  unfold blockZ; fun_prop

theorem twoByM_continuous_lqQ {n : ℕ} {q : ℝ} (hq : 0 < q) :
    Continuous fun ξ : Fin (2 * n) → ℝ => lqNorm q (wirtQ (jac (testU n) ξ)) := by
  have : (fun ξ : Fin (2 * n) → ℝ => lqNorm q (wirtQ (jac (testU n) ξ))) = fun ξ =>
      lqNorm q fun j => (∏ k ∈ Finset.univ.erase j, conj (blockZ ξ k)) *
        (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ) * (1 - (Complex.normSq (blockZ ξ j) : ℂ) / 2) :=
    funext fun ξ => congrArg (lqNorm q) (funext (twoByM_wirtQ_jac ξ))
  rw [this]
  refine (twoByM_continuous_lqNorm hq).comp (continuous_pi fun j => ?_)
  have := twoByM_continuous_blockZ (n := n)
  fun_prop

theorem twoByM_continuous_lqP {n : ℕ} {q : ℝ} (hq : 0 < q) :
    Continuous fun ξ : Fin (2 * n) → ℝ => lqNorm q (wirtP (jac (testU n) ξ)) := by
  have : (fun ξ : Fin (2 * n) → ℝ => lqNorm q (wirtP (jac (testU n) ξ))) = fun ξ =>
      lqNorm q fun j => -((∏ k ∈ Finset.univ.erase j, conj (blockZ ξ k)) *
        (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ) * (conj (blockZ ξ j) ^ 2 / 2)) :=
    funext fun ξ => congrArg (lqNorm q) (funext (twoByM_wirtP_jac ξ))
  rw [this]
  refine (twoByM_continuous_lqNorm hq).comp (continuous_pi fun j => ?_)
  have := twoByM_continuous_blockZ (n := n)
  fun_prop

/-- `‖F‖_{L^p}^p = ∫ F^p` for a continuous `F ≥ 0`. -/
theorem twoByM_eLpNorm_eq_rpow {d : ℕ} {p : ℝ} (hp : 0 < p) {F : (Fin d → ℝ) → ℝ}
    (hF : Continuous F) (hF0 : ∀ ξ, 0 ≤ F ξ) :
    eLpNorm F (ENNReal.ofReal p) volume = (∫⁻ ξ, ENNReal.ofReal (F ξ ^ p)) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    hF.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  congr 1
  refine lintegral_congr fun ξ => ?_
  rw [Real.enorm_eq_ofReal (hF0 ξ), ENNReal.ofReal_rpow_of_nonneg (hF0 ξ) hp.le]

/-- Almost every `ξ ∈ ℝ^{2n}` has all its blocks `z_j ≠ 0`. -/
theorem twoByM_ae_blockZ_ne_zero (n : ℕ) :
    ∀ᵐ ξ : Fin (2 * n) → ℝ, ∀ j, blockZ ξ j ≠ 0 := by
  refine ae_all_iff.2 fun j => ?_
  have hT := twoByM_measurePreserving_blockZ n
  have : (volume : Measure (Fin (2 * n) → ℝ)) {ξ | blockZ ξ j = 0} = 0 := by
    have h := hT.measure_preimage (s := {z : Fin n → ℂ | z j = 0})
      (measurableSet_eq_fun (measurable_pi_apply j) measurable_const).nullMeasurableSet
    rw [show (fun ξ : Fin (2 * n) → ℝ => fun j => blockZ ξ j) ⁻¹' {z | z j = 0} =
      {ξ | blockZ ξ j = 0} from rfl] at h
    rw [h]
    exact Measure.pi_hyperplane _ j 0
  exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun ξ hξ => hξ


/-- `∫_{ℝ^{2n}} G (∇u_n) = c^n n^{p/q} E (n⁻¹ Σ_{j<n} g (Z_j))^{p/q}` for the integrands
`‖·‖_{ℓ_q}^p` of `Q_n (∇u_n)` (`g = |∂̄f/f|^q`) and of `P_n (∇u_n)` (`g = |∂f/f|^q`). -/
theorem twoByM_integral_reduce {n : ℕ} (hn : 0 < n) {p q : ℝ} (hp : 0 < p)
    {G : ℂ → ℝ} (hG : Measurable G) (hG0 : ∀ z, 0 ≤ G z) {F : (Fin (2 * n) → ℝ) → ℝ}
    (hF : ∀ᵐ ξ, F ξ = (∏ j, twoByM_a p (blockZ ξ j)) * (∑ j, G (blockZ ξ j)) ^ (p / q)) :
    ∫⁻ ξ, ENNReal.ofReal (F ξ) = twoByM_c p ^ n * (ENNReal.ofReal ((n : ℝ) ^ (p / q)) *
      ∫⁻ ω, ENNReal.ofReal (((∑ j ∈ Finset.range n, G (ω j)) / n) ^ (p / q)) ∂twoByM_P p) := by
  have hT := twoByM_measurePreserving_blockZ n
  have hΦ : Measurable fun z : Fin n → ℂ => (∑ j, G (z j)) ^ (p / q) :=
    (Finset.measurable_sum _ fun j _ => hG.comp (measurable_pi_apply j)).pow_const _
  have hprod : Measurable fun z : Fin n → ℂ =>
      ENNReal.ofReal ((∏ j, twoByM_a p (z j)) * (∑ j, G (z j)) ^ (p / q)) :=
    ((Finset.measurable_prod (f := fun j (z : Fin n → ℂ) => twoByM_a p (z j)) _
      fun j _ => (twoByM_measurable_a p).comp (measurable_pi_apply j)).mul hΦ).ennreal_ofReal
  rw [lintegral_congr_ae (hF.mono fun ξ hξ => by rw [hξ]),
    hT.lintegral_comp (f := fun z : Fin n → ℂ =>
      ENNReal.ofReal ((∏ j, twoByM_a p (z j)) * (∑ j, G (z j)) ^ (p / q))) hprod,
    twoByM_lintegral_product hp hΦ]
  congr 1
  rw [← lintegral_const_mul _ ?_]
  · refine lintegral_congr fun ω => ?_
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hS : 0 ≤ (∑ j ∈ Finset.range n, G (ω j)) / n :=
      div_nonneg (Finset.sum_nonneg fun j _ => hG0 _) hn'.le
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hn'.le _), ← Real.mul_rpow hn'.le hS,
      mul_div_cancel₀ _ hn'.ne', Fin.sum_univ_eq_sum_range (fun j => G (ω j))]
  · exact ((Finset.measurable_sum _ fun j _ => hG.comp (measurable_pi_apply j)).div_const _
      |>.pow_const _).ennreal_ofReal

/-- **Lemma 4.2** (`lem:order`): if `1 < p < ∞` and `p + 2 ≤ q < ∞`, then
`‖Q_n (∇u_n)‖_{L^p (ℂ^n; ℓ_q^n)} / ‖P_n (∇u_n)‖_{L^p (ℂ^n; ℓ_q^n)} → ∞` as `n → ∞` (12).

Proof: the paper's. `Q_n (∇u_n) = ∂̄u_n` and `P_n (∇u_n) = ∂u_n` are computed explicitly
(`twoByM_wirtQ_jac`, `twoByM_wirtP_jac`); with `μ = c⁻¹ |f|^p dA` (`twoByM_prob`), the change of
variables `ℝ^{2n} ≅ ℂ^n` and the product structure give
`‖Q_n (∇u_n)‖_{L^p}^p = c^n n^{p/q} E (n⁻¹ Σ_{j<n} |∂̄f/f (Z_j)|^q)^{p/q}` for an i.i.d. sequence
`Z_j ∼ μ` (`twoByM_P`, `twoByM_integral_reduce`), and the same with `∂f/f` for `P_n`. Since
`E |∂̄f/f|^q = ∞` for `q ≥ p + 2` (the radial integrand behaves like `r^{p+1−q}` at `0`,
`twoByM_lintegral_aGQ_eq_top`), the law of large numbers applied to the truncations
`min (|∂̄f/f|^q, M)` and Fatou's lemma make the numerator tend to `∞`
(`twoByM_numerator_tendsto`); Jensen's inequality (`p/q < 1`) bounds the denominator by
`(E |∂f/f|^q)^{p/q} < ∞` (`twoByM_denominator_le`). The paper also notes, with Fatou's lemma, that
the denominator converges; only the Jensen bound is needed and proved. -/
theorem lemma4_2 {p q : ℝ} (hp : 1 < p) (hpq : p + 2 ≤ q) :
    Tendsto (fun n : ℕ =>
        eLpNorm (fun ξ => lqNorm q (wirtQ (jac (testU n) ξ))) (ENNReal.ofReal p) volume /
          eLpNorm (fun ξ => lqNorm q (wirtP (jac (testU n) ξ))) (ENNReal.ofReal p) volume)
      atTop (𝓝 ⊤) := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < q := by linarith
  have hs0 : 0 < p / q := div_pos hp0 hq
  have hP := twoByM_isProbabilityMeasure hp0
  -- `K = (E |∂f/f|^q)^{p/q} < ∞` bounds the denominators
  set K := (∫⁻ z, ENNReal.ofReal (twoByM_GP q z) ∂twoByM_prob p) ^ (p / q)
  have hK : K ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg hs0.le ?_
    rw [twoByM_lintegral_prob (twoByM_measurable_GP q).ennreal_ofReal]
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (twoByM_c_ne_zero p)) ?_
    have := (twoByM_integrable_aGP hp0 hq).lintegral_lt_top
    refine ne_of_lt (lt_of_eq_of_lt (lintegral_congr fun z => ?_) this)
    rw [ENNReal.ofReal_mul (twoByM_a_nonneg p z)]
  set N : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ENNReal.ofReal
    (((∑ j ∈ Finset.range n, twoByM_GQ q (ω j)) / n) ^ (p / q)) ∂twoByM_P p
  set D : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ENNReal.ofReal
    (((∑ j ∈ Finset.range n, twoByM_GP q (ω j)) / n) ^ (p / q)) ∂twoByM_P p
  -- the ratio is `(N_n / D_n)^{1/p}`
  have hratio : ∀ n : ℕ, 0 < n →
      eLpNorm (fun ξ => lqNorm q (wirtQ (jac (testU n) ξ))) (ENNReal.ofReal p) volume /
        eLpNorm (fun ξ => lqNorm q (wirtP (jac (testU n) ξ))) (ENNReal.ofReal p) volume =
      (N n / D n) ^ (1 / p) := by
    intro n hn
    rw [twoByM_eLpNorm_eq_rpow hp0 (twoByM_continuous_lqQ hq) fun ξ => twoByM_lqNorm_nonneg q _,
      twoByM_eLpNorm_eq_rpow hp0 (twoByM_continuous_lqP hq) fun ξ => twoByM_lqNorm_nonneg q _,
      ← ENNReal.div_rpow_of_nonneg _ _ (by positivity)]
    congr 1
    rw [twoByM_integral_reduce hn hp0 (twoByM_measurable_GQ q) (twoByM_GQ_nonneg q)
        ((twoByM_ae_blockZ_ne_zero n).mono fun ξ hξ => twoByM_lqQ_eq hq ξ hξ),
      twoByM_integral_reduce hn hp0 (twoByM_measurable_GP q) (twoByM_GP_nonneg q)
        (Eventually.of_forall fun ξ => twoByM_lqP_eq hq ξ),
      ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ (twoByM_c_ne_zero p))
        (ENNReal.pow_ne_top (twoByM_c_lt_top hp0).ne),
      ENNReal.mul_div_mul_left _ _ (by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) _) ENNReal.ofReal_ne_top]
  -- `N_n / D_n ≥ N_n / K → ∞`
  have hlow : Tendsto (fun n => (N n / K) ^ (1 / p)) atTop (𝓝 ⊤) := by
    have h1 : Tendsto (fun n => N n / K) atTop (𝓝 ⊤) := by
      have := ENNReal.Tendsto.div_const (b := K) (twoByM_numerator_tendsto hp0 hpq)
        (Or.inl ENNReal.top_ne_zero)
      rwa [ENNReal.top_div_of_ne_top hK] at this
    have h2 := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto ⊤).comp h1
    rwa [ENNReal.top_rpow_of_pos (by positivity)] at h2
  refine tendsto_nhds_top_mono hlow ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hratio n hn]
  refine ENNReal.rpow_le_rpow (ENNReal.div_le_div_left ?_ _) (by positivity)
  exact twoByM_denominator_le hp0 (by linarith) hn

/-- The integrand of Proposition 4.2: `f_n (A) = 5⁴ ‖P_n (A)‖_{ℓ_6}^3 − ‖Q_n (A)‖_{ℓ_6}^3`. -/
noncomputable def explicitF (n : ℕ) (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) : ℝ :=
  5 ^ 4 * lqNorm 6 (wirtP A) ^ 3 - lqNorm 6 (wirtQ A) ^ 3

/-- Burkholder's scalar function for the exponent `6` (proof of Proposition 4.2):
`u (a, b) = α (|b| − 5 |a|) (|a| + |b|)^5`, `α = 6 (5/6)^5 = 5^5 / 6^4`. -/
noncomputable def burkholderU (a b : ℂ) : ℝ :=
  5 ^ 5 / 6 ^ 4 * (‖b‖ - 5 * ‖a‖) * (‖a‖ + ‖b‖) ^ 5

/-- `burkholderU` is the function of `External.Burkholder.ScalarFunction`. -/
theorem burkholderU_eq : burkholderU = External.Burkholder.u6 := rfl

/-- `R (x, y) = Σ_j (u (x_j, y_j) + 2 · 5^6 |x_j|^6)` (proof of Proposition 4.2). -/
noncomputable def burkholderR {n : ℕ} (x y : Fin n → ℂ) : ℝ :=
  ∑ j, (burkholderU (x j) (y j) + 2 * 5 ^ 6 * ‖x j‖ ^ 6)

/-- `B (x) = ‖x‖_{ℓ_6}^6` (proof of Proposition 4.2). -/
noncomputable def burkholderB {n : ℕ} (x : Fin n → ℂ) : ℝ :=
  ∑ j, ‖x j‖ ^ 6

/-- (15): `U (x, y) = R (x, y)^{1/2} − 5⁴ B (x)^{1/2}`. -/
noncomputable def zigzagU {n : ℕ} (x y : Fin n → ℂ) : ℝ :=
  √(burkholderR x y) - 5 ^ 4 * √(burkholderB x)

/-- The rank-one convex minorant of the proof of Proposition 4.2:
`g_n (A) = −U (conj (P_n (A)), Q_n (A))`. -/
noncomputable def explicitG (n : ℕ) (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) : ℝ :=
  -zigzagU (fun j => conj (wirtP A j)) (wirtQ A)

/-! ### Proposition 4.2: the explicit rank-one convex minorant

The zig-zag concavity of `U` (TeX 1286–1352) is proved by the paper's mollification. For
`b (t) = B (x + t h)` and `r (t) = R (x + t h, y + t ε h)`, and a mollifier
`ρ_η = (ContDiffBump.ofRadius η).normed volume` on `ℝ`, the mollifications
`b_η = ρ_η ⋆ b`, `r_η = ρ_η ⋆ r` satisfy (17) (`twoByM_eq17`); `b_η^{1/6}` is convex by Minkowski's
inequality (`twoByM_convexOn_mollify_Bq`) and `b_η > 0` (`twoByM_mollify_Bq_pos`), so (18) holds
for `b_η` (`twoByM_eq18`); the paper's computation makes `√r_η − 5⁴ √b_η` concave
(`twoByM_sqrt_concave`), and the limit `η ↓ 0` (`twoByM_concaveOn_of_mollify`) gives the concavity
of `U (x + t h, y + t ε h)` (`twoByM_zigzag`). The same steps with the exponent `q` give the
zig-zag concavity of Remark 4.5 (`twoByM_zigzagq`). -/

/-- `B_q (x) = ‖x‖_{ℓ_q}^q`: `B_6` is the `B` of the proof of Proposition 4.2 (TeX 1246,
`twoByM_burkholderB_eq`), and `B_q` that of Remark 4.5. -/
noncomputable def twoByM_Bq {n : ℕ} (q : ℝ) (x : Fin n → ℂ) : ℝ :=
  ∑ j, ‖x j‖ ^ q

theorem twoByM_Bq_nonneg {n : ℕ} (q : ℝ) (x : Fin n → ℂ) : 0 ≤ twoByM_Bq q x :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- `‖z‖_{ℓ_q}^p = B_q (z)^{p/q}`. -/
theorem twoByM_lqNorm_rpow {n : ℕ} {q : ℝ} (p : ℝ) (z : Fin n → ℂ) :
    lqNorm q z ^ p = twoByM_Bq q z ^ (p / q) := by
  rw [lqNorm, twoByM_Bq, ← Real.rpow_mul (Finset.sum_nonneg fun j _ => by positivity)]
  congr 1; ring

/-- `B = B_6`. -/
theorem twoByM_burkholderB_eq {n : ℕ} (z : Fin n → ℂ) : burkholderB z = twoByM_Bq 6 z := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem twoByM_lqNorm_eq_norm {n : ℕ} (q : ℝ) (hq : 0 < q) (z : Fin n → ℂ) :
    lqNorm q z = ‖WithLp.toLp (ENNReal.ofReal q) z‖ := by
  rw [PiLp.norm_eq_sum (by rw [ENNReal.toReal_ofReal hq.le]; exact hq), ENNReal.toReal_ofReal hq.le]
  rfl

/-- The first two derivatives of `√g` for a positive twice differentiable `g`. -/
theorem twoByM_sqrt_hasDerivAt {g g' g'' : ℝ → ℝ} (hg0 : ∀ t, 0 < g t)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t) (t : ℝ) :
    HasDerivAt (fun t => √(g t)) (g' t / (2 * √(g t))) t ∧
      HasDerivAt (fun t => g' t / (2 * √(g t)))
        ((g'' t - 2 * (g' t / (2 * √(g t))) ^ 2) / (2 * √(g t))) t := by
  have h1 : ∀ t, HasDerivAt (fun t => √(g t)) (g' t / (2 * √(g t))) t := fun t =>
    (hg t).sqrt (hg0 t).ne'
  refine ⟨h1 t, ?_⟩
  have hs : 0 < √(g t) := Real.sqrt_pos.2 (hg0 t)
  have hs2 : √(g t) ^ 2 = g t := Real.sq_sqrt (hg0 t).le
  convert (hg' t).div ((h1 t).const_mul 2) (by positivity) using 1
  field_simp

/-- Inequality (18) of the proof of Proposition 4.2 (TeX 1317–1326), for a positive twice
differentiable `b` with `b^{1/6}` convex: differentiating `b^{1/6}` twice gives
`5 b'² ≤ 6 b b''`. -/
theorem twoByM_eq18 {b b' b'' : ℝ → ℝ} (hb0 : ∀ t, 0 < b t) (hb : ∀ t, HasDerivAt b (b' t) t)
    (hb' : ∀ t, HasDerivAt b' (b'' t) t)
    (hconv : ConvexOn ℝ Set.univ fun t => b t ^ (1 / 6 : ℝ)) (t : ℝ) :
    5 * b' t ^ 2 ≤ 6 * b t * b'' t := by
  set c' : ℝ → ℝ := fun t => 1 / 6 * b t ^ (1 / 6 - 1 : ℝ) * b' t
  set c'' : ℝ → ℝ := fun t => 1 / 6 * ((1 / 6 - 1) * b t ^ (1 / 6 - 1 - 1 : ℝ) * b' t * b' t +
    b t ^ (1 / 6 - 1 : ℝ) * b'' t)
  have hc : ∀ t, HasDerivAt (fun t => b t ^ (1 / 6 : ℝ)) (c' t) t := fun t => by
    convert (hb t).rpow_const (p := 1 / 6) (Or.inl (hb0 t).ne') using 1
    simp only [c']; ring
  have hc' : ∀ t, HasDerivAt c' (c'' t) t := fun t => by
    have := (((hb t).rpow_const (p := 1 / 6 - 1) (Or.inl (hb0 t).ne')).const_mul (1 / 6)).mul
      (hb' t)
    convert this using 1
    simp only [c'']; ring
  -- `c'' ≥ 0`, since `c'` is the derivative of a convex function
  have hmono : Monotone c' := by
    have hd : deriv (fun t => b t ^ (1 / 6 : ℝ)) = c' := funext fun t => (hc t).deriv
    have := hconv.monotoneOn_deriv fun t _ => (hc t).differentiableAt
    rw [hd] at this
    exact monotoneOn_univ.1 this
  have hc''0 : 0 ≤ c'' t := by
    rw [← (hc' t).deriv]; exact hmono.deriv_nonneg
  have hbt := hb0 t
  have hsplit : b t ^ (1 / 6 - 1 : ℝ) = b t ^ (1 / 6 - 1 - 1 : ℝ) * b t := by
    conv_lhs => rw [show (1 / 6 - 1 : ℝ) = (1 / 6 - 1 - 1) + 1 by ring]
    rw [Real.rpow_add hbt, Real.rpow_one]
  have hpos : 0 < b t ^ (1 / 6 - 1 - 1 : ℝ) := Real.rpow_pos_of_pos hbt _
  have : 0 ≤ b t ^ (1 / 6 - 1 - 1 : ℝ) * (6 * b t * b'' t - 5 * b' t ^ 2) := by
    have : c'' t = b t ^ (1 / 6 - 1 - 1 : ℝ) * (6 * b t * b'' t - 5 * b' t ^ 2) / 36 := by
      simp only [c'', hsplit]; ring
    linarith
  have := (mul_nonneg_iff_of_pos_left hpos).1 this
  linarith

/-- The computation of the proof of Proposition 4.2 (TeX 1328–1346), for twice differentiable
`r` and `b > 0` with (17) `r ≥ 5⁶ b`, `r'' ≤ 2·5⁶ b''` and (18) `5 b'² ≤ 6 b b''`:
`(√r)'' = r'' / (2 √r) − r'² / (4 r^{3/2}) ≤ 2·5⁶ b'' / (2·5³ √b) = 5³ b'' / √b ≤ 5⁴ (√b)''`
(the first inequality uses `r'' ≤ 2·5⁶ b''`, `b'' ≥ 0` and `√r ≥ 5³ √b`; the last is (18) in the
form `b'' / √b ≤ 5 (√b)''`), so `√r − 5⁴ √b` has a nonpositive second derivative and is concave.
In the proof of Proposition 4.2 it is applied to `r_η`, `b_η`. -/
theorem twoByM_sqrt_concave {r r' r'' b b' b'' : ℝ → ℝ}
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : ∀ t, HasDerivAt r' (r'' t) t)
    (hb0 : ∀ t, 0 < b t) (hb : ∀ t, HasDerivAt b (b' t) t) (hb' : ∀ t, HasDerivAt b' (b'' t) t)
    (h17 : ∀ t, 5 ^ 6 * b t ≤ r t) (h17' : ∀ t, r'' t ≤ 2 * 5 ^ 6 * b'' t)
    (h18 : ∀ t, 5 * b' t ^ 2 ≤ 6 * b t * b'' t) :
    ConcaveOn ℝ Set.univ fun t => √(r t) - 5 ^ 4 * √(b t) := by
  have hr0 : ∀ t, 0 < r t := fun t => by have := hb0 t; linarith [h17 t]
  set F' : ℝ → ℝ := fun t => r' t / (2 * √(r t)) - 5 ^ 4 * (b' t / (2 * √(b t)))
  set F'' : ℝ → ℝ := fun t => (r'' t - 2 * (r' t / (2 * √(r t))) ^ 2) / (2 * √(r t)) -
    5 ^ 4 * ((b'' t - 2 * (b' t / (2 * √(b t))) ^ 2) / (2 * √(b t)))
  have hF : ∀ t, HasDerivAt (fun t => √(r t) - 5 ^ 4 * √(b t)) (F' t) t := fun t =>
    (twoByM_sqrt_hasDerivAt hr0 hr hr' t).1.sub
      ((twoByM_sqrt_hasDerivAt hb0 hb hb' t).1.const_mul _)
  have hF' : ∀ t, HasDerivAt F' (F'' t) t := fun t =>
    (twoByM_sqrt_hasDerivAt hr0 hr hr' t).2.sub
      ((twoByM_sqrt_hasDerivAt hb0 hb hb' t).2.const_mul _)
  -- `F'' ≤ 0`: the paper's chain `(√r)'' ≤ 5³ b'' / √b ≤ 5⁴ (√b)''`
  have hF''0 : ∀ t, F'' t ≤ 0 := fun t => by
    have hbt := hb0 t
    have hβ : 0 < √(b t) := Real.sqrt_pos.2 hbt
    have hβ2 : √(b t) ^ 2 = b t := Real.sq_sqrt hbt.le
    have hs : 0 < √(r t) := Real.sqrt_pos.2 (hr0 t)
    -- `√r ≥ 5³ √b`, from `r ≥ 5⁶ b`
    have hsβ : 125 * √(b t) ≤ √(r t) := by
      rw [show (125 : ℝ) = √(5 ^ 6) by
        rw [show (5 : ℝ) ^ 6 = 125 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
        ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (h17 t)
    have hb''0 : 0 ≤ b'' t := by
      have := h18 t
      nlinarith [sq_nonneg (b' t)]
    have e1 : (r'' t - 2 * (r' t / (2 * √(r t))) ^ 2) / (2 * √(r t)) ≤ 125 * b'' t / √(b t) := by
      calc (r'' t - 2 * (r' t / (2 * √(r t))) ^ 2) / (2 * √(r t)) ≤ r'' t / (2 * √(r t)) := by
            gcongr; nlinarith [sq_nonneg (r' t / (2 * √(r t)))]
        _ ≤ 2 * 5 ^ 6 * b'' t / (2 * √(r t)) := by gcongr; exact h17' t
        _ = 5 ^ 6 * b'' t / √(r t) := by field_simp
        _ ≤ 5 ^ 6 * b'' t / (125 * √(b t)) := by gcongr
        _ = 125 * b'' t / √(b t) := by field_simp; ring
    -- `5³ b'' / √b ≤ 5⁴ (√b)''`, that is (18)
    have e2 : 125 * b'' t / √(b t) ≤
        5 ^ 4 * ((b'' t - 2 * (b' t / (2 * √(b t))) ^ 2) / (2 * √(b t))) := by
      rw [div_le_iff₀ hβ]
      have : 5 ^ 4 * ((b'' t - 2 * (b' t / (2 * √(b t))) ^ 2) / (2 * √(b t))) * √(b t) =
          5 ^ 4 * (b'' t - b' t ^ 2 / (2 * b t)) / 2 := by
        field_simp; rw [hβ2]; ring
      rw [this]
      have h18t := h18 t
      have : b' t ^ 2 / (2 * b t) ≤ 3 / 5 * b'' t := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      nlinarith
    simp only [F'']
    linarith
  exact concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
    (fun t _ => (hF t).continuousAt.continuousWithinAt) (fun t _ => (hF t).hasDerivWithinAt)
    (fun t _ => (hF' t).hasDerivWithinAt) fun t _ => hF''0 t

/-! #### The mollification of the zig-zag step (TeX 1299–1351)

`ρ_η = φ.normed volume` for a bump `φ : ContDiffBump (0 : ℝ)` (the paper's nonnegative smooth
mollifier; for the limit `η ↓ 0`, `φ = ContDiffBump.ofRadius η`), and `g_η = ρ_η ⋆ g` the mollification
(`Morrey.Common.Basic.Analysis.Calculus.BumpFunction.Mollify`). -/

section Mollify

open ContinuousLinearMap
open scoped Convolution

/-- A smooth function on `ℝ` has its first two derivatives everywhere. -/
theorem twoByM_hasDerivAt_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (t : ℝ) : HasDerivAt f (deriv f t) t ∧ HasDerivAt (deriv f) (deriv (deriv f) t) t :=
  ⟨(hf.differentiable (by simp)).differentiableAt.hasDerivAt,
    ((contDiff_infty_iff_deriv.1 hf).2.differentiable (by simp)).differentiableAt.hasDerivAt⟩

/-- (17) (`eq:mollified-inequalities`, TeX 1296–1307): for continuous `r`, `b` with `r − 2 c b`
concave and `r ≥ c b`, the mollifications satisfy `r_η ≥ c b_η` (the mollification is monotone)
and `r_η'' ≤ 2 c b_η''`: `(r − 2 c b)_η = r_η − 2 c b_η` is smooth and concave (the mollification
of a concave function is concave), so its derivative is antitone and its second derivative is
`≤ 0`. -/
theorem twoByM_eq17 {r b : ℝ → ℝ} {c : ℝ} (hr : Continuous r) (hb : Continuous b)
    (hκ : ConcaveOn ℝ Set.univ fun t => r t - 2 * c * b t) (hrb : ∀ t, c * b t ≤ r t)
    (φ : ContDiffBump (0 : ℝ)) (t : ℝ) :
    c * (φ.normed volume ⋆[lsmul ℝ ℝ, volume] b) t ≤
        (φ.normed volume ⋆[lsmul ℝ ℝ, volume] r) t ∧
      deriv (deriv (φ.normed volume ⋆[lsmul ℝ ℝ, volume] r)) t ≤
        2 * c * deriv (deriv (φ.normed volume ⋆[lsmul ℝ ℝ, volume] b)) t := by
  set rη := φ.normed volume ⋆[lsmul ℝ ℝ, volume] r
  set bη := φ.normed volume ⋆[lsmul ℝ ℝ, volume] b
  constructor
  · have := φ.normed_convolution_mono (μ := volume) (g := fun t => c * b t)
      (continuous_const.mul hb).locallyIntegrable hr.locallyIntegrable hrb t
    rwa [φ.normed_convolution_const_mul] at this
  -- `κ_η = (r − 2 c b)_η = r_η − 2 c b_η` is concave
  have hκη : (φ.normed volume ⋆[lsmul ℝ ℝ, volume] fun t => r t - 2 * c * b t) =
      fun t => rη t - 2 * c * bη t := by
    have := φ.normed_convolution_sub (μ := volume) (g' := fun t => 2 * c * b t)
      hr.locallyIntegrable (continuous_const.mul hb).locallyIntegrable
    rw [φ.normed_convolution_const_mul] at this
    exact this
  have hconc : ConcaveOn ℝ Set.univ fun t => rη t - 2 * c * bη t := by
    rw [← hκη]
    exact φ.normed_convolution_concaveOn (hr.sub (continuous_const.mul hb)) hκ
  have hR := twoByM_hasDerivAt_deriv
    (φ.contDiff_normed_convolution (μ := volume) hr.locallyIntegrable)
  have hB := twoByM_hasDerivAt_deriv
    (φ.contDiff_normed_convolution (μ := volume) hb.locallyIntegrable)
  have hd : ∀ s, HasDerivAt (fun t => rη t - 2 * c * bη t) (deriv rη s - 2 * c * deriv bη s) s :=
    fun s => (hR s).1.sub ((hB s).1.const_mul _)
  -- the derivative of the concave `κ_η` is antitone, so `κ_η'' ≤ 0`
  have hanti : Antitone fun s => deriv rη s - 2 * c * deriv bη s := by
    have := hconc.antitoneOn_deriv fun s _ => (hd s).differentiableAt
    rw [show deriv (fun t => rη t - 2 * c * bη t) = fun s => deriv rη s - 2 * c * deriv bη s from
      funext fun s => (hd s).deriv] at this
    exact antitoneOn_univ.1 this
  have h2 := hanti.deriv_nonpos (x := t)
  have h3 : HasDerivAt (fun s => deriv rη s - 2 * c * deriv bη s)
      (deriv (deriv rη) t - 2 * c * deriv (deriv bη) t) t :=
    (hR t).2.sub ((hB t).2.const_mul (2 * c))
  rw [h3.deriv] at h2
  linarith

/-- `t ↦ ‖a + t v‖` is convex. -/
theorem twoByM_convexOn_norm_line {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (a v : E) : ConvexOn ℝ Set.univ fun t : ℝ => ‖a + t • v‖ := by
  refine ⟨convex_univ, fun t₁ _ t₂ _ θ φ hθ hφ hsum => ?_⟩
  obtain rfl : φ = 1 - θ := by linarith
  simp only [smul_eq_mul]
  calc ‖a + (θ * t₁ + (1 - θ) * t₂) • v‖ = ‖θ • (a + t₁ • v) + (1 - θ) • (a + t₂ • v)‖ := by
        congr 1; module
    _ ≤ θ * ‖a + t₁ • v‖ + (1 - θ) * ‖a + t₂ • v‖ := by
      refine (norm_add_le _ _).trans_eq ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hθ, Real.norm_of_nonneg hφ]

/-- The convexity of `b_η^{1/q}`, `b (t) = B_q (x + t h)`, `q ≥ 1` (TeX 1308–1317 for `q = 6`):
`b_η (t) = ∫ ρ_η (s) ‖x + (t − s) h‖_{ℓ_q}^q ds` is the `q`-th power of the `L^q (ℝ; ℓ_q)` norm of
`s ↦ ρ_η (s)^{1/q} (x + (t − s) h) = u (s) + t k (s)`, with `u (s) = ρ_η (s)^{1/q} (x − s h)` and
`k (s) = ρ_η (s)^{1/q} h`; by Minkowski's inequality (the triangle inequality of the norm of
`L^q`) and its homogeneity, `t ↦ ‖u + t k‖_{L^q} = b_η (t)^{1/q}` is convex. -/
theorem twoByM_convexOn_mollify_Bq {q : ℝ} (hq : 1 ≤ q) {n : ℕ} (x h : Fin n → ℂ)
    (φ : ContDiffBump (0 : ℝ)) :
    ConvexOn ℝ Set.univ fun t => (φ.normed volume ⋆[lsmul ℝ ℝ, volume]
      fun t : ℝ => twoByM_Bq q fun j => x j + t * h j) t ^ (1 / q) := by
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨one_le_ofReal_of_one_le hq⟩
  have hq0 : 0 < q := by linarith
  set ρ := φ.normed volume with hρ_def
  -- the weight `w = ρ_η^{1/q}`, continuous with compact support
  set w : ℝ → ℝ := fun s => ρ s ^ (1 / q) with hw_def
  have hw : Continuous w := φ.continuous_normed.rpow_const fun _ => Or.inr (by positivity)
  have hwc : HasCompactSupport w :=
    φ.hasCompactSupport_normed.comp_left (g := fun z : ℝ => z ^ (1 / q))
      (Real.zero_rpow (by positivity))
  set u : ℝ → PiLp (ENNReal.ofReal q) (fun _ : Fin n => ℂ) := fun s =>
    w s • (WithLp.toLp (ENNReal.ofReal q) x - s • WithLp.toLp (ENNReal.ofReal q) h) with hu_def
  set k : ℝ → PiLp (ENNReal.ofReal q) (fun _ : Fin n => ℂ) := fun s =>
    w s • WithLp.toLp (ENNReal.ofReal q) h with hk_def
  have hu : MemLp u (ENNReal.ofReal q) volume :=
    (hw.smul (continuous_const.sub (continuous_id.smul continuous_const))).memLp_of_hasCompactSupport
      (hwc.smul_right (f' := fun s : ℝ =>
        WithLp.toLp (ENNReal.ofReal q) x - s • WithLp.toLp (ENNReal.ofReal q) h))
  have hk : MemLp k (ENNReal.ofReal q) volume :=
    (hw.smul continuous_const).memLp_of_hasCompactSupport
      (hwc.smul_right (f' := fun _ : ℝ => WithLp.toLp (ENNReal.ofReal q) h))
  -- `b_η (t)^{1/q} = ‖u + t k‖_{L^q}`
  have hval : ∀ t, (ρ ⋆[lsmul ℝ ℝ, volume]
      fun t : ℝ => twoByM_Bq q fun j => x j + t * h j) t ^ (1 / q) =
        ‖hu.toLp u + t • hk.toLp k‖ := fun t => by
    have hmem := hu.add (hk.const_smul t)
    have h1 : ‖hu.toLp u + t • hk.toLp k‖ =
        (eLpNorm (u + t • k) (ENNReal.ofReal q) volume).toReal := by
      rw [← MemLp.toLp_const_smul, ← MemLp.toLp_add, Lp.norm_toLp]
    have h2 := hmem.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.2 hq0).ne'
      ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hq0.le] at h2
    rw [h1, h2, ENNReal.toReal_ofReal (by positivity), φ.normed_convolution_apply, one_div]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    -- `ρ_η (s) B_q (x + (t − s) h) = ‖ρ_η (s)^{1/q} (x + (t − s) h)‖^q`
    have hρs : 0 ≤ ρ s := φ.nonneg_normed s
    have hws : 0 ≤ w s := Real.rpow_nonneg hρs _
    have hV : WithLp.toLp (ENNReal.ofReal q) (fun j => x j + ((t - s : ℝ) : ℂ) * h j) =
        WithLp.toLp (ENNReal.ofReal q) x + (t - s) • WithLp.toLp (ENNReal.ofReal q) h := by
      rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
      congr 1
    have e : (u + t • k) s = w s • WithLp.toLp (ENNReal.ofReal q)
        (fun j => x j + ((t - s : ℝ) : ℂ) * h j) := by
      rw [hV]
      simp only [Pi.add_apply, Pi.smul_apply, u, k]
      module
    have hw' : w s ^ q = ρ s := by
      show (ρ s ^ (1 / q)) ^ q = ρ s
      rw [← Real.rpow_mul hρs, one_div_mul_cancel hq0.ne', Real.rpow_one]
    show ρ s * twoByM_Bq q (fun j => x j + ((t - s : ℝ) : ℂ) * h j) = ‖(u + t • k) s‖ ^ q
    rw [e, norm_smul, Real.norm_of_nonneg hws, Real.mul_rpow hws (norm_nonneg _), hw',
      ← twoByM_lqNorm_eq_norm q hq0, twoByM_lqNorm_rpow, div_self hq0.ne', Real.rpow_one]
  exact (twoByM_convexOn_norm_line (hu.toLp u) (hk.toLp k)).congr fun t _ => (hval t).symm

/-- `t ↦ B_q (x + t h)` is continuous. -/
theorem twoByM_continuous_Bq_line {q : ℝ} (hq : 0 ≤ q) {n : ℕ} (x h : Fin n → ℂ) :
    Continuous fun t : ℝ => twoByM_Bq q fun j => x j + t * h j :=
  continuous_finsetSum _ fun _ _ =>
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).norm.rpow_const
      fun _ => Or.inr hq

/-- `b_η > 0` (TeX 1318), unless `x = h = 0` (TeX 1294): `b (t) = B_q (x + t h) ≥ 0` is continuous
and positive somewhere in every interval, since `x + t h` vanishes for at most one `t`; the
mollification of such a function is positive. -/
theorem twoByM_mollify_Bq_pos {q : ℝ} (hq : 0 < q) {n : ℕ} {x h : Fin n → ℂ}
    (hxh : ¬(x = 0 ∧ h = 0)) (φ : ContDiffBump (0 : ℝ)) (t : ℝ) :
    0 < (φ.normed volume ⋆[lsmul ℝ ℝ, volume]
      fun t : ℝ => twoByM_Bq q fun j => x j + t * h j) t := by
  -- a point `t'` near `t` with `x + t' h ≠ 0`
  obtain ⟨t', ht', j, hj⟩ : ∃ t' ∈ Metric.ball t φ.rOut, ∃ j, x j + t' * h j ≠ 0 := by
    by_cases h0 : ∃ j, x j + t * h j ≠ 0
    · exact ⟨t, Metric.mem_ball_self φ.rOut_pos, h0⟩
    push Not at h0
    have hh : h ≠ 0 := fun hh => hxh ⟨funext fun j => by simpa [hh] using h0 j, hh⟩
    obtain ⟨j, hj⟩ : ∃ j, h j ≠ 0 := by
      by_contra hc; push Not at hc; exact hh (funext hc)
    have hδ := φ.rOut_pos
    refine ⟨t + φ.rOut / 2, ?_, j, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, show t + φ.rOut / 2 - t = φ.rOut / 2 by ring,
        abs_of_pos (by linarith)]
      linarith
    · have e : x j + ((t + φ.rOut / 2 : ℝ) : ℂ) * h j = ((φ.rOut / 2 : ℝ) : ℂ) * h j := by
        have := h0 j
        push_cast
        linear_combination this
      rw [e]
      exact mul_ne_zero (Complex.ofReal_ne_zero.2 (by linarith)) hj
  refine φ.normed_convolution_pos (μ := volume) (twoByM_continuous_Bq_line hq.le x h)
    (fun s => twoByM_Bq_nonneg q _) ht' ?_
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos (norm_pos_iff.2 hj) q)
    (Finset.single_le_sum (f := fun j => ‖x j + (t' : ℂ) * h j‖ ^ q) (fun j _ => by positivity)
      (Finset.mem_univ j))

/-- The limit `η ↓ 0` (TeX 1348–1351): for continuous `r`, `b` and `Φ`, if
`t ↦ Φ (r_η (t), b_η (t))` is concave for every mollifier, so is `t ↦ Φ (r (t), b (t))`. With
`η = 1/(k + 1)`, `r_η → r` and `b_η → b` pointwise (the paper has locally uniform convergence;
pointwise convergence suffices), and a pointwise limit of concave functions is concave. -/
theorem twoByM_concaveOn_of_mollify {r b : ℝ → ℝ} (hr : Continuous r) (hb : Continuous b)
    {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous fun z : ℝ × ℝ => Φ z.1 z.2)
    (h : ∀ φ : ContDiffBump (0 : ℝ), ConcaveOn ℝ Set.univ fun t =>
      Φ ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] r) t)
        ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] b) t)) :
    ConcaveOn ℝ Set.univ fun t => Φ (r t) (b t) := by
  set φ : ℕ → ContDiffBump (0 : ℝ) := fun k =>
    ContDiffBump.ofRadius (Nat.one_div_pos_of_nat : (0 : ℝ) < 1 / ((k : ℝ) + 1))
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine External.Burkholder.concaveOn_univ_of_tendsto (fun k => h (φ k)) fun t => ?_
  exact (hΦ.tendsto (r t, b t)).comp
    ((ContDiffBump.tendsto_normed_convolution (μ := volume) hφ hr t).prodMk_nhds
      (ContDiffBump.tendsto_normed_convolution (μ := volume) hφ hb t))

end Mollify

/-- A finite sum of concave functions is concave. -/
theorem twoByM_concaveOn_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ s, ConcaveOn ℝ Set.univ (F i)) :
    ConcaveOn ℝ Set.univ fun t => ∑ i ∈ s, F i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using concaveOn_const (c := (0 : ℝ)) convex_univ
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem twoByM_continuous_zigzagU (n : ℕ) :
    Continuous fun p : (Fin n → ℂ) × (Fin n → ℂ) => zigzagU p.1 p.2 := by
  unfold zigzagU burkholderR burkholderB burkholderU
  fun_prop

open ContinuousLinearMap in
open scoped Convolution in
/-- **Zig-zag concavity of `U`** (proof of Proposition 4.2, TeX 1286–1352): for `x, y, h ∈ ℂ^n`
and `|ε| ≤ 1`, `t ↦ U (x + t h, y + t ε h)` is concave.

Proof, the paper's. If `x = h = 0` the function is constant. Otherwise, with `b (t) = B (x + t h)`
and `r (t) = R (x + t h, y + t ε h)`: `r − 2·5⁶ b = Σ_j u (x_j + t h_j, y_j + t ε h_j)` is concave
by (14), and `r ≥ 5⁶ b` by (13). For every mollifier `ρ_η`, `r_η` and `b_η` satisfy (17)
(`twoByM_eq17`), `b_η^{1/6}` is convex (`twoByM_convexOn_mollify_Bq`) and `b_η > 0`
(`twoByM_mollify_Bq_pos`), so (18) holds for `b_η` (`twoByM_eq18`), and the paper's computation
makes `√r_η − 5⁴ √b_η` concave (`twoByM_sqrt_concave`). Letting `η ↓ 0`
(`twoByM_concaveOn_of_mollify`) gives the concavity of `√r − 5⁴ √b = U (x + t h, y + t ε h)`. -/
theorem twoByM_zigzag {n : ℕ}
    (x y h : Fin n → ℂ) {ε : ℂ} (hε : ‖ε‖ ≤ 1) :
    ConcaveOn ℝ Set.univ fun t : ℝ =>
      zigzagU (fun j => x j + t * h j) (fun j => y j + t * ε * h j) := by
  by_cases hxh : x = 0 ∧ h = 0
  · obtain ⟨rfl, rfl⟩ := hxh
    have : (fun t : ℝ => zigzagU (fun j => (0 : Fin n → ℂ) j + (t : ℂ) * (0 : Fin n → ℂ) j)
        (fun j => y j + (t : ℂ) * ε * (0 : Fin n → ℂ) j)) = fun _ => zigzagU 0 y := by
      funext t
      congr 1 <;> funext j <;> simp
    rw [this]
    exact concaveOn_const _ convex_univ
  -- `b (t) = B (x + t h) = B_6 (x + t h)` and `r (t) = R (x + t h, y + t ε h)`
  set b : ℝ → ℝ := fun t => twoByM_Bq 6 fun j => x j + t * h j with hb_def
  set r : ℝ → ℝ := fun t =>
    burkholderR (fun j => x j + t * h j) (fun j => y j + t * ε * h j) with hr_def
  have hb : Continuous b := twoByM_continuous_Bq_line (by norm_num) x h
  have hr : Continuous r := by
    simp only [hr_def, burkholderR, burkholderU]
    fun_prop
  -- `r − 2·5⁶ b = Σ_j u (x_j + t h_j, y_j + t ε h_j)`
  have hrκ : ∀ t, r t - 2 * 5 ^ 6 * b t =
      ∑ j, burkholderU (x j + t * h j) (y j + t * ε * h j) := fun t => by
    simp only [hr_def, hb_def, ← twoByM_burkholderB_eq, burkholderR, burkholderB,
      Finset.sum_add_distrib, Finset.mul_sum]
    ring
  -- (14): `r − 2·5⁶ b` is concave
  have hκ : ConcaveOn ℝ Set.univ fun t => r t - 2 * 5 ^ 6 * b t := by
    simp only [hrκ]
    exact twoByM_concaveOn_sum _ fun j _ =>
      External.Burkholder.scalarFunction_holds.2 (x j) (y j) (h j) ε hε
  -- (13): `r ≥ 5⁶ b`
  have hrb : ∀ t, 5 ^ 6 * b t ≤ r t := fun t => by
    have : -(5 ^ 6 * b t) ≤ r t - 2 * 5 ^ 6 * b t := by
      rw [hrκ]
      simp only [hb_def, ← twoByM_burkholderB_eq, burkholderB, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have := External.Burkholder.scalarFunction_holds.1 (x j + t * h j) (y j + t * ε * h j)
      have : 0 ≤ ‖y j + t * ε * h j‖ ^ 6 := by positivity
      simp only [burkholderU_eq]
      linarith
    linarith
  have hU : (fun t : ℝ => zigzagU (fun j => x j + t * h j) (fun j => y j + t * ε * h j)) =
      fun t => √(r t) - 5 ^ 4 * √(b t) := by
    funext t
    simp only [zigzagU, twoByM_burkholderB_eq, hr_def, hb_def]
  rw [hU]
  refine twoByM_concaveOn_of_mollify (Φ := fun r b => √r - 5 ^ 4 * √b) hr hb (by fun_prop)
    fun φ => ?_
  -- the mollifications `r_η`, `b_η`: smooth, (17), `b_η > 0`, convexity of `b_η^{1/6}` and (18)
  have hR := twoByM_hasDerivAt_deriv
    (φ.contDiff_normed_convolution (μ := volume) hr.locallyIntegrable)
  have hB := twoByM_hasDerivAt_deriv
    (φ.contDiff_normed_convolution (μ := volume) hb.locallyIntegrable)
  have hb0 := twoByM_mollify_Bq_pos (q := 6) (by norm_num) hxh φ
  have h17 := twoByM_eq17 hr hb hκ hrb φ
  have h18 := twoByM_eq18 hb0 (fun t => (hB t).1) (fun t => (hB t).2)
    (twoByM_convexOn_mollify_Bq (q := 6) (by norm_num) x h φ)
  -- the paper's computation: `√r_η − 5⁴ √b_η` is concave
  exact twoByM_sqrt_concave (fun t => (hR t).1) (fun t => (hR t).2) hb0 (fun t => (hB t).1)
    (fun t => (hB t).2) (fun t => (h17 t).1) (fun t => (h17 t).2) h18

/-- `‖z‖_{ℓ_6}^3 = B (z)^{1/2}`. -/
theorem twoByM_lq6_cube {n : ℕ} (z : Fin n → ℂ) : lqNorm 6 z ^ 3 = √(burkholderB z) := by
  rw [lqNorm, burkholderB, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Finset.sum_nonneg fun _ _ => by positivity)]
  have : ∀ j, ‖z j‖ ^ (6 : ℝ) = ‖z j‖ ^ 6 := fun j => by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [this]
  norm_num

/-- (16) (`eq:U-majorization`): `U (x, y) ≥ ‖y‖_6³ − 5⁴ ‖x‖_6³`, from (13). -/
theorem twoByM_U_majorization {n : ℕ}
    (x y : Fin n → ℂ) : lqNorm 6 y ^ 3 - 5 ^ 4 * lqNorm 6 x ^ 3 ≤ zigzagU x y := by
  rw [twoByM_lq6_cube, twoByM_lq6_cube, zigzagU]
  -- `R (x, y) ≥ ‖y‖_6⁶ + 5⁶ ‖x‖_6⁶ ≥ ‖y‖_6⁶`
  have hR : burkholderB y ≤ burkholderR x y := by
    rw [burkholderB, burkholderR]
    refine Finset.sum_le_sum fun j _ => ?_
    have := External.Burkholder.scalarFunction_holds.1 (x j) (y j)
    have : 0 ≤ ‖x j‖ ^ 6 := by positivity
    simp only [burkholderU_eq]
    linarith
  have := Real.sqrt_le_sqrt hR
  linarith

theorem twoByM_continuous_explicitG (n : ℕ) : Continuous (explicitG n) := by
  have hP : Continuous fun A : Matrix (Fin 2) (Fin (2 * n)) ℝ => fun j => conj (wirtP A j) :=
    continuous_pi fun j => Complex.continuous_conj.comp
      ((continuous_apply j).comp (twoByM_continuous_wirtP n))
  exact ((twoByM_continuous_zigzagU n).comp (hP.prodMk (twoByM_continuous_wirtQ n))).neg

/-- **Proposition 4.2** (`prop:explicit`), the claim of its proof: `g_n` is a globally rank-one
convex integrand with `g_n ≤ f_n` and `g_n (0) = 0 = f_n (0)`. By (13), (14)
(`External.Burkholder.scalarFunction_holds`).

Proof: the paper's (TeX 1223–1352): (16) from (13) (`twoByM_U_majorization`); rank-one
convexity along `B + t R`, `rank R = 1`: Lemma 4.1 gives `Q_n R = λ conj (P_n R)` with
`|λ| = 1`, so `g_n = −U (x + t h, y + t λ h)`, which is convex by the zig-zag concavity of `U`
(`twoByM_zigzag`). That is proved as in the paper, with the mollifications `r_η`, `b_η` of
`r (t) = R (x + t h, y + t λ h)` and `b (t) = B (x + t h)`: (14) and (13) give (17)
(`twoByM_eq17`); `b_η^{1/6}` is convex by Minkowski's inequality and `b_η > 0`
(`twoByM_convexOn_mollify_Bq`, `twoByM_mollify_Bq_pos`), which gives (18) (`twoByM_eq18`); the
computation `(√r_η)'' ≤ 5⁴ (√b_η)''` makes `√r_η − 5⁴ √b_η` concave (`twoByM_sqrt_concave`); and
`η ↓ 0` gives the concavity of `U (x + t h, y + t λ h)` (`twoByM_concaveOn_of_mollify`). -/
theorem proposition4_2_minorant (n : ℕ) :
    IsIntegrand (explicitG n) ∧ RankOneConvex (explicitG n) ∧
      (∀ A, explicitG n A ≤ explicitF n A) ∧ explicitG n 0 = 0 ∧ explicitF n 0 = 0 := by
  refine ⟨isIntegrand_of_continuous (twoByM_continuous_explicitG n), fun A B hAB => ?_,
    fun A => ?_, ?_, ?_⟩
  · -- along `B + t (A − B)`, `g_n = −U (x + t h, y + t λ h)` with `x = conj P B`,
    -- `h = conj P (A − B)`, `y = Q B`, and `λ = λ (A − B)` unimodular (Lemma 4.1)
    set R := A - B
    have hR : R.rank ≤ 1 := hAB.le
    obtain ⟨lam, -, hlam⟩ := lemma4_1 n
    have hline : ∀ t : ℝ, t • A + (1 - t) • B = B + t • R := fun t => by
      simp only [R]; module
    have key : (fun t : ℝ => explicitG n (t • A + (1 - t) • B)) = fun t : ℝ =>
        -zigzagU (fun j => conj (wirtP B j) + t * conj (wirtP R j))
          (fun j => wirtQ B j + t * lam R * conj (wirtP R j)) := by
      funext t
      rw [hline, explicitG]
      congr 2
      · funext j
        rw [twoByM_wirtP_add, twoByM_wirtP_smul, Pi.add_apply, map_add, map_mul,
          Complex.conj_ofReal]
      · funext j
        rw [twoByM_wirtQ_add, twoByM_wirtQ_smul, Pi.add_apply, (hlam R hR).2.1 j, mul_assoc]
    rw [key]
    exact (twoByM_zigzag _ _ _ (hlam R hR).1.le).neg.subset (Set.subset_univ _)
      (convex_Icc 0 1)
  · -- (16)
    have := twoByM_U_majorization (fun j => conj (wirtP A j)) (wirtQ A)
    rw [twoByM_lqNorm_conj] at this
    rw [explicitG, explicitF]
    linarith
  · simp [explicitG, zigzagU, burkholderR, burkholderB, burkholderU, twoByM_wirtP_zero,
      twoByM_wirtQ_zero]
  · simp [explicitF, twoByM_wirtP_zero, twoByM_wirtQ_zero,
      twoByM_lqNorm_zero (by norm_num : (0:ℝ) < 6)]

/-- **Proposition 4.2** (`prop:explicit`): `f_n` is rank-one convex at `0` (for every `n`; the
section fixes `n ∈ ℕ`). By Burkholder's properties (13), (14) of `u`
(`External.Burkholder.scalarFunction_holds`).

Proof: the paper's: `g_n` is a rank-one convex minorant of `f_n` with `g_n (0) = 0 = f_n (0)`
(`proposition4_2_minorant`). -/
theorem proposition4_2 (n : ℕ) :
    RankOneConvexAt (explicitF n) 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := proposition4_2_minorant n
  exact ⟨explicitG n, h1, h2, h3, by rw [h4, h5]⟩

/-! ### Proposition 4.3: the limiting argument and the failure of quasiconvexity -/


/-- The derivative matrix of `y ↦ L⁻¹ φ (L (y − c))` at `y` is that of `φ` at `L (y − c)`. -/
theorem twoByM_jac_rescale {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hφ : Differentiable ℝ φ) {L : ℝ} (hL : L ≠ 0) (c : Fin m → ℝ) (y : Fin m → ℝ) :
    jac (fun y => L⁻¹ • φ (L • (y - c))) y = jac φ (L • (y - c)) := by
  ext i k
  simp only [jac, Matrix.of_apply]
  have hφi : Differentiable ℝ fun x => φ x i := fun x =>
    (differentiableAt_pi.1 (hφ x)) i
  have hA : HasFDerivAt (fun y : Fin m → ℝ => L • (y - c))
      (L • ContinuousLinearMap.id ℝ (Fin m → ℝ)) y := by
    simpa using ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const c).const_smul L
  have hcomp : HasFDerivAt (fun y => L⁻¹ • φ (L • (y - c)) i)
      (L⁻¹ • ((fderiv ℝ (fun x => φ x i) (L • (y - c))).comp
        (L • ContinuousLinearMap.id ℝ (Fin m → ℝ)))) y :=
    ((hφi (L • (y - c))).hasFDerivAt.comp y hA).const_smul L⁻¹
  have : (fun y => (L⁻¹ • φ (L • (y - c))) i) = fun y => L⁻¹ • (φ (L • (y - c)) i) := by
    funext y; simp
  rw [this, hcomp.fderiv]
  simp [smul_smul, inv_mul_cancel₀ hL]

/-- A smooth compactly supported map on `ℝ^m` with `∫ F (∇φ) < 0`, rescaled into the unit cube,
refutes quasiconvexity of `F` at `0` (`F (0) = 0`). -/
theorem twoByM_not_qc_of_compact {d m : ℕ} {F : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hF : Continuous F) (hF0 : F 0 = 0) {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (hneg : ∫ x, F (jac φ x) < 0) : ¬ QuasiconvexAt F 0 := by
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ tsupport φ ⊆ Metric.closedBall 0 r := by
    obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall 0
    exact ⟨max r 1, by positivity, hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  set L : ℝ := 4 * r
  have hL : 0 < L := by positivity
  set c : Fin m → ℝ := fun _ => 1 / 2
  set ψ : (Fin m → ℝ) → Fin d → ℝ := fun y => L⁻¹ • φ (L • (y - c))
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    simp only [ψ]; fun_prop
  -- `ψ` vanishes off `closedBall c (1/4)`
  have hsupp : ∀ y, ψ y ≠ 0 → y ∈ Metric.closedBall c (1 / 4) := by
    intro y hy
    have h1 : L • (y - c) ∈ tsupport φ := subset_tsupport _ fun h => hy (by simp [ψ, h])
    have h2 := hr h1
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hL.le] at h2
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : ‖y - c‖ ≤ r / L := by rw [le_div_iff₀ hL]; linarith
    calc ‖y - c‖ ≤ r / L := this
      _ = 1 / 4 := by simp only [L]; field_simp
  have htsupp : tsupport ψ ⊆ Metric.closedBall c (1 / 4) :=
    closure_minimal (fun y hy => hsupp y hy) Metric.isClosed_closedBall
  have hcψ : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c (1 / 4))
      fun y hy => hsupp y hy
  have hcube : Metric.closedBall c (1 / 4) ⊆ unitCube m := by
    intro y hy i _
    rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)] at hy
    have := hy i
    rw [Real.dist_eq, abs_le] at this
    simp only [c] at this
    constructor <;> linarith [this.1, this.2]
  refine not_quasiconvexAt_of_smooth hF hψ hcψ (htsupp.trans hcube) ?_
  -- `∫_{(0,1)^m} F (∇ψ) = L^{−m} ∫ F (∇φ) < 0`
  have hjac : ∀ y, jac ψ y = jac φ (L • (y - c)) := fun y =>
    twoByM_jac_rescale (hφ.differentiable (by simp)) hL.ne' c y
  have hzero : ∀ y, y ∉ unitCube m → F (0 + jac ψ y) = 0 := by
    intro y hy
    have hy' : y ∉ tsupport ψ := fun h => hy (hcube (htsupp h))
    have : jac ψ y = 0 := by
      ext i k
      simp only [jac, Matrix.of_apply, Matrix.zero_apply]
      have hloc : (fun y => ψ y i) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy'] with z hz
        simp [hz]
      rw [hloc.fderiv_eq]; simp
    rw [this, zero_add, hF0]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero, hF0]
  simp only [zero_add, hjac]
  have h1 : ∫ y, F (jac φ (L • (y - c))) = ∫ y, F (jac φ (L • y)) :=
    integral_sub_right_eq_self (fun y => F (jac φ (L • y))) c
  rw [h1, Measure.integral_comp_smul (μ := volume) (f := fun x => F (jac φ x)) L]
  exact smul_neg_of_pos_of_neg (by positivity) hneg


theorem twoByM_contDiff_W (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (twoByM_W n) := by
  have : twoByM_W n = fun ξ => (∏ j, ((ξ (blockCol j 0) : ℂ) - (ξ (blockCol j 1) : ℂ) *
      Complex.I)) * (Real.exp (-(∑ k, ξ k ^ 2) / 2) : ℂ) := by
    funext ξ; simp only [twoByM_W, twoByM_conj_blockZ]
  rw [this]
  have hof : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ => (x : ℂ) := Complex.ofRealCLM.contDiff
  fun_prop

theorem twoByM_contDiff_testU (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (testU n) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · have : (fun ξ => testU n ξ 0) = fun ξ => (twoByM_W n ξ).re :=
      funext fun ξ => (twoByM_testU_apply n ξ).1
    simp only [Fin.zero_eta, Fin.isValue]
    rw [this]; exact Complex.reCLM.contDiff.comp (twoByM_contDiff_W n)
  · have : (fun ξ => testU n ξ 1) = fun ξ => (twoByM_W n ξ).im :=
      funext fun ξ => (twoByM_testU_apply n ξ).2
    simp only [Fin.mk_one, Fin.isValue]
    rw [this]; exact Complex.imCLM.contDiff.comp (twoByM_contDiff_W n)

/-- The cutoff `χ` (`= 1` on the unit ball, supported in the ball of radius `2`). -/
noncomputable def twoByM_χ (d : ℕ) : ContDiffBump (0 : Fin d → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The truncated test map `φ_R = χ (·/R) u_n`. -/
noncomputable def twoByM_cut (n : ℕ) (R : ℝ) (x : Fin (2 * n) → ℝ) : Fin 2 → ℝ :=
  twoByM_χ (2 * n) (R⁻¹ • x) • testU n x

theorem twoByM_contDiff_cut (n : ℕ) (R : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (twoByM_cut n R) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun x : Fin (2 * n) → ℝ => twoByM_χ (2 * n) (R⁻¹ • x) :=
    (twoByM_χ (2 * n)).contDiff.comp (contDiff_const_smul R⁻¹)
  exact h1.smul (twoByM_contDiff_testU n)

theorem twoByM_hasCompactSupport_cut (n : ℕ) {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (twoByM_cut n R) := by
  have : HasCompactSupport fun x : Fin (2 * n) → ℝ => twoByM_χ (2 * n) (R⁻¹ • x) :=
    (twoByM_χ (2 * n)).hasCompactSupport.comp_smul (inv_ne_zero hR)
  exact this.smul_right

/-- `φ_R = u_n` near `x` once `R > ‖x‖`. -/
theorem twoByM_jac_cut_eventually (n : ℕ) (x : Fin (2 * n) → ℝ) :
    ∀ᶠ m : ℕ in atTop, jac (twoByM_cut n ((m : ℝ) + 1)) x = jac (testU n) x := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop m₀] with m hm
  have hR : ‖x‖ < (m : ℝ) + 1 := by
    have : (m₀ : ℝ) ≤ m := Nat.cast_le.2 hm
    linarith
  have hloc : twoByM_cut n ((m : ℝ) + 1) =ᶠ[𝓝 x] testU n := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self (x := x) (ε := (m : ℝ) + 1 - ‖x‖)
      (by linarith))] with y hy
    have hy' : ‖y‖ < (m : ℝ) + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have := norm_le_norm_add_norm_sub' y x
      linarith [norm_sub_rev y x]
    have : twoByM_χ (2 * n) (((m : ℝ) + 1)⁻¹ • y) = 1 := by
      refine ContDiffBump.one_of_mem_closedBall _ ?_
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
      show ((m : ℝ) + 1)⁻¹ * ‖y‖ ≤ 1
      rw [inv_mul_le_iff₀ (by positivity)]; linarith
    simp [twoByM_cut, this]
  ext i k
  simp only [jac, Matrix.of_apply]
  have : (fun y => twoByM_cut n ((m : ℝ) + 1) y i) =ᶠ[𝓝 x] fun y => testU n y i :=
    hloc.mono fun y hy => congrFun hy i
  rw [this.fderiv_eq]


theorem twoByM_lqNorm_add {n : ℕ} {q : ℝ} (hq : 1 ≤ q) (a b : Fin n → ℂ) :
    lqNorm q (a + b) ≤ lqNorm q a + lqNorm q b := by
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨one_le_ofReal_of_one_le hq⟩
  have hq0 : 0 < q := by linarith
  rw [twoByM_lqNorm_eq_norm q hq0, twoByM_lqNorm_eq_norm q hq0, twoByM_lqNorm_eq_norm q hq0,
    WithLp.toLp_add]
  exact norm_add_le _ _

theorem twoByM_lqNorm_smul {n : ℕ} {q : ℝ} (hq : 1 ≤ q) (t : ℝ) (a : Fin n → ℂ) :
    lqNorm q (fun j => (t : ℂ) * a j) = |t| * lqNorm q a := by
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨one_le_ofReal_of_one_le hq⟩
  have hq0 : 0 < q := by linarith
  rw [twoByM_lqNorm_eq_norm q hq0, twoByM_lqNorm_eq_norm q hq0,
    show (fun j => (t : ℂ) * a j) = (t : ℂ) • a from rfl, WithLp.toLp_smul, norm_smul,
    Complex.norm_real, Real.norm_eq_abs]

theorem twoByM_lqNorm_le_sum {n : ℕ} {q : ℝ} (hq : 1 ≤ q) (a : Fin n → ℂ) :
    lqNorm q a ≤ ∑ j, ‖a j‖ := by
  have hq0 : 0 < q := by linarith
  set S := ∑ j, ‖a j‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hle : ∑ j, ‖a j‖ ^ q ≤ S ^ q := by
    calc ∑ j, ‖a j‖ ^ q ≤ ∑ j, ‖a j‖ * S ^ (q - 1) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hj : ‖a j‖ ≤ S := Finset.single_le_sum (f := fun j => ‖a j‖)
            (fun j _ => norm_nonneg _) (Finset.mem_univ j)
          rcases eq_or_lt_of_le (norm_nonneg (a j)) with h0 | h0
          · rw [← h0, Real.zero_rpow hq0.ne', zero_mul]
          · rw [show ‖a j‖ ^ q = ‖a j‖ * ‖a j‖ ^ (q - 1) by
              rw [← Real.rpow_one_add' h0.le (by linarith)]; ring_nf]
            gcongr
      _ = S ^ q := by
          rw [← Finset.sum_mul]
          rcases eq_or_lt_of_le hS with h0 | h0
          · have h0' : ∑ j, ‖a j‖ = 0 := h0.symm
            rw [h0', zero_mul, ← h0, Real.zero_rpow hq0.ne']
          · rw [← Real.rpow_one_add' h0.le (by linarith)]; ring_nf
  calc lqNorm q a ≤ (S ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => by positivity) hle (by positivity)
    _ = S := by rw [← Real.rpow_mul hS, mul_one_div_cancel hq0.ne', Real.rpow_one]

/-- `‖α_j (v ⊗ g)‖ ≤ (|v₀| + |v₁|) G` when every `|g_k| ≤ G`. -/
theorem twoByM_norm_wirtP_rankOne {n : ℕ} (v : Fin 2 → ℝ) (g : Fin (2 * n) → ℝ) {G : ℝ}
    (hg : ∀ k, |g k| ≤ G) (j : Fin n) :
    ‖wirtP (Matrix.of fun i k => v i * g k) j‖ ≤ (|v 0| + |v 1|) * G := by
  rw [twoByM_wirtP_apply]
  simp only [Matrix.of_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have h1 := hg (blockCol j 0); have h2 := hg (blockCol j 1)
  have hG : 0 ≤ G := (abs_nonneg _).trans h1
  rw [abs_div, abs_div, abs_two]
  have e1 : |v 0 * g (blockCol j 0) + v 1 * g (blockCol j 1)| ≤ |v 0| * G + |v 1| * G := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
  have e2 : |v 1 * g (blockCol j 0) - v 0 * g (blockCol j 1)| ≤ |v 1| * G + |v 0| * G := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
  linarith


/-- The derivative of the cutoff `χ (·/R)` in the direction `e_k`. -/
noncomputable def twoByM_gcut (n : ℕ) (R : ℝ) (x : Fin (2 * n) → ℝ) (k : Fin (2 * n)) : ℝ :=
  fderiv ℝ (fun y => twoByM_χ (2 * n) (R⁻¹ • y)) x (Pi.single k 1)

theorem twoByM_jac_cut (n : ℕ) (R : ℝ) (x : Fin (2 * n) → ℝ) :
    jac (twoByM_cut n R) x = twoByM_χ (2 * n) (R⁻¹ • x) • jac (testU n) x +
      Matrix.of fun i k => testU n x i * twoByM_gcut n R x k := by
  have hχ : Differentiable ℝ fun y : Fin (2 * n) → ℝ => twoByM_χ (2 * n) (R⁻¹ • y) :=
    ((twoByM_χ (2 * n)).contDiff (n := 1)).differentiable (by simp) |>.comp
      (differentiable_id.const_smul R⁻¹)
  have hu : Differentiable ℝ (testU n) :=
    (twoByM_contDiff_testU n).differentiable (by simp)
  ext i k
  simp only [jac, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hui : Differentiable ℝ fun y => testU n y i := fun y => differentiableAt_pi.1 (hu y) i
  have : (fun y => twoByM_cut n R y i) =
      fun y => twoByM_χ (2 * n) (R⁻¹ • y) * testU n y i := by
    funext y; simp [twoByM_cut]
  rw [this, ((hχ x).hasFDerivAt.fun_mul (hui x).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    twoByM_gcut]

theorem twoByM_gcut_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 0 < R → ∀ x k, |twoByM_gcut n R x k| ≤ R⁻¹ * C := by
  obtain ⟨C, hC⟩ :=
    ((twoByM_χ (2 * n)).hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (((twoByM_χ (2 * n)).contDiff (n := 1)).continuous_fderiv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, hC0, fun R hR x k => ?_⟩
  have hdiff : DifferentiableAt ℝ (twoByM_χ (2 * n)) (R⁻¹ • x) :=
    ((twoByM_χ (2 * n)).contDiff (n := 1)).differentiable (by simp) _
  have hA : HasFDerivAt (fun y : Fin (2 * n) → ℝ => R⁻¹ • y)
      (R⁻¹ • ContinuousLinearMap.id ℝ (Fin (2 * n) → ℝ)) x := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) x).const_smul R⁻¹
  have hcomp : HasFDerivAt (fun y => twoByM_χ (2 * n) (R⁻¹ • y))
      ((fderiv ℝ (twoByM_χ (2 * n)) (R⁻¹ • x)).comp
        (R⁻¹ • ContinuousLinearMap.id ℝ (Fin (2 * n) → ℝ))) x :=
    hdiff.hasFDerivAt.comp x hA
  rw [twoByM_gcut, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hR]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |fderiv ℝ (twoByM_χ (2 * n)) (R⁻¹ • x) (Pi.single k 1)|
      ≤ ‖fderiv ℝ (twoByM_χ (2 * n)) (R⁻¹ • x)‖ * ‖(Pi.single k 1 : Fin (2 * n) → ℝ)‖ := by
        rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * 1 := by
        gcongr
        · exact hC _
        · rw [Pi.norm_single, norm_one]
    _ = C := mul_one C

/-- `‖P_n (∇φ_R)‖_{ℓ_6} ≤ ‖P_n (∇u_n)‖_{ℓ_6} + n C (|u_n|₁) / R`. -/
theorem twoByM_lqP_cut_le {q : ℝ} (hq : 1 ≤ q) (n : ℕ) {C : ℝ}
    (hC : ∀ (R : ℝ), 0 < R → ∀ x k, |twoByM_gcut n R x k| ≤ R⁻¹ * C) {R : ℝ} (hR : 0 < R)
    (x : Fin (2 * n) → ℝ) :
    lqNorm q (wirtP (jac (twoByM_cut n R) x)) ≤ lqNorm q (wirtP (jac (testU n) x)) +
      n * ((|testU n x 0| + |testU n x 1|) * (R⁻¹ * C)) := by
  rw [twoByM_jac_cut, twoByM_wirtP_add, twoByM_wirtP_smul]
  refine (twoByM_lqNorm_add hq _ _).trans (add_le_add ?_ ?_)
  · rw [twoByM_lqNorm_smul hq]
    have h0 := (twoByM_χ (2 * n)).nonneg (x := R⁻¹ • x)
    have h1 := (twoByM_χ (2 * n)).le_one (x := R⁻¹ • x)
    rw [abs_of_nonneg h0]
    exact mul_le_of_le_one_left (twoByM_lqNorm_nonneg q _) h1
  · refine (twoByM_lqNorm_le_sum hq _).trans ?_
    calc ∑ j, ‖wirtP (Matrix.of fun i k => testU n x i * twoByM_gcut n R x k) j‖
        ≤ ∑ _j : Fin n, (|testU n x 0| + |testU n x 1|) * (R⁻¹ * C) :=
          Finset.sum_le_sum fun j _ =>
            twoByM_norm_wirtP_rankOne (testU n x) _ (fun k => hC R hR x k) j
      _ = _ := by simp

theorem twoByM_norm_W {n : ℕ} (ξ : Fin (2 * n) → ℝ) :
    ‖twoByM_W n ξ‖ = ∏ j, (‖blockZ ξ j‖ * Real.exp (-‖blockZ ξ j‖ ^ 2 / 2)) := by
  rw [twoByM_W, norm_mul, norm_prod, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    twoByM_exp_split, ← Finset.prod_mul_distrib]
  simp

/-- `∫ (|u_n|₁)^3 < ∞`. -/
theorem twoByM_lintegral_testU_lt_top (n : ℕ) :
    ∫⁻ x : Fin (2 * n) → ℝ, ENNReal.ofReal ((|testU n x 0| + |testU n x 1|) ^ 3) < ⊤ := by
  have hT := twoByM_measurePreserving_blockZ n
  have hle : ∀ x : Fin (2 * n) → ℝ, (|testU n x 0| + |testU n x 1|) ^ 3 ≤
      8 * ∏ j, twoByM_a 3 (blockZ x j) := by
    intro x
    obtain ⟨h0, h1⟩ := twoByM_testU_apply n x
    have e0 : |testU n x 0| ≤ ‖twoByM_W n x‖ := by rw [h0]; exact Complex.abs_re_le_norm _
    have e1 : |testU n x 1| ≤ ‖twoByM_W n x‖ := by rw [h1]; exact Complex.abs_im_le_norm _
    have : ∏ j, twoByM_a 3 (blockZ x j) = ‖twoByM_W n x‖ ^ 3 := by
      rw [twoByM_norm_W, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [twoByM_a, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [this]
    have hW := norm_nonneg (twoByM_W n x)
    have := add_le_add e0 e1
    calc (|testU n x 0| + |testU n x 1|) ^ 3 ≤ (2 * ‖twoByM_W n x‖) ^ 3 := by
          gcongr; linarith
      _ = 8 * ‖twoByM_W n x‖ ^ 3 := by ring
  have hmeas : Measurable fun z : Fin n → ℂ => ENNReal.ofReal (8 * ∏ j, twoByM_a 3 (z j)) :=
    (measurable_const.mul (Finset.measurable_prod (f := fun j (z : Fin n → ℂ) => twoByM_a 3 (z j)) _
      fun j _ => (twoByM_measurable_a 3).comp (measurable_pi_apply j))).ennreal_ofReal
  calc ∫⁻ x : Fin (2 * n) → ℝ, ENNReal.ofReal ((|testU n x 0| + |testU n x 1|) ^ 3)
      ≤ ∫⁻ x : Fin (2 * n) → ℝ, ENNReal.ofReal (8 * ∏ j, twoByM_a 3 (blockZ x j)) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x)
    _ = ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (8 * ∏ j, twoByM_a 3 (z j)) :=
        hT.lintegral_comp (f := fun z : Fin n → ℂ => ENNReal.ofReal (8 * ∏ j, twoByM_a 3 (z j)))
          hmeas
    _ = 8 * ∏ _j : Fin n, twoByM_c 3 := by
        simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
          ENNReal.ofReal_prod_of_nonneg fun j _ => twoByM_a_nonneg 3 _]
        rw [lintegral_const_mul _ (Finset.measurable_prod
            (f := fun j (z : Fin n → ℂ) => ENNReal.ofReal (twoByM_a 3 (z j))) _ fun j _ =>
            (twoByM_measurable_a 3).ennreal_ofReal.comp (measurable_pi_apply j)),
          show (volume : Measure (Fin n → ℂ)) = Measure.pi fun _ => volume from rfl,
          twoByM_lintegral_fin_prod (fun _ z => ENNReal.ofReal (twoByM_a 3 z))
            fun _ => (twoByM_measurable_a 3).ennreal_ofReal]
        simp [twoByM_c_eq]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (by norm_num) ?_
        rw [Finset.prod_const]
        exact ENNReal.pow_lt_top (twoByM_c_lt_top (by norm_num))

theorem twoByM_continuous_jac {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hφ : ContDiff ℝ 1 φ) : Continuous (jac φ) := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  simp only [jac, Matrix.of_apply]
  have hi : ContDiff ℝ 1 fun y => φ y i := (contDiff_pi.1 hφ) i
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

/-- `x ↦ Φ (∇φ (x))` has compact support when `φ` does and `Φ (0) = 0`. -/
theorem twoByM_hasCompactSupport_comp_jac {d m : ℕ} {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hc : HasCompactSupport φ) {Φ : Matrix (Fin d) (Fin m) ℝ → ℝ} (hΦ0 : Φ 0 = 0) :
    HasCompactSupport fun x => Φ (jac φ x) := by
  refine HasCompactSupport.of_support_subset_isCompact hc.isCompact fun x hx => ?_
  by_contra hx'
  apply hx
  have : jac φ x = 0 := by
    ext i k
    simp only [jac, Matrix.of_apply, Matrix.zero_apply]
    have hloc : (fun y => φ y i) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with z hz
      simp [hz]
    rw [hloc.fderiv_eq]; simp
  simp [this, hΦ0]


theorem twoByM_rpow_three (x : ℝ) : x ^ (3 : ℝ) = x ^ 3 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `E |∂f/f (Z)|^q < ∞`. -/
theorem twoByM_EGP_lt_top {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫⁻ z, ENNReal.ofReal (twoByM_GP q z) ∂twoByM_prob p < ⊤ := by
  rw [twoByM_lintegral_prob (twoByM_measurable_GP q).ennreal_ofReal]
  refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 (twoByM_c_ne_zero p))) ?_
  have := (twoByM_integrable_aGP hp hq).lintegral_lt_top
  refine lt_of_eq_of_lt (lintegral_congr fun z => ?_) this
  rw [ENNReal.ofReal_mul (twoByM_a_nonneg p z)]

/-- `∫ ‖P_n (∇u_n)‖_{ℓ_q}^p < ∞` (`p < q`). -/
theorem twoByM_lintegral_lqP_lt_top {n : ℕ} (hn : 0 < n) {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    ∫⁻ ξ, ENNReal.ofReal (lqNorm q (wirtP (jac (testU n) ξ)) ^ p) < ⊤ := by
  have hq : 0 < q := by linarith
  rw [twoByM_integral_reduce hn hp (twoByM_measurable_GP q) (twoByM_GP_nonneg q)
    (Eventually.of_forall fun ξ => twoByM_lqP_eq hq ξ)]
  refine ENNReal.mul_lt_top (ENNReal.pow_lt_top (twoByM_c_lt_top hp))
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact (twoByM_denominator_le hp hpq hn).trans_lt
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) (twoByM_EGP_lt_top hp hq).ne)

theorem twoByM_continuous_explicitF (n : ℕ) : Continuous (explicitF n) := by
  unfold explicitF
  exact (continuous_const.mul (((twoByM_continuous_lqNorm (by norm_num)).comp
    (twoByM_continuous_wirtP n)).pow 3)).sub
    (((twoByM_continuous_lqNorm (by norm_num)).comp (twoByM_continuous_wirtQ n)).pow 3)

theorem twoByM_explicitF_zero (n : ℕ) : explicitF n 0 = 0 := by
  simp [explicitF, twoByM_wirtP_zero, twoByM_wirtQ_zero,
    twoByM_lqNorm_zero (by norm_num : (0 : ℝ) < 6)]

/-- **The limiting argument of Section 4.3** (`cs-sec4.3-limit`, TeX line 1051) for `f_n`, with
Lemma 4.2 at `p = 3`, `q = 6`: for `n` large, `f_n` is not quasiconvex at `0`. The truncations `φ_R = χ (·/R) u_n` of the
test map `u_n` satisfy `liminf_R ∫ ‖Q_n (∇φ_R)‖_6³ ≥ ∫ ‖Q_n (∇u_n)‖_6³` (Fatou) and
`∫ ‖P_n (∇φ_R)‖_6³ ≤ 4 ∫ ‖P_n (∇u_n)‖_6³ + O (R^{−3})`, so `∫ f_n (∇φ_R) < 0` for `R` large once
`‖Q_n (∇u_n)‖_{L³} / ‖P_n (∇u_n)‖_{L³} > (4 · 5⁴)^{1/3}` (Lemma 4.2); rescaled into the unit cube,
`φ_R` refutes quasiconvexity at `0`. -/
theorem twoByM_not_qc_explicitF : ∃ n₀ : ℕ, ∀ n ≥ n₀, ¬ QuasiconvexAt (explicitF n) 0 := by
  have h42 := lemma4_2 (p := 3) (q := 6) (by norm_num) (by norm_num)
  set T : ℝ≥0∞ := (4 * 5 ^ 4 : ℝ≥0∞) ^ (1 / 3 : ℝ)
  have hT : T < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((tendsto_order.1 h42).1 T hT)
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le one_pos (le_of_max_le_right hn)
  have hratio := hn₀ n (le_of_max_le_left hn)
  set IQ := ∫⁻ ξ, ENNReal.ofReal (lqNorm 6 (wirtQ (jac (testU n) ξ)) ^ (3 : ℝ))
  set IP := ∫⁻ ξ, ENNReal.ofReal (lqNorm 6 (wirtP (jac (testU n) ξ)) ^ (3 : ℝ))
  rw [show ENNReal.ofReal 3 = (ENNReal.ofReal (3 : ℝ)) from rfl,
    twoByM_eLpNorm_eq_rpow (by norm_num) (twoByM_continuous_lqQ (by norm_num))
      fun ξ => twoByM_lqNorm_nonneg 6 _,
    twoByM_eLpNorm_eq_rpow (by norm_num) (twoByM_continuous_lqP (by norm_num))
      fun ξ => twoByM_lqNorm_nonneg 6 _,
    ← ENNReal.div_rpow_of_nonneg _ _ (by norm_num)] at hratio
  have hIP : IP < ⊤ := twoByM_lintegral_lqP_lt_top hn0 (by norm_num) (by norm_num)
  have hkey : 4 * 5 ^ 4 * IP < IQ := by
    have h3 : 4 * 5 ^ 4 < IQ / IP := by
      have h := ENNReal.rpow_lt_rpow hratio (by norm_num : (0 : ℝ) < 3)
      rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num : (3 : ℝ) ≠ 0),
        ENNReal.rpow_one, ENNReal.rpow_one] at h
    by_cases hIP0 : IP = 0
    · rw [hIP0, mul_zero]
      rw [hIP0] at h3
      exact pos_iff_ne_zero.2 fun hQ => by simp [hQ] at h3
    · exact (ENNReal.lt_div_iff_mul_lt (Or.inl hIP0) (Or.inl hIP.ne)).1 h3
  obtain ⟨A', hA'1, hA'2⟩ := exists_between hkey
  obtain ⟨C, hC0, hC⟩ := twoByM_gcut_bound n
  have hJ := twoByM_lintegral_testU_lt_top n
  set J := ∫⁻ x : Fin (2 * n) → ℝ, ENNReal.ofReal ((|testU n x 0| + |testU n x 1|) ^ 3)
  -- the `Q`-part: Fatou's lemma
  have hcontQ : ∀ m : ℕ, Continuous fun x =>
      lqNorm 6 (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ (3 : ℝ) := fun m =>
    (((twoByM_continuous_lqNorm (by norm_num)).comp (twoByM_continuous_wirtQ n)).comp
      (twoByM_continuous_jac ((twoByM_contDiff_cut n _).of_le (by simp)))).rpow_const
      fun _ => Or.inr (by norm_num)
  have hQ : ∀ᶠ m : ℕ in atTop, A' <
      ∫⁻ x, ENNReal.ofReal (lqNorm 6 (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ (3 : ℝ)) := by
    have hfatou := lintegral_liminf_le (μ := (volume : Measure (Fin (2 * n) → ℝ))) (u := atTop)
      (f := fun (m : ℕ) x =>
        ENNReal.ofReal (lqNorm 6 (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ (3 : ℝ)))
      fun m => (hcontQ m).measurable.ennreal_ofReal
    have hlim : ∫⁻ x, liminf (fun (m : ℕ) =>
        ENNReal.ofReal (lqNorm 6 (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ (3 : ℝ))) atTop =
        IQ := by
      refine lintegral_congr fun x => ?_
      refine Tendsto.liminf_eq (tendsto_const_nhds.congr' ?_)
      filter_upwards [twoByM_jac_cut_eventually n x] with m hm
      rw [hm]
    rw [hlim] at hfatou
    exact eventually_lt_of_lt_liminf (hA'2.trans_le hfatou)
  -- the `P`-part: `∫ ‖P_n (∇φ_R)‖³ ≤ 4 I_P + 4 (n C / R)³ J`
  have hPbound : ∀ m : ℕ,
      ∫⁻ x, ENNReal.ofReal (lqNorm 6 (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ (3 : ℝ)) ≤
        4 * IP + ENNReal.ofReal (4 * (n * (((m : ℝ) + 1)⁻¹ * C)) ^ 3) * J := by
    intro m
    have hR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    calc ∫⁻ x, ENNReal.ofReal (lqNorm 6 (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ (3 : ℝ))
        ≤ ∫⁻ x, (4 * ENNReal.ofReal (lqNorm 6 (wirtP (jac (testU n) x)) ^ (3 : ℝ)) +
            ENNReal.ofReal (4 * (n * (((m : ℝ) + 1)⁻¹ * C)) ^ 3) *
              ENNReal.ofReal ((|testU n x 0| + |testU n x 1|) ^ 3)) := by
          refine lintegral_mono fun x => ?_
          have hb := twoByM_lqP_cut_le (q := 6) (by norm_num) n hC hR x
          set a := lqNorm 6 (wirtP (jac (testU n) x))
          set b := (n : ℝ) * ((|testU n x 0| + |testU n x 1|) * (((m : ℝ) + 1)⁻¹ * C))
          have ha0 : 0 ≤ a := twoByM_lqNorm_nonneg 6 _
          have hb0 : 0 ≤ b := by positivity
          have hc0 := twoByM_lqNorm_nonneg 6 (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x))
          rw [twoByM_rpow_three, twoByM_rpow_three, ← ENNReal.ofReal_ofNat 4,
            ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have : b ^ 3 = (n * (((m : ℝ) + 1)⁻¹ * C)) ^ 3 * (|testU n x 0| + |testU n x 1|) ^ 3 := by
            simp only [b]; ring
          calc lqNorm 6 (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ 3 ≤ (a + b) ^ 3 := by
                gcongr
            _ ≤ 4 * a ^ 3 + 4 * b ^ 3 := by nlinarith [sq_nonneg (a - b), mul_nonneg ha0 hb0]
            _ = _ := by rw [this]; ring
      _ = 4 * IP + ENNReal.ofReal (4 * (n * (((m : ℝ) + 1)⁻¹ * C)) ^ 3) * J := by
          rw [lintegral_add_left ((((twoByM_continuous_lqP (n := n) (by norm_num)).rpow_const
            fun _ => Or.inr (by norm_num)).measurable.ennreal_ofReal).const_mul _),
            lintegral_const_mul _ (((twoByM_continuous_lqP (n := n) (by norm_num)).rpow_const
            fun _ => Or.inr (by norm_num)).measurable.ennreal_ofReal),
            lintegral_const_mul _ (by
              refine Measurable.ennreal_ofReal (Measurable.pow_const ?_ _)
              have h0 := (twoByM_contDiff_testU n).continuous
              exact ((continuous_apply 0).comp h0 |>.abs.add
                ((continuous_apply 1).comp h0).abs).measurable)]
  have hP : ∀ᶠ m : ℕ in atTop, 5 ^ 4 *
      ∫⁻ x, ENNReal.ofReal (lqNorm 6 (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ (3 : ℝ)) <
        A' := by
    have hlim : Tendsto (fun m : ℕ => 5 ^ 4 * (4 * IP +
        ENNReal.ofReal (4 * (n * (((m : ℝ) + 1)⁻¹ * C)) ^ 3) * J)) atTop (𝓝 (4 * 5 ^ 4 * IP)) := by
      have h1 : Tendsto (fun m : ℕ => 4 * (n * (((m : ℝ) + 1)⁻¹ * C)) ^ 3) atTop (𝓝 0) := by
        have : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
          have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          simp only [one_div] at this
          exact this
        have h := (this.pow 3).const_mul (4 * ((n : ℝ) * C) ^ 3)
        rw [zero_pow three_ne_zero, mul_zero] at h
        exact h.congr fun m => by ring
      have h2 := ENNReal.Tendsto.const_mul
        ((ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hJ.ne)).const_add (4 * IP))
        (Or.inr (by norm_num : (5 : ℝ≥0∞) ^ 4 ≠ ⊤))
      convert h2 using 1
      simp [ENNReal.ofReal_zero]; ring
    filter_upwards [(tendsto_order.1 hlim).2 A' hA'1] with m hm
    exact lt_of_le_of_lt (by gcongr; exact hPbound m) hm
  obtain ⟨m, hmQ, hmP⟩ := (hQ.and hP).exists
  -- `∫ f_n (∇φ_R) < 0`
  have hR : ((m : ℝ) + 1) ≠ 0 := by positivity
  refine twoByM_not_qc_of_compact (twoByM_continuous_explicitF n) (twoByM_explicitF_zero n)
    (twoByM_contDiff_cut n _) (twoByM_hasCompactSupport_cut n hR) ?_
  have hjc := twoByM_continuous_jac ((twoByM_contDiff_cut n ((m : ℝ) + 1)).of_le (by simp))
  have hcP : Continuous fun x => lqNorm 6 (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ 3 :=
    (((twoByM_continuous_lqNorm (by norm_num)).comp (twoByM_continuous_wirtP n)).comp hjc).pow 3
  have hcQ : Continuous fun x => lqNorm 6 (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ 3 :=
    (((twoByM_continuous_lqNorm (by norm_num)).comp (twoByM_continuous_wirtQ n)).comp hjc).pow 3
  have hsP := twoByM_hasCompactSupport_comp_jac (twoByM_hasCompactSupport_cut n hR)
    (Φ := fun A => lqNorm 6 (wirtP A) ^ 3) (by simp [twoByM_wirtP_zero, twoByM_lqNorm_zero])
  have hsQ := twoByM_hasCompactSupport_comp_jac (twoByM_hasCompactSupport_cut n hR)
    (Φ := fun A => lqNorm 6 (wirtQ A) ^ 3) (by simp [twoByM_wirtQ_zero, twoByM_lqNorm_zero])
  have hiP := hcP.integrable_of_hasCompactSupport (μ := volume) hsP
  have hiQ := hcQ.integrable_of_hasCompactSupport (μ := volume) hsQ
  simp only [explicitF]
  rw [integral_sub (hiP.const_mul _) hiQ, integral_const_mul, sub_neg]
  have hlt : ENNReal.ofReal
      (5 ^ 4 * ∫ x, lqNorm 6 (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ 3) <
      ENNReal.ofReal (∫ x, lqNorm 6 (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ 3) := by
    rw [ENNReal.ofReal_mul (by norm_num), ofReal_integral_eq_lintegral_ofReal hiP
        (Eventually.of_forall fun x => pow_nonneg (twoByM_lqNorm_nonneg 6 _) 3),
      ofReal_integral_eq_lintegral_ofReal hiQ
        (Eventually.of_forall fun x => pow_nonneg (twoByM_lqNorm_nonneg 6 _) 3)]
    simp only [twoByM_rpow_three] at hmQ hmP
    calc ENNReal.ofReal (5 ^ 4) * ∫⁻ x, ENNReal.ofReal
          (lqNorm 6 (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ 3)
        = 5 ^ 4 * ∫⁻ x, ENNReal.ofReal
          (lqNorm 6 (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ 3) := by norm_num
      _ < A' := hmP
      _ < _ := hmQ
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg (by norm_num)
    (integral_nonneg fun x => pow_nonneg (twoByM_lqNorm_nonneg 6 _) 3))).1 hlt


theorem twoByM_zigzagU_smul {n : ℕ} (t : ℝ) (x y : Fin n → ℂ) :
    zigzagU (fun j => (t : ℂ) * x j) (fun j => (t : ℂ) * y j) = |t| ^ 3 * zigzagU x y := by
  have hn : ∀ z : ℂ, ‖(t : ℂ) * z‖ = |t| * ‖z‖ := fun z => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hR : burkholderR (fun j => (t : ℂ) * x j) (fun j => (t : ℂ) * y j) =
      |t| ^ 6 * burkholderR x y := by
    simp only [burkholderR, burkholderU, hn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hB : burkholderB (fun j => (t : ℂ) * x j) = |t| ^ 6 * burkholderB x := by
    simp only [burkholderB, hn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have h6 : √(|t| ^ 6) = |t| ^ 3 := by
    rw [show |t| ^ 6 = (|t| ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [zigzagU, zigzagU, hR, hB, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), h6]
  ring

/-- `g_n` is `3`-homogeneous. -/
theorem twoByM_isPHomogeneous_explicitG (n : ℕ) : IsPHomogeneous 3 (explicitG n) := by
  intro t A
  rw [twoByM_rpow_three, explicitG, explicitG, twoByM_wirtQ_smul, twoByM_wirtP_smul]
  have : (fun j => conj ((t : ℂ) * wirtP A j)) = fun j => (t : ℂ) * conj (wirtP A j) := by
    funext j; rw [map_mul, Complex.conj_ofReal]
  rw [this, twoByM_zigzagU_smul]
  ring

/-- **Proposition 4.3** (`prop:elem`): for `n` large enough, `g_n` is not quasiconvex at `0`, and
hence it is not quasiconvex anywhere. By (13), (14) (`External.Burkholder.scalarFunction_holds`)
and Dacorogna's formula (`External.KinderlehrerPedregal.dacorognaFormula_holds`).

Why Dacorogna's formula (TeX lines 1359–1366). The proof reads: if `g_n` were quasiconvex at `0`,
then `0 = g_n (0) = g_n^{qc} (0) ≤ f_n^{qc} (0) ≤ f_n (0) = 0`, contradicting that `f_n` is not
quasiconvex at `0`. The steps `g_n^{qc} ≤ f_n^{qc} ≤ f_n` and "`f_n^{qc} (0) = f_n (0)` makes `f_n`
quasiconvex at `0`" need no formula. The step `g_n (0) = g_n^{qc} (0)` does: `g_n` is assumed
quasiconvex at `0` only, and `g_n^{qc} (0) = g_n (0)` asks for a quasiconvex (at every matrix)
minorant of `g_n` touching it at `0`. That is the "only if" direction of line 559, which the paper
derives from Proposition 2.2 (Kinderlehrer–Pedregal); without the formula no such minorant is
available. So the proof uses the formula, on the paper's route (`cs-qc-minorant`). A shorter
argument would avoid it, by never forming the envelope: for each test map `φ`,
`∫ f_n (∇φ) ≥ ∫ g_n (∇φ) ≥ g_n (0) = 0 = f_n (0)` (`g_n` is continuous and `∇φ` bounded, so the
second integral exists), so `f_n` would be quasiconvex at `0`; it is recorded as a simplification,
not used here, because it departs from the paper's proof (it is stated, for the report, as
`twoByM_quasiconvexAt_of_minorant`, which no proof uses; `theorem1_2_elementary` follows this
proof too).

Proof: the paper's, through `quasiconvexAt_iff_exists_minorant` (both directions; `g_n` and `f_n`
are
continuous). That `f_n` is not quasiconvex at `0` for `n` large is the paper's implicit step from
Lemma 4.2 (at `p = 3`, `q = 6 ≥ p + 2`) and the limiting argument of Section 4.3 (TeX line 1051);
it is proved in `twoByM_not_qc_explicitF` (cutoff of `u_n`, Fatou's lemma, rescaling into the unit
cube). Nowhere quasiconvexity: `g_n` is `3`-homogeneous (`twoByM_isPHomogeneous_explicitG`) and
continuous, and `nowhereQuasiconvex_of_not_quasiconvexAt_zero` applies. -/
theorem proposition4_3 :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ¬ QuasiconvexAt (explicitG n) 0 ∧ NowhereQuasiconvex (explicitG n) := by
  obtain ⟨n₀, hn₀⟩ := twoByM_not_qc_explicitF
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨-, -, hle, hg0, hf0⟩ := proposition4_2_minorant n
  have hnot : ¬ QuasiconvexAt (explicitG n) 0 := by
    intro hqc
    -- `g_n (0) = g_n^{qc} (0)`: a quasiconvex minorant `g'` of `g_n` touching it at `0`
    obtain ⟨g', hg'i, hg'q, hg'le, hg'0⟩ :=
      (quasiconvexAt_iff_exists_minorant (twoByM_continuous_explicitG n) 0).1 hqc
    -- `g' ≤ g_n ≤ f_n` and `g' (0) = 0 = f_n (0)`, so `f_n^{qc} (0) = f_n (0)`: `f_n` would be
    -- quasiconvex at `0`
    exact hn₀ n hn ((quasiconvexAt_iff_exists_minorant (twoByM_continuous_explicitF n) 0).2
      ⟨g', hg'i, hg'q, fun B => (hg'le B).trans (hle B), by rw [hg'0, hg0, hf0]⟩)
  exact ⟨hnot, nowhereQuasiconvex_of_not_quasiconvexAt_zero (p := 3) (by norm_num)
    (twoByM_continuous_explicitG n) (Or.inl (twoByM_isPHomogeneous_explicitG n)) hnot⟩

/-! ### The limiting argument of Section 4.3: `C^{qc}` is at least the ratio for `u_n` -/


/-- `‖ |u_n|₁ ‖_{L^p (ℝ^{2n})} < ∞`. -/
theorem twoByM_eLpNorm_testU_lt_top {p : ℝ} (hp : 0 < p) (n : ℕ) :
    eLpNorm (fun x : Fin (2 * n) → ℝ => |testU n x 0| + |testU n x 1|) (ENNReal.ofReal p) volume
      < ⊤ := by
  have hT := twoByM_measurePreserving_blockZ n
  have hcont : Continuous fun x : Fin (2 * n) → ℝ => |testU n x 0| + |testU n x 1| := by
    have h0 := (twoByM_contDiff_testU n).continuous
    exact ((continuous_apply 0).comp h0).abs.add ((continuous_apply 1).comp h0).abs
  rw [twoByM_eLpNorm_eq_rpow hp hcont fun x => by positivity]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt ?_)
  have hle : ∀ x : Fin (2 * n) → ℝ, (|testU n x 0| + |testU n x 1|) ^ p ≤
      2 ^ p * ∏ j, twoByM_a p (blockZ x j) := by
    intro x
    obtain ⟨h0, h1⟩ := twoByM_testU_apply n x
    have e0 : |testU n x 0| ≤ ‖twoByM_W n x‖ := by rw [h0]; exact Complex.abs_re_le_norm _
    have e1 : |testU n x 1| ≤ ‖twoByM_W n x‖ := by rw [h1]; exact Complex.abs_im_le_norm _
    have : ∏ j, twoByM_a p (blockZ x j) = ‖twoByM_W n x‖ ^ p := by
      rw [twoByM_norm_W, twoByM_prod_rpow _ _ fun j _ => by positivity]
      rfl
    rw [this, ← Real.mul_rpow (by norm_num) (norm_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hp.le
  have hmeas : Measurable fun z : Fin n → ℂ => ENNReal.ofReal (2 ^ p * ∏ j, twoByM_a p (z j)) :=
    (measurable_const.mul (Finset.measurable_prod (f := fun j (z : Fin n → ℂ) => twoByM_a p (z j)) _
      fun j _ => (twoByM_measurable_a p).comp (measurable_pi_apply j))).ennreal_ofReal
  calc ∫⁻ x : Fin (2 * n) → ℝ, ENNReal.ofReal ((|testU n x 0| + |testU n x 1|) ^ p)
      ≤ ∫⁻ x : Fin (2 * n) → ℝ, ENNReal.ofReal (2 ^ p * ∏ j, twoByM_a p (blockZ x j)) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x)
    _ = ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (2 ^ p * ∏ j, twoByM_a p (z j)) :=
        hT.lintegral_comp (f := fun z : Fin n → ℂ => ENNReal.ofReal (2 ^ p * ∏ j, twoByM_a p (z j)))
          hmeas
    _ = ENNReal.ofReal (2 ^ p) * ∏ _j : Fin n, twoByM_c p := by
        simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ p),
          ENNReal.ofReal_prod_of_nonneg fun j _ => twoByM_a_nonneg p _]
        rw [lintegral_const_mul _ (Finset.measurable_prod
            (f := fun j (z : Fin n → ℂ) => ENNReal.ofReal (twoByM_a p (z j))) _ fun j _ =>
            (twoByM_measurable_a p).ennreal_ofReal.comp (measurable_pi_apply j)),
          show (volume : Measure (Fin n → ℂ)) = Measure.pi fun _ => volume from rfl,
          twoByM_lintegral_fin_prod (fun _ z => ENNReal.ofReal (twoByM_a p z))
            fun _ => (twoByM_measurable_a p).ennreal_ofReal]
        simp [twoByM_c_eq]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [Finset.prod_const]
        exact ENNReal.pow_lt_top (twoByM_c_lt_top hp)

/-- The limiting argument of Section 4.3 (TeX lines 1047–1053) for `F_{n,p,q,C}`: if
`C < ‖Q_n (∇u_n)‖_{L^p (ℓ_q^n)} / ‖P_n (∇u_n)‖_{L^p (ℓ_q^n)}`, then `F_{n,p,q,C}` is not quasiconvex
at `0`. The truncations `φ_R = χ (·/R) u_n` satisfy
`‖Q_n (∇u_n)‖_{L^p} ≤ liminf_R ‖Q_n (∇φ_R)‖_{L^p}` (Fatou) and
`‖P_n (∇φ_R)‖_{L^p} ≤ ‖P_n (∇u_n)‖_{L^p} + O (1/R)` (Minkowski), so `∫ F_{n,p,q,C} (∇φ_R) < 0` for
`R` large, and `φ_R`, rescaled into the unit cube, refutes quasiconvexity at `0`. -/
theorem twoByM_not_qc_blockF {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (n : ℕ) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hlt : ENNReal.ofReal C <
      eLpNorm (fun ξ => lqNorm q (wirtQ (jac (testU n) ξ))) (ENNReal.ofReal p) volume /
        eLpNorm (fun ξ => lqNorm q (wirtP (jac (testU n) ξ))) (ENNReal.ofReal p) volume) :
    ¬ QuasiconvexAt (blockF n p q C) 0 := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := one_le_ofReal_of_one_le hp.le
  set A := eLpNorm (fun ξ => lqNorm q (wirtQ (jac (testU n) ξ))) (ENNReal.ofReal p) volume
  set B := eLpNorm (fun ξ => lqNorm q (wirtP (jac (testU n) ξ))) (ENNReal.ofReal p) volume
  have hB : B ≠ ⊤ := by
    intro h
    rw [h, ENNReal.div_top] at hlt
    exact ENNReal.not_lt_zero hlt
  have hkey : ENNReal.ofReal C * B < A := by
    by_cases hB0 : B = 0
    · rw [hB0, mul_zero]
      rw [hB0] at hlt
      exact pos_iff_ne_zero.2 fun hA => by simp [hA] at hlt
    · exact (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hB)).1 hlt
  obtain ⟨A', hA'1, hA'2⟩ := exists_between hkey
  obtain ⟨K, hK0, hK⟩ := twoByM_gcut_bound n
  have hJ := twoByM_eLpNorm_testU_lt_top hp0 n
  set J := eLpNorm (fun x : Fin (2 * n) → ℝ => |testU n x 0| + |testU n x 1|) (ENNReal.ofReal p)
    volume
  have hjc : ∀ m : ℕ, Continuous (jac (twoByM_cut n ((m : ℝ) + 1))) := fun m =>
    twoByM_continuous_jac ((twoByM_contDiff_cut n _).of_le (by simp))
  have hcQ : ∀ m : ℕ, Continuous fun x => lqNorm q (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x)) :=
    fun m => ((twoByM_continuous_lqNorm hq0).comp (twoByM_continuous_wirtQ n)).comp (hjc m)
  have hcP : ∀ m : ℕ, Continuous fun x => lqNorm q (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) :=
    fun m => ((twoByM_continuous_lqNorm hq0).comp (twoByM_continuous_wirtP n)).comp (hjc m)
  -- Fatou: `‖Q_n (∇u_n)‖_{L^p} ≤ liminf ‖Q_n (∇φ_R)‖_{L^p}`
  have hQ : ∀ᶠ m : ℕ in atTop, A' < eLpNorm
      (fun x => lqNorm q (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x))) (ENNReal.ofReal p)
        volume := by
    have := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p) (μ := volume)
      (f := fun (m : ℕ) x => lqNorm q (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x)))
      (fun m => (hcQ m).aestronglyMeasurable) (fun x => lqNorm q (wirtQ (jac (testU n) x)))
      (twoByM_continuous_lqQ hq0).aestronglyMeasurable (Eventually.of_forall fun x =>
        tendsto_const_nhds.congr' (by
          filter_upwards [twoByM_jac_cut_eventually n x] with m hm
          rw [hm]))
    exact eventually_lt_of_lt_liminf (hA'2.trans_le this)
  -- Minkowski: `‖P_n (∇φ_R)‖_{L^p} ≤ ‖P_n (∇u_n)‖_{L^p} + (n K / R) ‖ |u_n|₁ ‖_{L^p}`
  have hcu : Continuous fun x : Fin (2 * n) → ℝ => |testU n x 0| + |testU n x 1| := by
    have h0 := (twoByM_contDiff_testU n).continuous
    exact ((continuous_apply 0).comp h0).abs.add ((continuous_apply 1).comp h0).abs
  have hPb : ∀ m : ℕ, eLpNorm (fun x => lqNorm q (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)))
      (ENNReal.ofReal p) volume ≤ B + ENNReal.ofReal (n * (((m : ℝ) + 1)⁻¹ * K)) * J := by
    intro m
    have hR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    set c : ℝ := n * (((m : ℝ) + 1)⁻¹ * K)
    have hc : 0 ≤ c := by positivity
    calc eLpNorm (fun x => lqNorm q (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)))
          (ENNReal.ofReal p) volume
        ≤ eLpNorm ((fun x => lqNorm q (wirtP (jac (testU n) x))) +
            c • fun x : Fin (2 * n) → ℝ => |testU n x 0| + |testU n x 1|) (ENNReal.ofReal p)
            volume := by
          refine eLpNorm_mono (hcP m).aestronglyMeasurable fun x => ?_
          have hb := twoByM_lqP_cut_le hq.le n hK hR x
          rw [Real.norm_of_nonneg (twoByM_lqNorm_nonneg q _), Real.norm_of_nonneg (by
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            exact add_nonneg (twoByM_lqNorm_nonneg q _) (by positivity))]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, c]
          linarith
      _ ≤ B + eLpNorm (c • fun x : Fin (2 * n) → ℝ => |testU n x 0| + |testU n x 1|)
            (ENNReal.ofReal p) volume := eLpNorm_add_le hp1
      _ = B + ENNReal.ofReal c * J := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  have hP : ∀ᶠ m : ℕ in atTop, ENNReal.ofReal C * eLpNorm
      (fun x => lqNorm q (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x))) (ENNReal.ofReal p) volume
        < A' := by
    have h1 : Tendsto (fun m : ℕ => (n : ℝ) * (((m : ℝ) + 1)⁻¹ * K)) atTop (𝓝 0) := by
      have : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simp only [one_div] at this
        exact this
      have h := (this.mul_const K).const_mul (n : ℝ)
      rwa [zero_mul, mul_zero] at h
    have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal C *
        (B + ENNReal.ofReal ((n : ℝ) * (((m : ℝ) + 1)⁻¹ * K)) * J)) atTop
        (𝓝 (ENNReal.ofReal C * B)) := by
      have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C)
        ((ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hJ.ne)).const_add B)
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h2
    filter_upwards [(tendsto_order.1 hlim).2 A' hA'1] with m hm
    exact lt_of_le_of_lt (by gcongr; exact hPb m) hm
  obtain ⟨m, hmQ, hmP⟩ := (hQ.and hP).exists
  -- `∫ F_{n,p,q,C} (∇φ_R) < 0`
  have hR : ((m : ℝ) + 1) ≠ 0 := by positivity
  refine twoByM_not_qc_of_compact (twoByM_continuous_blockF n hp0 hq0 C)
    (twoByM_blockF_zero n hp0 hq0 C) (twoByM_contDiff_cut n _)
    (twoByM_hasCompactSupport_cut n hR) ?_
  have hpowP : Continuous fun x =>
      lqNorm q (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ p :=
    (hcP m).rpow_const fun _ => Or.inr hp0.le
  have hpowQ : Continuous fun x =>
      lqNorm q (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ p :=
    (hcQ m).rpow_const fun _ => Or.inr hp0.le
  have hsP := twoByM_hasCompactSupport_comp_jac (twoByM_hasCompactSupport_cut n hR)
    (Φ := fun A => lqNorm q (wirtP A) ^ p)
    (by simp [twoByM_wirtP_zero, twoByM_lqNorm_zero hq0, Real.zero_rpow hp0.ne'])
  have hsQ := twoByM_hasCompactSupport_comp_jac (twoByM_hasCompactSupport_cut n hR)
    (Φ := fun A => lqNorm q (wirtQ A) ^ p)
    (by simp [twoByM_wirtQ_zero, twoByM_lqNorm_zero hq0, Real.zero_rpow hp0.ne'])
  have hiP := hpowP.integrable_of_hasCompactSupport (μ := volume) hsP
  have hiQ := hpowQ.integrable_of_hasCompactSupport (μ := volume) hsQ
  set IP := ∫ x, lqNorm q (wirtP (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ p
  set IQ := ∫ x, lqNorm q (wirtQ (jac (twoByM_cut n ((m : ℝ) + 1)) x)) ^ p
  have hIP0 : 0 ≤ IP := integral_nonneg fun x => Real.rpow_nonneg (twoByM_lqNorm_nonneg q _) _
  have hIQ0 : 0 ≤ IQ := integral_nonneg fun x => Real.rpow_nonneg (twoByM_lqNorm_nonneg q _) _
  have hnorm : ∀ (G : (Fin (2 * n) → ℝ) → ℝ) (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x)
      (hGi : Integrable (fun x => G x ^ p)),
      eLpNorm G (ENNReal.ofReal p) volume = ENNReal.ofReal ((∫ x, G x ^ p) ^ (1 / p)) := by
    intro G hG hG0 hGi
    rw [twoByM_eLpNorm_eq_rpow hp0 hG hG0, ← ofReal_integral_eq_lintegral_ofReal hGi
      (Eventually.of_forall fun x => Real.rpow_nonneg (hG0 x) _),
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => Real.rpow_nonneg (hG0 x) _)
        (by positivity)]
  rw [hnorm _ (hcQ m) (fun x => twoByM_lqNorm_nonneg q _) hiQ] at hmQ
  rw [hnorm _ (hcP m) (fun x => twoByM_lqNorm_nonneg q _) hiP] at hmP
  have hlt2 : C * IP ^ (1 / p) < IQ ^ (1 / p) := by
    have := hmP.trans hmQ
    rw [← ENNReal.ofReal_mul hC0] at this
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hC0 (by positivity))).1 this
  have hlt3 : C ^ p * IP < IQ := by
    have := Real.rpow_lt_rpow (mul_nonneg hC0 (by positivity)) hlt2 hp0
    rwa [Real.mul_rpow hC0 (by positivity), ← Real.rpow_mul hIP0, ← Real.rpow_mul hIQ0,
      one_div_mul_cancel hp0.ne', Real.rpow_one, Real.rpow_one] at this
  simp only [blockF]
  rw [integral_sub (hiP.const_mul _) hiQ, integral_const_mul]
  linarith

/-- **The limiting argument of Section 4.3** (`cs-sec4.3-limit`, TeX lines 1047–1053):
`‖Q_n (∇u_n)‖_{L^p (ℂ^n; ℓ_q^n)} / ‖P_n (∇u_n)‖_{L^p (ℂ^n; ℓ_q^n)} ≤ C^{qc} (p, q, n)`. The paper
writes `C^{qc}` as the supremum of this ratio over `C_c^∞` maps and notes that, "by a
straightforward limiting argument", the supremum over Schwartz maps is the same; here the
direction used is proved for the test map `u_n` (`twoByM_not_qc_blockF`: cutoff, Fatou's lemma
and Minkowski's inequality, rescaling into the unit cube). -/
theorem twoByM_ratio_le_qcThreshold {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (n : ℕ) :
    eLpNorm (fun ξ => lqNorm q (wirtQ (jac (testU n) ξ))) (ENNReal.ofReal p) volume /
        eLpNorm (fun ξ => lqNorm q (wirtP (jac (testU n) ξ))) (ENNReal.ofReal p) volume ≤
      qcThreshold (fun C => blockF n p q C) := by
  refine le_iInf₂ fun C hC => ?_
  by_contra hlt
  exact twoByM_not_qc_blockF hp hq n hC.1 (not_le.1 hlt) hC.2

/-! ### Theorem 1.2 by the route of Remark 4.5: the explicit minorant for general `p`

For `1 < p < q`, `q ≥ 2` (Remark 4.5 asks for `p + 2 < q`; the proof of Theorem 1.2 below takes
`q = p + 3`), the construction of the proof of Proposition 4.2 with Burkholder's function `u_q`
for the exponent `q` (`External.Burkholder.uq`, with (13), (14) proved in
`External.Burkholder.scalarFunctionQ_holds`): `c = (q − 1)^q`,
`R (x, y) = Σ_j (u_q (x_j, y_j) + 2 c |x_j|^q)`, `B (x) = ‖x‖_{ℓ_q}^q` (`twoByM_Bq`),
`U = R^{p/q} − K B^{p/q}` with `K = 2 (q − 1)^p (q − 1) / (p − 1)` (for `p = 3`, `q = 6`, these
are `burkholderR`, `burkholderB`, `zigzagU`, and `K = 5⁴`), and `g (A) = −U (conj (P_n A), Q_n A)`.
-/

/-- `R_q (x, y) = Σ_j (u_q (x_j, y_j) + 2 (q − 1)^q |x_j|^q)` (Remark 4.5). -/
noncomputable def twoByM_Rq {n : ℕ} (q : ℝ) (x y : Fin n → ℂ) : ℝ :=
  ∑ j, (External.Burkholder.uq q (x j) (y j) + 2 * (q - 1) ^ q * ‖x j‖ ^ q)

/-- The constant `K = 2 (q − 1)^p (q − 1) / (p − 1)` of Remark 4.5 (`5⁴` for `p = 3`, `q = 6`). -/
noncomputable def twoByM_K (p q : ℝ) : ℝ := 2 * (q - 1) ^ p * (q - 1) / (p - 1)

/-- `U (x, y) = R_q (x, y)^{p/q} − K B_q (x)^{p/q}` (Remark 4.5; (15) for `p = 3`, `q = 6`). -/
noncomputable def twoByM_Uq {n : ℕ} (p q : ℝ) (x y : Fin n → ℂ) : ℝ :=
  twoByM_Rq q x y ^ (p / q) - twoByM_K p q * twoByM_Bq q x ^ (p / q)

/-- The explicit rank-one convex minorant of Remark 4.5:
`g (A) = −U (conj (P_n (A)), Q_n (A))`. -/
noncomputable def twoByM_gq (n : ℕ) (p q : ℝ) (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) : ℝ :=
  -twoByM_Uq p q (fun j => conj (wirtP A j)) (wirtQ A)

/-- For `p = 3`, `q = 6`, `K` is the constant `5⁴` of Proposition 4.2. -/
theorem twoByM_K_three_six : twoByM_K 3 6 = 5 ^ 4 := by
  rw [twoByM_K, show (6 : ℝ) - 1 = 5 by norm_num, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  norm_num

theorem twoByM_K_pos {p q : ℝ} (hp : 1 < p) (hq : 1 < q) : 0 < twoByM_K p q := by
  unfold twoByM_K
  have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < q - 1) p
  exact div_pos (mul_pos (mul_pos two_pos this) (by linarith)) (by linarith)

/-- (18) for the exponent `q` (TeX 1317–1326 for `q = 6`): for a positive twice differentiable
`b` with `b^{1/q}` convex, differentiating `b^{1/q}` twice gives `(q − 1) b'² ≤ q b b''`. -/
theorem twoByM_eq18q {q : ℝ} (hq : 0 < q) {b b' b'' : ℝ → ℝ} (hb0 : ∀ t, 0 < b t)
    (hb : ∀ t, HasDerivAt b (b' t) t) (hb' : ∀ t, HasDerivAt b' (b'' t) t)
    (hconv : ConvexOn ℝ Set.univ fun t => b t ^ (1 / q)) (t : ℝ) :
    (q - 1) * b' t ^ 2 ≤ q * b t * b'' t := by
  obtain ⟨c', hc'd⟩ : ∃ c' : ℝ → ℝ, c' = fun t => b' t * (1 / q) * b t ^ (1 / q - 1) := ⟨_, rfl⟩
  obtain ⟨c'', hc''d⟩ : ∃ c'' : ℝ → ℝ, c'' = fun t => b'' t * (1 / q) * b t ^ (1 / q - 1) +
      b' t * (1 / q) * (b' t * (1 / q - 1) * b t ^ (1 / q - 1 - 1)) := ⟨_, rfl⟩
  have hc : ∀ t, HasDerivAt (fun t => b t ^ (1 / q)) (c' t) t := fun t => by
    rw [hc'd]; exact (hb t).rpow_const (Or.inl (hb0 t).ne')
  have hc' : ∀ t, HasDerivAt c' (c'' t) t := fun t => by
    rw [hc'd, hc''d]
    exact ((hb' t).mul_const (1 / q)).fun_mul ((hb t).rpow_const (Or.inl (hb0 t).ne'))
  -- `c'' ≥ 0`, since `c'` is the derivative of a convex function
  have hmono : Monotone c' := by
    have hd : deriv (fun t => b t ^ (1 / q)) = c' := funext fun t => (hc t).deriv
    have := hconv.monotoneOn_deriv fun t _ => (hc t).differentiableAt
    rw [hd] at this
    exact monotoneOn_univ.1 this
  have hc''0 : 0 ≤ c'' t := by
    rw [← (hc' t).deriv]; exact hmono.deriv_nonneg
  have hbt := hb0 t
  have hsplit : b t ^ (1 / q - 1) = b t ^ (1 / q - 1 - 1) * b t := by
    rw [← Real.rpow_add_one hbt.ne']; congr 1; ring
  have hpos : 0 < b t ^ (1 / q - 1 - 1) := Real.rpow_pos_of_pos hbt _
  have e : c'' t * q ^ 2 = b t ^ (1 / q - 1 - 1) * (q * b t * b'' t - (q - 1) * b' t ^ 2) := by
    rw [hc''d]
    simp only [hsplit]
    field_simp
    ring
  have : 0 ≤ b t ^ (1 / q - 1 - 1) * (q * b t * b'' t - (q - 1) * b' t ^ 2) := by
    rw [← e]; positivity
  have := (mul_nonneg_iff_of_pos_left hpos).1 this
  linarith

/-- The first two derivatives of `g^s` for a positive twice differentiable `g`. -/
theorem twoByM_rpow_hasDerivAt {g g' g'' : ℝ → ℝ} {s : ℝ} (hg0 : ∀ t, 0 < g t)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t) (t : ℝ) :
    HasDerivAt (fun t => g t ^ s) (g' t * s * g t ^ (s - 1)) t ∧
      HasDerivAt (fun t => g' t * s * g t ^ (s - 1))
        (g'' t * s * g t ^ (s - 1) + g' t * s * (g' t * (s - 1) * g t ^ (s - 1 - 1))) t :=
  ⟨(hg t).rpow_const (Or.inl (hg0 t).ne'),
    ((hg' t).mul_const s).fun_mul ((hg t).rpow_const (Or.inl (hg0 t).ne'))⟩

/-- The computation of Remark 4.5 (the analogue of `twoByM_sqrt_concave` for the exponent
`s = p/q`): for twice differentiable `r` and `b > 0` with (17) `r ≥ c b`, `r'' ≤ 2 c b''`, (18)
`(q − 1) b'² ≤ q b b''`, and `2 c^{p/q} (q − 1) ≤ K (p − 1)`, `r^{p/q} − K b^{p/q}` is concave:
`(r^s)'' ≤ s r^{s−1} r'' ≤ 2 s c^s b^{s−1} b''` (from `s < 1`, `r'' ≤ 2 c b''`, `b'' ≥ 0` and
`r ≥ c b`), and `(b^s)'' ≥ s b^{s−1} b'' (p − 1)/(q − 1)` (from `b b'' ≥ (1 − 1/q) b'²`), so the
second derivative of `r^s − K b^s` is `≤ 0`. In Remark 4.5 it is applied to `r_η`, `b_η`. -/
theorem twoByM_rpow_concave {r r' r'' b b' b'' : ℝ → ℝ} {p q c K : ℝ} (hp : 1 < p)
    (hpq : p < q) (hc : 0 < c) (hK : 2 * c ^ (p / q) * (q - 1) ≤ K * (p - 1))
    (hr : ∀ t, HasDerivAt r (r' t) t) (hr' : ∀ t, HasDerivAt r' (r'' t) t)
    (hb0 : ∀ t, 0 < b t) (hb : ∀ t, HasDerivAt b (b' t) t) (hb' : ∀ t, HasDerivAt b' (b'' t) t)
    (h17 : ∀ t, c * b t ≤ r t) (h17' : ∀ t, r'' t ≤ 2 * c * b'' t)
    (h18 : ∀ t, (q - 1) * b' t ^ 2 ≤ q * b t * b'' t) :
    ConcaveOn ℝ Set.univ fun t => r t ^ (p / q) - K * b t ^ (p / q) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  set s := p / q with hs
  have hs0 : 0 < s := div_pos (by linarith) hq0
  have hs1 : s < 1 := (div_lt_one hq0).2 hpq
  have hsq : s * q = p := by simp only [s]; field_simp
  have hcs0 : 0 < c ^ s := Real.rpow_pos_of_pos hc s
  have hK0 : 0 ≤ K := by
    have : 0 < K * (p - 1) := lt_of_lt_of_le (by positivity) hK
    exact (pos_of_mul_pos_left this (by linarith : (0 : ℝ) ≤ p - 1)).le
  have hr0 : ∀ t, 0 < r t := fun t => lt_of_lt_of_le (mul_pos hc (hb0 t)) (h17 t)
  obtain ⟨F', hF'd⟩ : ∃ F' : ℝ → ℝ,
      F' = fun t => r' t * s * r t ^ (s - 1) - K * (b' t * s * b t ^ (s - 1)) := ⟨_, rfl⟩
  obtain ⟨F'', hF''d⟩ : ∃ F'' : ℝ → ℝ, F'' = fun t =>
      (r'' t * s * r t ^ (s - 1) + r' t * s * (r' t * (s - 1) * r t ^ (s - 1 - 1))) -
        K * (b'' t * s * b t ^ (s - 1) + b' t * s * (b' t * (s - 1) * b t ^ (s - 1 - 1))) :=
    ⟨_, rfl⟩
  have hF : ∀ t, HasDerivAt (fun t => r t ^ s - K * b t ^ s) (F' t) t := fun t => by
    rw [hF'd]
    exact (twoByM_rpow_hasDerivAt hr0 hr hr' t).1.sub
      ((twoByM_rpow_hasDerivAt hb0 hb hb' t).1.const_mul _)
  have hF' : ∀ t, HasDerivAt F' (F'' t) t := fun t => by
    rw [hF'd, hF''d]
    exact (twoByM_rpow_hasDerivAt hr0 hr hr' t).2.sub
      ((twoByM_rpow_hasDerivAt hb0 hb hb' t).2.const_mul _)
  -- `F'' ≤ 0`: the computation of Remark 4.5
  have hF''0 : ∀ t, F'' t ≤ 0 := fun t => by
    have hBt := hb0 t
    have hRt := hr0 t
    have hD : 0 ≤ b'' t := by
      have h1 := h18 t
      have h2 : 0 ≤ (q - 1) * b' t ^ 2 := mul_nonneg hq1.le (sq_nonneg _)
      by_contra hneg
      push Not at hneg
      have : q * b t * b'' t < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
      linarith
    set β := b t ^ (s - 1) with hβ
    have hβ0 : 0 < β := Real.rpow_pos_of_pos hBt _
    -- the `r`-term: `(r^s)'' ≤ s r^{s−1} r'' ≤ 2 s c^s b^{s−1} b''`
    have hR1 : r t ^ (s - 1) ≤ c ^ (s - 1) * β := by
      rw [hβ, ← Real.mul_rpow hc.le hBt.le]
      exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hBt) (h17 t) (by linarith)
    have hcs : c * c ^ (s - 1) = c ^ s := by
      rw [Real.rpow_sub_one hc.ne']; field_simp
    have hX2 : r' t * s * (r' t * (s - 1) * r t ^ (s - 1 - 1)) ≤ 0 := by
      have e : r' t * s * (r' t * (s - 1) * r t ^ (s - 1 - 1)) =
          -(s * (1 - s) * (r' t ^ 2 * r t ^ (s - 1 - 1))) := by ring
      rw [e, neg_nonpos]
      exact mul_nonneg (mul_nonneg hs0.le (by linarith))
        (mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hRt _).le)
    have hX1 : r'' t * s * r t ^ (s - 1) ≤ 2 * s * c ^ s * b'' t * β := by
      have hsr : 0 ≤ s * r t ^ (s - 1) := mul_nonneg hs0.le (Real.rpow_pos_of_pos hRt _).le
      calc r'' t * s * r t ^ (s - 1) = r'' t * (s * r t ^ (s - 1)) := by ring
        _ ≤ 2 * c * b'' t * (s * r t ^ (s - 1)) := mul_le_mul_of_nonneg_right (h17' t) hsr
        _ ≤ 2 * c * b'' t * (s * (c ^ (s - 1) * β)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR1 hs0.le)
              (mul_nonneg (mul_nonneg two_pos.le hc.le) hD)
        _ = 2 * s * (c * c ^ (s - 1)) * b'' t * β := by ring
        _ = 2 * s * c ^ s * b'' t * β := by rw [hcs]
    -- the `b`-term: `(b^s)'' (q − 1) ≥ s b^{s−1} b'' (p − 1)`
    have hbs : b t ^ (s - 1 - 1) * b t = β := by
      rw [hβ, ← Real.rpow_add_one hBt.ne']; congr 1; ring
    have hY : s * b'' t * β * (p - 1) ≤
        (b'' t * s * β + b' t * s * (b' t * (s - 1) * b t ^ (s - 1 - 1))) * (q - 1) := by
      have hb2 : 0 < b t ^ (s - 1 - 1) := Real.rpow_pos_of_pos hBt _
      -- `(1 − s) s b'² b^{s−2} (q − 1) ≤ (1 − s) s q b'' b^{s−1}`
      have h1 : s * (1 - s) * b t ^ (s - 1 - 1) * ((q - 1) * b' t ^ 2) ≤
          s * (1 - s) * b t ^ (s - 1 - 1) * (q * b t * b'' t) :=
        mul_le_mul_of_nonneg_left (h18 t) (mul_nonneg (mul_nonneg hs0.le (by linarith)) hb2.le)
      have e1 : s * (1 - s) * b t ^ (s - 1 - 1) * (q * b t * b'' t) =
          s * (1 - s) * q * b'' t * β := by rw [← hbs]; ring
      have e2 : (b'' t * s * β + b' t * s * (b' t * (s - 1) * b t ^ (s - 1 - 1))) * (q - 1) =
          s * b'' t * β * (q - 1) -
            s * (1 - s) * b t ^ (s - 1 - 1) * ((q - 1) * b' t ^ 2) := by ring
      have e3 : s * b'' t * β * (p - 1) =
          s * b'' t * β * (q - 1) - s * (1 - s) * q * b'' t * β := by
        rw [← hsq]; ring
      rw [e2, e3]
      linarith
    -- assemble: `F'' (q − 1) ≤ s b'' b^{s−1} (2 c^s (q − 1) − K (p − 1)) ≤ 0`
    have hsDβ : 0 ≤ s * b'' t * β := by positivity
    have hfin : F'' t * (q - 1) ≤ 0 := by
      have e : F'' t * (q - 1) =
          (r'' t * s * r t ^ (s - 1) + r' t * s * (r' t * (s - 1) * r t ^ (s - 1 - 1))) * (q - 1)
            - K * ((b'' t * s * β + b' t * s * (b' t * (s - 1) * b t ^ (s - 1 - 1))) *
              (q - 1)) := by
        rw [hF''d]; ring
      have h1 : (r'' t * s * r t ^ (s - 1) + r' t * s * (r' t * (s - 1) * r t ^ (s - 1 - 1))) *
          (q - 1) ≤ 2 * s * c ^ s * b'' t * β * (q - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hq1.le
      have h2 : K * (s * b'' t * β * (p - 1)) ≤
          K * ((b'' t * s * β + b' t * s * (b' t * (s - 1) * b t ^ (s - 1 - 1))) * (q - 1)) :=
        mul_le_mul_of_nonneg_left hY hK0
      have h3 : s * b'' t * β * (2 * c ^ s * (q - 1)) ≤ s * b'' t * β * (K * (p - 1)) :=
        mul_le_mul_of_nonneg_left hK hsDβ
      rw [e]
      nlinarith
    exact nonpos_of_mul_nonpos_left hfin hq1
  exact concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
    (fun t _ => (hF t).continuousAt.continuousWithinAt) (fun t _ => (hF t).hasDerivWithinAt)
    (fun t _ => (hF' t).hasDerivWithinAt) fun t _ => hF''0 t

theorem twoByM_continuous_Rq {q : ℝ} (hq : 1 ≤ q) (n : ℕ) :
    Continuous fun z : (Fin n → ℂ) × (Fin n → ℂ) => twoByM_Rq q z.1 z.2 := by
  have hq0 : 0 < q := by linarith
  have hnorm : ∀ j : Fin n, Continuous fun z : (Fin n → ℂ) × (Fin n → ℂ) => ‖z.1 j‖ ^ q :=
    fun j => ((continuous_apply j).comp continuous_fst).norm.rpow_const fun _ => Or.inr hq0.le
  unfold twoByM_Rq
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((External.Burkholder.continuous_uq hq).comp
    (((continuous_apply j).comp continuous_fst).prodMk
      ((continuous_apply j).comp continuous_snd))).add (continuous_const.mul (hnorm j))

theorem twoByM_continuous_Uq {p q : ℝ} (hp : 0 < p) (hq : 1 ≤ q) (n : ℕ) :
    Continuous fun z : (Fin n → ℂ) × (Fin n → ℂ) => twoByM_Uq p q z.1 z.2 := by
  have hq0 : 0 < q := by linarith
  have hs : 0 ≤ p / q := by positivity
  have hnorm : ∀ j : Fin n, Continuous fun z : (Fin n → ℂ) × (Fin n → ℂ) => ‖z.1 j‖ ^ q :=
    fun j => ((continuous_apply j).comp continuous_fst).norm.rpow_const fun _ => Or.inr hq0.le
  have hB : Continuous fun z : (Fin n → ℂ) × (Fin n → ℂ) => twoByM_Bq q z.1 := by
    unfold twoByM_Bq; exact continuous_finsetSum _ fun j _ => hnorm j
  unfold twoByM_Uq
  exact ((twoByM_continuous_Rq hq n).rpow_const fun _ => Or.inr hs).sub
    (continuous_const.mul (hB.rpow_const fun _ => Or.inr hs))

open ContinuousLinearMap in
open scoped Convolution in
/-- **Zig-zag concavity of `U`** (Remark 4.5, the analogue of `twoByM_zigzag`): for
`x, y, h ∈ ℂ^n` and `|ε| ≤ 1`, `t ↦ U (x + t h, y + t ε h)` is concave.

Proof, the proof of Proposition 4.2 (TeX 1286–1352) with the exponent `q`. If `x = h = 0` the
function is constant. Otherwise, with `b (t) = B_q (x + t h)`, `r (t) = R_q (x + t h, y + t ε h)`
and `c = (q − 1)^q`: `r − 2 c b = Σ_j u_q (x_j + t h_j, y_j + t ε h_j)` is concave by (14) and
`r ≥ c b` by (13) (`External.Burkholder.scalarFunctionQ_holds`). For every mollifier `ρ_η`, `r_η`
and `b_η` satisfy (17) (`twoByM_eq17`), `b_η^{1/q}` is convex (`twoByM_convexOn_mollify_Bq`) and
`b_η > 0` (`twoByM_mollify_Bq_pos`), so (18) `(q − 1) b_η'² ≤ q b_η b_η''` holds
(`twoByM_eq18q`), and the computation `twoByM_rpow_concave` makes `r_η^{p/q} − K b_η^{p/q}`
concave. Letting `η ↓ 0` (`twoByM_concaveOn_of_mollify`) gives the concavity of
`r^{p/q} − K b^{p/q} = U (x + t h, y + t ε h)`. -/
theorem twoByM_zigzagq {p q : ℝ} (hp : 1 < p) (hpq : p < q) (hq2 : 2 ≤ q) {n : ℕ}
    (x y h : Fin n → ℂ) {ε : ℂ} (hε : ‖ε‖ ≤ 1) :
    ConcaveOn ℝ Set.univ fun t : ℝ =>
      twoByM_Uq p q (fun j => x j + t * h j) (fun j => y j + t * ε * h j) := by
  by_cases hxh : x = 0 ∧ h = 0
  · obtain ⟨rfl, rfl⟩ := hxh
    have : (fun t : ℝ => twoByM_Uq p q (fun j => (0 : Fin n → ℂ) j + (t : ℂ) * (0 : Fin n → ℂ) j)
        (fun j => y j + (t : ℂ) * ε * (0 : Fin n → ℂ) j)) = fun _ => twoByM_Uq p q 0 y := by
      funext t
      congr 1 <;> funext j <;> simp
    rw [this]
    exact concaveOn_const _ convex_univ
  have hBq := External.Burkholder.scalarFunctionQ_holds hq2
  have hq0 : 0 < q := by linarith
  have hc0 : 0 < (q - 1) ^ q := Real.rpow_pos_of_pos (by linarith) q
  have hs : 0 ≤ p / q := by positivity
  -- `b (t) = B_q (x + t h)` and `r (t) = R_q (x + t h, y + t ε h)`
  set b : ℝ → ℝ := fun t => twoByM_Bq q fun j => x j + t * h j with hb_def
  set r : ℝ → ℝ := fun t =>
    twoByM_Rq q (fun j => x j + t * h j) (fun j => y j + t * ε * h j) with hr_def
  have hb : Continuous b := twoByM_continuous_Bq_line hq0.le x h
  have hr : Continuous r := (twoByM_continuous_Rq (by linarith) n).comp
    (f := fun t : ℝ => ((fun j => x j + (t : ℂ) * h j), (fun j => y j + (t : ℂ) * ε * h j)))
    (by fun_prop)
  -- `r − 2 c b = Σ_j u_q (x_j + t h_j, y_j + t ε h_j)`
  have hrκ : ∀ t, r t - 2 * (q - 1) ^ q * b t =
      ∑ j, External.Burkholder.uq q (x j + t * h j) (y j + t * ε * h j) := fun t => by
    simp only [hr_def, hb_def, twoByM_Rq, twoByM_Bq, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  -- (14): `r − 2 c b` is concave
  have hκ : ConcaveOn ℝ Set.univ fun t => r t - 2 * (q - 1) ^ q * b t := by
    simp only [hrκ]
    exact twoByM_concaveOn_sum _ fun j _ => hBq.2 (x j) (y j) (h j) ε hε
  -- (13): `r ≥ c b`
  have hrb : ∀ t, (q - 1) ^ q * b t ≤ r t := fun t => by
    have : -((q - 1) ^ q * b t) ≤ r t - 2 * (q - 1) ^ q * b t := by
      rw [hrκ]
      simp only [hb_def, twoByM_Bq, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have := hBq.1 (x j + t * h j) (y j + t * ε * h j)
      have : 0 ≤ ‖y j + t * ε * h j‖ ^ q := by positivity
      linarith
    linarith
  have hK : 2 * ((q - 1) ^ q) ^ (p / q) * (q - 1) ≤ twoByM_K p q * (p - 1) := by
    rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ q - 1), show q * (p / q) = p by field_simp,
      twoByM_K, div_mul_cancel₀ _ (by linarith : p - 1 ≠ 0)]
  change ConcaveOn ℝ Set.univ fun t => r t ^ (p / q) - twoByM_K p q * b t ^ (p / q)
  refine twoByM_concaveOn_of_mollify (Φ := fun r b => r ^ (p / q) - twoByM_K p q * b ^ (p / q))
    hr hb ((continuous_fst.rpow_const fun _ => Or.inr hs).sub
      (continuous_const.mul (continuous_snd.rpow_const fun _ => Or.inr hs))) fun φ => ?_
  -- the mollifications `r_η`, `b_η`: smooth, (17), `b_η > 0`, convexity of `b_η^{1/q}` and (18)
  have hR := twoByM_hasDerivAt_deriv
    (φ.contDiff_normed_convolution (μ := volume) hr.locallyIntegrable)
  have hB := twoByM_hasDerivAt_deriv
    (φ.contDiff_normed_convolution (μ := volume) hb.locallyIntegrable)
  have hb0 := twoByM_mollify_Bq_pos hq0 hxh φ
  have h17 := twoByM_eq17 hr hb hκ hrb φ
  have h18 := twoByM_eq18q hq0 hb0 (fun t => (hB t).1) (fun t => (hB t).2)
    (twoByM_convexOn_mollify_Bq (by linarith) x h φ)
  -- the computation of Remark 4.5: `r_η^{p/q} − K b_η^{p/q}` is concave
  exact twoByM_rpow_concave hp hpq hc0 hK (fun t => (hR t).1) (fun t => (hR t).2) hb0
    (fun t => (hB t).1) (fun t => (hB t).2) (fun t => (h17 t).1) (fun t => (h17 t).2) h18

/-- `B_q (y) ≤ R_q (x, y)`, by (13). -/
theorem twoByM_Bq_le_Rq {q : ℝ} (hq : 2 ≤ q) {n : ℕ} (x y : Fin n → ℂ) :
    twoByM_Bq q y ≤ twoByM_Rq q x y := by
  have hB := External.Burkholder.scalarFunctionQ_holds hq
  unfold twoByM_Bq twoByM_Rq
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := hB.1 (x j) (y j)
  have h2 : 0 ≤ (q - 1) ^ q * ‖x j‖ ^ q :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity)
  linarith

theorem twoByM_Rq_nonneg {q : ℝ} (hq : 2 ≤ q) {n : ℕ} (x y : Fin n → ℂ) : 0 ≤ twoByM_Rq q x y :=
  (twoByM_Bq_nonneg q y).trans (twoByM_Bq_le_Rq hq x y)

/-- (16) for Remark 4.5: `U (x, y) ≥ ‖y‖_q^p − K ‖x‖_q^p`, from (13). -/
theorem twoByM_Uq_majorization {p q : ℝ} (hp : 0 < p) (hq : 2 ≤ q) {n : ℕ} (x y : Fin n → ℂ) :
    lqNorm q y ^ p - twoByM_K p q * lqNorm q x ^ p ≤ twoByM_Uq p q x y := by
  have hq0 : 0 < q := by linarith
  rw [twoByM_lqNorm_rpow, twoByM_lqNorm_rpow, twoByM_Uq]
  have := Real.rpow_le_rpow (twoByM_Bq_nonneg q y) (twoByM_Bq_le_Rq hq x y)
    (by positivity : 0 ≤ p / q)
  linarith

/-- `U` is `p`-homogeneous. -/
theorem twoByM_Uq_smul {p q : ℝ} (hq : 2 ≤ q) {n : ℕ} (t : ℝ) (x y : Fin n → ℂ) :
    twoByM_Uq p q (fun j => (t : ℂ) * x j) (fun j => (t : ℂ) * y j) =
      |t| ^ p * twoByM_Uq p q x y := by
  have hq0 : 0 < q := by linarith
  have hn : ∀ z : ℂ, ‖(t : ℂ) * z‖ ^ q = |t| ^ q * ‖z‖ ^ q := fun z => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg t) (norm_nonneg z)]
  have hR : twoByM_Rq q (fun j => (t : ℂ) * x j) (fun j => (t : ℂ) * y j) =
      |t| ^ q * twoByM_Rq q x y := by
    simp only [twoByM_Rq, External.Burkholder.uq_smul (by linarith : (1 : ℝ) ≤ q), hn,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hB : twoByM_Bq q (fun j => (t : ℂ) * x j) = |t| ^ q * twoByM_Bq q x := by
    simp only [twoByM_Bq, hn, Finset.mul_sum]
  have hpow : (|t| ^ q) ^ (p / q) = |t| ^ p := by
    rw [← Real.rpow_mul (abs_nonneg t)]; congr 1; field_simp
  rw [twoByM_Uq, twoByM_Uq, hR, hB, Real.mul_rpow (by positivity) (twoByM_Rq_nonneg hq x y),
    Real.mul_rpow (by positivity) (twoByM_Bq_nonneg q x), hpow]
  ring

theorem twoByM_continuous_gq (n : ℕ) {p q : ℝ} (hp : 0 < p) (hq : 1 ≤ q) :
    Continuous (twoByM_gq n p q) := by
  have hP : Continuous fun A : Matrix (Fin 2) (Fin (2 * n)) ℝ => fun j => conj (wirtP A j) :=
    continuous_pi fun j => Complex.continuous_conj.comp
      ((continuous_apply j).comp (twoByM_continuous_wirtP n))
  exact ((twoByM_continuous_Uq hp hq n).comp (hP.prodMk (twoByM_continuous_wirtQ n))).neg

/-- `g` is `p`-homogeneous. -/
theorem twoByM_isPHomogeneous_gq (n : ℕ) {p q : ℝ} (hq : 2 ≤ q) :
    IsPHomogeneous p (twoByM_gq n p q) := by
  intro t A
  rw [twoByM_gq, twoByM_gq, twoByM_wirtQ_smul, twoByM_wirtP_smul]
  have : (fun j => conj ((t : ℂ) * wirtP A j)) = fun j => (t : ℂ) * conj (wirtP A j) := by
    funext j; rw [map_mul, Complex.conj_ofReal]
  rw [this, twoByM_Uq_smul hq]
  ring

/-- `g` is rank-one convex: along `B + t R`, `rank R = 1`, Lemma 4.1 gives
`Q_n R = λ conj (P_n R)` with `|λ| = 1`, so `g = −U (x + t h, y + t λ h)`, which is convex by the
zig-zag concavity of `U` (`twoByM_zigzagq`). -/
theorem twoByM_rankOneConvex_gq (n : ℕ) {p q : ℝ} (hp : 1 < p) (hpq : p < q) (hq : 2 ≤ q) :
    RankOneConvex (twoByM_gq n p q) := by
  intro A B hAB
  set R := A - B
  have hR : R.rank ≤ 1 := hAB.le
  -- Lemma 4.1: `Q_n R = λ conj (P_n R)` with `|λ| = 1`
  obtain ⟨lam, -, hlam⟩ := lemma4_1 n
  obtain ⟨hlam1, hlamQ, -⟩ := hlam R hR
  have hline : ∀ t : ℝ, t • A + (1 - t) • B = B + t • R := fun t => by
    simp only [R]; module
  have key : (fun t : ℝ => twoByM_gq n p q (t • A + (1 - t) • B)) = fun t : ℝ =>
      -twoByM_Uq p q (fun j => conj (wirtP B j) + t * conj (wirtP R j))
        (fun j => wirtQ B j + t * lam R * conj (wirtP R j)) := by
    funext t
    rw [hline, twoByM_gq]
    congr 2
    · funext j
      rw [twoByM_wirtP_add, twoByM_wirtP_smul, Pi.add_apply, map_add, map_mul,
        Complex.conj_ofReal]
    · funext j
      rw [twoByM_wirtQ_add, twoByM_wirtQ_smul, Pi.add_apply, hlamQ j, mul_assoc]
  rw [key]
  exact (twoByM_zigzagq hp hpq hq _ _ _ hlam1.le).neg.subset (Set.subset_univ _)
    (convex_Icc 0 1)

/-- `g ≤ F_{n,p,q,K^{1/p}}`, from (16). -/
theorem twoByM_gq_le_blockF (n : ℕ) {p q : ℝ} (hp : 1 < p) (hq : 2 ≤ q)
    (A : Matrix (Fin 2) (Fin (2 * n)) ℝ) :
    twoByM_gq n p q A ≤ blockF n p q (twoByM_K p q ^ (1 / p)) A := by
  have hK := (twoByM_K_pos hp (by linarith : (1 : ℝ) < q)).le
  have hC : (twoByM_K p q ^ (1 / p)) ^ p = twoByM_K p q := by
    rw [← Real.rpow_mul hK, one_div_mul_cancel (by linarith : p ≠ 0), Real.rpow_one]
  have := twoByM_Uq_majorization (p := p) (by linarith) hq (fun j => conj (wirtP A j)) (wirtQ A)
  rw [twoByM_lqNorm_conj] at this
  rw [twoByM_gq, blockF, hC]
  linarith

theorem twoByM_gq_zero (n : ℕ) {p q : ℝ} (hp : 0 < p) (hq : 1 ≤ q) : twoByM_gq n p q 0 = 0 := by
  have hq0 : q ≠ 0 := by positivity
  have hs : p / q ≠ 0 := div_ne_zero hp.ne' hq0
  simp [twoByM_gq, twoByM_Uq, twoByM_Rq, twoByM_Bq, External.Burkholder.uq, twoByM_wirtP_zero,
    twoByM_wirtQ_zero, Real.zero_rpow hq0, Real.zero_rpow hs]

/-- Remark 4.5, the claim of the generalized proof of Proposition 4.2: for `1 < p < q`, `q ≥ 2`,
`g` is a continuous, `p`-homogeneous, globally rank-one convex integrand with
`g ≤ F_{n,p,q,K^{1/p}}` and `g (0) = 0`. -/
theorem twoByM_explicit_minorant_q (n : ℕ) {p q : ℝ} (hp : 1 < p) (hpq : p < q) (hq : 2 ≤ q) :
    Continuous (twoByM_gq n p q) ∧ IsPHomogeneous p (twoByM_gq n p q) ∧
      RankOneConvex (twoByM_gq n p q) ∧
      (∀ A, twoByM_gq n p q A ≤ blockF n p q (twoByM_K p q ^ (1 / p)) A) ∧
      twoByM_gq n p q 0 = 0 :=
  ⟨twoByM_continuous_gq n (by linarith) (by linarith), twoByM_isPHomogeneous_gq n hq,
    twoByM_rankOneConvex_gq n hp hpq hq, twoByM_gq_le_blockF n hp hq,
    twoByM_gq_zero n (by linarith) (by linarith)⟩

/-! ### A minorant touching at `A` passes quasiconvexity at `A` upwards -/

/-- If a continuous `g ≤ f` touches `f` at `A` and is quasiconvex at `A`, then so is `f`:
`f (A) = g (A) ≤ ∫ g (A + ∇φ) ≤ ∫ f (A + ∇φ)` (the integral of `g (A + ∇φ)` exists since `g` is
continuous and `∇φ` is bounded). The direct form, without envelopes, of the step
`g_n (0) = g_n^{qc} (0) ≤ f_n^{qc} (0)` of the proof of Proposition 4.3: a simpler argument,
recorded for the report and used by no proof, which follow the paper's. -/
theorem twoByM_quasiconvexAt_of_minorant {d m : ℕ} {f g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hg : Continuous g) (hgf : ∀ B, g B ≤ f B) {A : Matrix (Fin d) (Fin m) ℝ} (hA : g A = f A)
    (hq : QuasiconvexAt g A) : QuasiconvexAt f A := by
  intro φ K hφ h0 hint
  have hgint := integrableOn_comp_jac hg A hφ
  rw [← hA]
  exact (hq φ K hφ h0 hgint).trans (setIntegral_mono hgint hint fun x => hgf _)


/-- **Theorem 1.2, elementary route** (`cs-thm1.2-elementary`): for `p ∈ (1, ∞)` there is `m₀ (p)`
such that for every `m ≥ m₀ (p)` there is a `p`-homogeneous, rank-one convex and nowhere
quasiconvex integrand `f : ℝ^{2×m} → ℝ`. The statement of `theorem1_2`, proved a second time, by
the route of the paper's Remark 4.5 ("an entirely elementary (if more inscrutable) proof of
Theorem 1.2"): Burkholder's scalar function `u_q` in place of the UMD constants that the paper's
own proof (Section 4.4, `theorem1_2`) uses through Proposition 4.1 and (10). Remark 4.5 only
sketches this route ("the argument can be extended to general `1 < p < ∞`, `p + 2 < q < ∞`, where
such a `U` can also be constructed"); the formal proof makes it explicit as follows.

Proof. `q = p + 3`, `K = 2 (q − 1)^p (q − 1) / (p − 1)`, `C = K^{1/p}`.
* By Lemma 4.2 (`lemma4_2`, `q ≥ p + 2`) and the limiting argument of Section 4.3
  (`twoByM_ratio_le_qcThreshold`) there is `n₀` with `C < C^{qc} (p, q, n₀)`, so `F_{n₀,p,q,C}` is
  not quasiconvex at `0`, as in the paper's proof.
* The proof of Proposition 4.2 with `u_q` in place of `u` (Remark 4.5): `U = R^{p/q} − K B^{p/q}`,
  `g (A) = −U (conj (P_{n₀} A), Q_{n₀} A)` is a continuous, `p`-homogeneous, globally rank-one
  convex integrand with `g ≤ F_{n₀,p,q,C}` and `g (0) = 0` (`twoByM_explicit_minorant_q`: (13),
  (14) for `u_q`, `External.Burkholder.scalarFunctionQ_holds`; Lemma 4.1; the zig-zag concavity of
  `U`, `twoByM_zigzagq`, regularized by mollification as in the paper (TeX 1299–1351): (17) for
  `r_η`, `b_η` (`twoByM_eq17`), the convexity of `b_η^{1/q}` by Minkowski's inequality
  (`twoByM_convexOn_mollify_Bq`), (18) for `b_η` (`twoByM_eq18q`), the computation
  `twoByM_rpow_concave` for `r_η^{p/q} − K b_η^{p/q}`, and `η ↓ 0`
  (`twoByM_concaveOn_of_mollify`)).
* As in Proposition 4.3, `g` is not quasiconvex at `0`: otherwise `F_{n₀,p,q,C}` would be, by the
  paper's argument through quasiconvex minorants (line 559, `quasiconvexAt_iff_exists_minorant`,
  from Dacorogna's formula). Being `p`-homogeneous and continuous, `g` is nowhere quasiconvex
  (`nowhereQuasiconvex_of_not_quasiconvexAt_zero`). No envelope is needed: `g` is already
  globally rank-one convex, so `f = g` for `m₀ = 2 n₀` (the paper takes `f = F^{rc}`).
* For `m ≥ m₀`, `f ∘ π` with the projection `π` onto the first `m₀` columns, as in the paper; a
  witness for `f` lifts to one for `f ∘ π` (`lift_quasiconvexAt_of_comp_trunc`, Lemma 2.2). -/
theorem theorem1_2_elementary {p : ℝ} (hp : 1 < p) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ f : Matrix (Fin 2) (Fin m) ℝ → ℝ,
      IsIntegrand f ∧ IsPHomogeneous p f ∧ RankOneConvex f ∧ NowhereQuasiconvex f := by
  -- `q = p + 3 > p + 2` and `C = K^{1/p}`
  set q := p + 3 with hqdef
  have hq : 1 < q := by linarith
  have hq2 : 2 ≤ q := by linarith
  have hpq : p < q := by linarith
  set C := twoByM_K p q ^ (1 / p) with hCdef
  have hC0 : 0 ≤ C := Real.rpow_nonneg (twoByM_K_pos hp hq).le _
  -- by (12) and Section 4.3, `n₀` with `C < C^{qc} (p, q, n₀)`: `F_{n₀,p,q,C}` is not
  -- quasiconvex at `0`
  obtain ⟨n₀, hn₀⟩ := ((lemma4_2 (q := q) hp (by linarith)).eventually
    (lt_mem_nhds (ENNReal.ofReal_lt_top (r := C)))).exists
  have hnq : ¬ QuasiconvexAt (blockF n₀ p q C) 0 :=
    not_quasiconvexAt_of_lt_qcThreshold (F := fun C => blockF n₀ p q C) hC0
      (hn₀.trans_le (twoByM_ratio_le_qcThreshold hp hq n₀))
  -- the explicit rank-one convex minorant `g` of Remark 4.5
  obtain ⟨hcont, hhom, hrc, hle, hg0⟩ := twoByM_explicit_minorant_q n₀ hp hpq hq2
  -- as in Proposition 4.3: if `g` were quasiconvex at `0`, a quasiconvex minorant `g'` of `g`
  -- touching it at `0` (line 559) would be one of `F` touching it at `0`, so `F` would be too
  have hgnq : ¬ QuasiconvexAt (twoByM_gq n₀ p q) 0 := fun h => by
    obtain ⟨g', hg'i, hg'q, hg'le, hg'0⟩ := (quasiconvexAt_iff_exists_minorant hcont 0).1 h
    exact hnq ((quasiconvexAt_iff_exists_minorant
      (twoByM_continuous_blockF n₀ (by linarith) (by linarith) C) 0).2
      ⟨g', hg'i, hg'q, fun B => (hg'le B).trans (hle B), by
        rw [hg'0, hg0, twoByM_blockF_zero n₀ (by linarith) (by linarith)]⟩)
  have hN := nowhereQuasiconvex_of_not_quasiconvexAt_zero hp hcont (Or.inl hhom) hgnq
  have hI : IsIntegrand (twoByM_gq n₀ p q) := isIntegrand_of_continuous hcont
  -- lifted to `ℝ^{2×m}` by the projection onto the first `2 n₀` columns
  refine ⟨2 * n₀, fun m hm => ⟨fun A => twoByM_gq n₀ p q (lift_trunc le_rfl hm A),
    lift_isIntegrand_comp le_rfl hm hI, fun t A => ?_, lift_rankOneConvex_comp le_rfl hm hrc,
    fun A hA => hN _ (lift_quasiconvexAt_of_comp_trunc le_rfl hm hI hA)⟩⟩
  change twoByM_gq n₀ p q (lift_trunc le_rfl hm (t • A)) =
    |t| ^ p * twoByM_gq n₀ p q (lift_trunc le_rfl hm A)
  rw [lift_trunc_smul]
  exact hhom t _

end Cassese
