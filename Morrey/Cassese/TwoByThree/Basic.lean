module

public import Morrey.Cassese.Toolkit
public import Morrey.Cassese.TwoByM
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Section 5: the algebra of the `2 × 3` quartic

The objects of Sections 5.1–5.2 that Corollary 5.3 names (`wirtAlpha`, `wirtBeta`, `zCoord`,
`quarticQ`, `calL`, `embedJ`, `L3`, `q3`, `projL3`, `qDeltaLambda`, `qHat`) are in the shared block
of `Morrey/Cassese/Defs.lean`. In this section `|·|` is the Frobenius norm (`frobNorm`) and
`⟨A, B⟩ = Σ A_{ij} B_{ij}` the Frobenius inner product (`frobInner`).

This module holds the definitions of Section 5 that are not shared (`frobInner`, `frobNorm`,
`IsFrobProj`, `HasRankOneCorrection`, `L3Submodule`), and the algebraic statements:

* `quarticQ_rankOneConvexOn_calL` (`cs-q-rc`) and `q3_rankOneConvexOn_L3` (`cs-q3-rc`), from
  Lemma 4.1 through the cancellation of (21) and the subordination (22);
* `equation24` (`eq:q-simp`);
* `L3_rankOneCorrection` (`cs-kappa`), which the paper asserts without proof.

Helpers are prefixed `tbt_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal ComplexConjugate

namespace Cassese

variable {d m : ℕ}

/-- The Frobenius inner product `⟨A, B⟩ = Σ A_{ij} B_{ij}`. -/
def frobInner (A B : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- The Frobenius norm `|A| = (Σ A_{ij}²)^{1/2}`. -/
noncomputable def frobNorm (A : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  √(frobSq A)

/-- `π` is the orthogonal projection onto `L` for the Frobenius inner product: `π A ∈ L` and
`A − π A ⊥ L` for every `A`. -/
def IsFrobProj (L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ))
    (π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ) : Prop :=
  ∀ A, π A ∈ L ∧ ∀ B ∈ L, frobInner (A - π A) B = 0

/-- Hypothesis (25) of Lemma 5.1: for every rank-one `R` there is a rank-one `R_L ∈ L` with
`|π R − R_L| ≤ κ |π^⊥ R|`. -/
def HasRankOneCorrection (L : Submodule ℝ (Matrix (Fin d) (Fin m) ℝ))
    (π : Matrix (Fin d) (Fin m) ℝ → Matrix (Fin d) (Fin m) ℝ) (κ : ℝ) : Prop :=
  ∀ R : Matrix (Fin d) (Fin m) ℝ, R.rank = 1 →
    ∃ RL ∈ L, RL.rank = 1 ∧ frobNorm (π R - RL) ≤ κ * frobNorm (R - π R)

/-- `projL3 A` lies in `𝓛₃`. -/
theorem projL3_mem (A : Matrix (Fin 2) (Fin 3) ℝ) : projL3 A ∈ L3 := by
  show wirtBeta (embedJ (projL3 A)) 2 3 = starRingEnd ℂ (wirtAlpha (embedJ (projL3 A)) 0 1)
  simp only [embedJ, projL3, wirtBeta, wirtAlpha, Matrix.of_apply]
  rw [Complex.ext_iff]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  norm_num
  constructor <;> ring

/-- `A − projL3 A` is orthogonal to `𝓛₃`: `projL3` is the orthogonal projection onto `𝓛₃`. -/
theorem projL3_orthogonal (A B : Matrix (Fin 2) (Fin 3) ℝ) (hB : B ∈ L3) :
    frobInner (A - projL3 A) B = 0 := by
  change wirtBeta (embedJ B) 2 3 = starRingEnd ℂ (wirtAlpha (embedJ B) 0 1) at hB
  simp only [embedJ, wirtBeta, wirtAlpha, Matrix.of_apply] at hB
  rw [Complex.ext_iff] at hB
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im] at hB
  norm_num at hB
  obtain ⟨h1, h2⟩ := hB
  simp [frobInner, projL3, Fin.sum_univ_succ]
  linear_combination (A 0 2 - A 0 0 - A 1 1) / 3 * h1 + 2 * ((A 1 2 - A 0 1 + A 1 0) / 3) * h2

/-- `A = (a b e; c d f)` lies in `𝓛₃` exactly when `e = a + d` and `f = b − c`. -/
theorem mem_L3_iff (A : Matrix (Fin 2) (Fin 3) ℝ) :
    A ∈ L3 ↔ A 0 2 = A 0 0 + A 1 1 ∧ A 1 2 = A 0 1 - A 1 0 := by
  change wirtBeta (embedJ A) 2 3 = starRingEnd ℂ (wirtAlpha (embedJ A) 0 1) ↔ _
  simp only [embedJ, wirtBeta, wirtAlpha, Matrix.of_apply]
  rw [Complex.ext_iff]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  constructor
  · rintro ⟨h1, h2⟩
    norm_num at h1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    norm_num
    constructor <;> linarith

/-- The subspace `𝓛₃` as a submodule of `ℝ^{2×3}`, with carrier `L3` (`coe_L3Submodule`), so
that Lemma 5.1, which takes a submodule, applies to it. -/
def L3Submodule : Submodule ℝ (Matrix (Fin 2) (Fin 3) ℝ) where
  carrier := L3
  add_mem' {A B} hA hB := by
    rw [mem_L3_iff] at hA hB ⊢
    simp only [Matrix.add_apply]
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  zero_mem' := by
    rw [mem_L3_iff]
    simp
  smul_mem' c A hA := by
    rw [mem_L3_iff] at hA ⊢
    simp only [Matrix.smul_apply, smul_eq_mul, hA.1, hA.2]
    constructor <;> ring

/-- The carrier of `L3Submodule` is `L3`. -/
theorem coe_L3Submodule : (L3Submodule : Set (Matrix (Fin 2) (Fin 3) ℝ)) = L3 := rfl

theorem mem_L3Submodule {A : Matrix (Fin 2) (Fin 3) ℝ} : A ∈ L3Submodule ↔ A ∈ L3 := Iff.rfl

/-- `projL3` is the orthogonal projection onto `𝓛₃`, in the sense of Lemma 5.1. -/
theorem isFrobProj_projL3 : IsFrobProj L3Submodule projL3 :=
  fun A => ⟨projL3_mem A, fun B hB => projL3_orthogonal A B hB⟩

/-- A matrix of rank at most one is an outer product `v wᵀ`. -/
theorem tbt_exists_vecMulVec {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ) (h : R.rank ≤ 1) :
    ∃ v : Fin n → ℝ, ∃ w : Fin k → ℝ, R = Matrix.vecMulVec v w := by
  rw [Matrix.rank_eq_finrank_span_row] at h
  obtain ⟨w0, hw0⟩ := finrank_le_one_iff.mp h
  have hmem : ∀ i, R.row i ∈ Submodule.span ℝ (Set.range R.row) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  choose c hc using fun i => hw0 ⟨R.row i, hmem i⟩
  refine ⟨c, (w0 : Fin k → ℝ), ?_⟩
  ext i j
  have := congrArg (fun x : Submodule.span ℝ (Set.range R.row) => (x : Fin k → ℝ) j) (hc i)
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.vecMulVec_apply, this, Matrix.row_apply]

/-- A matrix of rank `0` is `0`. -/
theorem tbt_eq_zero_of_rank_eq_zero {n k : ℕ} (R : Matrix (Fin n) (Fin k) ℝ) (h : R.rank = 0) :
    R = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero] at h
  ext i j
  have : R.mulVecLin (Pi.single j 1) ∈ LinearMap.range R.mulVecLin := ⟨_, rfl⟩
  rw [h, Submodule.mem_bot] at this
  have := congrFun this i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using this

/-- An outer product of nonzero vectors has rank one. -/
theorem tbt_rank_vecMulVec {n k : ℕ} {v : Fin n → ℝ} {w : Fin k → ℝ} (hv : v ≠ 0) (hw : w ≠ 0) :
    (Matrix.vecMulVec v w).rank = 1 := by
  have h1 := Matrix.rank_vecMulVec_le v w
  rcases Nat.lt_or_ge (Matrix.vecMulVec v w).rank 1 with h | h
  · have h0 : (Matrix.vecMulVec v w).rank = 0 := by omega
    have := tbt_eq_zero_of_rank_eq_zero _ h0
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
    have := congrFun (congrFun this i) j
    simp [Matrix.vecMulVec_apply] at this
    tauto
  · omega

/-- `D (z) = z₀ z₂ − z₁²` (Section 5.1). -/
noncomputable def tbtD (z : Fin 3 → ℂ) : ℂ := z 0 * z 2 - z 1 ^ 2

/-- `H (z) = |z₀|² + |z₂|² − 2 |z₁|²` (Section 5.1). -/
noncomputable def tbtH (z : Fin 3 → ℂ) : ℝ := ‖z 0‖ ^ 2 + ‖z 2‖ ^ 2 - 2 * ‖z 1‖ ^ 2

theorem tbt_quarticQ_eq (A : Matrix (Fin 2) (Fin 4) ℝ) :
    quarticQ A = 4 * ‖tbtD (zCoord A)‖ ^ 2 - tbtH (zCoord A) ^ 2 := rfl

/-- A quadratic `t ↦ a t² + b t + c` with `a ≥ 0` is convex. -/
theorem tbt_convexOn_quadratic {a b c : ℝ} (ha : 0 ≤ a) :
    ConvexOn ℝ Set.univ fun t : ℝ => a * t ^ 2 + b * t + c := by
  refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  obtain rfl : q = 1 - p := by linarith
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha hp) hq) (sq_nonneg (x - y))]

theorem tbt_norm_sq_add (a b : ℂ) (t : ℝ) :
    ‖a + t * b‖ ^ 2 = ‖a‖ ^ 2 + 2 * t * (a * conj b).re + t ^ 2 * ‖b‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- **Section 5.1**, the cancellation: if the increment `r` satisfies `D (r) = 0` and
`H (r) = 0` (the increments `a (1, λ, λ²)` of (21)), then along `z + t r` the quartic
`4 |D|² − H²` is a quadratic in `t` with leading coefficient `4 |dD|² − (dH)² ≥ 0` by (22). -/
theorem tbt_convexOn_of_increment (z r : Fin 3 → ℂ) (hD : tbtD r = 0) (hH : tbtH r = 0) :
    ConvexOn ℝ Set.univ fun t : ℝ =>
      4 * ‖tbtD (fun k => z k + t * r k)‖ ^ 2 - tbtH (fun k => z k + t * r k) ^ 2 := by
  set B : ℂ := z 0 * r 2 + r 0 * z 2 - 2 * z 1 * r 1 with hB
  set C : ℝ := (z 0 * conj (r 0) + z 2 * conj (r 2) - 2 * (z 1 * conj (r 1))).re with hC
  -- the quadratic terms vanish on the increment
  have hDt : ∀ t : ℝ, tbtD (fun k => z k + t * r k) = tbtD z + t * B := by
    intro t
    have : tbtD (fun k => z k + t * r k) = tbtD z + t * B + t ^ 2 * tbtD r := by
      simp only [tbtD, hB]; ring
    rw [this, hD]; ring
  have hHt : ∀ t : ℝ, tbtH (fun k => z k + t * r k) = tbtH z + 2 * t * C := by
    intro t
    have : tbtH (fun k => z k + t * r k) = tbtH z + 2 * t * C + t ^ 2 * tbtH r := by
      simp only [tbtH, tbt_norm_sq_add, hC, Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.re_ofNat, Complex.im_ofNat]
      ring
    rw [this, hH]; ring
  -- (22): `|dH| ≤ |d (2D)|`, that is `C² ≤ |B|²`
  have hCB : C ^ 2 ≤ ‖B‖ ^ 2 := by
    have hn : ‖r 0‖ * ‖r 2‖ = ‖r 1‖ ^ 2 := by
      have : r 0 * r 2 = r 1 ^ 2 := by simpa [tbtD, sub_eq_zero] using hD
      rw [← norm_mul, this, norm_pow]
    have hs : ‖r 0‖ ^ 2 + ‖r 2‖ ^ 2 = 2 * ‖r 1‖ ^ 2 := by simp only [tbtH] at hH; linarith
    have h02 : ‖r 0‖ = ‖r 2‖ := by
      have : (‖r 0‖ - ‖r 2‖) ^ 2 = 0 := by nlinarith
      nlinarith [sq_nonneg (‖r 0‖ - ‖r 2‖)]
    have h01 : ‖r 0‖ = ‖r 1‖ := by
      have : ‖r 0‖ ^ 2 = ‖r 1‖ ^ 2 := by rw [← hn, h02]; ring
      have := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
      exact this
    rcases eq_or_ne (r 0) 0 with h0 | h0
    · have h1 : r 1 = 0 := by rw [← norm_eq_zero, ← h01, h0, norm_zero]
      have h2 : r 2 = 0 := by rw [← norm_eq_zero, ← h02, h0, norm_zero]
      simp [hB, hC, h0, h1, h2]
    · obtain ⟨l, hl⟩ : ∃ l : ℂ, l = r 1 / r 0 := ⟨_, rfl⟩
      have hr1 : r 1 = l * r 0 := by rw [hl]; field_simp
      have hr2 : r 2 = l ^ 2 * r 0 := by
        have : r 0 * r 2 = r 1 ^ 2 := by simpa [tbtD, sub_eq_zero] using hD
        rw [hr1] at this
        have : r 0 * (r 2 - l ^ 2 * r 0) = 0 := by linear_combination this
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h h0
        · linear_combination h
      have hl1 : l * conj l = 1 := by
        have : ‖l‖ = 1 := by
          rw [hl, norm_div, ← h01, div_self (norm_ne_zero_iff.mpr h0)]
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, this]; simp
      have hCe : C = (conj (r 0) * conj l ^ 2 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1)).re := by
        rw [hC]; congr 1
        rw [hr1, hr2]; simp only [map_mul, map_pow]
        linear_combination (-(conj (r 0) * z 0 * (l * conj l + 1)) + 2 * z 1 * conj (r 0) * conj l) * hl1
      have hBe : ‖B‖ = ‖conj (r 0) * conj l ^ 2 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1)‖ := by
        have hln : ‖l‖ = 1 := by
          have := congrArg (fun x => ‖x‖) hl1
          simp only [norm_mul, Complex.norm_conj, norm_one] at this
          nlinarith [norm_nonneg l]
        have hB' : B = r 0 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1) := by rw [hB, hr1, hr2]; ring
        rw [hB', norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_conj,
          hln]
        ring
      rw [hCe, hBe]
      have := Complex.abs_re_le_norm (conj (r 0) * conj l ^ 2 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1))
      nlinarith [abs_nonneg ((conj (r 0) * conj l ^ 2 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1)).re),
        sq_abs ((conj (r 0) * conj l ^ 2 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1)).re)]
  have hq : (fun t : ℝ =>
      4 * ‖tbtD (fun k => z k + t * r k)‖ ^ 2 - tbtH (fun k => z k + t * r k) ^ 2) =
      fun t => (4 * ‖B‖ ^ 2 - 4 * C ^ 2) * t ^ 2 +
        (8 * (tbtD z * conj B).re - 4 * tbtH z * C) * t + (4 * ‖tbtD z‖ ^ 2 - tbtH z ^ 2) := by
    funext t
    rw [hDt, hHt, tbt_norm_sq_add]
    ring
  rw [hq]
  exact tbt_convexOn_quadratic (by linarith)


theorem tbt_wirtAlpha_re {m : ℕ} (A : Matrix (Fin 2) (Fin m) ℝ) (k l : Fin m) :
    (wirtAlpha A k l).re = (A 0 k + A 1 l) / 2 := by simp [wirtAlpha]

theorem tbt_wirtAlpha_im {m : ℕ} (A : Matrix (Fin 2) (Fin m) ℝ) (k l : Fin m) :
    (wirtAlpha A k l).im = (A 1 k - A 0 l) / 2 := by simp [wirtAlpha]

theorem tbt_wirtBeta_re {m : ℕ} (A : Matrix (Fin 2) (Fin m) ℝ) (k l : Fin m) :
    (wirtBeta A k l).re = (A 0 k - A 1 l) / 2 := by simp [wirtBeta]

theorem tbt_wirtBeta_im {m : ℕ} (A : Matrix (Fin 2) (Fin m) ℝ) (k l : Fin m) :
    (wirtBeta A k l).im = (A 1 k + A 0 l) / 2 := by simp [wirtBeta]

theorem tbt_zCoord0 (A : Matrix (Fin 2) (Fin 4) ℝ) :
    zCoord A 0 = starRingEnd ℂ (wirtAlpha A 2 3) := rfl

theorem tbt_zCoord1 (A : Matrix (Fin 2) (Fin 4) ℝ) :
    zCoord A 1 = starRingEnd ℂ (wirtAlpha A 0 1) := rfl

theorem tbt_zCoord2 (A : Matrix (Fin 2) (Fin 4) ℝ) : zCoord A 2 = wirtBeta A 0 1 := rfl

/-- `Z` is real-linear: `Z (A + t R) = Z (A) + t Z (R)`. -/
theorem tbt_zCoord_add_smul (A R : Matrix (Fin 2) (Fin 4) ℝ) (t : ℝ) :
    zCoord (A + t • R) = fun k => zCoord A k + t * zCoord R k := by
  funext k
  match k with
  | 0 =>
    simp only [tbt_zCoord0]
    apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, tbt_wirtAlpha_re, tbt_wirtAlpha_im,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> ring
  | 1 =>
    simp only [tbt_zCoord1]
    apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, tbt_wirtAlpha_re, tbt_wirtAlpha_im,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> ring
  | 2 =>
    simp only [tbt_zCoord2]
    apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, tbt_wirtBeta_re, tbt_wirtBeta_im,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- (21) for a single increment, from Lemma 4.1: a matrix `R ∈ 𝓛` of rank at most one has
`Z (R) = a (1, λ, λ²)` with `|λ| = 1`, so `D (Z (R)) = 0` and `H (Z (R)) = 0`. -/
theorem tbt_D_H_of_rank_le_one (R : Matrix (Fin 2) (Fin 4) ℝ) (hL : R ∈ calL)
    (hR1 : R.rank ≤ 1) : tbtD (zCoord R) = 0 ∧ tbtH (zCoord R) = 0 := by
  obtain ⟨lam, -, hlam⟩ := lemma4_1 2
  obtain ⟨hl1, hQ, -⟩ := hlam R hR1
  -- `Y^j = λ conj X^j`, `j = 1, 2` (Lemma 4.1, (8))
  have hQ0 : wirtBeta R 0 1 = lam R * conj (wirtAlpha R 0 1) := hQ 0
  have hQ1 : wirtBeta R 2 3 = lam R * conj (wirtAlpha R 2 3) := hQ 1
  have hc : wirtBeta R 2 3 = conj (wirtAlpha R 0 1) := hL
  -- (21): `Z (R) = a (1, λ, λ²)` with `a = conj α₂`
  set a := conj (wirtAlpha R 2 3) with ha
  have hz1 : zCoord R 1 = lam R * a := by rw [tbt_zCoord1, ← hc, hQ1]
  have hz2 : zCoord R 2 = lam R ^ 2 * a := by
    rw [tbt_zCoord2, hQ0, ← hc, hQ1]; ring
  have hz0 : zCoord R 0 = a := tbt_zCoord0 R
  have hn : ‖lam R‖ ^ 2 = 1 := by rw [hl1]; norm_num
  constructor
  · simp only [tbtD, hz0, hz1, hz2]; ring
  · simp only [tbtH, hz0, hz1, hz2, norm_mul, norm_pow, mul_pow]
    rw [hl1]; ring

/-- `q` is convex along every line whose direction is a matrix of rank at most one in `𝓛`. -/
theorem tbt_quarticQ_convexOn (A R : Matrix (Fin 2) (Fin 4) ℝ) (hR : R ∈ calL)
    (hR1 : R.rank ≤ 1) : ConvexOn ℝ Set.univ fun t : ℝ => quarticQ (A + t • R) := by
  obtain ⟨hD, hH⟩ := tbt_D_H_of_rank_le_one R hR hR1
  have := tbt_convexOn_of_increment (zCoord A) (zCoord R) hD hH
  simpa only [tbt_quarticQ_eq, tbt_zCoord_add_smul] using this

/-- `J` is linear. -/
theorem tbt_embedJ_add_smul (A R : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ) :
    embedJ (A + t • R) = embedJ A + t • embedJ R := by
  ext i j
  simp only [embedJ, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `J` maps an outer product to an outer product. -/
theorem tbt_embedJ_vecMulVec (v : Fin 2 → ℝ) (w : Fin 3 → ℝ) :
    embedJ (Matrix.vecMulVec v w) =
      Matrix.vecMulVec v (fun j : Fin 4 => if h : j.val < 3 then w ⟨j.val, h⟩ else 0) := by
  ext i j
  simp only [embedJ, Matrix.of_apply, Matrix.vecMulVec_apply]
  split_ifs <;> simp

/-- `J` preserves rank at most one. -/
theorem tbt_rank_embedJ_le (R : Matrix (Fin 2) (Fin 3) ℝ) (hR1 : R.rank ≤ 1) :
    (embedJ R).rank ≤ 1 := by
  obtain ⟨v, w, rfl⟩ := tbt_exists_vecMulVec R hR1
  rw [tbt_embedJ_vecMulVec]
  exact Matrix.rank_vecMulVec_le _ _


-- The proof does not use the paper's hypothesis `A ∈ 𝓛` (see the docstring).
set_option linter.unusedVariables false in
/-- **Section 5.1** (`cs-q-rc`, lines 1550–1555): `q` is globally rank-one convex on `𝓛`: for
`A ∈ 𝓛` and rank-one `R ∈ 𝓛`, `t ↦ q (A + t R)` is convex. The hypothesis `A ∈ 𝓛` is the
paper's; the proof does not use it (only the direction `R` needs to lie in `𝓛`).

Proof. Lemma 4.1 gives `Z (R) = a (1, λ, λ²)` with `|λ| = 1` ((21)), on which the quadratic parts
of `D` and `H` vanish; so along the line `q` is the quadratic `4 |D₀ + t a Γ|² − (H₀ + 2 t C)²`,
whose leading coefficient `4 (|a Γ|² − C²)` is nonnegative by (22), `|C| ≤ |a Γ|`
(`tbt_convexOn_of_increment`). The paper states the martingale form `E q (M_n) ≥ q (M₀)` (by
orthogonality of the martingale differences); along a single line, which is what the statement
asks, this is the same computation. -/
theorem quarticQ_rankOneConvexOn_calL (A R : Matrix (Fin 2) (Fin 4) ℝ) (hA : A ∈ calL)
    (hR : R ∈ calL) (hR1 : R.rank = 1) :
    ConvexOn ℝ Set.univ fun t : ℝ => quarticQ (A + t • R) :=
  tbt_quarticQ_convexOn A R hR hR1.le

/-- **Section 5.2** (`cs-q3-rc`, lines 1573–1574): `q₃` is globally rank-one convex on `𝓛₃`
("since `J` preserves rank"): `J` maps `𝓛₃` into `𝓛` and rank-one matrices to rank-one matrices
(`R` is a block of `J R`), so the claim for `q` on `𝓛` (`quarticQ_rankOneConvexOn_calL`) applies. -/
theorem q3_rankOneConvexOn_L3 (A R : Matrix (Fin 2) (Fin 3) ℝ) (hA : A ∈ L3) (hR : R ∈ L3)
    (hR1 : R.rank = 1) :
    ConvexOn ℝ Set.univ fun t : ℝ => q3 (A + t • R) := by
  have hJR : (embedJ R).rank = 1 := by
    refine le_antisymm (tbt_rank_embedJ_le R hR1.le) ?_
    have hsub : (embedJ R).submatrix id (Fin.castLE (by norm_num : 3 ≤ 4)) = R := by
      ext i j
      simp [embedJ, Fin.castLE, j.isLt]
    rw [← hR1, ← hsub]
    exact Matrix.rank_submatrix_le _ _ _
  have := quarticQ_rankOneConvexOn_calL (embedJ A) (embedJ R) hA hR hJR
  simpa only [q3, tbt_embedJ_add_smul] using this

/-- **Equation (24)** (`eq:q-simp`): on `𝓛₃`, `q₃ (A) = −det (A diag (1, 1, −1) Aᵀ)`. -/
theorem equation24 (A : Matrix (Fin 2) (Fin 3) ℝ) (hA : A ∈ L3) :
    q3 A = -(A * Matrix.diagonal (![1, 1, -1] : Fin 3 → ℝ) * Aᵀ).det := by
  rw [mem_L3_iff] at hA
  simp only [q3, quarticQ, zCoord, embedJ, wirtAlpha, wirtBeta, Matrix.of_apply]
  simp only [Complex.sq_norm, Complex.normSq_apply, Matrix.det_fin_two, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.transpose_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im, pow_two]
  norm_num
  rw [hA.1, hA.2]
  ring

theorem tbt_frobSq_nonneg {d m : ℕ} (A : Matrix (Fin d) (Fin m) ℝ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem tbt_eq_zero_of_frobSq_eq_zero {d m : ℕ} {A : Matrix (Fin d) (Fin m) ℝ}
    (h : frobSq A = 0) : A = 0 := by
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (A i j)).mp h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (A i j)).mp h1 j
    (Finset.mem_univ _)
  simpa using h2

/-- `frobNorm A ≤ 2 frobNorm B` as soon as `|A|² ≤ 4 |B|²`. -/
theorem tbt_frobNorm_le_two_mul {d m : ℕ} {A B : Matrix (Fin d) (Fin m) ℝ}
    (h : frobSq A ≤ 4 * frobSq B) : frobNorm A ≤ 2 * frobNorm B := by
  unfold frobNorm
  calc √(frobSq A) ≤ √(4 * frobSq B) := Real.sqrt_le_sqrt h
    _ = 2 * √(frobSq B) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]

/-- **Proof of Theorem 1.3** (`cs-kappa`), the correction behind `L3_rankOneCorrection`: for
`R = v wᵀ`, keep the column `v` and take `R_L = x v uᵀ` with `u = (v₀² − v₁², 2 v₀ v₁, |v|²)`, so
that `R_L ∈ 𝓛₃`; with `n = |v|²`, `⟨w, u⟩` and `E = ⟨w, u⟩ − 2 n w₂`,
`2 n (2 |π^⊥ R|² − |π R − R_L|²) = E² − (2 n² x − ⟨w, u⟩)²`. -/
theorem tbt_correction_identity (v : Fin 2 → ℝ) (w : Fin 3 → ℝ) (x : ℝ) :
    let n := v 0 ^ 2 + v 1 ^ 2
    let u : Fin 3 → ℝ := ![v 0 ^ 2 - v 1 ^ 2, 2 * v 0 * v 1, n]
    let wu := w 0 * u 0 + w 1 * u 1 + w 2 * u 2
    2 * n * (2 * frobSq (Matrix.vecMulVec v w - projL3 (Matrix.vecMulVec v w)) -
        frobSq (projL3 (Matrix.vecMulVec v w) - Matrix.vecMulVec v (x • u))) =
      (wu - 2 * n * w 2) ^ 2 - (2 * n ^ 2 * x - wu) ^ 2 := by
  intro n u wu
  simp only [frobSq, Fin.sum_univ_two, Fin.sum_univ_three, projL3, Matrix.vecMulVec_apply,
    Matrix.sub_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul,
    Matrix.head_cons, Matrix.tail_cons, u, wu, n]
  ring

/-- **Proof of Theorem 1.3** (`cs-kappa`, line 1978): `𝓛₃` satisfies hypothesis (25) of Lemma 5.1
with `κ = 2`. Asserted without proof in the paper (inventory E5; numerically the best `κ` is about
`1.054`).

Proof (the paper gives none; inventory E5). Write `R = v wᵀ` and `u = (v₀² − v₁², 2 v₀ v₁, |v|²)`; every
`x v uᵀ` lies in `𝓛₃`, and `tbt_correction_identity` shows that `x = ⟨w, u⟩ / (2 |v|⁴)` gives
`|π R − R_L|² ≤ 2 |π^⊥ R|²` (so even `κ = √2`). When `⟨w, u⟩ = 0` this `x` vanishes; a small
`x = η ≠ 0` then keeps `R_L` of rank one, at the cost `2 |v|⁶ η² ≤ 2 |π^⊥ R|²`. -/
theorem L3_rankOneCorrection (R : Matrix (Fin 2) (Fin 3) ℝ) (hR : R.rank = 1) :
    ∃ RL ∈ L3, RL.rank = 1 ∧ frobNorm (projL3 R - RL) ≤ 2 * frobNorm (R - projL3 R) := by
  obtain ⟨v, w, rfl⟩ := tbt_exists_vecMulVec R hR.le
  have hR0 : Matrix.vecMulVec v w ≠ 0 := by
    intro h; rw [h, Matrix.rank_zero] at hR; exact zero_ne_one hR
  have hv : v ≠ 0 := by rintro rfl; apply hR0; ext i j; simp [Matrix.vecMulVec_apply]
  set n := v 0 ^ 2 + v 1 ^ 2 with hn_def
  have hn : 0 < n := by
    by_contra hle
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    apply hv; ext i; fin_cases i <;> simp [h0, h1]
  set u : Fin 3 → ℝ := ![v 0 ^ 2 - v 1 ^ 2, 2 * v 0 * v 1, n] with hu
  set wu := w 0 * u 0 + w 1 * u 1 + w 2 * u 2 with hwu_def
  have key : ∀ x : ℝ, 2 * n * (2 * frobSq (Matrix.vecMulVec v w - projL3 (Matrix.vecMulVec v w)) -
        frobSq (projL3 (Matrix.vecMulVec v w) - Matrix.vecMulVec v (x • u))) =
      (wu - 2 * n * w 2) ^ 2 - (2 * n ^ 2 * x - wu) ^ 2 := fun x => tbt_correction_identity v w x
  -- every `x v uᵀ` lies in `𝓛₃`, and has rank one for `x ≠ 0`
  have hmem : ∀ x : ℝ, Matrix.vecMulVec v (x • u) ∈ L3 := by
    intro x
    rw [mem_L3_iff]
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hu, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hn_def]
    constructor <;> ring
  have hrank : ∀ x : ℝ, x ≠ 0 → (Matrix.vecMulVec v (x • u)).rank = 1 := by
    intro x hx
    refine tbt_rank_vecMulVec hv ?_
    intro h
    have := congrFun h 2
    simp only [Pi.smul_apply, smul_eq_mul, hu, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Pi.zero_apply, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact hx h1
    · exact hn.ne' h1
  set b := frobSq (Matrix.vecMulVec v w - projL3 (Matrix.vecMulVec v w)) with hb
  have hb0 : 0 ≤ b := tbt_frobSq_nonneg _
  by_cases hwu : wu = 0
  · -- a small multiple keeps the rank equal to one
    have hbpos : 0 < b := by
      rcases hb0.lt_or_eq with h | h
      · exact h
      · exfalso
        have k0 := key 0
        rw [← h, hwu] at k0
        have hP : frobSq (projL3 (Matrix.vecMulVec v w) - Matrix.vecMulVec v ((0 : ℝ) • u)) = 0 :=
          le_antisymm (by nlinarith [sq_nonneg (w 2)]) (tbt_frobSq_nonneg _)
        have hP' := tbt_eq_zero_of_frobSq_eq_zero hP
        have hN' := tbt_eq_zero_of_frobSq_eq_zero h.symm
        apply hR0
        simp only [zero_smul] at hP'
        have : Matrix.vecMulVec v (0 : Fin 3 → ℝ) = 0 := by
          ext i j; simp [Matrix.vecMulVec_apply]
        rw [this, sub_zero] at hP'
        rw [hP', sub_zero] at hN'
        exact hN'
    set η := √(b / n ^ 3) with hη
    have hηpos : 0 < η := Real.sqrt_pos.mpr (div_pos hbpos (pow_pos hn 3))
    have hη2 : η ^ 2 = b / n ^ 3 := Real.sq_sqrt (div_pos hbpos (pow_pos hn 3)).le
    refine ⟨Matrix.vecMulVec v (η • u), hmem η, hrank η hηpos.ne', tbt_frobNorm_le_two_mul ?_⟩
    have kη := key η
    rw [hwu, sub_zero] at kη
    have : (2 * n ^ 2 * η) ^ 2 = 4 * n * b := by
      rw [mul_pow, hη2]; field_simp; ring
    rw [this] at kη
    nlinarith [sq_nonneg (0 - 2 * n * w 2)]
  · set x := wu / (2 * n ^ 2) with hx
    have hx0 : x ≠ 0 := div_ne_zero hwu (by positivity)
    refine ⟨Matrix.vecMulVec v (x • u), hmem x, hrank x hx0, tbt_frobNorm_le_two_mul ?_⟩
    have kx := key x
    have : 2 * n ^ 2 * x - wu = 0 := by rw [hx]; field_simp; ring
    rw [this] at kx
    nlinarith [sq_nonneg (wu - 2 * n * w 2),
      tbt_frobSq_nonneg (projL3 (Matrix.vecMulVec v w) - Matrix.vecMulVec v (x • u))]

/-- `𝓛₃` satisfies hypothesis (25) of Lemma 5.1 with `κ = 2`, as a submodule (from
`L3_rankOneCorrection`). -/
theorem hasRankOneCorrection_L3 : HasRankOneCorrection L3Submodule projL3 2 :=
  fun R hR => L3_rankOneCorrection R hR

end Cassese
