module

public import Morrey.Cassese.TwoByThree.ExtensionOne
public import Morrey.Cassese.TwoByThree.WitnessCutoff
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Section 5: the proof of Theorem 1.3 (b), `p`-homogeneous examples for `p` near `4`

The proof of Theorem 1.3 (b) (TeX lines 2031–2044) uses, on `𝓛₃`, the integrand
`f_{r,δ,C} (A) = C^r |2D (JA)|^r − |H (JA)|^r + δ |A|^{2r}` with `r = p/2` and `C = r* − 1`
(`tbt1Fp`), extends it by Lemma 5.1 (1) to `g = f ∘ π + Λ^p |π^⊥ ·|^p` (`tbt1G`), and concludes
"by continuity of the rank-one convexity and quasiconvexity estimates" from the quartic case
`p = 4` of Theorem 1.3 (a). The continuity is not written in the paper (inventory E4); here the
constants of Lemma 5.1 (1) are made explicit and uniform in `p` (`lemma5_1_part1_quant`,
`tbt1_fp_young`), `δ` and `Λ` are fixed from the case `p = 4` before `p` varies, and the witness
integral is continuous in `p` by dominated convergence.

Helpers are prefixed `tbt1_`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Matrix ENNReal ComplexConjugate

namespace Cassese

/-! ### The quadratic observables along `𝓛₃` -/

/-- `D (Z (J A))`. -/
noncomputable def tbt1Dz (A : Matrix (Fin 2) (Fin 3) ℝ) : ℂ := tbtD (zCoord (embedJ A))

/-- `H (Z (J A))`. -/
noncomputable def tbt1Hz (A : Matrix (Fin 2) (Fin 3) ℝ) : ℝ := tbtH (zCoord (embedJ A))

/-- The cross term `B (z, r) = z₀ r₂ + r₀ z₂ − 2 z₁ r₁` of `D`. -/
noncomputable def tbt1B (z r : Fin 3 → ℂ) : ℂ := z 0 * r 2 + r 0 * z 2 - 2 * z 1 * r 1

/-- The cross term `C (z, r) = Re (z₀ r̄₀ + z₂ r̄₂ − 2 z₁ r̄₁)` of `H`. -/
noncomputable def tbt1C (z r : Fin 3 → ℂ) : ℝ :=
  (z 0 * conj (r 0) + z 2 * conj (r 2) - 2 * (z 1 * conj (r 1))).re

theorem tbt1_zJ_add_smul (A R : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ) :
    zCoord (embedJ (A + t • R)) = fun k => zCoord (embedJ A) k + t * zCoord (embedJ R) k := by
  rw [tbt_embedJ_add_smul, tbt_zCoord_add_smul]

theorem tbt1_zJ_zero : zCoord (embedJ (0 : Matrix (Fin 2) (Fin 3) ℝ)) = 0 := by
  have h := tbt1_zJ_add_smul 0 0 0
  have h0 : (0 : Matrix (Fin 2) (Fin 3) ℝ) + (0 : ℝ) • 0 = 0 := by simp
  rw [h0] at h
  funext k
  have hk := congrFun h k
  have hk2 := congrFun (tbt1_zJ_add_smul 0 0 1) k
  simp only [one_smul, add_zero, Complex.ofReal_one, one_mul] at hk2
  simpa using hk2

theorem tbt1_zJ_smul (t : ℝ) (A : Matrix (Fin 2) (Fin 3) ℝ) :
    zCoord (embedJ (t • A)) = fun k => t * zCoord (embedJ A) k := by
  have h := tbt1_zJ_add_smul 0 A t
  rw [zero_add, tbt1_zJ_zero] at h
  simpa using h

theorem tbt1_zJ_add (A R : Matrix (Fin 2) (Fin 3) ℝ) :
    zCoord (embedJ (A + R)) = fun k => zCoord (embedJ A) k + zCoord (embedJ R) k := by
  have h := tbt1_zJ_add_smul A R 1
  simpa using h

/-- `D (z + t r) = D (z) + t B (z, r) + t² D (r)`. -/
theorem tbt1_D_add (z r : Fin 3 → ℂ) (t : ℝ) :
    tbtD (fun k => z k + t * r k) = tbtD z + t * tbt1B z r + t ^ 2 * tbtD r := by
  simp only [tbtD, tbt1B]; ring

/-- `H (z + t r) = H (z) + 2 t C (z, r) + t² H (r)`. -/
theorem tbt1_H_add (z r : Fin 3 → ℂ) (t : ℝ) :
    tbtH (fun k => z k + t * r k) = tbtH z + 2 * t * tbt1C z r + t ^ 2 * tbtH r := by
  simp only [tbtH, tbt_norm_sq_add, tbt1C, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- (22): if `D (r) = 0` and `H (r) = 0` (a rank-one increment in `𝓛`), then
`C (z, r)² ≤ |B (z, r)|²`, that is `|dH| ≤ |d (2D)|`. -/
theorem tbt1_C_sq_le (z r : Fin 3 → ℂ) (hD : tbtD r = 0) (hH : tbtH r = 0) :
    tbt1C z r ^ 2 ≤ ‖tbt1B z r‖ ^ 2 := by
  set B : ℂ := tbt1B z r with hB
  set C : ℝ := tbt1C z r with hC
  have hn : ‖r 0‖ * ‖r 2‖ = ‖r 1‖ ^ 2 := by
    have : r 0 * r 2 = r 1 ^ 2 := by simpa [tbtD, sub_eq_zero] using hD
    rw [← norm_mul, this, norm_pow]
  have hs : ‖r 0‖ ^ 2 + ‖r 2‖ ^ 2 = 2 * ‖r 1‖ ^ 2 := by simp only [tbtH] at hH; linarith
  have h02 : ‖r 0‖ = ‖r 2‖ := by
    have : (‖r 0‖ - ‖r 2‖) ^ 2 = 0 := by nlinarith
    nlinarith [sq_nonneg (‖r 0‖ - ‖r 2‖)]
  have h01 : ‖r 0‖ = ‖r 1‖ := by
    have : ‖r 0‖ ^ 2 = ‖r 1‖ ^ 2 := by rw [← hn, h02]; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
  rcases eq_or_ne (r 0) 0 with h0 | h0
  · have h1 : r 1 = 0 := by rw [← norm_eq_zero, ← h01, h0, norm_zero]
    have h2 : r 2 = 0 := by rw [← norm_eq_zero, ← h02, h0, norm_zero]
    simp [hB, hC, tbt1B, tbt1C, h0, h1, h2]
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
      rw [hC, tbt1C]; congr 1
      rw [hr1, hr2]; simp only [map_mul, map_pow]
      linear_combination (-(conj (r 0) * z 0 * (l * conj l + 1)) + 2 * z 1 * conj (r 0) * conj l) * hl1
    have hBe : ‖B‖ = ‖conj (r 0) * conj l ^ 2 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1)‖ := by
      have hln : ‖l‖ = 1 := by
        have := congrArg (fun x => ‖x‖) hl1
        simp only [norm_mul, Complex.norm_conj, norm_one] at this
        nlinarith [norm_nonneg l]
      have hB' : B = r 0 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1) := by
        rw [hB, tbt1B, hr1, hr2]; ring
      rw [hB', norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_conj, hln]
      ring
    rw [hCe, hBe]
    have := Complex.abs_re_le_norm (conj (r 0) * conj l ^ 2 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1))
    nlinarith [abs_nonneg ((conj (r 0) * conj l ^ 2 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1)).re),
      sq_abs ((conj (r 0) * conj l ^ 2 * (l ^ 2 * z 0 + z 2 - 2 * l * z 1)).re)]

/-- (21) for an increment in `𝓛₃` of rank at most one: `D (Z (J R)) = 0` and `H (Z (J R)) = 0`. -/
theorem tbt1_DH_incr {R : Matrix (Fin 2) (Fin 3) ℝ} (hR : R ∈ L3) (hR1 : R.rank ≤ 1) :
    tbtD (zCoord (embedJ R)) = 0 ∧ tbtH (zCoord (embedJ R)) = 0 :=
  tbt_D_H_of_rank_le_one (embedJ R) hR (tbt_rank_embedJ_le R hR1)

/-! ### The integrand and its coercivity on `𝓛₃`-valued martingales -/

/-- The integrand of the proof of Theorem 1.3 (b), `f_{r,δ,C} (A) = C^r |2D (JA)|^r − |H (JA)|^r +
δ |A|^{2r}` with `r = p/2` and `C = r* − 1` (`|A|^{2r} = |A|^p`). -/
noncomputable def tbt1Fp (p δ : ℝ) (A : Matrix (Fin 2) (Fin 3) ℝ) : ℝ :=
  (pStar (p / 2) - 1) ^ (p / 2) * ‖2 * tbt1Dz A‖ ^ (p / 2) - |tbt1Hz A| ^ (p / 2) +
    δ * frobNorm A ^ p

/-- Its extension `g = f ∘ π + Λ^p |π^⊥ ·|^p` (Lemma 5.1 (1)). -/
noncomputable def tbt1G (p δ Λ : ℝ) (A : Matrix (Fin 2) (Fin 3) ℝ) : ℝ :=
  tbt1Fp p δ (projL3 A) + Λ ^ p * frobNorm (A - projL3 A) ^ p

/-- Along an `𝓛₃`-valued rank-one Rademacher martingale `M_n = Σ_{k<n} ε_k A_k`, `2 D (Z (J M_n))`
and `H (Z (J M_n))` are Rademacher martingales, with increments `2 B (Z (J M_k), Z (J A_k))` and
`2 C (Z (J M_k), Z (J A_k))` (the quadratic parts vanish on the increments, (21)). -/
theorem tbt1_DH_mart {N : ℕ} {A : Fin N → (Fin N → Bool) → Matrix (Fin 2) (Fin 3) ℝ}
    (hA : IsRankOneIncrements A) (hL : ∀ k ε, A k ε ∈ L3Submodule) (n : ℕ) (ε : Fin N → Bool) :
    2 * tbt1Dz (mart A n ε) =
        mart (fun k ε => 2 * tbt1B (zCoord (embedJ (mart A k.val ε))) (zCoord (embedJ (A k ε))))
          n ε ∧
      ((tbt1Hz (mart A n ε) : ℝ) : ℂ) =
        mart (fun k ε => (((2 * tbt1C (zCoord (embedJ (mart A k.val ε)))
          (zCoord (embedJ (A k ε))) : ℝ)) : ℂ)) n ε := by
  induction n with
  | zero =>
    simp only [rad_mart_zero, tbt1Dz, tbt1Hz, tbt1_zJ_zero]
    simp [tbtD, tbtH]
  | succ n ih =>
    rw [tbt1_mart_succ, tbt1_mart_succ, tbt1_mart_succ]
    by_cases hn : n < N
    · obtain ⟨hD0, hH0⟩ := tbt1_DH_incr (hL ⟨n, hn⟩ ε) (hA.2 ⟨n, hn⟩ ε)
      simp only [tbt1D, hn, dite_true]
      rw [← ih.1, ← ih.2]
      simp only [tbt1Dz, tbt1Hz, tbt1_zJ_add_smul, tbt1_D_add, tbt1_H_add, hD0, hH0,
        Complex.real_smul]
      constructor
      · ring
      · push_cast; ring
    · simp only [tbt1D, hn, dite_false, add_zero]
      exact ih

/-- **Coercivity** (the hypothesis of Lemma 5.1 (1) for `f_{r,δ,C}` with `η = δ`): for an
`𝓛₃`-valued rank-one Rademacher martingale started at `0`, `E f (M_N) ≥ δ E |M_N|^p`. Burkholder's
inequality in `L^r` (`r = p/2 > 1`) for the martingales `H (Z (J M))` and `2 D (Z (J M))` in
`ℂ ≅ ℝ²`, with `|dH| ≤ |d (2D)|` by (22), gives `E |H_N|^r ≤ (r* − 1)^r E |2 D_N|^r`. -/
theorem tbt1_coercive {p : ℝ} (hp : 2 < p) (δ : ℝ) (N : ℕ)
    (A : Fin N → (Fin N → Bool) → Matrix (Fin 2) (Fin 3) ℝ) (hA : IsRankOneIncrements A)
    (hL : ∀ k ε, A k ε ∈ L3Submodule) :
    δ * avg (fun ε => frobNorm (radMart 0 A N ε) ^ p) ≤
      avg fun ε => tbt1Fp p δ (radMart 0 A N ε) := by
  have hr : 1 < p / 2 := by linarith
  set ξD : Fin N → (Fin N → Bool) → ℂ :=
    fun k ε => 2 * tbt1B (zCoord (embedJ (mart A k.val ε))) (zCoord (embedJ (A k ε)))
  set ξH : Fin N → (Fin N → Bool) → ℂ := fun k ε =>
    (((2 * tbt1C (zCoord (embedJ (mart A k.val ε))) (zCoord (embedJ (A k ε))) : ℝ)) : ℂ)
  have hpredM : ∀ (k : Fin N) (ε ε' : Fin N → Bool), (∀ j, j < k → ε j = ε' j) →
      mart A k.val ε = mart A k.val ε' := fun k ε ε' h =>
    rad_mart_congr hA.1 k.val fun j hj => h j (Fin.lt_def.mpr hj)
  have hξD : IsPredictable ξD := fun k ε ε' h => by
    simp only [ξD, hpredM k ε ε' h, hA.1 k ε ε' h]
  have hξH : IsPredictable ξH := fun k ε ε' h => by
    simp only [ξH, hpredM k ε ε' h, hA.1 k ε ε' h]
  have hle : ∀ k ε, ‖ξH k ε‖ ≤ ‖ξD k ε‖ := fun k ε => by
    obtain ⟨hD0, hH0⟩ := tbt1_DH_incr (hL k ε) (hA.2 k ε)
    have := tbt1_C_sq_le (zCoord (embedJ (mart A k.val ε))) (zCoord (embedJ (A k ε))) hD0 hH0
    simp only [ξH, ξD, Complex.norm_real, norm_mul, Real.norm_eq_abs, Complex.norm_two]
    rw [abs_two]
    have h := abs_le_of_sq_le_sq' this (norm_nonneg _)
    have : |tbt1C (zCoord (embedJ (mart A (↑k) ε))) (zCoord (embedJ (A k ε)))| ≤
        ‖tbt1B (zCoord (embedJ (mart A (↑k) ε))) (zCoord (embedJ (A k ε)))‖ := abs_le.mpr h
    linarith
  have hbk := tbt1_burkholder_avg hξH hξD hle hr
  have e1 : ∀ ε, ‖mart ξH N ε‖ = |tbt1Hz (radMart 0 A N ε)| := fun ε => by
    rw [← (tbt1_DH_mart hA hL N ε).2, radMart, zero_add, Complex.norm_real, Real.norm_eq_abs]
  have e2 : ∀ ε, ‖mart ξD N ε‖ = ‖2 * tbt1Dz (radMart 0 A N ε)‖ := fun ε => by
    rw [← (tbt1_DH_mart hA hL N ε).1, radMart, zero_add]
  simp only [e1, e2] at hbk
  simp only [tbt1Fp]
  rw [rad_avg_add, rad_avg_sub, rad_avg_mul_left, rad_avg_mul_left]
  linarith

/-! ### The homogeneity and Young estimate, with explicit constants -/

theorem tbt1_norm_z_le (X : Matrix (Fin 2) (Fin 3) ℝ) (k : Fin 3) :
    ‖zCoord (embedJ X) k‖ ≤ frobNorm X := by
  rw [frobNorm]
  apply Real.le_sqrt_of_sq_le
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [frobSq, Fin.sum_univ_two, Fin.sum_univ_three]
  fin_cases k <;>
  simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, tbt_zCoord0, tbt_zCoord1, tbt_zCoord2,
    Complex.conj_re, Complex.conj_im, tbt_wirtAlpha_re, tbt_wirtAlpha_im, tbt_wirtBeta_re,
    tbt_wirtBeta_im, embedJ, Matrix.of_apply] <;> norm_num <;>
  nlinarith [sq_nonneg (X 0 0), sq_nonneg (X 0 1), sq_nonneg (X 0 2), sq_nonneg (X 1 0),
    sq_nonneg (X 1 1), sq_nonneg (X 1 2), sq_nonneg (X 0 0 - X 1 1), sq_nonneg (X 1 0 + X 0 1),
    sq_nonneg (X 0 0 + X 1 1), sq_nonneg (X 1 0 - X 0 1)]

theorem tbt1_norm_B_le {z w : Fin 3 → ℂ} {a b : ℝ} (hz : ∀ k, ‖z k‖ ≤ a) (hw : ∀ k, ‖w k‖ ≤ b) :
    ‖tbt1B z w‖ ≤ 4 * a * b := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hz 0)
  have hb : 0 ≤ b := (norm_nonneg _).trans (hw 0)
  unfold tbt1B
  calc ‖z 0 * w 2 + w 0 * z 2 - 2 * z 1 * w 1‖
      ≤ ‖z 0‖ * ‖w 2‖ + ‖w 0‖ * ‖z 2‖ + 2 * (‖z 1‖ * ‖w 1‖) := by
        refine (norm_sub_le _ _).trans ?_
        rw [mul_assoc, norm_mul _ (z 1 * w 1), Complex.norm_two, norm_mul (z 1)]
        have := norm_add_le (z 0 * w 2) (w 0 * z 2)
        rw [norm_mul, norm_mul] at this
        linarith
    _ ≤ a * b + b * a + 2 * (a * b) := by
        gcongr <;> first | exact hz _ | exact hw _
    _ = 4 * a * b := by ring

theorem tbt1_abs_C_le {z w : Fin 3 → ℂ} {a b : ℝ} (hz : ∀ k, ‖z k‖ ≤ a) (hw : ∀ k, ‖w k‖ ≤ b) :
    |tbt1C z w| ≤ 4 * a * b := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hz 0)
  have hb : 0 ≤ b := (norm_nonneg _).trans (hw 0)
  unfold tbt1C
  refine (Complex.abs_re_le_norm _).trans ?_
  calc ‖z 0 * conj (w 0) + z 2 * conj (w 2) - 2 * (z 1 * conj (w 1))‖
      ≤ ‖z 0‖ * ‖w 0‖ + ‖z 2‖ * ‖w 2‖ + 2 * (‖z 1‖ * ‖w 1‖) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul (2 : ℂ), Complex.norm_two, norm_mul _ (conj (w 1)), Complex.norm_conj]
        refine add_le_add_left ((norm_add_le _ _).trans ?_) _
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    _ ≤ a * b + a * b + 2 * (a * b) := by
        gcongr <;> first | exact hz _ | exact hw _
    _ = 4 * a * b := by ring

theorem tbt1_norm_D_le {z : Fin 3 → ℂ} {a : ℝ} (hz : ∀ k, ‖z k‖ ≤ a) : ‖tbtD z‖ ≤ 2 * a ^ 2 := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hz 0)
  unfold tbtD
  calc ‖z 0 * z 2 - z 1 ^ 2‖ ≤ ‖z 0‖ * ‖z 2‖ + ‖z 1‖ ^ 2 := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_pow]
    _ ≤ a * a + a ^ 2 := by gcongr <;> exact hz _
    _ = 2 * a ^ 2 := by ring

theorem tbt1_abs_H_le {z : Fin 3 → ℂ} {a : ℝ} (hz : ∀ k, ‖z k‖ ≤ a) : |tbtH z| ≤ 4 * a ^ 2 := by
  have ha : 0 ≤ a := (norm_nonneg _).trans (hz 0)
  have h0 := pow_le_pow_left₀ (norm_nonneg _) (hz 0) 2
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hz 1) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (hz 2) 2
  unfold tbtH
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ‖z 0‖, sq_nonneg ‖z 1‖, sq_nonneg ‖z 2‖]

theorem tbt1_norm_Dz_le (X : Matrix (Fin 2) (Fin 3) ℝ) : ‖2 * tbt1Dz X‖ ≤ 8 * frobNorm X ^ 2 := by
  rw [norm_mul, Complex.norm_two]
  have := tbt1_norm_D_le (tbt1_norm_z_le X)
  have : 0 ≤ frobNorm X ^ 2 := sq_nonneg _
  unfold tbt1Dz; linarith

theorem tbt1_abs_Hz_le (X : Matrix (Fin 2) (Fin 3) ℝ) : |tbt1Hz X| ≤ 8 * frobNorm X ^ 2 := by
  have := tbt1_abs_H_le (tbt1_norm_z_le X)
  have : 0 ≤ frobNorm X ^ 2 := sq_nonneg _
  unfold tbt1Hz; linarith

theorem tbt1_norm_Dz_sub_le (X Y : Matrix (Fin 2) (Fin 3) ℝ) :
    ‖2 * tbt1Dz (X + Y) - 2 * tbt1Dz X‖ ≤ 8 * (frobNorm X + frobNorm Y) * frobNorm Y := by
  have e : tbt1Dz (X + Y) = tbt1Dz X + tbt1B (zCoord (embedJ X)) (zCoord (embedJ Y)) +
      tbtD (zCoord (embedJ Y)) := by
    have := tbt1_D_add (zCoord (embedJ X)) (zCoord (embedJ Y)) 1
    simp only [Complex.ofReal_one, one_mul, one_pow] at this
    rw [tbt1Dz, tbt1_zJ_add, this, tbt1Dz]
  rw [e, show 2 * (tbt1Dz X + tbt1B (zCoord (embedJ X)) (zCoord (embedJ Y)) +
      tbtD (zCoord (embedJ Y))) - 2 * tbt1Dz X = 2 * (tbt1B (zCoord (embedJ X))
      (zCoord (embedJ Y)) + tbtD (zCoord (embedJ Y))) by ring, norm_mul, Complex.norm_two]
  have h1 := tbt1_norm_B_le (tbt1_norm_z_le X) (tbt1_norm_z_le Y)
  have h2 := tbt1_norm_D_le (tbt1_norm_z_le Y)
  have h3 := norm_add_le (tbt1B (zCoord (embedJ X)) (zCoord (embedJ Y))) (tbtD (zCoord (embedJ Y)))
  have hX := tbt1_frobNorm_nonneg X
  have hY := tbt1_frobNorm_nonneg Y
  nlinarith

theorem tbt1_abs_Hz_sub_le (X Y : Matrix (Fin 2) (Fin 3) ℝ) :
    |tbt1Hz (X + Y) - tbt1Hz X| ≤ 8 * (frobNorm X + frobNorm Y) * frobNorm Y := by
  have e : tbt1Hz (X + Y) = tbt1Hz X + 2 * tbt1C (zCoord (embedJ X)) (zCoord (embedJ Y)) +
      tbtH (zCoord (embedJ Y)) := by
    have := tbt1_H_add (zCoord (embedJ X)) (zCoord (embedJ Y)) 1
    simp only [Complex.ofReal_one, one_mul, one_pow, mul_one] at this
    rw [tbt1Hz, tbt1_zJ_add, this, tbt1Hz]
  rw [e, show tbt1Hz X + 2 * tbt1C (zCoord (embedJ X)) (zCoord (embedJ Y)) +
      tbtH (zCoord (embedJ Y)) - tbt1Hz X = 2 * tbt1C (zCoord (embedJ X)) (zCoord (embedJ Y)) +
      tbtH (zCoord (embedJ Y)) by ring]
  have h1 := tbt1_abs_C_le (tbt1_norm_z_le X) (tbt1_norm_z_le Y)
  have h2 := tbt1_abs_H_le (tbt1_norm_z_le Y)
  have h3 := abs_add_le (2 * tbt1C (zCoord (embedJ X)) (zCoord (embedJ Y)))
    (tbtH (zCoord (embedJ Y)))
  rw [abs_mul, abs_two] at h3
  have hX := tbt1_frobNorm_nonneg X
  have hY := tbt1_frobNorm_nonneg Y
  nlinarith

/-- The mean value inequality for `t ↦ t^r`, `r ≥ 1`: `|a^r − b^r| ≤ r max (a, b)^{r−1} |a − b|`. -/
theorem tbt1_rpow_sub_le {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 1 ≤ r) :
    |a ^ r - b ^ r| ≤ r * max a b ^ (r - 1) * |a - b| := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, max_comm, abs_sub_comm a b]; exact this hb ha (le_of_not_ge hab)
  rw [max_eq_left hab, abs_of_nonneg (sub_nonneg.mpr hab),
    abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hb hab (by linarith)))]
  rcases ha.lt_or_eq with ha' | ha'
  · -- Bernoulli: `1 + r (b/a − 1) ≤ (b/a)^r`
    have hs : -1 ≤ b / a - 1 := by have : 0 ≤ b / a := div_nonneg hb ha'.le; linarith
    have key := one_add_mul_self_le_rpow_one_add hs hr
    rw [add_sub_cancel, Real.div_rpow hb ha'.le] at key
    have har : 0 < a ^ r := Real.rpow_pos_of_pos ha' r
    have e : a ^ r = a ^ (r - 1) * a := by
      rw [← Real.rpow_add_one ha'.ne', sub_add_cancel]
    rw [le_div_iff₀ har] at key
    have : r * (b / a - 1) * a ^ r = r * a ^ (r - 1) * (b - a) := by
      rw [e]; field_simp
    nlinarith
  · subst ha'
    have : b = 0 := le_antisymm hab hb
    subst this
    simp

/-- The constant of `tbt1_fp_diff`: `(r* − 1)^r r 8^r + r 8^r + p` with `r = p/2`. -/
noncomputable def tbt1L (p : ℝ) : ℝ :=
  (pStar (p / 2) - 1) ^ (p / 2) * (p / 2) * 8 ^ (p / 2) + (p / 2) * 8 ^ (p / 2) + p

/-- The constant of the homogeneity and Young estimate (`tbt1_fp_young`). -/
noncomputable def tbt1Cp (p δ : ℝ) : ℝ :=
  tbt1L p * (2 ^ p * tbt1L p / δ + 1) ^ (p - 1)

theorem tbt1_pStar_ge {r : ℝ} : r ≤ pStar r := le_max_left _ _

theorem tbt1_L_ge {p : ℝ} (hp : 2 ≤ p) : p ≤ tbt1L p := by
  have h1 : 0 ≤ pStar (p / 2) - 1 := by
    have : p / 2 ≤ pStar (p / 2) := tbt1_pStar_ge; linarith
  have : 0 ≤ (pStar (p / 2) - 1) ^ (p / 2) * (p / 2) * 8 ^ (p / 2) := by positivity
  have : 0 ≤ (p / 2) * 8 ^ (p / 2) := by positivity
  unfold tbt1L; linarith

theorem tbt1_rpow_alg {S y r : ℝ} (hS : 0 < S) :
    (8 * S ^ 2) ^ (r - 1) * (8 * S * y) = 8 ^ r * S ^ (2 * r - 1) * y := by
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast S 2,
    ← Real.rpow_mul hS.le]
  have e1 : (8 : ℝ) ^ r = 8 ^ (r - 1) * 8 := by
    rw [← Real.rpow_add_one (by norm_num : (8 : ℝ) ≠ 0), sub_add_cancel]
  have e2 : S ^ (2 * r - 1) = S ^ ((2 : ℕ) * (r - 1)) * S := by
    rw [← Real.rpow_add_one hS.ne']; congr 1; push_cast; ring
  rw [e1, e2]; ring

/-- The difference estimate: `|f (X + Y) − f (X)| ≤ L (|X| + |Y|)^{p−1} |Y|` for `p ≥ 2` and
`0 ≤ δ ≤ 1`, with `L = tbt1L p` (mean value inequality for `t ↦ t^r` and the quadratic bounds on
`D`, `H`). -/
theorem tbt1_fp_diff {p δ : ℝ} (hp : 2 ≤ p) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (X Y : Matrix (Fin 2) (Fin 3) ℝ) :
    |tbt1Fp p δ (X + Y) - tbt1Fp p δ X| ≤
      tbt1L p * (frobNorm X + frobNorm Y) ^ (p - 1) * frobNorm Y := by
  have hx := tbt1_frobNorm_nonneg X
  have hy := tbt1_frobNorm_nonneg Y
  rcases hy.lt_or_eq with hy' | hy'
  swap
  · have hY : Y = 0 := tbt1_eq_zero_of_frobNorm_eq_zero hy'.symm
    subst hY
    simp only [add_zero, sub_self, abs_zero]
    rw [← hy', mul_zero]
  set S := frobNorm X + frobNorm Y with hS_def
  have hS : 0 < S := by linarith
  set r := p / 2 with hr_def
  have hr : 1 ≤ r := by rw [hr_def]; linarith
  have hα : 0 ≤ pStar r - 1 := by have : r ≤ pStar r := tbt1_pStar_ge; linarith
  have hXY : frobNorm (X + Y) ≤ S := tbt1_frobNorm_add_le X Y
  have hXY0 := tbt1_frobNorm_nonneg (X + Y)
  -- the three terms
  have hD : |‖2 * tbt1Dz (X + Y)‖ ^ r - ‖2 * tbt1Dz X‖ ^ r| ≤
      r * 8 ^ r * S ^ (p - 1) * frobNorm Y := by
    refine (tbt1_rpow_sub_le (norm_nonneg _) (norm_nonneg _) hr).trans ?_
    have hmax : max ‖2 * tbt1Dz (X + Y)‖ ‖2 * tbt1Dz X‖ ≤ 8 * S ^ 2 := by
      refine max_le ((tbt1_norm_Dz_le _).trans ?_) ((tbt1_norm_Dz_le _).trans ?_) <;> gcongr
      linarith
    have h1 : max ‖2 * tbt1Dz (X + Y)‖ ‖2 * tbt1Dz X‖ ^ (r - 1) ≤ (8 * S ^ 2) ^ (r - 1) :=
      Real.rpow_le_rpow (le_max_of_le_left (norm_nonneg _)) hmax (by linarith)
    have h2 : |‖2 * tbt1Dz (X + Y)‖ - ‖2 * tbt1Dz X‖| ≤ 8 * S * frobNorm Y :=
      (abs_norm_sub_norm_le _ _).trans (tbt1_norm_Dz_sub_le X Y)
    calc r * max ‖2 * tbt1Dz (X + Y)‖ ‖2 * tbt1Dz X‖ ^ (r - 1) *
          |‖2 * tbt1Dz (X + Y)‖ - ‖2 * tbt1Dz X‖|
        ≤ r * (8 * S ^ 2) ^ (r - 1) * (8 * S * frobNorm Y) := by gcongr
      _ = r * 8 ^ r * S ^ (p - 1) * frobNorm Y := by
        rw [mul_assoc r, tbt1_rpow_alg hS, show 2 * r - 1 = p - 1 by rw [hr_def]; ring]; ring
  have hH : |(|tbt1Hz (X + Y)| ^ r - |tbt1Hz X| ^ r)| ≤ r * 8 ^ r * S ^ (p - 1) * frobNorm Y := by
    refine (tbt1_rpow_sub_le (abs_nonneg _) (abs_nonneg _) hr).trans ?_
    have hmax : max (|tbt1Hz (X + Y)|) (|tbt1Hz X|) ≤ 8 * S ^ 2 := by
      refine max_le ((tbt1_abs_Hz_le _).trans ?_) ((tbt1_abs_Hz_le _).trans ?_) <;> gcongr
      linarith
    have h1 : max (|tbt1Hz (X + Y)|) (|tbt1Hz X|) ^ (r - 1) ≤ (8 * S ^ 2) ^ (r - 1) :=
      Real.rpow_le_rpow (le_max_of_le_left (abs_nonneg _)) hmax (by linarith)
    have h2 : |(|tbt1Hz (X + Y)| - |tbt1Hz X|)| ≤ 8 * S * frobNorm Y :=
      (abs_abs_sub_abs_le _ _).trans (tbt1_abs_Hz_sub_le X Y)
    calc r * max (|tbt1Hz (X + Y)|) (|tbt1Hz X|) ^ (r - 1) * |(|tbt1Hz (X + Y)| - |tbt1Hz X|)|
        ≤ r * (8 * S ^ 2) ^ (r - 1) * (8 * S * frobNorm Y) := by gcongr
      _ = r * 8 ^ r * S ^ (p - 1) * frobNorm Y := by
        rw [mul_assoc r, tbt1_rpow_alg hS, show 2 * r - 1 = p - 1 by rw [hr_def]; ring]; ring
  have hN : |frobNorm (X + Y) ^ p - frobNorm X ^ p| ≤ p * S ^ (p - 1) * frobNorm Y := by
    refine (tbt1_rpow_sub_le hXY0 hx (by linarith)).trans ?_
    have hmax : max (frobNorm (X + Y)) (frobNorm X) ≤ S := max_le hXY (by linarith)
    have h1 : max (frobNorm (X + Y)) (frobNorm X) ^ (p - 1) ≤ S ^ (p - 1) :=
      Real.rpow_le_rpow (le_max_of_le_right hx) hmax (by linarith)
    have h2 : |frobNorm (X + Y) - frobNorm X| ≤ frobNorm Y := by
      rw [abs_sub_le_iff]
      constructor
      · linarith
      · have := tbt1_frobNorm_add_le (X + Y) ((-1 : ℝ) • Y)
        rw [show X + Y + (-1 : ℝ) • Y = X by module, tbt1_frobNorm_smul] at this
        norm_num at this; linarith
    have h3 : p * max (frobNorm (X + Y)) (frobNorm X) ^ (p - 1) *
        |frobNorm (X + Y) - frobNorm X| ≤ p * S ^ (p - 1) * frobNorm Y := by
      gcongr
    exact h3
  -- assembling
  have hSp : 0 ≤ S ^ (p - 1) * frobNorm Y := mul_nonneg (Real.rpow_nonneg hS.le _) hy
  have e : tbt1Fp p δ (X + Y) - tbt1Fp p δ X =
      (pStar r - 1) ^ r * (‖2 * tbt1Dz (X + Y)‖ ^ r - ‖2 * tbt1Dz X‖ ^ r) -
        (|tbt1Hz (X + Y)| ^ r - |tbt1Hz X| ^ r) + δ * (frobNorm (X + Y) ^ p - frobNorm X ^ p) := by
    simp only [tbt1Fp, hr_def]; ring
  rw [e]
  have hαr : 0 ≤ (pStar r - 1) ^ r := Real.rpow_nonneg hα _
  have t1 := abs_add_le ((pStar r - 1) ^ r * (‖2 * tbt1Dz (X + Y)‖ ^ r - ‖2 * tbt1Dz X‖ ^ r) -
    (|tbt1Hz (X + Y)| ^ r - |tbt1Hz X| ^ r)) (δ * (frobNorm (X + Y) ^ p - frobNorm X ^ p))
  have t2 := abs_sub ((pStar r - 1) ^ r * (‖2 * tbt1Dz (X + Y)‖ ^ r - ‖2 * tbt1Dz X‖ ^ r))
    (|tbt1Hz (X + Y)| ^ r - |tbt1Hz X| ^ r)
  rw [abs_mul, abs_of_nonneg hαr] at t2
  rw [abs_mul, abs_of_nonneg hδ0] at t1
  have t3 := mul_le_mul_of_nonneg_left hD hαr
  have t4 := mul_le_mul_of_nonneg_left hN hδ0
  have t5 : δ * (p * S ^ (p - 1) * frobNorm Y) ≤ p * (S ^ (p - 1) * frobNorm Y) := by
    have := mul_le_mul_of_nonneg_right hδ1 (mul_nonneg (by linarith : (0 : ℝ) ≤ p) hSp)
    nlinarith
  have eL : tbt1L p * S ^ (p - 1) * frobNorm Y = (pStar r - 1) ^ r * (r * 8 ^ r * S ^ (p - 1) *
      frobNorm Y) + r * 8 ^ r * S ^ (p - 1) * frobNorm Y + p * (S ^ (p - 1) * frobNorm Y) := by
    simp only [tbt1L, hr_def]; ring
  rw [eL]
  linarith

/-- **"By homogeneity and Young's inequality"**, with explicit constants: for `p ≥ 2` and
`0 < δ ≤ 1`, `|f (X + Y) − f (X)| ≤ (δ/2) |X|^p + C_p (δ) |Y|^p`, with
`C_p (δ) = L (2^p L / δ + 1)^{p−1}` and `L = tbt1L p` (the cases `|Y| ≤ θ |X|` and `|Y| > θ |X|`,
`θ = δ / (2^p L)`). -/
theorem tbt1_fp_young {p δ : ℝ} (hp : 2 ≤ p) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (X Y : Matrix (Fin 2) (Fin 3) ℝ) :
    |tbt1Fp p δ (X + Y) - tbt1Fp p δ X| ≤ δ / 2 * frobNorm X ^ p + tbt1Cp p δ * frobNorm Y ^ p := by
  have hx := tbt1_frobNorm_nonneg X
  have hy := tbt1_frobNorm_nonneg Y
  set L := tbt1L p with hL_def
  have hL : 2 ≤ L := le_trans hp (tbt1_L_ge hp)
  have h2p : 1 ≤ (2 : ℝ) ^ p := Real.one_le_rpow (by norm_num) (by linarith)
  set θ := δ / (2 ^ p * L) with hθ_def
  have hθ : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ_def, div_le_one (by positivity)]; nlinarith
  have hdiff := tbt1_fp_diff hp hδ.le hδ1 X Y
  rw [← hL_def] at hdiff
  have hA : 0 ≤ δ / 2 * frobNorm X ^ p := by positivity
  have hB : 0 ≤ tbt1Cp p δ * frobNorm Y ^ p := by
    unfold tbt1Cp; positivity
  by_cases hcase : frobNorm Y ≤ θ * frobNorm X
  · -- `|Y| ≤ θ |X|`
    have hS : frobNorm X + frobNorm Y ≤ 2 * frobNorm X := by nlinarith
    have h1 : (frobNorm X + frobNorm Y) ^ (p - 1) ≤ (2 * frobNorm X) ^ (p - 1) :=
      Real.rpow_le_rpow (by positivity) hS (by linarith)
    have h2 : L * (frobNorm X + frobNorm Y) ^ (p - 1) * frobNorm Y ≤
        L * (2 * frobNorm X) ^ (p - 1) * (θ * frobNorm X) := by gcongr
    rcases hx.lt_or_eq with hx' | hx'
    · have e : L * (2 * frobNorm X) ^ (p - 1) * (θ * frobNorm X) = δ / 2 * frobNorm X ^ p := by
        rw [Real.mul_rpow (by norm_num) hx, hθ_def]
        have e1 : frobNorm X ^ p = frobNorm X ^ (p - 1) * frobNorm X := by
          rw [← Real.rpow_add_one hx'.ne', sub_add_cancel]
        have e2 : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
          rw [← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0), sub_add_cancel]
        rw [e1, e2]; field_simp
      linarith
    · have : frobNorm Y = 0 := le_antisymm (by rw [← hx'] at hcase; linarith) hy
      rw [this, mul_zero] at hdiff
      linarith
  · -- `|Y| > θ |X|`
    push Not at hcase
    have hS : frobNorm X + frobNorm Y ≤ (1 / θ + 1) * frobNorm Y := by
      have : frobNorm X ≤ frobNorm Y / θ := by rw [le_div_iff₀ hθ]; linarith
      have : frobNorm Y / θ = 1 / θ * frobNorm Y := by ring
      linarith
    have h1 : (frobNorm X + frobNorm Y) ^ (p - 1) ≤ ((1 / θ + 1) * frobNorm Y) ^ (p - 1) :=
      Real.rpow_le_rpow (by positivity) hS (by linarith)
    have e1 : 1 / θ = 2 ^ p * L / δ := by rw [hθ_def]; field_simp
    have h2 : L * (frobNorm X + frobNorm Y) ^ (p - 1) * frobNorm Y ≤ tbt1Cp p δ * frobNorm Y ^ p := by
      rcases hy.lt_or_eq with hy' | hy'
      · calc L * (frobNorm X + frobNorm Y) ^ (p - 1) * frobNorm Y
            ≤ L * ((1 / θ + 1) * frobNorm Y) ^ (p - 1) * frobNorm Y := by gcongr
          _ = tbt1Cp p δ * frobNorm Y ^ p := by
            rw [Real.mul_rpow (by positivity) hy, e1, tbt1Cp, ← hL_def,
              show frobNorm Y ^ p = frobNorm Y ^ (p - 1) * frobNorm Y by
                rw [← Real.rpow_add_one hy'.ne', sub_add_cancel]]
            ring
      · have h0 : frobNorm Y = 0 := hy'.symm
        rw [h0] at hB ⊢
        rw [mul_zero]; exact hB
    linarith

/-! ### Homogeneity and continuity -/

theorem tbt1_Dz_smul (t : ℝ) (A : Matrix (Fin 2) (Fin 3) ℝ) :
    tbt1Dz (t • A) = (t : ℂ) ^ 2 * tbt1Dz A := by
  simp only [tbt1Dz, tbt1_zJ_smul, tbtD]; ring

theorem tbt1_Hz_smul (t : ℝ) (A : Matrix (Fin 2) (Fin 3) ℝ) :
    tbt1Hz (t • A) = t ^ 2 * tbt1Hz A := by
  simp only [tbt1Hz, tbt1_zJ_smul, tbtH, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring

theorem tbt1_sq_rpow (t p : ℝ) : (t ^ 2) ^ (p / 2) = |t| ^ p := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]
  congr 1; push_cast; ring

/-- `f_{r,δ,C}` is `p`-homogeneous: `f (t A) = |t|^p f (A)`. -/
theorem tbt1_Fp_smul {p : ℝ} (δ t : ℝ) (A : Matrix (Fin 2) (Fin 3) ℝ) :
    tbt1Fp p δ (t • A) = |t| ^ p * tbt1Fp p δ A := by
  simp only [tbt1Fp, tbt1_Dz_smul, tbt1_Hz_smul, tbt1_frobNorm_smul]
  rw [show (2 : ℂ) * ((t : ℂ) ^ 2 * tbt1Dz A) = ((t ^ 2 : ℝ) : ℂ) * (2 * tbt1Dz A) by
      push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
    Real.mul_rpow (sq_nonneg t) (norm_nonneg _), abs_mul, abs_of_nonneg (sq_nonneg t),
    Real.mul_rpow (sq_nonneg t) (abs_nonneg _), Real.mul_rpow (abs_nonneg t)
      (tbt1_frobNorm_nonneg _), tbt1_sq_rpow]
  ring

/-- `g = f ∘ π + Λ^p |π^⊥ ·|^p` is `p`-homogeneous. -/
theorem tbt1_G_isPHomogeneous (p δ Λ : ℝ) : IsPHomogeneous p (tbt1G p δ Λ) := by
  intro t A
  simp only [tbt1G, tbt3_projL3_smul, tbt1_Fp_smul]
  rw [show t • A - t • projL3 A = t • (A - projL3 A) by rw [smul_sub], tbt1_frobNorm_smul,
    Real.mul_rpow (abs_nonneg t) (tbt1_frobNorm_nonneg _)]
  ring

theorem tbt1_continuous_zJ (k : Fin 3) :
    Continuous fun A : Matrix (Fin 2) (Fin 3) ℝ => zCoord (embedJ A) k :=
  (tbt_continuous_zCoord k).comp tbt_continuous_embedJ

theorem tbt1_continuous_Dz : Continuous tbt1Dz := by
  have h0 := tbt1_continuous_zJ 0
  have h1 := tbt1_continuous_zJ 1
  have h2 := tbt1_continuous_zJ 2
  unfold tbt1Dz tbtD
  fun_prop

theorem tbt1_continuous_Hz : Continuous tbt1Hz := by
  have h0 := tbt1_continuous_zJ 0
  have h1 := tbt1_continuous_zJ 1
  have h2 := tbt1_continuous_zJ 2
  unfold tbt1Hz tbtH
  fun_prop

theorem tbt1_continuousAt_pStar {r : ℝ} (hr : r ≠ 1) : ContinuousAt pStar r := by
  unfold pStar
  exact continuousAt_id.max (continuousAt_id.div (continuousAt_id.sub continuousAt_const)
    (sub_ne_zero.mpr hr))

/-- `(p, A) ↦ g_{p,δ,Λ} (A)` is continuous at every `(p, A)` with `p > 2`. -/
theorem tbt1_continuousAt_G {δ Λ : ℝ} (hΛ : 0 < Λ) (x : ℝ × Matrix (Fin 2) (Fin 3) ℝ)
    (hx : 2 < x.1) : ContinuousAt (fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ => tbt1G y.1 δ Λ y.2) x := by
  have hπ : Continuous projL3 := tbt1_continuous_proj isFrobProj_projL3
  have hp2 : ContinuousAt (fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ => y.1 / 2) x :=
    (continuous_fst.div_const 2).continuousAt
  have hp1 : ContinuousAt (fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ => y.1) x :=
    continuous_fst.continuousAt
  have hr1 : x.1 / 2 ≠ 1 := by intro h; linarith
  have hps : 0 < pStar (x.1 / 2) - 1 := by
    have : x.1 / 2 ≤ pStar (x.1 / 2) := tbt1_pStar_ge; linarith
  have ha : ContinuousAt (fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ =>
      (pStar (y.1 / 2) - 1) ^ (y.1 / 2)) x :=
    ((ContinuousAt.comp (f := fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ => y.1 / 2)
      (tbt1_continuousAt_pStar hr1) hp2).sub continuousAt_const).rpow hp2 (Or.inl hps.ne')
  have hb : ContinuousAt (fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ =>
      ‖2 * tbt1Dz (projL3 y.2)‖ ^ (y.1 / 2)) x :=
    ((continuous_const.mul (tbt1_continuous_Dz.comp (hπ.comp continuous_snd))).norm.continuousAt).rpow
      hp2 (Or.inr (by linarith))
  have hc : ContinuousAt (fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ =>
      |tbt1Hz (projL3 y.2)| ^ (y.1 / 2)) x :=
    ((tbt1_continuous_Hz.comp (hπ.comp continuous_snd)).abs.continuousAt).rpow hp2
      (Or.inr (by linarith))
  have hd : ContinuousAt (fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ =>
      frobNorm (projL3 y.2) ^ y.1) x :=
    ((tbt1_continuous_frobNorm.comp (hπ.comp continuous_snd)).continuousAt).rpow hp1
      (Or.inr (by linarith))
  have he : ContinuousAt (fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ => Λ ^ y.1) x :=
    continuousAt_const.rpow hp1 (Or.inl hΛ.ne')
  have hf : ContinuousAt (fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ =>
      frobNorm (y.2 - projL3 y.2) ^ y.1) x :=
    ((tbt1_continuous_frobNorm.comp (continuous_snd.sub (hπ.comp continuous_snd))).continuousAt).rpow
      hp1 (Or.inr (by linarith))
  exact ((ha.mul hb).sub hc |>.add (continuousAt_const.mul hd)).add (he.mul hf)

theorem tbt1_continuous_G {p δ Λ : ℝ} (hΛ : 0 < Λ) (hp : 2 < p) : Continuous (tbt1G p δ Λ) := by
  rw [continuous_iff_continuousAt]
  intro A
  exact (tbt1_continuousAt_G hΛ (p, A) hp).comp (Continuous.prodMk_right p).continuousAt

theorem tbt1_G_zero {p δ Λ : ℝ} (hp : 0 < p) : tbt1G p δ Λ 0 = 0 := by
  have h := tbt1_G_isPHomogeneous p δ Λ 0 0
  rw [zero_smul, abs_zero, Real.zero_rpow hp.ne', zero_mul] at h
  exact h

/-! ### The witness integral is continuous in `p` -/

theorem tbt1_jac_bound {φ : (Fin 3 → ℝ) → Fin 2 → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (x : Fin 3 → ℝ) (i : Fin 2) (k : Fin 3) : |jac φ x i k| ≤ K := by
  have hi : LipschitzWith K fun y => φ y i := by
    have := (LipschitzWith.eval (α := fun _ : Fin 2 => ℝ) i).comp hφ
    rw [one_mul] at this
    exact this
  simp only [jac, Matrix.of_apply]
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ (fun y => φ y i) x).le_opNorm _).trans ?_
  have h1 : ‖(Pi.single k (1 : ℝ) : Fin 3 → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  calc ‖fderiv ℝ (fun y => φ y i) x‖ * ‖(Pi.single k (1 : ℝ) : Fin 3 → ℝ)‖
      ≤ K * 1 := mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hi) h1 (norm_nonneg _) K.2
    _ = K := mul_one _

theorem tbt1_measurable_jac (φ : (Fin 3 → ℝ) → Fin 2 → ℝ) : Measurable fun x => jac φ x :=
  Measurable.of_eval_matrix _ fun i k => by
    simp only [jac, Matrix.of_apply]
    exact measurable_fderiv_apply_const ℝ (fun y => φ y i) _

/-- The matrices with entries in `[−K, K]`. -/
def tbt1Box (K : ℝ) : Set (Matrix (Fin 2) (Fin 3) ℝ) := {A | ∀ i j, |A i j| ≤ K}

theorem tbt1_isCompact_box (K : ℝ) : IsCompact (tbt1Box K) := by
  have : tbt1Box K = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 3 =>
      Set.Icc (-K) K := by
    ext A
    simp only [tbt1Box, Set.mem_ofPred_eq, abs_le]
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

/-- For a Lipschitz `φ`, the integrands `x ↦ g_{p,δ,Λ} (∇φ (x))`, `p ∈ [7/2, 9/2]`, are uniformly
bounded and measurable, so integrable on the unit cube, and their integral is continuous at
`p = 4` (dominated convergence). -/
theorem tbt1_witness_integral {δ Λ : ℝ} (hΛ : 0 < Λ) {φ : (Fin 3 → ℝ) → Fin 2 → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) :
    (∀ p ∈ Set.Icc (7 / 2 : ℝ) (9 / 2),
      IntegrableOn (fun x => tbt1G p δ Λ (0 + jac φ x)) (unitCube 3)) ∧
    ContinuousAt (fun p => ∫ x in unitCube 3, tbt1G p δ Λ (0 + jac φ x)) 4 := by
  have hbox : ∀ x, (0 + jac φ x) ∈ tbt1Box K := fun x i j => by
    rw [zero_add]; exact tbt1_jac_bound hφ x i j
  have hcpt := (isCompact_Icc (a := (7 / 2 : ℝ)) (b := 9 / 2)).prod (tbt1_isCompact_box K)
  have hcont : ContinuousOn (fun y : ℝ × Matrix (Fin 2) (Fin 3) ℝ => tbt1G y.1 δ Λ y.2)
      (Set.Icc (7 / 2 : ℝ) (9 / 2) ×ˢ tbt1Box K) := fun y hy =>
    (tbt1_continuousAt_G hΛ y (by linarith [hy.1.1])).continuousWithinAt
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn hcont
  have hmeas : ∀ p : ℝ, 2 < p →
      AEStronglyMeasurable (fun x => tbt1G p δ Λ (0 + jac φ x)) (volume.restrict (unitCube 3)) :=
    fun p hp => by
      simp only [zero_add]
      exact ((tbt1_continuous_G hΛ hp).measurable.comp (tbt1_measurable_jac φ)).aestronglyMeasurable
  have hbound : ∀ p ∈ Set.Icc (7 / 2 : ℝ) (9 / 2), ∀ x,
      ‖tbt1G p δ Λ (0 + jac φ x)‖ ≤ M := fun p hp x => hM (p, 0 + jac φ x) ⟨hp, hbox x⟩
  have hint : Integrable (fun _ : Fin 3 → ℝ => M) (volume.restrict (unitCube 3)) :=
    integrableOn_const (by rw [volume_unitCube]; simp)
  refine ⟨fun p hp => hint.mono' (hmeas p (by linarith [hp.1]))
    (Filter.Eventually.of_forall (hbound p hp)), ?_⟩
  refine continuousAt_of_dominated ?_ ?_ hint ?_
  · filter_upwards [Ioi_mem_nhds (show (2 : ℝ) < 4 by norm_num)] with p hp
    exact hmeas p hp
  · filter_upwards [Icc_mem_nhds (show (7 / 2 : ℝ) < 4 by norm_num)
      (show (4 : ℝ) < 9 / 2 by norm_num)] with p hp
    exact Filter.Eventually.of_forall (hbound p hp)
  · exact Filter.Eventually.of_forall fun x =>
      (tbt1_continuousAt_G (δ := δ) hΛ (4, 0 + jac φ x) (by norm_num)).comp
        (f := fun p : ℝ => (p, 0 + jac φ x)) (Continuous.prodMk_left (0 + jac φ x)).continuousAt

/-! ### The constants at `p = 4` and their continuity in `p` -/

theorem tbt1_pStar_two : pStar 2 = 2 := by norm_num [pStar]

theorem tbt1_pStar_four : pStar 4 = 4 := by norm_num [pStar]

theorem tbt1_rpow_nat (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n := Real.rpow_natCast x n

theorem tbt1_L_four : tbt1L 4 = 260 := by
  unfold tbt1L
  rw [show (4 : ℝ) / 2 = ((2 : ℕ) : ℝ) by norm_num, tbt1_rpow_nat, tbt1_rpow_nat]
  norm_num [tbt1_pStar_two]

/-- The penalty `Λ₀ (p, δ)` of Lemma 5.1 (1) for `f_{r,δ,C}` on `𝓛₃` (`κ = 2`). -/
noncomputable def tbt1Lam0 (δ p : ℝ) : ℝ :=
  (tbt1Cp p δ * ((pStar p - 1) ^ p * max 2 0 ^ p)) ^ (1 / p)

theorem tbt1_Cp_pos {p δ : ℝ} (hp : 2 ≤ p) (hδ : 0 < δ) : 0 < tbt1Cp p δ := by
  have hL : 0 < tbt1L p := lt_of_lt_of_le (by linarith) (tbt1_L_ge hp)
  unfold tbt1Cp
  exact mul_pos hL (Real.rpow_pos_of_pos (by positivity) _)

theorem tbt1_continuousAt_L : ContinuousAt tbt1L 4 := by
  have hp2 : ContinuousAt (fun p : ℝ => p / 2) 4 := (continuous_id.div_const 2).continuousAt
  have hps : ContinuousAt (fun p : ℝ => pStar (p / 2)) 4 :=
    ContinuousAt.comp (f := fun p : ℝ => p / 2) (tbt1_continuousAt_pStar (by norm_num)) hp2
  have h1 : ContinuousAt (fun p : ℝ => (pStar (p / 2) - 1) ^ (p / 2)) 4 :=
    (hps.sub continuousAt_const).rpow hp2 (Or.inl (by
      show pStar (4 / 2) - 1 ≠ 0
      rw [show (4 : ℝ) / 2 = 2 by norm_num, tbt1_pStar_two]; norm_num))
  have h8 : ContinuousAt (fun p : ℝ => (8 : ℝ) ^ (p / 2)) 4 :=
    continuousAt_const.rpow hp2 (Or.inl (by norm_num))
  unfold tbt1L
  exact ((h1.mul hp2).mul h8).add (hp2.mul h8) |>.add continuousAt_id

theorem tbt1_continuousAt_Lam0 {δ : ℝ} (hδ : 0 < δ) : ContinuousAt (tbt1Lam0 δ) 4 := by
  have hL := tbt1_continuousAt_L
  have h2p : ContinuousAt (fun p : ℝ => (2 : ℝ) ^ p) 4 :=
    continuousAt_const.rpow continuousAt_id (Or.inl (by norm_num))
  have hCp : ContinuousAt (fun p => tbt1Cp p δ) 4 := by
    unfold tbt1Cp
    refine hL.mul (((h2p.mul hL).div_const δ |>.add continuousAt_const).rpow
      (continuousAt_id.sub continuousAt_const) (Or.inl ?_))
    show 2 ^ (4 : ℝ) * tbt1L 4 / δ + 1 ≠ 0
    rw [tbt1_L_four]; positivity
  have hps : ContinuousAt (fun p : ℝ => (pStar p - 1) ^ p) 4 :=
    ((tbt1_continuousAt_pStar (by norm_num)).sub continuousAt_const).rpow continuousAt_id
      (Or.inl (by show pStar 4 - 1 ≠ 0; rw [tbt1_pStar_four]; norm_num))
  have hm : ContinuousAt (fun p : ℝ => (max 2 0 : ℝ) ^ p) 4 :=
    continuousAt_const.rpow continuousAt_id (Or.inl (by norm_num))
  have hX0 : tbt1Cp 4 δ * ((pStar 4 - 1) ^ (4 : ℝ) * max 2 0 ^ (4 : ℝ)) ≠ 0 := by
    have := tbt1_Cp_pos (p := 4) (by norm_num) hδ
    rw [tbt1_pStar_four]
    positivity
  unfold tbt1Lam0
  exact (hCp.mul (hps.mul hm)).rpow (continuousAt_const.div continuousAt_id (by norm_num))
    (Or.inl hX0)

/-- The constant `K` (any `K > (260 · 4161³ · 1296)^{1/4}` would do). -/
noncomputable def tbt1K : ℝ := 2 * (260 * 4161 ^ 3 * 1296)

/-- At `p = 4`, `Λ₀ (4, δ) < Λ := (K⁴ / δ³)^{1/4}` for `0 < δ ≤ 1`. -/
theorem tbt1_Lam0_four_lt {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    tbt1Lam0 δ 4 < (tbt1K ^ 4 / δ ^ 3) ^ (1 / 4 : ℝ) := by
  unfold tbt1Lam0
  set X := tbt1Cp 4 δ * ((pStar 4 - 1) ^ (4 : ℝ) * max 2 0 ^ (4 : ℝ))
  have hX : X = 260 * (4160 / δ + 1) ^ 3 * 1296 := by
    simp only [X, tbt1Cp, tbt1_L_four, tbt1_pStar_four]
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, tbt1_rpow_nat, tbt1_rpow_nat, tbt1_rpow_nat,
      show ((4 : ℕ) : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, tbt1_rpow_nat]
    norm_num
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have h1 : 4160 / δ + 1 ≤ 4161 / δ := by
    rw [div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]; linarith
  have h2 : X ≤ 260 * 4161 ^ 3 * 1296 / δ ^ 3 := by
    rw [hX]
    have := pow_le_pow_left₀ (by positivity) h1 3
    rw [div_pow] at this
    calc 260 * (4160 / δ + 1) ^ 3 * 1296 ≤ 260 * (4161 ^ 3 / δ ^ 3) * 1296 := by gcongr
      _ = 260 * 4161 ^ 3 * 1296 / δ ^ 3 := by ring
  have h3 : 260 * 4161 ^ 3 * 1296 / δ ^ 3 < tbt1K ^ 4 / δ ^ 3 := by
    apply div_lt_div_of_pos_right _ (by positivity)
    unfold tbt1K; norm_num
  rw [show (1 : ℝ) / 4 = 1 / (4 : ℝ) from rfl]
  exact Real.rpow_lt_rpow hX0 (h2.trans_lt h3) (by norm_num)

theorem tbt1_frobNorm_rpow_four (A : Matrix (Fin 2) (Fin 3) ℝ) :
    frobNorm A ^ (4 : ℝ) = frobSq A ^ 2 := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, tbt1_rpow_nat, frobNorm,
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (tbt_frobSq_nonneg A)]

/-- `f_{2,δ,1} = q₃ + δ |·|⁴`. -/
theorem tbt1_Fp_four (δ : ℝ) (B : Matrix (Fin 2) (Fin 3) ℝ) :
    tbt1Fp 4 δ B = q3 B + δ * frobSq B ^ 2 := by
  unfold tbt1Fp
  rw [show (4 : ℝ) / 2 = ((2 : ℕ) : ℝ) by norm_num, tbt1_rpow_nat, tbt1_rpow_nat, tbt1_rpow_nat,
    show ((2 : ℕ) : ℝ) = 2 by norm_num, tbt1_pStar_two, tbt1_frobNorm_rpow_four, q3,
    tbt_quarticQ_eq, sq_abs, norm_mul, Complex.norm_two, tbt1Dz, tbt1Hz]
  ring

/-- At `p = 4` and `Λ = (K⁴/δ³)^{1/4}`, `g_{4,δ,Λ} ≤ q_{δ, K/δ}` pointwise:
`δ |π A|⁴ + (K⁴/δ³) |π^⊥ A|⁴ ≤ δ (|π A|² + (K/δ)² |π^⊥ A|²)²`. -/
theorem tbt1_G_four_le {δ K : ℝ} (hδ : 0 < δ) (A : Matrix (Fin 2) (Fin 3) ℝ) :
    tbt1G 4 δ ((K ^ 4 / δ ^ 3) ^ (1 / 4 : ℝ)) A ≤ qDeltaLambda δ (K / δ) A := by
  have hΛ : ((K ^ 4 / δ ^ 3) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = K ^ 4 / δ ^ 3 := by
    rw [← Real.rpow_mul (by positivity)]; norm_num
  unfold tbt1G qDeltaLambda
  rw [hΛ, tbt1_frobNorm_rpow_four, tbt1_Fp_four]
  have ha := tbt_frobSq_nonneg (projL3 A)
  have hb := tbt_frobSq_nonneg (A - projL3 A)
  have e : δ * ((K / δ) ^ 2) ^ 2 = K ^ 4 / δ ^ 3 := by field_simp
  have : 0 ≤ 2 * δ * (K / δ) ^ 2 * (frobSq (projL3 A) * frobSq (A - projL3 A)) := by positivity
  nlinarith

theorem tbt1_continuous_Fp {p : ℝ} (δ : ℝ) (hp : 0 < p) : Continuous (tbt1Fp p δ) := by
  unfold tbt1Fp
  have h2 : 0 ≤ p / 2 := by linarith
  exact ((continuous_const.mul ((continuous_const.mul tbt1_continuous_Dz).norm.rpow_const
    fun _ => Or.inr h2)).sub (tbt1_continuous_Hz.abs.rpow_const fun _ => Or.inr h2)).add
    (continuous_const.mul (tbt1_continuous_frobNorm.rpow_const fun _ => Or.inr hp.le))

/-! ### Theorem 1.3 (b) -/

/-- **Proof of Theorem 1.3 (b)** (`cs-thm1.3b-witness`, TeX lines 2031–2044): for `p`
sufficiently close to `4` there is a continuous `p`-homogeneous integrand on `ℝ^{2×3}` that is
rank-one convex at `0` but not quasiconvex at `0`. Burkholder's inequality (Theorem 2.3) enters
through Lemma 5.1 (1) and the coercivity of `f_{r,δ,C}`.

Proof, as in the paper: the integrand is `g = f_{r,δ,C} ∘ π + Λ^p |π^⊥ ·|^p` (`tbt1G`) with
`f_{r,δ,C} (A) = C^r |2D (JA)|^r − |H (JA)|^r + δ |A|^{2r}`, `r = p/2`, `C = r* − 1`. It is
`p`-homogeneous and continuous; `C = r* − 1` makes `f` coercive on `𝓛₃`-valued rank-one
martingales (`tbt1_coercive`, Burkholder's inequality for `H` and `2D`), so Lemma 5.1 (1) makes
`g` rank-one convex at `0` once `Λ ≥ Λ₀ (p, δ)`. At `p = 4`, `f = q₃ + δ |·|⁴` and
`g_{4,δ,Λ} ≤ q_{δ,K/δ}` for `Λ = (K⁴/δ³)^{1/4}` (`tbt1_G_four_le`), so the witness of
Theorem 1.3 (a) (`twoByThree_not_quasiconvexAt_qDeltaLambda`) gives `∫ g_{4,δ,Λ} (∇φ) < 0`.

Departure from the paper (reason 1, inventory E4): the paper concludes "by continuity of the
rank-one convexity and quasiconvexity estimates", which needs the constant `Λ` of Lemma 5.1 (1) to
be uniform for `p` near `4` (Lemma 5.1 (1) is stated for a fixed `p`), and the cut-off witness to be
fixed before `p` varies. Here the constants are explicit: the homogeneity and Young estimate holds
with `C_p (δ) = L (2^p L / δ + 1)^{p−1}`, `L = tbt1L p` (`tbt1_fp_young`), Lemma 5.1 (1) is used in
its quantitative form (`lemma5_1_part1_quant`), so `Λ₀ (p, δ)` is continuous in `p`
(`tbt1_continuousAt_Lam0`); `K` is fixed first (`tbt1K`), then `δ` from Theorem 1.3 (a), then
`Λ = (K⁴/δ³)^{1/4} > Λ₀ (4, δ)`; and `p ↦ ∫ g_{p,δ,Λ} (∇φ)` is continuous at `4` by dominated
convergence (`tbt1_witness_integral`). The envelope step of the paper ("finally taking the rank-one
convex envelope") belongs to Theorem 1.3 (b) itself, not to this witness. -/
theorem twoByThree_theorem1_3_b_witness :
    ∃ ε > 0, ∀ p : ℝ, |p - 4| < ε → ∃ g : Matrix (Fin 2) (Fin 3) ℝ → ℝ,
      Continuous g ∧ IsPHomogeneous p g ∧ RankOneConvexAt g 0 ∧ ¬ QuasiconvexAt g 0 := by
  have hK : 0 < tbt1K := by unfold tbt1K; norm_num
  obtain ⟨δ₀, hδ₀, hq⟩ := twoByThree_not_quasiconvexAt_qDeltaLambda tbt1K
  set δ : ℝ := min (δ₀ / 2) (1 / 2) with hδ_def
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδδ₀ : δ < δ₀ := (min_le_left _ _).trans_lt (by linarith)
  set Λ : ℝ := (tbt1K ^ 4 / δ ^ 3) ^ (1 / 4 : ℝ) with hΛ_def
  have hΛ : 0 < Λ := Real.rpow_pos_of_pos (by positivity) _
  -- the witness of Theorem 1.3 (a)
  have hnq := hq δ hδ hδδ₀
  simp only [QuasiconvexAt, not_forall] at hnq
  obtain ⟨φ, K', hφ, h0, hint, hlt⟩ := hnq
  rw [not_le, tbt4_qDeltaLambda_zero] at hlt
  obtain ⟨hintp, hcont⟩ := tbt1_witness_integral (δ := δ) hΛ hφ
  have hI4 : ∫ x in unitCube 3, tbt1G 4 δ Λ (0 + jac φ x) < 0 :=
    (integral_mono (hintp 4 ⟨by norm_num, by norm_num⟩) hint
      fun x => tbt1_G_four_le hδ _).trans_lt hlt
  -- `ε` from the continuity of `Λ₀ (·, δ)` and of the witness integral at `p = 4`
  have hev1 : ∀ᶠ p in 𝓝 (4 : ℝ), tbt1Lam0 δ p < Λ :=
    (tbt1_continuousAt_Lam0 hδ).eventually (Iio_mem_nhds (tbt1_Lam0_four_lt hδ hδ1))
  have hev2 : ∀ᶠ p in 𝓝 (4 : ℝ), ∫ x in unitCube 3, tbt1G p δ Λ (0 + jac φ x) < 0 :=
    hcont.eventually (Iio_mem_nhds hI4)
  have hev3 : ∀ᶠ p in 𝓝 (4 : ℝ), p ∈ Set.Ioo (7 / 2 : ℝ) (9 / 2) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp (hev1.and (hev2.and hev3))
  refine ⟨ε, hε, fun p hp => ?_⟩
  obtain ⟨hΛ0, hneg, hrange⟩ := hall (by rw [Real.dist_eq]; exact hp)
  have hp2 : 2 < p := by linarith [hrange.1]
  refine ⟨tbt1G p δ Λ, tbt1_continuous_G hΛ hp2, tbt1_G_isPHomogeneous p δ Λ, ?_, ?_⟩
  · -- rank-one convex at `0`, by Lemma 5.1 (1) with explicit constants
    exact lemma5_1_part1_quant L3Submodule projL3 isFrobProj_projL3 2 hasRankOneCorrection_L3
      (p := p) (by linarith) (tbt1Fp p δ) (tbt1_continuous_Fp δ (by linarith)).continuousOn
      (fun t ht X _ => by rw [tbt1_Fp_smul, abs_of_pos ht]) hδ (tbt1_coercive hp2 δ)
      (tbt1Cp p δ) (tbt1_Cp_pos hp2.le hδ).le (fun X _ Y _ => tbt1_fp_young hp2.le hδ hδ1 X Y)
      Λ hΛ0.le
  · -- not quasiconvex at `0`: the same witness `φ`
    intro hqc
    have := hqc φ K' hφ h0 (hintp p ⟨hrange.1.le, hrange.2.le⟩)
    rw [tbt1_G_zero (by linarith)] at this
    linarith

end Cassese
