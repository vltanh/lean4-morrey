module

public import Morrey.Cassese.TwoByThree.Basic

/-!
# Proposition 5.1: finite prelaminates

Finite prelaminates given by lists of weighted atoms (`tbt6Meas`), the chain of symmetric splittings
that reaches a prescribed atom `A = Σ E_i` from `δ₀` (`tbt6Disc`), and the inequality
`f (0) ≤ ∫ f dμ` for prelaminates centred at `0` when `f` is rank-one convex at `0` (from the
envelope formula, Proposition 2.1).

Helpers are prefixed `tbt6_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-- The measure `Σ w_i δ_{x_i}` of a list of weighted atoms. -/
noncomputable def tbt6Meas (l : List (ℝ × Matrix (Fin d) (Fin m) ℝ)) :
    Measure (Matrix (Fin d) (Fin m) ℝ) :=
  (l.map fun p => ENNReal.ofReal p.1 • Measure.dirac p.2).sum

theorem tbt6_meas_nil : tbt6Meas ([] : List (ℝ × Matrix (Fin d) (Fin m) ℝ)) = 0 := rfl

theorem tbt6_meas_cons (p : ℝ × Matrix (Fin d) (Fin m) ℝ) (l : List (ℝ × Matrix (Fin d) (Fin m) ℝ)) :
    tbt6Meas (p :: l) = ENNReal.ofReal p.1 • Measure.dirac p.2 + tbt6Meas l := by
  simp [tbt6Meas]

theorem tbt6_meas_append (l l' : List (ℝ × Matrix (Fin d) (Fin m) ℝ)) :
    tbt6Meas (l ++ l') = tbt6Meas l + tbt6Meas l' := by
  simp [tbt6Meas]

theorem tbt6_integrable_meas {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (l : List (ℝ × Matrix (Fin d) (Fin m) ℝ)) : Integrable g (tbt6Meas l) := by
  induction l with
  | nil => simp [tbt6_meas_nil]
  | cons p l ih =>
    rw [tbt6_meas_cons]
    refine Integrable.add_measure ?_ ih
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- `∫ g d(Σ w_i δ_{x_i}) = Σ w_i g (x_i)` for nonnegative weights. -/
theorem tbt6_integral_meas {g : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (l : List (ℝ × Matrix (Fin d) (Fin m) ℝ)) (hl : ∀ p ∈ l, 0 ≤ p.1) :
    ∫ X, g X ∂tbt6Meas l = (l.map fun p => p.1 * g p.2).sum := by
  induction l with
  | nil => simp [tbt6_meas_nil]
  | cons p l ih =>
    rw [tbt6_meas_cons, integral_add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top) (tbt6_integrable_meas l),
      integral_smul_measure, integral_dirac, ih fun q hq => hl q (List.mem_cons_of_mem _ hq)]
    simp [ENNReal.toReal_ofReal (hl p List.mem_cons_self)]

/-- The atoms discarded along the chain of symmetric splittings `S → S ± E₁ → …`. -/
noncomputable def tbt6Disc : Matrix (Fin d) (Fin m) ℝ → ℝ → List (Matrix (Fin d) (Fin m) ℝ) →
    List (ℝ × Matrix (Fin d) (Fin m) ℝ)
  | _, _, [] => []
  | S, c, E :: Es => (c / 2, S - E) :: tbt6Disc (S + E) (c / 2) Es

/-- A symmetric split of the atom `c δ_S` along `±h R`. -/
theorem tbt6_split {μ ν : Measure (Matrix (Fin d) (Fin m) ℝ)} {S R : Matrix (Fin d) (Fin m) ℝ}
    {c h : ℝ} (hμ : IsPrelaminate μ) (hμe : μ = ENNReal.ofReal c • Measure.dirac S + ν)
    (hR : R.rank = 1) (hh : h ≠ 0) :
    IsPrelaminate (ENNReal.ofReal (c / 2) • Measure.dirac (S + h • R) +
      ENNReal.ofReal (c / 2) • Measure.dirac (S - h • R) + ν) := by
  have hR2 : ((2 * h) • R).rank = 1 := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero
      (mul_ne_zero two_ne_zero hh)), hR]
  have := IsPrelaminate.split (t := 1 / 2) hμ hμe hR2 (by norm_num) (by norm_num)
  have e1 : S + (1 - 1 / 2 : ℝ) • (2 * h) • R = S + h • R := by
    rw [smul_smul]; congr 1; congr 1; ring
  have e2 : S - (1 / 2 : ℝ) • (2 * h) • R = S - h • R := by
    rw [smul_smul]; congr 1; congr 1; ring
  have e3 : ENNReal.ofReal (1 / 2) • ENNReal.ofReal c = ENNReal.ofReal (c / 2) := by
    rw [smul_eq_mul, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  have e4 : ENNReal.ofReal (1 - 1 / 2) • ENNReal.ofReal c = ENNReal.ofReal (c / 2) := by
    rw [smul_eq_mul, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  rw [e1, e2, smul_smul, smul_smul] at this
  rw [← smul_eq_mul, e3, ← smul_eq_mul, e4] at this
  exact this

/-- The chain of symmetric splittings along `E₁, …, E_n` (rank one) reaches the atom
`c 2⁻ⁿ δ_{S + Σ E_i}`. -/
theorem tbt6_chain (Es : List (Matrix (Fin d) (Fin m) ℝ)) (hEs : ∀ E ∈ Es, E.rank = 1) :
    ∀ (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ) (ν : Measure (Matrix (Fin d) (Fin m) ℝ)), 0 ≤ c →
      IsPrelaminate (ENNReal.ofReal c • Measure.dirac S + ν) →
      IsPrelaminate (ENNReal.ofReal (c / 2 ^ Es.length) • Measure.dirac (S + Es.sum) +
        (tbt6Meas (tbt6Disc S c Es) + ν)) := by
  induction Es with
  | nil =>
    intro S c ν _ h
    simpa [tbt6Disc, tbt6_meas_nil] using h
  | cons E Es ih =>
    intro S c ν hc h
    have h1 := tbt6_split h rfl (hEs E List.mem_cons_self) one_ne_zero
    simp only [one_smul] at h1
    have h2 := ih (fun E' hE' => hEs E' (List.mem_cons_of_mem _ hE')) (S + E) (c / 2)
      (ENNReal.ofReal (c / 2) • Measure.dirac (S - E) + ν) (by positivity) (by
        rw [← add_assoc]; exact h1)
    have e1 : c / 2 ^ (E :: Es).length = c / 2 / 2 ^ Es.length := by
      rw [List.length_cons, pow_succ]; field_simp
    have e2 : S + (E :: Es).sum = S + E + Es.sum := by rw [List.sum_cons, add_assoc]
    have e3 : tbt6Meas (tbt6Disc S c (E :: Es)) + ν =
        tbt6Meas (tbt6Disc (S + E) (c / 2) Es) +
          (ENNReal.ofReal (c / 2) • Measure.dirac (S - E) + ν) := by
      simp only [tbt6Disc, tbt6_meas_cons]
      abel
    rw [e1, e2, e3]
    exact h2

/-- The weights of the chain sum to `c`. -/
theorem tbt6_disc_weights (Es : List (Matrix (Fin d) (Fin m) ℝ)) :
    ∀ (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ),
      ((tbt6Disc S c Es).map fun p => p.1).sum + c / 2 ^ Es.length = c := by
  induction Es with
  | nil => intro S c; simp [tbt6Disc]
  | cons E Es ih =>
    intro S c
    have := ih (S + E) (c / 2)
    simp only [tbt6Disc, List.map_cons, List.sum_cons, List.length_cons, pow_succ]
    linarith [show c / 2 / 2 ^ Es.length = c / (2 ^ Es.length * 2) by field_simp]

theorem tbt6_disc_nonneg (Es : List (Matrix (Fin d) (Fin m) ℝ)) :
    ∀ (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ), 0 ≤ c → ∀ p ∈ tbt6Disc S c Es, 0 ≤ p.1 := by
  induction Es with
  | nil => intro S c _ p hp; simp [tbt6Disc] at hp
  | cons E Es ih =>
    intro S c hc p hp
    simp only [tbt6Disc, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp only; positivity
    · exact ih (S + E) (c / 2) (by positivity) p hp

/-- The barycentre of the chain is `c S`. -/
theorem tbt6_disc_bary (Es : List (Matrix (Fin d) (Fin m) ℝ)) :
    ∀ (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ),
      ((tbt6Disc S c Es).map fun p => p.1 • p.2).sum + (c / 2 ^ Es.length) • (S + Es.sum) =
        c • S := by
  induction Es with
  | nil => intro S c; simp [tbt6Disc]
  | cons E Es ih =>
    intro S c
    have := ih (S + E) (c / 2)
    simp only [tbt6Disc, List.map_cons, List.sum_cons, List.length_cons]
    rw [show c / 2 ^ (Es.length + 1) = c / 2 / 2 ^ Es.length by rw [pow_succ]; field_simp,
      show S + (E + Es.sum) = S + E + Es.sum by abel, add_assoc, this]
    module

/-- Scaling the directions scales the atoms. -/
theorem tbt6_disc_smul (s : ℝ) (Es : List (Matrix (Fin d) (Fin m) ℝ)) :
    ∀ (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ),
      tbt6Disc (s • S) c (Es.map (s • ·)) = (tbt6Disc S c Es).map fun p => (p.1, s • p.2) := by
  induction Es with
  | nil => intro S c; simp [tbt6Disc]
  | cons E Es ih =>
    intro S c
    simp only [List.map_cons, tbt6Disc]
    rw [← smul_add, ih, smul_sub]

/-- **The envelope formula** (Proposition 2.1) gives Jensen's inequality at `0`: if `f` is
continuous and rank-one convex at `0`, then `f (0) ≤ ∫ f dμ` for every prelaminate `μ` with
barycentre `0`. -/
theorem tbt6_jensen {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hrc : RankOneConvexAt f 0) {μ : Measure (Matrix (Fin d) (Fin m) ℝ)} (hμ : IsPrelaminate μ)
    (hb : IsBarycentre μ 0) : f 0 ≤ ∫ X, f X ∂μ := by
  obtain ⟨g, hg, hgrc, hgle, hg0⟩ := hrc
  have hle : ((f 0 : ℝ) : EReal) ≤ rcEnvelope f 0 := by
    rw [← hg0]
    exact le_iSup₂ (f := fun (g : Matrix (Fin d) (Fin m) ℝ → ℝ)
      (_ : IsIntegrand g ∧ RankOneConvex g ∧ ∀ B, g B ≤ f B) => ((g 0 : ℝ) : EReal)) g
      ⟨hg, hgrc, hgle⟩
  rw [proposition2_1 hf 0] at hle
  have := hle.trans (iInf₂_le μ ⟨hμ, hb⟩)
  exact EReal.coe_le_coe_iff.mp this

/-- A cubic `a s + b s² + c s³` that is nonnegative for every `s ≠ 0` has `c = 0` and `b ≥ 0`. -/
theorem tbt6_cubic {a b c : ℝ} (h : ∀ s : ℝ, s ≠ 0 → 0 ≤ a * s + b * s ^ 2 + c * s ^ 3) :
    c = 0 ∧ 0 ≤ b := by
  have hc : c = 0 := by
    by_contra hc
    set M := 1 + (|a| + |b|) / |c| with hM
    have hcpos : 0 < |c| := abs_pos.mpr hc
    have hM1 : 1 ≤ M := by rw [hM]; have : 0 ≤ (|a| + |b|) / |c| := by positivity
                           linarith
    have hMc : |c| * M = |c| + (|a| + |b|) := by rw [hM]; field_simp
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · have := h M (by linarith)
      have hab : a * M + b * M ^ 2 ≤ (|a| + |b|) * M ^ 2 := by
        have h1 : a * M ≤ |a| * M := mul_le_mul_of_nonneg_right (le_abs_self a) (by linarith)
        have h2 : |a| * M ≤ |a| * M ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg a)
        have h3 : b * M ^ 2 ≤ |b| * M ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self b) (sq_nonneg M)
        linarith
      have hcM : c * M ^ 3 = -(|c| * M) * M ^ 2 := by rw [abs_of_neg hneg]; ring
      rw [hcM, hMc] at this
      nlinarith [sq_nonneg M, abs_nonneg a, abs_nonneg b]
    · have := h (-M) (by linarith)
      have hab : a * (-M) + b * (-M) ^ 2 ≤ (|a| + |b|) * M ^ 2 := by
        have h1 : a * (-M) ≤ |a| * M := by
          rw [mul_neg, ← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs a) (by linarith)
        have h2 : |a| * M ≤ |a| * M ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg a)
        have h3 : b * (-M) ^ 2 ≤ |b| * M ^ 2 := by
          rw [neg_sq]; exact mul_le_mul_of_nonneg_right (le_abs_self b) (sq_nonneg M)
        linarith
      have hcM : c * (-M) ^ 3 = -(|c| * M) * M ^ 2 := by rw [abs_of_pos hpos]; ring
      rw [hcM, hMc] at this
      nlinarith [sq_nonneg M, abs_nonneg a, abs_nonneg b]
  refine ⟨hc, ?_⟩
  by_contra hb
  push Not at hb
  set s := 1 + |a| / |b|
  have hbpos : 0 < |b| := abs_pos.mpr hb.ne
  have hs1 : 1 ≤ s := by have : 0 ≤ |a| / |b| := by positivity
                         linarith
  have hsb : |b| * s = |b| + |a| := by simp only [s]; field_simp
  have := h s (by linarith)
  rw [hc] at this
  have : a * s + b * s ^ 2 = s * (a + b * s) := by ring
  have h2 : a + b * s < 0 := by
    have : b * s = -(|b| * s) := by rw [abs_of_neg hb]; ring
    rw [this, hsb]; linarith [le_abs_self a]
  nlinarith

theorem tbt6_list_sum_apply (l : List (Matrix (Fin d) (Fin m) ℝ)) (i : Fin d) (j : Fin m) :
    l.sum i j = (l.map fun X => X i j).sum := by
  induction l with
  | nil => simp
  | cons X l ih => simp [ih]

theorem tbt6_bary_smul (L : List (ℝ × Matrix (Fin d) (Fin m) ℝ)) (s : ℝ) (i : Fin d)
    (j : Fin m) :
    (L.map fun p => p.1 * (s • p.2) i j).sum = s * (L.map fun p => p.1 • p.2).sum i j := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, Matrix.add_apply,
      Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

/-- The cubic structure of `∫ f dμ_s` along the scaled laminates. -/
theorem tbt6_list_expand (L : List (ℝ × Matrix (Fin d) (Fin m) ℝ)) (a s : ℝ)
    (b c e : Matrix (Fin d) (Fin m) ℝ → ℝ) :
    (L.map fun p => p.1 * (a + s * b p.2 + s ^ 2 * c p.2 + s ^ 3 * e p.2)).sum =
      a * (L.map fun p => p.1).sum + s * (L.map fun p => p.1 * b p.2).sum +
        s ^ 2 * (L.map fun p => p.1 * c p.2).sum + s ^ 3 * (L.map fun p => p.1 * e p.2).sum := by
  induction L with
  | nil => simp
  | cons p L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **Proposition 5.1, the limiting argument** ("`Q` is rank-one convex at `0` by the envelope
formula and a limiting argument", made quantitative): let `f = f₀ + f₁ + f₂ + f₃` with `f_k`
homogeneous of degree `k`, continuous and rank-one convex at `0`. For a laminate `L` centred at `0`
all of whose dilations are prelaminates, `∫ f₃ dL = 0` and `∫ f₂ dL ≥ 0`: Jensen's inequality for
the dilations by `s` reads `0 ≤ s ∫ f₁ + s² ∫ f₂ + s³ ∫ f₃` for every `s ≠ 0`. -/
theorem tbt6_list_cubic {f f₀ f₁ f₂ f₃ : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hrc : RankOneConvexAt f 0) (hsum : ∀ X, f X = f₀ X + f₁ X + f₂ X + f₃ X)
    (h0 : ∀ (s : ℝ) X, f₀ (s • X) = f₀ X) (h1 : ∀ (s : ℝ) X, f₁ (s • X) = s * f₁ X)
    (h2 : ∀ (s : ℝ) X, f₂ (s • X) = s ^ 2 * f₂ X) (h3 : ∀ (s : ℝ) X, f₃ (s • X) = s ^ 3 * f₃ X)
    (L : List (ℝ × Matrix (Fin d) (Fin m) ℝ)) (hw : ∀ p ∈ L, 0 ≤ p.1)
    (hw1 : (L.map fun p => p.1).sum = 1) (hbary : (L.map fun p => p.1 • p.2).sum = 0)
    (hpre : ∀ s : ℝ, s ≠ 0 → IsPrelaminate (tbt6Meas (L.map fun p => (p.1, s • p.2)))) :
    (L.map fun p => p.1 * f₃ p.2).sum = 0 ∧ 0 ≤ (L.map fun p => p.1 * f₂ p.2).sum := by
  have hz : ∀ (g : Matrix (Fin d) (Fin m) ℝ → ℝ) (k : ℕ), 0 < k →
      (∀ (s : ℝ) X, g (s • X) = s ^ k * g X) → g 0 = 0 := by
    intro g k hk hg
    have := hg 0 0
    rw [smul_zero, zero_pow hk.ne', zero_mul] at this
    exact this
  have hf0 : f 0 = f₀ 0 := by
    rw [hsum, hz f₁ 1 one_pos (fun s X => by rw [h1, pow_one]), hz f₂ 2 two_pos h2,
      hz f₃ 3 (by norm_num) h3]
    ring
  refine tbt6_cubic (a := (L.map fun p => p.1 * f₁ p.2).sum) fun s hs => ?_
  have hLw : ∀ p ∈ L.map (fun p => (p.1, s • p.2)), 0 ≤ p.1 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hw q hq
  have hb : IsBarycentre (tbt6Meas (L.map fun p => (p.1, s • p.2))) 0 := by
    intro i j
    rw [tbt6_integral_meas (g := fun X => X i j) _ hLw, List.map_map]
    have := tbt6_bary_smul L s i j
    simp only [Function.comp_def] at this ⊢
    rw [this, hbary, Matrix.zero_apply, mul_zero]
  have hJ := tbt6_jensen hf hrc (hpre s hs) hb
  rw [tbt6_integral_meas (g := f) _ hLw, List.map_map] at hJ
  have he : ∀ p : ℝ × Matrix (Fin d) (Fin m) ℝ, ((fun p : ℝ × Matrix (Fin d) (Fin m) ℝ =>
      p.1 * f p.2) ∘ fun p => (p.1, s • p.2)) p =
      p.1 * (f₀ 0 + s * f₁ p.2 + s ^ 2 * f₂ p.2 + s ^ 3 * f₃ p.2) := by
    intro p
    simp only [Function.comp, hsum, h1, h2, h3]
    rw [h0, ← h0 0 p.2, zero_smul]
  rw [List.map_congr_left fun p _ => he p, tbt6_list_expand, hw1, hf0] at hJ
  linarith

/-- `A = Σ_{a_{ij} ≠ 0} a_{ij} e_{ij}`, a sum of rank-one matrices. -/
noncomputable def tbt6Es (A : Matrix (Fin d) (Fin m) ℝ) : List (Matrix (Fin d) (Fin m) ℝ) :=
  (Finset.univ.filter fun ij : Fin d × Fin m => A ij.1 ij.2 ≠ 0).toList.map
    fun ij => Matrix.single ij.1 ij.2 (A ij.1 ij.2)

theorem tbt6_Es_sum (A : Matrix (Fin d) (Fin m) ℝ) : (tbt6Es A).sum = A := by
  rw [tbt6Es, Finset.sum_map_toList, Finset.sum_filter_of_ne (p := fun ij : Fin d × Fin m =>
    A ij.1 ij.2 ≠ 0) (fun ij _ h => by intro h0; apply h; rw [h0, Matrix.single_zero])]
  conv_rhs => rw [Matrix.matrix_eq_sum_single A]
  rw [Fintype.sum_prod_type]

theorem tbt6_Es_rank (A : Matrix (Fin d) (Fin m) ℝ) : ∀ E ∈ tbt6Es A, E.rank = 1 := by
  intro E hE
  simp only [tbt6Es, List.mem_map, Finset.mem_toList, Finset.mem_filter] at hE
  obtain ⟨ij, ⟨-, hij⟩, rfl⟩ := hE
  exact rank_single_eq_one hij

theorem tbt6_dirac_eq (S : Matrix (Fin d) (Fin m) ℝ) :
    Measure.dirac S = ENNReal.ofReal 1 • Measure.dirac S + 0 := by simp

/-- **Legendre–Hadamard** for the quadratic part: `f₂ (R) ≥ 0` for rank-one `R` (the laminate
`½ δ_R + ½ δ_{−R}`). -/
theorem tbt6_LH {f f₀ f₁ f₂ f₃ : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hrc : RankOneConvexAt f 0) (hsum : ∀ X, f X = f₀ X + f₁ X + f₂ X + f₃ X)
    (h0 : ∀ (s : ℝ) X, f₀ (s • X) = f₀ X) (h1 : ∀ (s : ℝ) X, f₁ (s • X) = s * f₁ X)
    (h2 : ∀ (s : ℝ) X, f₂ (s • X) = s ^ 2 * f₂ X) (h3 : ∀ (s : ℝ) X, f₃ (s • X) = s ^ 3 * f₃ X)
    {R : Matrix (Fin d) (Fin m) ℝ} (hR : R.rank = 1) : 0 ≤ f₂ R := by
  have := (tbt6_list_cubic hf hrc hsum h0 h1 h2 h3 [(1 / 2, R), (1 / 2, -R)]
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num) (by norm_num)
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, smul_neg]; abel)
    (fun s hs => by
      have := tbt6_split (c := 1) (S := 0) (h := s)
        (IsPrelaminate.dirac (0 : Matrix (Fin d) (Fin m) ℝ)) (tbt6_dirac_eq 0) hR hs
      simp only [zero_add, zero_sub] at this
      simp only [List.map_cons, List.map_nil, tbt6_meas_cons, tbt6_meas_nil, smul_neg]
      rw [← add_assoc]; norm_num at this ⊢; exact this)).2
  have hneg : f₂ (-R) = f₂ R := by rw [← neg_one_smul ℝ R, h2]; ring
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hneg] at this
  linarith

/-- **`Q` is rank-one affine** (inventory E9, repaired): for every `A`, rank-one `R` and `h`,
`f₃ (A + h R) + f₃ (A − h R) = 2 f₃ (A)`. The chain of symmetric splittings along the rank-one
pieces `E_i` of `A = Σ E_i` is a prelaminate centred at `0` with an atom `2⁻ⁿ δ_A`; splitting that
atom along `±h R` gives a second one; both have `∫ f₃ = 0` (`tbt6_list_cubic`), and the difference
is `2⁻ⁿ⁻¹ (f₃ (A + h R) + f₃ (A − h R) − 2 f₃ (A))`. -/
theorem tbt6_sym {f f₀ f₁ f₂ f₃ : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : Continuous f)
    (hrc : RankOneConvexAt f 0) (hsum : ∀ X, f X = f₀ X + f₁ X + f₂ X + f₃ X)
    (h0 : ∀ (s : ℝ) X, f₀ (s • X) = f₀ X) (h1 : ∀ (s : ℝ) X, f₁ (s • X) = s * f₁ X)
    (h2 : ∀ (s : ℝ) X, f₂ (s • X) = s ^ 2 * f₂ X) (h3 : ∀ (s : ℝ) X, f₃ (s • X) = s ^ 3 * f₃ X)
    (A : Matrix (Fin d) (Fin m) ℝ) {R : Matrix (Fin d) (Fin m) ℝ} (hR : R.rank = 1) (h : ℝ) :
    f₃ (A + h • R) + f₃ (A - h • R) = 2 * f₃ A := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp; ring
  set Es := tbt6Es A
  set n := Es.length
  set D := tbt6Disc (0 : Matrix (Fin d) (Fin m) ℝ) 1 Es
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 / 2 ^ n := ⟨_, rfl⟩
  have hEs := tbt6_Es_rank A
  have hsumA : Es.sum = A := tbt6_Es_sum A
  have hDw := tbt6_disc_nonneg Es 0 1 zero_le_one
  have hD1 : (D.map fun p => p.1).sum + w = 1 := by rw [hw]; exact tbt6_disc_weights Es 0 1
  have hDb : (D.map fun p => p.1 • p.2).sum + w • A = 0 := by
    have := tbt6_disc_bary Es 0 1
    rwa [zero_add, hsumA, smul_zero, ← hw] at this
  have hpos : 0 < w := by rw [hw]; positivity
  -- the scaled chain
  have hchain : ∀ s : ℝ, s ≠ 0 → IsPrelaminate (ENNReal.ofReal w • Measure.dirac (s • A) +
      (tbt6Meas (D.map fun p => (p.1, s • p.2)) + 0)) := by
    intro s hs
    have hr : ∀ E ∈ Es.map (s • ·), E.rank = 1 := by
      intro E hE
      obtain ⟨E', hE', rfl⟩ := List.mem_map.mp hE
      rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hs),
        hEs E' hE']
    have := tbt6_chain (Es.map (s • ·)) hr 0 1 0 zero_le_one (by
      rw [← tbt6_dirac_eq]; exact IsPrelaminate.dirac 0)
    rw [List.length_map, zero_add, ← List.smul_sum, hsumA] at this
    have hd := tbt6_disc_smul s Es 0 1
    rw [smul_zero] at hd
    rw [hd, ← hw] at this
    exact this
  have L1 := tbt6_list_cubic hf hrc hsum h0 h1 h2 h3 (D ++ [(w, A)])
    (by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hDw p hp
      · rw [List.mem_singleton] at hp; rw [hp]; exact hpos.le)
    (by
      rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      exact hD1)
    (by
      rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      exact hDb)
    (fun s hs => by
      have := hchain s hs
      rw [List.map_append, tbt6_meas_append, List.map_singleton, tbt6_meas_cons, tbt6_meas_nil,
        add_zero]
      rw [add_zero] at this
      rwa [add_comm])
  have L2 := tbt6_list_cubic hf hrc hsum h0 h1 h2 h3
    (D ++ [(w / 2, A + h • R), (w / 2, A - h • R)])
    (by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hDw p hp
      · rw [List.mem_cons, List.mem_singleton] at hp
        rcases hp with hp | hp <;> rw [hp] <;> positivity)
    (by
      rw [List.map_append, List.sum_append, List.map_cons, List.map_singleton, List.sum_cons,
        List.sum_singleton]
      linarith)
    (by
      rw [List.map_append, List.sum_append, List.map_cons, List.map_singleton, List.sum_cons,
        List.sum_singleton, ← hDb]
      congr 1; module)
    (fun s hs => by
      have := tbt6_split (h := s * h) (hchain s hs) rfl hR (mul_ne_zero hs hh)
      rw [List.map_append, tbt6_meas_append, List.map_cons, List.map_singleton, tbt6_meas_cons,
        tbt6_meas_cons, tbt6_meas_nil, add_zero]
      rw [add_zero] at this
      rw [smul_add, smul_sub, smul_smul]
      convert this using 1
      abel)
  have e1 := L1.1
  have e2 := L2.1
  rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton] at e1
  rw [List.map_append, List.sum_append, List.map_cons, List.map_singleton, List.sum_cons,
    List.sum_singleton] at e2
  simp only at e1 e2
  have : w / 2 * (f₃ (A + h • R) + f₃ (A - h • R)) = w * f₃ A := by linarith
  have hw0 : w ≠ 0 := hpos.ne'
  field_simp at this
  linarith

end Cassese
