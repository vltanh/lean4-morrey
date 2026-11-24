module

public import Morrey.HomogeneousIsotropic.Coordinates
public import Morrey.HomogeneousIsotropic.Polyaffine
public import Morrey.HomogeneousIsotropic.Supports
public import CalculusOfVariations.Quasiconvex.RankOneConvex
public import CalculusOfVariations.RankOneConvex.LocallyLipschitz
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rank-one convex, isotropic, positively homogeneous integrands on `ℝ^{2×2}`

Let `F : ℝ^{2×2} → ℝ` be isotropic, positively `p`-homogeneous and rank-one convex. The numbers
are those of the paper, `docs/HomogeneousIsotropic/paper/main.tex`.

* `polyconvex_of_rankOneConvex` (**Theorem 1.1**): if `p ≥ 2` and `F ≥ 0`, then `F` is polyconvex;
  `hasPolyaffineSupportAt_of_rankOneConvex` gives a polyaffine support at every matrix, and
  `quasiconvex_of_rankOneConvex` the quasiconvexity.
* `polyaffine_multiplier_le`: the support at `diag (1, t)`, `|t| < 1`, in closed form: its
  determinant coefficient is `multiplier p H m t`, the value `(p − 1) m` clamped to `[L, U]`,
  where `H = F (diag (1, t))` and `m` is the slope of a supporting line of
  `s ↦ F (diag (1, s))` at `t`.
* `tfae_of_two_le` (**Corollary 1.4**): for `p ≥ 2` and `F ≥ 0` isotropic, positively
  `p`-homogeneous, Borel and locally bounded, rank-one convexity, quasiconvexity and
  polyconvexity are equivalent.
* `nonneg_of_polyconvex`, `polyconvex_iff_of_two_lt`: for `p > 2` a polyconvex, positively
  `p`-homogeneous function is nonnegative, so that an isotropic, positively `p`-homogeneous
  function is polyconvex if and only if it is rank-one convex and nonnegative.
* `polyconvex_of_rankOneConvex_two`, `polyconvex_iff_two`: for `p = 2` no sign condition is
  needed.
* `exists_burkholderTypeCoord_le`: if `1 ≤ p < 2` and `F ≥ 0`, then at every matrix `F` has a
  touching minorant `(|z| + |w|)^{p−1} (c₀ (|z| + |w|) + m (|z| − |w|))` with
  `(2 − p) |m| ≤ p c₀`, a nonnegative combination of `burkholderCoord p` and its mirror image
  (`burkholderTypeCoord_eq`). This is **Theorem 1.5** in conformal coordinates;
  `Morrey/HomogeneousIsotropic/Burkholder.lean` states it with the operator norm and the
  Burkholder function of the paper.
* `quasiconvex_of_rankOneConvex_of_burkholderCoord`: hence, for `1 ≤ p < 2`, `F` is quasiconvex
  if `burkholderCoord p` is quasiconvex.
* `convexOn_of_rankOneConvex_one`, `quasiconvex_of_rankOneConvex_one` (**Corollary 1.6 (b)**):
  for `p = 1`, `burkholderCoord 1` is `|z|`, which is convex, and no sign condition is needed:
  `F` is nonnegative and convex.
* `eq_zero_of_rankOneConvex_of_lt_one` (**Proposition 1.7**): for `0 < p < 1` a positively
  `p`-homogeneous, rank-one convex `F` is `0`; isotropy and the sign condition are not needed.
* `quasiconvex_of_rankOneConvex_of_pos_of_burkholderCoord`: for every `p > 0`, a nonnegative `F`
  of the class is quasiconvex if `burkholderCoord p` is quasiconvex when `1 < p < 2`.
  **Corollary 1.6 (a)** and the nonnegative case of **Theorem A**, without that hypothesis, are in
  `Morrey/HomogeneousIsotropic/Signed/BurkholderRadial.lean`.
-/

@[expose] public section

open CalculusOfVariations

namespace HomogeneousIsotropic

variable {p : ℝ} {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}

/-! ### The exponents `p ≥ 2` -/

/-- A nonnegative, isotropic, positively `p`-homogeneous, rank-one convex integrand on
`ℝ^{2×2}`, `p ≥ 2`, has a polyaffine support at every matrix. -/
theorem hasPolyaffineSupportAt_of_rankOneConvex (hp : 2 ≤ p) (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F)
    (A₀ : Matrix (Fin 2) (Fin 2) ℝ) : HasPolyaffineSupportAt F A₀ := by
  have hΦ := isProfile_profile hiso hhom hrc
  obtain ⟨k, b, g, c, hb, hg, hle, heq⟩ := hΦ.exists_support (fun x y _ _ => h0 _) hp
    (norm_nonneg (conformalPart A₀)) (norm_nonneg (anticonformalPart A₀))
  exact hasPolyaffineSupportAt_of_profile hiso A₀ hb hg hle heq

/-- **Theorem 1.1.** A nonnegative, isotropic, positively `p`-homogeneous, rank-one convex
integrand on `ℝ^{2×2}` with `p ≥ 2` is polyconvex. -/
theorem polyconvex_of_rankOneConvex (hp : 2 ≤ p) (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F) : Polyconvex F :=
  polyconvex_of_hasPolyaffineSupportAt fun A =>
    hasPolyaffineSupportAt_of_rankOneConvex hp h0 hiso hhom hrc A

/-- A nonnegative, isotropic, positively `p`-homogeneous, rank-one convex integrand on
`ℝ^{2×2}` with `p ≥ 2` is quasiconvex. -/
theorem quasiconvex_of_rankOneConvex (hp : 2 ≤ p) (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F) : Quasiconvex F :=
  quasiconvex_of_hasPolyaffineSupportAt fun A =>
    hasPolyaffineSupportAt_of_rankOneConvex hp h0 hiso hhom hrc A

/-- **Corollary 1.4.** For a nonnegative, isotropic, positively `p`-homogeneous integrand on
`ℝ^{2×2}` with `p ≥ 2` (Borel and locally bounded), rank-one convexity, quasiconvexity and
polyconvexity are equivalent. -/
theorem tfae_of_two_le (hp : 2 ≤ p) (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous p F) (hm : Measurable F) (hb : IsLocallyBounded F) :
    List.TFAE [RankOneConvex F, Quasiconvex F, Polyconvex F] := by
  tfae_have 1 → 3 := fun h => polyconvex_of_rankOneConvex hp h0 hiso hhom h
  tfae_have 3 → 2 := fun h => h.quasiconvex
  tfae_have 2 → 1 := fun h => rankOneConvex_of_quasiconvex hm hb h
  tfae_finish

/-- **Nonnegativity is necessary for `p > 2`.** A polyconvex, positively `p`-homogeneous
function with `p > 2` is nonnegative: its polyaffine supports at `0` vanish identically. -/
theorem nonneg_of_polyconvex (hp : 2 < p) (hhom : IsPosHomogeneous p F) (hpc : Polyconvex F)
    (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ F A := by
  have hF0 : F 0 = 0 := by
    have h := hhom 2 two_pos 0
    rw [smul_zero] at h
    have h2 : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow one_lt_two (by linarith)
    nlinarith
  obtain ⟨k, K, c, hle, heq⟩ := hpc.hasPolyaffineSupportAt 0
  have hk : k = 0 := by simpa [polyaffine, hF0] using heq
  subst hk
  have hscale : ∀ (B : Matrix (Fin 2) (Fin 2) ℝ) (l : ℝ), 0 < l →
      l * (∑ i, ∑ j, K i j * B i j) + l ^ 2 * (c * B.det) ≤ l ^ p * F B := by
    intro B l hl
    have h := hle (l • B)
    rw [hhom l hl B] at h
    have e : polyaffine 0 K c (l • B) =
        l * (∑ i, ∑ j, K i j * B i j) + l ^ 2 * (c * B.det) := by
      simp [polyaffine, Matrix.det_fin_two, Fin.sum_univ_two]
      ring
    rwa [e] at h
  -- the linear part is nonpositive, hence zero
  have hL0 : ∀ B : Matrix (Fin 2) (Fin 2) ℝ, ∑ i, ∑ j, K i j * B i j ≤ 0 := by
    intro B
    by_contra hcon
    have hs : 0 < ∑ i, ∑ j, K i j * B i j := not_le.1 hcon
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ∑ i, ∑ j, K i j * B i j := ⟨_, rfl⟩
    rw [← hsdef] at hs
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |F B| + |c * B.det| + 1 := ⟨_, rfl⟩
    have hMpos : 0 < M := by rw [hM]; positivity
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = min 1 (s / (2 * M)) := ⟨_, rfl⟩
    have hlpos : 0 < l := by rw [hl]; exact lt_min one_pos (by positivity)
    have hl1 : l ≤ 1 := by rw [hl]; exact min_le_left _ _
    have hl2 : l ≤ s / (2 * M) := by rw [hl]; exact min_le_right _ _
    have h := hscale B l hlpos
    rw [← hsdef] at h
    have hpow : l ^ p ≤ l ^ 2 := by
      have h' := Real.rpow_le_rpow_of_exponent_ge hlpos hl1 hp.le
      rwa [Real.rpow_two] at h'
    have h1 : l ^ p * F B ≤ l ^ 2 * |F B| :=
      (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.rpow_nonneg hlpos.le _)).trans
        (mul_le_mul_of_nonneg_right hpow (abs_nonneg _))
    have h2 : -(l ^ 2 * (c * B.det)) ≤ l ^ 2 * |c * B.det| := by
      have := mul_le_mul_of_nonneg_left (neg_le_abs (c * B.det)) (sq_nonneg l)
      linarith
    have h3 : l * s ≤ l * (l * M) := by
      rw [hM]
      nlinarith
    have h4 : s ≤ l * M := le_of_mul_le_mul_left h3 hlpos
    have h5 : l * M ≤ s / 2 := by
      calc l * M ≤ s / (2 * M) * M := mul_le_mul_of_nonneg_right hl2 hMpos.le
        _ = s / 2 := by field_simp
    linarith
  have hLz : ∀ B : Matrix (Fin 2) (Fin 2) ℝ, ∑ i, ∑ j, K i j * B i j = 0 := by
    intro B
    refine le_antisymm (hL0 B) ?_
    have h := hL0 (-B)
    simp only [Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib] at h
    linarith
  -- the determinant part is nonpositive, hence zero
  have hcd : ∀ B : Matrix (Fin 2) (Fin 2) ℝ, c * B.det ≤ 0 := by
    intro B
    by_contra hcon
    have he : 0 < c * B.det := not_le.1 hcon
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = min 1 (c * B.det / (2 * (|F B| + 1))) := ⟨_, rfl⟩
    have hxpos : 0 < x := by rw [hx]; exact lt_min one_pos (by positivity)
    have hx2 : x ≤ c * B.det / (2 * (|F B| + 1)) := by rw [hx]; exact min_le_right _ _
    have hlpos : 0 < x ^ (1 / (p - 2)) := Real.rpow_pos_of_pos hxpos _
    have hlp : (x ^ (1 / (p - 2))) ^ (p - 2) = x := by
      rw [← Real.rpow_mul hxpos.le, one_div, inv_mul_cancel₀ (by linarith : p - 2 ≠ 0),
        Real.rpow_one]
    have h := hscale B (x ^ (1 / (p - 2))) hlpos
    rw [hLz, mul_zero, zero_add] at h
    have hpw : (x ^ (1 / (p - 2))) ^ p =
        (x ^ (1 / (p - 2))) ^ 2 * (x ^ (1 / (p - 2))) ^ (p - 2) := by
      rw [← Real.rpow_two, ← Real.rpow_add hlpos]
      congr 1
      ring
    rw [hpw, hlp, mul_assoc] at h
    have h2 : c * B.det ≤ x * F B := le_of_mul_le_mul_left h (by positivity)
    have h3 : x * F B ≤ x * |F B| := mul_le_mul_of_nonneg_left (le_abs_self _) hxpos.le
    have h4 : x * (|F B| + 1) ≤ c * B.det / 2 := by
      calc x * (|F B| + 1) ≤ c * B.det / (2 * (|F B| + 1)) * (|F B| + 1) :=
            mul_le_mul_of_nonneg_right hx2 (by positivity)
        _ = c * B.det / 2 := by field_simp
    nlinarith [abs_nonneg (F B)]
  have hc0 : c = 0 := by
    have h1 := hcd 1
    have h2 := hcd reflection
    simp [reflection, Matrix.det_fin_two] at h1 h2
    linarith
  have h := hle A
  have e : polyaffine 0 K c A = ∑ i, ∑ j, K i j * A i j + c * A.det := by simp [polyaffine]
  rw [e, hLz, hc0] at h
  linarith

/-- For `p > 2`, an isotropic, positively `p`-homogeneous function on `ℝ^{2×2}` is polyconvex if
and only if it is rank-one convex and nonnegative. -/
theorem polyconvex_iff_of_two_lt (hp : 2 < p) (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous p F) : Polyconvex F ↔ RankOneConvex F ∧ ∀ A, 0 ≤ F A :=
  ⟨fun h => ⟨h.rankOneConvex, nonneg_of_polyconvex hp hhom h⟩,
    fun h => polyconvex_of_rankOneConvex hp.le h.2 hiso hhom h.1⟩

/-- The matrix `diag (1, s)` is `ofComplex ((1 + s)/2) ((1 − s)/2)`. -/
theorem profile_half_add_half_sub (F : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (s : ℝ) :
    profile F ((1 + s) / 2) ((1 - s) / 2) = F !![1, 0; 0, s] := by
  rw [profile, ofComplex_ofReal]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **Theorem 1.2, the support in closed form.** Let `F ≥ 0` be isotropic, positively
`p`-homogeneous and rank-one convex, `p ≥ 2`. Let `|t| < 1`, `H = F (diag (1, t)) > 0`, and let
`m` be the slope of a supporting line at `t` of `s ↦ F (diag (1, s))` on `[−1, 1]`. With
`c = multiplier p H m t`, the polyaffine function
`A ↦ c t − (p − 1) H + (p H − t m − c t) a₁₁ + (m − c) a₂₂ + c det A` lies below `F` and equals
`F` at `diag (1, t)`. -/
theorem polyaffine_multiplier_le (hp : 2 ≤ p) (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F) {t m H : ℝ} (ht : |t| < 1)
    (hH : F !![1, 0; 0, t] = H) (hHpos : 0 < H)
    (hm : ∀ s : ℝ, -1 ≤ s → s ≤ 1 → H + m * (s - t) ≤ F !![1, 0; 0, s]) :
    (∀ A, polyaffine (multiplier p H m t * t - (p - 1) * H)
        !![p * H - t * m - multiplier p H m t * t, 0; 0, m - multiplier p H m t]
        (multiplier p H m t) A ≤ F A) ∧
      polyaffine (multiplier p H m t * t - (p - 1) * H)
        !![p * H - t * m - multiplier p H m t * t, 0; 0, m - multiplier p H m t]
        (multiplier p H m t) !![1, 0; 0, t] = H := by
  have hΦ := isProfile_profile hiso hhom hrc
  have hmin : BurkholderMinorant p (H - m * t) m (profile F) := by
    refine hΦ.burkholderMinorant_of_slice (by linarith) fun s hs1 hs2 => ?_
    rw [profile_half_add_half_sub]
    have h := hm s hs1 hs2
    linarith
  have heq : profile F ((1 + t) / 2) ((1 - t) / 2) = H := by
    rw [profile_half_add_half_sub, hH]
  obtain ⟨hb, hg, hle⟩ := hΦ.support_multiplier (fun x y _ _ => h0 _) hp ht hmin heq hHpos
  constructor
  · intro A
    have h := hle ‖conformalPart A‖ ‖anticonformalPart A‖ (norm_nonneg _) (norm_nonneg _)
    rw [← hiso.eq_profile A, ← det_eq_norm_sq_sub] at h
    have hz : (conformalPart A).re ≤ ‖conformalPart A‖ := Complex.re_le_norm _
    have hw : (anticonformalPart A).re ≤ ‖anticonformalPart A‖ := Complex.re_le_norm _
    have hzre : (conformalPart A).re = (A 0 0 + A 1 1) / 2 := rfl
    have hwre : (anticonformalPart A).re = (A 0 0 - A 1 1) / 2 := rfl
    have h1 := mul_le_mul_of_nonneg_left hz hb
    have h2 := mul_le_mul_of_nonneg_left hw hg
    rw [hzre] at h1
    rw [hwre] at h2
    have e : polyaffine (multiplier p H m t * t - (p - 1) * H)
        !![p * H - t * m - multiplier p H m t * t, 0; 0, m - multiplier p H m t]
        (multiplier p H m t) A =
        multiplier p H m t * t - (p - 1) * H +
          (p * H + (1 - t) * m - (1 + t) * multiplier p H m t) * ((A 0 0 + A 1 1) / 2) +
          (p * H - (1 + t) * m + (1 - t) * multiplier p H m t) * ((A 0 0 - A 1 1) / 2) +
          multiplier p H m t * A.det := by
      simp [polyaffine, Fin.sum_univ_two]
      ring
    rw [e]
    linarith
  · simp [polyaffine, Fin.sum_univ_two, Matrix.det_fin_two]
    ring

/-! ### The exponent `p = 2`, with no sign condition -/

/-- An isotropic, positively `2`-homogeneous, rank-one convex integrand on `ℝ^{2×2}`, of any
sign, has a polyaffine support at every matrix. -/
theorem hasPolyaffineSupportAt_of_rankOneConvex_two (hiso : IsIsotropic F)
    (hhom : IsPosHomogeneous 2 F) (hrc : RankOneConvex F) (A₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    HasPolyaffineSupportAt F A₀ := by
  have hΦ := isProfile_profile hiso hhom hrc
  obtain ⟨k, b, g, c, hb, hg, hle, heq⟩ := hΦ.exists_support_two
    (norm_nonneg (conformalPart A₀)) (norm_nonneg (anticonformalPart A₀))
  exact hasPolyaffineSupportAt_of_profile hiso A₀ hb hg hle heq

/-- An isotropic, positively `2`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is
polyconvex; no sign condition is needed. -/
theorem polyconvex_of_rankOneConvex_two (hiso : IsIsotropic F) (hhom : IsPosHomogeneous 2 F)
    (hrc : RankOneConvex F) : Polyconvex F :=
  polyconvex_of_hasPolyaffineSupportAt fun A =>
    hasPolyaffineSupportAt_of_rankOneConvex_two hiso hhom hrc A

/-- An isotropic, positively `2`-homogeneous function on `ℝ^{2×2}` is polyconvex if and only if
it is rank-one convex. -/
theorem polyconvex_iff_two (hiso : IsIsotropic F) (hhom : IsPosHomogeneous 2 F) :
    Polyconvex F ↔ RankOneConvex F :=
  ⟨fun h => h.rankOneConvex, fun h => polyconvex_of_rankOneConvex_two hiso hhom h⟩

/-! ### The exponents `1 ≤ p < 2` -/

/-- **Theorem 1.5, in conformal coordinates.** Let `F ≥ 0` be isotropic, positively
`p`-homogeneous and rank-one convex on `ℝ^{2×2}`, `1 ≤ p < 2`. At every matrix `A₀` there are
`c₀`, `m` with `(2 − p) |m| ≤ p c₀` such that the Burkholder-type function
`burkholderTypeCoord p c₀ m` lies below `F` and equals `F` at `A₀`. -/
theorem exists_burkholderTypeCoord_le (hp1 : 1 ≤ p) (hp2 : p < 2) (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F)
    (A₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ c₀ m : ℝ, (2 - p) * |m| ≤ p * c₀ ∧ (∀ A, burkholderTypeCoord p c₀ m A ≤ F A) ∧
      burkholderTypeCoord p c₀ m A₀ = F A₀ := by
  have hΦ := isProfile_profile hiso hhom hrc
  have hp0 : 0 < p := by linarith
  rcases (add_nonneg (norm_nonneg (conformalPart A₀))
    (norm_nonneg (anticonformalPart A₀))).eq_or_lt with h00 | hpos
  · refine ⟨0, 0, by simp, fun A => by simpa [burkholderTypeCoord] using h0 A, ?_⟩
    have hz : ‖conformalPart A₀‖ = 0 := by
      linarith [norm_nonneg (conformalPart A₀), norm_nonneg (anticonformalPart A₀)]
    have hw : ‖anticonformalPart A₀‖ = 0 := by
      linarith [norm_nonneg (conformalPart A₀), norm_nonneg (anticonformalPart A₀)]
    rw [hiso.eq_profile A₀, hz, hw, hΦ.zero_zero hp0]
    simp [burkholderTypeCoord]
  · obtain ⟨c₀, m, hc, hmin, heq⟩ := hΦ.exists_burkholderMinorant_of_lt_two
      (fun x y _ _ => h0 _) hp1 hp2
      (div_nonneg (norm_nonneg (conformalPart A₀)) hpos.le)
      (div_nonneg (norm_nonneg (anticonformalPart A₀)) hpos.le)
      (by rw [← add_div, div_self hpos.ne'])
    refine ⟨c₀, m, hc, fun A => ?_, ?_⟩
    · rw [hiso.eq_profile A]
      exact hmin _ _ (norm_nonneg _) (norm_nonneg _)
    · rw [hiso.eq_profile A₀, hΦ.eq_rpow_mul (norm_nonneg _) (norm_nonneg _) hpos, ← heq,
        burkholderTypeCoord]
      have hpow : (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) ^ p =
          (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) ^ (p - 1) *
            (‖conformalPart A₀‖ + ‖anticonformalPart A₀‖) := by
        rw [← Real.rpow_add_one hpos.ne']
        congr 1
        ring
      rw [hpow]
      field_simp

/-- The modulus of the conformal part is a continuous function of the matrix. -/
theorem continuous_norm_conformalPart :
    Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => ‖conformalPart A‖ := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℝ => ‖conformalPart A‖) =
      fun A => √(((A 0 0 + A 1 1) / 2) * ((A 0 0 + A 1 1) / 2) +
        ((A 1 0 - A 0 1) / 2) * ((A 1 0 - A 0 1) / 2)) := by
    funext A
    rw [Complex.norm_def, Complex.normSq_apply]
    rfl
  rw [h]
  have e : ∀ i j : Fin 2, Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j :=
    fun i j => continuous_id.matrix_elem i j
  exact Real.continuous_sqrt.comp ((((e 0 0).add (e 1 1)).div_const 2).mul
    (((e 0 0).add (e 1 1)).div_const 2) |>.add
    ((((e 1 0).sub (e 0 1)).div_const 2).mul (((e 1 0).sub (e 0 1)).div_const 2)))

/-- The modulus of the anticonformal part is a continuous function of the matrix. -/
theorem continuous_norm_anticonformalPart :
    Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => ‖anticonformalPart A‖ := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℝ => ‖anticonformalPart A‖) =
      fun A => √(((A 0 0 - A 1 1) / 2) * ((A 0 0 - A 1 1) / 2) +
        ((A 1 0 + A 0 1) / 2) * ((A 1 0 + A 0 1) / 2)) := by
    funext A
    rw [Complex.norm_def, Complex.normSq_apply]
    rfl
  rw [h]
  have e : ∀ i j : Fin 2, Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j :=
    fun i j => continuous_id.matrix_elem i j
  exact Real.continuous_sqrt.comp ((((e 0 0).sub (e 1 1)).div_const 2).mul
    (((e 0 0).sub (e 1 1)).div_const 2) |>.add
    ((((e 1 0).add (e 0 1)).div_const 2).mul (((e 1 0).add (e 0 1)).div_const 2)))

/-- `burkholderCoord p` is continuous for `p ≥ 1`. -/
theorem continuous_burkholderCoord (hp : 1 ≤ p) : Continuous (burkholderCoord p) := by
  have h1 := continuous_norm_conformalPart
  have h2 := continuous_norm_anticonformalPart
  exact ((Real.continuous_rpow_const (by linarith : 0 ≤ p - 1)).comp (h1.add h2)).mul
    (h1.sub (continuous_const.mul h2))

/-- `burkholderCoord p` at `J A`, `J = diag (1, −1)`: the conformal and anticonformal parts
change roles. -/
theorem burkholderCoord_reflection_mul (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderCoord p (reflection * A) =
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
        (‖anticonformalPart A‖ - (p - 1) * ‖conformalPart A‖) := by
  rw [burkholderCoord, conformalPart_reflection_mul, anticonformalPart_reflection_mul]
  simp only [RCLike.norm_conj]
  rw [add_comm]

/-- A Burkholder-type function is a combination of `burkholderCoord p` and its mirror image;
the coefficients are nonnegative exactly when `(2 − p) |m| ≤ p c₀` (for `0 < p < 2`). -/
theorem burkholderTypeCoord_eq (hp0 : 0 < p) (hp2 : p < 2) (c₀ m : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderTypeCoord p c₀ m A =
      (p * c₀ + (2 - p) * m) / (p * (2 - p)) * burkholderCoord p A +
        (p * c₀ - (2 - p) * m) / (p * (2 - p)) * burkholderCoord p (reflection * A) := by
  rw [burkholderCoord_reflection_mul, burkholderCoord, burkholderTypeCoord]
  have h2 : (2 - p) ≠ 0 := by linarith
  field_simp
  ring

/-- If `burkholderCoord p` is quasiconvex, so is every Burkholder-type function with
`(2 − p) |m| ≤ p c₀`, `1 ≤ p < 2`. -/
theorem quasiconvex_burkholderTypeCoord (hp1 : 1 ≤ p) (hp2 : p < 2) {c₀ m : ℝ}
    (hc : (2 - p) * |m| ≤ p * c₀) (hB : Quasiconvex (burkholderCoord p)) :
    Quasiconvex (burkholderTypeCoord p c₀ m) := by
  have hp0 : 0 < p := by linarith
  have hden : 0 < p * (2 - p) := mul_pos hp0 (by linarith)
  have hm1 : (2 - p) * m ≤ p * c₀ :=
    (mul_le_mul_of_nonneg_left (le_abs_self m) (by linarith)).trans hc
  have hm2 : (2 - p) * -m ≤ p * c₀ :=
    (mul_le_mul_of_nonneg_left (neg_le_abs m) (by linarith)).trans hc
  have hcB : Continuous (burkholderCoord p) := continuous_burkholderCoord hp1
  have hcB' : Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => burkholderCoord p (reflection * A) :=
    hcB.comp (continuous_const.mul continuous_id)
  have h := quasiconvex_add_mul (a := (p * c₀ + (2 - p) * m) / (p * (2 - p)))
    (b := (p * c₀ - (2 - p) * m) / (p * (2 - p))) (div_nonneg (by linarith) hden.le)
    (div_nonneg (by linarith) hden.le) hB hcB (quasiconvex_comp_reflection_mul hB) hcB'
  have he : burkholderTypeCoord p c₀ m = fun A =>
      (p * c₀ + (2 - p) * m) / (p * (2 - p)) * burkholderCoord p A +
        (p * c₀ - (2 - p) * m) / (p * (2 - p)) * burkholderCoord p (reflection * A) :=
    funext fun A => burkholderTypeCoord_eq hp0 hp2 c₀ m A
  rw [he]
  exact h

/-- A Burkholder-type function is continuous for `p ≥ 1`. -/
theorem continuous_burkholderTypeCoord (hp : 1 ≤ p) (c₀ m : ℝ) :
    Continuous (burkholderTypeCoord p c₀ m) := by
  have h1 := continuous_norm_conformalPart
  have h2 := continuous_norm_anticonformalPart
  exact ((Real.continuous_rpow_const (by linarith : 0 ≤ p - 1)).comp (h1.add h2)).mul
    ((continuous_const.mul (h1.add h2)).add (continuous_const.mul (h1.sub h2)))

/-- Let `F ≥ 0` be isotropic, positively `p`-homogeneous and rank-one convex on `ℝ^{2×2}`,
`1 ≤ p < 2`. If `burkholderCoord p` is quasiconvex, then `F` is quasiconvex. -/
theorem quasiconvex_of_rankOneConvex_of_burkholderCoord (hp1 : 1 ≤ p) (hp2 : p < 2)
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : RankOneConvex F) (hB : Quasiconvex (burkholderCoord p)) : Quasiconvex F := by
  intro A₀
  obtain ⟨c₀, m, hc, hle, heq⟩ := exists_burkholderTypeCoord_le hp1 hp2 h0 hiso hhom hrc A₀
  exact quasiconvexAtOn_of_le_of_eq (quasiconvex_burkholderTypeCoord hp1 hp2 hc hB A₀)
    (continuous_burkholderTypeCoord hp1 c₀ m) hle heq

/-! ### The exponent `p = 1`, with no sign condition -/

/-- An isotropic, positively `1`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is
nonnegative. -/
theorem nonneg_of_rankOneConvex_one (hiso : IsIsotropic F) (hhom : IsPosHomogeneous 1 F)
    (hrc : RankOneConvex F) (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ F A := by
  rw [hiso.eq_profile A]
  exact (isProfile_profile hiso hhom hrc).nonneg_of_one (norm_nonneg _) (norm_nonneg _)

/-- `burkholderCoord 1` is the modulus of the conformal part. -/
theorem burkholderCoord_one (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderCoord 1 A = ‖conformalPart A‖ := by
  simp [burkholderCoord]

/-- `burkholderCoord 1`, that is `A ↦ |z|`, is quasiconvex: it has an affine support at every
matrix. -/
theorem quasiconvex_burkholderCoord_one : Quasiconvex (burkholderCoord 1) := by
  refine quasiconvex_of_hasPolyaffineSupportAt fun A₀ => ?_
  obtain ⟨u, hu, huz⟩ := exists_norm_eq_one_mul_eq_norm (conformalPart A₀)
  have hK : ∀ A, polyaffine 0 (ofComplex ((starRingEnd ℂ) u / 2) 0) 0 A =
      (u * conformalPart A).re := by
    intro A
    have e : (starRingEnd ℂ) ((starRingEnd ℂ) u / 2) * conformalPart A =
        ((1 / 2 : ℝ) : ℂ) * (u * conformalPart A) := by
      rw [map_div₀, Complex.conj_conj, map_ofNat]
      push_cast
      ring
    rw [polyaffine, sum_ofComplex_mul, e, Complex.re_ofReal_mul, map_zero, zero_mul,
      Complex.zero_re]
    ring
  refine ⟨0, ofComplex ((starRingEnd ℂ) u / 2) 0, 0, fun A => ?_, ?_⟩
  · rw [hK, burkholderCoord_one]
    calc (u * conformalPart A).re ≤ ‖u * conformalPart A‖ := Complex.re_le_norm _
      _ = ‖conformalPart A‖ := by rw [norm_mul, hu, one_mul]
  · rw [hK, burkholderCoord_one, huz, Complex.ofReal_re]

/-- An isotropic, positively `1`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is convex
(Dacorogna): at every matrix it has a touching minorant `(c₀ + m) |z| + (c₀ − m) |w|` with
`|m| ≤ c₀`, which is convex. -/
theorem convexOn_of_rankOneConvex_one (hiso : IsIsotropic F) (hhom : IsPosHomogeneous 1 F)
    (hrc : RankOneConvex F) : ConvexOn ℝ Set.univ F := by
  have h0 := nonneg_of_rankOneConvex_one hiso hhom hrc
  refine ⟨convex_univ, fun A _ B _ a b ha hb _ => ?_⟩
  obtain ⟨c₀, m, hc, hle, heq⟩ := exists_burkholderTypeCoord_le le_rfl one_lt_two h0 hiso hhom hrc
    (a • A + b • B)
  have hG : ∀ C, burkholderTypeCoord 1 c₀ m C =
      (c₀ + m) * ‖conformalPart C‖ + (c₀ - m) * ‖anticonformalPart C‖ := by
    intro C
    simp [burkholderTypeCoord]
    ring
  have hz : ‖conformalPart (a • A + b • B)‖ ≤ a * ‖conformalPart A‖ + b * ‖conformalPart B‖ := by
    rw [conformalPart_add, conformalPart_smul, conformalPart_smul]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  have hw : ‖anticonformalPart (a • A + b • B)‖ ≤
      a * ‖anticonformalPart A‖ + b * ‖anticonformalPart B‖ := by
    rw [anticonformalPart_add, anticonformalPart_smul, anticonformalPart_smul]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  have hcm1 : 0 ≤ c₀ + m := by linarith [neg_le_abs m]
  have hcm2 : 0 ≤ c₀ - m := by linarith [le_abs_self m]
  simp only [smul_eq_mul]
  calc F (a • A + b • B) = burkholderTypeCoord 1 c₀ m (a • A + b • B) := heq.symm
    _ = (c₀ + m) * ‖conformalPart (a • A + b • B)‖ +
        (c₀ - m) * ‖anticonformalPart (a • A + b • B)‖ := hG _
    _ ≤ (c₀ + m) * (a * ‖conformalPart A‖ + b * ‖conformalPart B‖) +
        (c₀ - m) * (a * ‖anticonformalPart A‖ + b * ‖anticonformalPart B‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hz hcm1) (mul_le_mul_of_nonneg_left hw hcm2)
    _ = a * burkholderTypeCoord 1 c₀ m A + b * burkholderTypeCoord 1 c₀ m B := by
      rw [hG, hG]
      ring
    _ ≤ a * F A + b * F B :=
      add_le_add (mul_le_mul_of_nonneg_left (hle A) ha) (mul_le_mul_of_nonneg_left (hle B) hb)

/-- An isotropic, positively `1`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is
quasiconvex. -/
theorem quasiconvex_of_rankOneConvex_one (hiso : IsIsotropic F) (hhom : IsPosHomogeneous 1 F)
    (hrc : RankOneConvex F) : Quasiconvex F :=
  quasiconvex_of_rankOneConvex_of_burkholderCoord le_rfl one_lt_two
    (nonneg_of_rankOneConvex_one hiso hhom hrc) hiso hhom hrc quasiconvex_burkholderCoord_one

/-! ### The exponents `0 < p < 1` -/

/-- A rank-one convex function on `ℝ^{2×2}` is continuous. -/
theorem continuous_of_rankOneConvex (hrc : RankOneConvex F) : Continuous F :=
  hrc.locallyLipschitz.continuous

/-- For `0 < p < 1`, a positively `p`-homogeneous, rank-one convex `F` grows sublinearly along
every line: `F (A + T B) / T → 0` as `T → +∞`. -/
theorem tendsto_div_atTop_of_lt_one (hp1 : p < 1) (hhom : IsPosHomogeneous p F)
    (hc : Continuous F) (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    Filter.Tendsto (fun T : ℝ => F (A + T • B) / T) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun T : ℝ => T ^ (-(1 - p))) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have h2 : Filter.Tendsto (fun T : ℝ => F (T⁻¹ • A + B)) Filter.atTop (nhds (F B)) := by
    have h : Filter.Tendsto (fun T : ℝ => T⁻¹ • A + B) Filter.atTop (nhds ((0 : ℝ) • A + B)) :=
      (tendsto_inv_atTop_zero.smul_const A).add_const B
    rw [zero_smul, zero_add] at h
    exact (hc.tendsto B).comp h
  have h3 := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with T hT
  have e : A + T • B = T • (T⁻¹ • A + B) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  rw [e, hhom T hT, show -(1 - p) = p - 1 by ring, Real.rpow_sub_one hT.ne']
  ring

/-- **Proposition 1.7.** For `0 < p < 1`, a positively `p`-homogeneous, rank-one convex function
on `ℝ^{2×2}` vanishes identically; neither isotropy nor a sign condition is needed. Along every
rank-one line it is convex of sublinear growth, hence constant, and the rank-one matrices span
`ℝ^{2×2}`. -/
theorem eq_zero_of_rankOneConvex_of_lt_one (hp0 : 0 < p) (hp1 : p < 1)
    (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    F A = 0 := by
  have hc : Continuous F := continuous_of_rankOneConvex hrc
  have hF0 : F 0 = 0 := by
    have h := hhom 2 two_pos 0
    rw [smul_zero] at h
    have h2 : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow one_lt_two hp0
    nlinarith
  -- `F` is constant along rank-one lines
  have hline : ∀ X B : Matrix (Fin 2) (Fin 2) ℝ, B.rank = 1 → ∀ t : ℝ, F (X + t • B) = F X := by
    intro X B hB t
    have hbot : Filter.Tendsto (fun T : ℝ => F (X + T • B) / T) Filter.atBot (nhds 0) := by
      have h := ((tendsto_div_atTop_of_lt_one hp1 hhom hc X (-B)).comp
        Filter.tendsto_neg_atBot_atTop).neg
      rw [neg_zero] at h
      refine h.congr fun T => ?_
      simp only [Function.comp_apply, neg_smul_neg, div_neg, neg_neg]
    have h := (hrc X B hB).eq_of_tendsto_div_zero
      (tendsto_div_atTop_of_lt_one hp1 hhom hc X B) hbot t 0
    simpa using h
  -- four rank-one directions that span the matrices
  have h1 : (ofComplex (1 / 2) (1 / 2)).rank = 1 :=
    rank_ofComplex_eq_one rfl (by norm_num)
  have h2 : (ofComplex (1 / 2) (-(1 / 2))).rank = 1 :=
    rank_ofComplex_eq_one (by simp) (by norm_num)
  have h3 : (ofComplex (Complex.I / 2) (Complex.I / 2)).rank = 1 :=
    rank_ofComplex_eq_one rfl (by simp)
  have h4 : (ofComplex (-(Complex.I / 2)) (Complex.I / 2)).rank = 1 :=
    rank_ofComplex_eq_one (by simp) (by simp)
  have e : A = 0 + A 0 0 • ofComplex (1 / 2) (1 / 2) + A 1 1 • ofComplex (1 / 2) (-(1 / 2)) +
      A 1 0 • ofComplex (Complex.I / 2) (Complex.I / 2) +
      A 0 1 • ofComplex (-(Complex.I / 2)) (Complex.I / 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ofComplex] <;> ring
  rw [e, hline _ _ h4, hline _ _ h3, hline _ _ h2, hline _ _ h1, hF0]

/-! ### All exponents `p > 0` -/

/-- Let `p > 0` and let `F ≥ 0` be isotropic, positively `p`-homogeneous and rank-one convex on
`ℝ^{2×2}`. Then `F` is quasiconvex, if `burkholderCoord p` is quasiconvex when `1 < p < 2`. For
`0 < p < 1` it is `0`, for `p = 1` it is convex, and for `p ≥ 2` it is polyconvex.
`quasiconvex_of_rankOneConvex_of_pos` removes the hypothesis. -/
theorem quasiconvex_of_rankOneConvex_of_pos_of_burkholderCoord (hp : 0 < p) (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F)
    (hB : 1 < p → p < 2 → Quasiconvex (burkholderCoord p)) : Quasiconvex F := by
  rcases lt_or_ge p 1 with hp1 | hp1
  · have hz := eq_zero_of_rankOneConvex_of_lt_one hp hp1 hhom hrc
    exact quasiconvex_of_hasPolyaffineSupportAt fun A =>
      ⟨0, 0, 0, fun X => by simp [polyaffine, hz X], by simp [polyaffine, hz A]⟩
  rcases lt_or_ge p 2 with hp2 | hp2
  · rcases hp1.eq_or_lt with h1 | h1
    · subst h1
      exact quasiconvex_of_rankOneConvex_one hiso hhom hrc
    · exact quasiconvex_of_rankOneConvex_of_burkholderCoord hp1 hp2 h0 hiso hhom hrc (hB h1 hp2)
  · exact quasiconvex_of_rankOneConvex hp2 h0 hiso hhom hrc

end HomogeneousIsotropic
