module

public import Morrey.HomogeneousIsotropic.Signed.Radial
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The Burkholder function is a radial function

Let `σ = |z| + |w|` and `δ = |z| − |w|` for the conformal part `z` and the anticonformal part `w`
of a matrix, and let `N (r) = r₊^{p−1}`, `p > 0`. Since `∫₀^σ N = σ^p / p`, the radial function
of Proposition 6.8 is `radial e N = σ^{p−1} ((1 − 2/p) σ + e δ)`, the Burkholder-type function
`G_{1 − 2/p, e}` in conformal coordinates (`radial_rpow`), and `radial e (−N) = −radial e N`
(`radial_neg_rpow`). The Burkholder function is `B_p = σ^{p−1} (|1 − 2/p| σ + δ)`
(`burkholder_eq_burkholderTypeCoord`), and `B_p (J ·)` has `−δ` in place of `δ`
(`burkholderTypeCoord_reflection_mul`). This is **Corollary 6.11** of the paper:

* `radial_rpow_eq_burkholder`, `radial_rpow_eq_burkholder_reflection_mul`: for `p ≥ 2`,
  `B_p = radial 1 N` and `B_p (J ·) = radial (−1) N`, and `N` is convex on `[0, ∞)`.
* `radial_neg_rpow_eq_burkholder`, `radial_neg_rpow_eq_burkholder_reflection_mul`: for
  `1 < p ≤ 2`, `B_p = radial (−1) (−N)` and `B_p (J ·) = radial 1 (−N)`, and `−N` is convex on
  `[0, ∞)`.
* `quasiconvex_burkholder_of_one_lt`, `quasiconvex_burkholder_reflection_mul`: by Proposition 6.8,
  `B_p` and `B_p (J ·)` are quasiconvex for every `p > 1`. The proof uses the quasiconvexity of
  the truncated determinant (`Agazzi.quasiconvex_integrandL` of the package lean4-iwaniec), and
  not that of the Burkholder function, which is claimed as Corollary 2 of the preprint of
  A. Agazzi et al., arXiv:2609.28311v2.

The consequences:

* `quasiconvex_burkholder` (`1 < p < 2`) and `quasiconvex_burkholderCoord` (`1 < p ≤ 2`).
* `quasiconvex_of_rankOneConvex_of_lt_two` (**Corollary 1.6 (a)**).
* `quasiconvex_of_rankOneConvex_of_pos` (the nonnegative case of **Theorem A**).
-/

@[expose] public section

open Set CalculusOfVariations

namespace HomogeneousIsotropic

variable {p : ℝ} {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}

/-! ### The radial function of a power -/

/-- `∫₀^σ r₊^{p−1} dr = σ^p / p` for `p > 0` and `σ ≥ 0`. -/
theorem integral_max_rpow (hp : 0 < p) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ r in (0 : ℝ)..σ, max r 0 ^ (p - 1) = σ ^ p / p := by
  have h : ∫ r in (0 : ℝ)..σ, max r 0 ^ (p - 1) = ∫ r in (0 : ℝ)..σ, r ^ (p - 1) :=
    intervalIntegral.integral_congr fun r hr => by
      rw [uIcc_of_le hσ] at hr
      simp only [max_eq_left hr.1]
  rw [h, integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.zero_rpow hp.ne', sub_zero]

/-- The radial function of `N (r) = r₊^{p−1}`, `p > 0`, is the Burkholder-type function
`σ^{p−1} ((1 − 2/p) σ + e δ)`, `σ = |z| + |w|`, `δ = |z| − |w|`. -/
theorem radial_rpow (hp : 0 < p) (e : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    radial e (fun r => max r 0 ^ (p - 1)) A = burkholderTypeCoord p (1 - 2 / p) e A := by
  have hσ : 0 ≤ ‖conformalPart A‖ + ‖anticonformalPart A‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpow : (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ p =
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
        (‖conformalPart A‖ + ‖anticonformalPart A‖) := by
    rw [← Real.rpow_add_one' hσ (by linarith)]
    congr 1
    ring
  unfold radial radialProfile
  beta_reduce
  rw [integral_max_rpow hp hσ, max_eq_left hσ, hpow, burkholderTypeCoord]
  field_simp
  ring

/-- The radial function of `−N` is `−radial e N`. -/
theorem radial_neg (e : ℝ) (N : ℝ → ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    radial e (fun r => -N r) A = -radial e N A := by
  unfold radial radialProfile
  rw [intervalIntegral.integral_neg]
  ring

/-- The radial function of `N (r) = −r₊^{p−1}`, `p > 0`, is the Burkholder-type function
`σ^{p−1} ((2/p − 1) σ − e δ)`. -/
theorem radial_neg_rpow (hp : 0 < p) (e : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    radial e (fun r => -max r 0 ^ (p - 1)) A = burkholderTypeCoord p (2 / p - 1) (-e) A := by
  rw [radial_neg e (fun r => max r 0 ^ (p - 1)), radial_rpow hp, burkholderTypeCoord,
    burkholderTypeCoord]
  ring

/-! ### The Burkholder function in conformal coordinates -/

/-- The Burkholder function is the Burkholder-type function with the coefficients
`(|1 − 2/p|, 1)` in conformal coordinates: `B_p = σ^{p−1} (|1 − 2/p| σ + δ)`. -/
theorem burkholder_eq_burkholderTypeCoord (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholder p A = burkholderTypeCoord p |1 - 2 / p| 1 A := by
  rw [burkholder_eq_burkholderType, burkholderType_eq_coord]

/-- A Burkholder-type function at `J A`, `J = diag (1, −1)`: the reflection exchanges `|z|` and
`|w|`, so that `δ` changes sign. -/
theorem burkholderTypeCoord_reflection_mul (p c₀ m : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderTypeCoord p c₀ m (reflection * A) = burkholderTypeCoord p c₀ (-m) A := by
  rw [burkholderTypeCoord, burkholderTypeCoord, conformalPart_reflection_mul,
    anticonformalPart_reflection_mul, RCLike.norm_conj, RCLike.norm_conj,
    add_comm ‖anticonformalPart A‖]
  ring

/-- The Burkholder function is continuous for `p ≥ 1`. -/
theorem continuous_burkholder (hp : 1 ≤ p) : Continuous (burkholder p) := by
  rw [funext (burkholder_eq_burkholderTypeCoord p)]
  exact continuous_burkholderTypeCoord hp _ _

/-! ### The Burkholder function as a radial function (Corollary 6.11) -/

/-- **Corollary 6.11, `p ≥ 2`.** For `N (r) = r₊^{p−1}`, the radial function with `e = 1` is the
Burkholder function: `2 |z| N (σ) − 2 ∫₀^σ N = B_p`. -/
theorem radial_rpow_eq_burkholder (hp : 2 ≤ p) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    radial 1 (fun r => max r 0 ^ (p - 1)) A = burkholder p A := by
  have ha : |1 - 2 / p| = 1 - 2 / p :=
    abs_of_nonneg (by rw [sub_nonneg, div_le_one (by linarith)]; exact hp)
  rw [radial_rpow (by linarith), burkholder_eq_burkholderTypeCoord, ha]

/-- **Corollary 6.11, `p ≥ 2`, the mirror image.** For `N (r) = r₊^{p−1}`, the radial function with
`e = −1` is the Burkholder function composed with the reflection:
`2 |w| N (σ) − 2 ∫₀^σ N = B_p (J ·)`. -/
theorem radial_rpow_eq_burkholder_reflection_mul (hp : 2 ≤ p) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    radial (-1) (fun r => max r 0 ^ (p - 1)) A = burkholder p (reflection * A) := by
  have ha : |1 - 2 / p| = 1 - 2 / p :=
    abs_of_nonneg (by rw [sub_nonneg, div_le_one (by linarith)]; exact hp)
  rw [radial_rpow (by linarith), burkholder_eq_burkholderTypeCoord,
    burkholderTypeCoord_reflection_mul, ha]

/-- **Corollary 6.11, `1 < p ≤ 2`.** For `N (r) = −r₊^{p−1}`, the radial function with `e = −1` is
the Burkholder function: `2 |w| N (σ) − 2 ∫₀^σ N = B_p`. -/
theorem radial_neg_rpow_eq_burkholder (hp1 : 1 < p) (hp2 : p ≤ 2)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    radial (-1) (fun r => -max r 0 ^ (p - 1)) A = burkholder p A := by
  have ha : |1 - 2 / p| = 2 / p - 1 := by
    rw [abs_of_nonpos (by rw [sub_nonpos, le_div_iff₀ (by linarith)]; linarith)]
    ring
  rw [radial_neg_rpow (by linarith), burkholder_eq_burkholderTypeCoord, ha, neg_neg]

/-- **Corollary 6.11, `1 < p ≤ 2`, the mirror image.** For `N (r) = −r₊^{p−1}`, the radial function
with `e = 1` is the Burkholder function composed with the reflection:
`2 |z| N (σ) − 2 ∫₀^σ N = B_p (J ·)`. -/
theorem radial_neg_rpow_eq_burkholder_reflection_mul (hp1 : 1 < p) (hp2 : p ≤ 2)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    radial 1 (fun r => -max r 0 ^ (p - 1)) A = burkholder p (reflection * A) := by
  have ha : |1 - 2 / p| = 2 / p - 1 := by
    rw [abs_of_nonpos (by rw [sub_nonpos, le_div_iff₀ (by linarith)]; linarith)]
    ring
  rw [radial_neg_rpow (by linarith), burkholder_eq_burkholderTypeCoord,
    burkholderTypeCoord_reflection_mul, ha]

/-! ### The quasiconvexity of the Burkholder function -/

/-- `r ↦ r₊^{p−1}` is continuous for `p ≥ 1`. -/
theorem continuous_max_rpow (hp : 1 ≤ p) : Continuous fun r : ℝ => max r 0 ^ (p - 1) :=
  (continuous_id.max continuous_const).rpow_const fun _ => Or.inr (by linarith)

/-- `r ↦ r₊^{p−1}` vanishes at `0` for `p ≠ 1`. -/
theorem max_zero_rpow (hp : p ≠ 1) : max (0 : ℝ) 0 ^ (p - 1) = 0 := by
  rw [max_self, Real.zero_rpow (sub_ne_zero.2 hp)]

/-- **Corollary 6.11, `p ≥ 2`.** The Burkholder function is quasiconvex for `p ≥ 2`: Proposition
6.8 with `e = 1` and the convex function `N (r) = r₊^{p−1}`. -/
theorem quasiconvex_burkholder_of_two_le (hp : 2 ≤ p) : Quasiconvex (burkholder p) := by
  have hN : ConvexOn ℝ (Ici 0) fun r : ℝ => max r 0 ^ (p - 1) :=
    (convexOn_rpow (p := p - 1) (by linarith)).congr fun r hr => by
      simp only [max_eq_left (mem_Ici.1 hr)]
  have h := quasiconvex_radial (Or.inl rfl) hN (continuous_max_rpow (by linarith))
    (max_zero_rpow (by linarith)).le
  rwa [funext (radial_rpow_eq_burkholder hp)] at h

/-- **Corollary 6.11, `1 < p ≤ 2`.** The Burkholder function is quasiconvex for `1 < p ≤ 2`:
Proposition 6.8 with `e = −1` and the convex function `N (r) = −r₊^{p−1}`. -/
theorem quasiconvex_burkholder_of_le_two (hp1 : 1 < p) (hp2 : p ≤ 2) :
    Quasiconvex (burkholder p) := by
  have hN : ConvexOn ℝ (Ici 0) fun r : ℝ => -max r 0 ^ (p - 1) :=
    (Real.concaveOn_rpow (p := p - 1) (by linarith) (by linarith)).neg.congr fun r hr => by
      simp only [Pi.neg_apply, max_eq_left (mem_Ici.1 hr)]
  have h := quasiconvex_radial (Or.inr rfl) hN (continuous_max_rpow hp1.le).neg
    (by rw [max_zero_rpow hp1.ne', neg_zero])
  rwa [funext (radial_neg_rpow_eq_burkholder hp1 hp2)] at h

/-- **Corollary 6.11. The Burkholder function is quasiconvex for every `p > 1`**, by Proposition
6.8: it is `radial 1 N` with `N (r) = r₊^{p−1}` for `p ≥ 2`, and `radial (−1) N` with
`N (r) = −r₊^{p−1}` for `p ≤ 2`. Only the quasiconvexity of the truncated determinant is used. -/
theorem quasiconvex_burkholder_of_one_lt (hp : 1 < p) : Quasiconvex (burkholder p) := by
  rcases le_total 2 p with hp2 | hp2
  · exact quasiconvex_burkholder_of_two_le hp2
  · exact quasiconvex_burkholder_of_le_two hp hp2

/-- The mirror image `A ↦ B_p (J A)` of the Burkholder function, `J = diag (1, −1)`, is
quasiconvex for every `p > 1`. -/
theorem quasiconvex_burkholder_reflection_mul (hp : 1 < p) :
    Quasiconvex fun A => burkholder p (reflection * A) :=
  quasiconvex_comp_reflection_mul (quasiconvex_burkholder_of_one_lt hp)

/-- **The Burkholder function is quasiconvex for `1 < p < 2`** (claimed as Corollary 2 of Agazzi
et al., arXiv:2609.28311v2): the case `p < 2` of `quasiconvex_burkholder_of_one_lt`, from the
quasiconvexity of the truncated determinant by Proposition 6.8. -/
theorem quasiconvex_burkholder (hp1 : 1 < p) (hp2 : p < 2) : Quasiconvex (burkholder p) :=
  quasiconvex_burkholder_of_le_two hp1 hp2.le

/-- For `1 < p ≤ 2`, the function `(|z| + |w|)^{p−1} (|z| − (p − 1) |w|)`, which is `p/2` times
the Burkholder function, is quasiconvex. -/
theorem quasiconvex_burkholderCoord (hp1 : 1 < p) (hp2 : p ≤ 2) :
    Quasiconvex (burkholderCoord p) := by
  have hp0 : 0 < p := by linarith
  have he : burkholderCoord p = fun A => p / 2 * burkholder p A := by
    funext A
    rw [burkholder_eq_coord hp0 hp2]
    field_simp
  rw [he]
  exact Agazzi.quasiconvex_const_mul (quasiconvex_burkholder_of_one_lt hp1) (by positivity)

/-! ### Nonnegative integrands -/

/-- **Corollary 1.6 (a).** For `1 < p < 2`, a nonnegative, isotropic, positively
`p`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is quasiconvex. -/
theorem quasiconvex_of_rankOneConvex_of_lt_two (hp1 : 1 < p) (hp2 : p < 2)
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : RankOneConvex F) : Quasiconvex F :=
  quasiconvex_of_rankOneConvex_of_burkholder hp1.le hp2 h0 hiso hhom hrc
    (quasiconvex_burkholder hp1 hp2)

/-- **Theorem A for nonnegative integrands.** For every `p > 0`, a nonnegative, isotropic,
positively `p`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is quasiconvex. For
`0 < p < 1` it is `0`, for `p = 1` it is convex, for `1 < p < 2` this is Corollary 1.6 (a), and
for `p ≥ 2` it is polyconvex. -/
theorem quasiconvex_of_rankOneConvex_of_pos (hp : 0 < p) (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F) :
    Quasiconvex F :=
  quasiconvex_of_rankOneConvex_of_pos_of_burkholderCoord hp h0 hiso hhom hrc fun h1 h2 =>
    quasiconvex_burkholderCoord h1 h2.le

end HomogeneousIsotropic
