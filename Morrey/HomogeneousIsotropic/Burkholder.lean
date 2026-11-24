module

public import Morrey.HomogeneousIsotropic.Main
public import Agazzi.Bridges
public import Agazzi.Quasiconvex

/-!
# The operator norm, the Burkholder function, and the exponents below `2`

`Morrey/HomogeneousIsotropic/Main.lean` works in conformal coordinates. This file passes to the
operator norm `|A|` and to the Burkholder function `B_p` as the paper writes them, and states
the results for `1 ≤ p < 2` and for every `p > 0`. The numbers are those of the paper,
`docs/HomogeneousIsotropic/paper/main.tex`.

* `opNorm_eq` (**Lemma 2.1 (a)**): `|A| = |z| + |w|`.
* `burkholderType_eq_coord`, `burkholder_eq_coord`: `G_{c₀,m}` and `B_p` in conformal
  coordinates; `burkholder_eq_burkholderType`: `B_p = G_{|1 − 2/p|, 1}`.
* `apply_eq_opNorm_rpow_mul`: `F (A) = |A|^p h (det A / |A|²)` with `h (s) = F (diag (1, s))`.
* `exists_burkholderType_le` (**Theorem 1.5**) and the identity `burkholderType_eq`.
* `quasiconvex_burkholder`: `B_p` is quasiconvex for `1 < p < 2`. This is claimed as Corollary 2
  of the preprint of A. Agazzi et al., *Sharp higher integrability theory, Part I: the
  `L^p`-norm of the Beurling–Ahlfors transform*, arXiv:2609.28311v2. The package lean4-iwaniec is
  the Lean formalization with which that preprint was audited; it proves the statement
  (`Agazzi.quasiconvex_burkholder`), and it is taken from there.
* `quasiconvex_of_rankOneConvex_of_burkholder`: for `1 ≤ p < 2`, if `B_p` is quasiconvex, so is
  every nonnegative, isotropic, positively `p`-homogeneous, rank-one convex `F`.
* `quasiconvex_of_rankOneConvex_of_lt_two` (**Corollary 1.6 (a)**) and
  `quasiconvex_of_rankOneConvex_of_pos` (**Corollary 1.8**).
-/

@[expose] public section

open CalculusOfVariations

namespace HomogeneousIsotropic

variable {p : ℝ} {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}

/-! ### The operator norm -/

/-- **Lemma 2.1 (a), the operator norm.** `|A| = |z| + |w|`: `Agazzi.opNorm_eq` of the package
lean4-iwaniec, whose conformal and anticonformal parts are those of this library. -/
theorem opNorm_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    opNorm A = ‖conformalPart A‖ + ‖anticonformalPart A‖ :=
  Agazzi.opNorm_eq A

/-- A matrix is `0` if the moduli of its conformal and anticonformal parts add up to `0`. -/
theorem eq_zero_of_norm_add_norm_eq_zero {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : ‖conformalPart A‖ + ‖anticonformalPart A‖ = 0) : A = 0 := by
  have hx0 := norm_nonneg (conformalPart A)
  have hy0 := norm_nonneg (anticonformalPart A)
  have hz : conformalPart A = 0 := norm_eq_zero.1 (by linarith)
  have hw : anticonformalPart A = 0 := norm_eq_zero.1 (by linarith)
  rw [← ofComplex_conformalPart A, hz, hw, ofComplex_zero]

/-! ### The Burkholder-type functions and the Burkholder function in coordinates -/

/-- The Burkholder-type function `|A|^{p−2} (c₀ |A|² + m det A)` in conformal coordinates:
`(|z| + |w|)^{p−1} (c₀ (|z| + |w|) + m (|z| − |w|))`. -/
theorem burkholderType_eq_coord (p c₀ m : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderType p c₀ m A = burkholderTypeCoord p c₀ m A := by
  rw [burkholderType, burkholderTypeCoord, opNorm_eq, det_eq_norm_sq_sub]
  have hx0 := norm_nonneg (conformalPart A)
  have hy0 := norm_nonneg (anticonformalPart A)
  rcases (add_nonneg hx0 hy0).eq_or_lt with h | h
  · have hx' : ‖conformalPart A‖ = 0 := by linarith
    have hy' : ‖anticonformalPart A‖ = 0 := by linarith
    simp [hx', hy']
  · have hpow : (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) =
        (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 2) *
          (‖conformalPart A‖ + ‖anticonformalPart A‖) := by
      rw [← Real.rpow_add_one h.ne']
      congr 1
      ring
    rw [hpow]
    ring

/-- The Burkholder-type function of `A` is the Burkholder-type function of the profile variables
(Definition 3.2) at the moduli of the coordinates of `A`. -/
theorem burkholderType_eq_profile (p c₀ m : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderType p c₀ m A =
      burkholderProfile p c₀ m ‖conformalPart A‖ ‖anticonformalPart A‖ :=
  burkholderType_eq_coord p c₀ m A

/-- The Burkholder function in conformal coordinates, for `0 < p ≤ 2`:
`B_p = (2/p) (|z| − (p − 1) |w|) (|z| + |w|)^{p−1}`. -/
theorem burkholder_eq_coord (hp0 : 0 < p) (hp2 : p ≤ 2) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholder p A = 2 / p * burkholderCoord p A := by
  have h1 : 1 ≤ 2 / p := by
    rw [le_div_iff₀ hp0]
    linarith
  have habs : |1 - 2 / p| = 2 / p - 1 := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [burkholder, burkholderCoord, opNorm_eq, det_eq_norm_sq_sub, habs]
  have hx0 := norm_nonneg (conformalPart A)
  have hy0 := norm_nonneg (anticonformalPart A)
  rcases (add_nonneg hx0 hy0).eq_or_lt with h | h
  · have hx' : ‖conformalPart A‖ = 0 := by linarith
    have hy' : ‖anticonformalPart A‖ = 0 := by linarith
    simp [hx', hy']
  · have hpow : (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) =
        (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 2) *
          (‖conformalPart A‖ + ‖anticonformalPart A‖) := by
      rw [← Real.rpow_add_one h.ne']
      congr 1
      ring
    rw [hpow]
    field_simp
    ring

/-- The Burkholder function is the Burkholder-type function with the coefficients
`(|1 − 2/p|, 1)`. -/
theorem burkholder_eq_burkholderType (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholder p A = burkholderType p |1 - 2 / p| 1 A := by
  rw [burkholder, burkholderType]
  ring

/-- For `F` with the common hypotheses, `F (A) = |A|^p h (det A / |A|²)` for `A ≠ 0`, where
`h (s) = F (diag (1, s))`: the function `h` of one variable determines `F`. -/
theorem apply_eq_opNorm_rpow_mul (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : RankOneConvex F) {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A ≠ 0) :
    F A = opNorm A ^ p * F !![1, 0; 0, A.det / opNorm A ^ 2] := by
  have hΦ := isProfile_profile hiso hhom hrc
  have hx0 := norm_nonneg (conformalPart A)
  have hy0 := norm_nonneg (anticonformalPart A)
  have hpos : 0 < ‖conformalPart A‖ + ‖anticonformalPart A‖ := by
    rcases (add_nonneg hx0 hy0).eq_or_lt with h | h
    · exact absurd (eq_zero_of_norm_add_norm_eq_zero h.symm) hA
    · exact h
  have hne := hpos.ne'
  rw [hiso.eq_profile A, hΦ.eq_rpow_mul hx0 hy0 hpos, opNorm_eq, det_eq_norm_sq_sub,
    ← profile_half_add_half_sub F]
  congr 2
  · field_simp
    ring
  · field_simp
    ring

/-! ### The exponents `1 ≤ p < 2` -/

/-- **Theorem 1.5.** Let `F ≥ 0` be isotropic, positively `p`-homogeneous and rank-one convex on
`ℝ^{2×2}`, `1 ≤ p < 2`. At every matrix `A₀` there are `c₀`, `m` with `(2 − p) |m| ≤ p c₀` such
that the Burkholder-type function `G_{c₀,m} (A) = |A|^{p−2} (c₀ |A|² + m det A)` lies below `F`
and equals `F` at `A₀`. -/
theorem exists_burkholderType_le (hp1 : 1 ≤ p) (hp2 : p < 2) (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F)
    (A₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ c₀ m : ℝ, (2 - p) * |m| ≤ p * c₀ ∧ (∀ A, burkholderType p c₀ m A ≤ F A) ∧
      burkholderType p c₀ m A₀ = F A₀ := by
  obtain ⟨c₀, m, hc, hle, heq⟩ := exists_burkholderTypeCoord_le hp1 hp2 h0 hiso hhom hrc A₀
  refine ⟨c₀, m, hc, fun A => ?_, ?_⟩
  · rw [burkholderType_eq_coord]
    exact hle A
  · rw [burkholderType_eq_coord]
    exact heq

/-- **The identity of Theorem 1.5.** For `0 < p < 2`, a Burkholder-type function is a
combination of the Burkholder function and of its mirror image `A ↦ B_p (J A)`,
`J = diag (1, −1)`:
`G_{c₀,m} = (p c₀ + (2 − p) m)/(2 (2 − p)) B_p + (p c₀ − (2 − p) m)/(2 (2 − p)) B_p (J ·)`.
The coefficients are nonnegative exactly when `(2 − p) |m| ≤ p c₀`. -/
theorem burkholderType_eq (hp0 : 0 < p) (hp2 : p < 2) (c₀ m : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderType p c₀ m A =
      (p * c₀ + (2 - p) * m) / (2 * (2 - p)) * burkholder p A +
        (p * c₀ - (2 - p) * m) / (2 * (2 - p)) * burkholder p (reflection * A) := by
  rw [burkholderType_eq_coord, burkholderTypeCoord_eq hp0 hp2, burkholder_eq_coord hp0 hp2.le,
    burkholder_eq_coord hp0 hp2.le]
  have h2 : (2 - p) ≠ 0 := by linarith
  field_simp

/-- **The Burkholder function is quasiconvex for `1 < p < 2`** (claimed as Corollary 2 of Agazzi
et al., arXiv:2609.28311v2): from `Agazzi.quasiconvex_burkholder` of the package lean4-iwaniec,
which states it for `(p/2) B_p` in conformal coordinates. -/
theorem quasiconvex_burkholder (hp1 : 1 < p) (hp2 : p < 2) : Quasiconvex (burkholder p) := by
  have hp0 : 0 < p := by linarith
  have h : Quasiconvex (burkholderCoord p) := Agazzi.quasiconvex_burkholder p hp1 hp2
  have h' := Agazzi.quasiconvex_const_mul h (c := 2 / p) (by positivity)
  have he : burkholder p = fun A => 2 / p * burkholderCoord p A :=
    funext fun A => burkholder_eq_coord hp0 hp2.le A
  rw [he]
  exact h'

/-- Let `F ≥ 0` be isotropic, positively `p`-homogeneous and rank-one convex on `ℝ^{2×2}`,
`1 ≤ p < 2`. If the Burkholder function `B_p` is quasiconvex, then `F` is quasiconvex. -/
theorem quasiconvex_of_rankOneConvex_of_burkholder (hp1 : 1 ≤ p) (hp2 : p < 2)
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : RankOneConvex F) (hB : Quasiconvex (burkholder p)) : Quasiconvex F := by
  have hp0 : 0 < p := by linarith
  have h' := Agazzi.quasiconvex_const_mul hB (c := p / 2) (by positivity)
  have he : burkholderCoord p = fun A => p / 2 * burkholder p A := by
    funext A
    rw [burkholder_eq_coord hp0 hp2.le]
    field_simp
  refine quasiconvex_of_rankOneConvex_of_burkholderCoord hp1 hp2 h0 hiso hhom hrc ?_
  rw [he]
  exact h'

/-- **Corollary 1.6 (a).** For `1 < p < 2`, a nonnegative, isotropic, positively
`p`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is quasiconvex. -/
theorem quasiconvex_of_rankOneConvex_of_lt_two (hp1 : 1 < p) (hp2 : p < 2)
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : RankOneConvex F) : Quasiconvex F :=
  quasiconvex_of_rankOneConvex_of_burkholder hp1.le hp2 h0 hiso hhom hrc
    (quasiconvex_burkholder hp1 hp2)

/-! ### All exponents `p > 0` -/

/-- **Corollary 1.8.** For every `p > 0`, a nonnegative, isotropic, positively `p`-homogeneous,
rank-one convex integrand on `ℝ^{2×2}` is quasiconvex. For `0 < p < 1` it is `0`, for `p = 1` it
is convex, for `1 < p < 2` this is Corollary 1.6 (a), and for `p ≥ 2` it is polyconvex. -/
theorem quasiconvex_of_rankOneConvex_of_pos (hp : 0 < p) (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F) :
    Quasiconvex F := by
  refine quasiconvex_of_rankOneConvex_of_pos_of_burkholderCoord hp h0 hiso hhom hrc
    fun h1 h2 => ?_
  exact Agazzi.quasiconvex_burkholder p h1 h2

end HomogeneousIsotropic
