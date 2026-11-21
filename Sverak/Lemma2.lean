module

public import Sverak.Construction
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Šverák 1992, Lemma 2: the extension is rank-one convex

For each `ε > 0` there is `k = k(ε) > 0` such that
`F (X) = f (P X) + ε |X|² + ε |X|⁴ + k |X − P X|²` (`Morrey.sverakF ε k`) is rank-one convex on
`M^{3×2}`. The paper's proof:

1. eq. (6): `(d²/dt²) F (A + t Y)|₀ = (d²/dt²) f (P A + t P Y)|₀ + 2ε |Y|² + 4ε |A|² |Y|²
   + 8ε ⟨A, Y⟩² + 2k |Y − P Y|²`;
2. since `X ↦ f (P X)` is a homogeneous cubic polynomial, `(d²/dt²) f (P A + t P Y)|₀ ≥ −c |A| |Y|²`
   for some `c > 0`, so (7) and `(*)`: the second derivative is `≥ 0` when `|A| ≥ c / (4ε)`;
3. eq. (8) and a compactness argument on `𝒦 = {(A, Y) : |A| ≤ c/(4ε), rank Y = 1, |Y| = 1}`:
   there is `k₀` with `g (A, Y, k₀) > ε` on `𝒦`, otherwise a limit `(Ā, Ȳ)` would have
   `Ȳ = P Ȳ` (a rank-one direction of `L`) and `(d²/dt²) f (P Ā + t P Ȳ)|₀ ≤ −ε`, against the
   convexity of `f` on rank-one lines of `L` (`sverakf_affine_of_rankOne`);
4. together, `F` is rank-one convex for `k = k₀`.

In the formalization, `|X| = √(frobSq X)`, `c = 6` (`l2_d2f_ge`), and `k₀ = n + 1` for some
`n ∈ ℕ` (`l2_claim`). Eq. (6) is `l2_eq6`: `t ↦ F (A + t Y)` is a quartic in `t`, and its second
derivative at `t` is the right-hand side of (6) at `A + t Y` (`l2_D2`); convexity on `ℝ` then
follows from `convexOn_univ_of_deriv2_nonneg`. `𝒦` is closed because `rank Y = 1` is equivalent
to the vanishing of the `2 × 2` minors of `Y` together with `Y ≠ 0` (`l2_rank_eq_one_iff`).
-/

@[expose] public section

open Morrey Filter Topology

namespace Sverak

local notation "M32" => Matrix (Fin 3) (Fin 2) ℝ

/-! ### Coordinates -/

/-- The Frobenius inner product `⟨X, Y⟩ = ∑ X_{ij} Y_{ij}`. -/
def l2_inner (X Y : M32) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

/-- The second derivative `(d²/dt²) f (P X + t P Y)|_{t=0}`, written out: with
`f (P X) = −X₀₀ X₁₁ (X₂₀ + X₂₁) / 2`. -/
def l2_d2f (X Y : M32) : ℝ :=
  -(Y 0 0 * Y 1 1 * (X 2 0 + X 2 1) + Y 0 0 * X 1 1 * (Y 2 0 + Y 2 1) +
    X 0 0 * Y 1 1 * (Y 2 0 + Y 2 1))

/-- The right-hand side of eq. (6): the second derivative of `t ↦ F (X + t Y)` at `0`. -/
noncomputable def l2_D2 (ε k : ℝ) (X Y : M32) : ℝ :=
  l2_d2f X Y + 2 * ε * frobSq Y + 4 * ε * frobSq X * frobSq Y + 8 * ε * l2_inner X Y ^ 2 +
    2 * k * frobSq (Y - sverakP Y)

/-- The function `g (A, Y, k)` of eq. (8). -/
noncomputable def l2_g (ε k : ℝ) (X Y : M32) : ℝ :=
  l2_d2f X Y + 2 * ε * frobSq Y + 2 * k * frobSq (Y - sverakP Y)

theorem l2_frobSq_eq (X : M32) :
    frobSq X = X 0 0 ^ 2 + X 0 1 ^ 2 + X 1 0 ^ 2 + X 1 1 ^ 2 + X 2 0 ^ 2 + X 2 1 ^ 2 := by
  simp [frobSq, Fin.sum_univ_succ]
  ring

theorem l2_inner_eq (X Y : M32) :
    l2_inner X Y = X 0 0 * Y 0 0 + X 0 1 * Y 0 1 + X 1 0 * Y 1 0 + X 1 1 * Y 1 1 +
      X 2 0 * Y 2 0 + X 2 1 * Y 2 1 := by
  simp [l2_inner, Fin.sum_univ_succ]
  ring

theorem l2_frobSq_sub_eq (X : M32) :
    frobSq (X - sverakP X) = X 0 1 ^ 2 + X 1 0 ^ 2 + (X 2 0 - X 2 1) ^ 2 / 2 := by
  simp [frobSq, sverakP, Fin.sum_univ_succ]
  ring

theorem l2_sverakf_eq (X : M32) :
    sverakf X = -(X 0 0 * X 1 1 * ((X 2 0 + X 2 1) / 2)) := by
  simp [sverakf, sverakP]

theorem l2_frobSq_nonneg (X : M32) : 0 ≤ frobSq X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Each entry is bounded by the Frobenius norm `|X| = √(frobSq X)`. -/
theorem l2_abs_le_sqrt (X : M32) (i : Fin 3) (j : Fin 2) : |X i j| ≤ Real.sqrt (frobSq X) := by
  apply Real.abs_le_sqrt
  calc X i j ^ 2 ≤ ∑ j', X i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => X i j' ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', X i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', X i' j' ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem l2_eq_zero_of_frobSq {X : M32} (h : frobSq X = 0) : X = 0 := by
  ext i j
  have := l2_abs_le_sqrt X i j
  rw [h, Real.sqrt_zero] at this
  simpa using abs_nonpos_iff.1 this

theorem l2_frobSq_smul (c : ℝ) (X : M32) : frobSq (c • X) = c ^ 2 * frobSq X := by
  simp only [l2_frobSq_eq, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ### Eq. (6): the second derivative along a line -/

/-- A quartic `t ↦ c₀ + c₁ t + c₂ t² + c₃ t³ + c₄ t⁴` is twice differentiable, with second
derivative `2 c₂ + 6 c₃ t + 12 c₄ t²`. -/
theorem l2_quartic_deriv2 {φ : ℝ → ℝ} (c0 c1 c2 c3 c4 : ℝ)
    (hφ : ∀ t, φ t = c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4) :
    Differentiable ℝ φ ∧ Differentiable ℝ (deriv φ) ∧
      ∀ t, deriv^[2] φ t = 2 * c2 + 6 * c3 * t + 12 * c4 * t ^ 2 := by
  have h1 : ∀ t, HasDerivAt φ (c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3) t := by
    intro t
    rw [show φ = fun t => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4 from funext hφ]
    have := (((((hasDerivAt_id' t).const_mul c1).const_add c0).add
      ((hasDerivAt_pow 2 t).const_mul c2)).add ((hasDerivAt_pow 3 t).const_mul c3)).add
      ((hasDerivAt_pow 4 t).const_mul c4)
    convert this using 1
    push_cast
    ring
  have h2 : ∀ t, HasDerivAt (fun t => c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3)
      (2 * c2 + 6 * c3 * t + 12 * c4 * t ^ 2) t := by
    intro t
    have := ((((hasDerivAt_id' t).const_mul (2 * c2)).const_add c1).add
      ((hasDerivAt_pow 2 t).const_mul (3 * c3))).add ((hasDerivAt_pow 3 t).const_mul (4 * c4))
    convert this using 1
    push_cast
    ring
  have hd : deriv φ = fun t => c1 + 2 * c2 * t + 3 * c3 * t ^ 2 + 4 * c4 * t ^ 3 :=
    funext fun t => (h1 t).deriv
  refine ⟨fun t => (h1 t).differentiableAt, ?_, fun t => ?_⟩
  · rw [hd]
    exact fun t => (h2 t).differentiableAt
  · show deriv (deriv φ) t = _
    rw [hd, (h2 t).deriv]

/-- The second derivative of `t ↦ f (P A + t P Y)` at `0` is `l2_d2f A Y` (recall that
`sverakf X` is `f (P X)`). -/
theorem l2_d2f_eq_deriv2 (A Y : M32) :
    deriv^[2] (fun t : ℝ => sverakf (A + t • Y)) 0 = l2_d2f A Y := by
  refine ((l2_quartic_deriv2 (φ := fun t : ℝ => sverakf (A + t • Y)) (sverakf A)
    (-(Y 0 0 * A 1 1 * (A 2 0 + A 2 1) + A 0 0 * Y 1 1 * (A 2 0 + A 2 1) +
        A 0 0 * A 1 1 * (Y 2 0 + Y 2 1)) / 2)
    (l2_d2f A Y / 2) (-(Y 0 0 * Y 1 1 * (Y 2 0 + Y 2 1)) / 2) 0 fun t => ?_).2.2 0).trans ?_
  · simp only [l2_d2f, l2_sverakf_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · ring

/-- **Eq. (6)** (`sv-eq6`). `t ↦ F (A + t Y)` is twice differentiable, and its second derivative
at `t` is `(d²/dt²) f (P X + s P Y)|₀ + 2ε |Y|² + 4ε |X|² |Y|² + 8ε ⟨X, Y⟩² + 2k |Y − P Y|²`
(`l2_D2 ε k X Y`) at `X = A + t Y`. -/
theorem l2_eq6 (ε k : ℝ) (A Y : M32) :
    Differentiable ℝ (fun t : ℝ => sverakF ε k (A + t • Y)) ∧
      Differentiable ℝ (deriv fun t : ℝ => sverakF ε k (A + t • Y)) ∧
      ∀ t, deriv^[2] (fun t : ℝ => sverakF ε k (A + t • Y)) t = l2_D2 ε k (A + t • Y) Y := by
  obtain ⟨h1, h2, h3⟩ := l2_quartic_deriv2 (φ := fun t : ℝ => sverakF ε k (A + t • Y))
    (sverakF ε k A)
    (-(Y 0 0 * A 1 1 * (A 2 0 + A 2 1) + A 0 0 * Y 1 1 * (A 2 0 + A 2 1) +
        A 0 0 * A 1 1 * (Y 2 0 + Y 2 1)) / 2 + 2 * ε * l2_inner A Y +
      4 * ε * frobSq A * l2_inner A Y +
      2 * k * (A 0 1 * Y 0 1 + A 1 0 * Y 1 0 + (A 2 0 - A 2 1) * (Y 2 0 - Y 2 1) / 2))
    (l2_D2 ε k A Y / 2)
    ((-3 * (Y 0 0 * Y 1 1 * (Y 2 0 + Y 2 1)) + 24 * ε * l2_inner A Y * frobSq Y) / 6)
    (ε * frobSq Y ^ 2) (fun t => by
      simp only [sverakF, l2_D2, l2_d2f, l2_sverakf_eq, l2_frobSq_sub_eq]
      simp only [l2_frobSq_eq, l2_inner_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring)
  refine ⟨h1, h2, fun t => (h3 t).trans ?_⟩
  simp only [l2_D2, l2_d2f, l2_frobSq_sub_eq]
  simp only [l2_frobSq_eq, l2_inner_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `t ↦ F (A + t Y)` is convex as soon as the right-hand side of (6) is nonnegative along the
line. -/
theorem l2_convexOn_line (ε k : ℝ) (A Y : M32) (h : ∀ t : ℝ, 0 ≤ l2_D2 ε k (A + t • Y) Y) :
    ConvexOn ℝ Set.univ fun t : ℝ => sverakF ε k (A + t • Y) := by
  obtain ⟨h1, h2, h3⟩ := l2_eq6 ε k A Y
  exact convexOn_univ_of_deriv2_nonneg h1 h2 fun t => (h3 t).symm ▸ h t

/-! ### Eq. (7) and `(*)` -/

/-- Step 2 of the proof, with `c = 6`: `(d²/dt²) f (P A + t P Y)|₀ ≥ −c |A| |Y|²`. -/
theorem l2_d2f_ge (X Y : M32) : -(6 * Real.sqrt (frobSq X) * frobSq Y) ≤ l2_d2f X Y := by
  set a := Real.sqrt (frobSq X)
  set b := Real.sqrt (frobSq Y)
  have hY : frobSq Y = b ^ 2 := (Real.sq_sqrt (l2_frobSq_nonneg Y)).symm
  have hX := l2_abs_le_sqrt X
  have hY' := l2_abs_le_sqrt Y
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have t1 : |Y 0 0 * Y 1 1 * (X 2 0 + X 2 1)| ≤ b * b * (a + a) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hY' 0 0) (hY' 1 1) (abs_nonneg _) hb)
      ((abs_add_le _ _).trans (add_le_add (hX 2 0) (hX 2 1))) (abs_nonneg _) (by positivity)
  have t2 : |Y 0 0 * X 1 1 * (Y 2 0 + Y 2 1)| ≤ b * a * (b + b) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hY' 0 0) (hX 1 1) (abs_nonneg _) hb)
      ((abs_add_le _ _).trans (add_le_add (hY' 2 0) (hY' 2 1))) (abs_nonneg _) (by positivity)
  have t3 : |X 0 0 * Y 1 1 * (Y 2 0 + Y 2 1)| ≤ a * b * (b + b) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hX 0 0) (hY' 1 1) (abs_nonneg _) ha)
      ((abs_add_le _ _).trans (add_le_add (hY' 2 0) (hY' 2 1))) (abs_nonneg _) (by positivity)
  have key : |l2_d2f X Y| ≤ 6 * a * frobSq Y := by
    unfold l2_d2f
    rw [abs_neg, hY]
    calc _ ≤ |Y 0 0 * Y 1 1 * (X 2 0 + X 2 1)| + |Y 0 0 * X 1 1 * (Y 2 0 + Y 2 1)| +
          |X 0 0 * Y 1 1 * (Y 2 0 + Y 2 1)| := abs_add_three _ _ _
      _ ≤ b * b * (a + a) + b * a * (b + b) + a * b * (b + b) := by gcongr
      _ = 6 * a * b ^ 2 := by ring
  linarith [neg_abs_le (l2_d2f X Y)]

/-- **Eq. (7)** (`sv-eq7`). `(d²/dt²) F (A + t Y)|₀ ≥ (−c |A| + 4ε |A|²) |Y|²`, `c = 6`. -/
theorem l2_eq7 {ε k : ℝ} (hε : 0 ≤ ε) (hk : 0 ≤ k) (X Y : M32) :
    (-(6 * Real.sqrt (frobSq X)) + 4 * ε * frobSq X) * frobSq Y ≤ l2_D2 ε k X Y := by
  have h0 := l2_d2f_ge X Y
  have hY := l2_frobSq_nonneg Y
  have h1 : 0 ≤ 2 * ε * frobSq Y := by positivity
  have h2 : 0 ≤ 8 * ε * l2_inner X Y ^ 2 := by positivity
  have h3 : 0 ≤ 2 * k * frobSq (Y - sverakP Y) := by
    have := l2_frobSq_nonneg (Y - sverakP Y)
    positivity
  unfold l2_D2
  nlinarith

/-- **`(*)`**: `(d²/dt²) F (A + t Y)|₀ ≥ 0` when `|A| ≥ c / (4ε)`. -/
theorem l2_star {ε k : ℝ} (hε : 0 < ε) (hk : 0 ≤ k) (X Y : M32)
    (hX : 6 / (4 * ε) ≤ Real.sqrt (frobSq X)) : 0 ≤ l2_D2 ε k X Y := by
  refine le_trans ?_ (l2_eq7 hε.le hk X Y)
  have ha : 6 ≤ 4 * ε * Real.sqrt (frobSq X) := by
    rwa [div_le_iff₀ (by positivity), mul_comm] at hX
  have hsq := Real.sq_sqrt (l2_frobSq_nonneg X)
  have : 0 ≤ -(6 * Real.sqrt (frobSq X)) + 4 * ε * frobSq X := by
    set a := Real.sqrt (frobSq X)
    rw [← hsq]
    nlinarith [Real.sqrt_nonneg (frobSq X)]
  exact mul_nonneg this (l2_frobSq_nonneg Y)

/-! ### Rank one -/

/-- The `2 × 2` minors of a rank-one `3 × 2` matrix vanish. -/
theorem l2_minor_eq_zero {Y : M32} (hY : Y.rank = 1) (i₀ i₁ : Fin 3) :
    Y i₀ 0 * Y i₁ 1 - Y i₀ 1 * Y i₁ 0 = 0 := by
  by_contra h
  have := Y.rank_submatrix_le ![i₀, i₁] id
  rw [Matrix.rank_of_det_ne_zero (by rw [Matrix.det_fin_two]; simpa using h),
    Fintype.card_fin] at this
  omega

/-- `rank Y = 1` iff `Y ≠ 0` and the `2 × 2` minors of `Y` vanish (`rank Y ≤ 1`). -/
theorem l2_rank_eq_one_iff (Y : M32) :
    Y.rank = 1 ↔ (∀ i₀ i₁ : Fin 3, Y i₀ 0 * Y i₁ 1 - Y i₀ 1 * Y i₁ 0 = 0) ∧ Y ≠ 0 := by
  refine ⟨fun h => ⟨l2_minor_eq_zero h, ?_⟩, fun ⟨hm, hne⟩ => le_antisymm ?_ ?_⟩
  · rintro rfl
    rw [Matrix.rank_zero] at h
    exact zero_ne_one h
  · by_cases hc : ∃ i₀, Y i₀ 0 ≠ 0
    · obtain ⟨i₀, hi₀⟩ := hc
      have he : Y = Matrix.vecMulVec (fun i => Y i 0) ![1, Y i₀ 1 / Y i₀ 0] := by
        ext i j
        fin_cases j
        · simp [Matrix.vecMulVec]
        · have := hm i₀ i
          simp only [Matrix.vecMulVec, Matrix.of_apply]
          simp
          field_simp
          linarith
      rw [he]
      exact Matrix.rank_vecMulVec_le _ _
    · push Not at hc
      have he : Y = Matrix.vecMulVec (fun i => Y i 1) ![0, 1] := by
        ext i j
        fin_cases j <;> simp [Matrix.vecMulVec, hc]
      rw [he]
      exact Matrix.rank_vecMulVec_le _ _
  · obtain ⟨i, j, h⟩ : ∃ i j, Y i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Matrix.ext h)
    have := Y.rank_submatrix_le (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)
    rwa [Matrix.rank_of_det_ne_zero (by simpa [Matrix.det_unique] using h), Fintype.card_fin]
      at this

/-! ### Eq. (8) and the compactness argument -/

/-- **Eq. (8)** (`sv-eq8`). `(d²/dt²) F (A + t Y)|₀ ≥ g (A, Y, k)`. -/
theorem l2_eq8 {ε k : ℝ} (hε : 0 ≤ ε) (X Y : M32) : l2_g ε k X Y ≤ l2_D2 ε k X Y := by
  have h1 : 0 ≤ 4 * ε * frobSq X * frobSq Y := by
    have := l2_frobSq_nonneg X
    have := l2_frobSq_nonneg Y
    positivity
  have h2 : 0 ≤ 8 * ε * l2_inner X Y ^ 2 := by positivity
  unfold l2_g l2_D2
  linarith

/-- `g` is homogeneous of degree two in `Y`. -/
theorem l2_g_smul (ε k c : ℝ) (X Y : M32) : l2_g ε k X (c • Y) = c ^ 2 * l2_g ε k X Y := by
  simp only [l2_g, l2_d2f, l2_frobSq_sub_eq]
  simp only [l2_frobSq_eq, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The set `𝒦 = {(A, Y) : |A| ≤ c/(4ε), rank Y = 1, |Y| = 1}`, with `c = 6`. -/
def l2_K (ε : ℝ) : Set (M32 × M32) :=
  {p | Real.sqrt (frobSq p.1) ≤ 6 / (4 * ε) ∧ p.2.rank = 1 ∧ frobSq p.2 = 1}

/-- `𝒦` is compact: it is bounded, and closed since `rank ≤ 1` (vanishing `2 × 2` minors) is a
closed condition and `|Y| = 1` forces `rank Y ≥ 1`. -/
theorem l2_K_isCompact (ε : ℝ) : IsCompact (l2_K ε) := by
  set R := 6 / (4 * ε)
  have hK : l2_K ε = {p : M32 × M32 | Real.sqrt (frobSq p.1) ≤ R} ∩
      ((⋂ i₀ : Fin 3, ⋂ i₁ : Fin 3,
        {p : M32 × M32 | p.2 i₀ 0 * p.2 i₁ 1 - p.2 i₀ 1 * p.2 i₁ 0 = 0}) ∩
        {p : M32 × M32 | frobSq p.2 = 1}) := by
    ext ⟨A, Y⟩
    simp only [l2_K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, l2_rank_eq_one_iff]
    constructor
    · rintro ⟨h1, ⟨h2, -⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ⟨h2, ?_⟩, h3⟩
      rintro rfl
      simp [frobSq] at h3
  have hbox : IsCompact ((Set.Icc (-R) R).matrix ×ˢ (Set.Icc (-1 : ℝ) 1).matrix :
      Set (M32 × M32)) :=
    isCompact_Icc.matrix.prod isCompact_Icc.matrix
  refine hbox.of_isClosed_subset ?_ ?_
  · have c1 : Continuous fun p : M32 × M32 => Real.sqrt (frobSq p.1) := by
      unfold frobSq
      fun_prop
    have c2 : ∀ i₀ i₁ : Fin 3,
        Continuous fun p : M32 × M32 => p.2 i₀ 0 * p.2 i₁ 1 - p.2 i₀ 1 * p.2 i₁ 0 := by
      intro i₀ i₁
      fun_prop
    have c3 : Continuous fun p : M32 × M32 => frobSq p.2 := by
      unfold frobSq
      fun_prop
    rw [hK]
    exact (isClosed_le c1 continuous_const).inter
      ((isClosed_iInter fun i₀ => isClosed_iInter fun i₁ =>
        isClosed_eq (c2 i₀ i₁) continuous_const).inter (isClosed_eq c3 continuous_const))
  · rintro ⟨A, Y⟩ ⟨hA, -, hY⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact abs_le.1 ((l2_abs_le_sqrt A i j).trans hA)
    · have := l2_abs_le_sqrt Y i j
      rw [hY, Real.sqrt_one] at this
      exact abs_le.1 this

/-- The second derivative of `τ ↦ f (P X + τ Y)` at `0`, as a second difference (the function is
a cubic in `τ`). -/
theorem l2_d2f_eq_second_difference (X Y : M32) :
    l2_d2f X Y = sverakf (sverakP X + (1 : ℝ) • Y) + sverakf (sverakP X + (-1 : ℝ) • Y) -
      2 * sverakf (sverakP X + (0 : ℝ) • Y) := by
  simp only [l2_d2f, l2_sverakf_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp [sverakP]
  ring

/-- The claim of the proof: there is `k₀` (here `n + 1`, `n ∈ ℕ`) with `g (A, Y, k₀) > ε` on `𝒦`.
Otherwise there are `(A⁽ᵏ⁾, Y⁽ᵏ⁾) ∈ 𝒦` with `g (A⁽ᵏ⁾, Y⁽ᵏ⁾, k) ≤ ε`; a subsequence converges to
`(Ā, Ȳ) ∈ 𝒦` with `Ȳ = P Ȳ` and `(d²/dt²) f (P Ā + t P Ȳ)|₀ ≤ −ε`, while `f` is affine on the
rank-one line `P Ā + t Ȳ` of `L`. -/
theorem l2_claim {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, ∀ p ∈ l2_K ε, ε < l2_g ε (n + 1) p.1 p.2 := by
  have : FirstCountableTopology M32 :=
    inferInstanceAs (FirstCountableTopology (Fin 3 → Fin 2 → ℝ))
  by_contra hcon
  push Not at hcon
  choose p hpK hpg using hcon
  obtain ⟨⟨Ab, Yb⟩, hqK, φ, hφ, hlim⟩ := (l2_K_isCompact ε).tendsto_subseq hpK
  set R := 6 / (4 * ε)
  -- on `𝒦`, `(d²/dt²) f (P A + t P Y)|₀ ≥ −c R`
  have hlow : ∀ n, -(6 * R) ≤ l2_d2f (p n).1 (p n).2 := by
    intro n
    obtain ⟨hA, -, hY⟩ := hpK n
    have := l2_d2f_ge (p n).1 (p n).2
    rw [hY, mul_one] at this
    linarith
  -- hence `2 k |Y⁽ᵏ⁾ − P Y⁽ᵏ⁾|²` is bounded
  have hq : ∀ n : ℕ, frobSq ((p n).2 - sverakP (p n).2) ≤ 3 * R * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hg := hpg n
    obtain ⟨-, -, hY⟩ := hpK n
    unfold l2_g at hg
    rw [hY] at hg
    have := hlow n
    have hpos : (0 : ℝ) < n + 1 := by positivity
    rw [mul_one_div, le_div_iff₀ hpos]
    nlinarith
  have hd : ∀ n : ℕ, l2_d2f (p n).1 (p n).2 ≤ -ε := by
    intro n
    have hg := hpg n
    obtain ⟨-, -, hY⟩ := hpK n
    unfold l2_g at hg
    rw [hY] at hg
    have : 0 ≤ 2 * ((n : ℝ) + 1) * frobSq ((p n).2 - sverakP (p n).2) := by
      have := l2_frobSq_nonneg ((p n).2 - sverakP (p n).2)
      positivity
    linarith
  have hcontq : Continuous fun p : M32 × M32 => frobSq (p.2 - sverakP p.2) := by
    simp only [l2_frobSq_sub_eq]
    fun_prop
  have hcontd : Continuous fun p : M32 × M32 => l2_d2f p.1 p.2 := by
    unfold l2_d2f
    fun_prop
  -- `Ȳ = P Ȳ`
  have h0 : frobSq (Yb - sverakP Yb) = 0 := by
    have h1 : Tendsto (fun n => frobSq ((p n).2 - sverakP (p n).2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (3 * R)
      rw [mul_zero] at this
      exact squeeze_zero (fun n => l2_frobSq_nonneg _) hq this
    have h2 : Tendsto (fun n => frobSq ((p (φ n)).2 - sverakP (p (φ n)).2)) atTop
        (𝓝 (frobSq (Yb - sverakP Yb))) := (hcontq.tendsto (Ab, Yb)).comp hlim
    have h3 : Tendsto (fun n => frobSq ((p (φ n)).2 - sverakP (p (φ n)).2)) atTop (𝓝 0) :=
      h1.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h2 h3
  have hYb : Yb = sverakP Yb := sub_eq_zero.1 (l2_eq_zero_of_frobSq h0)
  have hYbL : Yb ∈ L := by
    rw [hYb]
    exact sverakP_mem _
  -- `(d²/dt²) f (P Ā + t P Ȳ)|₀ ≤ −ε`
  have hdq : l2_d2f Ab Yb ≤ -ε := by
    have h2 : Tendsto (fun n => l2_d2f (p (φ n)).1 (p (φ n)).2) atTop (𝓝 (l2_d2f Ab Yb)) :=
      (hcontd.tendsto (Ab, Yb)).comp hlim
    exact le_of_tendsto' h2 fun n => hd (φ n)
  -- but `f` is affine on the rank-one line `P Ā + τ Ȳ` of `L`
  obtain ⟨-, hrank, -⟩ := hqK
  obtain ⟨a, b, hab⟩ := sverakf_affine_of_rankOne (sverakP_mem Ab) hYbL hrank
  rw [l2_d2f_eq_second_difference, hab, hab, hab] at hdq
  linarith

/-- For `k = k₀`, `(d²/dt²) F (A + t Y)|₀ ≥ 0` for every `A` and every rank-one `Y`: by `(*)`
when `|A| ≥ c/(4ε)`, and otherwise by the claim and homogeneity in `Y`. -/
theorem l2_D2_nonneg {ε k : ℝ} (hε : 0 < ε) (hk : 0 ≤ k)
    (hK : ∀ p ∈ l2_K ε, ε < l2_g ε k p.1 p.2) {Y : M32} (hY : Y.rank = 1) (X : M32) :
    0 ≤ l2_D2 ε k X Y := by
  by_cases hX : 6 / (4 * ε) ≤ Real.sqrt (frobSq X)
  · exact l2_star hε hk X Y hX
  push Not at hX
  have hY0 : 0 < frobSq Y := by
    rcases (l2_frobSq_nonneg Y).lt_or_eq with h | h
    · exact h
    · rw [l2_eq_zero_of_frobSq h.symm, Matrix.rank_zero] at hY
      exact absurd hY zero_ne_one
  set c := 1 / Real.sqrt (frobSq Y)
  have hc0 : c ≠ 0 := by positivity
  have hc2 : c ^ 2 * frobSq Y = 1 := by
    rw [div_pow, one_pow, Real.sq_sqrt hY0.le]
    field_simp
  have hmem : (X, c • Y) ∈ l2_K ε := by
    refine ⟨hX.le, ?_, ?_⟩
    · rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc0)]
      exact hY
    · rw [l2_frobSq_smul]
      exact hc2
  have hg := hK _ hmem
  rw [l2_g_smul] at hg
  have hgpos : 0 < l2_g ε k X Y := by
    by_contra h
    push Not at h
    have : c ^ 2 * l2_g ε k X Y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h
    linarith
  exact hgpos.le.trans (l2_eq8 hε.le X Y)

/-- **Lemma 2** (`sv-lemma2`). Let `P` be the orthogonal projection onto `L` and `f` the function
`−r s t` on `L`. For each `ε > 0` there exists `k = k(ε) > 0` such that
`F (X) = f (P X) + ε |X|² + ε |X|⁴ + k |X − P X|²` is rank-one convex on `M^{3×2}`. -/
theorem lemma2 {ε : ℝ} (hε : 0 < ε) : ∃ k > 0, RankOneConvex (sverakF ε k) := by
  obtain ⟨n, hn⟩ := l2_claim hε
  refine ⟨n + 1, by positivity, fun A B hB => l2_convexOn_line _ _ A B fun t => ?_⟩
  exact l2_D2_nonneg hε (by positivity) hn hB (A + t • B)

end Sverak
