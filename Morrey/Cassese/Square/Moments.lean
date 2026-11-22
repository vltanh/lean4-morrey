module

public import Morrey.Cassese.Defs
public import Morrey.Sverak.Cube
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Trigonometric moments on the unit cube

The integrals that Proposition 6.6 needs: on the unit cube `(0, 1)^n` (the torus `𝕋^n` with its
probability measure, the angles being `θ_k = 2π y_k`), with `θ_k` independent and uniform,

* for a continuous `g` with `∫₀¹ g = 0`, `∫₀¹ g² = a`, `∫₀¹ g⁴ = b`, the sum `S = Σ_k g (y_k)` has
  `E S = 0`, `E S² = n a` and `E S⁴ = n b + 3 n (n − 1) a²` (`square_moments_sum`);
* the planar random walk `W = Σ_k e^{2 i θ_k}`, `P = Re W`, `Q = Im W`, has `E |W|² = n` and
  `E |W|⁴ = 2 n² − n` (`square_moments_walk`).

Both are proved by induction on `n`, integrating out one coordinate at a time
(`square_integral_cube_succ`, Fubini on `(0, 1)^{n+1} = (0, 1) × (0, 1)^n`).
-/

@[expose] public section

open MeasureTheory Real

namespace Cassese

/-- The Lebesgue measure on the unit cube is the product of the Lebesgue measures on `(0, 1)`. -/
theorem square_restrict_unitCube (n : ℕ) :
    volume.restrict (unitCube n) =
      Measure.pi fun _ : Fin n => volume.restrict (Set.Ioo (0:ℝ) 1) := by
  rw [unitCube, volume_pi, Measure.restrict_pi_pi]

/-- A continuous function is integrable on the unit cube. -/
theorem square_integrableOn_cube {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Continuous F) :
    IntegrableOn F (unitCube n) :=
  Sverak.gen_integrableOn_unitCube hF

/-- Fubini on `(0, 1)^{n+1} = (0, 1) × (0, 1)^n`, separating the coordinate `i`, inner integral over
the separated coordinate. -/
theorem square_integral_cube_succ {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ} (hF : Continuous F)
    (i : Fin (n + 1)) :
    ∫ x in unitCube (n + 1), F x =
      ∫ y in unitCube n, ∫ t in Set.Ioo (0:ℝ) 1, F (i.insertNth t y) := by
  set ν := volume.restrict (Set.Ioo (0:ℝ) 1)
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i).symm
  have hint : Integrable F (Measure.pi fun _ : Fin (n + 1) => ν) := by
    rw [← square_restrict_unitCube]; exact square_integrableOn_cube hF
  have hint' := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hint
  rw [square_restrict_unitCube, square_restrict_unitCube, ← hmp.integral_comp']
  exact integral_prod_symm _ hint'

/-- Fubini on `(0, 1)^{n+1} = (0, 1) × (0, 1)^n`, separating the coordinate `i`, outer integral over
the separated coordinate. -/
theorem square_integral_cube_succ' {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ} (hF : Continuous F)
    (i : Fin (n + 1)) :
    ∫ x in unitCube (n + 1), F x =
      ∫ t in Set.Ioo (0:ℝ) 1, ∫ y in unitCube n, F (i.insertNth t y) := by
  set ν := volume.restrict (Set.Ioo (0:ℝ) 1)
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i).symm
  have hint : Integrable F (Measure.pi fun _ : Fin (n + 1) => ν) := by
    rw [← square_restrict_unitCube]; exact square_integrableOn_cube hF
  have hint' := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hint
  rw [square_restrict_unitCube, square_restrict_unitCube, ← hmp.integral_comp']
  exact integral_prod _ hint'

theorem square_volume_unitCube (n : ℕ) : volume.real (unitCube n) = 1 := by
  show (volume (Sverak.unitCube n)).toReal = 1
  rw [Sverak.volume_unitCube, ENNReal.toReal_one]

/-- The integral of a constant over the unit cube. -/
theorem square_integral_cube_const (n : ℕ) (c : ℝ) : ∫ _ in unitCube n, c = c := by
  rw [setIntegral_const, square_volume_unitCube, one_smul]

theorem square_integral_Ioo_const (c : ℝ) : ∫ _ in Set.Ioo (0:ℝ) 1, c = c := by
  rw [setIntegral_const]; simp

theorem square_integrableOn_Ioo {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f (Set.Ioo (0:ℝ) 1) :=
  (hf.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self

theorem square_integral_Ioo_eq (f : ℝ → ℝ) :
    ∫ t in Set.Ioo (0:ℝ) 1, f t = ∫ t in (0:ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- `∫₀¹ cos (2π k t + φ) dt = 0` for a nonzero integer `k`. -/
theorem square_integral_cos {k : ℤ} (hk : k ≠ 0) (φ : ℝ) :
    ∫ t in Set.Ioo (0:ℝ) 1, cos (2 * π * k * t + φ) = 0 := by
  rw [square_integral_Ioo_eq]
  have hc : (2 * π * k : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) (Int.cast_ne_zero.2 hk)
  rw [intervalIntegral.integral_comp_mul_add (fun x => cos x) hc φ, integral_cos]
  rw [show 2 * π * k * 1 + φ = φ + k * (2 * π) by ring, sin_add_int_mul_two_pi]
  simp

/-- `∫₀¹ sin (2π k t + φ) dt = 0` for a nonzero integer `k`. -/
theorem square_integral_sin {k : ℤ} (hk : k ≠ 0) (φ : ℝ) :
    ∫ t in Set.Ioo (0:ℝ) 1, sin (2 * π * k * t + φ) = 0 := by
  have h := square_integral_cos hk (φ - π / 2)
  simpa [show ∀ t : ℝ, 2 * π * k * t + (φ - π / 2) = 2 * π * k * t + φ - π / 2 from
    fun t => by ring, cos_sub_pi_div_two] using h

/-! ### Sums of independent coordinates -/

/-- The integral over `t` of a quartic polynomial in `g t` with constant coefficients. -/
theorem square_integral_quartic {g : ℝ → ℝ} (hg : Continuous g) (c0 c1 c2 c3 c4 : ℝ) :
    ∫ t in Set.Ioo (0:ℝ) 1, (c0 + c1 * g t + c2 * g t ^ 2 + c3 * g t ^ 3 + c4 * g t ^ 4) =
      c0 + c1 * (∫ t in Set.Ioo (0:ℝ) 1, g t) + c2 * (∫ t in Set.Ioo (0:ℝ) 1, g t ^ 2) +
        c3 * (∫ t in Set.Ioo (0:ℝ) 1, g t ^ 3) + c4 * ∫ t in Set.Ioo (0:ℝ) 1, g t ^ 4 := by
  rw [integral_add, integral_add, integral_add, integral_add, square_integral_Ioo_const,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  all_goals exact square_integrableOn_Ioo (by fun_prop)

/-- The integral over the cube of a quartic polynomial in `S y` with constant coefficients. -/
theorem square_integral_cube_quartic {n : ℕ} {S : (Fin n → ℝ) → ℝ} (hS : Continuous S)
    (c0 c1 c2 c3 c4 : ℝ) :
    ∫ y in unitCube n, (c0 + c1 * S y + c2 * S y ^ 2 + c3 * S y ^ 3 + c4 * S y ^ 4) =
      c0 + c1 * (∫ y in unitCube n, S y) + c2 * (∫ y in unitCube n, S y ^ 2) +
        c3 * (∫ y in unitCube n, S y ^ 3) + c4 * ∫ y in unitCube n, S y ^ 4 := by
  rw [integral_add, integral_add, integral_add, integral_add, square_integral_cube_const,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  all_goals exact square_integrableOn_cube (by fun_prop)

/-- **Moments of a sum of independent coordinates.** For a continuous `g` with `∫₀¹ g = 0`,
`∫₀¹ g² = a` and `∫₀¹ g⁴ = b`, the sum `S (y) = Σ_k g (y_k)` on `(0, 1)^n` has `E S = 0`,
`E S² = n a` and `E S⁴ = n b + 3 n (n − 1) a²`. -/
theorem square_moments_sum {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    (h1 : ∫ t in Set.Ioo (0:ℝ) 1, g t = 0) (h2 : ∫ t in Set.Ioo (0:ℝ) 1, g t ^ 2 = a)
    (h4 : ∫ t in Set.Ioo (0:ℝ) 1, g t ^ 4 = b) (n : ℕ) :
    ∫ y in unitCube n, (∑ k, g (y k)) = 0 ∧
      ∫ y in unitCube n, (∑ k, g (y k)) ^ 2 = n * a ∧
      ∫ y in unitCube n, (∑ k, g (y k)) ^ 4 = n * b + 3 * n * (n - 1) * a ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨e1, e2, e4⟩ := ih
    set c3 := ∫ t in Set.Ioo (0:ℝ) 1, g t ^ 3
    set S : (Fin n → ℝ) → ℝ := fun y => ∑ k, g (y k) with hSdef
    have hS : Continuous S := by fun_prop
    have hsplit : ∀ (y : Fin n → ℝ) (t : ℝ),
        ∑ k, g ((Fin.insertNth 0 t y : Fin (n + 1) → ℝ) k) = g t + S y := by
      intro y t
      rw [Fin.sum_univ_succAbove _ 0, Fin.insertNth_apply_same]
      try simp only [Fin.insertNth_apply_succAbove, hSdef]
    have hc : ∀ m : ℕ, Continuous fun x : Fin (n + 1) → ℝ => (∑ k, g (x k)) ^ m := fun m => by
      fun_prop
    have hq := fun y => square_integral_quartic hg (S y) 1 0 0 0
    have hq2 := fun y => square_integral_quartic hg (S y ^ 2) (2 * S y) 1 0 0
    have hq4 := fun y => square_integral_quartic hg (S y ^ 4) (4 * S y ^ 3) (6 * S y ^ 2)
      (4 * S y) 1
    simp only [h1, h2, h4] at hq hq2 hq4
    have hQ2 := square_integral_cube_quartic hS a 0 1 0 0
    have hQ4 := square_integral_cube_quartic hS b (4 * c3) (6 * a) 0 1
    rw [e1, e2] at hQ2
    rw [e1, e2, e4] at hQ4
    refine ⟨?_, ?_, ?_⟩
    · have h := square_integral_cube_succ (by simpa using hc 1) 0
      rw [h]
      simp_rw [hsplit]
      calc ∫ y in unitCube n, ∫ t in Set.Ioo (0:ℝ) 1, (g t + S y)
          = ∫ y in unitCube n, ∫ t in Set.Ioo (0:ℝ) 1,
              (S y + 1 * g t + 0 * g t ^ 2 + 0 * g t ^ 3 + 0 * g t ^ 4) := by
            congr 1; funext y; congr 1; funext t; ring
        _ = ∫ y in unitCube n, S y := by
            congr 1; funext y; rw [hq y]; ring
        _ = 0 := e1
    · rw [square_integral_cube_succ (hc 2) 0]
      simp_rw [hsplit]
      calc ∫ y in unitCube n, ∫ t in Set.Ioo (0:ℝ) 1, (g t + S y) ^ 2
          = ∫ y in unitCube n, ∫ t in Set.Ioo (0:ℝ) 1,
              (S y ^ 2 + 2 * S y * g t + 1 * g t ^ 2 + 0 * g t ^ 3 + 0 * g t ^ 4) := by
            congr 1; funext y; congr 1; funext t; ring
        _ = ∫ y in unitCube n, (a + 0 * S y + 1 * S y ^ 2 + 0 * S y ^ 3 + 0 * S y ^ 4) := by
            congr 1; funext y; rw [hq2 y]; ring
        _ = ((n + 1 : ℕ) : ℝ) * a := by rw [hQ2]; push_cast; ring
    · rw [square_integral_cube_succ (hc 4) 0]
      simp_rw [hsplit]
      calc ∫ y in unitCube n, ∫ t in Set.Ioo (0:ℝ) 1, (g t + S y) ^ 4
          = ∫ y in unitCube n, ∫ t in Set.Ioo (0:ℝ) 1,
              (S y ^ 4 + 4 * S y ^ 3 * g t + 6 * S y ^ 2 * g t ^ 2 + 4 * S y * g t ^ 3 +
                1 * g t ^ 4) := by
            congr 1; funext y; congr 1; funext t; ring
        _ = ∫ y in unitCube n,
              (b + 4 * c3 * S y + 6 * a * S y ^ 2 + 0 * S y ^ 3 + 1 * S y ^ 4) := by
            congr 1; funext y; rw [hq4 y]; ring
        _ = ((n + 1 : ℕ) : ℝ) * b + 3 * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) * a ^ 2 := by
            rw [hQ4]; push_cast; ring

/-! ### One-dimensional trigonometric integrals -/

theorem square_integral_cos_of {k : ℤ} (hk : k ≠ 0) (φ : ℝ) {f : ℝ → ℝ}
    (hf : ∀ t, f t = 2 * π * k * t + φ) : ∫ t in Set.Ioo (0:ℝ) 1, cos (f t) = 0 := by
  simp_rw [hf]; exact square_integral_cos hk φ

theorem square_integral_sin_of {k : ℤ} (hk : k ≠ 0) (φ : ℝ) {f : ℝ → ℝ}
    (hf : ∀ t, f t = 2 * π * k * t + φ) : ∫ t in Set.Ioo (0:ℝ) 1, sin (f t) = 0 := by
  simp_rw [hf]; exact square_integral_sin hk φ

/-- `∫₀¹ (α + β c + γ s + δ c² + ε c s + ζ s²) dt = α + δ / 2 + ζ / 2` for `c = cos 4πt`,
`s = sin 4πt`. -/
theorem square_integral_trig_quadratic (α β γ δ ε ζ : ℝ) :
    ∫ t in Set.Ioo (0:ℝ) 1, (α + β * cos (4 * π * t) + γ * sin (4 * π * t) +
      δ * cos (4 * π * t) ^ 2 + ε * (cos (4 * π * t) * sin (4 * π * t)) +
      ζ * sin (4 * π * t) ^ 2) = α + δ / 2 + ζ / 2 := by
  have hpt : ∀ t : ℝ, α + β * cos (4 * π * t) + γ * sin (4 * π * t) +
      δ * cos (4 * π * t) ^ 2 + ε * (cos (4 * π * t) * sin (4 * π * t)) +
      ζ * sin (4 * π * t) ^ 2 = (α + δ / 2 + ζ / 2) + β * cos (4 * π * t) +
      γ * sin (4 * π * t) + (δ - ζ) / 2 * cos (8 * π * t) + ε / 2 * sin (8 * π * t) := by
    intro t
    have h8 : 8 * π * t = 2 * (4 * π * t) := by ring
    rw [h8, cos_two_mul, sin_two_mul]
    have := sin_sq_add_cos_sq (4 * π * t)
    linear_combination ζ * this
  simp_rw [hpt]
  rw [integral_add, integral_add, integral_add, integral_add, square_integral_Ioo_const,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    square_integral_cos_of (k := 2) (by norm_num) 0 (fun t => by push_cast; ring),
    square_integral_sin_of (k := 2) (by norm_num) 0 (fun t => by push_cast; ring),
    square_integral_cos_of (k := 4) (by norm_num) 0 (fun t => by push_cast; ring),
    square_integral_sin_of (k := 4) (by norm_num) 0 (fun t => by push_cast; ring)]
  · ring
  all_goals exact square_integrableOn_Ioo (by fun_prop)

/-- For `g (s) = sin (2π (c − s))`: `∫₀¹ g = 0`. -/
theorem square_integral_sin_shift (c : ℝ) :
    ∫ s in Set.Ioo (0:ℝ) 1, sin (2 * π * (c - s)) = 0 :=
  square_integral_sin_of (k := -1) (by norm_num) (2 * π * c) (fun t => by push_cast; ring)

/-- For `g (s) = sin (2π (c − s))`: `∫₀¹ g² = 1/2`. -/
theorem square_integral_sin_shift_sq (c : ℝ) :
    ∫ s in Set.Ioo (0:ℝ) 1, sin (2 * π * (c - s)) ^ 2 = 1 / 2 := by
  have hpt : ∀ s : ℝ, sin (2 * π * (c - s)) ^ 2 = 1 / 2 - 1 / 2 * cos (2 * (2 * π * (c - s))) := by
    intro s
    rw [cos_two_mul]
    have := sin_sq_add_cos_sq (2 * π * (c - s))
    linear_combination this
  simp_rw [hpt]
  rw [integral_sub, square_integral_Ioo_const, integral_const_mul,
    square_integral_cos_of (k := -2) (by norm_num) (4 * π * c) (fun t => by push_cast; ring)]
  · ring
  all_goals exact square_integrableOn_Ioo (by fun_prop)

/-- For `g (s) = sin (2π (c − s))`: `∫₀¹ g⁴ = 3/8`. -/
theorem square_integral_sin_shift_pow_four (c : ℝ) :
    ∫ s in Set.Ioo (0:ℝ) 1, sin (2 * π * (c - s)) ^ 4 = 3 / 8 := by
  have hpt : ∀ s : ℝ, sin (2 * π * (c - s)) ^ 4 = 3 / 8 -
      1 / 2 * cos (2 * (2 * π * (c - s))) + 1 / 8 * cos (2 * (2 * (2 * π * (c - s)))) := by
    intro s
    rw [cos_two_mul (2 * (2 * π * (c - s))), cos_two_mul]
    have := sin_sq_add_cos_sq (2 * π * (c - s))
    have h2 : cos (2 * π * (c - s)) ^ 2 = 1 - sin (2 * π * (c - s)) ^ 2 := by linarith
    rw [h2]; ring
  simp_rw [hpt]
  rw [integral_add, integral_sub, square_integral_Ioo_const, integral_const_mul,
    integral_const_mul,
    square_integral_cos_of (k := -2) (by norm_num) (4 * π * c) (fun t => by push_cast; ring),
    square_integral_cos_of (k := -4) (by norm_num) (8 * π * c) (fun t => by push_cast; ring)]
  · ring
  all_goals exact square_integrableOn_Ioo (by fun_prop)

/-! ### The planar random walk -/

/-- **Moments of the planar random walk** `W = Σ_k e^{2 i θ_k}` (`θ_k = 2π y_k`):
`E |W|² = n` and `E |W|⁴ = 2 n² − n`, with `|W|² = P² + Q²`, `P = Σ cos 2θ_k`, `Q = Σ sin 2θ_k`. -/
theorem square_moments_walk (n : ℕ) :
    ∫ y in unitCube n, ((∑ k, cos (4 * π * y k)) ^ 2 + (∑ k, sin (4 * π * y k)) ^ 2) = n ∧
      ∫ y in unitCube n, ((∑ k, cos (4 * π * y k)) ^ 2 + (∑ k, sin (4 * π * y k)) ^ 2) ^ 2 =
        2 * n ^ 2 - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨e2, e4⟩ := ih
    set P : (Fin n → ℝ) → ℝ := fun y => ∑ k, cos (4 * π * y k) with hP
    set Q : (Fin n → ℝ) → ℝ := fun y => ∑ k, sin (4 * π * y k) with hQ
    set R : (Fin n → ℝ) → ℝ := fun y => P y ^ 2 + Q y ^ 2 with hR
    have hRc : Continuous R := by simp only [hR, hP, hQ]; fun_prop
    have hsplitP : ∀ (y : Fin n → ℝ) (t : ℝ),
        ∑ k, cos (4 * π * (Fin.insertNth 0 t y : Fin (n + 1) → ℝ) k) =
          cos (4 * π * t) + P y := by
      intro y t
      rw [Fin.sum_univ_succAbove _ 0, Fin.insertNth_apply_same]
      try simp only [Fin.insertNth_apply_succAbove, hP]
    have hsplitQ : ∀ (y : Fin n → ℝ) (t : ℝ),
        ∑ k, sin (4 * π * (Fin.insertNth 0 t y : Fin (n + 1) → ℝ) k) =
          sin (4 * π * t) + Q y := by
      intro y t
      rw [Fin.sum_univ_succAbove _ 0, Fin.insertNth_apply_same]
      try simp only [Fin.insertNth_apply_succAbove, hQ]
    have hpt : ∀ (y : Fin n → ℝ) (t : ℝ), (cos (4 * π * t) + P y) ^ 2 +
        (sin (4 * π * t) + Q y) ^ 2 =
        R y + 1 + 2 * P y * cos (4 * π * t) + 2 * Q y * sin (4 * π * t) := by
      intro y t
      have := sin_sq_add_cos_sq (4 * π * t)
      simp only [hR]
      linear_combination this
    have hQ4 := square_integral_cube_quartic hRc 1 4 1 0 0
    have hQ2 := square_integral_cube_quartic hRc 1 1 0 0 0
    rw [e2, e4] at hQ4
    rw [e2] at hQ2
    refine ⟨?_, ?_⟩
    · rw [square_integral_cube_succ (by fun_prop) 0]
      simp_rw [hsplitP, hsplitQ, hpt]
      calc ∫ y in unitCube n, ∫ t in Set.Ioo (0:ℝ) 1,
            (R y + 1 + 2 * P y * cos (4 * π * t) + 2 * Q y * sin (4 * π * t))
          = ∫ y in unitCube n, (1 + 1 * R y + 0 * R y ^ 2 + 0 * R y ^ 3 + 0 * R y ^ 4) := by
            congr 1; funext y
            have := square_integral_trig_quadratic (R y + 1) (2 * P y) (2 * Q y) 0 0 0
            simp only [zero_mul, add_zero] at this
            rw [this]; ring
        _ = ((n + 1 : ℕ) : ℝ) := by rw [hQ2]; push_cast; ring
    · rw [square_integral_cube_succ (by fun_prop) 0]
      simp_rw [hsplitP, hsplitQ, hpt]
      calc ∫ y in unitCube n, ∫ t in Set.Ioo (0:ℝ) 1,
            (R y + 1 + 2 * P y * cos (4 * π * t) + 2 * Q y * sin (4 * π * t)) ^ 2
          = ∫ y in unitCube n, (1 + 4 * R y + 1 * R y ^ 2 + 0 * R y ^ 3 + 0 * R y ^ 4) := by
            congr 1; funext y
            have := square_integral_trig_quadratic ((R y + 1) ^ 2) (4 * (R y + 1) * P y)
              (4 * (R y + 1) * Q y) (4 * P y ^ 2) (8 * P y * Q y) (4 * Q y ^ 2)
            rw [show (fun t => (R y + 1 + 2 * P y * cos (4 * π * t) +
                2 * Q y * sin (4 * π * t)) ^ 2) = fun t => (R y + 1) ^ 2 +
                4 * (R y + 1) * P y * cos (4 * π * t) + 4 * (R y + 1) * Q y * sin (4 * π * t) +
                4 * P y ^ 2 * cos (4 * π * t) ^ 2 +
                8 * P y * Q y * (cos (4 * π * t) * sin (4 * π * t)) +
                4 * Q y ^ 2 * sin (4 * π * t) ^ 2 from funext fun t => by ring, this]
            simp only [hR]; ring
        _ = 2 * ((n + 1 : ℕ) : ℝ) ^ 2 - ((n + 1 : ℕ) : ℝ) := by rw [hQ4]; push_cast; ring

end Cassese
