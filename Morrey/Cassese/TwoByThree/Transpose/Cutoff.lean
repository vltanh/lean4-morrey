module

public import Morrey.Cassese.TwoByThree.Transpose.Profile
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Corollary 5.3: the cut-off potentials

With `|z|² = z₀² + z₁²` (`tbt3Sq`), the cut-offs `χ_in (z) = σ (|z|² − 1)`, `χ_out (z) = σ (2 − |z|²)`
and `χ_mid (z) = σ (4 |z|² − 1)` (`σ = Real.smoothTransition`), the potential
`φ_R = χ_in · χ_out (·/R) · φ` (`tbt3PhiR`) agrees with `φ_in = χ_in φ` on `|z|² < R²`, with `φ` on
`2 < |z|² < R²`, and with `R^{5/2} φ_out (·/R)`, `φ_out = χ_mid χ_out φ`, on `|z|² > R²/2`
(for `R > 2`). All three are smooth, and `φ_R`, `φ_out` have compact support.

Helpers are prefixed `tbt3_`.
-/

@[expose] public section

open MeasureTheory MvPolynomial
open scoped Matrix

namespace Cassese

/-- `|z|² = z₀² + z₁²`. -/
def tbt3Sq (z : Fin 2 → ℝ) : ℝ := z 0 ^ 2 + z 1 ^ 2

theorem tbt3_continuous_Sq : Continuous tbt3Sq := by unfold tbt3Sq; fun_prop

theorem tbt3_contDiff_Sq : ContDiff ℝ tbt3Top tbt3Sq := by
  unfold tbt3Sq
  exact ((contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (0 : Fin 2)).pow 2).add
    ((contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (1 : Fin 2)).pow 2)

theorem tbt3_Sq_smul (a : ℝ) (z : Fin 2 → ℝ) : tbt3Sq (a • z) = a ^ 2 * tbt3Sq z := by
  simp [tbt3Sq]; ring

theorem tbt3_Sq_nonneg (z : Fin 2 → ℝ) : 0 ≤ tbt3Sq z := by unfold tbt3Sq; positivity

/-- `χ_in (z) = σ (|z|² − 1)`: `0` on `|z|² ≤ 1`, `1` on `|z|² ≥ 2`. -/
noncomputable def tbt3ChiIn (z : Fin 2 → ℝ) : ℝ := Real.smoothTransition (tbt3Sq z - 1)

/-- `χ_out (z) = σ (2 − |z|²)`: `1` on `|z|² ≤ 1`, `0` on `|z|² ≥ 2`. -/
noncomputable def tbt3ChiOut (z : Fin 2 → ℝ) : ℝ := Real.smoothTransition (2 - tbt3Sq z)

/-- `χ_mid (z) = σ (4 |z|² − 1)`: `0` on `|z|² ≤ 1/4`, `1` on `|z|² ≥ 1/2`. -/
noncomputable def tbt3ChiMid (z : Fin 2 → ℝ) : ℝ := Real.smoothTransition (4 * tbt3Sq z - 1)

/-- `φ_R = χ_in · χ_out (·/R) · φ`. -/
noncomputable def tbt3PhiR (R : ℝ) (z : Fin 2 → ℝ) : ℝ :=
  tbt3ChiIn z * tbt3ChiOut (R⁻¹ • z) * tbt3Phi z

/-- `φ_in = χ_in · φ`. -/
noncomputable def tbt3PhiIn (z : Fin 2 → ℝ) : ℝ := tbt3ChiIn z * tbt3Phi z

/-- `φ_out = χ_mid · χ_out · φ`. -/
noncomputable def tbt3PhiOut (z : Fin 2 → ℝ) : ℝ := tbt3ChiMid z * tbt3ChiOut z * tbt3Phi z

theorem tbt3_Phi_eq (z : Fin 2 → ℝ) :
    tbt3Phi z = (z 0 ^ 3 - 3 * z 0 * z 1 ^ 2) * tbt3Sq z ^ (-1 / 4 : ℝ) := by
  simp [tbt3Phi, tbt3F, tbt3P0, tbt3S, tbt3Sq]

theorem tbt3_contDiffAt_Phi {z : Fin 2 → ℝ} (hz : 0 < tbt3Sq z) :
    ContDiffAt ℝ tbt3Top tbt3Phi z := by
  have e : tbt3Phi = fun z => (z 0 ^ 3 - 3 * z 0 * z 1 ^ 2) * tbt3Sq z ^ (-1 / 4 : ℝ) :=
    funext tbt3_Phi_eq
  rw [e]
  have h0 := contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (n := tbt3Top) (0 : Fin 2)
  have h1 := contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) (n := tbt3Top) (1 : Fin 2)
  have hp : ContDiff ℝ tbt3Top fun z : Fin 2 → ℝ => z 0 ^ 3 - 3 * z 0 * z 1 ^ 2 :=
    (h0.pow 3).sub ((contDiff_const.mul h0).mul (h1.pow 2))
  exact hp.contDiffAt.mul (tbt3_contDiff_Sq.contDiffAt.rpow_const_of_ne hz.ne')

/-- A smooth multiple of `φ` that vanishes near the origin is smooth. -/
theorem tbt3_contDiff_mul_Phi {g : (Fin 2 → ℝ) → ℝ} (hg : ContDiff ℝ tbt3Top g) {ε : ℝ}
    (hε : 0 < ε) (h0 : ∀ z, tbt3Sq z < ε → g z = 0) :
    ContDiff ℝ tbt3Top fun z => g z * tbt3Phi z := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases (tbt3_Sq_nonneg z).lt_or_eq with hz | hz
  · exact hg.contDiffAt.mul (tbt3_contDiffAt_Phi hz)
  · have hU : {w | tbt3Sq w < ε} ∈ nhds z :=
      (isOpen_lt tbt3_continuous_Sq continuous_const).mem_nhds (by simp [← hz, hε])
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hU] with w hw
    simp [h0 w hw]

theorem tbt3_contDiff_chiIn : ContDiff ℝ tbt3Top tbt3ChiIn :=
  Real.smoothTransition.contDiff.comp (tbt3_contDiff_Sq.sub contDiff_const)

theorem tbt3_contDiff_chiOut : ContDiff ℝ tbt3Top tbt3ChiOut :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub tbt3_contDiff_Sq)

theorem tbt3_contDiff_chiMid : ContDiff ℝ tbt3Top tbt3ChiMid :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul tbt3_contDiff_Sq).sub contDiff_const)

theorem tbt3_chiIn_zero {z : Fin 2 → ℝ} (h : tbt3Sq z < 1) : tbt3ChiIn z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem tbt3_chiIn_one {z : Fin 2 → ℝ} (h : 2 ≤ tbt3Sq z) : tbt3ChiIn z = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem tbt3_chiOut_one {z : Fin 2 → ℝ} (h : tbt3Sq z ≤ 1) : tbt3ChiOut z = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem tbt3_chiOut_zero {z : Fin 2 → ℝ} (h : 2 ≤ tbt3Sq z) : tbt3ChiOut z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem tbt3_chiMid_zero {z : Fin 2 → ℝ} (h : tbt3Sq z < 1 / 4) : tbt3ChiMid z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem tbt3_chiMid_one {z : Fin 2 → ℝ} (h : 1 / 2 ≤ tbt3Sq z) : tbt3ChiMid z = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem tbt3_contDiff_PhiR (R : ℝ) : ContDiff ℝ tbt3Top (tbt3PhiR R) := by
  have := tbt3_contDiff_mul_Phi (g := fun z => tbt3ChiIn z * tbt3ChiOut (R⁻¹ • z))
    (tbt3_contDiff_chiIn.mul (tbt3_contDiff_chiOut.comp (contDiff_const_smul _)))
    one_pos (fun z hz => by simp [tbt3_chiIn_zero hz])
  exact this

theorem tbt3_contDiff_PhiIn : ContDiff ℝ tbt3Top tbt3PhiIn :=
  tbt3_contDiff_mul_Phi tbt3_contDiff_chiIn one_pos (fun _ hz => tbt3_chiIn_zero hz)

theorem tbt3_contDiff_PhiOut : ContDiff ℝ tbt3Top tbt3PhiOut :=
  tbt3_contDiff_mul_Phi (g := fun z => tbt3ChiMid z * tbt3ChiOut z)
    (tbt3_contDiff_chiMid.mul tbt3_contDiff_chiOut) (by norm_num : (0 : ℝ) < 1 / 4)
    (fun _ hz => by simp [tbt3_chiMid_zero hz])

/-- `φ (z) = R^{5/2} φ (z / R)` for `R > 0`. -/
theorem tbt3_Phi_scale {R : ℝ} (hR : 0 < R) (z : Fin 2 → ℝ) :
    tbt3Phi z = R ^ (5 / 2 : ℝ) * tbt3Phi (R⁻¹ • z) := by
  rw [tbt3_Phi_eq, tbt3_Phi_eq, tbt3_Sq_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Real.mul_rpow (by positivity) (tbt3_Sq_nonneg z)]
  have h1 : (R⁻¹ ^ 2) ^ (-1 / 4 : ℝ) = R ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.inv_rpow hR.le,
      ← Real.rpow_neg hR.le]
    norm_num
  rw [h1]
  have h2 : R ^ (5 / 2 : ℝ) = R ^ 3 * R ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]; norm_num
  have h3 : R ^ (-1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hR]; norm_num
  rw [h2]
  have hRi : R * R⁻¹ = 1 := mul_inv_cancel₀ hR.ne'
  generalize tbt3Sq z ^ (-1 / 4 : ℝ) = w
  generalize R ^ (-1 / 2 : ℝ) = a at h3 ⊢
  generalize R ^ (1 / 2 : ℝ) = b at h3 ⊢
  linear_combination (-(z 0 ^ 3 - 3 * z 0 * z 1 ^ 2) * w * a * b *
    ((R * R⁻¹) ^ 2 + R * R⁻¹ + 1)) * hRi + (-(z 0 ^ 3 - 3 * z 0 * z 1 ^ 2) * w) * h3

theorem tbt3_isOpen_Sq_lt (c : ℝ) : IsOpen {z : Fin 2 → ℝ | tbt3Sq z < c} :=
  isOpen_lt tbt3_continuous_Sq continuous_const

theorem tbt3_isOpen_lt_Sq (c : ℝ) : IsOpen {z : Fin 2 → ℝ | c < tbt3Sq z} :=
  isOpen_lt continuous_const tbt3_continuous_Sq

/-- On `|z|² < R²`, `φ_R = φ_in`. -/
theorem tbt3_PhiR_eq_in {R : ℝ} (hR : 0 < R) :
    Set.EqOn (tbt3PhiR R) tbt3PhiIn {z | tbt3Sq z < R ^ 2} := by
  intro z hz
  have : tbt3Sq (R⁻¹ • z) ≤ 1 := by
    rw [tbt3_Sq_smul]
    simp only [Set.mem_ofPred_eq] at hz
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]; linarith
  simp [tbt3PhiR, tbt3PhiIn, tbt3_chiOut_one this]

/-- On `2 < |z|² < R²`, `φ_R = φ`. -/
theorem tbt3_PhiR_eq_bulk {R : ℝ} (hR : 0 < R) :
    Set.EqOn (tbt3PhiR R) tbt3Phi {z | 2 < tbt3Sq z ∧ tbt3Sq z < R ^ 2} := by
  intro z hz
  rw [tbt3_PhiR_eq_in hR hz.2]
  simp [tbt3PhiIn, tbt3_chiIn_one hz.1.le]

/-- On `|z|² > R²/2`, `φ_R = R^{5/2} φ_out (·/R)` (for `R² > 4`). -/
theorem tbt3_PhiR_eq_out {R : ℝ} (hR : 0 < R) (hR4 : 4 < R ^ 2) :
    Set.EqOn (tbt3PhiR R) (fun z => R ^ (5 / 2 : ℝ) * tbt3PhiOut (R⁻¹ • z))
      {z | R ^ 2 / 2 < tbt3Sq z} := by
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  have h1 : tbt3ChiIn z = 1 := tbt3_chiIn_one (by linarith)
  have h2 : tbt3ChiMid (R⁻¹ • z) = 1 := by
    apply tbt3_chiMid_one
    rw [tbt3_Sq_smul, inv_pow, le_inv_mul_iff₀ (by positivity)]; linarith
  simp only [tbt3PhiR, tbt3PhiOut, h1, h2, one_mul]
  rw [tbt3_Phi_scale hR z]; ring

/-- `φ_R` vanishes on `|z|² ≥ 2R²`. -/
theorem tbt3_PhiR_zero {R : ℝ} (hR : 0 < R) {z : Fin 2 → ℝ} (hz : 2 * R ^ 2 ≤ tbt3Sq z) :
    tbt3PhiR R z = 0 := by
  have : tbt3ChiOut (R⁻¹ • z) = 0 := by
    apply tbt3_chiOut_zero
    rw [tbt3_Sq_smul, inv_pow, le_inv_mul_iff₀ (by positivity)]; linarith
  simp [tbt3PhiR, this]

theorem tbt3_PhiOut_zero {z : Fin 2 → ℝ} (hz : 2 ≤ tbt3Sq z) : tbt3PhiOut z = 0 := by
  simp [tbt3PhiOut, tbt3_chiOut_zero hz]

/-- A function vanishing on `|z|² ≥ ρ` has compact support. -/
theorem tbt3_hasCompactSupport_of_Sq {E : Type*} [NormedAddCommGroup E] {f : (Fin 2 → ℝ) → E}
    {ρ : ℝ} (h : ∀ z, ρ ≤ tbt3Sq z → f z = 0) : HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) (√|ρ| + 1)) fun z hz => ?_
  apply h
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  obtain ⟨i, hi⟩ : ∃ i, √|ρ| + 1 < |z i| := by
    by_contra hc
    push Not at hc
    have : ‖z‖ ≤ √|ρ| + 1 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      rw [Real.norm_eq_abs]; exact hc i
    linarith
  have h1 : (√|ρ|) ^ 2 < z i ^ 2 := by
    have : √|ρ| < |z i| := by linarith
    rw [← sq_abs (z i)]; exact pow_lt_pow_left₀ this (Real.sqrt_nonneg _) (by norm_num)
  rw [Real.sq_sqrt (abs_nonneg ρ)] at h1
  have : z i ^ 2 ≤ tbt3Sq z := by
    fin_cases i <;> simp [tbt3Sq] <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  linarith [le_abs_self ρ]

end Cassese
