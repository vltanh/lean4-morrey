module

public import Morrey.Cassese.TwoByThree.Folklore.Laminate
public import Morrey.Cassese.TwoByThree.Folklore.Quasiaffine
public import Morrey.Cassese.TwoByThree.ExtensionAux
public import Morrey.Common.External.Dacorogna.Minors
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Section 5: Proposition 5.1, polynomials of degree at most three

"Interestingly, among polynomials, degree four is minimal" (TeX lines 1396–1414): a polynomial of
degree at most `3` that is rank-one convex at `0` is quasiconvex.

The pieces: `Folklore/Laminate.lean` (finite prelaminates and the limiting argument),
`Folklore/NullLagrangian.lean` and `Folklore/Quasiaffine.lean` (`3 × 3` minors are quasiaffine).

Helpers are prefixed `tbt6_`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace Cassese

variable {d m : ℕ}

/-- `A ↦ P (A)` for a polynomial `P` in the entries. -/
noncomputable def tbt6Ev (P : MvPolynomial (Fin d × Fin m) ℝ) (A : Matrix (Fin d) (Fin m) ℝ) : ℝ :=
  MvPolynomial.eval (fun ij => A ij.1 ij.2) P

theorem tbt6_continuous_ev (P : MvPolynomial (Fin d × Fin m) ℝ) : Continuous (tbt6Ev P) := by
  unfold tbt6Ev
  simp_rw [MvPolynomial.eval_eq']
  refine continuous_finsetSum _ fun s _ => continuous_const.mul ?_
  refine continuous_finsetProd _ fun ij _ => ?_
  exact (((continuous_apply ij.2).comp (continuous_apply ij.1))).pow _

/-- A homogeneous polynomial of degree `n` scales by `s^n`. -/
theorem tbt6_ev_smul {P : MvPolynomial (Fin d × Fin m) ℝ} {n : ℕ} (hP : P.IsHomogeneous n)
    (s : ℝ) (A : Matrix (Fin d) (Fin m) ℝ) : tbt6Ev P (s • A) = s ^ n * tbt6Ev P A := by
  simp only [tbt6Ev, MvPolynomial.eval_eq', Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : ∑ ij, e ij = n := by
    have := hP (MvPolynomial.mem_support_iff.mp he)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simpa using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- A homogeneous polynomial of degree `1` is linear: `P (A) = Σ c_{ij} A_{ij}`. -/
theorem tbt6_ev_deg1 {P : MvPolynomial (Fin d × Fin m) ℝ} (hP : P.IsHomogeneous 1)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    tbt6Ev P A = ∑ ij, A ij.1 ij.2 * (MvPolynomial.pderiv ij P).coeff 0 := by
  have hE := congrArg (MvPolynomial.eval fun ij : Fin d × Fin m => A ij.1 ij.2)
    hP.sum_X_mul_pderiv
  simp only [map_sum, map_mul, MvPolynomial.eval_X, one_smul] at hE
  rw [tbt6Ev, ← hE]
  refine Finset.sum_congr rfl fun ij _ => ?_
  have h0 := (hP.pderiv (i := ij))
  rw [show (1 : ℕ) - 1 = 0 by rfl, ← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
  rw [h0]
  simp [MvPolynomial.coeff_C]

/-- A homogeneous polynomial of degree `2` is a quadratic form:
`P (A) = ½ Σ_{ij,kl} c_{ij,kl} A_{ij} A_{kl}` (Euler's identity twice). -/
theorem tbt6_ev_deg2 {P : MvPolynomial (Fin d × Fin m) ℝ} (hP : P.IsHomogeneous 2)
    (A : Matrix (Fin d) (Fin m) ℝ) :
    tbt6Ev P A = 1 / 2 * ∑ ij : Fin d × Fin m, A ij.1 ij.2 *
      ∑ kl : Fin d × Fin m, A kl.1 kl.2 *
        (MvPolynomial.pderiv kl (MvPolynomial.pderiv ij P)).coeff 0 := by
  have hE := congrArg (MvPolynomial.eval fun ij : Fin d × Fin m => A ij.1 ij.2)
    hP.sum_X_mul_pderiv
  simp only [map_sum, map_mul, MvPolynomial.eval_X, nsmul_eq_mul, map_natCast] at hE
  have h1 : ∀ ij : Fin d × Fin m, (MvPolynomial.eval fun ij => A ij.1 ij.2)
      (MvPolynomial.pderiv ij P) = ∑ kl : Fin d × Fin m, A kl.1 kl.2 *
        (MvPolynomial.pderiv kl (MvPolynomial.pderiv ij P)).coeff 0 := fun ij =>
    tbt6_ev_deg1 (hP.pderiv (i := ij)) A
  simp_rw [h1] at hE
  rw [tbt6Ev]
  push_cast at hE
  linear_combination (-1 / 2 : ℝ) * hE

/-- The bilinear form `B (X, Y) = ½ Σ c_{ij,kl} X_{ij} Y_{kl}`. -/
noncomputable def tbt6Bil (c : Fin d × Fin m → Fin d × Fin m → ℝ) :
    LinearMap.BilinForm ℝ (Matrix (Fin d) (Fin m) ℝ) :=
  LinearMap.mk₂ ℝ (fun X Y => ∑ ij : Fin d × Fin m, ∑ kl : Fin d × Fin m,
      1 / 2 * c ij kl * X ij.1 ij.2 * Y kl.1 kl.2)
    (fun X X' Y => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun kl _ => ?_
      simp only [Matrix.add_apply]; ring)
    (fun a X Y => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun kl _ => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]; ring)
    (fun X Y Y' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun kl _ => ?_
      simp only [Matrix.add_apply]; ring)
    (fun a X Y => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun kl _ => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]; ring)

theorem tbt6_bil_apply (c : Fin d × Fin m → Fin d × Fin m → ℝ) (X Y : Matrix (Fin d) (Fin m) ℝ) :
    tbt6Bil c X Y = ∑ ij : Fin d × Fin m, ∑ kl : Fin d × Fin m,
      1 / 2 * c ij kl * X ij.1 ij.2 * Y kl.1 kl.2 := rfl

/-- **`Q` is rank-one affine**: `t ↦ f₃ (A + t B)` is midpoint affine (`tbt6_sym`) and continuous. -/
theorem tbt6_rankOneAffine {f₃ : Matrix (Fin d) (Fin m) ℝ → ℝ} (hc : Continuous f₃)
    (hsym : ∀ (A R : Matrix (Fin d) (Fin m) ℝ), R.rank = 1 → ∀ h : ℝ,
      f₃ (A + h • R) + f₃ (A - h • R) = 2 * f₃ A) :
    CalculusOfVariations.RankOneAffine f₃ := by
  have hmid : ∀ (A B : Matrix (Fin d) (Fin m) ℝ), B.rank = 1 → ∀ x h : ℝ,
      f₃ (A + (x + h) • B) + f₃ (A + (x - h) • B) = 2 * f₃ (A + x • B) := by
    intro A B hB x h
    rw [← hsym (A + x • B) B hB h]
    congr 1 <;> congr 1 <;> module
  refine ⟨fun A B hB => ?_, fun A B hB => ?_⟩
  · refine tbt2_convexOn_of_midpoint (hc.comp (by fun_prop)) fun x h => ?_
    linarith [hmid A B hB x h]
  · refine tbt2_convexOn_of_midpoint ((hc.comp (by fun_prop)).neg) fun x h => ?_
    simp only [Pi.neg_apply]
    linarith [hmid A B hB x h]

theorem tbt6_minor_smul {k : ℕ} (A : Matrix (Fin d) (Fin m) ℝ) (r : Fin k ↪o Fin d)
    (c : Fin k ↪o Fin m) (s : ℝ) :
    External.Dacorogna.minor (s • A) r c = s ^ k * External.Dacorogna.minor A r c := by
  have : (s • A).submatrix r c = s • A.submatrix r c := by ext; simp
  rw [External.Dacorogna.minor, External.Dacorogna.minor, this, Matrix.det_smul, Fintype.card_fin]

theorem tbt6_continuous_minor {k : ℕ} (r : Fin k ↪o Fin d) (c : Fin k ↪o Fin m) :
    Continuous fun A : Matrix (Fin d) (Fin m) ℝ => External.Dacorogna.minor A r c :=
  (continuous_id.matrix_submatrix r c).matrix_det

/-- A cubic form that is an affine combination of minors is a combination of the `3 × 3` minors:
the minors of order `k ≠ 3` cancel by homogeneity. -/
theorem tbt6_minors_extract {N : ℕ} {f₃ : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (h3 : ∀ (s : ℝ) X, f₃ (s • X) = s ^ 3 * f₃ X)
    (a : (k : ℕ) → (Fin k ↪o Fin d) → (Fin k ↪o Fin m) → ℝ)
    (ha : ∀ A, f₃ A = ∑ k ∈ Finset.range N, ∑ r, ∑ c, a k r c * External.Dacorogna.minor A r c)
    (k : ℕ) (hk : k ∈ Finset.range N) (hk3 : k ≠ 3) (A : Matrix (Fin d) (Fin m) ℝ) :
    ∑ r, ∑ c, a k r c * External.Dacorogna.minor A r c = 0 := by
  set cf : ℕ → ℝ := fun k => ∑ r, ∑ c, a k r c * External.Dacorogna.minor A r c
  set p : Polynomial ℝ := ∑ k ∈ Finset.range N, Polynomial.C (cf k) * Polynomial.X ^ k -
    Polynomial.C (f₃ A) * Polynomial.X ^ 3
  have key : ∀ s : ℝ, ∑ k ∈ Finset.range N, cf k * s ^ k = f₃ A * s ^ 3 := by
    intro s
    have := ha (s • A)
    rw [h3] at this
    simp only [tbt6_minor_smul] at this
    rw [mul_comm, this, Finset.sum_congr rfl fun k _ => ?_]
    simp only [cf, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  have hp : p = 0 := by
    apply Polynomial.funext
    intro s
    simp only [p, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [key, sub_self]
  have := congrArg (fun q : Polynomial ℝ => q.coeff k) hp
  simp only [p, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero, hk3, ↓reduceIte, sub_zero] at this
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (fun h => absurd hk h)] at this
  simpa using this

/-- **Proposition 5.1** (`cs-prop5.1`): a polynomial `P : ℝ^{d×m} → ℝ` of degree at most `3` that
is rank-one convex at `0` is quasiconvex. The proof uses Dacorogna's Theorem 5.20 (rank-one
affine functions are affine combinations of minors), which is proved in the project
(`External.Dacorogna.rankOneAffineMinors_holds`), so the statement has no hypothesis.

Proof, after the paper (TeX lines 1402–1414). Write `P = P₀ + P₁ + P₂ + P₃` (homogeneous parts,
`Q = P₃`). By the envelope formula (Proposition 2.1), `P (0) ≤ ∫ P dμ` for every prelaminate `μ`
centred at `0` (`tbt6_jensen`); applied to the dilations of a fixed laminate this gives
`0 ≤ s ∫ P₁ + s² ∫ P₂ + s³ ∫ P₃` for all `s ≠ 0`, hence `∫ Q dμ = 0` and `∫ P₂ dμ ≥ 0` (the
"limiting argument", `tbt6_list_cubic`): `P₂` satisfies the Legendre–Hadamard condition
(`tbt6_LH`), and `Q` is rank-one affine (`tbt6_sym`, `tbt6_rankOneAffine`). By Dacorogna's
Theorem 5.20 (`External.Dacorogna.rankOneAffineMinors_holds`), `Q` is an affine combination of
minors, and homogeneity leaves only the
`3 × 3` minors (`tbt6_minors_extract`). The quadratic form `P₂` is rank-one convex, hence
quasiconvex (Dacorogna, Theorem 5.25 (i), `External.Dacorogna.quadraticForm_quasiconvex`);
`P₁` is linear (`∫ ∇φ = 0`); and the `3 × 3` minors are quasiaffine (`tbt6_minor3_quasiaffine`).
So `∫ P (A + ∇φ) ≥ P (A)`.

Departure from the paper. Inventory E9: "`Q` is rank-one affine at `0`. It follows that `Q`
is rank-one affine" skips an argument; it is supplied by a prelaminate centred at `0` with an atom
at an arbitrary `A` (symmetric splittings along the rank-one pieces of `A`), split once more along
`±h R`, so that `Q (A + h R) + Q (A − h R) = 2 Q (A)` (reason 1, a repair). The paper's "`P − Q`
is rank-one convex, since `P'' (0) = (P − Q)'' (0)`" is obtained in the same way, as the
Legendre–Hadamard condition for `P₂`.

Not a departure: the paper concludes from "`Q` is a linear combination of minors" that `P` is
quasiconvex, which uses that the `3 × 3` minors are quasiaffine (null Lagrangians). Dacorogna's
Theorem 5.20, which the paper cites at this step, is the full equivalence "quasiaffine ⇔ rank-one
affine ⇔ affine combination of minors"; the proposition `External.Dacorogna.RankOneAffineMinors`
records only the direction "rank-one affine ⇒ affine combination of minors", and the direction
"minors ⇒ quasiaffine" of the same cited theorem is proved here, by the standard divergence
identities and mollification (`tbt6_minor3_quasiaffine`,
`Morrey/Cassese/TwoByThree/Folklore/NullLagrangian.lean`). This proves part of the cited result;
the argument of the proposition is the paper's. -/
theorem proposition5_1
    (P : MvPolynomial (Fin d × Fin m) ℝ) (hP : P.totalDegree ≤ 3)
    (hrc : RankOneConvexAt (fun A => MvPolynomial.eval (fun ij => A ij.1 ij.2) P) 0) :
    Quasiconvex fun A : Matrix (Fin d) (Fin m) ℝ =>
      MvPolynomial.eval (fun ij => A ij.1 ij.2) P := by
  set f := tbt6Ev P with hfdef
  set fk : ℕ → Matrix (Fin d) (Fin m) ℝ → ℝ :=
    fun k => tbt6Ev (MvPolynomial.homogeneousComponent k P) with hfk
  have hhom : ∀ k (s : ℝ) X, fk k (s • X) = s ^ k * fk k X := fun k s X =>
    tbt6_ev_smul (MvPolynomial.homogeneousComponent_isHomogeneous k P) s X
  have hcont : ∀ k, Continuous (fk k) := fun k => tbt6_continuous_ev _
  have hf : Continuous f := tbt6_continuous_ev P
  -- `P = P₀ + P₁ + P₂ + P₃`
  have hsumP : ∑ k ∈ Finset.range 4, MvPolynomial.homogeneousComponent k P = P := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : P.totalDegree + 1 ≤ 4))
      (fun k _ hk => MvPolynomial.homogeneousComponent_eq_zero k P (by
        rw [Finset.mem_range] at hk; omega)), MvPolynomial.sum_homogeneousComponent]
  have hsum : ∀ X, f X = fk 0 X + fk 1 X + fk 2 X + fk 3 X := by
    intro X
    simp only [hfdef, hfk, tbt6Ev]
    conv_lhs => rw [← hsumP]
    simp [Finset.sum_range_succ]
  have h0 : ∀ (s : ℝ) X, fk 0 (s • X) = fk 0 X := fun s X => by rw [hhom, pow_zero, one_mul]
  have h1 : ∀ (s : ℝ) X, fk 1 (s • X) = s * fk 1 X := fun s X => by rw [hhom, pow_one]
  -- Legendre–Hadamard and rank-one affinity
  have hLH : ∀ R : Matrix (Fin d) (Fin m) ℝ, R.rank = 1 → 0 ≤ fk 2 R := fun R hR =>
    tbt6_LH hf hrc hsum h0 h1 (hhom 2) (hhom 3) hR
  have hRA : CalculusOfVariations.RankOneAffine (fk 3) :=
    tbt6_rankOneAffine (hcont 3) fun A R hR h =>
      tbt6_sym hf hrc hsum h0 h1 (hhom 2) (hhom 3) A hR h
  obtain ⟨a, ha⟩ := External.Dacorogna.rankOneAffineMinors_holds d m (fk 3) (hcont 3) hRA
  -- the quadratic part is a quasiconvex quadratic form
  set c : Fin d × Fin m → Fin d × Fin m → ℝ := fun ij kl =>
    (MvPolynomial.pderiv kl (MvPolynomial.pderiv ij
      (MvPolynomial.homogeneousComponent 2 P))).coeff 0
  have hB : ∀ X, tbt6Bil c X X = fk 2 X := by
    intro X
    show _ = tbt6Ev (MvPolynomial.homogeneousComponent 2 P) X
    rw [tbt6_bil_apply, tbt6_ev_deg2 (MvPolynomial.homogeneousComponent_isHomogeneous 2 P),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun kl _ => ?_
    ring
  have hBrc : CalculusOfVariations.RankOneConvex fun A => tbt6Bil c A A := by
    intro A R hR
    have e : (fun t : ℝ => tbt6Bil c (A + t • R) (A + t • R)) = fun t =>
        tbt6Bil c R R * t ^ 2 + (tbt6Bil c A R + tbt6Bil c R A) * t + tbt6Bil c A A := by
      funext t
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact tbt_convexOn_quadratic (by rw [hB]; exact hLH R hR)
  have hBqc : Quasiconvex fun A => tbt6Bil c A A :=
    (cov_quasiconvex_iff _).mp (External.Dacorogna.quadraticForm_quasiconvex _ hBrc)
  -- quasiconvexity at every `A`
  intro A φ K hφ hφ0 _
  have hcube : volume (unitCube m) = 1 := volume_unitCube m
  have hcube' : volume (unitCube m) ≠ ⊤ := by rw [hcube]; simp
  have hI : ∀ k, IntegrableOn (fun x => fk k (A + jac φ x)) (unitCube m) := fun k =>
    tbt6_integrableOn_cube hφ (hcont k) A _ hcube'
  -- the constant part
  have e0 : ∫ x in unitCube m, fk 0 (A + jac φ x) = fk 0 A := by
    have : ∀ X, fk 0 X = fk 0 A := fun X => by rw [← h0 0 X, ← h0 0 A, zero_smul, zero_smul]
    simp_rw [this]
    rw [setIntegral_const, Measure.real, hcube]; simp
  -- the linear part
  have e1 : ∫ x in unitCube m, fk 1 (A + jac φ x) = fk 1 A := by
    have hlin : ∀ X, fk 1 X = ∑ ij : Fin d × Fin m, X ij.1 ij.2 *
        (MvPolynomial.pderiv ij (MvPolynomial.homogeneousComponent 1 P)).coeff 0 := fun X =>
      tbt6_ev_deg1 (MvPolynomial.homogeneousComponent_isHomogeneous 1 P) X
    have hJ : ∫ x in unitCube m, fk 1 (jac φ x) = 0 := by
      rw [tbt6_setIntegral_cube_of_zero hφ0 (by rw [hlin]; simp)]
      simp_rw [hlin]
      rw [integral_finsetSum _ fun ij _ => (tbt6_integrable_of_zero hφ hφ0
        (Φ := fun J => J ij.1 ij.2 * (MvPolynomial.pderiv ij
          (MvPolynomial.homogeneousComponent 1 P)).coeff 0) (by fun_prop) (by simp))]
      refine Finset.sum_eq_zero fun ij _ => ?_
      rw [integral_mul_const, tbt6_integral_jac hφ hφ0, zero_mul]
    have hsplit : ∀ x, fk 1 (A + jac φ x) = fk 1 A + fk 1 (jac φ x) := by
      intro x; simp only [hlin, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    simp_rw [hsplit]
    have hI1 := tbt6_integrableOn_cube hφ (hcont 1) 0 _ hcube'
    simp only [zero_add] at hI1
    rw [integral_add (integrableOn_const hcube' enorm_ne_top) hI1, hJ,
      setIntegral_const, Measure.real, hcube]
    simp
  -- the quadratic part
  have e2 : fk 2 A ≤ ∫ x in unitCube m, fk 2 (A + jac φ x) := by
    have := hBqc A φ K hφ hφ0 (by simp_rw [hB]; exact hI 2)
    simp_rw [hB] at this
    exact this
  -- the cubic part
  have e3 : ∫ x in unitCube m, fk 3 (A + jac φ x) = fk 3 A := by
    have hint : ∀ k : ℕ, IntegrableOn (fun x => ∑ r, ∑ c, a k r c *
        External.Dacorogna.minor (A + jac φ x) r c) (unitCube m) := fun k =>
      tbt6_integrableOn_cube hφ (Φ := fun J => ∑ r, ∑ c, a k r c *
        External.Dacorogna.minor J r c)
        (continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun c _ =>
          continuous_const.mul (tbt6_continuous_minor r c)) A _ hcube'
    simp_rw [ha]
    rw [integral_finsetSum _ fun k _ => hint k]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases eq_or_ne k 3 with rfl | hk3
    · rw [integral_finsetSum _ fun r _ => ?_]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [integral_finsetSum _ fun c _ => ?_]
        · refine Finset.sum_congr rfl fun c _ => ?_
          rw [integral_const_mul, tbt6_minor3_quasiaffine hφ hφ0 A r c]
        · exact (tbt6_integrableOn_cube hφ (tbt6_continuous_minor r c) A _
            hcube').const_mul _
      · exact tbt6_integrableOn_cube hφ (Φ := fun J => ∑ c, a 3 r c *
          External.Dacorogna.minor J r c)
          (continuous_finsetSum _ fun c _ => continuous_const.mul (tbt6_continuous_minor r c))
          A _ hcube'
    · simp_rw [tbt6_minors_extract (hhom 3) a ha k hk hk3]
      simp
  -- conclusion
  have hsplit : ∀ x, f (A + jac φ x) =
      fk 0 (A + jac φ x) + fk 1 (A + jac φ x) + fk 2 (A + jac φ x) + fk 3 (A + jac φ x) :=
    fun x => hsum _
  show f A ≤ ∫ x in unitCube m, f (A + jac φ x)
  simp_rw [hsplit]
  rw [integral_add (f := fun x => fk 0 (A + jac φ x) + fk 1 (A + jac φ x) + fk 2 (A + jac φ x))
      (((hI 0).add (hI 1)).add (hI 2)) (hI 3),
    integral_add (f := fun x => fk 0 (A + jac φ x) + fk 1 (A + jac φ x))
      ((hI 0).add (hI 1)) (hI 2), integral_add (hI 0) (hI 1), e0, e1, e3, hsum A]
  linarith

end Cassese
