module

public import Morrey.Cassese.Toolkit
public import Morrey.Sverak.Lemma1
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Periodic test maps for Hessian quasiconvexity

The second-order analogue of the periodic characterization of quasiconvexity (Lemma 2.2;
Šverák's Lemma 1, `Sverak.lemma1_witness`): a smooth `ℤ^n`-periodic `φ : ℝ^n → ℝ` with
`∫_{(0,1)^n} F (A + D²φ) < F (A)`, for a continuous `F`, witnesses that `F` is not Hessian
quasiconvex at `A` (`square_not_hessianQuasiconvexAt_of_periodic`).

The test maps are `ψ_K (x) = N_K⁻² η_K (x) φ (N_K x)`, with Šverák's cutoff `η_K = l1_eta n K`
(equal to `1` on `[1/K, 1 − 1/K]^n`, vanishing off `(1/(2K), 1 − 1/(2K))^n`) and an oscillation
`N_K = K + a_K + b_K`, where `a_K`, `b_K` bound `‖D η_K‖` and `‖D² η_K‖`. By Leibniz's rule
(`norm_iteratedFDeriv_mul_le`),
`‖D² ψ_K‖ ≤ ‖D²φ‖_∞ + 2 (a_K / N_K) ‖Dφ‖_∞ + (b_K / N_K²) ‖φ‖_∞ ≤ ‖D²φ‖_∞ + 2 ‖Dφ‖_∞ + ‖φ‖_∞`
uniformly in `K ≥ 1`; on `(1/K, 1 − 1/K)^n`, `D² ψ_K (x) = D²φ (N_K x)`. Dominated convergence
and the averaging limit `Sverak.l1_tendsto_setIntegral_comp_smul` then give
`∫ F (A + D² ψ_K) → ∫ F (A + D²φ)` as `K → ∞`.

Helpers have the prefix `square_hess_`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace Cassese

variable {n : ℕ}

theorem square_hess_two_le_top : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  simp

theorem square_hess_nat_le_top (k : ℕ) : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- The Hessian is the second iterated derivative: `D²φ (x)_{ij} = D²φ (x) (e_i, e_j)`. -/
theorem square_hess_hessian_apply {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (x : Fin n → ℝ)
    (i j : Fin n) :
    hessian φ x i j = iteratedFDeriv ℝ 2 φ x ![Pi.single i 1, Pi.single j 1] := by
  rw [iteratedFDeriv_two_apply]
  simp only [hessian, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply (u := fun _ => (Pi.single j 1 : Fin n → ℝ)) hd
    (differentiableAt_const _)]
  simp

/-- An entry of the Hessian is bounded by the norm of the second derivative. -/
theorem square_hess_abs_hessian_le {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (x : Fin n → ℝ)
    (i j : Fin n) : |hessian φ x i j| ≤ ‖iteratedFDeriv ℝ 2 φ x‖ := by
  rw [square_hess_hessian_apply hφ, ← Real.norm_eq_abs]
  refine ((iteratedFDeriv ℝ 2 φ x).le_opNorm _).trans ?_
  have h1 : ∀ k : Fin n, ‖(Pi.single k (1:ℝ) : Fin n → ℝ)‖ ≤ 1 := fun k => by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
    by_cases h : l = k
    · subst h; simp
    · simp [h]
  have hp : ∏ k : Fin 2, ‖(![Pi.single i 1, Pi.single j 1] : Fin 2 → Fin n → ℝ) k‖ ≤ 1 := by
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    calc ‖(Pi.single i 1 : Fin n → ℝ)‖ * ‖(Pi.single j 1 : Fin n → ℝ)‖ ≤ 1 * 1 :=
          mul_le_mul (h1 i) (h1 j) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc _ ≤ ‖iteratedFDeriv ℝ 2 φ x‖ * 1 :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = _ := mul_one _

/-- The Hessian of a smooth map is continuous. -/
theorem square_hess_continuous_hessian {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : Continuous (hessian φ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [hessian, Matrix.of_apply]
  have hj : ContDiff ℝ 1 fun y => fderiv ℝ φ y (Pi.single j 1) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact (hj.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The Hessian only depends on the germ of the map. -/
theorem square_hess_hessian_congr {ψ ψ' : (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψ' : ContDiff ℝ 2 ψ') {x : Fin n → ℝ} (h : ψ =ᶠ[𝓝 x] ψ') : hessian ψ x = hessian ψ' x := by
  ext i j
  rw [square_hess_hessian_apply hψ, square_hess_hessian_apply hψ',
    (h.iteratedFDeriv ℝ 2).eq_of_nhds]

/-- The iterated derivatives of a periodic map are periodic. -/
theorem square_hess_iteratedFDeriv_periodic {φ : (Fin n → ℝ) → ℝ}
    (hper : ∀ (x : Fin n → ℝ) (z : Fin n → ℤ), φ (x + fun i => (z i : ℝ)) = φ x) (k : ℕ)
    (x : Fin n → ℝ) (z : Fin n → ℤ) :
    iteratedFDeriv ℝ k φ (x + fun i => (z i : ℝ)) = iteratedFDeriv ℝ k φ x := by
  rw [← iteratedFDeriv_comp_add_right]
  congr 1
  funext y
  exact hper y z

/-- The Hessian of a periodic map is periodic. -/
theorem square_hess_hessian_periodic {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hper : ∀ (x : Fin n → ℝ) (z : Fin n → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (x : Fin n → ℝ) (z : Fin n → ℤ) : hessian φ (x + fun i => (z i : ℝ)) = hessian φ x := by
  ext i j
  rw [square_hess_hessian_apply hφ, square_hess_hessian_apply hφ,
    square_hess_iteratedFDeriv_periodic hper]

/-- The iterated derivatives of `z ↦ c φ (N z)`. -/
theorem square_hess_iteratedFDeriv_scale {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (c N : ℝ) (k : ℕ) (y : Fin n → ℝ) :
    iteratedFDeriv ℝ k (fun z => c * φ (N • z)) y =
      c • (iteratedFDeriv ℝ k φ (N • y)).compContinuousLinearMap
        fun _ => N • ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  set L := N • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hk := square_hess_nat_le_top k
  have e : (fun z => c * φ (N • z)) = fun z => c • (φ ∘ L) z := by
    funext z; simp [L, smul_eq_mul]
  rw [e, iteratedFDeriv_const_smul_apply' ((hφ.comp L.contDiff).of_le hk).contDiffAt,
    L.iteratedFDeriv_comp_right hφ y hk]
  simp [L]

/-- `‖D^k (c φ (N ·)) (y)‖ ≤ |c| |N|^k ‖D^k φ (N y)‖`. -/
theorem square_hess_norm_scale_le {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (c N : ℝ) (k : ℕ) (y : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ k (fun z => c * φ (N • z)) y‖ ≤
      |c| * |N| ^ k * ‖iteratedFDeriv ℝ k φ (N • y)‖ := by
  rw [square_hess_iteratedFDeriv_scale hφ, norm_smul, Real.norm_eq_abs]
  have hL : ‖N • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤ |N| := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]
    calc |N| * ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤ |N| * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)
      _ = |N| := mul_one _
  have hc := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k φ (N • y)) fun _ : Fin k => N • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  have hp : ‖N • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ^ k ≤ |N| ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) hL k
  calc |c| * ‖(iteratedFDeriv ℝ k φ (N • y)).compContinuousLinearMap
        fun _ => N • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖
      ≤ |c| * (‖iteratedFDeriv ℝ k φ (N • y)‖ * |N| ^ k) :=
        mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _)))
          (abs_nonneg _)
    _ = _ := by ring

/-- `D² (N⁻² φ (N ·)) (x) = D²φ (N x)`. -/
theorem square_hess_hessian_scale {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {N : ℝ} (hN : N ≠ 0) (x : Fin n → ℝ) :
    hessian (fun z => (N ^ 2)⁻¹ * φ (N • z)) x = hessian φ (N • x) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le square_hess_two_le_top
  have hg2 : ContDiff ℝ 2 fun z => (N ^ 2)⁻¹ * φ (N • z) :=
    contDiff_const.mul (hφ2.comp (contDiff_const_smul N))
  ext i j
  rw [square_hess_hessian_apply hg2, square_hess_hessian_apply hφ2,
    square_hess_iteratedFDeriv_scale hφ, smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [smul_apply, ContinuousLinearMap.id_apply]
  have h := (iteratedFDeriv ℝ 2 φ (N • x)).map_smul_univ (fun _ => N)
    (![Pi.single i 1, Pi.single j 1] : Fin 2 → Fin n → ℝ)
  rw [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, smul_eq_mul]
  field_simp

/-- Leibniz's rule for the second derivative of a product. -/
theorem square_hess_norm_iteratedFDeriv_two_mul_le {η g : (Fin n → ℝ) → ℝ}
    (hη : ContDiff ℝ 2 η) (hg : ContDiff ℝ 2 g) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ 2 (fun y => η y * g y) x‖ ≤
      ‖η x‖ * ‖iteratedFDeriv ℝ 2 g x‖ + 2 * ‖fderiv ℝ η x‖ * ‖fderiv ℝ g x‖ +
        ‖iteratedFDeriv ℝ 2 η x‖ * ‖g x‖ := by
  have h := norm_iteratedFDeriv_mul_le hη hg x (n := 2) le_rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.choose_self, norm_iteratedFDeriv_zero, Nat.cast_one, one_mul,
    Nat.sub_zero] at h
  have e : (2 - 1 : ℕ) = 1 := rfl
  rw [e, norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at h
  rw [show (2 - 2 : ℕ) = 0 from rfl, norm_iteratedFDeriv_zero] at h
  push_cast at h
  linarith

/-- Šverák's cutoff `η_K` has compact support. -/
theorem square_hess_eta_hasCompactSupport {K : ℝ} (hK : 0 < K) :
    HasCompactSupport (Sverak.l1_eta n K) := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun _ =>
    isCompact_Icc (a := 1 / (2 * K)) (b := 1 - 1 / (2 * K))) fun x hx => ?_
  exact Sverak.l1_eta_eq_zero hK fun h => hx fun i _ => ⟨(h i).1.le, (h i).2.le⟩

/-- The derivatives of `η_K` are bounded. -/
theorem square_hess_eta_bound {K : ℝ} (hK : 0 < K) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ k (Sverak.l1_eta n K) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((Sverak.l1_eta_contDiff n K).continuous_iteratedFDeriv
    (square_hess_nat_le_top k)).bounded_above_of_compact_support
      ((square_hess_eta_hasCompactSupport hK).iteratedFDeriv k)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- **Periodic test maps for Hessian quasiconvexity** (`cs-hess-periodic`): a smooth
`ℤ^n`-periodic `φ` with `∫_{(0,1)^n} F (A + D²φ) < F (A)`, for a continuous `F`, witnesses that
`F` is not Hessian quasiconvex at `A`.

Proof: the test maps `ψ_K (x) = N_K⁻² η_K (x) φ (N_K x)`, with Šverák's cutoff
`η_K = Sverak.l1_eta n K` and `N_K = K + a_K + b_K` (`a_K`, `b_K` bounds for `‖D η_K‖`,
`‖D² η_K‖`), are smooth with compact support in `(0, 1)^n`; by Leibniz's rule their Hessians are
bounded uniformly in `K ≥ 1`, and `D² ψ_K (x) = D²φ (N_K x)` on `(1/K, 1 − 1/K)^n`. By dominated
convergence `∫ F (A + D² ψ_K) − ∫ F (A + D²φ (N_K x)) dx → 0`, and by periodicity
`∫ F (A + D²φ (N_K x)) dx → ∫ F (A + D²φ)` (`Sverak.l1_tendsto_setIntegral_comp_smul`). So
`∫ F (A + D² ψ_K) < F (A)` for some `K`, against Hessian quasiconvexity. -/
theorem square_not_hessianQuasiconvexAt_of_periodic {n : ℕ} {F : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hF : Continuous F) {A : Matrix (Fin n) (Fin n) ℝ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hper : ∀ (x : Fin n → ℝ) (z : Fin n → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (hlt : ∫ x in unitCube n, F (A + hessian φ x) < F A) :
    ¬ HessianQuasiconvexAt F A := by
  intro hqc
  have hle2 := square_hess_two_le_top
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le hle2
  -- `‖D^k φ‖ ≤ Φ k`, by periodicity
  have hbφ : ∀ k : ℕ, ∃ C, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ k φ x‖ ≤ C := fun k =>
    Sverak.l1_periodic_bounded (hφ.continuous_iteratedFDeriv (square_hess_nat_le_top k))
      fun x z => square_hess_iteratedFDeriv_periodic hper k x z
  choose Φ hΦ0 hΦ using hbφ
  set R := Φ 2 + 2 * Φ 1 + Φ 0 with hR
  -- `‖D η_K‖ ≤ a K` and `‖D² η_K‖ ≤ b K`
  have hbη : ∀ K : ℝ, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ (0 < K → ∀ x,
      ‖fderiv ℝ (Sverak.l1_eta n K) x‖ ≤ a ∧ ‖iteratedFDeriv ℝ 2 (Sverak.l1_eta n K) x‖ ≤ b) := by
    intro K
    by_cases hK : 0 < K
    · obtain ⟨a, ha0, ha⟩ := square_hess_eta_bound (n := n) hK 1
      obtain ⟨b, hb0, hb⟩ := square_hess_eta_bound (n := n) hK 2
      exact ⟨a, b, ha0, hb0, fun _ x => ⟨by simpa using ha x, hb x⟩⟩
    · exact ⟨0, 0, le_rfl, le_rfl, fun h => absurd h hK⟩
  choose a b ha0 hb0 hab using hbη
  -- the oscillation `N_K` and the test maps `ψ_K`
  set N : ℝ → ℝ := fun K => K + a K + b K with hNdef
  set ψ : ℝ → (Fin n → ℝ) → ℝ :=
    fun K y => Sverak.l1_eta n K y * ((N K ^ 2)⁻¹ * φ (N K • y)) with hψdef
  have hKN : ∀ K, K ≤ N K := fun K => by simp only [hNdef]; linarith [ha0 K, hb0 K]
  have hgc : ∀ K, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => (N K ^ 2)⁻¹ * φ (N K • y) :=
    fun K => contDiff_const.mul (hφ.comp (contDiff_const_smul _))
  have hψc : ∀ K, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ K) := fun K =>
    (Sverak.l1_eta_contDiff n K).mul (hgc K)
  -- `ψ_K` has compact support in the cube
  have hsupp : ∀ K, 1 ≤ K → HasCompactSupport (ψ K) ∧ tsupport (ψ K) ⊆ unitCube n := by
    intro K hK
    have hK0 : 0 < K := by linarith
    set S := Set.pi Set.univ fun _ : Fin n => Set.Icc (1 / (2 * K)) (1 - 1 / (2 * K))
    have h0 : ∀ x, x ∉ S → ψ K x = 0 := fun x hx => by
      have : Sverak.l1_eta n K x = 0 :=
        Sverak.l1_eta_eq_zero hK0 fun h => hx fun i _ => ⟨(h i).1.le, (h i).2.le⟩
      simp [hψdef, this]
    refine ⟨HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_Icc) h0, ?_⟩
    refine (closure_minimal (Function.support_subset_iff'.2 h0)
      (isClosed_set_pi fun _ _ => isClosed_Icc)).trans ?_
    intro x hx i _
    have := hx i (Set.mem_univ _)
    have hp : 0 < 1 / (2 * K) := by positivity
    exact ⟨hp.trans_le this.1, by linarith [this.2]⟩
  -- the Hessians of `ψ_K` are bounded uniformly in `K ≥ 1`
  have hbound : ∀ K, 1 ≤ K → ∀ x i j, |hessian (ψ K) x i j| ≤ R := by
    intro K hK x i j
    have hK0 : 0 < K := by linarith
    obtain ⟨haK, hbK⟩ := hab K hK0 x
    have hN1 : 1 ≤ N K := hK.trans (hKN K)
    have hN0 : 0 < N K := by linarith
    have haN : a K ≤ N K := by simp only [hNdef]; linarith [hb0 K]
    have hbN : b K ≤ N K ^ 2 := by
      have : b K ≤ N K := by simp only [hNdef]; linarith [ha0 K]
      nlinarith
    set g : (Fin n → ℝ) → ℝ := fun y => (N K ^ 2)⁻¹ * φ (N K • y) with hg
    have hg2 : ContDiff ℝ 2 g := (hgc K).of_le hle2
    have hη2 : ContDiff ℝ 2 (Sverak.l1_eta n K) := (Sverak.l1_eta_contDiff n K).of_le hle2
    have hgk : ∀ k, ‖iteratedFDeriv ℝ k g x‖ ≤ (N K ^ 2)⁻¹ * N K ^ k * Φ k := fun k => by
      refine (square_hess_norm_scale_le hφ _ _ k x).trans ?_
      rw [abs_of_pos (inv_pos.2 (pow_pos hN0 2)), abs_of_pos hN0]
      exact mul_le_mul_of_nonneg_left (hΦ k _) (by positivity)
    have hg0 : ‖g x‖ ≤ (N K ^ 2)⁻¹ * N K ^ 0 * Φ 0 := by
      have := hgk 0; rwa [norm_iteratedFDeriv_zero] at this
    have hg1 : ‖fderiv ℝ g x‖ ≤ (N K ^ 2)⁻¹ * N K ^ 1 * Φ 1 := by
      have := hgk 1; rwa [norm_iteratedFDeriv_one] at this
    have hgg : ‖iteratedFDeriv ℝ 2 g x‖ ≤ (N K ^ 2)⁻¹ * N K ^ 2 * Φ 2 := hgk 2
    have hη1 : ‖Sverak.l1_eta n K x‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (Sverak.l1_eta_nonneg n K x)]; exact Sverak.l1_eta_le_one n K x
    have hL := square_hess_norm_iteratedFDeriv_two_mul_le hη2 hg2 x
    have e1 : a K * ((N K ^ 2)⁻¹ * N K ^ 1 * Φ 1) ≤ Φ 1 := by
      rw [show a K * ((N K ^ 2)⁻¹ * N K ^ 1 * Φ 1) = (a K / N K) * Φ 1 by field_simp]
      exact mul_le_of_le_one_left (hΦ0 1) ((div_le_one hN0).2 haN)
    have e2 : b K * ((N K ^ 2)⁻¹ * N K ^ 0 * Φ 0) ≤ Φ 0 := by
      rw [show b K * ((N K ^ 2)⁻¹ * N K ^ 0 * Φ 0) = (b K / N K ^ 2) * Φ 0 by field_simp]
      exact mul_le_of_le_one_left (hΦ0 0) ((div_le_one (by positivity)).2 hbN)
    have e3 : (N K ^ 2)⁻¹ * N K ^ 2 * Φ 2 = Φ 2 := by field_simp
    have t1 : ‖Sverak.l1_eta n K x‖ * ‖iteratedFDeriv ℝ 2 g x‖ ≤
        1 * ((N K ^ 2)⁻¹ * N K ^ 2 * Φ 2) :=
      mul_le_mul hη1 hgg (norm_nonneg _) zero_le_one
    have t2 : 2 * ‖fderiv ℝ (Sverak.l1_eta n K) x‖ * ‖fderiv ℝ g x‖ ≤
        2 * a K * ((N K ^ 2)⁻¹ * N K ^ 1 * Φ 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left haK zero_le_two) hg1 (norm_nonneg _)
        (mul_nonneg zero_le_two (ha0 K))
    have t3 : ‖iteratedFDeriv ℝ 2 (Sverak.l1_eta n K) x‖ * ‖g x‖ ≤
        b K * ((N K ^ 2)⁻¹ * N K ^ 0 * Φ 0) :=
      mul_le_mul hbK hg0 (norm_nonneg _) (hb0 K)
    have hψK : ψ K = fun y => Sverak.l1_eta n K y * g y := rfl
    calc |hessian (ψ K) x i j| ≤ ‖iteratedFDeriv ℝ 2 (ψ K) x‖ :=
          square_hess_abs_hessian_le ((hψc K).of_le hle2) x i j
      _ ≤ R := by
          rw [hψK]
          refine hL.trans ?_
          rw [hR]
          nlinarith
  -- on `(1/K, 1 − 1/K)^n`, `D² ψ_K (x) = D² φ (N_K x)`
  have hinner : ∀ K, 0 < K → ∀ x : Fin n → ℝ, (∀ i, 1 / K < x i ∧ x i < 1 - 1 / K) →
      hessian (ψ K) x = hessian φ (N K • x) := by
    intro K hK0 x hx
    have hN0 : N K ≠ 0 := (hK0.trans_le (hKN K)).ne'
    have hev : ψ K =ᶠ[𝓝 x] fun y => (N K ^ 2)⁻¹ * φ (N K • y) := by
      have hO : IsOpen (Set.pi Set.univ fun _ : Fin n => Set.Ioo (1 / K) (1 - 1 / K)) :=
        isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
      filter_upwards [hO.mem_nhds fun i _ => hx i] with y hy
      have : Sverak.l1_eta n K y = 1 := Sverak.l1_eta_eq_one hK0 fun i =>
        ⟨(hy i (Set.mem_univ _)).1.le, (hy i (Set.mem_univ _)).2.le⟩
      simp only [hψdef, this, one_mul]
    rw [square_hess_hessian_congr ((hψc K).of_le hle2) ((hgc K).of_le hle2) hev,
      square_hess_hessian_scale hφ hN0]
  -- the integrand is bounded on the matrices with entries in `[-R, R]`
  set S : Set (Matrix (Fin n) (Fin n) ℝ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-R) R
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    (hF.comp (continuous_const.add continuous_id)).continuousOn
  have hφR : ∀ y i j, |hessian φ y i j| ≤ R := fun y i j => by
    refine (square_hess_abs_hessian_le hφ2 y i j).trans ((hΦ 2 y).trans ?_)
    rw [hR]; linarith [hΦ0 0, hΦ0 1]
  have hmemS : ∀ X : Matrix (Fin n) (Fin n) ℝ, (∀ i j, |X i j| ≤ R) → X ∈ S :=
    fun X h i _ j _ => abs_le.1 (h i j)
  -- the averaged integrand
  let G : (Fin n → ℝ) → ℝ := fun y => F (A + hessian φ y)
  have hGc : Continuous G :=
    hF.comp (continuous_const.add (square_hess_continuous_hessian hφ))
  have hGper : ∀ x (z : Fin n → ℤ), G (x + fun i => (z i : ℝ)) = G x := fun x z => by
    simp only [G, square_hess_hessian_periodic hφ2 hper]
  let H : ℝ → (Fin n → ℝ) → ℝ := fun K x => F (A + hessian (ψ K) x) - G (N K • x)
  have hψint : ∀ K, Continuous fun x => F (A + hessian (ψ K) x) := fun K =>
    hF.comp (continuous_const.add (square_hess_continuous_hessian (hψc K)))
  have hHc : ∀ K, Continuous (H K) := fun K =>
    (hψint K).sub (hGc.comp (continuous_const_smul _))
  have : IsFiniteMeasure (volume.restrict (unitCube n)) :=
    isFiniteMeasure_restrict.2 (by
      rw [show unitCube n = Sverak.unitCube n from rfl, Sverak.volume_unitCube]; simp)
  have hcube : MeasurableSet (unitCube n) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  -- dominated convergence: `∫ F (A + D² ψ_K) − ∫ F (A + D²φ (N_K x)) dx → 0`
  have hlim : Tendsto (fun K => ∫ x in unitCube n, H K x) atTop
      (𝓝 (∫ x in unitCube n, (0:ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * M)
      (Eventually.of_forall fun K => (hHc K).aestronglyMeasurable) ?_ (integrable_const _) ?_
    · filter_upwards [eventually_ge_atTop 1] with K hK
      refine Eventually.of_forall fun x => ?_
      have h1 : ‖F (A + hessian (ψ K) x)‖ ≤ M := hM _ (hmemS _ (hbound K hK x))
      have h2 : ‖G (N K • x)‖ ≤ M := hM _ (hmemS _ (hφR _))
      calc ‖H K x‖ ≤ ‖F (A + hessian (ψ K) x)‖ + ‖G (N K • x)‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith
    · rw [ae_restrict_iff' hcube]
      refine Eventually.of_forall fun x hx => ?_
      refine tendsto_const_nhds.congr' ?_
      have ht : Tendsto (fun K : ℝ => 1 / K) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hev : ∀ᶠ K in atTop, ∀ i, 1 / K < x i ∧ x i < 1 - 1 / K := by
        rw [eventually_all]
        intro i
        have hxi := hx i (Set.mem_univ _)
        filter_upwards [ht.eventually (Iio_mem_nhds hxi.1),
          ht.eventually (Iio_mem_nhds (sub_pos.2 hxi.2))] with K h1 h2
        exact ⟨h1, by linarith⟩
      filter_upwards [hev, eventually_gt_atTop 0] with K hK hK0
      show (0:ℝ) = F (A + hessian (ψ K) x) - F (A + hessian φ (N K • x))
      rw [hinner K hK0 x hK, sub_self]
  rw [integral_zero] at hlim
  -- by periodicity, `∫ F (A + D²φ (N_K x)) dx → ∫ F (A + D²φ)`
  have hNt : Tendsto N atTop atTop := tendsto_atTop_mono hKN tendsto_id
  have havg : Tendsto (fun K : ℝ => ∫ x in unitCube n, G (N K • x)) atTop
      (𝓝 (∫ x in unitCube n, G x)) :=
    (Sverak.l1_tendsto_setIntegral_comp_smul hGc hGper).comp hNt
  have hK : Tendsto (fun K => ∫ x in unitCube n, F (A + hessian (ψ K) x)) atTop
      (𝓝 (∫ x in unitCube n, G x)) := by
    have h := hlim.add havg
    rw [zero_add] at h
    refine h.congr fun K => ?_
    have i1 : IntegrableOn (H K) (unitCube n) := Sverak.gen_integrableOn_unitCube (hHc K)
    have i2 : IntegrableOn (fun x => G (N K • x)) (unitCube n) :=
      Sverak.gen_integrableOn_unitCube (hGc.comp (continuous_const_smul _))
    rw [← integral_add i1 i2]
    congr 1
    funext x
    simp only [H]
    ring
  -- some `ψ_K` contradicts Hessian quasiconvexity
  obtain ⟨K, hKlt, hK1⟩ := ((hK.eventually_lt_const hlt).and (eventually_ge_atTop 1)).exists
  obtain ⟨hcs, hts⟩ := hsupp K hK1
  have := hqc (ψ K) (hψc K) hcs hts (Sverak.gen_integrableOn_unitCube (hψint K))
  linarith

end Cassese
