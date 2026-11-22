module

public import Morrey.Cassese.Introduction
public import Morrey.Common.External.Kristensen.Smoothing

/-!
# Section 5: the non-locality of quasiconvexity among smooth integrands

Corollary 5.2 follows from Theorem 1.3 (the quartic) by "a standard smoothing argument"
(Kristensen 1999, Proposition 2; Heinz 2008). It is in a module of its own because its proof
uses Theorem 1.3, which `Cassese.Introduction` states.
-/

@[expose] public section

namespace Cassese

/-- **Corollary 5.2** (`cs-cor5.2`): for every `m ≥ 3` there are a smooth `h : ℝ^{2×m} → ℝ` and
`c, C > 0` with `D²h (A) [H, H] ≥ c ‖H‖²` for every `A` and every rank-one `H`,
`c ‖A‖² ≤ h (A) ≤ C (1 + ‖A‖²)` for every `A`, and `h` not quasiconvex at `0` (`‖·‖` the
Frobenius norm; `D²h (A) [H, H]` is the second derivative of `t ↦ h (A + t H)` at `0`).
The proof uses Kristensen's smoothing argument (`External.Kristensen.Smoothing`, stated for
rank-one convex homogeneous quartics on `ℝ^{2×m}`, `m ≥ 3`, that are not quasiconvex at `0`, and
proved in `External.Kristensen.smoothing_holds`). It applies it to the quartic of Theorem 1.3
lifted to `ℝ^{2×m}` through the first three columns, read through the bridges
`cov_rankOneConvex_iff` and `cov_quasiconvexAtOn_unitCube_iff` of `Cassese.Bridges`.

Proof: the quartic `P` of Theorem 1.3 lifted to `P ∘ T`, `T A` the first three columns of `A`
(the polynomial `MvPolynomial.rename` of `P`'s), is a rank-one convex homogeneous quartic
(`lift_rankOneConvex_comp`) which is not quasiconvex at `0` (a witness for `P ∘ T` would give one
for `P`, `lift_quasiconvexAt_of_comp_trunc`); Kristensen's smoothing gives `h`. -/
theorem corollary5_2 {m : ℕ} (hm : 3 ≤ m) :
    ∃ (h : Matrix (Fin 2) (Fin m) ℝ → ℝ) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X : Fin 2 → Fin m → ℝ => h (Matrix.of X)) ∧
      (∀ A H : Matrix (Fin 2) (Fin m) ℝ, H.rank = 1 →
        c * frobSq H ≤ iteratedDeriv 2 (fun t : ℝ => h (A + t • H)) 0) ∧
      (∀ A : Matrix (Fin 2) (Fin m) ℝ, c * frobSq A ≤ h A ∧ h A ≤ C * (1 + frobSq A)) ∧
      ¬ QuasiconvexAt h 0 := by
  -- the quartic `P` of Theorem 1.3, lifted to `P ∘ T` with `T A` the first three columns of `A`
  obtain ⟨P, ⟨Q, hQh, hQ⟩, hR, hnq⟩ := theorem1_3_a
  set Q' := MvPolynomial.rename
    (fun ij : Fin 2 × Fin 3 => (Fin.castLE le_rfl ij.1, Fin.castLE hm ij.2)) Q with hQ'def
  have hfun : (fun A : Matrix (Fin 2) (Fin m) ℝ => MvPolynomial.eval (fun ij => A ij.1 ij.2) Q') =
      fun A => P (lift_trunc le_rfl hm A) := by
    funext A
    rw [hQ'def, MvPolynomial.eval_rename, hQ]
    rfl
  -- `P ∘ T` is a rank-one convex homogeneous quartic, not quasiconvex at `0`
  have hRl : CalculusOfVariations.RankOneConvex
      (fun A : Matrix (Fin 2) (Fin m) ℝ => MvPolynomial.eval (fun ij => A ij.1 ij.2) Q') := by
    rw [hfun]
    exact (cov_rankOneConvex_iff _).2 (lift_rankOneConvex_comp le_rfl hm hR)
  have hnql : ¬ CalculusOfVariations.QuasiconvexAtOn (CalculusOfVariations.unitCube m)
      (fun A : Matrix (Fin 2) (Fin m) ℝ => MvPolynomial.eval (fun ij => A ij.1 ij.2) Q') 0 := by
    rw [hfun, cov_quasiconvexAtOn_unitCube_iff]
    intro hq
    have := lift_quasiconvexAt_of_comp_trunc le_rfl hm (intro_isIntegrand_of_continuous
      (intro_continuous_of_isHomogeneousPolynomial ⟨Q, hQh, hQ⟩)) hq
    rw [lift_trunc_zero] at this
    exact hnq 0 this
  -- Kristensen's smoothing
  obtain ⟨h, c, C, hc, hC, hsm, hLH, hgr, hnq'⟩ :=
    External.Kristensen.smoothing_holds m hm Q' hQh.rename_isHomogeneous hRl hnql
  exact ⟨h, c, C, hc, hC, hsm, hLH, hgr,
    fun hq => hnq' ((cov_quasiconvexAtOn_unitCube_iff h 0).2 hq)⟩

end Cassese
