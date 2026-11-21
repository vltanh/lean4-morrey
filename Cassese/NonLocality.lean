module

public import Cassese.Introduction
public import External.Kristensen.Smoothing

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
Conditional on Burkholder's inequality (through Theorem 1.3) and on Kristensen's smoothing
argument (`External.Kristensen.Smoothing`, stated for rank-one convex homogeneous quartics on
`ℝ^{2×m}`, `m ≥ 3`, that are not quasiconvex at `0`). The proof applies it to the quartic of
Theorem 1.3 lifted to `ℝ^{2×m}` through the first three columns, read through the bridges
`cov_rankOneConvex_iff` and `cov_quasiconvexAtOn_unitCube_iff` of `Cassese.Bridges`. -/
theorem corollary5_2 (hB : BurkholderInequality)
    (hK : External.Kristensen.Smoothing) {m : ℕ} (hm : 3 ≤ m) :
    ∃ (h : Matrix (Fin 2) (Fin m) ℝ → ℝ) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun X : Fin 2 → Fin m → ℝ => h (Matrix.of X)) ∧
      (∀ A H : Matrix (Fin 2) (Fin m) ℝ, H.rank = 1 →
        c * frobSq H ≤ iteratedDeriv 2 (fun t : ℝ => h (A + t • H)) 0) ∧
      (∀ A : Matrix (Fin 2) (Fin m) ℝ, c * frobSq A ≤ h A ∧ h A ≤ C * (1 + frobSq A)) ∧
      ¬ QuasiconvexAt h 0 := by
  sorry

end Cassese
