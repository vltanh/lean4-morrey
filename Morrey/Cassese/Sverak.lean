module

public import Morrey.Cassese.Bridges
public import Morrey.Sverak.Theorem

/-!
# Section 1.1: Šverák's example in Cassese's terms

Section 1.1 (TeX lines 110–133) recalls Šverák's example: "for sufficiently small `ε > 0`, there
exists `k (ε)` such that" the integrand
`f (X) = h (P X) + ε ‖X‖² + ε ‖X‖⁴ + k (ε) ‖X − P X‖²` on `ℝ^{3×2}` "is rank-one convex but not
quasiconvex at `0`". `sverak_example` proves this, for every `ε ∈ (0, ε₀]`, in Cassese's
definitions, from the formalization of Šverák's paper (`Sverak.equation10`, `Sverak.lemma2`,
`Sverak.lemma1_witness`) and the bridges (`rankOneConvex_iff`, `not_quasiconvexAt_of_smooth`).
-/

@[expose] public section

open MeasureTheory

namespace Cassese

/-- **Šverák's example** (`cs-sverak`, Section 1.1, TeX lines 127–133, citing Šverák 1992): there
is `ε₀ > 0` such that for every `ε ∈ (0, ε₀]` there is `k = k (ε) > 0` for which Šverák's `F`
is rank-one convex (Definition 2.2) and not quasiconvex at `0` (Definition 2.1).

Proof: `ε₀` from Šverák's (10) (`Sverak.equation10`, which holds for every `ε ∈ (0, ε₀]`), and
`k (ε)` from Šverák's Lemma 2, so that `F` is rank-one convex; since `D w (x) ∈ L`,
`F (D w) = f (D w) + ε |D w|² + ε |D w|⁴`, so (10) gives `∫ F (D w) < 0 = F (0)` for Šverák's
periodic `w`; Šverák's Lemma 1 turns `w` into a smooth compactly supported witness, a test map
of Definition 2.1. -/
theorem sverak_example :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ k > 0, RankOneConvex (Sverak.sverakF ε k) ∧
      ¬ QuasiconvexAt (Sverak.sverakF ε k) 0 := by
  obtain ⟨ε₀, hε₀, h10⟩ := Sverak.equation10
  refine ⟨ε₀, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨k, hk, hR⟩ := Sverak.lemma2 hε
  refine ⟨k, hk, (rankOneConvex_iff _).1 hR, ?_⟩
  have hF0 : Sverak.sverakF ε k 0 = 0 := by
    simp [Sverak.sverakF, Sverak.sverakf, Sverak.sverakP, Sverak.frobSq, Fin.sum_univ_succ,
      Matrix.sub_apply]
  have h0 : Sverak.frobSq (0 : Matrix (Fin 3) (Fin 2) ℝ) = 0 := by simp [Sverak.frobSq]
  -- `|D w − P D w| = 0`, since `D w (x) ∈ L`: the integrand `F (D w)` is the one of (10)
  have hFw : ∀ x : Fin 2 → ℝ, Sverak.sverakF ε k (Sverak.jac Sverak.w x) =
      Sverak.sverakf (Sverak.jac Sverak.w x) + ε * Sverak.frobSq (Sverak.jac Sverak.w x) +
        ε * Sverak.frobSq (Sverak.jac Sverak.w x) ^ 2 := by
    intro x
    have hP : Sverak.sverakP (Sverak.jac Sverak.w x) = Sverak.jac Sverak.w x :=
      Sverak.sverakP_of_mem (by rw [Sverak.jac_w]; exact ⟨(_, _, _), rfl⟩)
    simp only [Sverak.sverakF, hP, sub_self, h0, mul_zero, add_zero]
  have hlt : ∫ x in Sverak.unitCube 2, Sverak.sverakF ε k (0 + Sverak.jac Sverak.w x) <
      Sverak.sverakF ε k 0 := by
    simp_rw [zero_add, hFw, hF0]
    exact h10 ε hε hεle
  obtain ⟨φ, hφ, hc, hs, hφlt⟩ :=
    Sverak.lemma1_witness (Sverak.thm_sverakF_continuous ε k) Sverak.w_contDiff
      Sverak.w_periodic hlt
  exact not_quasiconvexAt_of_smooth (Sverak.thm_sverakF_continuous ε k) hφ hc hs hφlt

end Cassese
