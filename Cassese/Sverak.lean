module

public import Cassese.Bridges
public import Sverak.Theorem

/-!
# Section 1.1: Šverák's example in Cassese's terms

Section 1.1 recalls Šverák's example: for small `ε > 0` and a suitable `k (ε)`, the integrand
`f (X) = h (P X) + ε ‖X‖² + ε ‖X‖⁴ + k (ε) ‖X − P X‖²` on `ℝ^{3×2}` "is rank-one convex but not
quasiconvex at `0`". `sverak_example` proves this for some `ε` and `k`, in Cassese's definitions,
from the formalization of Šverák's paper (`Sverak.equation11`, `Sverak.lemma1_witness`) and the
bridges (`rankOneConvex_iff`, `not_quasiconvexAt_of_smooth`).
-/

@[expose] public section

open MeasureTheory

namespace Cassese

/-- Šverák's example (Section 1.1, citing Šverák 1992): there are `ε > 0` and `k > 0` such that
Šverák's `F` is rank-one convex (Definition 2.2) and not quasiconvex at `0` (Definition 2.1). -/
theorem sverak_example :
    ∃ ε > 0, ∃ k > 0, RankOneConvex (Sverak.sverakF ε k) ∧
      ¬ QuasiconvexAt (Sverak.sverakF ε k) 0 := by
  obtain ⟨ε, hε, k, hk, hR, hlt⟩ := Sverak.equation11
  refine ⟨ε, hε, k, hk, (rankOneConvex_iff _).1 hR, ?_⟩
  have hlt' : ∫ x in Sverak.unitCube 2, Sverak.sverakF ε k (0 + Sverak.jac Sverak.w x) <
      Sverak.sverakF ε k 0 := by
    simp only [zero_add]; exact hlt
  obtain ⟨φ, hφ, hc, hs, hφlt⟩ :=
    Sverak.lemma1_witness (Sverak.thm_sverakF_continuous ε k) Sverak.w_contDiff
      Sverak.w_periodic hlt'
  exact not_quasiconvexAt_of_smooth (Sverak.thm_sverakF_continuous ε k) hφ hc hs hφlt

end Cassese
