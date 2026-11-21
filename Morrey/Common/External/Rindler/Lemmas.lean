module

public import Morrey.Common.Basic.CalculusOfVariations.Basic

/-!
# Rindler and Dacorogna: rank-one convex functions and quasiconvexity

F. Rindler, *Calculus of variations*, Springer 2018, Lemma 5.6 and Propositions 5.1, 5.3;
B. Dacorogna, *Direct methods in the calculus of variations*, 2nd ed., Springer 2008,
Propositions 5.11, 5.13. Cassese quotes them as Lemma 2.1 and Lemma 2.2. They are standard and
within reach (class Mod of the inventory): they are stated here, to be proved.

Integrands are lower semicontinuous and locally bounded, as in Cassese (Section 1.5).
-/

@[expose] public section

namespace External.Rindler

open CalculusOfVariations

variable {d m : ℕ}

/-- **Lemma 2.1** (`cs-lem2.1`) of Cassese, citing Rindler, Lemma 5.6: a rank-one convex
integrand is locally Lipschitz. (`Matrix.of` identifies `ℝ^{d×m}` with `Fin d → Fin m → ℝ`, with
its product metric.) -/
theorem lemma5_6 {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f) :
    LocallyLipschitz fun X : Fin d → Fin m → ℝ => f (Matrix.of X) := by
  sorry

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, first assertion, citing Rindler, Proposition 5.1, and
Dacorogna, Proposition 5.11: a quasiconvex integrand is rank-one convex. -/
theorem rankOneConvex_of_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (hf : Quasiconvex f) :
    RankOneConvex f := by
  sorry

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, second assertion, citing Rindler, Proposition 5.3,
and Dacorogna, Proposition 5.13: quasiconvexity at `A` does not depend on the bounded open domain
of the test maps. -/
theorem quasiconvexAtOn_iff {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hlsc : LowerSemicontinuous f)
    (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) {Ω : Set (Fin m → ℝ)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtOn Ω f A := by
  sorry

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, third assertion, citing Rindler, Proposition 5.3, and
Dacorogna, Proposition 5.13: quasiconvexity at `A` is equivalent to the inequality for periodic
Lipschitz test maps on the torus `𝕋^m = ℝ^m / ℤ^m`. -/
theorem quasiconvexAtOn_iff_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtPeriodic f A := by
  sorry

end External.Rindler
