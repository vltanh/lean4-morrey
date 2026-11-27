module

public import Morrey.Pedregal.Introduction
public import Morrey.Pedregal.Jensen
public import Morrey.Cassese.Bridges
public import Morrey.Common.External.KinderlehrerPedregal.Envelope
public import Morrey.Common.External.Rindler.Lemmas

/-!
# Pedregal's definitions and the shared analytic interface

Connects rank-one convexity and quasiconvexity to the shared definitions and exports the
periodic strict-gap criterion. These bridges do not establish the planar Morrey implication.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Pedregal

/-- The derivative matrices agree definitionally. -/
theorem jacobian_eq_cov_grad (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    jacobian φ x = CalculusOfVariations.grad φ x := rfl

/-- Pedregal's test class includes the unit cube. This direction needs no continuity. -/
theorem cov_quasiconvex_of_quasiconvex {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (h : Quasiconvex f) : CalculusOfVariations.Quasiconvex f := by
  intro A φ K hφ h0 _
  have hb : Bornology.IsBounded (CalculusOfVariations.unitCube 2) :=
    (isCompact_closedBall (fun _ : Fin 2 => (1 / 2 : ℝ)) (1 / 2 : ℝ)).isBounded.subset
      External.KinderlehrerPedregal.kp_unitCube_subset_closedBall
  have hboundary : volume (frontier (CalculusOfVariations.unitCube 2)) = 0 := by
    rw [External.KinderlehrerPedregal.kp_unitCube_eq_ball]
    exact Convex.addHaar_frontier volume
      (convex_ball (fun _ : Fin 2 => (1 / 2 : ℝ)) (1 / 2 : ℝ) : Convex ℝ _)
  exact h (CalculusOfVariations.unitCube 2)
    External.KinderlehrerPedregal.kp_isOpen_unitCube hb hboundary A φ K hφ h0

/-- The missing integrability premise in Pedregal's definition is automatic for continuous
integrands and Lipschitz maps on bounded domains. The existing domain theorem supplies QC. -/
theorem quasiconvex_of_cov_quasiconvex {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hf : Continuous f) (h : CalculusOfVariations.Quasiconvex f) : Quasiconvex f := by
  intro D hD hb _ A φ K hφ h0
  have hDqc := External.Rindler.rd_quasiconvexAtOn_of_unitCube
    hf.lowerSemicontinuous (Cassese.isIntegrand_of_continuous hf).2 hb hD.measurableSet (h A)
  exact hDqc φ K hφ h0
    (External.KinderlehrerPedregal.kp_integrableOn hf A hφ hb.measure_lt_top.ne)

/-- Exact agreement with the shared definition for the continuous integrands of Theorem 1.2. -/
theorem cov_quasiconvex_iff {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hf : Continuous f) :
    CalculusOfVariations.Quasiconvex f ↔ Quasiconvex f :=
  ⟨quasiconvex_of_cov_quasiconvex hf, cov_quasiconvex_of_quasiconvex⟩

/-- The known implication QC ⇒ RC, in Pedregal's definitions. -/
theorem rankOneConvex_of_quasiconvex {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hf : Continuous f) (h : Quasiconvex f) : RankOneConvex f :=
  (cov_rankOneConvex_iff f).1
    (External.Rindler.rankOneConvex_of_quasiconvex hf.lowerSemicontinuous
      (Cassese.isIntegrand_of_continuous hf).2 (cov_quasiconvex_of_quasiconvex h))

/-- The paper's endpoint is exactly the universal planar implication in the shared definitions.
Continuity need not be assumed on the shared side: finite rank-one convex functions are
locally Lipschitz. This equivalence does not prove either endpoint. -/
theorem theorem1_1_part2_iff_cov_morrey : Theorem1_1_part2 ↔
    (∀ f : Matrix (Fin 2) (Fin 2) ℝ → ℝ,
      CalculusOfVariations.RankOneConvex f → CalculusOfVariations.Quasiconvex f) := by
  constructor
  · intro h f hrc
    have hf : Continuous f := (External.Rindler.lemma5_6 hrc).continuous
    exact cov_quasiconvex_of_quasiconvex (h f hf ((cov_rankOneConvex_iff f).1 hrc))
  · intro h f hf hrc
    exact quasiconvex_of_cov_quasiconvex hf (h f ((cov_rankOneConvex_iff f).2 hrc))

/-- Theorem 1.2 and Theorem 1.1 (2) have the same unresolved mathematical content. -/
theorem theorem1_2_iff_theorem1_1_part2 : Theorem1_2 ↔ Theorem1_1_part2 := by
  constructor
  · intro h f hf
    exact (h f hf).1
  · intro h f hf
    exact ⟨h f hf, rankOneConvex_of_quasiconvex hf⟩

/-- Any strict genuine periodic Lipschitz violation refutes Pedregal's notion; this is the
interface needed by a polynomial/finite-element negative certificate. -/
theorem not_quasiconvex_of_periodic_gap {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hf : Continuous f) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (K : NNReal) (hφ : LipschitzWith K φ)
    (hper : ∀ (x : Fin 2 → ℝ) (z : Fin 2 → ℤ),
      φ (x + fun i => (z i : ℝ)) = φ x)
    (hgap : (∫ x in CalculusOfVariations.unitCube 2,
      f (A + CalculusOfVariations.grad φ x)) < f A) : ¬ Quasiconvex f := by
  intro h
  have hqc := cov_quasiconvex_of_quasiconvex h
  have hp := (External.Rindler.quasiconvexAtOn_iff_periodic hf.lowerSemicontinuous
    (Cassese.isIntegrand_of_continuous hf).2 A).1 (hqc A)
  have hfin : volume (CalculusOfVariations.unitCube 2) ≠ ⊤ := by
    rw [External.KinderlehrerPedregal.kp_volume_unitCube]
    exact ENNReal.one_ne_top
  exact (hp φ K hφ hper
    (External.KinderlehrerPedregal.kp_integrableOn hf A hφ hfin)).not_gt hgap

end Pedregal
