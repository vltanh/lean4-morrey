module

public import Morrey.Pedregal.Map

/-!
# The paper's proof of Theorem 1.1 (1), up to Corollary 7.2

Section 8 (Conclusion) proves Theorem 1.1 (1) by applying Kakutani's theorem (Theorem 6.2) to
`𝐓`, whose hypotheses are checked in Subsection 6.1 (closed graph, compact values), Proposition
6.3 (convex values) and Corollary 7.2 (nonempty values), and then Proposition 6.1 (a fixed point
gives a laminate). Every step but Corollary 7.2 is correct. This file formalizes the argument with
the non-emptiness of the values as a hypothesis: Corollary 7.2 is false
(`Pedregal.corollary7_2_false`), so this is not a proof of Theorem 1.1 (1).
-/

@[expose] public section

namespace Pedregal

/-- **Theorem 1.1 (1)** (`objetivo`), the paper's argument with the conclusion of Corollary 7.2 as a
hypothesis. If `𝐓(t)` is nonempty for every `t ∈ Θ_l`, then `𝐓` has a fixed point (Kakutani's
theorem, with Proposition 6.3 and Subsection 6.1), and the gradient measure `ν` of `(u, v)` is a
laminate (Proposition 6.1). The hypothesis does not hold in general (`Pedregal.corollary7_2_false`).

Departure from the paper (reason 1: the paper's step is wrong; REPORT.md, E13): Section 8 takes
the non-emptiness of the values of `𝐓` from Corollary 7.2, which is false, and nothing along the
paper's lines supplies it; so this theorem takes it as a hypothesis, and is not Theorem 1.1 (1). -/
theorem theorem1_1_of_nonempty {l : ℕ} (S : TriMold l) {u v : (Fin 2 → ℝ) → ℝ} (hu : u ∈ PL l)
    (hv : v ∈ PL l) (hne : ∀ t ∈ Theta S, (T S u v t).Nonempty) :
    IsLaminate (gradMeasure l u v) := by
  obtain ⟨t, ht, hfix⟩ := External.Kakutani.exists_fixedPoint (theta_nonempty S)
    (isCompact_theta S) (convex_theta S) (fun t _ => T_subset_theta S u v t)
    (section6_1_usc S u v) hne (fun t _ => proposition6_3 S u v t)
    (fun _ ht => section6_1_isCompact S u v ht)
  exact proposition6_1 S hu hv ht hfix

end Pedregal
