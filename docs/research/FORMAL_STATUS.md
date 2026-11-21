# Formalization baseline

Inspected source at upstream commit `d0471a6f174c8d5851398ec8069cd5bb2defbb54` (21 November 2026). This inspection did **not** rebuild Lean, run the axiom audit or rerun Comparator. The upstream README reports those checks as passing; that is a historical project claim, not a new validation result for this research-ledger PR. No `sorry`, declaration of an `axiom`, or `native_decide` was found in `Morrey/` by the source-text scan. `palomar/*/Challenge.lean` intentionally has `sorry` challenge placeholders.

## 1. Source-backed ledger entries

All paths below are relative to the repository root. `SOURCE-FORMAL` means a proof declaration and body are present in the inspected Lean source; use the established CI/build to certify the current checkout. The new Python experiments and prose deductions do not acquire this status from being stored beside Lean code.

| ID | Result and exact scope | Status | Current source / symbol |
| --- | --- | --- | --- |
| F01 | Pedregal Proposition 7.1 is false. | SOURCE-FORMAL refutation | [Morrey/Pedregal/NonEmptiness/Counterexample.lean](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean): `Pedregal.proposition7_1_false` |
| F02 | Pedregal Corollary 7.2 is false: the canonical level-one mold, explicit functions, and uniform weights give an empty value of the map. | SOURCE-FORMAL refutation | Same file: `Pedregal.T_cex_eq_empty`, `Pedregal.corollary7_2_false` |
| F03 | Both the weakened Step 2 summary and the paper's summary with its prescribed starting barycenter are false. | SOURCE-FORMAL refutations | Same file: `Pedregal.step2Claim_false`, `Pedregal.step2ClaimPaper_false` |
| F04 | A fixed point of the stated map gives a finite-order laminate. If every value is nonempty, Kakutani provides such a fixed point. The universal nonemptiness premise is false. | SOURCE-FORMAL conditional result | [Morrey/Pedregal/Map.lean](../../Morrey/Pedregal/Map.lean): `Pedregal.proposition6_1`; [Morrey/Pedregal/Reduction.lean](../../Morrey/Pedregal/Reduction.lean): `Pedregal.theorem1_1_of_nonempty` |
| F05 | Every pair of functions in `PL 1` has a gradient measure that is a finite-order laminate, by the explicit eight-vertex construction. | SOURCE-FORMAL, level one only | [Morrey/Pedregal/LevelOne.lean](../../Morrey/Pedregal/LevelOne.lean): `Pedregal.theorem1_1_part1_levelOne` |
| F06 | The weight polytope is nonempty, convex and compact. The set-valued map has a closed graph and compact, convex values and is upper semicontinuous. None of these entails nonempty values. | SOURCE-FORMAL infrastructure | [Morrey/Pedregal/Weights.lean](../../Morrey/Pedregal/Weights.lean): `theta_nonempty`, `convex_theta`, `isCompact_theta`; [Morrey/Pedregal/Map.lean](../../Morrey/Pedregal/Map.lean): `section6_1_isClosed_graph`, `section6_1_isCompact`, `section6_1_usc`, `proposition6_3` |
| F07 | A finite rank-one splitting tree yields a finite-order laminate. | SOURCE-FORMAL infrastructure | [Morrey/Pedregal/Hn/Laminate.lean](../../Morrey/Pedregal/Hn/Laminate.lean): `Pedregal.Mold.isLaminate_leafMeasure` |
| F08 | The upper-semicontinuous formulation of Kakutani, derived from the fixed-point dependency. | SOURCE-FORMAL infrastructure | [Morrey/Common/External/Kakutani/Theorem.lean](../../Morrey/Common/External/Kakutani/Theorem.lean): `External.Kakutani.exists_fixedPoint` |
| F09 | The all-level finite-order laminate statement, RC implies QC in `2 × 2`, and RC iff QC for continuous integrands are propositions only. | OPEN; no proof or refutation here | [Morrey/Pedregal/Introduction.lean](../../Morrey/Pedregal/Introduction.lean): `Pedregal.Theorem1_1_part1`, `Pedregal.Theorem1_1_part2`, `Pedregal.Theorem1_2` are `def ... : Prop` |
| F10 | Šverák's quartic counterexample in `3 × 2`, and the extension to at least three components and two variables. | SOURCE-FORMAL; does not resolve `2 × 2` | [Morrey/Sverak/Theorem.lean](../../Morrey/Sverak/Theorem.lean): `Sverak.theorem_main`, `Sverak.corollary`, `Sverak.remark_polynomial` |
| F11 | A strict periodic smooth energy violation for a continuous integrand yields a smooth compactly supported witness on the unit cube. This is dimension-general infrastructure already available. | SOURCE-FORMAL infrastructure | [Morrey/Sverak/Lemma1.lean](../../Morrey/Sverak/Lemma1.lean): `Sverak.lemma1_witness`; the periodic equivalence is `Sverak.lemma1` |
| F12 | Cassese's definitions, equivalence with Šverák's RC definition, a one-way QC bridge, and Šverák's `3 × 2` example expressed in Cassese's definitions. | SOURCE-FORMAL; **not** Cassese's new `2 × 3` construction | [Morrey/Cassese/Defs.lean](../../Morrey/Cassese/Defs.lean), `Bridges.lean`, `Sverak.lean`: `Cassese.rankOneConvex_iff`, `Cassese.quasiconvexOn_of_quasiconvex`, `Cassese.sverak_example` |

In this checkout `Morrey/Cassese/` has exactly the three files named in F12. The root README says Cassese's full statements are on branch `cassese`. That branch was not inspected for this task; do not claim its proofs or pending work have been incorporated into `main`.

## 2. Definitions and scope that must remain explicit

`Pedregal.IsLaminate` is an inductive predicate for **finite-order** laminates on finitely supported measures ([Morrey/Pedregal/Defs.lean](../../Morrey/Pedregal/Defs.lean)). It is not a definition of every measure satisfying rank-one-convex Jensen inequalities, nor every weak limit of finite laminates. Pedregal's all-level finite-order target is a sufficient route to the planar problem; a positive proof of Morrey's statement need not establish this stronger target. Conversely, failure to find a finite tree is not a counterexample to Jensen's inequality.

`Pedregal.Quasiconvex` tests bounded open planar domains with null boundary and globally Lipschitz maps vanishing outside the domain. `Cassese.QuasiconvexAt` tests Lipschitz maps on the unit cube, explicitly requiring integrability; `Sverak.QuasiconvexOn` uses smooth compactly supported tests. The existing bridges cover Cassese–Šverák, not the full Pedregal–Cassese equivalence. For a continuous polynomial with a bounded Lipschitz gradient, the necessary integrability is standard mathematics but still needs a Lean lemma if the final result uses that definition.

The determinant moment identity and the correct mean are necessary conditions on a gradient law. They are not a realization theorem. A finite measure violating polyconvex Jensen, or a finite measure with compatible minors, is not automatically an admissible gradient witness.

`section6_1_isClosed_graph` keeps the pair of functions fixed. A claim about joint closedness in `(u,v,t,r)`, robust empty fibers under perturbation, or proper algebraic exceptional sets needs additional proof. Source-FORMAL F06 must not silently be used as if it included those results.


For the completion gates, see [ROADMAP.md](ROADMAP.md). The full research record is in [LEDGER.md](LEDGER.md).
