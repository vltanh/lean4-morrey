# Formalization baseline and audited additions

Reaudited upstream source at `764256f7910b00551419fe71c35809e6b52d7ddd` on 22 November
2026. Its Lean source is unchanged from the previous baseline
`cde348ba320b65d902c9f0f782f392e932ba507c`. The [main CI job](https://github.com/vltanh/lean4-morrey/actions/runs/44989900031/job/137108445876)
passed, including the standard-axiom audit of all 4,166 library declarations. No local Lean
runtime or new Comparator run was available. The [formalization audit](MAIN_FORMALIZATION_AUDIT.md)
records the semantic review and the new global bridge modules in this PR, whose branch-CI
validation is recorded there. Python checks and prose arguments are not Lean proofs.

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
| F12 | Cassese's homogeneous quartic counterexample on `ℝ²ˣ³`, the nearby-exponent result, the elementary all-`p>1` higher-dimensional result, and the nonplanar dimensional landscape. | SOURCE-FORMAL; unconditional declarations for these results. Does not resolve `2 × 2`. | [Introduction.lean](../../Morrey/Cassese/Introduction.lean): `Cassese.theorem1_2`, `theorem1_3_a`, `theorem1_3_b`, `morrey_landscape`; construction in [TwoByThree.lean](../../Morrey/Cassese/TwoByThree.lean). |
| F13 | Every real-valued rank-one-convex function is locally Lipschitz. | SOURCE-FORMAL, dimension-general | [Rindler/Lemmas.lean](../../Morrey/Common/External/Rindler/Lemmas.lean): `External.Rindler.lemma5_6`; underlying separate-convexity result in [SeparatelyConvex.lean](../../Morrey/Common/Basic/Analysis/Convex/SeparatelyConvex.lean). |
| F14 | Quasiconvexity on the unit cube is equivalent to the periodic Lipschitz formulation, and to tests on any nonempty bounded open domain, for lower-semicontinuous locally bounded integrands. | SOURCE-FORMAL infrastructure; includes periodic FE maps once their admissibility and integral are instantiated | [Rindler/Lemmas.lean](../../Morrey/Common/External/Rindler/Lemmas.lean): `External.Rindler.quasiconvexAtOn_iff_periodic`, `quasiconvexAtOn_iff`; standard definitions in [CalculusOfVariations/Basic.lean](../../Morrey/Common/Basic/CalculusOfVariations/Basic.lean). |
| F15 | A polynomial of total degree at most three satisfying Cassese's `RankOneConvexAt ... 0` is quasiconvex. In `2 × 2`, global RC polynomials of degree at most three cannot furnish counterexamples. | SOURCE-FORMAL; `RankOneConvexAt` is defined by a touching globally RC integrand minorant, not a pointwise LH condition. Its Jensen characterization is a separate theorem. | [Folklore.lean](../../Morrey/Cassese/TwoByThree/Folklore.lean): `Cassese.proposition5_1`; definition in [Toolkit.lean](../../Morrey/Cassese/Toolkit.lean); quadratic bridge in [Dacorogna/Minors.lean](../../Morrey/Common/External/Dacorogna/Minors.lean). |

### Cassese results with named external hypotheses

The merge does not justify describing every Cassese result as unconditional.
`Cassese.theorem1_4` for general `p` still assumes named UMD/extrapolation and noncommutative
Khintchine inputs; `theorem1_4_four` supplies an unconditional `p=4` specialization in dimensions
at least 588. `theorem1_5` and `corollary1_6` assume `HNVWTransference` and
`DragicevicLowerBound`. These are visible hypotheses, not hidden axioms. See
[Introduction.lean](../../Morrey/Cassese/Introduction.lean), [Square.lean](../../Morrey/Cassese/Square.lean)
and the [Cassese report](../Cassese/REPORT.md).

The earlier ledger's statement that main contained only three Cassese files is superseded by
this baseline. The broader source can be reused without rebuilding its general analytic lemmas.

## 2. Definitions and scope that must remain explicit

`Pedregal.IsLaminate` is an inductive predicate for **finite-order** laminates on finitely supported measures ([Morrey/Pedregal/Defs.lean](../../Morrey/Pedregal/Defs.lean)). It is not a definition of every measure satisfying rank-one-convex Jensen inequalities, nor every weak limit of finite laminates. Pedregal's all-level finite-order target is a sufficient route to the planar problem; a positive proof of Morrey's statement need not establish this stronger target. Conversely, failure to find a finite tree is not a counterexample to Jensen's inequality.

`Pedregal.Quasiconvex` tests bounded open planar domains with null boundary and globally Lipschitz maps vanishing outside the domain. `Cassese.QuasiconvexAt` tests Lipschitz maps on the unit cube, explicitly requiring integrability; `Sverak.QuasiconvexOn` uses smooth compactly supported tests. Main has the Cassese–Šverák–shared bridges; this PR adds the Pedregal–shared equivalence for continuous integrands in [Bridges.lean](../../Morrey/Pedregal/Bridges.lean). The shared integrability theorem already handles every continuous integrand and Lipschitz map on a finite-volume set.

The determinant moment identity and the correct mean are necessary conditions on a gradient law. They are not a realization theorem. A finite measure violating polyconvex Jensen, or a finite measure with compatible minors, is not automatically an admissible gradient witness.

`section6_1_isClosed_graph` keeps the pair of functions fixed. A claim about joint closedness in `(u,v,t,r)`, robust empty fibers under perturbation, or proper algebraic exceptional sets needs additional proof. Source-FORMAL F06 must not silently be used as if it included those results.


## 3. Global additions in this PR

These entries describe the new source, with validation tracked in
[MAIN_FORMALIZATION_AUDIT.md](MAIN_FORMALIZATION_AUDIT.md); they were not present in the pinned
main snapshot.

| ID | Result and exact scope | Source / symbol |
| --- | --- | --- |
| F16 | Jensen for every Pedregal finite-order laminate, translation by every base matrix, and the all-level discrete consequence under the laminate-existence hypothesis. | [Jensen.lean](../../Morrey/Pedregal/Jensen.lean): `IsLaminate.jensen`, `discrete_jensen_of_theorem1_1_part1` |
| F17 | Exact planar RC-definition matching and QC-definition matching for continuous integrands; the two open Pedregal endpoints are equivalent to the shared universal implication. | [Jensen.lean](../../Morrey/Pedregal/Jensen.lean): `cov_rankOneConvex_iff`; [Bridges.lean](../../Morrey/Pedregal/Bridges.lean): `cov_quasiconvex_iff`, `theorem1_1_part2_iff_cov_morrey`, `theorem1_2_iff_theorem1_1_part2` |
| F18 | For every C² integrand in every matrix dimension, global LH nonnegativity is equivalent to global RC. | [LegendreHadamard.lean](../../Morrey/Common/Basic/CalculusOfVariations/LegendreHadamard.lean): `rankOneConvex_iff_iteratedFDeriv_nonneg` |
| F19 | Global LH plus a genuine periodic Lipschitz strict energy gap refutes the universal planar implication. This is a conditional acceptance theorem, not a supplied counterexample. | [CounterexampleCertificate.lean](../../Morrey/Pedregal/CounterexampleCertificate.lean): `not_cov_morrey_of_lh_periodic_gap` |

## 4. What remains to assemble

The new F16–F19 modules supply universal algebraic and analytic interfaces. The positive route
still needs the PL gradient-sum-to-integral identity, controlled dyadic interpolation and energy
convergence, as well as the central all-level Jensen or laminate-existence theorem. The negative
route needs an actual globally certified planar candidate; its polynomial certificate and
finite-element witness/integral must be instantiated in Lean before F19 applies. Neither route
needs a new proof of the general periodic cutoff theorem. No Python checker has become a Lean
checker merely by the addition of F19.

The main planar assertions remain propositions rather than proved theorems (F09). Their
central mathematical content is still missing; the Cassese merge settles different dimensions.

For the completion gates, see [ROADMAP.md](ROADMAP.md). The full research record is in [LEDGER.md](LEDGER.md).
