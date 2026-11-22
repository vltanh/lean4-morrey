module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the libraries, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   { find Morrey -name '*.lean'; cd palomar && find . -name Solution.lean; } |
--     sed 's#^\./##; s/\.lean$//; s#/#.#g; s/^/import all /' | sort
-- Every paper's Solution is imported, and no Challenge: a Challenge holds a copy of its paper's
-- definitions under the library's names.
import all Cassese.Solution
import all Morrey.Cassese.Bridges
import all Morrey.Cassese.Conclusion
import all Morrey.Cassese.Defs
import all Morrey.Cassese.FourByTwo
import all Morrey.Cassese.Hypotheses
import all Morrey.Cassese.Introduction
import all Morrey.Cassese.Lifting
import all Morrey.Cassese.NonLocality
import all Morrey.Cassese.Rademacher
import all Morrey.Cassese.Square
import all Morrey.Cassese.Square.Envelope
import all Morrey.Cassese.Square.Frobenius
import all Morrey.Cassese.Square.Hermite
import all Morrey.Cassese.Square.Hessian
import all Morrey.Cassese.Square.Korn
import all Morrey.Cassese.Square.Moments
import all Morrey.Cassese.Square.Schatten
import all Morrey.Cassese.Square.Sharpness
import all Morrey.Cassese.Square.Torus
import all Morrey.Cassese.Square.TorusTwo
import all Morrey.Cassese.Square.Trace
import all Morrey.Cassese.Square.Triangle
import all Morrey.Cassese.Square.Weyl
import all Morrey.Cassese.Square.Witness
import all Morrey.Cassese.Sverak
import all Morrey.Cassese.Toolkit
import all Morrey.Cassese.TwoByM
import all Morrey.Cassese.TwoByThree
import all Morrey.Cassese.TwoByThree.Basic
import all Morrey.Cassese.TwoByThree.Extension
import all Morrey.Cassese.TwoByThree.ExtensionAux
import all Morrey.Cassese.TwoByThree.ExtensionOne
import all Morrey.Cassese.TwoByThree.Folklore
import all Morrey.Cassese.TwoByThree.Folklore.Laminate
import all Morrey.Cassese.TwoByThree.Folklore.NullLagrangian
import all Morrey.Cassese.TwoByThree.Folklore.Quasiaffine
import all Morrey.Cassese.TwoByThree.Hessian
import all Morrey.Cassese.TwoByThree.HessianCutoff
import all Morrey.Cassese.TwoByThree.NearFour
import all Morrey.Cassese.TwoByThree.Polynomial
import all Morrey.Cassese.TwoByThree.Rademacher
import all Morrey.Cassese.TwoByThree.Transpose
import all Morrey.Cassese.TwoByThree.Transpose.Cutoff
import all Morrey.Cassese.TwoByThree.Transpose.Estimate
import all Morrey.Cassese.TwoByThree.Transpose.Potential
import all Morrey.Cassese.TwoByThree.Transpose.Profile
import all Morrey.Cassese.TwoByThree.Witness
import all Morrey.Cassese.TwoByThree.WitnessCutoff
import all Morrey.Common.Basic.Analysis.Calculus.BumpFunction.Mollify
import all Morrey.Common.Basic.Analysis.Convex.SeparatelyConvex
import all Morrey.Common.Basic.Analysis.Fourier.TorusLipschitz
import all Morrey.Common.Basic.CalculusOfVariations.Basic
import all Morrey.Common.Basic.LinearAlgebra.Matrix.RankTwo
import all Morrey.Common.External.Burkholder.Inequality
import all Morrey.Common.External.Burkholder.ScalarFunction
import all Morrey.Common.External.Dacorogna.Minors
import all Morrey.Common.External.Dacorogna.Plancherel
import all Morrey.Common.External.Dragicevic.LowerBound
import all Morrey.Common.External.HNVW.Transference
import all Morrey.Common.External.Kakutani.Theorem
import all Morrey.Common.External.KinderlehrerPedregal.Basic
import all Morrey.Common.External.KinderlehrerPedregal.Envelope
import all Morrey.Common.External.KinderlehrerPedregal.Formula
import all Morrey.Common.External.KirchheimKristensen.Theorem
import all Morrey.Common.External.Kristensen.Smoothing
import all Morrey.Common.External.Osekowski.HilbertCharacterization
import all Morrey.Common.External.Rindler.Lemmas
import all Morrey.Pedregal.Checks
import all Morrey.Pedregal.Defs
import all Morrey.Pedregal.Hn.Laminate
import all Morrey.Pedregal.Hn.Mold
import all Morrey.Pedregal.Introduction
import all Morrey.Pedregal.LevelOne
import all Morrey.Pedregal.Map
import all Morrey.Pedregal.MoldTau
import all Morrey.Pedregal.NonEmptiness.Counterexample
import all Morrey.Pedregal.NonEmptiness.Statements
import all Morrey.Pedregal.Reduction
import all Morrey.Pedregal.Triangulation
import all Morrey.Pedregal.Weights
import all Morrey.Sverak.Construction
import all Morrey.Sverak.Cube
import all Morrey.Sverak.Defs
import all Morrey.Sverak.Lemma1
import all Morrey.Sverak.Lemma2
import all Morrey.Sverak.Theorem
import all Pedregal.Solution
import all Sverak.Solution

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`External/`) that it uses, whether proved there or, in a conditional
formalization, assumed as hypotheses of its statement. It then checks every declaration
of the library and the theorems that Palomar's comparator checks. The run fails if any of them
depends on an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a
`sorry` shows up as the axiom `sorryAx`). Its table of results is the source of the report's
dependency table.

It also writes the *route* of every numbered result to `.lake/route_deps.tsv`: the other
numbered results that its proof uses, found by following the proof through the library's helper
lemmas and stopping at numbered results, together with the TeX label that the result's docstring
names in backticks. `route_check.py` (in the skill's `scripts/`) compares these routes with the
results that the paper's proofs cite.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set the libraries' root
names in `isLibraryModule`: the paper's library, `External`, the results it cites, and `Basic`,
the library of general mathematics.
Keep one `import all` line per module of the libraries, each on its own line: a module that is
missing is still imported through the others, but without its proofs, and the audit then misses the
axioms and the routes inside them. The CI template checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, with a short label: the theorems proved in `External/`
or, when general, in `Basic/`, and, in a conditional formalization, the propositions assumed as
hypotheses. The traversal
stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Kakutani's fixed-point theorem (Thm 6.2)", ``External.Kakutani.exists_fixedPoint),
   -- Cassese: the cited results proved in `Morrey/Common/External`
   ("Burkholder's inequality (Cassese Thm 2.3 (1))", ``External.Burkholder.inequality),
   ("Burkholder's square function inequality (Cassese Thm 2.3 (2))",
    ``External.Burkholder.squareFunction),
   ("Burkholder's scalar function u (Cassese (13), (14))",
    ``External.Burkholder.scalarFunction_holds),
   ("Burkholder's scalar function u_q (Cassese Remark 4.5)",
    ``External.Burkholder.scalarFunctionQ_holds),
   ("Rindler Lemma 5.6 (Cassese Lemma 2.1)", ``External.Rindler.lemma5_6),
   ("Rindler, rank-one convexity of quasiconvex integrands (Cassese Lemma 2.2)",
    ``External.Rindler.rankOneConvex_of_quasiconvex),
   ("Rindler, domain independence (Cassese Lemma 2.2)", ``External.Rindler.quasiconvexAtOn_iff),
   ("Rindler, periodic test maps (Cassese Lemma 2.2)",
    ``External.Rindler.quasiconvexAtOn_iff_periodic),
   ("Dacorogna Thm 5.20 (Cassese Prop 5.1)", ``External.Dacorogna.rankOneAffineMinors_holds),
   ("Dacorogna Thm 5.25 (i) (Cassese Prop 5.1)", ``External.Dacorogna.quadraticForm_quasiconvex),
   ("Dacorogna's formula (Cassese Prop 2.2)",
    ``External.KinderlehrerPedregal.dacorognaFormula_holds),
   ("Kristensen's smoothing (Cassese Cor 5.2)", ``External.Kristensen.smoothing_holds),
   -- Cassese: the cited results assumed, as hypotheses of the statements that use them
   ("HNVW extrapolation (Cassese Prop 2.7 (1), assumed)", ``Cassese.HNVWExtrapolation),
   ("Randrianantoanina (Cassese Prop 2.7 (2), assumed)", ``Cassese.RandrianantoaninaSchattenUMD),
   ("Pisier (Cassese Prop 2.7 (3), assumed)", ``Cassese.PisierLpUMD),
   ("HNVW dyadic UMD (Cassese Prop 2.7 (4), assumed)", ``Cassese.HNVWDyadicUMD),
   ("Yaroslavtsev (Cassese Prop 2.7 (5), assumed)", ``Cassese.YaroslavtsevComplexUMD),
   ("HNVW zig-zag (Cassese Prop 2.7 (6), assumed)", ``Cassese.HNVWZigZag),
   ("Cox–Veraar decoupling (Cassese Prop 2.8, assumed)", ``Cassese.CoxVeraarDecoupling),
   ("Pisier–Xu (Cassese Prop 6.3, assumed)", ``Cassese.PisierXuKhintchine),
   ("Kahane–Khintchine (Cassese Prop 6.4, assumed)", ``Cassese.KahaneKhintchine),
   ("Hypercontractive Kahane–Khintchine (Remark 6.3, Prop 6.5 at q = ∞, assumed)",
    ``Cassese.KahaneKhintchineHypercontractive),
   ("Sharpness of Burkholder's constant (Cassese Cor 6.3)", ``Cassese.burkholderSharpness_holds),
   ("HNVW transference (Cassese Prop 7.2, assumed)", ``Cassese.HNVWTransference),
   ("Dragičević's lower bound (Cassese Thm 7.1, assumed)", ``Cassese.DragicevicLowerBound),
   ("Dragičević's L⁴ bound (Cassese Cor 7.2, assumed)", ``Cassese.DragicevicL4Bound)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("Prop 3.3", ``Pedregal.proposition3_3),
   ("Def 5.1 (assertions)", ``Pedregal.theta_nonempty),
   ("Def 5.1 (assertions)", ``Pedregal.convex_theta),
   ("Def 5.1 (assertions)", ``Pedregal.isCompact_theta),
   ("Def 5.1 (assertions)", ``Pedregal.theta_subset_simplex),
   ("Eq. (5.13)", ``Pedregal.equation5_13),
   ("Eq. (5.15)", ``Pedregal.equation5_15),
   ("Prop 6.1", ``Pedregal.proposition6_1),
   ("Thm 6.2 (Kakutani, cited)", ``External.Kakutani.exists_fixedPoint),
   ("Subsection 6.1", ``Pedregal.section6_1_isClosed_graph),
   ("Subsection 6.1", ``Pedregal.section6_1_isCompact),
   ("Subsection 6.1", ``Pedregal.section6_1_usc),
   ("Prop 6.3 (1)", ``Pedregal.proposition6_3_point),
   ("Prop 6.3 (1)", ``Pedregal.proposition6_3_dir),
   ("Prop 6.3 (2)", ``Pedregal.proposition6_3),
   ("Prop 7.1 (false)", ``Pedregal.proposition7_1_false),
   ("Cor 7.2 (false)", ``Pedregal.corollary7_2_false),
   ("Cor 7.2 from Prop 7.1", ``Pedregal.corollary7_2_of_proposition7_1),
   ("Step 2 summary (false)", ``Pedregal.step2Claim_false),
   ("Claim 7.4", ``Pedregal.claim7_4),
   ("Thm 1.1 (1), up to Cor 7.2", ``Pedregal.theorem1_1_of_nonempty),
   ("Thm 1.1 (1), l = 1", ``Pedregal.theorem1_1_part1_levelOne),
   ("Šverák Lemma 1", ``Sverak.lemma1),
   ("Šverák Lemma 1 (limit)", ``Sverak.lemma1_limit),
   ("Šverák Lemma 1 (witness)", ``Sverak.lemma1_witness),
   ("Šverák rank-one directions of L", ``Sverak.rank_ofRST_eq_one),
   ("Šverák f affine on rank-one lines of L", ``Sverak.sverakf_affine_of_rankOne),
   ("Šverák (4)", ``Sverak.equation4),
   ("Šverák (6)", ``Sverak.equation6),
   ("Šverák (7)", ``Sverak.equation7),
   ("Šverák (*)", ``Sverak.equation_star),
   ("Šverák (8)", ``Sverak.equation8),
   ("Šverák Lemma 2", ``Sverak.lemma2),
   ("Šverák (10)", ``Sverak.equation10),
   ("Šverák (11)", ``Sverak.equation11),
   ("Šverák Theorem", ``Sverak.theorem_main),
   ("Šverák Remark", ``Sverak.remark_polynomial),
   ("Šverák Corollary", ``Sverak.corollary),
   ("Cassese Section 1.1 (monotonicity)", ``Cassese.morreyPositive_mono),
   ("Cassese Section 1.1 (min (d, m) = 1)", ``Cassese.rankOneConvex_iff_convexOn_of_min_eq_one),
   ("Cassese Section 1.1 (min (d, m) = 1)", ``Cassese.quasiconvex_iff_convexOn_of_min_eq_one),
   ("Cassese Section 1.1 (min (d, m) = 1)", ``Cassese.morreyPositive_of_min_le_one),
   ("Cassese Section 1.1 (Šverák's example)", ``Cassese.sverak_example),
   ("Cassese Thm 1.1 (Kirchheim–Kristensen, quoted)", ``External.KirchheimKristensen.Theorem1_1),
   ("Cassese Section 1.3 (homogeneous monotonicity)", ``Cassese.homMorreyPositive_mono),
   ("Cassese Thm 1.2", ``Cassese.theorem1_2),
   ("Cassese Thm 1.2 (the paper's proof)", ``Cassese.theorem1_2_umd),
   ("Cassese Thm 1.3 (a)", ``Cassese.theorem1_3_a),
   ("Cassese Thm 1.3 (b)", ``Cassese.theorem1_3_b),
   ("Cassese Section 1.4 (2 × 2 landscape)", ``Cassese.morrey_landscape),
   ("Cassese Section 1.4 (homogeneous landscape)", ``Cassese.homMorrey_landscape),
   ("Cassese Thm 1.4", ``Cassese.theorem1_4),
   ("Cassese Thm 1.5", ``Cassese.theorem1_5),
   ("Cassese Cor 1.6", ``Cassese.corollary1_6),
   ("Cassese Lemma 2.1 (Rindler, cited)", ``External.Rindler.lemma5_6),
   ("Cassese Lemma 2.2 (Rindler, cited)", ``External.Rindler.rankOneConvex_of_quasiconvex),
   ("Cassese Lemma 2.2 (Rindler, cited)", ``External.Rindler.quasiconvexAtOn_iff),
   ("Cassese Lemma 2.2 (Rindler, cited)", ``External.Rindler.quasiconvexAtOn_iff_periodic),
   ("Cassese Prop 2.1", ``Cassese.proposition2_1),
   ("Cassese Prop 2.2 (Kinderlehrer–Pedregal, cited)",
    ``External.KinderlehrerPedregal.dacorognaFormula_holds),
   ("Cassese Section 2.1 (quasiconvex minorants)", ``Cassese.quasiconvexAt_iff_exists_minorant),
   ("Cassese Prop 2.3 (a)", ``Cassese.proposition2_3_a),
   ("Cassese Prop 2.3 (b)", ``Cassese.proposition2_3_b),
   ("Cassese Prop 2.3 (c)", ``Cassese.proposition2_3_c),
   ("Cassese Prop 2.3 (c), one direction", ``Cassese.proposition2_3_c_left),
   ("Cassese Section 2.1 (consequences of Prop 2.3)", ``Cassese.envelope_zero),
   ("Cassese Section 2.1 (consequences of Prop 2.3)",
    ``Cassese.rankOneConvexAt_zero_of_rankOneConvexAt),
   ("Cassese Section 2.1 (consequences of Prop 2.3)",
    ``Cassese.quasiconvexAt_zero_of_quasiconvexAt),
   ("Cassese Section 2.1 (consequences of Prop 2.3)",
    ``Cassese.nowhereQuasiconvex_of_not_quasiconvexAt_zero),
   ("Cassese Prop 2.4", ``Cassese.proposition2_4),
   ("Cassese Prop 2.5", ``Cassese.proposition2_5),
   ("Cassese Thm 2.3 (1) (Burkholder, cited)", ``Cassese.burkholderInequality_holds),
   ("Cassese Thm 2.3 (2) (Burkholder, cited)", ``Cassese.burkholderSquareFunction_holds),
   ("Cassese Prop 2.6 (Osękowski, quoted)", ``External.Osekowski.HilbertCharacterization),
   ("Cassese Prop 2.7 (1) (HNVW, assumed)", ``Cassese.HNVWExtrapolation),
   ("Cassese Prop 2.7 (2) (Randrianantoanina, assumed)", ``Cassese.RandrianantoaninaSchattenUMD),
   ("Cassese Prop 2.7 (3) (Pisier, assumed)", ``Cassese.PisierLpUMD),
   ("Cassese Prop 2.7 (4) (HNVW, assumed)", ``Cassese.HNVWDyadicUMD),
   ("Cassese Prop 2.7 (5) (Yaroslavtsev, assumed)", ``Cassese.YaroslavtsevComplexUMD),
   ("Cassese Prop 2.7 (6) (HNVW, Yaroslavtsev, assumed)", ``Cassese.HNVWZigZag),
   ("Cassese Prop 2.8 (Cox–Veraar, assumed)", ``Cassese.CoxVeraarDecoupling),
   ("Cassese Lemma 4.1", ``Cassese.lemma4_1),
   ("Cassese Prop 4.1", ``Cassese.proposition4_1),
   ("Cassese Prop 4.1 (nonnegativity)", ``Cassese.proposition4_1_nonneg),
   ("Cassese Eq. (10)", ``Cassese.equation10),
   ("Cassese Section 4.2 (UMD of ℓ_q)", ``Cassese.umdEllq_lt_top),
   ("Cassese Section 4.3 (limiting argument)", ``Cassese.twoByM_ratio_le_qcThreshold),
   ("Cassese Lemma 4.2", ``Cassese.lemma4_2),
   ("Cassese Eqs. (13), (14) (Burkholder, cited)", ``External.Burkholder.scalarFunction_holds),
   ("Cassese Prop 4.2", ``Cassese.proposition4_2),
   ("Cassese Prop 4.2 (the minorant)", ``Cassese.proposition4_2_minorant),
   ("Cassese Section 4.3 (limiting argument, for f_n)", ``Cassese.twoByM_not_qc_explicitF),
   ("Cassese Prop 4.3", ``Cassese.proposition4_3),
   ("Cassese Remark 4.5 (Thm 1.2, elementary route)", ``Cassese.theorem1_2_elementary),
   ("Cassese Prop 5.1", ``Cassese.proposition5_1),
   ("Cassese Section 5.1 (q rank-one convex on 𝓛)", ``Cassese.quarticQ_rankOneConvexOn_calL),
   ("Cassese Section 5.2 (q₃ rank-one convex on 𝓛₃)", ``Cassese.q3_rankOneConvexOn_L3),
   ("Cassese Eq. (24)", ``Cassese.equation24),
   ("Cassese Prop 5.2", ``Cassese.proposition5_2),
   ("Cassese Lemma 5.1 (1)", ``Cassese.lemma5_1_part1),
   ("Cassese Lemma 5.1 (1), with constants", ``Cassese.lemma5_1_part1_quant),
   ("Cassese Lemma 5.1 (2)", ``Cassese.lemma5_1_part2),
   ("Cassese Proof of Thm 1.3 (κ = 2)", ``Cassese.tbt_correction_identity),
   ("Cassese Proof of Thm 1.3 (κ = 2)", ``Cassese.L3_rankOneCorrection),
   ("Cassese Proof of Thm 1.3 (q_{δ,K/δ} rank-one convex)", ``Cassese.qDeltaLambda_rankOneConvex),
   ("Cassese Proof of Thm 1.3 (a) (the witness)",
    ``Cassese.twoByThree_not_quasiconvexAt_qDeltaLambda),
   ("Cassese Proof of Thm 1.3 (b) (the witness)", ``Cassese.twoByThree_theorem1_3_b_witness),
   ("Cassese Cor 5.2", ``Cassese.corollary5_2),
   ("Cassese Cor 5.3", ``Cassese.corollary5_3),
   ("Cassese Cor 5.4", ``Cassese.corollary5_4),
   ("Cassese Prop 6.1", ``Cassese.proposition6_1),
   ("Cassese Prop 6.2", ``Cassese.proposition6_2),
   ("Cassese Prop 6.3 (Pisier–Xu, assumed)", ``Cassese.PisierXuKhintchine),
   ("Cassese Prop 6.4 (Kahane–Khintchine, assumed)", ``Cassese.KahaneKhintchine),
   ("Cassese Eq. (31)", ``Cassese.equation31),
   ("Cassese Remark 6.3", ``Cassese.remark6_3),
   ("Cassese Prop 6.5", ``Cassese.proposition6_5),
   ("Cassese Prop 6.5 (q < ∞)", ``Cassese.proposition6_5_finite),
   ("Cassese Prop 6.5 (q = ∞)", ``Cassese.proposition6_5_infty),
   ("Cassese Cor 6.1", ``Cassese.corollary6_1),
   ("Cassese Cor 6.1 (every large d)", ``Cassese.corollary6_1_ge),
   ("Cassese Proof of Cor 6.1 (periodic Hessian test maps)",
    ``Cassese.not_hessianQuasiconvexAt_of_periodic),
   ("Cassese Proof of Cor 6.1 (periodic Hessian test maps)",
    ``Cassese.square_not_hessianQuasiconvexAt_of_periodic),
   ("Cassese Prop 6.6", ``Cassese.proposition6_6),
   ("Cassese Thm 6.2", ``Cassese.theorem6_2),
   ("Cassese Cor 6.3 (lower bound)", ``Cassese.corollary6_3_lower),
   ("Cassese Cor 6.3 (upper bound)", ``Cassese.corollary6_3_upper),
   ("Cassese Cor 6.3 (separation)", ``Cassese.corollary6_3_separation),
   ("Cassese Cor 6.4", ``Cassese.corollary6_4),
   ("Cassese Cor 6.4 (not quasiconvex)", ``Cassese.corollary6_4_not_quasiconvexAt),
   ("Cassese Thm 1.4, p = 4 (Section 6.4)", ``Cassese.theorem1_4_four),
   ("Cassese Prop 7.1", ``Cassese.proposition7_1),
   ("Cassese Prop 7.2", ``Cassese.proposition7_2),
   ("Cassese Prop 7.2 (lower bound)", ``Cassese.proposition7_2_lower),
   ("Cassese Thm 7.1", ``Cassese.theorem7_1),
   ("Cassese Cor 7.2", ``Cassese.corollary7_2),
   ("Cassese Conjecture 1 (stated)", ``Cassese.Conjecture1)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``PedregalChallenge.corollary7_2_false, ``PedregalChallenge.exists_T_eq_empty,
   ``PedregalChallenge.theorem1_1_of_nonempty, ``PedregalChallenge.theorem1_1_part1_levelOne,
   ``PedregalChallenge.mem_T_self,
   ``PedregalChallenge.card_C,
   ``SverakChallenge.theorem_main, ``SverakChallenge.corollary,
   ``SverakChallenge.remark_polynomial,
   ``CasseseChallenge.theorem1_2, ``CasseseChallenge.theorem1_3_a,
   ``CasseseChallenge.theorem1_3_b, ``CasseseChallenge.theorem1_4,
   ``CasseseChallenge.theorem1_4_four, ``CasseseChallenge.theorem1_5,
   ``CasseseChallenge.corollary1_6, ``CasseseChallenge.corollary5_3,
   ``CasseseChallenge.morrey_landscape, ``CasseseChallenge.homMorrey_landscape,
   ``CasseseChallenge.projL3_mem]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the libraries: the papers', `External` or `Basic`. -/
meta def isLibraryModule (m : Name) : Bool :=
  (`Morrey).isPrefixOf m || (`Pedregal).isPrefixOf m || (`Sverak).isPrefixOf m ||
    (`Cassese).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
