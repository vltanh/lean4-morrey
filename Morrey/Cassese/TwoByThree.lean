module

public import Morrey.Cassese.TwoByThree.Basic
public import Morrey.Cassese.TwoByThree.Witness
public import Morrey.Cassese.TwoByThree.ExtensionOne
public import Morrey.Cassese.TwoByThree.Extension
public import Morrey.Cassese.TwoByThree.Transpose
public import Morrey.Cassese.TwoByThree.WitnessCutoff
public import Morrey.Cassese.TwoByThree.NearFour
public import Morrey.Cassese.TwoByThree.Hessian
public import Morrey.Cassese.TwoByThree.HessianCutoff
public import Morrey.Cassese.TwoByThree.Folklore
public import Morrey.Common.External.Dacorogna.Minors
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Section 5: the problem in dimension `2 × 3`

The objects of Sections 5.1–5.2 that Corollary 5.3 names (`wirtAlpha`, `wirtBeta`, `zCoord`,
`quarticQ`, `calL`, `embedJ`, `L3`, `q3`, `projL3`, `qDeltaLambda`, `qHat`) are in the shared block
of `Morrey/Cassese/Defs.lean`. In this section `|·|` is the Frobenius norm (`frobNorm`) and
`⟨A, B⟩ = Σ A_{ij} B_{ij}` the Frobenius inner product (`frobInner`).

This module re-exports the submodules of Section 5:

* `TwoByThree.Basic`: `frobInner`, `frobNorm`, `IsFrobProj`, `HasRankOneCorrection`, `L3Submodule`;
  `quarticQ_rankOneConvexOn_calL` (`cs-q-rc`), `q3_rankOneConvexOn_L3` (`cs-q3-rc`), `equation24`
  (`eq:q-simp`), `L3_rankOneCorrection` and `hasRankOneCorrection_L3` (`cs-kappa`);
* `TwoByThree.Witness`: `proposition5_2` (`prop:qc-witness`);
* `TwoByThree.ExtensionOne` (with `TwoByThree.Rademacher`): `lemma5_1_part1` and its quantitative
  form `lemma5_1_part1_quant` (`lem:extension-from-subspace`);
* `TwoByThree.Extension` (with `TwoByThree.ExtensionAux`): `lemma5_1_part2`
  (`lem:extension-from-subspace`) and `qDeltaLambda_rankOneConvex` (`cs-qdl-rc`);
* `TwoByThree.Polynomial`: `q₃` and `q_{δ,Λ}` are homogeneous quartic polynomials;
* `TwoByThree.Transpose` (with `TwoByThree.Transpose.*`): `corollary5_3` (`cor:transp`);
* `TwoByThree.WitnessCutoff`: `twoByThree_not_quasiconvexAt_qDeltaLambda` (`cs-thm1.3a-witness`,
  the cutoff of Proposition 5.2's witness in the proof of Theorem 1.3 (a));
* `TwoByThree.NearFour`: `twoByThree_theorem1_3_b_witness` (`cs-thm1.3b-witness`, the proof of
  Theorem 1.3 (b));
* `TwoByThree.Hessian`, `TwoByThree.HessianCutoff`: `hessB` and `corollary5_4`
  (`cor:hessian-quartic`);
* `TwoByThree.Folklore` (with `TwoByThree.Folklore.*`): `proposition5_1` (`cs-prop5.1`).

Statements not numbered in the paper: the claims of Sections 5.1–5.2 that `q` and `q₃` are
rank-one convex on `𝓛` and `𝓛₃` (`cs-q-rc`, `cs-q3-rc`); equation (24) (`eq:q-simp`); and the
claims of the proof of Theorem 1.3, that `𝓛₃` satisfies (25) with `κ = 2` (`cs-kappa`, asserted
without proof in the paper), that `q_{δ, K/δ}` is rank-one convex (`cs-qdl-rc`), and the two
witnesses (`cs-thm1.3a-witness`, `cs-thm1.3b-witness`).
-/
