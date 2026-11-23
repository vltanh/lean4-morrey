# Cassese (2026) in Lean: audit report

Paper: G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*,
[arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3) (16 September 2026), a preprint. The
audit was made against the arXiv LaTeX source of that version. Section, result and equation numbers
are the paper's, and "lines" are lines of its TeX source. Labels in backticks are the paper's TeX
labels; labels `cs-…` are ours, for results the paper does not label
([`paper_routes.tsv`](paper_routes.tsv)). The main theorems are numbered 1.2–1.5 because
Theorem 1.1 is Kirchheim and Kristensen's cited theorem. The repository also formalizes Šverák
(1992) and audits Pedregal's claimed `2 × 2` proof ([overview](../../README.md)). This
formalization was written independently of the author's own Lean code, which its proofs did not
consult (Section 10, "Formalizations").

Status of the formalization:

- **Every result of the paper is proved**: Theorems 1.2–1.5, Corollary 1.6, the consequences
  drawn after Theorem 1.3 (only `2 × 2` remains, for Morrey's problem and, at `p = 4`, for the
  homogeneous problem), every numbered lemma, proposition and corollary (Proposition 2.6, quoted
  from Osękowski as context, aside), and the claims of the running text that the proofs use. Theorem 1.2 is proved by the paper's own route (Section 4.4,
  through UMD constants); the elementary route of Remark 4.5 is formalized as a second theorem,
  [`theorem1_2_elementary`](../../Morrey/Cassese/TwoByM.lean#L3480).
- **The results of other works that the proofs use are proved too.** Each is stated, in its
  source's terms or as the paper quotes it, in `Morrey/Common/External/<Source>/`, and in the paper's
  terms in
  [`Morrey/Cassese/Hypotheses.lean`](../../Morrey/Cassese/Hypotheses.lean). The proofs come from three Lake packages written for this
  formalization: [lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis),
  [lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability) and
  [lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations), which
  [`lakefile.toml`](../../lakefile.toml) pins by commit.
- **Nothing is assumed.** No statement takes a result of another work as a hypothesis. Two cited
  theorems that the paper quotes only as context, Kirchheim–Kristensen's Theorem 1.1 and
  Osękowski's characterization of Hilbert spaces (Proposition 2.6), are stated and not proved; no
  proof uses them. Conjecture 1 is stated.
- `lake build` passes, with no `sorry` outside the Challenges and no `axiom`.
  [`scripts/Audit.lean`](../../scripts/Audit.lean) checks that every declaration of the
  repository's library (3,380 at commit `ee3b66b`, for the three papers and the shared code) uses
  only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and lists the results of other works that
  each result of the paper uses (Section 8). Each package has an audit of the same kind.
- [`palomar/Cassese/Challenge.lean`](../../palomar/Cassese/Challenge.lean) states the main results
  in Mathlib's vocabulary, with no hypotheses beyond the paper's;
  [`Solution.lean`](../../palomar/Cassese/Solution.lean) proves them from the library, and
  Comparator compares the two ([`comparator.json`](../../palomar/Cassese/comparator.json)).
- No statement of the paper had to change (Section 4).
- Every proof follows the paper's argument, except three that repair a gap or a false step
  (Section 7). The cited results follow their sources' proofs, whose gaps and slips are repaired
  along the sources' lines (Section 7); Proposition 2.1 is proved by the paper's own second route.
  In the proof of the non-commutative Khintchine inequality (Proposition 6.3), steps that its sources
  take from works that were not read, only recall, or state without proof, follow named substitutes
  (Section 7).

## Contents

1. Summary
2. Results from prior work and how the paper uses them
3. Errors and gaps in the paper
4. Missing hypotheses
5. Redundant hypotheses
6. How the formalization reads the paper
7. Departures from the paper's proofs
8. What each result depends on
9. Not formalized
10. The paper in the literature
11. What's next

## 1. Summary

The paper constructs rank-one convex integrands on `ℝ^{2×m}`, `m ≥ 3`, that are nowhere
quasiconvex. With Šverák's theorem, this leaves `2 × 2` as the only size in which Morrey's problem
can have a positive answer. It also answers Kirchheim and Kristensen's homogeneous problem
negatively in many sizes: there are `p`-homogeneous, rank-one convex, nowhere quasiconvex
integrands. Its proofs rest on Burkholder's martingale inequalities, UMD theory for `L^p` and the
Schatten classes, the non-commutative Khintchine inequality, transference and Dragičević's lower
bound for the Beurling–Ahlfors transform, and the standard facts of the calculus of variations;
all are proved here.

The audit found no false statement. The findings are steps that the paper leaves to the reader or
only sketches, one intermediate claim that is false under the reading that the proof around it
needs, and misprints:

| Kind | Findings |
| --- | --- |
| Errors | none: no statement is false. One intermediate claim, at lines 661–663, is false under the reading of prelaminates that Proposition 2.4 needs (E10) |
| Gaps that change what must be proved | E4: Theorem 1.3 (b) needs the constants of Lemma 5.1 (1) uniform in `p`; E10: Proposition 2.5 "⇐" rests on the claim of lines 661–663 |
| Results stated without proof | E5: `κ = 2` for `𝓛₃`; E6: Proposition 6.6; E8: Proposition 2.3; E19: Corollary 5.2 |
| Proofs only sketched | E17: Corollary 5.3; E26: Remark 4.5; E31: Corollary 6.4 |
| Steps left to the reader | E2, E3, E7, E9, E16, E21–E25, E28, E29, E32 (Corollary 7.2's "standard calculations"), E33–E35 (Section 3) |
| Claims without proof, not formalized | E18: Corollary 1.6 for `p > 2` |
| Not errors | E14: no value of `n₀` in Proposition 4.3; E20: `q₃(∇u) ∈ L¹` |
| Misprints and wording | E11, E12, E13, E15, E40–E42 |
| Missing hypotheses | none (Section 4) |
| Redundant hypotheses | eight, among them the evenness in Lemma 5.1 (2), which Remark 5.2 needs to drop, and `ρ > 0` in Proposition 7.2 (Section 5) |
| Use of cited results | correct, with reservations (Section 2). Applied loosely but correctly: Randrianantoanina's Corollary 4.5, Kristensen's growth bound, Dragičević's theorem for `p < 2` (E39), the theorems on UMD constants, which are for deterministic signs (E38), and the theorem behind Proposition 7.1, stated for complementary orthogonal projections (E42). Quoted inexactly: Dacorogna's Theorem 6.10 (E36), Osękowski's Theorem 3.24 (E37), Pisier–Xu's Theorem 6.1 (E40), and the theorem behind Proposition 6.4, whose bound on the constants the paper leaves out, and which Remark 6.3 and Proposition 6.5 at `q = ∞` use (E27). Used in part: the transference identity (E41). Source only hinted at: the sharpness of `p* − 1` (E30). Silent steps: Lemma 2.1 for the minorant `G` (E21), the nonempty domain of Lemma 2.2, Proposition 2.2 from the ball to the cube (E22), `UMD_p` for `UMD_{ℂ,p}` in Remark 4.2 (E11) |

## 2. Results from prior work and how the paper uses them

### Proved in `Morrey/Common/External/`

Each result is stated, in its source's terms or as the paper quotes it, in
`Morrey/Common/External/<Source>/`, whose README gives the source, the statement, the argument and
the users, and is proved there from the packages named in the last column: HA = `lean4-harmonic-analysis`, BP = `lean4-banach-probability`,
CV = `lean4-calculus-of-variations`. Section 7 says how each source was read, which module follows
it and where the proof differs.

| Result | Where the paper uses it | Source cited by the paper | Lean |
| --- | --- | --- | --- |
| Lemma 2.1: a rank-one convex function is locally Lipschitz | implicit uses (the paper never cites it): Propositions 2.3–2.5, Corollary 1.6 | Rindler 2018, Lemma 5.6 | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) (CV) |
| Lemma 2.2: quasiconvexity implies rank-one convexity, does not depend on the domain, and may be tested with periodic maps | Proposition 2.3, the thresholds, the lifting, Propositions 6.1, 7.2 | Rindler 2018, Propositions 5.1, 5.3 (numbers not checked: the first edition was not obtained, and the second one's Proposition 5.1 is another result); Dacorogna 2008, Propositions 5.11, 5.13 | [`External.Rindler.rankOneConvex_of_quasiconvex`](../../Morrey/Common/External/Rindler/Lemmas.lean#L88), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128) (CV) |
| Proposition 2.1: the rank-one convex envelope by prelaminates | Propositions 2.3, 5.1 | Pedregal 1993, §4; Dacorogna 2008, Theorem 6.10 | [`proposition2_1`](../../Morrey/Cassese/Toolkit.lean#L780), in the library, by the paper's own route of Remark 2.1 (through Proposition 2.4) |
| Proposition 2.2: Dacorogna's formula for the quasiconvex envelope | line 559, Propositions 2.3, 4.3 | Kinderlehrer–Pedregal 1991, Proposition 8.1 | [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) (CV) |
| Theorem 2.3 (1): Burkholder's inequality, Hilbert-valued | Lemma 5.1 (1) and (2), Theorem 1.3 (a) and (b), Proposition 7.1 | Osękowski 2012, Theorem 3.5 | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), from [`External.Osekowski.theorem3_5`](../../Morrey/Common/External/Osekowski/Inequality.lean#L68) (the book's form) (BP) |
| Theorem 2.3 (2): Burkholder's square function inequality | Proposition 6.5 | Osękowski 2012, Theorem 8.6 | [`External.Osekowski.squareFunction`](../../Morrey/Common/External/Osekowski/Inequality.lean#L119), from [`External.Osekowski.theorem8_6`](../../Morrey/Common/External/Osekowski/Inequality.lean#L106) (BP) |
| Proposition 2.7 (1): extrapolation of the UMD property, with constants | Section 4.2 (for Theorem 1.2), Proposition 6.5, Corollary 6.1 | HNVW I, Theorem 4.2.7 | [`External.HNVW.theorem4_2_7`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L55); the book's form, [`External.HNVW.theorem4_2_7_general`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L46) (BP) |
| Proposition 2.7 (2): `UMD₂(S_q) ≤ C (q* − 1)` | Propositions 6.2, 6.5, Remark 6.3 | Randrianantoanina 2002, Corollary 4.5 | [`External.Randrianantoanina.remark4_6`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L67), with [`External.Randrianantoanina.corollary4_5`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L49) (BP) |
| Proposition 2.7 (3): `L^p` is UMD | Section 4.2 (Theorem 1.2) | Pisier 2016, Corollary 5.22 | [`External.Pisier.corollary5_22`](../../Morrey/Common/External/Pisier/LpUMD.lean#L40) (BP) |
| Proposition 2.7 (4): the dyadic and the general UMD constants agree | no proof | HNVW I, Theorem 4.2.5 | [`External.HNVW.theorem4_2_5`](../../Morrey/Common/External/HNVW/DyadicUMD.lean#L39) (BP) |
| Proposition 2.7 (5): `UMD_p ≤ UMD_{ℂ,p} ≤ (π/2) UMD_p` | Section 4.2 (Theorem 1.2) | Yaroslavtsev 2018, Lemma 3.2 | [`External.Yaroslavtsev.lemma3_2`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean#L54) (BP) |
| Proposition 2.7 (6): `X` is `UMD_p` if and only if there is a zig-zag concave function, whose `β` then bounds `UMD_p` and, for complex `X`, `UMD_{ℂ,p}` | no proof | HNVW I, Theorem 4.5.6; Yaroslavtsev 2018, Proposition 3.7 | [`External.HNVW.theorem4_5_6`](../../Morrey/Common/External/HNVW/ZigZag.lean#L52), with the book's final clause [`External.HNVW.theorem4_5_6_isLeast`](../../Morrey/Common/External/HNVW/ZigZag.lean#L63); for complex `X`, [`External.Yaroslavtsev.proposition3_7_iff`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean#L71), [`External.Yaroslavtsev.proposition3_7`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean#L63) and [`External.Yaroslavtsev.lemma3_2`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean#L54) (BP) |
| Proposition 2.8: decoupling with the UMD constant | Propositions 6.2, 6.5, Remark 6.3 | Cox–Veraar 2007; HNVW I, Proposition 4.2.3 | [`External.CoxVeraar.decoupling`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean#L51) (BP) |
| (13), (14): Burkholder's function `u`; the function `u_q` behind Remark 4.5's "such a `U` can also be constructed" | Propositions 4.2, 4.3; Remark 4.5 | Burkholder 1988 (for `u`) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L142), [`External.Burkholder.scalarFunctionQ_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L123) (BP) |
| rank-one affine functions are affine combinations of minors (no continuity assumed), and minors are quasiaffine | Proposition 5.1 | Dacorogna 2008, Theorem 5.20 | [`External.Dacorogna.rankOneAffineMinors_holds`](../../Morrey/Common/External/Dacorogna/Minors.lean#L75), [`External.Dacorogna.minor3_quasiaffine`](../../Morrey/Common/External/Dacorogna/Minors.lean#L87) (CV) |
| rank-one convex quadratic forms are quasiconvex | Proposition 5.1 | Dacorogna 2008, Theorem 5.25 (i) | [`External.Dacorogna.quadraticForm_quasiconvex`](../../Morrey/Common/External/Dacorogna/Minors.lean#L104) (CV) |
| a smoothing that keeps the failure of quasiconvexity | Corollary 5.2 | Kristensen 1999, Proposition 2; Heinz 2008 | [`External.Kristensen.smoothing_holds`](../../Morrey/Common/External/Kristensen/Smoothing.lean#L106) (CV) |
| Proposition 6.3: the non-commutative Khintchine inequality | (31) | Pisier–Xu 2003, Theorem 6.1; Lust-Piquard 1986; Lust-Piquard–Pisier 1991 | [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74), with [`External.PisierXu.theorem6_1_general`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L59) (every real square matrix, not only the normal ones) (HA, with BP) |
| Proposition 6.4: the Kahane–Khintchine inequality | (31) | HNVW II, Theorem 6.2.4 | [`External.HNVW.theorem6_2_4_seminorm`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L58) (BP) |
| the constants `κ_{q,p} ≤ √((q − 1)/(p − 1))` | Remark 6.3, Proposition 6.5 at `q = ∞` | HNVW II, Theorem 6.2.4, through Proposition 6.4, which leaves them out (E27) | [`External.HNVW.theorem6_2_4_hypercontractive`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L48) (BP) |
| the sharpness of `p* − 1` for dyadic `±1`-transforms | Corollary 6.3, lower bound | "see also [Cassese 2025]" (E30), that is Burkholder 1984, Theorem 14.1, and Osękowski 2012, Theorem 3.5 with Remark 3.8 and p. 138 | [`External.Osekowski.exists_lt_lpNorm_transform`](../../Morrey/Common/External/Osekowski/Sharpness.lean#L82) (BP) |
| the bound `C^{rc} ≤ (p* − 1) sup ‖Q‖/‖P_ρ‖` | Proposition 7.1 | "the results of [Cassese 2025]" | from Burkholder's inequality, in [`proposition7_1`](../../Morrey/Cassese/FourByTwo.lean#L344) |
| transference: `‖𝓑^k‖_{L^p(ℝ²)} ≤ ‖𝓑^k‖_{L^p_0(𝕋²)}` | Proposition 7.2, lower bound | HNVW I, Corollary 5.7.6 | [`External.HNVW.transference_beurlingPow`](../../Morrey/Common/External/HNVW/Transference.lean#L56) (HA) |
| Dragičević's lower bound `‖𝓑²‖_p ≥ κ₂(p*) > p* − 1`, with `κ₂(p) = (p − 1)(2p − 1)/(p + 1)`, and `‖𝓑²‖₄ ≥ 21/5` | Theorem 7.1, Corollary 7.2 | Dragičević 2011, Theorem 1.1 (for `p > 2`); "see also" Carbonaro–Dragičević–Kovač 2023 | [`External.Dragicevic.theorem1_1_two_pStar`](../../Morrey/Common/External/Dragicevic/LowerBound.lean#L64), [`External.Dragicevic.theorem1_1_two`](../../Morrey/Common/External/Dragicevic/LowerBound.lean#L52) (HA) |

Quoted for context, stated and not proved, used by no proof: Kirchheim–Kristensen 2016 (the
paper's Theorem 1.1, [`External.KirchheimKristensen.Theorem1_1`](../../Morrey/Common/External/KirchheimKristensen/Theorem.lean#L25)) and Osękowski 2012, Theorem 3.24
(Proposition 2.6, [`External.Osekowski.HilbertCharacterization`](../../Morrey/Common/External/Osekowski/HilbertCharacterization.lean#L48); E37).

### Assumed

Nothing.

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| the Schatten-norm facts (1)–(3) of Section 1.5, "immediate consequences of the definitions (see also [Bhatia, Chapter 4])", and, with no source, the triangle inequality | Section 6 | proved: [`schattenNorm_mul_self`](../../Morrey/Cassese/Square.lean#L196) (fact (1), for every `q ≥ 1`: E2; Bhatia's (IV.49)), fact (2) from the definition, Weyl's monotonicity for fact (3) as in Bhatia's second proof of his Corollary III.2.3 ([`Morrey/Cassese/Square/Weyl.lean`](../../Morrey/Cassese/Square/Weyl.lean)), [`schattenNorm_add_le`](../../Morrey/Cassese/Square.lean#L441) (BP's, after Bourin–Zhang, arXiv:2610.30538, Proposition 3.13; Section 7) |
| the Bernstein–Doetsch theorem: a midpoint convex function, locally bounded above, is convex | lines 643–646 (Proposition 2.4) | proved, in `tk_midpoint_principle` |
| the uniform convexity of `\|·\|^p` | (29) | proved, [`tbt2_gain`](../../Morrey/Cassese/TwoByThree/ExtensionAux.lean#L526) (E3) |
| the strong law of large numbers with infinite mean, Fatou's lemma, Jensen's inequality | Lemma 4.2 | Mathlib, in [`lemma4_2`](../../Morrey/Cassese/TwoByM.lean#L1585) |
| mollification of continuous and of Lipschitz functions | Propositions 4.2, 7.2, Remark 4.5, Corollary 1.6 | [`Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean`](../../Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean); `CalculusOfVariations.mollifyPi` (CV) |
| the implicit function theorem; the change of variables `(ζ, τ) ↦ (w, t)` | Proposition 5.2 | Mathlib's `ContDiffAt.implicitFunction`; the change of variables is proved in [`Morrey/Cassese/TwoByThree/Witness.lean`](../../Morrey/Cassese/TwoByThree/Witness.lean) |
| Hölder's inequality; polar coordinates | Theorem 1.3 (a), Corollaries 5.3, 5.4 | Mathlib |
| the multinomial theorem and the orthogonality of the characters of the torus | Proposition 6.1 | Mathlib, in [`Morrey/Cassese/Square/Torus.lean`](../../Morrey/Cassese/Square/Torus.lean) |
| Fourier series of smooth periodic functions; `∂̄` is invertible on smooth mean-zero functions; `𝓑(∂̄w) = ∂w` | Proposition 7.2 | HA (`UnitAddTorus.exists_dzbarPi_eq`, `periodicMultiplier_beurlingSymbol_dzbarPi`) |
| distributional second derivatives on `ℝ`: the Leibniz rule, and convexity from a nonnegative second derivative | Corollary 1.6 | CV (`CalculusOfVariations.convexOn_of_distribNonneg`) |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Theorem 2.3 (Burkholder) | Sections 5–7 | correct. The paper asks for a separable Hilbert space; the proofs do not use separability (Section 5) |
| (13), (14) (Burkholder's `u`) | Proposition 4.2 | correct |
| Lemma 2.1 (Rindler) | implicit uses (the paper never cites it): Propositions 2.3–2.5, Corollary 1.6 | correct. The paper uses the minorant `G` of Propositions 2.4 and 2.5 as a competitor without showing that it is an integrand; Lemma 2.1 for every real-valued rank-one convex function, proved here, supplies this (E21); Rindler's definition of rank-one convexity includes local boundedness and Borel measurability |
| Lemma 2.2 (Rindler, Dacorogna) | Sections 2, 4, 6, 7 | correct; the domain must be nonempty, which the paper does not say |
| Proposition 2.1 (Pedregal, Dacorogna) | Propositions 2.3, 5.1 | correct; Remark 2.1 says that the sources assume `f` bounded below, where Dacorogna's Theorem 6.10 asks only for a rank-one convex minorant (E36) |
| Proposition 2.6 (Osękowski, Theorem 3.24) | no proof | quoted with more than the source proves: the bound on the Banach–Mazur distance is not in it (E37) |
| Proposition 2.2 (Kinderlehrer–Pedregal) | line 559 | correct; the passage from the ball of the formula to the cube of Definition 2.1 is silent (E22) |
| Dacorogna, Theorems 5.20 and 5.25 (i) | Proposition 5.1 | correct |
| Kristensen, Proposition 2 | Corollary 5.2 | applied loosely but correctly: the paper's form asks `c ‖A‖² ≤ h(A)` for every `A`, which Kristensen's function need not satisfy, since the cut-off polynomial can be negative; adding a constant repairs it and changes neither the second derivatives nor quasiconvexity at `0` |
| Proposition 2.7 (1), (3)–(6) | Section 4.2 (for Theorem 1.2); (4), (6) in no proof | applied loosely but correctly: the sources' constants are for deterministic signs or multipliers, the paper's for predictable ones, and HNVW I, Theorem 4.2.25, which shows that they agree, is not cited (E38). Remark 4.2 writes `UMD_p` where the argument gives `UMD_{ℂ,p}`, harmless under `≲` (E11) |
| Proposition 2.7 (2) (Randrianantoanina) | Propositions 6.2, 6.5 | applied loosely but correctly: Corollary 4.5 bounds `UMD_q(S_q)` by `C q²/(q − 1)`; the bound at the exponent `2`, linear in `q*`, is the source's Remark 4.6 (1), through extrapolation; the source's constants are for deterministic signs (E38) |
| Proposition 2.8 (Cox–Veraar, HNVW) | Propositions 6.2, 6.5 | correct; the case used is the Paley–Walsh case of Cox–Veraar's statement |
| Propositions 6.3, 6.4 | (31) | correct; the order `√q` in Proposition 6.3 is not in Pisier–Xu's Theorem 6.1 but in the remark after it (E40); Proposition 6.4 leaves out the constants of the theorem it cites, which Remark 6.3 and Proposition 6.5 at `q = ∞` use (E27) |
| the sharpness of `p* − 1` | Corollary 6.3 | correct, with only "see also [Cassese 2025]" as a source (E30) |
| Cassese 2025 | Proposition 7.1 | applied loosely but correctly: its Theorem 2.1 is stated for the orthogonal projections onto a subspace and its complement, which `P_ρ` and `Q` are not; the proof carries over (E42) |
| transference (HNVW I, Corollary 5.7.6) | Proposition 7.2 | correct: the corollary states that the three norms are equal, and the proof uses one inequality, from `L^p_0(𝕋²)` to `L^p(ℝ²)` (E41) |
| Dragičević, Theorem 1.1 | Theorem 7.1, Corollary 7.2 | applied loosely but correctly: the theorem is stated for `p > 2` (the article's standing assumption, p. 464); for `p < 2` it follows from the duality `‖𝓑^n‖_p = ‖𝓑^n‖_{p'}` of Carbonaro–Dragičević–Kovač, §1.3.1, the paper's "see also [Dragicevic1]"; and `κ₂(p*) − (p* − 1) = (p* − 1)(p* − 2)/(p* + 1) > 0` for `p* > 2` (E39) |

The other citations give context and are used in no proof: the history of Morrey's problem and of
Burkholder's method in the calculus of variations (Sections 1, 2 and 8, Remarks 2.3 and 3.1),
Grabovsky's examples, Gennaioli–Rindler, Guerra–Kristensen, and the literature on Iwaniec's
conjecture.

## 3. Errors and gaps in the paper

No statement was found false. The items below are gaps (steps that need an argument the paper does not
give, or only sketches), one intermediate claim that is false under a natural reading (E10),
citations that say more or less than their sources, and misprints, collected at the end. The numbers
are those of the inventory of the paper, which the docstrings of the code cite; E1 of the inventory is
the remark on numbering in the preamble, not a finding, and E35–E42 are not in the inventory. In every
case but two the result holds and the formalization supplies the missing argument; E18 and E37
(claims that no proof uses) are not proved here.

### E2. Lines 375–377, 2350–2378: Schatten fact (1)

Fact (1) of Section 1.5, `‖A²‖_{S_q} = ‖A‖²_{S_{2q}}` for self-adjoint `A`, is stated for `q ≥ 2`,
but the proof of Proposition 6.2 uses it at the exponent `q/2`, below `2` when `q < 4`. The
identity holds for every `q ≥ 1`, since the singular values of `A²` are the squares of those of
`A`. The formalization proves it for `q ≥ 1` ([`schattenNorm_mul_self`](../../Morrey/Cassese/Square.lean#L196)).

### E3. Lines 1914–1929: Lemma 5.1 (2), inequality (28)

Comparing `E f(π M_n)` with `E f(M̃_n)` needs the first-order cancellation
`E [Df(X) · 𝓔_n] = 0` (`𝓔` is a martingale started at `0`, and `X = π M_0` is deterministic), which
the paper does not mention; without it a term `|X|^{p−1} E |𝓔_n|` appears that (28) does not
contain. The remainder also needs a Lipschitz bound on `Df` across the origin,
`‖Df(Y) − Df(Y')‖ ≤ C max(|Y|, |Y'|)^{p−2} |Y − Y'|`, which follows from the `C²` regularity and the
homogeneity. Both are supplied in [`lemma5_1_part2`](../../Morrey/Cassese/TwoByThree/Extension.lean#L276), which follows the paper's `n`-step argument;
(29), "uniform convexity of `|·|^p`", neither proved nor cited in the paper, is proved there too.

### E4. Lines 2031–2046: Theorem 1.3 (b)

The proof of (b) says that "the result follows by extending it via Lemma 5.1 (1) and continuity of
the rank-one convexity and quasiconvexity estimates for `f`", the continuity being in `p`. This
needs the constant `Λ` of Lemma 5.1 (1), which is stated for a fixed `p`, to be uniform for
`p` near `4`, and the cut-off of the witness to be fixed before `p` varies: for `p < 4` the
uncut integrand is positive far away, since `r* − 1 > 1` and `|H|/|2D| → 1`. The theorem holds:
the formalization proves Lemma 5.1 (1) with explicit constants ([`lemma5_1_part1_quant`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L324)), so that
`Λ₀(p, δ)` is continuous in `p`, fixes `K`, `δ` and the cut-off first, and passes to the limit in
`p` by dominated convergence ([`twoByThree_theorem1_3_b_witness`](../../Morrey/Cassese/TwoByThree/NearFour.lean#L860); Section 7).

### E5. Lines 1978–1979: `κ = 2` for `𝓛₃`

"`𝓛₃` satisfies the hypothesis of Lemma 5.1 with `κ = 2`" has no proof. It is true: for
`R = v wᵀ`, the correction `R_L = x v uᵀ`, `u = (v₀² − v₁², 2 v₀ v₁, |v|²)`,
`x = ⟨w, u⟩/(2 |v|⁴)`, lies in `𝓛₃` and gives `|π R − R_L|² ≤ 2 |π^⊥ R|²`, so even `κ = √2`
([`tbt_correction_identity`](../../Morrey/Cassese/TwoByThree/Basic.lean#L459)); numerically the best constant is about `1.054`. When `⟨w, u⟩ = 0`, a
small `x ≠ 0` keeps `R_L` of rank one, and `κ = 2` covers it ([`L3_rankOneCorrection`](../../Morrey/Cassese/TwoByThree/Basic.lean#L481)).

### E6. Lines 2558–2563: Proposition 6.6

Proposition 6.6 has no proof. It is correct: for `u_i = Σ_{j≠i} cos(x_i − x_j)`, exact
trigonometric moments give `E ‖Skew ∇u‖⁴_{S_4} = d(d − 1)(d² − d + 1)/8` and
`E ‖Sym ∇u‖⁴_{S_4} = d(d − 1)(6d − 9)/8`. Proved in [`proposition6_6`](../../Morrey/Cassese/Square.lean#L2752).

### E7. Lines 2683–2684: Corollary 6.4

The bound `⟨W, Z⟩ ≤ (1/3)(2ae + 2bc) + (2/3)(2aρ)` does not follow "by the assumption on
`(E, D)`", which gives only `a ≤ b`, `c ≤ e`. It holds by a trace argument,
`tr(YEXD) = −⟨YD, EX⟩ ≤ bc` and `tr(YEDX) = ⟨XD, YE⟩ ≤ ae`, together with
`⟨W, Z⟩ ≤ ‖W‖ ρ ≤ 2aρ`. Supplied in [`corollary6_4`](../../Morrey/Cassese/Square.lean#L3475).

### E8. Lines 562–578: Proposition 2.3

Proposition 2.3 has no proof ("follows directly"). The formalization splits it into (a), the
dichotomy `≡ −∞` or finite and the homogeneity of the envelopes; (b), the invariances; (c), the
equivalence at `0` (the paper's statement has no item labels). The conjugation invariance of
`f^{qc}` in (b) needs Dacorogna's formula (Proposition 2.2), and the direction "`f` quasiconvex at
`0` ⇒ `f^{rc}` quasiconvex at `0`" of (c) needs line 559 and Lemma 2.2; what the main theorems use
is elementary. Proved: (a) and (b) from the dual formulas of the envelopes, (c) through line 559
([`proposition2_3_a`](../../Morrey/Cassese/Toolkit.lean#L1286), [`proposition2_3_b`](../../Morrey/Cassese/Toolkit.lean#L1458), [`proposition2_3_c`](../../Morrey/Cassese/Toolkit.lean#L1565)).

### E9. Lines 1406–1411: Proposition 5.1

Two steps are skipped: "`Q` is rank-one affine at `0`. It follows that `Q` is rank-one affine", and
"Since `P''(0) = (P − Q)''(0)`, the quadratic polynomial `P − Q` is rank-one convex". Both hold: a
prelaminate centred at `0` with an atom at an arbitrary `A`, split once more along `±hR`, gives
`Q(A + hR) + Q(A − hR) = 2 Q(A)`, and the same device gives the Legendre–Hadamard condition for
the quadratic part. Supplied in [`proposition5_1`](../../Morrey/Cassese/TwoByThree/Folklore.lean#L260) (Section 7).

### E10. Lines 504–530, 661–663: prelaminates and Proposition 2.5

Definition 2.4 does not say whether the atoms `A_i` of `Σ c_i δ_{A_i}` are distinct, and neither
reading makes both Proposition 2.4 and Proposition 2.5 work. The gluing in the proof of
Proposition 2.4 ("a midpoint split followed by dyadic splittings at `B` and `C`") needs repeated
atoms: with distinct atoms, coinciding atoms of `μ_B` and `μ_C` are split together. With repeated
atoms, the claim of lines 661–663 that "a dyadic prelaminate has a representing martingale on the
uniform binary tree, so the coordinates `(ε_k)` are independent Rademacher variables" is false:
splitting a third of `δ₀` with `t = 1/2` gives the weight `1/6`, which is not dyadic. Only a reading on split trees makes both steps work. Proposition 2.5 still holds: the
formalization reads Definition 2.4 with repeated atoms and proves "⇐" by running the argument of
Proposition 2.4 on the infimum of `E f(M_N)` over rank-one Rademacher martingales
([`proposition2_5`](../../Morrey/Cassese/Toolkit.lean#L1935); Section 7).

### E14. Lines 1355–1366: Proposition 4.3

No value of `n₀` is given. Not an error: the proofs are existence proofs. With `p = 3`, `q = 6`,
Remark 4.2 bounds `C^{qc}(3, 6, n)` below by a multiple of `n^{1/30}`; if that multiple is about
`1`, passing `5⁴` needs `n > 625^{30} ≈ 7.6·10^{83}`, which suggests `n` of order `10^{84}`.

### E16. Lines 1821–1832: Lemma 5.1, hypothesis (25)

The hypothesis asks for a rank-one `R_L ∈ 𝓛`. When `π R = 0` the natural choice is `R_L = 0`,
which the hypothesis excludes; a rank-one `R_L` of small norm serves as well, as long as `𝓛`
contains a rank-one matrix, and the proof only uses increments of rank at most one. The
formalization keeps the hypothesis as stated ([`HasRankOneCorrection`](../../Morrey/Cassese/TwoByThree/Basic.lean#L51)), and meets it for `𝓛₃` with
`κ = 2` (E5).

### E17. Lines 2090–2102, 2121–2125: Corollary 5.3

The proof is a sketch: "Cutting off `φ` smoothly at radii `1` and `R`", and constants `c, C > 0`
that are only said to exist. The formalization completes it with explicit cut-offs and the
constants `c = 75/8`, `C = 4·10⁶`, `δ₀ = 75/(64·10⁶)` ([`corollary5_3`](../../Morrey/Cassese/TwoByThree/Transpose.lean#L197)); a numerical evaluation of
the paper's "direct calculation" gives the sharper `c ≈ 1029.8`, `C ≈ 62938`.

### E18. Lines 2956–2966: Corollary 1.6 for `p > 2`

The variant for `p > 2` (`N_p` and `G = Λ N_p + det(YᵀY)^{p/2} N_p^{1−3p} F`) is asserted ("a
similar construction goes through") without proof. `N_p` degenerates where `X` or `Y` vanishes,
so the rank-one convexity estimate is not a copy of the case `p < 2`. Not formalized.

### E19. Lines 2051–2065: Corollary 5.2

Corollary 5.2 has no proof, only references to smoothing arguments. Proved, by Kristensen's
smoothing applied to the quartic of Theorem 1.3 lifted to `ℝ^{2×m}` ([`corollary5_2`](../../Morrey/Cassese/NonLocality.lean#L32);
[`External.Kristensen.smoothing_holds`](../../Morrey/Common/External/Kristensen/Smoothing.lean#L106)).

### E20. Lines 1602–1614, 1995: `q₃(∇u) ∈ L¹`

Proposition 5.2 asserts `q₃(∇u) ∈ L¹(ℝ³)`, and the proof of Theorem 1.3 (a) uses it through
`I = ∫_{ℝ³} q₃(∇u) < 0`. It holds: the paper's formula gives `I ≈ −0.3636`, which a direct
quadrature confirms. Not an error. The formalization proves the integrability
([`proposition5_2`](../../Morrey/Cassese/TwoByThree/Witness.lean#L1327)) and follows the paper's proof of Theorem 1.3 (a), with `I` and Hölder's
inequality ([`twoByThree_not_quasiconvexAt_qDeltaLambda`](../../Morrey/Cassese/TwoByThree/WitnessCutoff.lean#L1030)). Theorem 1.3 (a) can avoid the
integrability (Section 11).

### E21. Lines 468–470, 616–659: the minorant `G` of Propositions 2.3–2.5

The minorant `G` is used as a competitor in `f^{rc}` (lines 643–658), so it must be an integrand,
and the paper does not say why it is one; Lemma 2.1, as the paper states it (for integrands), does
not apply before that is known. `G` is real-valued and rank-one convex, and a real-valued rank-one
convex function is locally Lipschitz without further assumptions: convexity in each entry gives the
local boundedness, which Rindler's definition of rank-one convexity asks for (with Borel
measurability), and then his proof applies. The formalization proves Lemma 2.1 in this generality
([`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71)).

### E22. Line 559: from the ball to the cube

Dacorogna's formula (Proposition 2.2) averages over the unit ball, and Definition 2.1 tests on the
unit cube; the passage, silent in the paper, needs the domain-independence clause of Lemma 2.2.
Supplied ([`quasiconvexAt_iff_exists_minorant`](../../Morrey/Cassese/Toolkit.lean#L1177), with [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109)).

### E23. Lines 1047–1053: the limiting argument of Section 4.3

The "straightforward limiting argument" from Schwartz test maps to Definition 2.1 is not given.
Proved: a cut-off of `u_n`, Fatou's lemma, and a rescaling into the unit cube
([`twoByM_ratio_le_qcThreshold`](../../Morrey/Cassese/TwoByM.lean#L3011), [`twoByM_not_qc_explicitF`](../../Morrey/Cassese/TwoByM.lean#L2602)).

### E24. Lines 1891–1895: Lemma 5.1 (1)

"By homogeneity and Young's inequality" needs a Lipschitz bound on `g`, which is only continuous.
Uniform continuity on a compact set and homogeneity give the estimate ([`lemma5_1_part1`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L436)).

### E25. Lines 1855, 1956, 1991: `δ = 1` in Lemma 5.1 (2)

Lemma 5.1 (2) is stated for `δ ∈ (0, 1)`, and the proof of Theorem 1.3 uses it for `0 < δ ≤ 1`.
Harmless: `q_{1,K} = q_{1/2,K} + ½ (|π A|² + K² |π^⊥ A|²)²`, a rank-one convex function plus a
convex one ([`qDeltaLambda_rankOneConvex`](../../Morrey/Cassese/TwoByThree/Extension.lean#L542)).

### E26. Lines 1367–1375: Remark 4.5

The elementary route to Theorem 1.2 is sketched without the function `U` or the constant `K`
("such a `U` can also be constructed"). Supplied: `q = p + 3`, `U = R^{p/q} − K B^{p/q}` with
Burkholder's `u_q`, `K = 2 (q − 1)^{p+1}/(p − 1)` ([`theorem1_2_elementary`](../../Morrey/Cassese/TwoByM.lean#L3480)).

### E27. Lines 2312–2321, 2425–2437, 2477–2479: Kahane–Khintchine constants

Remark 6.3, and Proposition 6.5 at `q = ∞` ("all the implied multiplicative constants in the above
inequalities are at most polynomial in `q`"), use (31) with constants that grow at most
polynomially in `q`. This needs the Kahane–Khintchine constants to grow so, and Proposition 6.4
gives only some constants `k_{p,q}`. The theorem that Proposition 6.4 cites, HNVW II, Theorem 6.2.4
(pp. 21–22), states the bound that is needed: `κ_{q,p} ≤ √((q − 1)/(p − 1))` for `1 < p < q < ∞` and
real signs. It is proved here by the book's proof
([`External.HNVW.theorem6_2_4_hypercontractive`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L48)). Theorem 1.4 uses Proposition 6.5 only at `q = 4`
and does not need it.

### E28. Lines 2807–2821, 915–919, 480–486: Proposition 7.2

The inequality "`≤`" is argued with smooth periodic maps, while Lemma 2.2 tests with Lipschitz
periodic maps; the density step between them is not stated. It holds: the mollification of a
Lipschitz periodic map is smooth and periodic, its gradients converge almost everywhere and stay
bounded, and dominated convergence carries the inequality over
([`fourByTwo_qcThreshold_le_chainOpNorm`](../../Morrey/Cassese/FourByTwo.lean#L1037)).

### E29. Lines 2489–2520: Corollary 6.1

The reduction from periodic to compactly supported Hessian test maps is not stated, and "the
calculation of Proposition 6.1" does not carry over: the skew part of `J D²φ` has two distinct
doubled singular values. Supplied, with matrices of rank at most `4` and `S₂` compared with `S₄`
([`not_hessianQuasiconvexAt_of_periodic`](../../Morrey/Cassese/Square.lean#L1925), [`square_not_hessianQuasiconvexAt_of_periodic`](../../Morrey/Cassese/Square/Hessian.lean#L204)).

### E30. Lines 2624–2633: Corollary 6.3, lower bound

The lower bound uses the sharpness of `p* − 1` for dyadic `±1`-transforms, with only "by choosing
the martingale-transform pair suitably (see also [Cassese 2025])" as a source. The place in
*Martingales, laminates and minimal Korn inequalities*
([arXiv:2512.02784](https://arxiv.org/abs/2512.02784)) is the proof of Theorem 2.2 (p. 10), the same
construction, which uses "the sharpness statement in Theorem 2.3" (p. 9): Burkholder's inequality,
quoted from Burkholder (Ann. Probab. 12 (1984)), "see [Osękowski 2012] for an exposition", "is sharp
among martingales defined on dyadic trees such that `‖dX_i‖ = ‖dY_i‖`". Those trees may split with
any weights; Corollary 6.3 needs the weights `1/2` of a Rademacher martingale. In that form the
sharpness is Burkholder 1984, Theorem 14.1 (p. 697: for the Haar functions and one sign for each, the
constant `p* − 1` "is best possible", through Maurey's theorem), and Osękowski 2012, Theorem 3.5 with
Theorem 3.34, Remark 3.8 and p. 138. It is proved here by Osękowski's proof: the second approach of
pp. 56–57 for `1 < p ≤ 2`, run on the dyadic function `W⁰` of the proof of Theorem 3.34, and the
duality of p. 59 for `p > 2` ([`External.Osekowski.exists_lt_lpNorm_transform`](../../Morrey/Common/External/Osekowski/Sharpness.lean#L82);
[`burkholderSharpness_holds`](../../Morrey/Cassese/Square/Sharpness.lean#L50) in the paper's notation).

### E31. Lines 2658–2659, 2670: Corollary 6.4

The paper only sketches the proof ("so we only sketch it"), and leaves `8/5 U ≥ ‖Y‖⁴ − 98 ‖X‖⁴` to
"standard calculations". Completed ([`corollary6_4`](../../Morrey/Cassese/Square.lean#L3475), [`corollary6_4_not_quasiconvexAt`](../../Morrey/Cassese/Square.lean#L3524)).

### E32. Lines 2891–2892: Corollary 7.2

The zig-zag concavity of `U` and `2U ≥ ‖y‖⁴ − 130 ‖x‖⁴` are left to "standard calculations".
Proved ([`corollary7_2`](../../Morrey/Cassese/FourByTwo.lean#L1603)). The bound is the identity
`2U − (|y|⁴ − 130 |x|⁴) = (|y|² − 10 |x|²)²`; with `C₀⁴ = 1170` it gives
`f_{4,√2,C₀} − 𝒫 = (30 |P_{√2}|² − |Q|²)² ≥ 0`. The zig-zag concavity reduces to a polynomial
inequality in `|x|²`, `|y|²`, `Re⟨x, h⟩`, `Re(y k̄)`, `|h|²`, `|k|²` ([`fourByTwo_U_core`](../../Morrey/Cassese/FourByTwo.lean#L1358)). The
margin of `C₀ = 1170^{1/4}` under Dragičević's `21√2/5` is about 1.5 %.

### E33. Lines 2184–2185: Corollary 5.4

"The negativity and integrability estimates for `u` in Proposition 5.2 still apply": the proof
reuses estimates from inside the proof of Proposition 5.2, for another profile, `F'(z) = 1 + z`.
They hold; the formal proof reruns them for that profile ([`corollary5_4`](../../Morrey/Cassese/TwoByThree/HessianCutoff.lean#L408); a route difference
recorded in [`route_differences.tsv`](route_differences.tsv)).

### E34. Lines 2552–2554, 2660–2668: the invariances in Theorem 1.4 at `p = 4`

Theorem 1.4 at `p = 4` needs Corollary 6.4's quartic to be invariant under conjugation and
transposition, which the paper does not state. Proved ([`theorem1_4_four`](../../Morrey/Cassese/Square.lean#L3586)).

### E35. Lines 2945–2947: the witness of Corollary 1.6

The proof takes "a smooth periodic `φ : 𝕋² → ℝ⁴` satisfying `∫_{𝕋²} F(∇φ) < 0`" without saying
where it comes from. Since `F` is not quasiconvex at `0`, Lemma 2.2 gives a Lipschitz periodic
`φ`; a smooth one needs a density step. It holds: the mollifications of the Lipschitz witness are
smooth, Lipschitz and periodic, and by dominated convergence one of them still has
`∫ F(∇φ) < 0` ([`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2215)).

### E36. Lines 541–549: Remark 2.1

"The proofs in [Pedregal 1993, Section 4] and [Dacorogna 2008, Theorem 6.10] assume that `f` is
bounded below." Dacorogna's Theorem 6.10 (p. 277) assumes less: a rank-one convex `g ≤ f`, with `f`
and `g` valued in `ℝ ∪ {+∞}`. The remark's device, `max {f, −n}`, applies either way, and
Proposition 2.1 is not affected; it is proved here by the remark's second route, from
Proposition 2.4. (Pedregal 1993 was not obtained.)

### E37. Lines 768–787: Proposition 2.6

Proposition 2.6 cites Osękowski's Theorem 3.24 (pp. 120–121), which concludes only that the space is
isomorphic to a Hilbert space. Its proof, by the Khintchine–Kahane inequality and a theorem of
Kwapień, estimates no distance: the bound `d_BM(X, H) ≲_p β_p` and its optimality are not in it. The
proposition is context and no proof uses it; it is stated with the bound
([`External.Osekowski.HilbertCharacterization`](../../Morrey/Common/External/Osekowski/HilbertCharacterization.lean#L48)) and not proved.

### E38. Lines 807–868: which signs, in Proposition 2.7

Definition 2.5 asks for the inequality for all *predictable* signs. The constants of the cited
theorems are for *deterministic* signs or multipliers (HNVW I, Definition 4.2.1; Randrianantoanina,
Definition 4.1; Pisier's lecture notes, Definition 8.7; Yaroslavtsev 2018, (3.1)). That the two
definitions give the same constants is HNVW I, Theorem 4.2.25 (Burkholder), which the paper does not
cite. Proposition 2.7 holds as stated: the formalization proves each item for predictable signs, the
sources' arguments applying to them directly, with Theorem 4.2.25 for (5). In (6), HNVW's
Theorem 4.5.6 asks concavity only for the signs `|ε| = 1`; the paper's `|ε| ≤ 1` is Yaroslavtsev's
Proposition 3.7 (multipliers in a convex set), stated there without `U(0,0) = 0`.

### E39. Lines 2865–2870: Theorem 7.1

"By [Dragičević 2011, Theorem 1.1] (see also [Dragicevic1]), we have `‖𝓑²‖_{L^p} > p* − 1` for
`p ≠ 2`." The theorem is stated for `p > 2` (p. 464: "Until the end of the paper we will assume that
`p > 2`, unless stated otherwise"). For `p < 2` one needs `‖𝓑²‖_p = ‖𝓑²‖_{p'}`, which is §1.3.1 of the
second reference (Carbonaro, Dragičević and Kovač), and for both cases `κ₂(p*) > p* − 1`, left to the
reader. Supplied ([`External.Dragicevic.theorem1_1_two_pStar`](../../Morrey/Common/External/Dragicevic/LowerBound.lean#L64), [`dragicevicLowerBound_holds`](../../Morrey/Cassese/Hypotheses.lean#L179)).

### Misprints and wording: E11, E12, E13, E15, E40, E41, E42

- E11 (line 1130): Remark 4.2 bounds `C^{rc}` by `UMD_p` where the argument gives `UMD_{ℂ,p}`;
  equivalent up to `π/2` (Proposition 2.7 (5)), so harmless under `≲`.
- E12 (lines 245, 1376): the TeX labels `thm:2x4` and `sec:2x4`, invisible in the PDF, are
  leftovers of v2; the content is `2 × 3`.
- E13 (lines 68, 242–243): the abstract and the introduction call the quartic "explicit", but it
  depends on unspecified `K` and `δ`.
- E15 (lines 1595–1596, 1722–1723): the wave equation that the proof mentions, `u_tt = Δu`
  (implied by `u_t = 2 conj(∂u)`), is never stated.
- E40 (lines 2300–2311): Proposition 6.3 cites Pisier–Xu's Theorem 6.1, "and also" Lust-Piquard 1986
  and Lust-Piquard–Pisier 1991, for the upper constant `≲ √q`. Theorem 6.1 says only that the constant
  depends on `q`; the order `√q` is in Remark (i) after it (p. 1486), with a reference to Pisier,
  Astérisque 247 (1998), p. 106, which says that it is "only implicitly contained" in
  Lust-Piquard–Pisier, and proves it from their inequality. That proof is followed here (Section 7).
- E41 (lines 2832–2835): "the standard transference identity for homogeneous multipliers". HNVW I,
  Corollary 5.7.6, states the identity (of three norms); the proof of Proposition 7.2 uses one
  inequality, `‖𝓑^{N+1}‖_{L^p(ℝ²)} ≤ ‖𝓑^{N+1}‖_{L^p_0(𝕋²)}`. Not an error.
- E42 (lines 2754–2762): "by the results of [Cassese 2025]", `C^{rc} ≤ (p* − 1) sup |Q|/‖P_ρ‖`. The
  result meant is Theorem 2.1 there, stated for `C^p ‖P_X(A)‖^p − ‖Q_X(A)‖^p` on square matrices, with
  `P_X`, `Q_X` the orthogonal projections onto a subspace `X` and its complement ((6), p. 7); `P_ρ` and
  `Q` are not such a pair, and the matrices are `2(N + 1) × 2`. Its proof (pp. 9–10) applies, and is
  made for them in [`proposition7_1`](../../Morrey/Cassese/FourByTwo.lean#L344).

The constants of Corollary 6.3 (`d₀ = 588`, the least that works) check out.

## 4. Missing hypotheses

None. Every statement is formalized as printed, with the readings of Section 6.

## 5. Redundant hypotheses

The proofs do not use the following hypotheses. All but the last two are kept in the Lean
statements, as the paper states them.

| Result | Hypothesis that the proof does not use | Lean |
| --- | --- | --- |
| Section 5.1: `q` is rank-one convex on `𝓛` (`cs-q-rc`) | `A ∈ 𝓛`: only the direction `R` must lie in `𝓛` | kept ([`quarticQ_rankOneConvexOn_calL`](../../Morrey/Cassese/TwoByThree/Basic.lean#L359)) |
| Lemma 5.1 (2) | the evenness of `f`: "`p`-homogeneous" means `f(tX) = \|t\|^p f(X)` for every real `t` (lines 158–163), and the proof uses it only for `t > 0`. Remark 5.2 applies the lemma to Šverák's `−rst`, which is only positively homogeneous, so it needs this | kept ([`lemma5_1_part2`](../../Morrey/Cassese/TwoByThree/Extension.lean#L276)), as the paper states it |
| Corollary 6.3, upper bound | `d ≥ 2` | kept ([`corollary6_3_upper`](../../Morrey/Cassese/Square.lean#L3076)) |
| Proposition 2.3 | the homogeneity, for the dichotomy `≡ −∞` or finite in (a) (the homogeneity of the envelopes uses it); the homogeneity and `p > 1` in (b), (c) (the formalization's split, E8) | kept |
| Section 1.3: monotonicity of the homogeneous problem | `1 < p` | kept ([`homMorreyPositive_mono`](../../Morrey/Cassese/Introduction.lean#L419)) |
| Theorem 2.3 | the separability of the Hilbert space | kept in [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82) and [`External.Osekowski.squareFunction`](../../Morrey/Common/External/Osekowski/Inequality.lean#L119); [`External.Osekowski.theorem3_5`](../../Morrey/Common/External/Osekowski/Inequality.lean#L68) and [`External.Osekowski.theorem8_6`](../../Morrey/Common/External/Osekowski/Inequality.lean#L106) do without it |
| Proposition 4.1 | the standing assumption `q > p + 2` of Section 4 | not assumed: [`proposition4_1`](../../Morrey/Cassese/TwoByM.lean#L431) asks only `1 < q` (Lemma 4.1 has no `q`) |
| Proposition 7.2 | `ρ > 0`, the setting of Section 7 | dropped: [`proposition7_2`](../../Morrey/Cassese/FourByTwo.lean#L1076) holds for every real `ρ`, a generalization of the paper's statement. Its lower bound, [`proposition7_2_lower`](../../Morrey/Cassese/FourByTwo.lean#L1092), keeps `ρ > 0`, which its proof uses (`‖ρ^N h‖ = ρ^N ‖h‖`) |

## 6. How the formalization reads the paper

- **Integrands and test maps.** Matrices `ℝ^{d×m}` are `Matrix (Fin d) (Fin m) ℝ`; the gradient of
  `φ` is `jac φ` (rows are components). An "integrand" (line 348) is lower semicontinuous and
  locally bounded ([`IsIntegrand`](../../palomar/Cassese/Challenge.lean#L114)). `W^{1,∞}_0([0, 1]^m)` maps are Lipschitz maps vanishing outside
  the open cube, with the gradient `fderiv`, defined almost everywhere by Rademacher's theorem.
  The formal Definition 2.1 also asks the integral to exist, which the paper does not; it is
  automatic for integrands, and it makes a failure of quasiconvexity a genuine integral.
- **Homogeneity.** `IsPHomogeneous p f` is `f(tA) = |t|^p f(A)` for every real `t`, the paper's
  `p`-homogeneity (lines 158–163); positive homogeneity is a separate predicate.
- **Rank-one convexity** is Definition 2.2, on segments. Bridges prove it equivalent to convexity
  along lines (Šverák's form) and to the textbook definitions of the package
  `lean4-calculus-of-variations`, in which the cited results of the calculus of variations are
  stated ([`Morrey/Cassese/Bridges.lean`](../../Morrey/Cassese/Bridges.lean)).
- **Prelaminates** (Definition 2.4) allow repeated atoms, the reading that Proposition 2.4's gluing
  needs (E10).
- **Rademacher martingales** live on `Fin N → Bool` with the uniform measure; the thresholds
  `C^{rc}`, `C^{qc}` are infima in `[0, ∞]`.
- **UMD constants** (Definition 2.5, and (5) of Proposition 2.7) are best constants over every
  probability space in `Type`, every filtration, every martingale started at `0` (Mathlib's
  `MeasureTheory.Martingale`), and every predictable sequence of signs, or of unimodular
  multipliers for `UMD_{ℂ,p}`. Banach spaces are real (complex for `UMD_{ℂ,p}`). The Schatten
  class `S_q^{d×d}` is `Fin d → Fin d → ℝ` renormed by `‖·‖_{S_q}` ([`umdConstWith`](../../Morrey/Cassese/Defs.lean#L297)). These
  definitions are the package's, definitionally ([`Morrey/Cassese/Hypotheses.lean`](../../Morrey/Cassese/Hypotheses.lean)).
- **Schatten norms** are defined from the singular values, `s_i = √λ_i(AᵀA)`.
- **The Beurling–Ahlfors transform.** `𝓑^k` is the Fourier multiplier with symbol `(ξ̄/ξ)^k`.
  `‖𝓑^k‖_{L^p(ℝ²)}` is the supremum of `‖𝓑^k f‖_p / ‖f‖_p` over Schwartz functions
  ([`beurlingPowNorm`](../../Morrey/Cassese/Defs.lean#L218)), and `‖𝓑^k‖_{L^p_0(𝕋²)}` over mean-zero trigonometric polynomials
  ([`torusBeurlingPowNorm`](../../Morrey/Cassese/Defs.lean#L236)). The operator norm of Proposition 7.2 is the supremum over smooth
  mean-zero periodic tuples ([`chainOpNorm`](../../Morrey/Cassese/FourByTwo.lean#L112)), as in the paper's proof.
- **Hessian quasiconvexity** (Corollaries 5.4, 6.1), undefined in the paper, is
  `∫_{(0,1)^n} F(A + D²φ) ≥ F(A)` for smooth compactly supported `φ`.
- **Quantifiers.** Theorem 1.3 (b): `∃ ε > 0, ∀ p, |p − 4| < ε → …`. Corollaries 5.3, 5.4:
  `∃ K₀ ∀ K ≥ K₀ ∃ δ₀ > 0 ∀ δ ∈ (0, δ₀)`, with `Λ = K/δ`. Proposition 6.5 at `q = ∞`: one exponent
  `α` for every `p` (the proof gives `α = 3`), which covers both readings of the paper.
  Corollary 6.1: the paper's `d(p)`, with `d = 2n`; the formalization takes `n = m⁸` and proves
  every larger `d` as an extra lemma ([`corollary6_1_ge`](../../Morrey/Cassese/Square.lean#L2274)).
- **Theorem 1.4** for general `p` fixes the Schatten exponent `q = 4` among the paper's
  `q ∈ (2, ∞)`.
- **The cited results** are stated, in their sources' terms or as the paper quotes them, in [`Morrey/Common/External/`](../../Morrey/Common/External), and in the
  paper's terms in [`Morrey/Cassese/Hypotheses.lean`](../../Morrey/Cassese/Hypotheses.lean) ([`burkholderInequality_holds`](../../Morrey/Cassese/Hypotheses.lean#L116),
  [`hnvwExtrapolation_holds`](../../Morrey/Cassese/Hypotheses.lean#L508), …, [`dragicevicLowerBound_holds`](../../Morrey/Cassese/Hypotheses.lean#L179)). Some are stated more generally than
  the paper quotes them: Lemma 2.1 for every real-valued rank-one convex function (E21);
  Burkholder's inequalities without separability (Section 5), and Theorem 3.5 in the book's form, with
  `‖g_0‖ ≤ ‖f_0‖`; the extrapolation of UMD constants for all exponents, as in HNVW; Kahane–Khintchine
  for any seminorm on a real vector space; Lemma 2.2 for Borel, locally bounded functions, as in the
  sources; Dacorogna's Theorem 5.20 without continuity, as in the book
  ([`External.Dacorogna.RankOneAffineMinors`](../../Morrey/Common/External/Dacorogna/Minors.lean#L61)). Others are stated
  in the case the paper uses: Osękowski's Theorem 8.6 for martingales started at `0`; HNVW's
  UMD theorems for real spaces, probability spaces and martingales started at `0`; Randrianantoanina's
  bounds, and Pisier–Xu's Theorem 6.1 for `q ≥ 2` ((6.4)), for real square matrices, uniformly in the
  size; Pisier's for the
  complex `L^p(μ)` as a real Banach space; decoupling for Paley–Walsh martingales; the quasiaffinity of
  minors for `3 × 3` minors on the cube; Kristensen's smoothing in the form of Corollary 5.2 (quartics on
  `ℝ^{2×m}`, `m ≥ 3`; the package has it for every smooth rank-one convex integrand on `ℝ^{d×m}` that is
  not quasiconvex at `0`); transference in the direction from `𝕋²` to `ℝ²`, for symbols homogeneous of
  degree `0`; Dragičević's theorem for `𝓑²`.
- **Proposition 2.7 (6)** ([`HNVWZigZag`](../../Morrey/Cassese/Hypotheses.lean#L477)). For a real `X`, the equivalence and the bound `β ≥ UMD_p(X)`,
  with functions concave along `z ↦ (x + z, y + εz)` for `ε ∈ [−1, 1]`; for a complex `X`, with `ε` in the
  closed unit disc (the paper's footnote), the equivalence with the finiteness of `UMD_p(X)`, the
  constant of `X` as a real space, and the bounds `β ≥ UMD_p(X)` and `β ≥ UMD_{ℂ,p}(X)`. The spaces are
  in `Type`, as in the other statements on UMD constants.

No statement of the paper had to be corrected.

## 7. Departures from the paper's proofs

### The paper's proofs

Every proof follows the paper's argument except the three below. Each repairs a step that is
false (E10) or missing (E4, E9), and each is described in its declaration's docstring; the one that
changes the results a proof uses (E10) is also in [`route_differences.tsv`](route_differences.tsv).

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Theorem 1.3 (b) ([`twoByThree_theorem1_3_b_witness`](../../Morrey/Cassese/TwoByThree/NearFour.lean#L860)) | "continuity of the rank-one convexity and quasiconvexity estimates for `f`", in `p` | the same continuity, made explicit: Lemma 5.1 (1) with explicit constants ([`lemma5_1_part1_quant`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L324)), so that `Λ₀(p, δ)` is continuous in `p`; `K`, `δ` and the cut-off fixed before `p` varies; dominated convergence in `p` | the continuity needs constants uniform in `p`, which Lemma 5.1 (1), stated for a fixed `p`, does not give (a gap) | E4 |
| Proposition 2.5, "⇐" ([`proposition2_5`](../../Morrey/Cassese/Toolkit.lean#L1935)) | Proposition 2.4 and the claim of lines 661–663 that every dyadic prelaminate is the law of a rank-one Rademacher martingale | Proposition 2.4's gluing argument, run on the infimum `G(A) = inf E f(M_N)` over rank-one Rademacher martingales started at `A` | the claim is false under the reading of prelaminates that Proposition 2.4 needs, and the gluing of Proposition 2.4 fails under the other reading | E10 |
| Proposition 5.1 ([`proposition5_1`](../../Morrey/Cassese/TwoByThree/Folklore.lean#L260)) | "`Q` is rank-one affine at `0`. It follows that `Q` is rank-one affine"; "Since `P''(0) = (P − Q)''(0)`, the quadratic polynomial `P − Q` is rank-one convex" | a prelaminate centred at `0` with an atom at an arbitrary `A`, split once more along `±hR`; the Legendre–Hadamard condition for the quadratic part by the same device | both steps are skipped (a gap) | E9 |

Not departures: Theorem 1.2 is proved by the paper's route, and the route of Remark 4.5 is a
second theorem, [`theorem1_2_elementary`](../../Morrey/Cassese/TwoByM.lean#L3480), which takes `f = g` (its `g` is already globally rank-one
convex, so no envelope is needed); the gaps that the formalization fills along the paper's own
lines, recorded as findings in Section 3, among them the density steps from smooth to Lipschitz
periodic test maps in Proposition 7.2 (E28) and Corollary 1.6 (E35), by mollification and
dominated convergence; the explicit constants and cut-offs that complete the sketched proofs (Corollary 5.3's `c = 75/8`, `C = 4·10⁶`, E17; Remark 4.5's `U`, `K`, `q`, E26;
Corollaries 6.4 and 7.2, E31, E32); and the route differences where the paper cites the proof of a
result rather than its statement (Corollaries 5.4 and 6.1, Remark 6.3, Proposition 6.5), recorded
in [`route_differences.tsv`](route_differences.tsv).

### The cited results

Each cited result that the proofs use is proved by the cited source's argument; Proposition 2.1 is
proved by the paper's second route, and Proposition 2.7 (4) by the second proof that its source gives.
The table says how each source was read, which module states the result and where in the packages the
proof is (HA, BP, CV as in Section 2), and what is different, and why. A "(gap)" or a "(slip)" is the
source's, repaired along the source's lines (the list "Errors and gaps found in the sources", below, has
the references). The READMEs of [`Morrey/Common/External/`](../../Morrey/Common/External) and the packages' module docstrings give
the details.

| Cited result | Source, and how it was read | Stated and proved in | What is different, and why |
| --- | --- | --- | --- |
| Lemma 2.1 | Rindler 2018, Lemma 5.6: the first edition was not obtained; the second one (2026) was read, where the result is Lemma 5.9 (pp. 114–115), matched by content | [`External/Rindler/Lemmas.lean`](../../Morrey/Common/External/Rindler/Lemmas.lean); CV `RankOneConvex/` | the local boundedness of a rank-one convex function, part of Rindler's definition, is proved, by convexity in each entry (the paper applies the lemma to functions not known to be integrands, E21; Rindler, p. 111, refers to Kirchheim–Kristensen for it); (5.10) is used where it holds (slip); the part on functions of `p`-growth is not formalized |
| Lemma 2.2, quasiconvex ⇒ rank-one convex | Rindler 2026, Proposition 5.6 (pp. 111–113): read; the first edition's Propositions 5.1 and 5.3 not checked | [`External/Rindler/Lemmas.lean`](../../Morrey/Common/External/Rindler/Lemmas.lean); CV `Quasiconvex/{Cutoff, Laminate, RankOneConvex}` | on the unit cube, with an orthogonal change of variables for the cubes of other directions (mechanics) |
| Lemma 2.2, the domain and the periodic test maps | Dacorogna 2008, Propositions 5.11 and 5.13 (pp. 172–174): read; also Rindler 2026, Lemma 5.2 (i) (p. 106) | the same; CV `Quasiconvex/{Domain, Periodic}` | the test maps are Lipschitz maps that vanish outside the domain, and their gradients vanish almost everywhere on the zero set, which is proved (for Dacorogna's `W^{1,∞}_0` it is immediate); the domain is nonempty, and the roles of the two domains are Dacorogna's (slips); the statements are at one matrix, as the paper's |
| Proposition 2.1 | Dacorogna 2008, Theorem 6.10 (pp. 277–279): read; Pedregal 1993: not obtained | [`proposition2_1`](../../Morrey/Cassese/Toolkit.lean#L780) | the paper's own second route (Remark 2.1), so neither source's argument is used |
| Proposition 2.2 | Kinderlehrer–Pedregal 1991, Proposition 8.1 (pp. 360–362) with Step 6 of Proposition 7.2: read; Dacorogna 1982, Theorem 5: read (a hypercube, and a growth condition) | [`External/KinderlehrerPedregal/Formula.lean`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean); CV `Envelope/` | the formula itself, `f^{qc} = ψ^#`, which the source does not state, and the approximation in (iv) by piecewise affine maps are supplied; the copied domains have null boundaries, a hypothesis that Proposition 8.1 leaves out (gaps) |
| Theorem 2.3 | Osękowski 2012, Theorems 3.5 (pp. 53–54, 58) and 8.6 (pp. 413–415): read | [`External/Osekowski/Inequality.lean`](../../Morrey/Common/External/Osekowski/Inequality.lean); BP `Martingale/Osekowski/{Method, SimpleFunctions, Integral, Moment}`, `Martingale/Burkholder/{Function, Inequality}` | a fixed time instead of `sup_n`, equivalent; no separability; Theorem 8.6 for martingales started at `0`; the two integral formulas for Burkholder's function, stated there without proof, are proved; the majorization `U_p ≥ V_p` also uses Burkholder 1988, (1.11), where the book's argument has a gap; slips |
| Proposition 2.6 | Osękowski 2012, Theorem 3.24 (pp. 120–121): read | [`External/Osekowski/HilbertCharacterization.lean`](../../Morrey/Common/External/Osekowski/HilbertCharacterization.lean) | stated, not proved (context; E37) |
| Proposition 2.7 (1) | HNVW I, Theorem 4.2.7 (pp. 283–285) with pp. 229–234: read | [`External/HNVW/Extrapolation.lean`](../../Morrey/Common/External/HNVW/Extrapolation.lean); BP `UMD/{CubeTransform, GoodLambda, Extrapolation}` | predictable signs, probability spaces, martingales started at `0`, real spaces (the paper's Definition 2.5 and the case used); Lemma 3.5.14 at the first index (gap); an elementary inequality left to the reader |
| Proposition 2.7 (2) | Randrianantoanina 2002 (arXiv:math/0111264), §§2–4: read | [`External/Randrianantoanina/SchattenUMD.lean`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean); BP `Noncommutative/` | Cuculescu's projections `q_{k+1} = 1_{[0,λ]}(q_k x_k q_k)` are read in the reduced algebra `q_k N q_k`, as the proof requires (read literally, they would not decrease); "by interpolation" (Theorem 4.3) is carried out in three ranges of exponents, so that the constant stays uniform near `2`; Lemma 3.2 in a counting form for matrices (constant `26` in (3.2)); HNVW I, Theorem 4.2.7, in place of the extrapolation theorem that the source quotes from Pisier |
| Proposition 2.7 (3) | Pisier 2016, Corollary 5.22, read in the 2011 lecture notes (Corollary 8.19): the book was not obtained | [`External/Pisier/LpUMD.lean`](../../Morrey/Common/External/Pisier/LpUMD.lean); BP `UMD/Lp` | Fubini's theorem is applied to Paley–Walsh martingales, and HNVW I, Theorem 4.2.5, passes to general filtrations: no σ-finiteness and no joint measurability needed |
| Proposition 2.7 (4) | HNVW I, Theorem 4.2.5 (p. 282): read | [`External/HNVW/DyadicUMD.lean`](../../Morrey/Common/External/HNVW/DyadicUMD.lean); BP `UMD/Maurey/`, `ZigZag/` | by the alternative proof that the book points out on p. 334 (Burkholder 1986), Theorem 4.5.6, (2)⇒(3)⇒(1); the proof printed at Theorem 4.2.5 (pp. 284–285, after Maurey) is not the one followed |
| Proposition 2.7 (5) | Yaroslavtsev 2018 (arXiv:1710.04958), Lemma 3.2: read, no proof there ("proven in" HNVW I, Proposition 4.2.10); HNVW I, p. 286, with Theorem 4.2.25 (pp. 300–301): read | [`External/Yaroslavtsev/ComplexUMD.lean`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean); BP `UMD/{ConvexHull, Incremental, Complex}` | none in the argument; Lemma 3.6.18 (iii) (slip) |
| Proposition 2.7 (6) | HNVW I, Theorem 4.5.6 (pp. 330–337), and Yaroslavtsev 2018, Proposition 3.7: read | [`External/HNVW/ZigZag.lean`](../../Morrey/Common/External/HNVW/ZigZag.lean), [`External/Yaroslavtsev/ComplexUMD.lean`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean); BP `ZigZag/` | the paper's functions are concave for `\|ε\| ≤ 1` and vanish at the origin, so the multipliers are constants in `[−1, 1]`, or in the unit disc, as Yaroslavtsev's; two steps of HNVW's proof are exchanged (gap) |
| Proposition 2.8 | Cox–Veraar 2007: introduction read, no proof there; HNVW I, Proposition 4.2.3 (p. 282, by Proposition 4.1.16, pp. 279–280): read | [`External/CoxVeraar/Decoupling.lean`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean); BP `UMD/Decoupling` | only the Paley–Walsh case, which the paper uses |
| (13), (14) | Burkholder 1988 (Numdam), proof of Theorem 1.1 and Remark 1.2: read; Vasyunin–Volberg 2010, cited as an alternative: not obtained | [`External/Burkholder/ScalarFunction.lean`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean); BP `Martingale/Burkholder/Function` | Remark 1.2, concavity along every line, has no proof in the source: it is completed from (1.14) and the shift of the proof of (1.8) (gap) |
| Dacorogna, Theorem 5.20 (Proposition 5.1) | Dacorogna 2008, pp. 179–191, with Theorem 8.35 (pp. 409–411): read | [`External/Dacorogna/Minors.lean`](../../Morrey/Common/External/Dacorogna/Minors.lean); CV `Minors/` | Lemma 5.24, Part 2, repaired, and (ii) ⇒ (ii′) avoided (gaps, slips); that the minors are quasiaffine by the proof of Theorem 8.35 (ii), for `3 × 3` minors on the cube, which the paper needs |
| Dacorogna, Theorem 5.25 (i) (Proposition 5.1) | Dacorogna 2008, pp. 191–194: read | [`External/Dacorogna/Minors.lean`](../../Morrey/Common/External/Dacorogna/Minors.lean); CV `QuadraticForm/` | Plancherel's formula for smooth maps, then mollification, where the book applies it to the Lipschitz map (mechanics) |
| Kristensen's smoothing (Corollary 5.2) | Kristensen 1999, proof of Proposition 2 (pp. 6–7): read (scan, Numdam); Heinz 2008: not obtained | [`External/Kristensen/Smoothing.lean`](../../Morrey/Common/External/Kristensen/Smoothing.lean); CV `Smoothing/` | the cut-offs are functions of `\|X\|²` instead of `\|X\|` (slip); a constant is added, since the paper's form asks `c ‖A‖² ≤ h(A)`; `ε` is chosen before the radius (the order of independent steps); his "it is not hard to see", the rank-one convexity of the cut-off function, is supplied along his lines |
| Proposition 6.3 | Pisier–Xu 2003, Theorem 6.1 (p. 1486): read, no proof there; Lust-Piquard 1986: not obtained; Lust-Piquard–Pisier 1991 (pp. 242–255), and, for the order `√q`, Pisier, Astérisque 247 (1998), pp. 101–108: read. Behind them: McConnell 1984, Theorems 1.1 (pp. 746–751) and 1.3 (pp. 754–756); Burkholder 1983, Lemmas 1–4 (pp. 277–283; pp. 403–409 of the reprint in his *Selected Works*, read as page images), and pp. 271–276; M. Riesz 1928, §18 (pp. 234–235), to which Lemma 4 refers: read; Sarason 1967, §10 (Theorem 4); Helson–Lowdenslager 1958 and 1961; HNVW I, Lemma 5.2.1 and Proposition 5.2.2 (pp. 388–389), Proposition 5.7.1 with the dilation of the proof of Theorem 5.7.10 (pp. 465–466), and Appendix D, and HNVW II, Proposition 7.4.22; Tomczak-Jaegermann 1974: read; Maurey–Pisier 1976, Remark 2.10: read, no proof there | [`External/PisierXu/Khintchine.lean`](../../Morrey/Common/External/PisierXu/Khintchine.lean); HA `NoncommutativeKhintchine`, `Paley/`, `Hardy/`, `VectorValued/`; BP `Schatten/`, `RandomSums/`, `TypeTwo/`, `KConvexity/`, `Noncommutative/`, `UMD/Decoupling`, `Martingale/Burkholder/Inequality` | real matrices of every size, taken as complex ones; Theorem III.1 (i) of Lust-Piquard–Pisier for the Paley projection and `C_p`, `1 ≤ p ≤ 2`, only; its (III.3), for every choice of signs, by McConnell's Theorem 1.3, the second of the two references given for it (the first, Bourgain 1986, Theorem 4, was not obtained), for `n = 1` and from UMD spaces, carried over to the circle by HNVW I, Proposition 5.7.1, with the dilation above, and to the values `ε_ℓ + ε_{ℓ+1}` at `2^ℓ` by a combination of multipliers (steps left to the reader); in McConnell's proofs, the places where a Brownian motion hits the heights are represented by their finite-dimensional distributions, which are all that his Section 3 uses (chains with independent Cauchy increments, so that his Lemma 2.3, proved there with a Bessel process and a time reversal, becomes a definition), and Poisson integrals by their Fourier transforms, with (2.7) and (3.4) proved on the Fourier side; `f = 𝓕⁻G` with `G ∈ L¹` in place of his test functions, `m` complex and of class `C²` off `0`, without mollification; (2.1) for deterministic coefficients, complex ones by real and imaginary parts; Lemma 3.1 without its two cases, (3.6) after the integration in `s`, finite parts of the sums `m_i` and `M`; the boundedness of the Hilbert transform on UMD spaces by the proof of Burkholder 1983, which he cites for it, and not by the one that his Remark 3.1 (pp. 753–754) indicates; in Burkholder's proof, a `UMD_p` constant `β` in place of ζ-convexity, and explicit constants, `β²` for conjugate harmonic polynomials (Lemma 2), `2β²` for conjugate Poisson integrals (Lemma 3), `2β² + 1` for the truncations on the circle (33) and on the line (Lemma 4), with Minkowski's inequality where he integrates `p`-th powers over the rotations; Lemma 4 by M. Riesz's argument applied to the truncations, with the limit that Riesz leaves out (p. 234) written out, and Fatou's lemma where he lets `m → ∞` without a reason; his signs as coordinates of a cube, then of an infinite product; his Taylor estimate by induction on the degree, his two equidistributed sequences of signs (pp. 281–282) by one change of the signs, and his `K_r` (p. 283, "there is a nonnegative function") given explicitly; the limit `ε → 0` only for the functions `𝓕⁻G ∈ L^p`, `G ∈ L¹`, where he states Theorem 2 without proof; the case `β = ∞` apart; the type 2 constant of `S_q` for every `q ≥ 2`, by Tomczak-Jaegermann's interpolation (Astérisque 247 quotes it "at least when `p` is an even integer"); the upper constant is `C √q`, `C` absolute and not explicit; named substitutes (below); gaps and slips |
| Proposition 6.4; the constants of E27 | HNVW II, Theorem 6.2.4 (pp. 21–22), with Theorem 6.2.2 and Lemma 6.2.3 (pp. 18–21): read | [`External/HNVW/KahaneKhintchine.lean`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean); BP `Hypercontractivity/`, `KahaneKhintchine/Basic` | values in any seminormed space; a constant in Lemma 6.2.3 and the case `q = 1` of Theorem 6.2.4 (slips) |
| the sharpness of `p* − 1` (Corollary 6.3) | Cassese 2025 (arXiv:2512.02784), Theorems 2.2 and 2.3 (pp. 8–10): read; Burkholder 1984 (Theorems 1.1, 14.1), quoted there: read, not followed; Osękowski 2012, Theorem 3.5 (pp. 56–57, 59), with Theorem 3.34, Remark 3.8 and pp. 137–138: read | [`External/Osekowski/Sharpness.lean`](../../Morrey/Common/External/Osekowski/Sharpness.lean); BP `Martingale/Osekowski/Sharpness` | the second approach is run on the dyadic function `W⁰` of the proof of Theorem 3.34, instead of on `U⁰` and then that theorem (which is not formalized); a predictable sign on the sign cube is a sign for each Haar function, as in (3.214); slips |
| the bound of Proposition 7.1 | Cassese 2025, Theorem 2.1 (pp. 7, 9–10): read | [`proposition7_1`](../../Morrey/Cassese/FourByTwo.lean#L344) | for `P_ρ` and `Q` instead of complementary orthogonal projections (E42); on rank-one Rademacher martingales, as the paper's Propositions 2.4 and 2.5 allow |
| transference (Proposition 7.2) | HNVW I, Corollary 5.7.6 (pp. 462–463), with Proposition 5.7.4, Lemma 5.7.5 and Proposition 2.4.23: read | [`External/HNVW/Transference.lean`](../../Morrey/Common/External/HNVW/Transference.lean); HA `Transference/`, `FourierMultiplier/{Density, Norming}`, `Torus/Poisson` | scalar symbols on `ℝ² ≅ ℂ`, and the inequality used, from `L^p_0(𝕋²)` to `L^p(ℝ²)`; the closing density and duality, left to the reader, are written out (gap); slips |
| Dragičević's lower bound (Theorem 7.1, Corollary 7.2) | Dragičević 2011 (pp. 463–467): read; Carbonaro–Dragičević–Kovač 2023 (arXiv:2109.08369), §1.3.1: read | [`External/Dragicevic/LowerBound.lean`](../../Morrey/Common/External/Dragicevic/LowerBound.lean); HA `BeurlingAhlfors/`, `FourierMultiplier/Duality` | `n = 2`; the sentence "`f` belongs to `W^{n,p}`, which ensures that `T^n(∂̄^n f) = ∂^n f`" (p. 465, no proof) is replaced by what is used of it, `‖∂²f‖_p ≤ ‖𝓑²‖_p ‖∂̄²f‖_p`, proved by approximating `f_{2,α}` by Schwartz functions; the duality on the Fourier side |
| Theorem 1.1 (Kirchheim–Kristensen) | Kirchheim–Kristensen 2016: not compared | [`External/KirchheimKristensen/Theorem.lean`](../../Morrey/Common/External/KirchheimKristensen/Theorem.lean) | stated, not proved (context) |
| the Schatten facts (1)–(3) of Section 1.5 | Bhatia 1997, Chapters III and IV: read in part | [`Morrey/Cassese/Square.lean`](../../Morrey/Cassese/Square.lean), [`Morrey/Cassese/Square/`](../../Morrey/Cassese/Square) | none in the argument; Bhatia writes out no proof of (2) |

**Proposition 6.3**, after Lust-Piquard and Pisier (whose numbers and pages these are, where no other
source is named). The lower bound, with constant `1`, is their convexity argument ((I.5)–(I.7),
pp. 246–247). The upper bound has four steps.

1. Paley's inequality in the Schatten classes `C_p` (Theorem III.1 (i), pp. 249–253), here with a constant
   independent of `p ∈ [1, 2]` and of the size. An analytic `f` is `g h` with
   `‖f‖_{L¹(C_p)} = ‖g‖_{L²(C_{2p})} ‖h‖_{L²(C_{2p})}` ((α), (β), p. 252): Sarason's Theorem 4, which rests
   on Helson and Lowdenslager's outer functions, Szegő's theorem and range functions. The coefficients
   `f̂(2^k)` split into two sums, bounded by Jensen's and Hölder's inequalities, (I.7), and (III.3): for
   every choice of the signs `ε_k`, `‖Σ ε_k H_{2^k}‖ ≤ C ‖h‖` in `L²(𝕋; C_{2p})`, where `H_{2^k}` is the part
   of `h` with the frequencies in `[2^{k−1}, 2^k]`. As `C_{2p}` is a UMD space, this follows from McConnell's
   Theorem 1.3 (the Littlewood–Paley inequalities for every choice of signs), transferred to the circle;
   that theorem rests on his Theorem 1.1 (Mihlin multipliers) and on the boundedness of the Hilbert
   transform on UMD spaces, a theorem of Burkholder (1983). Burkholder bounds the conjugates of
   trigonometric polynomials by a random walk stopped when it leaves the disc (Lemmas 1 and 2: decoupling,
   Taylor's theorem, the square function inequality for real martingales, which he asserts on p. 275 to
   follow from his Theorem 1 for `ℝ` and Khintchine's inequality, proved here by the argument of his
   Lemma 1), and passes to conjugate functions on the circle (Lemma 3) and to the line (Lemma 4, by
   M. Riesz's argument, 1928, §18).
2. Corollary III.4, with signs in place of `e^{i2^k t}`, by averaging (p. 243).
3. The Rademacher projection on `L^{q'}(S_{q'})`, `1/q + 1/q' = 1`, is bounded by a multiple of `√q`
   (Astérisque 247, p. 106): `S_q` has type 2 with constant at most `√(q + 1)` (Tomczak-Jaegermann), and
   type 2 implies K-convexity (Maurey and Pisier; HNVW II).
4. Duality (pp. 246–248 and 254–255; Astérisque 247, p. 106).

Apart from the differences named in the table, no argument replaces a source's, with one kind of
exception: a step that a source of Proposition 6.3 takes from a work that was not read, recalls as known,
or states without proof. The argument is then that of a named substitute. No attempt to obtain the works
that the table marks as not read is recorded. (Bourgain 1986, the other reference for (III.3), was looked
for and not found; it is not needed.)

| Step | In the source | Substitute |
| --- | --- | --- |
| from the truncations to the multiplier `−i sgn` (McConnell, (3.20), p. 755) | the symbol is recalled (McConnell, Remark 3.1, p. 753, `i sign λ` in his normalization); the limit `ε → 0` is in Burkholder 1983, Theorem 2 (p. 284), stated without proof | HNVW I, Lemma 5.2.1 and Proposition 5.2.2, and Fatou's lemma |
| the inequality (8) for `ℝ`, from which the square function inequality (9) for real martingales follows with Khintchine's inequality, as Burkholder 1983 asserts without proof on p. 275 (proved here by the argument of his Lemma 1, pp. 277–278, for `ℝ`; (9) is used at the exponents `p` and `2p` in (20), (25) and the estimate of `W^j` after (26), pp. 279–281) | "By Theorem 1" (p. 275), whose proof is in Burkholder 1981 (Ann. Probab. 9): read, not followed | Burkholder's inequality with the constant `p* − 1` (the paper's Theorem 2.3 (1)) |
| `C_{2p}` is UMD (p. 251) | recalled, with Cotlar's trick, interpolation and duality, from Rubio de Francia 1986, Proposition 3: not read | Randrianantoanina's theorem, the paper's source for `S_q` (Proposition 2.7 (2)) |
| Hölder's inequality (I.1), and the duality of the Schatten classes (p. 245) | Simon 1979, Theorems 2.8 and 3.2: not read | HNVW I, Appendix D |
| Sarason, Lemma 10.3: a factorable function is `BᴴB` with `B` outer | Helson's book, p. 121: not read | Helson–Lowdenslager 1961, §§9–10 |
| Sarason, Lemma 10.4: Szegő's theorem, and a quotient by an outer function | Hoffman's book, pp. 53 and 75: not read | Helson–Lowdenslager 1958, Theorem 9, for scalar functions; the argument that ends the proof of Sarason's Theorem 4 |
| Tomczak-Jaegermann, pp. 165 and 167: Horn's inequality, and the three lines theorem for Schatten norms | Gohberg–Krein 1965: not read | HNVW I, Appendix D; Sutter–Berta–Tomamichel 2017 (arXiv:1604.03023), Theorem 3.1 |
| Tomczak-Jaegermann, p. 177: the comparison of the multinomial coefficients with `M_{2k}` | quoted from two other works: not read | elementary, `(2β)! ≥ 2^β β!` |
| type 2 implies K-convexity | Maurey–Pisier 1976, Remark 2.10: stated without proof | HNVW II, Proposition 7.4.22 |

Not a cited result, hence not in the table: the triangle inequality for Schatten norms, which the
paper uses with no source (Bhatia, Theorem IV.2.1, proves it by majorization). It is proved after
Bourin and Zhang, *Matrix triangle inequalities: past, present, and future*, arXiv:2610.30538 (2026),
Proposition 3.13, by the third proof of their Remark 3.14 (Hermitian dilations and the convexity
inequality (1.1), proved by Peierls's argument; `q = ∞` by Weyl's inequality), for real `m × n`
matrices where they have complex square ones.

### Errors and gaps found in the sources

None affects a statement used here. Those on the pages that the proofs follow are noted in the
docstrings, with the repairs.

- **Osękowski 2012.** P. 11, Theorem 2.2: the spliced pair need not have deterministic signs. P. 27,
  (3.8) and the last display before "and (3.8) follows": signs (the inequality of (3.8) is reversed).
  P. 29: `U_∞ ≥ (|y| − 1)² − |x|²` should be `≤`, and the two inner products in the bracket have the
  wrong sign. P. 30: `= U₁(x, y)` should be `= |U₁(x, y)|`. P. 54: `F` is convex on `(0, s₀)` and
  concave on `(s₀, 1]`, not the reverse, so `F ≥ 0` also needs `F(1) ≥ 0`, which is Burkholder's (1.11);
  the factor `p − 1` in the constant of the integral formula should not be there. P. 56: `x/(2x + 1)`
  should be `x/(2x − 1)`. P. 57: `w(1) < 0` follows from (3.65), not from (3.66). The integral
  formulas (pp. 54, 58) have no proof.
- **HNVW I (2016).** Proposition 2.4.23 (i) (p. 118): false for `C_c^∞(ℝ^d∖{0})`, since
  `|f(0)| ≤ ‖f̂‖_1` (not used). Lemma 3.5.14 (p. 231): `g_{ρ−1}` has no meaning at the first index, and
  the bound `3δλ`, stated for `ρ`, is needed for every `k`. Lemma 3.6.18 (iii) (p. 258): `k = 0, …, n`,
  not `N`. Theorem 4.2.5 (p. 284): the printed proof applies Theorem 3.6.1, for divisible spaces, to any
  space (not used). Theorem 4.5.6, Step 2 (p. 335): Lemma 4.5.2, for real-valued functions, is applied
  before `U < ∞` is known. Proposition 5.7.4 (pp. 460–462): printed without its first
  hypotheses (Banach spaces, `1 < p < ∞`), and the boundedness of `m` is not stated; `ε^{d/p}` and
  `ε^{d/p'}` interchanged; the density of the `g` in `L^{p'}` does not by itself norm `T_m f`. Lemma 5.7.5 (p. 461): the bound on `f(u + k/ε)` needs a centred cell. Corollary 5.7.6,
  III ≤ I (p. 463): Proposition 5.7.1 asks that `0` be a Lebesgue point of `m`, and it is not one for a
  non-constant homogeneous `m` (not used).
- **HNVW II (2017).** Lemma 6.2.3 (p. 21): `√(1/(q − 2))` should be `√(1/(q − 1))`. Theorem 6.2.4
  (p. 22): the case `q = 1` is left out. Proposition 7.4.22 (p. 124): "cotype 2 implies Gaussian cotype 2"
  should be type 2.
- **Dacorogna 2008.** Lemma 5.24, Part 2 (pp. 188–190): for `n > s + 1`, `g ≠ Σ_β X_β` (each term is
  counted `n − s` times) and `X_β` need not be rank-one affine (`N = 2`, `n = 3`,
  `g = det(ξ₁, ξ₂) + det(ξ₁, ξ₃)`, `β = (1, 2)`: the `t²` coefficient along `(1, 1) ⊗ b` is `−b₁b₃`); the
  displayed `t²` coefficients (p. 190) omit terms. Repaired by restricting the columns to `β` first.
  Theorem 5.20, (ii) ⇒ (ii′) (pp. 181–182): "then, obviously, `f ∈ C¹`" is not justified (not needed).
  Proposition 5.11 (p. 172): false for `D = ∅`.
- **Rindler 2026.** (5.10) (p. 114): printed with absolute values, it holds when `h(B) ≤ h(A)`;
  otherwise `A` and `B` are to be exchanged. Lemma 5.2 (i) (p. 106): the proof tests `Ω̃` only with
  scaled copies of maps on `Ω`; a copy of `Ω̃` is to be put into `Ω`.
- **Randrianantoanina 2002** (p. 13 of arXiv:math/0111264): the constant
  `inf {24 α⁻¹ β⁻² + 2(1 − α)⁻¹ : α, β ∈ (0, 1)}` is `26 + 8√3`, not `14√3/3 + 28`. Cuculescu's
  projections: the spectral projections are to be taken in the reduced algebra, as they would not
  decrease otherwise (Proposition 2.4, p. 6). Theorem 4.3, "by interpolation": not detailed.
- **Kristensen 1999**, p. 7: `ξ_s` (convex, `0` below `s − 1`, `t²` above `s + 1`) exists only for
  `s < 3`, since convexity at `s + 1` gives `0 = ξ_s(s − 1) ≥ (s + 1)² − 4(s + 1)`; how `s` is chosen is
  not said.
- **Kinderlehrer–Pedregal 1991**, Proposition 8.1: (i) needs `|∂D| = 0`, which the introduction asks
  (p. 331) and the proposition does not repeat; `f^{qc} = ψ^#` is not stated.
- **Lust-Piquard–Pisier 1991**, p. 252: "proof p. 204" of Sarason 1967, which ends on p. 203 (the proof
  of its Theorem 4 is on pp. 200–201). **Pisier, Astérisque 247**, p. 106: the type 2 constant of `S_p` is
  quoted from Tomczak-Jaegermann "at least when `p` is an even integer"; the other `p` are in her
  Theorem 3.1 (ii).
- **McConnell 1984.** Pp. 741–742: with the dyadic intervals of p. 741, the series `T_{(ε)} f` of p. 742
  makes no sense; Theorem 1.3 means the intervals `±[2^j, 2^{j+1})` (p. 755). P. 746, (3.1): `|λ|^{|α|}`,
  not `|λ|^α`; with the normalization (1.1), `T_m f = (2π)^{−n} M ∗ f`, so (3.3) and (3.4) lack this factor
  (immaterial). Pp. 747–748: the limit of `g_N` is `2 (n + 1)! (−4)^{−(n+2)} T_m^A f`; the factor is
  misprinted on p. 747 and, differently, on p. 748. P. 747: the second mean value theorem for integrals
  fails for vector-valued `u`, and can fail for scalar `u` if `u_y` changes sign; `u_y(s − x, y_i + 2y)`
  stands for `u_y(x − s, y_i + 2y)`, and a bracket is missing. Pp. 749–750 and 755–756: (2.1), stated for
  real coefficients, is applied to complex ones (`e(X̃(y_i), y_i)`, unless `m` is even, and `ε_j e^{iα_j x}`).
  Pp. 750–751: in (3.11) and after it the differences have the sign opposite to `(Δu)_i` (immaterial).
  P. 751: the measures `P_{(x',A)}` must start at a height not below `y_{N−1} + y_N`, which exceeds
  `A = y_N` if `N > 1`. P. 754: `φ(3/2) = 1` does not make `ψ` smooth; `φ = 1` near `3/2` does. P. 755:
  Theorem 1.1, stated for `m` of class `C^{n+1}` on `ℝⁿ`, is applied to `m_i` and `M`, which are not
  continuous at `0` (its proof needs `m` only off `0`); (3.19) is an inequality in both directions, by
  Theorem 1.1, not an equality. P. 756, last display: `‖T_{m₁} T_m f‖` stands for `‖T_{m₁} T_m f‖_p^p`.
- **Burkholder 1983** (Lemma 2). P. 279: the Taylor estimate, printed with `<`, needs `≤` (it fails for
  `u = 0`). P. 280: the `k`-th term of the martingale difference sequence of `W^j` is said to be bounded by
  `k²δ²`; the bound is `N²δ²w_k`, as p. 281 uses it (for `u = 2xy` the first term is `±2δ²`). Without
  proof: the function `K_r` of p. 283 ("there is a nonnegative function"), Lemma 4 (referred to M. Riesz
  and Zygmund), Theorem 2 (p. 284).
- **M. Riesz 1928**, §18 (p. 234): "on démontre très facilement que lim f̃_n(x) = f̃(x). Nous ne nous y
  arrêtons pas": written out, for the truncations, by dominated convergence.
- **Helson–Lowdenslager 1958**, p. 173 (Lemma 2, used for Lemma 5): "for each `n` there is an `m`" with
  `∫ u_n ≤ ∫ v_m` fails for the truncations `u_n = min (u, n)`, `v_m = min (v, m)` if `u` is bounded and `v`
  is not. **1961**, (131) (p. 204): two logarithms are missing; p. 207: that `B` has full rank ends with a
  step that is not proved.
- **Tomczak-Jaegermann 1974**, pp. 166–167: the three lines theorem quoted from Gohberg–Krein, and
  Proposition 1.2, need `Ψ` bounded (`Ψ(z) = exp (exp (iπ(z − 1/2)))` has modulus `1` on both lines, and `Ψ(1/2) = e`).
- **Burkholder 1988**, Remark 1.2, **Dragičević 2011**, p. 465 (`f ∈ W^{n,p}`), and **Maurey–Pisier
  1976**, Remark 2.10: stated without proof.

## 8. What each result depends on

From [`scripts/Audit.lean`](../../scripts/Audit.lean), which also checks every declaration of the
library: every result below depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). The
third column lists the results of other works that each one uses, all proved
(Section 2); none is a hypothesis.

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Section 1.1 (monotonicity) | [`Cassese.morreyPositive_mono`](../../Morrey/Cassese/Introduction.lean#L405) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128) |
| Section 1.1 (min (d, m) = 1) | [`Cassese.rankOneConvex_iff_convexOn_of_min_eq_one`](../../Morrey/Cassese/Introduction.lean#L431) | – |
| Section 1.1 (min (d, m) = 1) | [`Cassese.quasiconvex_iff_convexOn_of_min_eq_one`](../../Morrey/Cassese/Introduction.lean#L460) | [`External.Rindler.rankOneConvex_of_quasiconvex`](../../Morrey/Common/External/Rindler/Lemmas.lean#L88) |
| Section 1.1 (min (d, m) = 1) | [`Cassese.morreyPositive_of_min_le_one`](../../Morrey/Cassese/Introduction.lean#L476) | – |
| Section 1.1 (Šverák's example) | [`Cassese.sverak_example`](../../Morrey/Cassese/Sverak.lean#L32) | – |
| Thm 1.1 (Kirchheim–Kristensen, quoted) | [`External.KirchheimKristensen.Theorem1_1`](../../Morrey/Common/External/KirchheimKristensen/Theorem.lean#L25) | – |
| Section 1.3 (homogeneous monotonicity) | [`Cassese.homMorreyPositive_mono`](../../Morrey/Cassese/Introduction.lean#L419) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128) |
| Thm 1.2 | [`Cassese.theorem1_2`](../../Morrey/Cassese/Introduction.lean#L1989) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`External.HNVW.theorem4_2_7`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L55), [`External.Pisier.corollary5_22`](../../Morrey/Common/External/Pisier/LpUMD.lean#L40), [`External.Yaroslavtsev.lemma3_2`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean#L54) |
| Thm 1.3 (a) | [`Cassese.theorem1_3_a`](../../Morrey/Cassese/Introduction.lean#L2027) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Thm 1.3 (b) | [`Cassese.theorem1_3_b`](../../Morrey/Cassese/Introduction.lean#L2052) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Section 1.4 (2 × 2 landscape) | [`Cassese.morrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2241) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Section 1.4 (homogeneous landscape) | [`Cassese.homMorrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2269) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Thm 1.4 | [`Cassese.theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2084) | [`External.Osekowski.squareFunction`](../../Morrey/Common/External/Osekowski/Inequality.lean#L119), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`External.HNVW.theorem4_2_7`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L55), [`External.Randrianantoanina.remark4_6`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L67), [`External.CoxVeraar.decoupling`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean#L51), [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74), [`External.HNVW.theorem6_2_4_seminorm`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L58) |
| Thm 1.5 | [`Cassese.theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2167) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`External.HNVW.transference_beurlingPow`](../../Morrey/Common/External/HNVW/Transference.lean#L56), [`External.Dragicevic.theorem1_1_two_pStar`](../../Morrey/Common/External/Dragicevic/LowerBound.lean#L64) |
| Cor 1.6 | [`Cassese.corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2215) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`External.HNVW.transference_beurlingPow`](../../Morrey/Common/External/HNVW/Transference.lean#L56), [`External.Dragicevic.theorem1_1_two_pStar`](../../Morrey/Common/External/Dragicevic/LowerBound.lean#L64) |
| Lemma 2.1 (Rindler, cited) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) | – |
| Lemma 2.2 (Rindler, cited) | [`External.Rindler.rankOneConvex_of_quasiconvex`](../../Morrey/Common/External/Rindler/Lemmas.lean#L88) | – |
| Lemma 2.2 (Rindler, cited) | [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109) | – |
| Lemma 2.2 (Rindler, cited) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128) | – |
| Prop 2.1 | [`Cassese.proposition2_1`](../../Morrey/Cassese/Toolkit.lean#L780) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Prop 2.2 (Kinderlehrer–Pedregal, cited) | [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) | – |
| Section 2.1 (quasiconvex minorants) | [`Cassese.quasiconvexAt_iff_exists_minorant`](../../Morrey/Cassese/Toolkit.lean#L1177) | [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 2.3 (a) | [`Cassese.proposition2_3_a`](../../Morrey/Cassese/Toolkit.lean#L1286) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 2.3 (b) | [`Cassese.proposition2_3_b`](../../Morrey/Cassese/Toolkit.lean#L1458) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 2.3 (c) | [`Cassese.proposition2_3_c`](../../Morrey/Cassese/Toolkit.lean#L1565) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.rankOneConvex_of_quasiconvex`](../../Morrey/Common/External/Rindler/Lemmas.lean#L88), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 2.3 (c), one direction | [`Cassese.proposition2_3_c_left`](../../Morrey/Cassese/Toolkit.lean#L1596) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.envelope_zero`](../../Morrey/Cassese/Toolkit.lean#L1608) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.rankOneConvexAt_zero_of_rankOneConvexAt`](../../Morrey/Cassese/Toolkit.lean#L1639) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.quasiconvexAt_zero_of_quasiconvexAt`](../../Morrey/Cassese/Toolkit.lean#L1661) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.nowhereQuasiconvex_of_not_quasiconvexAt_zero`](../../Morrey/Cassese/Toolkit.lean#L1683) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 2.4 | [`Cassese.proposition2_4`](../../Morrey/Cassese/Toolkit.lean#L762) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Prop 2.5 | [`Cassese.proposition2_5`](../../Morrey/Cassese/Toolkit.lean#L1935) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Thm 2.3 (1) (Burkholder, cited) | [`Cassese.burkholderInequality_holds`](../../Morrey/Cassese/Hypotheses.lean#L116) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82) |
| Thm 2.3 (2) (Burkholder, cited) | [`Cassese.burkholderSquareFunction_holds`](../../Morrey/Cassese/Hypotheses.lean#L125) | [`External.Osekowski.squareFunction`](../../Morrey/Common/External/Osekowski/Inequality.lean#L119) |
| Prop 2.6 (Osękowski, quoted) | [`External.Osekowski.HilbertCharacterization`](../../Morrey/Common/External/Osekowski/HilbertCharacterization.lean#L48) | – |
| Prop 2.7 (1) (HNVW, cited) | [`Cassese.hnvwExtrapolation_holds`](../../Morrey/Cassese/Hypotheses.lean#L508) | [`External.HNVW.theorem4_2_7`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L55) |
| Prop 2.7 (2) (Randrianantoanina, cited) | [`Cassese.randrianantoaninaSchattenUMD_holds`](../../Morrey/Cassese/Hypotheses.lean#L518) | [`External.Randrianantoanina.remark4_6`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L67) |
| Prop 2.7 (3) (Pisier, cited) | [`Cassese.pisierLpUMD_holds`](../../Morrey/Cassese/Hypotheses.lean#L532) | [`External.Pisier.corollary5_22`](../../Morrey/Common/External/Pisier/LpUMD.lean#L40) |
| Prop 2.7 (4) (HNVW, cited) | [`Cassese.hnvwDyadicUMD_holds`](../../Morrey/Cassese/Hypotheses.lean#L538) | [`External.HNVW.theorem4_2_5`](../../Morrey/Common/External/HNVW/DyadicUMD.lean#L39) |
| Prop 2.7 (5) (Yaroslavtsev, cited) | [`Cassese.yaroslavtsevComplexUMD_holds`](../../Morrey/Cassese/Hypotheses.lean#L544) | [`External.Yaroslavtsev.lemma3_2`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean#L54) |
| Prop 2.7 (6) (HNVW, Yaroslavtsev, cited) | [`Cassese.hnvwZigZag_holds`](../../Morrey/Cassese/Hypotheses.lean#L554) | [`External.Yaroslavtsev.lemma3_2`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean#L54), [`External.HNVW.theorem4_5_6`](../../Morrey/Common/External/HNVW/ZigZag.lean#L52), [`External.Yaroslavtsev.proposition3_7`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean#L63), [`External.Yaroslavtsev.proposition3_7_iff`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean#L71) |
| Prop 2.8 (Cox–Veraar, cited) | [`Cassese.coxVeraarDecoupling_holds`](../../Morrey/Cassese/Hypotheses.lean#L567) | [`External.CoxVeraar.decoupling`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean#L51) |
| Lemma 4.1 | [`Cassese.lemma4_1`](../../Morrey/Cassese/TwoByM.lean#L229) | – |
| Prop 4.1 | [`Cassese.proposition4_1`](../../Morrey/Cassese/TwoByM.lean#L431) | – |
| Prop 4.1 (nonnegativity) | [`Cassese.proposition4_1_nonneg`](../../Morrey/Cassese/TwoByM.lean#L632) | – |
| Eq. (10) | [`Cassese.equation10`](../../Morrey/Cassese/TwoByM.lean#L667) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Section 4.2 (UMD of ℓ_q) | [`Cassese.umdEllq_lt_top`](../../Morrey/Cassese/TwoByM.lean#L690) | [`External.HNVW.theorem4_2_7`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L55), [`External.Pisier.corollary5_22`](../../Morrey/Common/External/Pisier/LpUMD.lean#L40), [`External.Yaroslavtsev.lemma3_2`](../../Morrey/Common/External/Yaroslavtsev/ComplexUMD.lean#L54) |
| Section 4.3 (limiting argument) | [`Cassese.twoByM_ratio_le_qcThreshold`](../../Morrey/Cassese/TwoByM.lean#L3011) | – |
| Lemma 4.2 | [`Cassese.lemma4_2`](../../Morrey/Cassese/TwoByM.lean#L1585) | – |
| Eqs. (13), (14) (Burkholder, cited) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L142) | [`External.Burkholder.scalarFunctionQ_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L123) |
| Prop 4.2 | [`Cassese.proposition4_2`](../../Morrey/Cassese/TwoByM.lean#L2197) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L142) |
| Prop 4.2 (the minorant) | [`Cassese.proposition4_2_minorant`](../../Morrey/Cassese/TwoByM.lean#L2155) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L142) |
| Section 4.3 (limiting argument, for f_n) | [`Cassese.twoByM_not_qc_explicitF`](../../Morrey/Cassese/TwoByM.lean#L2602) | – |
| Prop 4.3 | [`Cassese.proposition4_3`](../../Morrey/Cassese/TwoByM.lean#L2799) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L142), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Remark 4.5 (Thm 1.2, elementary route) | [`Cassese.theorem1_2_elementary`](../../Morrey/Cassese/TwoByM.lean#L3480) | [`External.Burkholder.scalarFunctionQ_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L123), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 5.1 | [`Cassese.proposition5_1`](../../Morrey/Cassese/TwoByThree/Folklore.lean#L260) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Dacorogna.rankOneAffineMinors_holds`](../../Morrey/Common/External/Dacorogna/Minors.lean#L75), [`External.Dacorogna.minor3_quasiaffine`](../../Morrey/Common/External/Dacorogna/Minors.lean#L87), [`External.Dacorogna.quadraticForm_quasiconvex`](../../Morrey/Common/External/Dacorogna/Minors.lean#L104) |
| Section 5.1 (q rank-one convex on 𝓛) | [`Cassese.quarticQ_rankOneConvexOn_calL`](../../Morrey/Cassese/TwoByThree/Basic.lean#L359) | – |
| Section 5.2 (q₃ rank-one convex on 𝓛₃) | [`Cassese.q3_rankOneConvexOn_L3`](../../Morrey/Cassese/TwoByThree/Basic.lean#L367) | – |
| Eq. (24) | [`Cassese.equation24`](../../Morrey/Cassese/TwoByThree/Basic.lean#L381) | – |
| Prop 5.2 | [`Cassese.proposition5_2`](../../Morrey/Cassese/TwoByThree/Witness.lean#L1327) | – |
| Lemma 5.1 (1) | [`Cassese.lemma5_1_part1`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L436) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Lemma 5.1 (1), with constants | [`Cassese.lemma5_1_part1_quant`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L324) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Lemma 5.1 (2) | [`Cassese.lemma5_1_part2`](../../Morrey/Cassese/TwoByThree/Extension.lean#L276) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Proof of Thm 1.3 (κ = 2) | [`Cassese.tbt_correction_identity`](../../Morrey/Cassese/TwoByThree/Basic.lean#L459) | – |
| Proof of Thm 1.3 (κ = 2) | [`Cassese.L3_rankOneCorrection`](../../Morrey/Cassese/TwoByThree/Basic.lean#L481) | – |
| Proof of Thm 1.3 (q_{δ,K/δ} rank-one convex) | [`Cassese.qDeltaLambda_rankOneConvex`](../../Morrey/Cassese/TwoByThree/Extension.lean#L542) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Proof of Thm 1.3 (a) (the witness) | [`Cassese.twoByThree_not_quasiconvexAt_qDeltaLambda`](../../Morrey/Cassese/TwoByThree/WitnessCutoff.lean#L1030) | – |
| Proof of Thm 1.3 (b) (the witness) | [`Cassese.twoByThree_theorem1_3_b_witness`](../../Morrey/Cassese/TwoByThree/NearFour.lean#L860) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Cor 5.2 | [`Cassese.corollary5_2`](../../Morrey/Cassese/NonLocality.lean#L32) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`External.Kristensen.smoothing_holds`](../../Morrey/Common/External/Kristensen/Smoothing.lean#L106) |
| Cor 5.3 | [`Cassese.corollary5_3`](../../Morrey/Cassese/TwoByThree/Transpose.lean#L197) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Cor 5.4 | [`Cassese.corollary5_4`](../../Morrey/Cassese/TwoByThree/HessianCutoff.lean#L408) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Prop 6.1 | [`Cassese.proposition6_1`](../../Morrey/Cassese/Square.lean#L2602) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128) |
| Prop 6.2 | [`Cassese.proposition6_2`](../../Morrey/Cassese/Square.lean#L1016) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Randrianantoanina.remark4_6`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L67), [`External.CoxVeraar.decoupling`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean#L51), [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74), [`External.HNVW.theorem6_2_4_seminorm`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L58) |
| Prop 6.3 (Pisier–Xu, cited) | [`Cassese.pisierXuKhintchine_holds`](../../Morrey/Cassese/Hypotheses.lean#L666) | [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74) |
| Prop 6.4 (Kahane–Khintchine, cited) | [`Cassese.kahaneKhintchine_holds`](../../Morrey/Cassese/Hypotheses.lean#L673) | [`External.HNVW.theorem6_2_4_seminorm`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L58) |
| Eq. (31) | [`Cassese.equation31`](../../Morrey/Cassese/Square.lean#L816) | [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74), [`External.HNVW.theorem6_2_4_seminorm`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L58) |
| Remark 6.3 | [`Cassese.remark6_3`](../../Morrey/Cassese/Square.lean#L1219) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Randrianantoanina.remark4_6`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L67), [`External.CoxVeraar.decoupling`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean#L51), [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74), [`External.HNVW.theorem6_2_4_hypercontractive`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L48) |
| Prop 6.5 | [`Cassese.proposition6_5`](../../Morrey/Cassese/Square.lean#L1895) | [`External.Osekowski.squareFunction`](../../Morrey/Common/External/Osekowski/Inequality.lean#L119), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.HNVW.theorem4_2_7`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L55), [`External.Randrianantoanina.remark4_6`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L67), [`External.CoxVeraar.decoupling`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean#L51), [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74), [`External.HNVW.theorem6_2_4_seminorm`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L58), [`External.HNVW.theorem6_2_4_hypercontractive`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L48) |
| Prop 6.5 (q < ∞) | [`Cassese.proposition6_5_finite`](../../Morrey/Cassese/Square.lean#L1722) | [`External.Osekowski.squareFunction`](../../Morrey/Common/External/Osekowski/Inequality.lean#L119), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.HNVW.theorem4_2_7`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L55), [`External.Randrianantoanina.remark4_6`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L67), [`External.CoxVeraar.decoupling`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean#L51), [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74), [`External.HNVW.theorem6_2_4_seminorm`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L58) |
| Prop 6.5 (q = ∞) | [`Cassese.proposition6_5_infty`](../../Morrey/Cassese/Square.lean#L1770) | [`External.Osekowski.squareFunction`](../../Morrey/Common/External/Osekowski/Inequality.lean#L119), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.HNVW.theorem4_2_7`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L55), [`External.Randrianantoanina.remark4_6`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L67), [`External.CoxVeraar.decoupling`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean#L51), [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74), [`External.HNVW.theorem6_2_4_hypercontractive`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L48) |
| Cor 6.1 | [`Cassese.corollary6_1`](../../Morrey/Cassese/Square.lean#L2259) | [`External.Osekowski.squareFunction`](../../Morrey/Common/External/Osekowski/Inequality.lean#L119), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`External.HNVW.theorem4_2_7`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L55), [`External.Randrianantoanina.remark4_6`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L67), [`External.CoxVeraar.decoupling`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean#L51), [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74), [`External.HNVW.theorem6_2_4_seminorm`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L58) |
| Cor 6.1 (every large d) | [`Cassese.corollary6_1_ge`](../../Morrey/Cassese/Square.lean#L2274) | [`External.Osekowski.squareFunction`](../../Morrey/Common/External/Osekowski/Inequality.lean#L119), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`External.HNVW.theorem4_2_7`](../../Morrey/Common/External/HNVW/Extrapolation.lean#L55), [`External.Randrianantoanina.remark4_6`](../../Morrey/Common/External/Randrianantoanina/SchattenUMD.lean#L67), [`External.CoxVeraar.decoupling`](../../Morrey/Common/External/CoxVeraar/Decoupling.lean#L51), [`External.PisierXu.theorem6_1`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L74), [`External.HNVW.theorem6_2_4_seminorm`](../../Morrey/Common/External/HNVW/KahaneKhintchine.lean#L58) |
| Proof of Cor 6.1 (periodic Hessian test maps) | [`Cassese.not_hessianQuasiconvexAt_of_periodic`](../../Morrey/Cassese/Square.lean#L1925) | – |
| Proof of Cor 6.1 (periodic Hessian test maps) | [`Cassese.square_not_hessianQuasiconvexAt_of_periodic`](../../Morrey/Cassese/Square/Hessian.lean#L204) | – |
| Prop 6.6 | [`Cassese.proposition6_6`](../../Morrey/Cassese/Square.lean#L2752) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128) |
| Thm 6.2 | [`Cassese.theorem6_2`](../../Morrey/Cassese/Square.lean#L2805) | – |
| Cor 6.3 (lower bound) | [`Cassese.corollary6_3_lower`](../../Morrey/Cassese/Square.lean#L2940) | [`External.Osekowski.exists_lt_lpNorm_transform`](../../Morrey/Common/External/Osekowski/Sharpness.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Cor 6.3 (upper bound) | [`Cassese.corollary6_3_upper`](../../Morrey/Cassese/Square.lean#L3076) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Cor 6.3 (separation) | [`Cassese.corollary6_3_separation`](../../Morrey/Cassese/Square.lean#L3174) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128) |
| Cor 6.4 | [`Cassese.corollary6_4`](../../Morrey/Cassese/Square.lean#L3475) | – |
| Cor 6.4 (not quasiconvex) | [`Cassese.corollary6_4_not_quasiconvexAt`](../../Morrey/Cassese/Square.lean#L3524) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128) |
| Thm 1.4, p = 4 (Section 6.3) | [`Cassese.theorem1_4_four`](../../Morrey/Cassese/Square.lean#L3586) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L109), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 7.1 | [`Cassese.proposition7_1`](../../Morrey/Cassese/FourByTwo.lean#L344) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71) |
| Prop 7.2 | [`Cassese.proposition7_2`](../../Morrey/Cassese/FourByTwo.lean#L1076) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128) |
| Prop 7.2 (lower bound) | [`Cassese.proposition7_2_lower`](../../Morrey/Cassese/FourByTwo.lean#L1092) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.HNVW.transference_beurlingPow`](../../Morrey/Common/External/HNVW/Transference.lean#L56) |
| Thm 7.1 | [`Cassese.theorem7_1`](../../Morrey/Cassese/FourByTwo.lean#L1262) | [`External.Osekowski.inequality`](../../Morrey/Common/External/Osekowski/Inequality.lean#L82), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L71), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.HNVW.transference_beurlingPow`](../../Morrey/Common/External/HNVW/Transference.lean#L56), [`External.Dragicevic.theorem1_1_two_pStar`](../../Morrey/Common/External/Dragicevic/LowerBound.lean#L64) |
| Cor 7.2 | [`Cassese.corollary7_2`](../../Morrey/Cassese/FourByTwo.lean#L1603) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L128), [`External.HNVW.transference_beurlingPow`](../../Morrey/Common/External/HNVW/Transference.lean#L56), [`External.Dragicevic.theorem1_1_two`](../../Morrey/Common/External/Dragicevic/LowerBound.lean#L52) |
| Conjecture 1 (stated) | [`Cassese.Conjecture1`](../../Morrey/Cassese/Conclusion.lean#L18) | – |

The route check ([`scripts/route_check.py`](../../scripts/route_check.py) with [`paper_routes.tsv`](paper_routes.tsv)) finds 67
results of the paper in the Lean code and checks that each proof uses the results that the paper's
proof cites. It finds ten differences, all recorded with their reasons in
[`route_differences.tsv`](route_differences.tsv): the departure of Proposition 2.5 (E10), three
uses that the paper leaves implicit (Lemma 2.2 at line 559, E22; Lemma 2.1 for the minorant `G`,
E21; Lemma 4.1 in the proof of Theorem 1.3 (b)), and six places where the paper cites a proof or a
definition rather than a statement.

## 9. Not formalized

- Claims that the paper states without proof and that no argument uses: Corollary 1.6 for `p > 2`
  (E18) and the remark that the construction adapts to Theorems 1.2 and 1.4 (lines 2956–2958);
  Remarks 2.2, 2.4, 4.1–4.4, 5.1–5.4, 6.1, 6.2, 6.4, 6.5, 7.1 and 7.2 (5.2: a positively
  3-homogeneous example from Šverák's; 5.3: the Cayley hyperdeterminant and extremality; 5.4:
  examples on `2 × 3` and `3 × 2` for `p ∈ (3.6, 5.15)`); the versions for `Sym₀`, `Skew_tr` and
  `h_{p,q,C}` (lines 2521–2549); "Considering `g(AJ)` also gives another counterexample to
  Hessian-quasiconvexity" (lines 2691–2692); `p = 4` in the proof of Theorem 7.1 (lines 2882–2884); the failure of the
  vector-valued estimate for `q > 4` (§8.2).
- Interpretations that combine the paper with work not formalized here: "quasiconvexity is
  nonlocal among smooth integrands" (lines 2061–2064, through Kristensen's theorem), the
  concentration interpretation (lines 279–288), and the relation of Corollary 1.6 to Gennaioli and
  Rindler's work (lines 303–312).
- Context only: Kirchheim–Kristensen's theorem (Theorem 1.1) and its consequence at lines
  186–188, Osękowski's Proposition 2.6, Grabovsky's examples (lines 144–156, 201–204), Iwaniec's bound
  `C^{rc} ≤ p* − 1` (lines 763–765), and the history of Remarks 2.3 and 3.1. Theorem 1.1 and
  Proposition 2.6 are stated ([`External.KirchheimKristensen.Theorem1_1`](../../Morrey/Common/External/KirchheimKristensen/Theorem.lean#L25),
  [`External.Osekowski.HilbertCharacterization`](../../Morrey/Common/External/Osekowski/HilbertCharacterization.lean#L48)) and not proved.
- Conjecture 1 is stated as a definition ([`Conjecture1`](../../Morrey/Cassese/Conclusion.lean#L18)), not proved.

## 10. The paper in the literature

Searched on 21 November 2026: arXiv (the paper's listing and versions, and the listings that cite
it), journal pages, zbMATH and Crossref, and GitHub for formalizations. Preprints are reported as
claimed, not as proved.

### Before the paper

- Morrey (1952) introduced quasiconvexity and asked whether rank-one convexity implies it. Ball
  (1990) gave a counterexample among extended-valued integrands; Šverák (1992) gave the first
  real-valued one, on `ℝ^{3×2}`, hence for `d ≥ 3` components ([formalized here](../Sverak/README.md)).
  For two components the question stayed open: positive results in special classes (Müller 1999,
  diagonal matrices; Chaudhuri–Müller 2003; Harris–Kirchheim–Lin 2018), Kristensen's non-locality
  theorem (1999), the connection with Burkholder's function and Iwaniec's conjecture (Astala,
  Iwaniec, Prause, Saksman, J. Amer. Math. Soc. 2012), Sebestyén and Székelyhidi's theorem (2017)
  that the gradient measures produced from periodic deformations by Šverák's procedure are
  laminates in `2 × 2`, and numerical evidence (Guerra and Teixeira da Costa, Rev. Mat. Iberoam.
  2022).
- Grabovsky (Arch. Ration. Mech. Anal. 2018) gave the only other finite-valued family before 2026,
  on `ℝ^{8×2}`; its examples are nonnegative, hence quasiconvex at `0`.
- Kirchheim and Kristensen (Arch. Ration. Mech. Anal. 221 (2016)) proved that positively
  1-homogeneous rank-one convex integrands are convex at rank-one matrices; according to the paper
  (lines 189–191), they asked the homogeneous problem for `p > 1`. Guerra and Kristensen (Arch.
  Ration. Mech. Anal. 245 (2022)) proved automatic quasiconvexity for homogeneous isotropic
  integrands, the background of Conjecture 1.
- Pedregal's claimed proof for two-component maps
  ([arXiv:1905.06571](https://arxiv.org/abs/1905.06571), [audited here](../Pedregal/README.md)):
  versions 1–2 (May and September 2019) claimed every `2 × N`; version 3 (August 2024) was a
  withdrawal; versions 4–5 (May 2025, June 2026) claim only `2 × 2`. The paper does not cite it.
  Its Theorem 1.2, and its `2 × 3` example, contradict the claim of the withdrawn versions 1–2 for
  `N ≥ 3`.
- The method rests on the author's correspondence between laminates and martingales (Cassese,
  *Martingales, laminates and minimal Korn inequalities*, J. Math. Pures Appl. 213 (2026),
  [arXiv:2512.02784](https://arxiv.org/abs/2512.02784)) and on Burkholder's martingale
  inequalities; Remarks 4.1 and 6.4 also use Cassese,
  [arXiv:2603.22431](https://arxiv.org/abs/2603.22431).

### The paper's versions

- v1 (4 August 2026): `2 × m` for large `m`, the square case `d × d` (now Theorem 1.4) and `4 × 2`
  (now Theorem 1.5).
- v2 (28 August 2026): adds a quartic on `2 × 4` and the Hessian corollary (now Corollary 6.1).
- v3 (16 September 2026, formalized here): replaces the `2 × 4` quartic by the `2 × 3` one, adds
  its transpose on `3 × 2` (as a sketch), Corollary 1.6, and the claim that only `2 × 2` remains.
  No journal version or erratum was found.

### Concurrent work

- Bruno and Pasqualotto ([arXiv:2608.06367](https://arxiv.org/abs/2608.06367), 6 August 2026),
  *Quasiconvexity for the Dacorogna–Marcellini Energy*: the planar Dacorogna–Marcellini energy is
  quasiconvex exactly when it is rank-one convex, that is when `|γ| ≤ 2/√3`; as a corollary,
  quasiconvexity is equivalent to rank-one convexity for homogeneous quartics on `2 × 2` invariant
  under left and right rotations.
- Agazzi, Bruno, Guerra and Pasqualotto ([arXiv:2608.12298](https://arxiv.org/abs/2608.12298),
  12 August 2026, between v1 and v2): a non-homogeneous example on `ℝ^{2×4}` from Grabovsky's
  integrand, and examples on symmetric matrices.
- Gennaioli and Rindler ([arXiv:2608.20899](https://arxiv.org/abs/2608.20899), 21 August 2026):
  the Vanishing Mass Conjecture; the paper relates it to Corollary 1.6.
- Guerra ([arXiv:2608.23388](https://arxiv.org/abs/2608.23388), 24 August 2026): the Burkholder
  function is quasiconvex on symmetric matrices; the paper uses it in Remark 6.4.

### Since the paper

- Scalabrino ([arXiv:2610.22560](https://arxiv.org/abs/2610.22560), 15 October 2026) uses
  Corollary 1.6; Conti, Dolzmann and Dondl ([arXiv:2610.31886](https://arxiv.org/abs/2610.31886),
  22 October 2026) give a frame-indifferent, non-isotropic example on `ℝ^{3×3}` and cite v3;
  Braides, Kristensen and Scalabrino ([arXiv:2610.32444](https://arxiv.org/abs/2610.32444),
  23 October 2026) cite the paper; Gammer ([arXiv:2610.35216](https://arxiv.org/abs/2610.35216),
  26 October 2026) uses its integrand. No correction of the paper and no counterexample to it were
  found.
- Agazzi, Astala, Bañuelos, Bruno, Cassese, Faraco, Guerra, Hormozi, Kirchheim, Koski, Kovač,
  Kristensen, Pasqualotto, Prause, Saksman, Šverák, Székelyhidi, Tione, Volberg and Yang
  ([arXiv:2609.28311](https://arxiv.org/abs/2609.28311), 23 September 2026, v2 8 October 2026)
  claim a proof of Iwaniec's conjecture, `‖𝓑‖_{L^p} = p* − 1`, which the paper treats as open
  (§1.3, Remarks 4.3, 6.4, 7.1, §8.1). By the paper's equivalence (lines 1158–1162), the
  integrands behind Theorem 1.2 would then give no counterexample in `2 × 2` (the case `n = 1`);
  the `2 × 2` problem itself stays open.

### Formalizations

- The author formalized Theorem 1.2 and Theorem 1.3 at `p = 4` in Lean (v4.32.2)
  ([MorreyTwoComponentsLean](https://github.com/Gabriele-Cassese/MorreyTwoComponentsLean)), with an
  AI system (the paper's declaration names ChatGPT 5.6 Sol), released without a license; the
  `2 × 3` file was added after v3 and is not in its default build. This formalization covers the
  whole paper, including what the author's does not: Theorems 1.4 and 1.5, Corollaries 1.6 and
  5.2–5.4, Sections 6 and 7, and the cited results that the proofs use.
- Conti, Dolzmann and Dondl's Lean code for their `3 × 3` example
  ([sergioconti/so3-r1c-and-not-qc](https://github.com/sergioconti/so3-r1c-and-not-qc),
  Apache-2.0, written with Claude Opus 5.5 under the authors' guidance) shares the subject, not the
  results.
- The proofs here were written without consulting either, and nothing from them was used. Parts of
  both were displayed on 21 and 22 November 2026 by searches for earlier formalizations and for the
  literature, and by checks of the documents: [`CREDITS.md`](CREDITS.md) says which.
- The cited results are proved in three Lake packages written for this formalization, which
  depend only on Mathlib (and the vector-valued part of lean4-harmonic-analysis on
  lean4-banach-probability) and are published on GitHub, pinned by commit in [`lakefile.toml`](../../lakefile.toml):
  [lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis),
  [lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability) and
  [lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations).
- Other formalizations of cited results, all in Lean, found on 22 November 2026 after the packages'
  proofs (for the non-commutative Khintchine inequality, after its first proof in each package; the
  packages' READMEs give the searches, the overlaps and the rest): Burkholder's inequality
  for real martingales ([SmaniaD/Burkholder](https://github.com/SmaniaD/Burkholder)); a UMD constant
  and cases of Burkholder's inequality
  ([elorist/UMD_Hilberttransform](https://github.com/elorist/UMD_Hilberttransform)); the
  Kahane–Khintchine inequality and the Schatten triangle inequality
  ([Tau Ceti](https://github.com/TauCetiProject/TauCeti)); the upper bound of the non-commutative
  Khintchine inequality for Hermitian matrices in `S_{2p}`, `p ∈ ℕ`
  ([NLAlib](https://github.com/tchen-research/NLAlib)); the Beurling–Ahlfors transform on `L^p`
  (Tau Ceti; `will1491/no-wandering-domains`); null Lagrangians
  ([PDEAtlas](https://github.com/Robertboy18/PDEAtlas)). None was used here.

## 11. What's next

Plans for follow-up papers are kept in `NEXT.md`, which is not published.

### Open directions

- **`2 × 2`.** The homogeneous problem in `2 × 2` is open; the paper expects a positive answer, and
  notes that it would imply Iwaniec's conjecture, so that a proof must use features of the plane
  (§8.1). Iwaniec's conjecture is now claimed proved
  ([arXiv:2609.28311](https://arxiv.org/abs/2609.28311), Section 10), which removes that
  obstruction but does not decide the problem.
- **A value of `m₀`.** The proof of Theorem 1.2 gives no value of `m₀(p)`; the paper expects
  `m_*(p) ≤ m₀(p) ≤ 4` and conjectures `m_*(p) ≤ 3` (line 1385).
- **`2 × 3` and `3 × 2` for every `p`.** Claimed for `p ∈ (3.6, 5.15)` (Remark 5.4); proved here
  on `2 × 3` for `p` near `4`, and on `3 × 2` at `p = 4`.
- **Theorem 1.4.** `d₀ = 588` for `h_{4,4,C}` is not expected to be optimal (numerics suggest `260`;
  Remark 6.4), and for the integrand (30) the paper expects `d = 3`.
- **Remark 7.2** (`ρ = √2` for every `p`); **Remark 5.3** (the extremality of `q` and `q₃`);
  **§8.2** (the Banach-space geometry viewpoint); **Corollary 1.6** for `p > 2` (E18) and in lower
  dimension; the claims for `Sym₀`, `Skew_tr` and `h_{p,q,C}` (lines 2521–2549).
- **Conjecture 1**: isotropic `p`-homogeneous rank-one convex integrands on `ℝ^{d×d}` are
  quasiconvex at `0`.

### Simpler proofs

Simpler arguments found while proving. The formal proofs follow the paper and the cited sources,
except where the last column says "the proof used"; the last column says where each simpler argument
was checked: in Lean (in a library, in the history of this repository or of a package, or in a file
outside the libraries that compiles against the commit named), or on paper.

Steps of the paper:

| Step | The paper's argument | The simpler one, and what it saves | Checked |
| --- | --- | --- | --- |
| Proposition 4.3 (and the route of Remark 4.5) | if `g_n` were quasiconvex at `0`, `0 = g_n(0) = g_n^{qc}(0) ≤ f_n^{qc}(0) ≤ f_n(0) = 0`, which needs Dacorogna's formula for `g_n^{qc}(0) = g_n(0)` | for every test map, `∫ f_n(∇φ) ≥ ∫ g_n(∇φ) ≥ g_n(0) = f_n(0)`; no envelope, no Dacorogna's formula | in Lean: [`twoByM_quasiconvexAt_of_minorant`](../../Morrey/Cassese/TwoByM.lean#L3442), in the library, used by no proof |
| Theorem 1.3 (a) (and Corollary 5.4) | `I = ∫_{ℝ³} q₃(∇u) < 0`, and Hölder's inequality for `∫ q₃(π∇u_R) = ∫ χ_R⁴ q₃(∇u) + O(R^{−1/4}(log R)^{3/4})` | since `q₃(∇u) < 0` everywhere, `∫ χ_R⁴ q₃(∇u) ≤ ∫_{B₁} q₃(∇u) < 0`, and the cross terms are bounded pointwise by Young's inequality `a³b ≤ η a⁴ + η⁻³ b⁴`, `η = R^{−1/4}`; saves `q₃(∇u) ∈ L¹` and Hölder | in Lean, in this repository's history (before `ddae9d2`) |
| Proposition 4.2's zig-zag step (and Remark 4.5's) | mollify `r` and `b`, prove (17), (18) and `(√r_η)'' ≤ 5⁴ (√b_η)''`, and let `η → 0` | at each `t₀`, replace `r` by the smooth majorant `κ(t₀) + m(t − t₀) + 2·5⁶ b` (`κ = r − 2·5⁶ b` is concave, `m` a supergradient at `t₀`), which satisfies (17) and touches `r` at `t₀`; `b` is already smooth and satisfies (18), and `x` is perturbed where `b` vanishes; the paper's computation makes the tangent at `t₀` a supporting line. Saves the convolution calculus and Minkowski's integral inequality | in Lean, in this repository's history (before `81d2b4f`) |
| Proposition 5.2, smoothness of `ζ` | `ζ` is the unique root of `w̄ ζ² + 2(t + i)ζ + w = 0` in the disc, a simple one, hence smooth by the implicit function theorem | the closed form `ζ = i w / (1 − i t + s)`, `s` the principal square root of `(1 − i t)² + \|w\|²`, which lies off the negative axis, with `Re(1 − i t + s) > 0`; smoothness by composition | in Lean, in this repository's history (before `a81ec2a`) |
| Corollary 1.6, the witness | a smooth periodic `φ` with `∫ F(∇φ) < 0` (E35) | the Lipschitz periodic `φ` that Lemma 2.2 gives: the expansion in `ε` needs only bounded `∇φ`; saves the density step | in Lean, in this repository's history (before `40df282`) |
| Lemma 5.1 (2) | `n`-step rank-one Rademacher martingales, Burkholder's inequality, Proposition 2.5, the estimates (27)–(29) | for `f` that is `C²` away from `0`, the second derivative along rank-one lines: with `D²f[R_L, R_L] ≥ 0` and `\|D²f(X)\| ≤ C\|X\|^{p−2}`, polarization gives `D²f(πA)[πR, πR] ≥ −C' \|πA\|^{p−2} \|π^⊥R\| (\|πR\| + \|π^⊥R\|)`, and the inequality of arithmetic and geometric means against `D²(‖·‖_Λ^p)(A)[R, R] ≥ p ‖A‖_Λ^{p−2} ‖R‖_Λ²`, `‖A‖_Λ² = \|πA\|² + Λ²\|π^⊥A\|²`, gives `Λ ≳ 1/δ`; saves the martingales and Burkholder's inequality | on paper only |

Cited results. The packages hold more sketches and smaller items: `docs/SHORTER_PROOFS.md` of BP and of
HA, and the section "Shorter proofs" of CV's README. Sizes are in lines of Lean, the simpler
argument against the source's.

| Cited result | The source's argument | The simpler one | Size | Checked |
| --- | --- | --- | --- | --- |
| Theorem 2.3 (1) (Osękowski, Theorem 3.5 (ii)) | `U_p` is an integral of simple functions; Fubini's theorem | Burkholder 1988, Theorem 1.1: (1.12) along lines on which neither coordinate vanishes, the shift of the martingales by a vector orthogonal to `H`, dominated convergence, `E U_p ≤ U_p(0, 0) = 0` | 527, beyond the lemmas kept for (13) and (14), against 1,120 | in Lean, in the history of BP (commit `250cd49`) |
| Theorem 2.3 (1) | the same | (14) and the one-sided derivatives of `U_p` in the norms give a tangent majorant of `U_p` at every point, so that Burkholder's method (Osękowski, Theorem 2.7) applies to `U_p` itself: no shift, no integral formula | 60–100 (estimate) | on paper |
| (14) (Burkholder 1988, Remark 1.2) | completed here from (1.14) and the shift of the proof of (1.8) | the two simple functions of Osękowski's integral formulas have affine majorants that touch them at every point of a line `t ↦ (x + th, y + tk)`, `‖k‖ ≤ ‖h‖`, hence are concave along it, and so is the integral; `p = 2` is an identity | 90 against 307 | in Lean, at BP `25b96a3` |
| the sharpness of `p* − 1` for `p > 2` | duality (Osękowski, p. 59) | the second approach on `x ↦ U⁰(1 − x, x)`: the chord from `1 − 1/(β + 1)` to `1` gives `p w(1) ≤ (β + 1) w(1)`, and `w(1) ≥ 1`; the "reasoning similar to that in the case `1 < p < 2`" that the book mentions | 41 against 137, given the lemmas of the case `1 < p ≤ 2` | in Lean, at BP `25b96a3` |
| the sharpness for `1 < p ≤ 2`, the end | one-sided derivatives of `w` at `1` | both slopes at `1` are at most the slope of the chord from `1/(β + 1)` to `1`, and `x ↓ 1`; `w(1) < 0` from the initial condition 3° | about 85 against 96 | in Lean, at BP `25b96a3` |
| the sharpness for dyadic martingales | on `U⁰`, then Theorem 3.34 | the second approach run on the dyadic `W⁰` | – | the proof used, in BP |
| Proposition 2.7 (1) (HNVW I, Lemmas 3.5.13, 3.5.14) | the localized weak-type bound, summed over `{ρ = k}` | one application of the weak-type bound, to `h`, the martingale between the times `ρ` and `ν ∧ σ`: `h* ≤ 3δλ 1_{ρ<∞}` gives `η = (K/α)^q` at once | about 100 less | on paper; a variant with a strong bound and `4δλ` in Lean, in the history of BP (commit `250cd49`) |
| Proposition 2.7 (1) (HNVW I, Lemma 3.5.3, the adjoint) | cross terms | `T = E_0 + Σ_k M_{σ_k} D_k`, with `D_k` self-adjoint and commuting with `M_{σ_k}`: termwise | about 40 less | on paper |
| Proposition 2.7 (4) (HNVW I, Theorem 4.2.5) | approximation by Paley–Walsh martingales, after Maurey (pp. 284–285) | the book's alternative proof (p. 334) | 2,345 against 3,222, for Theorems 4.2.5 and 4.5.6 together: the first over `ℝ` and `ℂ`, with the final clause of 4.5.6, the second (Maurey's route as in Pisier's lecture notes) over `ℝ` and one bound over `ℂ` | the proof used, in BP; Maurey's route in its history (commit `250cd49`) |
| Proposition 2.7 (5) (HNVW I, Proposition 4.2.10 with Theorem 4.2.25) | convex hulls for deterministic multipliers, then incremental filtrations | Proposition 3.2.14 for the vector of the *values* `z_i` of the predictable multipliers: `z_i = Σ_ε c(ε) ε_i` with `Σ \|c(ε)\| ≤ π/2`, so `φ • Y = Σ_ε c(ε) (σ^ε • Y)` with the predictable signs `σ^ε_k(ω) = ε_i` where `φ_k(ω) = z_i`; no Lemma 3.6.18 and no Theorem 4.2.25 | 88 against 911 | in Lean, at BP `67f48bf` |
| Proposition 2.7 (5) | the same | averaging: for `\|λ\| = 1`, `λ = e^{iθ}`, `(1/2π) ∫ sgn cos(θ − φ) e^{iφ} dφ = (2/π) λ`, with the predictable signs `sgn cos(θ_k − φ)` for each `φ`, and Riemann sums; longer than the previous one | 517 against 1,242 | in Lean, in the history of BP (commit `250cd49`) |
| HNVW I, Theorem 4.2.25, for signs | Lemma 3.6.18 (incremental filtrations) | Theorem 4.5.6, (2)⇒(3)⇒(1), from the cube: it ends with predictable signs | 12 | in Lean, at BP `67f48bf` |
| HNVW I, Theorem 4.2.25 | the same | for multipliers in the unit ball, from the same theorem (about 60 lines); or on any probability space, revealing `ℱ_{k+1}` on one level set `{φ_{k+1} = z_i}` at a time (150–200) | estimates, against about 500 | on paper |
| Proposition 2.7 (6) (HNVW I, Theorem 4.5.6) | homogenization (4.31); padding and even/odd interleaving of two pairs (Step 2) | `E F(f_n, g_n) ≤ u(0, 0)` for `tf`, `tg` and `t → ∞`; the two pairs on consecutive blocks of signs; `ũ(0,0) = 0` from `ũ(0,0) = 2^p ũ(0,0)` | about 10 against 101; about 125 against 185 | on paper |
| Proposition 6.4 (HNVW II, Lemma 6.2.3) | the two-point inequality for all real functions: the case `\|y\| > 1`, duality | after the reduction by positivity, only nonnegative functions are needed | 123 less | in Lean, in BP (kept for Borell's proof) |
| Proposition 6.4 (HNVW II, Theorem 6.2.4) | tensorization in `L^q(D^{N−1}; X)` | Borell 1979, (2.1), at `c = 0` | about 10, given Borell's proof | in Lean, at BP `67f48bf` |
| Proposition 6.3, the upper bound | Lust-Piquard–Pisier 1991 and Astérisque 247 (Section 7) | exchangeable pairs: Mackey–Jordan–Chen–Farrell–Tropp 2014 (arXiv:1201.6002), §7 (Corollary 7.3) for Hermitian matrices and §8 (the Hermitian dilation), with the explicit constant `√(2(q − 1))` (`√(q − 1)` for `q = 2` and `q ≥ 3`). Their Remark 7.2, for `2 < q < 3`, uses a variant of the mean value trace inequality that they do not prove and BP proves | about 560, and 409 of trace inequalities (`Holder` and `Dilation`, shared, not counted), against 19,198 in the 32 modules of HA that the proof imports (HA `90f1e01`; commit `11e9e12` removed from them six files, 3,424 lines on dyadic shifts and Littlewood–Paley theory, that the proof did not use) and about 3,900 in BP | in Lean, in BP (`ncKhintchine_upper`); it was used here before commit `af922cc` |
| Proposition 6.3: the factorization of `H¹` functions (Sarason 1967, Theorem 4) | outer functions, Szegő's theorem and range functions of matrix-valued functions (Helson–Lowdenslager) | Bekjan–Xu (arXiv:0705.1947), Theorems 3.1 and 3.4, for `L^∞(𝕋; M_n)`; for analytic polynomials, and with `‖h‖²_{S_{2p}} ≤ ‖f‖_{S_p} + δ` in place of the equality, which is enough for Paley's inequality | 762 against about 5,600 | in Lean, in the history of HA (commit `3ecee00`) |
| the same: Helson–Lowdenslager 1958, Theorems 8 and 9 | their Lemmas 4 and 5, and (68) | Jensen's inequality for the determinants of the Fejér means, then the limit | – | on paper |
| the same: Helson–Lowdenslager 1961, Theorem 12; Sarason 1967, Theorem 4 | the functions `B`, `D̃` and `V = BD̃⁻¹`; the partial isometry of the polar decomposition | the innovation of `A ∈ H²` is already an analytic isometry with the range of `A`; `A₁ = A A₂ᴴ (A₂A₂ᴴ)⁻¹` | 12 for the first | checked by Lean, not kept in HA |
| Proposition 6.3: (III.3) of Lust-Piquard–Pisier, on average over the signs, which is all that (III.2) uses | McConnell 1984, Theorems 1.1 and 1.3, and transference, with Burkholder 1983 for the Hilbert transform | the Littlewood–Paley inequality with random signs (HNVW I, Theorem 5.7.10 (2)) and the randomised boundedness of single frequencies, since the blocks `[2^{k−1}, 2^k]` and `(2^{k−1}, 2^k]` differ from the dyadic ones by one and two frequencies | about 280, given that theorem, against about 4,740 and, for the Hilbert transform, about 3,490 | in Lean, in the history of HA (commit `ec00cb2`); it was used here before commit `fd2c773` |
| the same route: Littlewood–Paley on the circle (HNVW I, Theorem 5.7.10 (2)) | transference by duality (Proposition 5.7.1) | a cut-off with compactly supported Fourier transform, on which the multiplier acts exactly (the book's argument in Proposition 5.2.5); it applies to the sign multipliers of McConnell's Theorem 1.3 too | – | in Lean, in the history of HA (commit `d0d081b`), for the random signs; on paper for McConnell's |
| Proposition 6.3: McConnell 1984, Theorem 1.3 | (2.1), twice, for Rademacher sums; Theorem 1.1, twice, at the end | Kahane's contraction principle, which holds in every Banach space: `C β⁶ħ²` in place of `C β⁸ħ²`, `β` the UMD constant and `ħ` the bound of the Hilbert transform (now `2β² + 1`); `T_M T_{m₁}` is itself a multiplier of Theorem 1.1: one use | – | in Lean: the first in the history of HA (commit `beab475`), the second checked, not kept |
| Proposition 6.3: the Hilbert transform on UMD spaces (Burkholder 1983, Lemmas 2–4) | a random walk in the disc, then Poisson integrals and truncations on the circle; the line by M. Riesz's argument (1928, §18), to which Lemma 4 refers | the dyadic shifts of HNVW I, §5.1 (Theorem 5.1.13), with the constant `4β² + 11` in place of `2β² + 1`; for the multiplier `sgn` both need HNVW I, Lemma 5.2.1 and Proposition 5.2.2 | 1,836 (HA `ec00cb2`) against 3,800 (HA `90f1e01`; 3,489 at `c8182f9`) | in Lean, in HA (kept for HNVW's Littlewood–Paley inequalities); it was used here before commit `ee3b66b` |
| the same: Burkholder 1983, Lemmas 3 and 4, for the multiplier `sgn` | truncated conjugate functions and Hilbert transforms, then HNVW I, §5.2 | no truncations: Lemma 2, in the limit, on the circle of length `2πR`, for `f` minus its mean and `r = 1 − y/R`; as `R → ∞`, `‖v(·, y)‖_p ≤ β² ‖f‖_p` for the conjugate Poisson integral `v` on the line, whose symbol is `−i sgn(ξ) e^{−2π\|ξ\|y}`; `y → 0` and Fatou's lemma give the constant `β²` in place of `2β² + 1` | – | on paper |
| Proposition 6.3: the Hilbert transform in McConnell 1984, Theorem 1.3 | Burkholder 1983 | McConnell's Theorem 1.1, proved in HA for `m` of class `C²` off `0`, applies to `m = sgn`, with `Cβ²`, `C` absolute and large (his Remark 3.1 indicates a direct proof by his method); neither Burkholder 1983 nor HNVW I, §5.2, is needed | about 20, given Theorem 1.1 | checked by Lean, not kept in HA |
| Proposition 6.3: (III.3) of Lust-Piquard–Pisier | McConnell 1984, Theorems 1.1 and 1.3, and transference | independent unimodular variables `z_1, …, z_n` on `𝕋ⁿ` in place of `e^{i2^k t}`, with a lexicographic order on `ℤⁿ`: (III.3) becomes the UMD inequality of `C_{2p}` | – | on paper (the identity behind it also numerically) |
| Proposition 6.3: type 2 of `S_q` (Tomczak-Jaegermann, Theorem 3.1 (ii)) | the trace expanded for even `q`, the general Horn inequality, three lines | the bound by exchangeable pairs for the Hermitian dilations, and `‖Σ D_k²‖_{S_{q/2}} ≤ Σ ‖D_k‖²_{S_q}` (Astérisque 247 goes the other way, from type 2 to Khintchine); for even `q`, iterated Hölder inequalities | about 40 against 1,095; about 190 against 399 for even `q` | on paper; for even `q` in Lean, in the history of BP (commit `8962532`) |
| Proposition 6.3: type 2 implies K-convexity (HNVW II, Proposition 7.4.22) | Walsh functions, the contraction principle for Gaussian sums, rotation | the reflection `R = 2P − 1` preserves the Gaussian measure, so `T(Pg) = ½ (T(g) + T(Rg))` is dominated by `T(g)` in `L²` | 466 against 672 | in Lean, in the history of BP (commit `8962532`) |
| transference (HNVW I, Corollary 5.7.6, I ≤ II) | a pairing with a second function, Hölder's inequality, duality and density | Igari 1969 (Tôhoku Math. J. 21, Theorem 2; there for `f ∈ C_c^∞(ℝ)` and the norm on `L^p(𝕋)`, here for Schwartz `f` on `ℝ²` and mean-zero functions): the torus bound extends to absolutely summable series, the series with coefficients `R⁻² m(n) f̂(n/R)`, `n ≠ 0`, at `x/R` are, up to the term `n = 0`, Riemann sums of `T_m f(x)`, and Fatou's lemma concludes | about 225 against 1,000 | in Lean, in the history of HA (commit `bf215c5`) |
| HNVW I, Proposition 5.7.4 | `g` with `ĝ` supported off `0` | any Schwartz `g`: no density step for `g` | – | on paper |
| HNVW I, Proposition 2.4.23 (ii) | `L^p` limits by translations and `‖φ_R‖_p` | `‖h‖_p ≤ ‖h‖_1^{1/p} ‖h‖_∞^{1−1/p}` | about 40 against 200 | on paper |
| Lemma 2.1 (Rindler) | the singular value decomposition | a rank-one convex function is convex in each entry, and a separately convex function is locally Lipschitz; no explicit constant | one line, given the latter | in Lean, at CV `e474abf` |
| Lemma 2.1, the bound (5.9) | the same | the rows (or the columns) of `B − A` are Frobenius-orthogonal of rank at most one | about 150 less | on paper (the orthogonality in Lean, at CV `e474abf`) |
| Lemma 2.2, quasiconvex ⇒ rank-one convex, on the cube | laminates with cut-offs (Rindler) | the periodic sawtooth is a periodic test map | 4 | in Lean, at CV `e474abf` |
| Proposition 2.2 (Kinderlehrer–Pedregal, Proposition 8.1) | (ii) in every rank-one direction, on rotated cubes | (ii) along the `e_i ⊗ e_j`, then the local Lipschitz bound for separately convex functions | about 100 less | in Lean, at CV `e474abf` |
| Dacorogna, Theorem 5.20 (Proposition 5.1) | induction on the rows, with Lemma 5.24 | `f` is multi-affine in the rows; its part multilinear in the rows `I` vanishes when two of them are equal (the `t²` coefficient along `(e_i + e_j) ⊗ b`), so it is an alternating form, a combination of minors with the rows `I`. The same argument shortens Lemma 5.24 | – | on paper |

### The formalization

- Nothing is assumed. What is not proved: the two theorems quoted only as context (Theorem 1.1,
  Proposition 2.6), Conjecture 1, and the claims of Section 9.
- The packages state their planned extensions: Dragičević's bound for every power `𝓑^n`, the reverse
  direction of transference, general dimension, and more of the sources of Proposition 6.3 (general
  `H¹–ℓ²` multipliers, infinite dimension, complex and rectangular matrices, the left-hand
  Littlewood–Paley inequalities with random signs, Burkholder's singular integrals (1983, Theorem 2),
  McConnell's theorems in higher dimension; `lean4-harmonic-analysis`);
  Randrianantoanina's Theorem 3.1 for general semifinite von Neumann algebras and non-scalar multipliers,
  the non-commutative Khintchine inequality for rectangular and complex matrices, and Kahane–Khintchine on
  a probability space (`lean4-banach-probability`);
  Dacorogna's formula for Borel, locally bounded integrands with a quasiconvex minorant
  (`lean4-calculus-of-variations`).
- [`Morrey/Common/Basic/`](../../Morrey/Common/Basic) holds two Mathlib candidates: `Basic.LinearAlgebra.Matrix.RankTwo` (for
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`) and `Basic.Analysis.Calculus.BumpFunction.Mollify`
  (for `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`). The latter overlaps with the
  mollification of Lipschitz maps in `lean4-calculus-of-variations` (`Lipschitz/Mollify.lean`);
  the two should be merged before either is contributed. The packages themselves hold general
  theory that Mathlib lacks: `L^p` bounds of Fourier multipliers and transference, Fourier series of
  smooth periodic functions, the Hilbert transform, Mihlin multipliers and Littlewood–Paley inequalities in
  UMD spaces, matrix-valued Hardy functions and their factorization, martingale inequalities in Banach
  spaces, UMD spaces, type 2 and K-convexity, Schatten classes, quasiconvexity, and convexity through second
  distributional derivatives on `ℝ`.
- [`Morrey/Common/External/`](../../Morrey/Common/External) states each cited result in its source's terms, under its source's
  name (Osękowski, Burkholder, HNVW, Pisier, Randrianantoanina, Cox–Veraar, Yaroslavtsev, Pisier–Xu,
  Dragičević, Rindler, Dacorogna, Kinderlehrer–Pedregal, Kristensen), for reuse by other
  formalizations that cite the same sources.
