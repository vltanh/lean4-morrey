# Cassese (2026) in Lean: audit report

G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*,
[arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3) (16 September 2026), a preprint.
Formalized in Lean 4 with Mathlib (`v4.36.0-rc2`) from the TeX source of v3, on 21 November 2026,
in a repository that also formalizes Šverák (1992) and Pedregal's claimed `2 × 2` proof
([overview](../../README.md)). Labels in backticks are the paper's TeX labels; labels `cs-…` are
ours, for results the paper does not label ([`paper_routes.tsv`](paper_routes.tsv)). The printed
numbers of the main theorems are 1.2–1.5, because Theorem 1.1 is the cited theorem of Kirchheim and
Kristensen. This formalization was written independently of the author's own Lean code, which was
not consulted.

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

The paper claims rank-one convex integrands that are not quasiconvex on `ℝ^{2×m}` for `m ≥ 3`. With
Šverák's theorem, this leaves `2 × 2` as the only size where Morrey's problem can have a positive
answer. It also answers Kirchheim and Kristensen's homogeneous problem negatively in many sizes:
there are `p`-homogeneous, rank-one convex, nowhere quasiconvex integrands.

**Every result of the paper is formalized and proved, some of them conditionally.** No statement of
the paper is false. The paper's proofs rest on deep results of martingale theory and Banach-space
geometry. Those that Lean can reach were built here: Burkholder's inequality and the sharpness of
its constant, Burkholder's functions, Dacorogna's formula for the quasiconvex envelope, and the
textbook facts of the calculus of variations. Those out of reach are named hypotheses of the
theorems whose proofs use them (Section 2): UMD theory for Schatten classes and `L^p`,
non-commutative Khintchine inequalities, transference, and Dragičević's lower bound for the
Beurling–Ahlfors transform.

| Paper | Lean | Statement | Assumes |
| --- | --- | --- | --- |
| Theorem 1.2 | [`theorem1_2`](../../Morrey/Cassese/Introduction.lean#L2029) ⭐ | every `p > 1`: a `p`-homogeneous, rank-one convex, nowhere quasiconvex integrand on `ℝ^{2×m}` for `m ≥ m₀(p)` | nothing (by the paper's Remark 4.5) |
| Theorem 1.2 | [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L1990) | the same, by the paper's main proof | Pisier, Yaroslavtsev, HNVW extrapolation |
| Theorem 1.3 | [`theorem1_3_a`](../../Morrey/Cassese/Introduction.lean#L2043) ⭐, [`theorem1_3_b`](../../Morrey/Cassese/Introduction.lean#L2068) ⭐ | a quartic polynomial on `ℝ^{2×3}`, rank-one convex and nowhere quasiconvex; and for `p` near `4` | nothing |
| Corollary 5.3 | [`corollary5_3`](../../Morrey/Cassese/TwoByThree/Transpose.lean#L197) ⭐ | its transpose, on `ℝ^{3×2}` | nothing |
| lines 251–254 | [`morrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2260) ⭐ | with Šverák's theorem: Morrey's problem fails in every `d × m` with `d, m ≥ 2` except `2 × 2` | nothing |
| lines 254–256 | [`homMorrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2288) ⭐ | at `p = 4` the homogeneous problem fails in every such size except `2 × 2` | nothing |
| Theorem 1.4 | [`theorem1_4_four`](../../Morrey/Cassese/Square.lean#L3610) ⭐ | at `p = 4`: a conjugation- and transposition-invariant example on `ℝ^{d×d}` for every `d ≥ 588` | nothing |
| Theorem 1.4 | [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2100) ⭐ | every `p > 1`: such an example for `d ≥ d₀(p)` | HNVW extrapolation, Randrianantoanina, Cox–Veraar, Pisier–Xu, Kahane–Khintchine |
| Theorem 1.5 | [`theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2186) ⭐ | every `p ≠ 2`: an example on `ℝ^{4×2}` | transference, Dragičević |
| Corollary 1.6 | [`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2234) ⭐ | a nonnegative 1-homogeneous rank-one convex integrand on `ℝ^{4×4}`, not quasiconvex at a matrix of rank two | transference, Dragičević |

⭐ in [`Challenge.lean`](../../palomar/Cassese/Challenge.lean), checked by Comparator against
[`Solution.lean`](../../palomar/Cassese/Solution.lean), with a check of the definitions
([`projL3_mem`](../../Morrey/Cassese/TwoByThree/Basic.lean#L57): the explicit projection maps into `L₃`). The results that use the assumed hypotheses
are Theorem 1.4 for general `p` with Propositions 6.2, 6.5, eq (31), Remark 6.3 and Corollary 6.1;
Theorem 1.5 and Corollary 1.6 with Theorem 7.1, Corollary 7.2 and the lower bound of
Proposition 7.2; and the paper's UMD route to Theorem 1.2 ([`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L1990), with
[`umdEllq_lt_top`](../../Morrey/Cassese/TwoByM.lean#L687)).

The proofs follow the paper's arguments. One departure replaces a whole argument, with the user's
approval: Theorem 1.2 is proved unconditionally by the route the paper itself announces in
Remark 4.5 (Burkholder's scalar functions instead of UMD constants); the paper's main proof is
formalized too, as [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L1990), conditional on the UMD results. The other departures are local
and listed in Section 7.

The audit found no false statement, and many steps that the paper leaves to the reader or argues
too briefly (Section 3). Some matter: the uniformity in `p` that Theorem 1.3 (b) needs (E4), a
reading of the prelaminates under which a step of Proposition 2.5 is false (E10), the constant `κ`
of Section 5 asserted without proof (E5; it holds, and `√2` suffices), Proposition 6.6 and
Corollary 5.2, which have no proof (E6, E19), and four proofs that the paper only sketches (E17,
E31–E33).

## 2. Results from prior work and how the paper uses them

### Proved in `Morrey/Common/External/` and in the library

| Result | Where the paper uses it | Source cited by the paper | Lean |
| --- | --- | --- | --- |
| Burkholder's inequality, Hilbert-valued (Theorem 2.3 (1)) | Lemma 5.1, Theorem 1.3 (b), Prop 7.1 | Osękowski 2012, Thm 3.5 (Burkholder 1984) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050) |
| Burkholder's square function inequality (Theorem 2.3 (2)) | Prop 6.5 | Osękowski 2012, Thm 8.6 | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224) |
| Burkholder's functions `u₆` and `u_q`, (13), (14) | Prop 4.2, Theorem 1.2 by Remark 4.5 | Burkholder 1988 | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L249), `scalarFunctionQ_holds` |
| the sharpness of `p* − 1` for dyadic `±1`-transforms | Cor 6.3, lower bound | "see also [Cassese 2025]" (Burkholder 1984) | [`burkholderSharpness_holds`](../../Morrey/Cassese/Square/Sharpness.lean#L878) |
| the bound `C^{rc} ≤ (p* − 1) sup ‖Q‖/‖P_ρ‖` | Prop 7.1 | "the results of [Cassese 2025]" | from Burkholder's inequality ([`proposition7_1`](../../Morrey/Cassese/FourByTwo.lean#L324)) |
| a rank-one convex function is locally Lipschitz (Lemma 2.1) | the envelopes, Cor 1.6 | Rindler 2018, Lemma 5.6 | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| quasiconvexity: rank-one convexity, domains, periodic test maps (Lemma 2.2) | Prop 2.3, the thresholds, the lifting | Rindler, Props 5.1, 5.3; Dacorogna 2008, Props 5.11, 5.13 | `External.Rindler.*` |
| the rank-one convex envelope by prelaminates (Prop 2.1) | Prop 2.3, Prop 5.1 | Pedregal 1993, §4; Dacorogna 2008, Thm 6.10 | [`proposition2_1`](../../Morrey/Cassese/Toolkit.lean#L779), through Prop 2.4 (the route of Remark 2.1) |
| Dacorogna's formula for the quasiconvex envelope (Prop 2.2) | line 559, Prop 2.3, Prop 4.3 | Kinderlehrer–Pedregal 1991, Prop 8.1 | [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) (proved following Dacorogna 2008, Thm 6.9) |
| rank-one affine functions are affine in the minors | Prop 5.1 | Dacorogna 2008, Thm 5.20 | [`External.Dacorogna.rankOneAffineMinors_holds`](../../Morrey/Common/External/Dacorogna/Minors.lean#L67) |
| rank-one convex quadratic forms are quasiconvex | Prop 5.1 | Dacorogna 2008, Thm 5.25 (i) | [`External.Dacorogna.quadraticForm_quasiconvex`](../../Morrey/Common/External/Dacorogna/Minors.lean#L95) |
| a smoothing that keeps the failure of quasiconvexity | Cor 5.2 | Kristensen 1999, Prop. 2; Heinz 2008 | [`External.Kristensen.smoothing_holds`](../../Morrey/Common/External/Kristensen/Smoothing.lean#L106) |

### Standard facts used without citation

All are proved: the Schatten-norm facts of Section 1.5 (with the triangle inequality and Weyl's
monotonicity); the Bernstein–Doetsch theorem (a midpoint convex function, locally bounded above, is
convex; TeX 643–646); the uniform convexity of `|·|^p` (used in (29)); the strong law of large
numbers with infinite mean, Fatou and Jensen (Lemma 4.2); Fourier series of Lipschitz periodic maps
and Fejér means on the torus (Prop 7.2,
[`Morrey/Common/Basic/Analysis/Fourier/TorusLipschitz.lean`](../../Morrey/Common/Basic/Analysis/Fourier/TorusLipschitz.lean)); the change of variables
`(ζ, τ) ↦ (w, t)` of Prop 5.2. The formalization also uses "separately convex functions are locally
Lipschitz" (Dacorogna 2008, Thm 2.31; `Matrix.locallyLipschitz_of_convexOn_single`) in its proofs of
Lemma 2.1 and Prop 2.2; the paper does not.

### Assumed: named hypotheses

Each is a hypothesis of exactly the statements whose proofs use it, under its source's name. Most
are defined in [`Morrey/Cassese/Defs.lean`](../../Morrey/Cassese/Defs.lean); [`DragicevicL4Bound`](../../Morrey/Cassese/Hypotheses.lean#L124) is
in `Hypotheses.lean`, and [`HNVWDyadicUMD`](../../Morrey/Cassese/Toolkit.lean#L1980), [`HNVWZigZag`](../../Morrey/Cassese/Toolkit.lean#L2003) in `Toolkit.lean`.

| Hypothesis | Source | Used by (numbered results) | What Lean lacks |
| --- | --- | --- | --- |
| [`HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L331) | Hytönen–van Neerven–Veraar–Weis I, Thm 4.2.7 | [`umdEllq_lt_top`](../../Morrey/Cassese/TwoByM.lean#L687), [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L1990), Prop 6.5, Cor 6.1, [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2100) | UMD theory |
| [`PisierLpUMD`](../../Morrey/Cassese/Defs.lean#L458) | Pisier 2016, Cor 5.22 | [`umdEllq_lt_top`](../../Morrey/Cassese/TwoByM.lean#L687), [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L1990) | UMD of `L^p` |
| [`YaroslavtsevComplexUMD`](../../Morrey/Cassese/Defs.lean#L466) | Yaroslavtsev 2018, Lemma 3.2 | [`umdEllq_lt_top`](../../Morrey/Cassese/TwoByM.lean#L687), [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L1990) | complex UMD constants |
| [`RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L344) | Randrianantoanina 2002, Cor 4.5 | Props 6.2, 6.5, Remark 6.3, Cor 6.1, [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2100) | UMD of Schatten classes |
| [`CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L355) | Cox–Veraar 2007 | Props 6.2, 6.5, Remark 6.3, Cor 6.1, [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2100) | decoupling |
| [`PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374) | Pisier–Xu 2003, Thm 6.1 | eq (31), Props 6.2, 6.5, Remark 6.3, Cor 6.1, [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2100) | non-commutative Khintchine |
| [`KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L397) | HNVW II, Thm 6.2.4 (the paper's Prop 6.4) | eq (31), Props 6.2, 6.5 ([`proposition6_5_finite`](../../Morrey/Cassese/Square.lean#L1726)), Cor 6.1, [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2100) | Khintchine inequalities |
| [`KahaneKhintchineHypercontractive`](../../Morrey/Cassese/Defs.lean#L417) | the hypercontractive bound `κ_{q,p} ≤ √((q − 1)/(p − 1))`, standard (not consulted; no source in the paper, E27) | Remark 6.3, Prop 6.5 ([`proposition6_5_infty`](../../Morrey/Cassese/Square.lean#L1774)) | hypercontractivity |
| [`HNVWTransference`](../../Morrey/Cassese/Hypotheses.lean#L110) | HNVW I, Cor 5.7.6 | Prop 7.2 (lower bound), Thm 7.1, Cor 7.2, [`theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2186), [`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2234) | transference of multipliers |
| [`DragicevicLowerBound`](../../Morrey/Cassese/Hypotheses.lean#L117), [`DragicevicL4Bound`](../../Morrey/Cassese/Hypotheses.lean#L124) | Dragičević 2011, Thm 1.1 | Thm 7.1, [`theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2186), [`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2234); Cor 7.2 | `L^p` bounds of the Beurling–Ahlfors transform |

Both Kahane–Khintchine hypotheses are stated for any seminorm on a real vector space, more
generally than the Banach-space source; the docstrings justify it (pass to the normed quotient;
the sums are finite). Two named hypotheses of the toolkit, [`HNVWDyadicUMD`](../../Morrey/Cassese/Toolkit.lean#L1980) and [`HNVWZigZag`](../../Morrey/Cassese/Toolkit.lean#L2003)
(Prop 2.7 (4), (6)), are stated and assumed by no theorem. Kirchheim and Kristensen's theorem
(Theorem 1.1) and Osękowski's characterization of Hilbert spaces (Prop 2.6) are stated for context;
no proof uses them.

### Does the paper use each cited result correctly?

Yes, with two reservations. Remark 6.3 and Proposition 6.5 at `q = ∞` need Kahane–Khintchine
constants that grow polynomially in `q`, which the paper's Proposition 6.4 as stated does not give
(E27). The lower bound of Corollary 6.3 uses the sharpness of `p* − 1` for dyadic `±1`-transforms
with only "see also [Cassese 2025]" as a source (E30).

## 3. Errors and gaps in the paper

No statement is false. The items below are gaps (steps that need an argument the paper does not
give, or that it only sketches), one false intermediate claim under a natural reading (E10), and
misprints. The formalization supplies each gap; the last column says how. E1 is kept so that the
numbers match those cited in the code.

| | Lines | Issue | In the formalization |
| --- | --- | --- | --- |
| E1 | — | not a finding (the numbering, see the preamble) | — |
| E2 | 375–377, 2350–2378 | Schatten fact (1) is stated for `q ≥ 2`, but Proposition 6.2 uses it at exponent `q/2 > 1`, below `2` when `q < 4` | proved for `q ≥ 1` |
| E3 | 1914–1929 | Lemma 5.1 (2), eq (28): the first-order cancellation `E[Df(X)·𝓔_n] = 0` is not mentioned; it also needs a Lipschitz bound on `Df` across the origin | supplied |
| E4 | 2031–2046 | Theorem 1.3 (b): "continuity of the estimates" in `p` needs the constant `Λ` of Lemma 5.1 (1) uniform for `p` near `4`, and the cut-off fixed before `p` varies | a uniform quantitative Lemma 5.1 (1) ([`lemma5_1_part1_quant`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L324)) |
| E5 | 1978–1979 | "`L₃` satisfies the hypothesis of Lemma 5.1 with `κ = 2`" has no proof | proved; the natural correction gives exactly `√2`, and `κ = 2` covers the rank-exactly-one requirement |
| E6 | 2558–2563 | Proposition 6.6 has no proof | proved, from exact trigonometric moments |
| E7 | 2683–2684 | Corollary 6.4: the bound on `⟨W, Z⟩` does not follow "by the assumption on `(E, D)`"; it is a trace argument, and also uses `‖W‖ ≤ 2a`, `ρ ≤ 2e` | supplied |
| E8 | 562–578 | Proposition 2.3 has no proof; the direction "`f` quasiconvex at `0` ⇒ `f^{rc}` quasiconvex at `0`" of (c) needs Dacorogna's formula (line 559) | proved: (a), (b) from the dual formulas, (c) through line 559 |
| E9 | 1406–1411 | Proposition 5.1: "`Q` is rank-one affine" and "`P − Q` is rank-one convex" skip arguments | supplied (a prelaminate centred at `0` with an atom at `A`) |
| E10 | 504–530, 661–663 | prelaminates: Proposition 2.4's gluing needs repeated atoms, and with repeated atoms "every dyadic prelaminate is the law of a rank-one Rademacher martingale" (661–663) is false (split a third of `δ₀`: weight `1/6`); under the whole-atom reading the gluing fails instead | Proposition 2.5 "⇐" by Proposition 2.4's argument on the martingales (Section 7) |
| E11 | 1130 | Remark 4.2 bounds `C^{rc}` by `UMD_p` where the argument gives `UMD_{ℂ,p}`; under `≲` this is harmless (Prop 2.7 (5)) | not an error |
| E12 | 245, 1376 | the TeX labels `thm:2x4`, `sec:2x4` (invisible in the PDF) are leftovers of v2; the content is `2 × 3` | cosmetic |
| E13 | 68, 242–243 | the abstract and the introduction call the quartic "explicit", but it depends on unspecified `K` and `δ` | wording |
| E14 | 1355–1366 | Proposition 4.3 gives no value of `n₀` | not an error: the proofs are existence proofs |
| E15 | 1595–1596, 1722–1723 | the wave equation the proof mentions is never stated | cosmetic |
| E16 | 1821–1832 | Lemma 5.1 asks for a rank-one `R_L`; `R_L = 0` must be allowed | allowed |
| E17 | 2090–2102, 2121–2123 | Corollary 5.3 is only sketched, and its constants are only said to exist | completed, with `c = 75/8`, `C = 4·10⁶` |
| E18 | 2956–2966 | the `p > 2` variant of Corollary 1.6 is asserted without proof | not formalized |
| E19 | 2051–2065 | Corollary 5.2 has no proof, only references | proved, through Kristensen's smoothing (proved) |
| E20 | 1602–1614, 1995 | the paper's proof of Theorem 1.3 integrates `q₃(∇u)` over `ℝ³`, which needs `L¹`; this is avoidable | the formal proof uses the integral over the unit ball (`L¹` is proved anyway) |
| E21 | 468–470, 616–659 | the minorant `G` of Propositions 2.3–2.5 is used as a competitor in `f^{rc}` (643–658), so it must be an integrand; the paper does not say why, and Lemma 2.1 as stated ("an integrand") does not apply before that is known | Lemma 2.1 in Rindler's form (any real-valued rank-one convex function) |
| E22 | 559 | the passage from the ball (Proposition 2.2) to the cube (Definition 2.1) is silent; it needs Lemma 2.2 (ii) | supplied |
| E23 | 1047–1053 | the "straightforward limiting argument" from Schwartz test maps to Definition 2.1 is not given | proved ([`twoByM_ratio_le_qcThreshold`](../../Morrey/Cassese/TwoByM.lean#L3004)) |
| E24 | 1891–1895 | Lemma 5.1 (1): "by homogeneity and Young's inequality" needs a Lipschitz bound on `g`, which is only continuous | uniform continuity on a compact set and homogeneity |
| E25 | 1855, 1956, 1991 | Lemma 5.1 (2) is stated for `δ ∈ (0, 1)` and used at `δ = 1` | covered |
| E26 | 1367–1375 | Remark 4.5 sketches the elementary route without `U` or `K` | supplied: `U = R^{p/q} − K B^{p/q}`, `K = 2(q − 1)^{p+1}/(p − 1)`, `q = p + 3` |
| E27 | 2425–2437, 2477–2479 | Remark 6.3 and Proposition 6.5 at `q = ∞` need Kahane–Khintchine constants polynomial in `q`; Proposition 6.4 as stated gives none and no source is named | the hypercontractive bound, assumed |
| E28 | 2807–2821, 2211–2216 | Proposition 7.2 "≤" argues with smooth maps, Lemma 2.2 tests with Lipschitz periodic maps; the density step is not stated | Fejér means |
| E29 | 2489–2520 | Corollary 6.1: the reduction from periodic to compactly supported Hessian test maps is not stated, and "the calculation of Proposition 6.1" does not carry over (the skew part of `JD²φ` has two distinct doubled singular values) | supplied (rank `≤ 4`, `S₂` against `S₄`) |
| E30 | 2624–2633 | Corollary 6.3's lower bound cites the sharpness of `p* − 1` only through "see also [Cassese 2025]" | proved here ([`burkholderSharpness_holds`](../../Morrey/Cassese/Square/Sharpness.lean#L878)) |
| E31 | 2658–2659, 2670 | Corollary 6.4 is "only sketched", and `8/5 U ≥ ‖Y‖⁴ − 98 ‖X‖⁴` is left to "standard calculations" | completed |
| E32 | 2891–2892 | Corollary 7.2: the zig-zag concavity of `U` and `2U ≥ ‖y‖⁴ − 130 ‖x‖⁴` are left to "standard calculations" | proved |
| E33 | 2184–2185 | Corollary 5.4 reuses estimates from inside the proof of Proposition 5.2, for another profile | rerun for that profile (route difference recorded) |
| E34 | 2552–2554, 2660–2668 | the invariances of Corollary 6.4's quartic, which Theorem 1.4 at `p = 4` needs, are not stated | proved |

The constants of Corollary 6.3 (`d₀ = 588` is the least that works) and Corollary 7.2 (`130`,
`1170`; margin 1.6 %) check out.

## 4. Missing hypotheses

None.

## 5. Redundant hypotheses

The proofs do not use: `A ∈ 𝓛` in the rank-one convexity of the quartic on `𝓛` (`cs-q-rc`; it holds
from any base point); `ρ > 0` in Proposition 7.2; `d ≥ 2` in Corollary 6.3's upper bound; the
homogeneity in Proposition 2.3 (a), and the homogeneity and `p > 1` in (b), (c); `1 < p` in the
monotonicity of the homogeneous problem; the separability of the Hilbert space in Burkholder's
inequalities (kept as `[SeparableSpace H]` in [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050) and
`squareFunction`). These are kept, as the paper states them. The section's standing assumption
`q > p + 2` is not assumed by Proposition 4.1, which does not need it; Lemma 4.1 has no `q`.

## 6. How the formalization reads the paper

- **Integrands and test maps.** Matrices `ℝ^{d×m}` are `Matrix (Fin d) (Fin m) ℝ`, the gradient of
  `φ` is `jac φ` (rows are components), an "integrand" (line 348) is lower semicontinuous and locally
  bounded ([`IsIntegrand`](../../palomar/Cassese/Challenge.lean#L149)). `W^{1,∞}_0([0, 1]^m)` maps are Lipschitz maps vanishing outside the open
  cube; their gradient is `fderiv`, defined almost everywhere by Rademacher's theorem. The formal
  Definition 2.1 also asks the integral to exist, which the paper does not; it is automatic for
  integrands, and it makes a failure of quasiconvexity a genuine integral.
- **Rank-one convexity** is Definition 2.2 on segments; bridges prove it equivalent to convexity
  along lines (Šverák's form) and to the textbook form of the cited results.
- **Prelaminates** (Definition 2.4) allow repeated atoms, the reading Proposition 2.4's gluing needs
  (E10).
- **Rademacher martingales** live on `Fin N → Bool` with the uniform measure; the thresholds
  `C^{rc}`, `C^{qc}` are infima in `ℝ≥0∞`.
- **Banach spaces** in the UMD hypotheses are complete normed spaces with an equivalent norm
  (`S_q` is `Fin d → Fin d → ℝ` with the Schatten norm). Schatten norms are defined from singular
  values; operator norms of powers of the Beurling–Ahlfors transform are suprema over Schwartz
  functions on `ℝ²` and mean-zero trigonometric polynomials on `𝕋²`.
- **Hessian quasiconvexity** (Corollaries 5.4, 6.1), undefined in the paper, is
  `∫_{(0,1)^n} F(A + D²φ) ≥ F(A)` for smooth compactly supported `φ`.
- **Quantifiers.** Theorem 1.3 (b): `∃ ε > 0, ∀ p, |p − 4| < ε → …`. Corollaries 5.3, 5.4:
  `∃ K₀ ∀ K ≥ K₀ ∃ δ₀ > 0 ∀ δ ∈ (0, δ₀)`, `Λ = K/δ`. Proposition 6.5 at `q = ∞`: one exponent `α` for
  every `p` (the proof gives `α = 3`), which covers both readings of the paper. Corollary 6.1: the
  paper's `d(p)`, with `d = 2n`; the formalization takes `n = m⁸` and proves every larger `d` as an
  extra lemma ([`corollary6_1_ge`](../../Morrey/Cassese/Square.lean#L2293)).
- **Theorem 1.4** (general `p`) fixes `q = 4` among the paper's `q ∈ (2, ∞)`.

## 7. Departures from the paper's proofs

Every proof follows the paper's argument, except where the table says otherwise. Each departure is
also described in its declaration's docstring and, where it changes a route, in
[`route_differences.tsv`](route_differences.tsv).

| Result | The paper | The formalization | Reason |
| --- | --- | --- | --- |
| Theorem 1.2 ([`theorem1_2`](../../Morrey/Cassese/Introduction.lean#L2029)) | the UMD route of Section 4.4 | the route of the paper's own Remark 4.5: Burkholder's scalar functions `u_q` instead of UMD constants; the paper's route is formalized as [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L1990), conditional on the UMD results | the UMD estimates are out of reach (approved by the user) |
| Theorem 1.3 (b) ([`twoByThree_theorem1_3_b_witness`](../../Morrey/Cassese/TwoByThree/NearFour.lean#L860)) | "by continuity of the estimates" in `p` | explicit constants, uniform and continuous in `p` near `4`; `K`, `δ` and the cut-off fixed before `p` varies | a gap of the paper (E4) |
| Proposition 2.5, "⇐" | every dyadic prelaminate is the law of a rank-one Rademacher martingale (661–663) | Proposition 2.4's gluing argument run on the martingales | that step is false under the reading Proposition 2.4 needs (E10) |
| Proposition 5.1 | "`Q` is rank-one affine at `0`. It follows that `Q` is rank-one affine" | a prelaminate centred at `0` with an atom at `A`, split once more | a gap of the paper (E9) |
| Proposition 7.2 | the identity `Q(∇u) = Σ ρ^{N−j} 𝓑^{N+1−j} h_j` for smooth periodic `u` | for trigonometric test maps, then Fejér means to reach Lipschitz test maps | the operator norm is defined on trigonometric polynomials (representation), and the density step is not in the paper (E28) |
| Corollary 1.6 | rank-one convexity from the distributional second derivative of `G ∘ A` | the same bounds for second differences, then a maximum principle for locally midpoint-convex functions | Mathlib has no distributional second derivatives of convex functions |

Choices that are mechanics, not departures, are described in the docstrings: the regularization
in the zig-zag step of Proposition 4.2 (a supporting majorant instead of mollification); in
Theorem 1.3 (a), Hölder replaced by a pointwise Young bound and the integral over `ℝ³` by the
integral over the unit ball (E20); in Corollary 1.6, the Lipschitz periodic witness that Lemma 2.2
provides instead of a smooth one, with `‖B‖² = 2`; explicit constants (Corollary 5.3's
`c = 75/8`, `C = 4·10⁶`); and the closed form of `ζ` in Proposition 5.2.

The cited results are proved by their sources' standard arguments, with these differences, each
stated in its docstring: Burkholder's inequality smooths the kinks of the special function and
uses `H^{n+1}` for `ℓ²(H)`; Dacorogna's Theorem 5.25 (i) applies Plancherel to smooth maps and
mollifies; his Theorem 5.20 is proved by an induction on the rows (the book was not consulted);
his formula for the quasiconvex envelope glues test maps at points of differentiability;
Rindler's "quasiconvex ⇒ rank-one convex" uses laminates in integer directions and density;
Kristensen's smoothing writes the cut-offs as functions of `|X|²` and adds a constant; the triangle
inequality of Schatten norms goes through Bessel's inequality instead of Ky Fan's dominance; the
sharpness of Burkholder's constant is proved by an explicit dyadic construction (the source was not
consulted).

## 8. What each result depends on

From [`scripts/Audit.lean`](../../scripts/Audit.lean), which also checks every declaration of the
library: every result below depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). The
third column lists the results from prior work each one uses, proved or assumed; an assumed result
appears there as the named hypothesis of the statement.

| Result | Lean | Results from prior work used (proved, or assumed: see Section 2) |
| --- | --- | --- |
| Section 1.1 (monotonicity) | [`Cassese.morreyPositive_mono`](../../Morrey/Cassese/Introduction.lean#L406) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117) |
| Section 1.1 (min (d, m) = 1) | [`Cassese.rankOneConvex_iff_convexOn_of_min_eq_one`](../../Morrey/Cassese/Introduction.lean#L432) | – |
| Section 1.1 (min (d, m) = 1) | [`Cassese.quasiconvex_iff_convexOn_of_min_eq_one`](../../Morrey/Cassese/Introduction.lean#L461) | [`External.Rindler.rankOneConvex_of_quasiconvex`](../../Morrey/Common/External/Rindler/Lemmas.lean#L78) |
| Section 1.1 (min (d, m) = 1) | [`Cassese.morreyPositive_of_min_le_one`](../../Morrey/Cassese/Introduction.lean#L476) | – |
| Section 1.1 (Šverák's example) | [`Cassese.sverak_example`](../../Morrey/Cassese/Sverak.lean#L32) | – |
| Thm 1.1 (Kirchheim–Kristensen, quoted) | [`External.KirchheimKristensen.Theorem1_1`](../../Morrey/Common/External/KirchheimKristensen/Theorem.lean#L25) | – |
| Section 1.3 (homogeneous monotonicity) | [`Cassese.homMorreyPositive_mono`](../../Morrey/Cassese/Introduction.lean#L420) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117) |
| Thm 1.2 | [`Cassese.theorem1_2`](../../Morrey/Cassese/Introduction.lean#L2029) | [`External.Burkholder.scalarFunctionQ_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L581), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Thm 1.2 (the paper's proof) | [`Cassese.theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L1990) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L331), [`Cassese.PisierLpUMD`](../../Morrey/Cassese/Defs.lean#L458), [`Cassese.YaroslavtsevComplexUMD`](../../Morrey/Cassese/Defs.lean#L466) |
| Thm 1.3 (a) | [`Cassese.theorem1_3_a`](../../Morrey/Cassese/Introduction.lean#L2043) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Thm 1.3 (b) | [`Cassese.theorem1_3_b`](../../Morrey/Cassese/Introduction.lean#L2068) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Section 1.4 (2 × 2 landscape) | [`Cassese.morrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2260) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Section 1.4 (homogeneous landscape) | [`Cassese.homMorrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2288) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Thm 1.4 | [`Cassese.theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2100) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L331), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L344), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L355), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L397) |
| Thm 1.5 | [`Cassese.theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2186) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`Cassese.HNVWTransference`](../../Morrey/Cassese/Hypotheses.lean#L110), [`Cassese.DragicevicLowerBound`](../../Morrey/Cassese/Hypotheses.lean#L117) |
| Cor 1.6 | [`Cassese.corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2234) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`Cassese.HNVWTransference`](../../Morrey/Cassese/Hypotheses.lean#L110), [`Cassese.DragicevicLowerBound`](../../Morrey/Cassese/Hypotheses.lean#L117) |
| Lemma 2.1 (Rindler, cited) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) | – |
| Lemma 2.2 (Rindler, cited) | [`External.Rindler.rankOneConvex_of_quasiconvex`](../../Morrey/Common/External/Rindler/Lemmas.lean#L78) | – |
| Lemma 2.2 (Rindler, cited) | [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98) | – |
| Lemma 2.2 (Rindler, cited) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117) | – |
| Prop 2.1 | [`Cassese.proposition2_1`](../../Morrey/Cassese/Toolkit.lean#L779) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Prop 2.2 (Kinderlehrer–Pedregal, cited) | [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) | – |
| Section 2.1 (quasiconvex minorants) | [`Cassese.quasiconvexAt_iff_exists_minorant`](../../Morrey/Cassese/Toolkit.lean#L1176) | [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 2.3 (a) | [`Cassese.proposition2_3_a`](../../Morrey/Cassese/Toolkit.lean#L1285) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 2.3 (b) | [`Cassese.proposition2_3_b`](../../Morrey/Cassese/Toolkit.lean#L1457) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 2.3 (c) | [`Cassese.proposition2_3_c`](../../Morrey/Cassese/Toolkit.lean#L1564) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.rankOneConvex_of_quasiconvex`](../../Morrey/Common/External/Rindler/Lemmas.lean#L78), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 2.3 (c), one direction | [`Cassese.proposition2_3_c_left`](../../Morrey/Cassese/Toolkit.lean#L1595) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.envelope_zero`](../../Morrey/Cassese/Toolkit.lean#L1607) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.rankOneConvexAt_zero_of_rankOneConvexAt`](../../Morrey/Cassese/Toolkit.lean#L1638) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.quasiconvexAt_zero_of_quasiconvexAt`](../../Morrey/Cassese/Toolkit.lean#L1660) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.nowhereQuasiconvex_of_not_quasiconvexAt_zero`](../../Morrey/Cassese/Toolkit.lean#L1682) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 2.4 | [`Cassese.proposition2_4`](../../Morrey/Cassese/Toolkit.lean#L761) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Prop 2.5 | [`Cassese.proposition2_5`](../../Morrey/Cassese/Toolkit.lean#L1934) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Thm 2.3 (1) (Burkholder, cited) | [`Cassese.burkholderInequality_holds`](../../Morrey/Cassese/Hypotheses.lean#L91) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050) |
| Thm 2.3 (2) (Burkholder, cited) | [`Cassese.burkholderSquareFunction_holds`](../../Morrey/Cassese/Hypotheses.lean#L100) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224) |
| Prop 2.6 (Osękowski, quoted) | [`External.Osekowski.HilbertCharacterization`](../../Morrey/Common/External/Osekowski/HilbertCharacterization.lean#L42) | – |
| Prop 2.7 (1) (HNVW, assumed) | [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L331) | – |
| Prop 2.7 (2) (Randrianantoanina, assumed) | [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L344) | – |
| Prop 2.7 (3) (Pisier, assumed) | [`Cassese.PisierLpUMD`](../../Morrey/Cassese/Defs.lean#L458) | – |
| Prop 2.7 (4) (HNVW, assumed) | [`Cassese.HNVWDyadicUMD`](../../Morrey/Cassese/Toolkit.lean#L1980) | – |
| Prop 2.7 (5) (Yaroslavtsev, assumed) | [`Cassese.YaroslavtsevComplexUMD`](../../Morrey/Cassese/Defs.lean#L466) | – |
| Prop 2.7 (6) (HNVW, Yaroslavtsev, assumed) | [`Cassese.HNVWZigZag`](../../Morrey/Cassese/Toolkit.lean#L2003) | – |
| Prop 2.8 (Cox–Veraar, assumed) | [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L355) | – |
| Lemma 4.1 | [`Cassese.lemma4_1`](../../Morrey/Cassese/TwoByM.lean#L227) | – |
| Prop 4.1 | [`Cassese.proposition4_1`](../../Morrey/Cassese/TwoByM.lean#L429) | – |
| Prop 4.1 (nonnegativity) | [`Cassese.proposition4_1_nonneg`](../../Morrey/Cassese/TwoByM.lean#L630) | – |
| Eq. (10) | [`Cassese.equation10`](../../Morrey/Cassese/TwoByM.lean#L665) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Section 4.2 (UMD of ℓ_q) | [`Cassese.umdEllq_lt_top`](../../Morrey/Cassese/TwoByM.lean#L687) | [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L331), [`Cassese.PisierLpUMD`](../../Morrey/Cassese/Defs.lean#L458), [`Cassese.YaroslavtsevComplexUMD`](../../Morrey/Cassese/Defs.lean#L466) |
| Section 4.3 (limiting argument) | [`Cassese.twoByM_ratio_le_qcThreshold`](../../Morrey/Cassese/TwoByM.lean#L3004) | – |
| Lemma 4.2 | [`Cassese.lemma4_2`](../../Morrey/Cassese/TwoByM.lean#L1581) | – |
| Eqs. (13), (14) (Burkholder, cited) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L249) | – |
| Prop 4.2 | [`Cassese.proposition4_2`](../../Morrey/Cassese/TwoByM.lean#L2190) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L249) |
| Prop 4.2 (the minorant) | [`Cassese.proposition4_2_minorant`](../../Morrey/Cassese/TwoByM.lean#L2148) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L249) |
| Section 4.3 (limiting argument, for f_n) | [`Cassese.twoByM_not_qc_explicitF`](../../Morrey/Cassese/TwoByM.lean#L2595) | – |
| Prop 4.3 | [`Cassese.proposition4_3`](../../Morrey/Cassese/TwoByM.lean#L2792) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L249), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Remark 4.5 (Thm 1.2, elementary route) | [`Cassese.theorem1_2_elementary`](../../Morrey/Cassese/TwoByM.lean#L3476) | [`External.Burkholder.scalarFunctionQ_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L581), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 5.1 | [`Cassese.proposition5_1`](../../Morrey/Cassese/TwoByThree/Folklore.lean#L260) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Dacorogna.rankOneAffineMinors_holds`](../../Morrey/Common/External/Dacorogna/Minors.lean#L67), [`External.Dacorogna.quadraticForm_quasiconvex`](../../Morrey/Common/External/Dacorogna/Minors.lean#L95) |
| Section 5.1 (q rank-one convex on 𝓛) | [`Cassese.quarticQ_rankOneConvexOn_calL`](../../Morrey/Cassese/TwoByThree/Basic.lean#L359) | – |
| Section 5.2 (q₃ rank-one convex on 𝓛₃) | [`Cassese.q3_rankOneConvexOn_L3`](../../Morrey/Cassese/TwoByThree/Basic.lean#L367) | – |
| Eq. (24) | [`Cassese.equation24`](../../Morrey/Cassese/TwoByThree/Basic.lean#L381) | – |
| Prop 5.2 | [`Cassese.proposition5_2`](../../Morrey/Cassese/TwoByThree/Witness.lean#L1327) | – |
| Lemma 5.1 (1) | [`Cassese.lemma5_1_part1`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L436) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Lemma 5.1 (1), with constants | [`Cassese.lemma5_1_part1_quant`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L324) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Lemma 5.1 (2) | [`Cassese.lemma5_1_part2`](../../Morrey/Cassese/TwoByThree/Extension.lean#L276) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Proof of Thm 1.3 (κ = 2) | [`Cassese.tbt_correction_identity`](../../Morrey/Cassese/TwoByThree/Basic.lean#L459) | – |
| Proof of Thm 1.3 (κ = 2) | [`Cassese.L3_rankOneCorrection`](../../Morrey/Cassese/TwoByThree/Basic.lean#L481) | – |
| Proof of Thm 1.3 (q_{δ,K/δ} rank-one convex) | [`Cassese.qDeltaLambda_rankOneConvex`](../../Morrey/Cassese/TwoByThree/Extension.lean#L542) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Proof of Thm 1.3 (a) (the witness) | [`Cassese.twoByThree_not_quasiconvexAt_qDeltaLambda`](../../Morrey/Cassese/TwoByThree/WitnessCutoff.lean#L1030) | – |
| Proof of Thm 1.3 (b) (the witness) | [`Cassese.twoByThree_theorem1_3_b_witness`](../../Morrey/Cassese/TwoByThree/NearFour.lean#L860) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Cor 5.2 | [`Cassese.corollary5_2`](../../Morrey/Cassese/NonLocality.lean#L32) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`External.Kristensen.smoothing_holds`](../../Morrey/Common/External/Kristensen/Smoothing.lean#L106) |
| Cor 5.3 | [`Cassese.corollary5_3`](../../Morrey/Cassese/TwoByThree/Transpose.lean#L197) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Cor 5.4 | [`Cassese.corollary5_4`](../../Morrey/Cassese/TwoByThree/HessianCutoff.lean#L408) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Prop 6.1 | [`Cassese.proposition6_1`](../../Morrey/Cassese/Square.lean#L2624) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117) |
| Prop 6.2 | [`Cassese.proposition6_2`](../../Morrey/Cassese/Square.lean#L1016) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L344), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L355), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L397) |
| Prop 6.3 (Pisier–Xu, assumed) | [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374) | – |
| Prop 6.4 (Kahane–Khintchine, assumed) | [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L397) | – |
| Eq. (31) | [`Cassese.equation31`](../../Morrey/Cassese/Square.lean#L814) | [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L397) |
| Remark 6.3 | [`Cassese.remark6_3`](../../Morrey/Cassese/Square.lean#L1222) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L344), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L355), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374), [`Cassese.KahaneKhintchineHypercontractive`](../../Morrey/Cassese/Defs.lean#L417) |
| Prop 6.5 | [`Cassese.proposition6_5`](../../Morrey/Cassese/Square.lean#L1905) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L331), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L344), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L355), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L397), [`Cassese.KahaneKhintchineHypercontractive`](../../Morrey/Cassese/Defs.lean#L417) |
| Prop 6.5 (q < ∞) | [`Cassese.proposition6_5_finite`](../../Morrey/Cassese/Square.lean#L1726) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L331), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L344), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L355), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L397) |
| Prop 6.5 (q = ∞) | [`Cassese.proposition6_5_infty`](../../Morrey/Cassese/Square.lean#L1774) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L331), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L344), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L355), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374), [`Cassese.KahaneKhintchineHypercontractive`](../../Morrey/Cassese/Defs.lean#L417) |
| Cor 6.1 | [`Cassese.corollary6_1`](../../Morrey/Cassese/Square.lean#L2275) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L331), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L344), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L355), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L397) |
| Cor 6.1 (every large d) | [`Cassese.corollary6_1_ge`](../../Morrey/Cassese/Square.lean#L2293) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L331), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L344), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L355), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L374), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L397) |
| Proof of Cor 6.1 (periodic Hessian test maps) | [`Cassese.not_hessianQuasiconvexAt_of_periodic`](../../Morrey/Cassese/Square.lean#L1938) | – |
| Proof of Cor 6.1 (periodic Hessian test maps) | [`Cassese.square_not_hessianQuasiconvexAt_of_periodic`](../../Morrey/Cassese/Square/Hessian.lean#L204) | – |
| Prop 6.6 | [`Cassese.proposition6_6`](../../Morrey/Cassese/Square.lean#L2774) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117) |
| Thm 6.2 | [`Cassese.theorem6_2`](../../Morrey/Cassese/Square.lean#L2827) | – |
| Cor 6.3 (lower bound) | [`Cassese.corollary6_3_lower`](../../Morrey/Cassese/Square.lean#L2964) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`Cassese.burkholderSharpness_holds`](../../Morrey/Cassese/Square/Sharpness.lean#L878) |
| Cor 6.3 (upper bound) | [`Cassese.corollary6_3_upper`](../../Morrey/Cassese/Square.lean#L3100) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Cor 6.3 (separation) | [`Cassese.corollary6_3_separation`](../../Morrey/Cassese/Square.lean#L3198) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117) |
| Cor 6.4 | [`Cassese.corollary6_4`](../../Morrey/Cassese/Square.lean#L3499) | – |
| Cor 6.4 (not quasiconvex) | [`Cassese.corollary6_4_not_quasiconvexAt`](../../Morrey/Cassese/Square.lean#L3548) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117) |
| Thm 1.4, p = 4 (Section 6.4) | [`Cassese.theorem1_4_four`](../../Morrey/Cassese/Square.lean#L3610) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L98), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L58) |
| Prop 7.1 | [`Cassese.proposition7_1`](../../Morrey/Cassese/FourByTwo.lean#L324) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61) |
| Prop 7.2 | [`Cassese.proposition7_2`](../../Morrey/Cassese/FourByTwo.lean#L1398) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117) |
| Prop 7.2 (lower bound) | [`Cassese.proposition7_2_lower`](../../Morrey/Cassese/FourByTwo.lean#L1412) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`Cassese.HNVWTransference`](../../Morrey/Cassese/Hypotheses.lean#L110) |
| Thm 7.1 | [`Cassese.theorem7_1`](../../Morrey/Cassese/FourByTwo.lean#L1545) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L61), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`Cassese.HNVWTransference`](../../Morrey/Cassese/Hypotheses.lean#L110), [`Cassese.DragicevicLowerBound`](../../Morrey/Cassese/Hypotheses.lean#L117) |
| Cor 7.2 | [`Cassese.corollary7_2`](../../Morrey/Cassese/FourByTwo.lean#L1886) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L117), [`Cassese.HNVWTransference`](../../Morrey/Cassese/Hypotheses.lean#L110), [`Cassese.DragicevicL4Bound`](../../Morrey/Cassese/Hypotheses.lean#L124) |
| Conjecture 1 (stated) | [`Cassese.Conjecture1`](../../Morrey/Cassese/Conclusion.lean#L18) | – |

## 9. Not formalized

- Claims stated without proof and used by no argument: the `p > 2` variant of Corollary 1.6
  (2956–2966) and the remark that the construction adapts to Theorems 1.2 and 1.4 (2956–2958);
  Remarks 2.2, 2.4, 4.1–4.4, 5.1–5.4 (5.2: a positively 3-homogeneous Šverák example; 5.3: the
  Cayley hyperdeterminant and extremality; 5.4: examples on `2 × 3` and `3 × 2` for
  `p ∈ (3.6, 5.15)`), 6.1, 6.2, 6.4, 6.5, 7.1, 7.2; the versions for `Sym₀`/`Skew_tr` and `h_{p,q,C}`
  (2521–2549); "`g(AJ)` gives another Hessian counterexample" (2691–2692); taking `p = 4` in the proof
  of Theorem 7.1 (2882–2884); the failure of the vector-valued estimate for `q > 4` (§8.2).
- Interpretations that combine the paper with work not formalized here: "quasiconvexity is non-local
  among smooth integrands" (2061–2064, through Kristensen's theorem), the concentration
  interpretation (279–288), and the relation of Corollary 1.6 to Gennaioli and Rindler's work
  (303–312).
- Context only: Kirchheim–Kristensen's theorem (Theorem 1.1) and its consequence at lines 186–188,
  Grabovsky's examples (196–199), Iwaniec's `C^{rc} ≤ p* − 1` (763–765).
- Conjecture 1 is stated as a definition ([`Conjecture1`](../../Morrey/Cassese/Conclusion.lean#L18)), not proved.

## 10. The paper in the literature

Searched on 21 November 2026: arXiv (the paper's listing and versions, and listings citing it),
journal pages, zbMATH and Crossref, and GitHub for formalizations. Preprints are reported as
claimed, not as proved.

### Before the paper

- Morrey (1952) introduced quasiconvexity and asked whether rank-one convexity implies it. Ball
  (1990) gave a counterexample among extended-valued integrands; Šverák (1992) gave the first
  real-valued one, on `ℝ^{3×2}`, hence for `d ≥ 3` components ([formalized here](../Sverak/README.md)).
  For two components the question stayed open: positive results in special classes (Müller 1999,
  diagonal matrices; Chaudhuri–Müller 2003; Harris–Kirchheim–Lin 2018), Kristensen's non-locality
  theorem (1999), the connection with Burkholder's function and Iwaniec's conjecture (Astala,
  Iwaniec, Prause, Saksman, J. Amer. Math. Soc. 2012), Sebestyén and Székelyhidi's theorem (2017) that
  the gradient measures produced from periodic deformations by Šverák's procedure are laminates in
  `2 × 2`, and numerical evidence (Guerra and Teixeira da Costa, Rev. Mat. Iberoam. 2022).
- Grabovsky (Arch. Ration. Mech. Anal. 2018) gave the only other finite-valued family before 2026,
  on `ℝ^{8×2}`; its examples are nonnegative, hence quasiconvex at `0`.
- Kirchheim and Kristensen (Arch. Ration. Mech. Anal. 221 (2016)) proved that positively
  1-homogeneous rank-one convex integrands are convex at rank-one matrices; according to the paper
  (189–191), they asked the homogeneous problem for `p > 1`. Guerra and Kristensen (Arch. Ration.
  Mech. Anal. 245 (2022)) proved automatic quasiconvexity for homogeneous isotropic integrands, the
  background of Conjecture 1.
- Pedregal's claimed proof for two-component maps ([arXiv:1905.06571](https://arxiv.org/abs/1905.06571),
  [audited here](../Pedregal/README.md)): versions 1–2 (May and September 2019) claimed every
  `2 × N`; version 3 (August 2024) was a withdrawal; versions 4–5 (May 2025, June 2026) claim only
  `2 × 2`. The paper does not cite it. Its Theorem 1.2, and its `2 × 3` example, contradict the claim
  of the withdrawn versions 1–2 for `N ≥ 3`.
- The method rests on the author's correspondence between laminates and martingales (Cassese,
  *Martingales, laminates and minimal Korn inequalities*, J. Math. Pures Appl. 213 (2026),
  [arXiv:2512.02784](https://arxiv.org/abs/2512.02784)) and on Burkholder's martingale inequalities;
  Remarks 4.1 and 6.4 also use Cassese, [arXiv:2603.22431](https://arxiv.org/abs/2603.22431).

### The paper's versions

- v1 (4 August 2026): `2 × m` for large `m`, the square case `d × d` (now Theorem 1.4) and `4 × 2`
  (now Theorem 1.5).
- v2 (28 August 2026): adds a quartic on `2 × 4` and the Hessian corollary (now Corollary 6.1).
- v3 (16 September 2026, formalized here): replaces the `2 × 4` quartic by the `2 × 3` one, adds its
  transpose on `3 × 2` (as a sketch), Corollary 1.6, and the claim that only `2 × 2` remains. No
  journal version or erratum was found.

### Concurrent work

- Bruno and Pasqualotto ([arXiv:2608.06367](https://arxiv.org/abs/2608.06367), 6 August 2026):
  symmetry can force quasiconvexity.
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
  22 October 2026) give a frame-indifferent, non-isotropic example on `ℝ^{3×3}` and cite v3; Braides,
  Kristensen and Scalabrino ([arXiv:2610.32444](https://arxiv.org/abs/2610.32444), 23 October 2026)
  cite the paper; Gammer ([arXiv:2610.35216](https://arxiv.org/abs/2610.35216), 26 October 2026) uses
  its integrand. No correction of the paper and no counterexample to it were found.
- Agazzi, Astala, Bañuelos, Bruno, Cassese, Faraco, Guerra, Hormozi, Kirchheim, Koski, Kovač,
  Kristensen, Pasqualotto, Prause, Saksman, Šverák, Székelyhidi, Tione, Volberg and Yang
  ([arXiv:2609.28311](https://arxiv.org/abs/2609.28311), 23 September 2026, v2 8 October 2026) claim a proof of Iwaniec's
  conjecture, `‖𝓑‖_{L^p} = p* − 1`, which the paper treats as open (§1.3, Remarks 4.3, 6.4, 7.1,
  §8.1). By the paper's equivalence (lines 1158–1162), the integrands behind Theorem 1.2 would then
  give no counterexample in `2 × 2` (the case `n = 1`); the `2 × 2` problem itself stays open.

### Formalizations

- The author formalized Theorem 1.2 and Theorem 1.3 at `p = 4` in Lean (v4.32.2)
  ([MorreyTwoComponentsLean](https://github.com/Gabriele-Cassese/MorreyTwoComponentsLean)), with an
  AI system (the paper's declaration names ChatGPT 5.6 Sol), released without a license; the `2 × 3`
  file was added after v3 and is not in its default build. It was not consulted. This formalization
  covers the whole paper, including what the author's does not: Theorems 1.4 and 1.5,
  Corollaries 1.6 and 5.2–5.4, Sections 6 and 7, and the cited results the paper's proofs use.
- Conti, Dolzmann and Dondl's Lean code for their `3 × 3` example
  ([sergioconti/so3-r1c-and-not-qc](https://github.com/sergioconti/so3-r1c-and-not-qc), Apache-2.0,
  written with Claude Opus 5.5 under the authors' guidance) shares the subject, not the results.

## 11. What's next

Plans for follow-up papers are kept in `NEXT.md`, which is not published.

### Open directions (from the paper and the formalization)

- **`2 × 2`.** The homogeneous problem in `2 × 2` is open; the paper expects a positive answer, and
  notes that it would imply Iwaniec's conjecture, so a proof must use features of the plane (§8.1).
  Iwaniec's conjecture is now claimed proved ([arXiv:2609.28311](https://arxiv.org/abs/2609.28311), Section 10), which removes
  that obstruction but does not decide the problem.
- **Quantitative `m₀`.** The proof gives no value of `m₀(p)`; the paper expects
  `m_*(p) ≤ m₀(p) ≤ 4` and conjectures `m_*(p) ≤ 3` (line 1385).
- **`2 × 3` and `3 × 2` for every `p`.** Claimed for `p ∈ (3.6, 5.15)` (Remark 5.4); proved here on
  `2 × 3` for `p` near `4`, and on `3 × 2` at `p = 4`.
- **Theorem 1.4.** `d₀ = 588` for `h_{4,4,C}` is not optimal (numerics suggest `260`; Remark 6.4),
  and for the integrand (30) the paper expects `d = 3`.
- **Remark 7.2**: `ρ = √2` for every `p`; **Remarks 5.2, 5.3**: a positively 3-homogeneous Šverák
  example, and the extremality of `q`, `q₃`; **§8.2**: the Banach-space geometry viewpoint;
  **Corollary 1.6** for `p > 2` and in lower dimension; the `Sym₀`/`Skew_tr` and `h_{p,q,C}` claims
  (2521–2549).
- **Conjecture 1**: isotropic `p`-homogeneous rank-one convex integrands on `ℝ^{d×d}` are
  quasiconvex at `0`.

### Simpler proofs

- Proposition 4.3 does not need Dacorogna's formula: `g ≤ f`, `g(0) = f(0)` and `g` quasiconvex at
  `0` give `∫ f(∇φ) ≥ ∫ g(∇φ) ≥ g(0) = f(0)` directly (checked in Lean:
  [`twoByM_quasiconvexAt_of_minorant`](../../Morrey/Cassese/TwoByM.lean#L3435), not used by the paper's route).
- Theorem 1.3 (a) does not need `q₃(∇u) ∈ L¹`: the integral over the unit ball is already negative
  (the formal proof does this).
- Corollary 7.2: `𝒫 = f_{4,√2,C₀} − (30|P|² − |Q|²)²` and `2U − (|y|⁴ − 130|x|⁴) = (|y|² − 10|x|²)²`
  give the bound in one line; the zig-zag concavity of `U` has an explicit sum-of-squares
  certificate.
- Section 5: `√2` suffices for `κ` (numerically about `1.054` is optimal) — a sharper constant.

### The formalization

- The remaining hypotheses are the frontier: UMD theory (extrapolation, `L^p` and Schatten classes),
  decoupling, non-commutative Khintchine, the Kahane–Khintchine inequalities and their
  hypercontractive constants, transference, and Dragičević's bound. Dragičević's
  `‖𝓑²‖_{L⁴} ≥ 21/5` could be replaced by explicit truncated test functions (`𝓑²` maps
  `r^{−1/2}e^{4iθ}` to `21/5` times itself); the margin in Corollary 7.2 is only 1.6 %.
- General results built here could go to Mathlib: Burkholder's inequality and square function
  inequality ([`Morrey/Common/External/Burkholder/`](../../Morrey/Common/External/Burkholder)), Dacorogna's formula and the textbook facts of
  quasiconvexity (`Morrey/Common/External/{KinderlehrerPedregal,Rindler,Dacorogna}/`), Fourier series
  of Lipschitz periodic maps and Fejér means ([`Morrey/Common/Basic/Analysis/Fourier/`](../../Morrey/Common/Basic/Analysis/Fourier)), and separately
  convex functions (`Morrey/Common/Basic/Analysis/Convex/`).
