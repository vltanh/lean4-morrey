# Cassese (2026) in Lean: audit report

G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*,
[arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3) (16 September 2026), a preprint.
Formalized in Lean 4 with Mathlib (`v4.36.0-rc2`) from the TeX source of v3, on 21 November 2026,
in a repository that also formalizes Šverák (1992) and Pedregal's claimed `2 × 2` proof
([overview](../../README.md)). Labels in backticks are the paper's TeX labels; labels `cs-…` are
ours, for results the paper does not label ([`paper_routes.tsv`](paper_routes.tsv)). This
formalization was written independently of the author's own Lean code, which was not consulted.

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

**Every result of the paper is formalized and proved.** No statement of the paper is false. The
paper's proofs rest on deep results of martingale theory and Banach-space geometry. Those that
Lean can reach were built here: Burkholder's inequality, Burkholder's functions, Dacorogna's formula
for the quasiconvex envelope, and the textbook facts of the calculus of variations. Those out of
reach are named hypotheses of the theorems whose proofs use them (Section 2): UMD theory for
Schatten classes and `L^p`, non-commutative Khintchine inequalities, transference, and Dragičević's
lower bound for the Beurling–Ahlfors transform.

| Paper | Lean | Statement | Assumes |
| --- | --- | --- | --- |
| Theorem 1.2 | [`theorem1_2`](../../Morrey/Cassese/Introduction.lean#L2046) ⭐ | every `p > 1`: a `p`-homogeneous, rank-one convex, nowhere quasiconvex integrand on `ℝ^{2×m}` for `m ≥ m₀(p)` | nothing (by the paper's Remark 4.5) |
| Theorem 1.2 | [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L2007) | the same, by the paper's main proof | Pisier, Yaroslavtsev, HNVW extrapolation |
| Theorem 1.3 | [`theorem1_3_a`](../../Morrey/Cassese/Introduction.lean#L2060), [`theorem1_3_b`](../../Morrey/Cassese/Introduction.lean#L2085) ⭐ | a quartic polynomial on `ℝ^{2×3}`, rank-one convex and nowhere quasiconvex; and for `p` near `4` | nothing |
| Corollary 5.3 | [`corollary5_3`](../../Morrey/Cassese/TwoByThree/Transpose.lean#L179) ⭐ | its transpose, on `ℝ^{3×2}` | nothing |
| lines 251–254 | [`morrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2279) ⭐ | with Šverák's theorem: Morrey's problem fails in every `d × m` with `d, m ≥ 2` except `2 × 2` | nothing |
| lines 254–256 | [`homMorrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2307) ⭐ | at `p = 4` the homogeneous problem fails in every such size except `2 × 2` | nothing |
| Theorem 1.4 | [`theorem1_4_four`](../../Morrey/Cassese/Square.lean#L3613) ⭐ | at `p = 4`: a conjugation- and transposition-invariant example on `ℝ^{d×d}` for every `d ≥ 588` | nothing |
| Theorem 1.4 | [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2119) ⭐ | every `p > 1`: such an example for `d ≥ d₀(p)` | HNVW extrapolation, Randrianantoanina, Cox–Veraar, Pisier–Xu, Kahane–Khintchine |
| Theorem 1.5 | [`theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2205) ⭐ | every `p ≠ 2`: an example on `ℝ^{4×2}` | transference, Dragičević |
| Corollary 1.6 | [`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2253) ⭐ | a nonnegative 1-homogeneous rank-one convex integrand on `ℝ^{4×4}`, not quasiconvex at a matrix of rank two | transference, Dragičević |

⭐ in [`Challenge.lean`](../../palomar/Cassese/Challenge.lean), checked by Comparator against
[`Solution.lean`](../../palomar/Cassese/Solution.lean).

The proofs follow the paper's arguments. One departure replaces a whole argument, with the user's
approval: Theorem 1.2 is proved unconditionally by the route the paper itself announces in
Remark 4.5 (Burkholder's scalar functions instead of UMD constants); the paper's main proof is
formalized too, as [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L2007), conditional on the UMD results. The other departures are local
and listed in Section 7.

The audit found no false statement, and many steps that the paper leaves to the reader or argues
too briefly (Section 3). Some matter: the uniformity in `p` that Theorem 1.3 (b) needs (E4), a
reading of the prelaminates under which a step of Proposition 2.5 is false (E10), the constant `κ` of
Section 5 asserted without proof (E5; it is true, and `√2` works), and Proposition 6.6 and
Corollary 5.2, which have no proof (E6, E19; both proved here).

## 2. Results from prior work and how the paper uses them

### Proved in `Morrey/Common/External/` and `Morrey/Common/Basic/`

| Result | Where the paper uses it | Source | Lean |
| --- | --- | --- | --- |
| Burkholder's inequality, Hilbert-valued (Theorem 2.3 (1)) | Lemma 5.1, Theorem 1.3 (b), Prop 7.1 | Burkholder 1984; Osękowski 2012, Thm 3.5 | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050) |
| Burkholder's square function inequality (Theorem 2.3 (2)) | Prop 6.5 | Osękowski 2012, Thm 8.6 | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224) |
| Burkholder's function `u₆` and `u_q`, (13), (14) | Prop 4.2, Theorem 1.2 by Remark 4.5 | Burkholder 1988 | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L249), `scalarFunctionQ_holds` |
| a rank-one convex function is locally Lipschitz (Lemma 2.1) | the envelopes, Cor 1.6 | Rindler 2018, Lemma 5.6 | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| quasiconvexity: rank-one convexity, domains, periodic test maps (Lemma 2.2) | Prop 2.3, the thresholds, the lifting | Rindler, Props 5.1, 5.3; Dacorogna 2008, Props 5.11, 5.13 | `External.Rindler.*` |
| Dacorogna's formula for the quasiconvex envelope (Prop 2.2) | line 559, Prop 2.3, Prop 4.3 | Kinderlehrer–Pedregal 1991; Dacorogna 2008, Thm 6.9 | [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| rank-one affine functions are affine in the minors | Prop 5.1 | Dacorogna 2008, Thm 5.20 | [`External.Dacorogna.rankOneAffineMinors_holds`](../../Morrey/Common/External/Dacorogna/Minors.lean#L774) |
| rank-one convex quadratic forms are quasiconvex | Prop 5.1 | Dacorogna 2008, Thm 5.25 (i) | [`External.Dacorogna.quadraticForm_quasiconvex`](../../Morrey/Common/External/Dacorogna/Minors.lean#L109) |
| a smoothing that keeps the failure of quasiconvexity | Cor 5.2 | Kristensen 1999, Prop. 2 | [`External.Kristensen.smoothing_holds`](../../Morrey/Common/External/Kristensen/Smoothing.lean#L505) |
| separately convex functions are locally Lipschitz | Lemma 2.1, Prop 2.2 | Dacorogna 2008, Thm 2.31 | [`Matrix.locallyLipschitz_of_convexOn_single`](../../Morrey/Common/Basic/Analysis/Convex/SeparatelyConvex.lean#L311) |
| Fourier coefficients of Lipschitz periodic maps, Fejér means | Prop 7.2 | standard | [`Morrey/Common/Basic/Analysis/Fourier/TorusLipschitz.lean`](../../Morrey/Common/Basic/Analysis/Fourier/TorusLipschitz.lean) |

The Schatten-norm facts of Section 1.5 (with the triangle inequality and Weyl's monotonicity), the
Bernstein–Doetsch theorem (midpoint convex and continuous implies convex, used without citation)
and the uniform convexity of `|·|^p` (used without citation in (29)) are proved in the paper's
library.

### Assumed: named hypotheses

Each is a hypothesis of exactly the statements whose proofs use it, under its source's name.

| Hypothesis | Source | Used by |
| --- | --- | --- |
| [`HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L373) | Hytönen–van Neerven–Veraar–Weis I, Thm 4.2.7 | [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L2007), Props 6.2, 6.5, [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2119) |
| [`PisierLpUMD`](../../Morrey/Cassese/Defs.lean#L465) | Pisier 2016, Cor 5.22 | [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L2007) |
| [`YaroslavtsevComplexUMD`](../../Morrey/Cassese/Defs.lean#L473) | Yaroslavtsev 2018, Lemma 3.2 | [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L2007) |
| [`RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L386) | Randrianantoanina 2002, Cor 4.5 | Props 6.2, 6.5, [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2119) |
| [`CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L397) | Cox–Veraar 2007 | Props 6.2, 6.5, [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2119) |
| [`PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416) | Pisier–Xu 2003, Thm 6.1 | eq (31), Props 6.2, 6.5, [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2119) |
| [`KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L441) | HNVW II, Thm 6.2.4 (the paper's Prop 6.4) | eq (31), Props 6.2, 6.5, [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2119) |
| [`KahaneKhintchineHypercontractive`](../../Morrey/Cassese/Defs.lean#L424) | the hypercontractive bound `κ_{q,p} ≤ √((q − 1)/(p − 1))`, HNVW II (no source in the paper; E27) | Remark 6.3, Prop 6.5 at `q = ∞` |
| [`HNVWTransference`](../../palomar/Cassese/Challenge.lean#L456) | HNVW I, Cor 5.7.6 | Prop 7.2 (lower bound), Thm 7.1, [`theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2205), [`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2253) |
| [`DragicevicLowerBound`](../../palomar/Cassese/Challenge.lean#L462), [`DragicevicL4Bound`](../../Morrey/Cassese/FourByTwo.lean#L109) | Dragičević 2011, Thm 1.1 | Thm 7.1, Cor 7.2, [`theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2205), [`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2253) |

Two named hypotheses of the toolkit, [`HNVWDyadicUMD`](../../Morrey/Cassese/Toolkit.lean#L1980) and [`HNVWZigZag`](../../Morrey/Cassese/Toolkit.lean#L2003) (Prop 2.7 (4), (6)), are stated
and assumed by no theorem. The sharpness of `p* − 1` for dyadic `±1`-transforms, which the lower
bound of Corollary 6.3 uses, is proved here ([`burkholderSharpness_holds`](../../Morrey/Cassese/Square/Sharpness.lean#L878), by an explicit dyadic
construction and a Bellman function; E30).

Kirchheim and Kristensen's theorem (Theorem 1.1) and Osękowski's characterization of Hilbert spaces
(Prop 2.6) are stated for context; no proof uses them.

### Does the paper use each cited result correctly?

Yes, with two reservations. Remark 6.3 and Proposition 6.5 at `q = ∞` need Kahane–Khintchine
constants that grow polynomially in `q`, which the cited Proposition 6.4 does not give (E27). The
lower bound of Corollary 6.3 uses the sharpness of `p* − 1` for dyadic `±1`-transforms with only "see
also [Cassese 2025]" as a source (E30).

## 3. Errors and gaps in the paper

No statement is false. The items below are gaps (steps that need an argument the paper does not
give), one false intermediate claim under a natural reading (E10), and misprints. The formalization
supplies each gap; the column says how.

| | Lines | Issue | In the formalization |
| --- | --- | --- | --- |
| E1 | 183, 225–302 | numbering: the cited Theorem 1.1 (Kirchheim–Kristensen) shifts the paper's own main theorems to 1.2–1.5 | not an error; the Lean names follow the printed numbers |
| E2 | 375–377, 2350–2378 | Schatten fact (1) is stated for `q ≥ 2`, but Proposition 6.2 uses it at exponent `q/2 ∈ (1, 2)` | proved for `q ≥ 1` |
| E3 | 1914–1929 | Lemma 5.1 (2), eq (28): the first-order cancellation `E[Df(X)·𝓔_n] = 0` is not mentioned; it also needs a Lipschitz bound on `Df` across the origin | supplied |
| E4 | 2031–2046 | Theorem 1.3 (b): "continuity of the estimates" in `p` needs the constant `Λ` of Lemma 5.1 (1) uniform for `p` near `4`, and the cut-off fixed before `p` varies | a uniform quantitative Lemma 5.1 (1) ([`lemma5_1_part1_quant`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L324)) |
| E5 | 1978–1979 | "`L₃` satisfies the hypothesis of Lemma 5.1 with `κ = 2`" has no proof | proved; the natural correction gives exactly `√2`, and `κ = 2` covers the rank-exactly-one requirement |
| E6 | 2558–2563 | Proposition 6.6 has no proof | proved, from exact trigonometric moments |
| E7 | 2683–2684 | Corollary 6.4: the bound on `⟨W, Z⟩` does not follow "by the assumption on `(E, D)`"; it is a trace argument, and also uses `‖W‖ ≤ 2a`, `ρ ≤ 2e` | supplied |
| E8 | 562–578 | Proposition 2.3 has no proof; part (c) "⇒" needs Dacorogna's formula (line 559) | proved: (a), (b) from the dual formulas, (c) through line 559 |
| E9 | 1406–1411 | Proposition 5.1: "`Q` is rank-one affine" and "`P − Q` is rank-one convex" skip arguments | supplied (a prelaminate centred at `0` with an atom at `A`) |
| E10 | 504–530, 661–663 | prelaminates: Proposition 2.4's gluing needs repeated atoms, and with repeated atoms "every dyadic prelaminate is the law of a rank-one Rademacher martingale" (661–663) is false (split a third of `δ₀`: weight `1/6`); under the whole-atom reading the gluing fails instead | Proposition 2.5 "⇐" by Proposition 2.4's argument on the martingales (Section 7) |
| E11 | 1130 | Remark 4.2 writes `UMD_p` where `UMD_{ℂ,p}` is meant | misprint |
| E12 | 245, 1376, 1415 | Section 5 and Theorem 1.3 are labelled `2x4` but are about `2 × 3` | misprint |
| E13 | 68, 246 | the abstract calls the quartic "explicit", but it depends on unspecified `K` and `δ` | wording |
| E14 | 1355–1366 | Proposition 4.3 needs `n` of order `10^{80}` (the threshold grows like `n^{1/30}`) | not an error: the proofs are existence proofs |
| E15 | 1585–1590 | the wave equation the proof mentions is never stated | cosmetic |
| E16 | 1821–1832 | Lemma 5.1 asks for a rank-one `R_L`; `R_L = 0` must be allowed | allowed |
| E17 | 2121–2123 | Corollary 5.3: the constants are only said to exist | checked: the Lean uses `c = 75/8`, `C = 4·10⁶` |
| E18 | 2956–2966 | the `p > 2` variant of Corollary 1.6 is asserted without proof | not formalized |
| E19 | 2051–2065 | Corollary 5.2 has no proof, only references | proved, through Kristensen's smoothing (proved) |
| E20 | 1602–1614 | Proposition 5.2 lists `q₃(∇u) ∈ L¹`, which Theorem 1.3 does not need | not an error; proved anyway |
| E21 | 466–468, 600–700 | Propositions 2.3–2.5 apply Lemma 2.1 to the infimum `G` before `G` is known to be an integrand; Lemma 2.1 as stated ("an integrand") would be circular | Rindler's form (any real-valued rank-one convex function) |
| E22 | 559 | the passage from the ball (Proposition 2.2) to the cube (Definition 2.1) is silent; it needs Lemma 2.2 (ii) | supplied |
| E23 | 1047–1053 | the "straightforward limiting argument" from Schwartz test maps to Definition 2.1 is not given | proved ([`twoByM_ratio_le_qcThreshold`](../../Morrey/Cassese/TwoByM.lean#L2924)) |
| E24 | 1891–1895 | Lemma 5.1 (1): "by homogeneity and Young's inequality" needs a Lipschitz bound on `g`, which is only continuous | uniform continuity on a compact set and homogeneity |
| E25 | 1849, 1956, 1991 | Lemma 5.1 (2) is stated for `δ ∈ (0, 1)` and used at `δ = 1` | covered |
| E26 | Remark 4.5 | gives no constant: `K = 2(q − 1)^{p+1}/(p − 1)`, and (13) for `u_q` needs `q ≥ 2` | supplied (`q = p + 3`) |
| E27 | 2425–2437, 2477–2479 | Remark 6.3 and Proposition 6.5 at `q = ∞` need Kahane–Khintchine constants polynomial in `q`; Proposition 6.4 gives none and no source is named | the hypercontractive bound, assumed |
| E28 | 2807–2821, 2211–2216 | Proposition 7.2 "≤" argues with smooth maps, Lemma 2.2 tests with Lipschitz periodic maps; the density step is not stated | Fejér means |
| E29 | 2489–2520 | Corollary 6.1: the reduction from periodic to compactly supported Hessian test maps is not stated, and "the calculation of Proposition 6.1" does not carry over (the skew part of `JD²φ` has two distinct doubled singular values) | supplied (rank `≤ 4`, `S₂` against `S₄`) |
| E30 | 2624–2633 | Corollary 6.3's lower bound cites the sharpness of `p* − 1` only through "see also [Cassese 2025]" | proved here ([`burkholderSharpness_holds`](../../Morrey/Cassese/Square/Sharpness.lean#L878)) |

The constants of Corollary 6.3 (`d₀ = 588` is the least that works) and Corollary 7.2 (`130`,
`1170`) check out.

## 4. Missing hypotheses

None.

## 5. Redundant hypotheses

The proofs do not use: `A ∈ 𝓛` in the rank-one convexity of the quartic on `𝓛` (`cs-q-rc`; it holds
from any base point); `q > p + 2` in Lemma 4.1 and Proposition 4.1 (the section's standing
assumption); `ρ > 0` in Proposition 7.2; `d ≥ 2` in Corollary 6.3's upper bound; the homogeneity and
`p > 1` in Proposition 2.3 (b), (c) (and only `p > 0` in (a)); `1 < p` in the monotonicity of the
homogeneous problem. They are kept, as the paper states them.

## 6. How the formalization reads the paper

- **Integrands and test maps.** Matrices `ℝ^{d×m}` are `Matrix (Fin d) (Fin m) ℝ`, the gradient of
  `φ` is `jac φ` (rows are components), an "integrand" (line 348) is lower semicontinuous and locally
  bounded ([`IsIntegrand`](../../palomar/Cassese/Challenge.lean#L157)). `W^{1,∞}_0([0, 1]^m)` maps are Lipschitz maps vanishing outside the open
  cube; their gradient is `fderiv`, defined almost everywhere by Rademacher's theorem. Definition 2.1
  also asks the integral to exist, which is automatic for integrands and makes a failure of
  quasiconvexity a genuine integral.
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
  `∃ K₀ ∀ K ≥ K₀ ∃ δ₀ > 0 ∀ δ ∈ (0, δ₀)`, `Λ = K/δ`. Proposition 6.5 at `q = ∞`: one exponent `α` for every `p`
  (the proof gives `α = 3`), which covers both readings of the paper. Corollary 6.1: one dimension
  `d = 2m⁸`, as printed, with every large `d` as an extra lemma ([`corollary6_1_ge`](../../Morrey/Cassese/Square.lean#L2298)).
- **Theorem 1.4** (general `p`) fixes `q = 4` among the paper's `q ∈ (2, ∞)`.

## 7. Departures from the paper's proofs

Every proof follows the paper's argument, except where the table says otherwise. Each departure is
also described in its declaration's docstring and, where it changes a route, in
[`route_differences.tsv`](route_differences.tsv).

| Result | The paper | The formalization | Reason |
| --- | --- | --- | --- |
| Theorem 1.2 ([`theorem1_2`](../../Morrey/Cassese/Introduction.lean#L2046)) | the UMD route of Section 4.4 | the route of the paper's own Remark 4.5: Burkholder's scalar functions `u_q` instead of UMD constants; the paper's route is formalized as [`theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L2007), conditional on the UMD results | the UMD estimates are out of reach (approved by the user) |
| Theorem 1.3 (b) ([`twoByThree_theorem1_3_b_witness`](../../Morrey/Cassese/TwoByThree/NearFour.lean#L860)) | "by continuity of the estimates" in `p` | explicit constants, uniform and continuous in `p` near `4`; `K`, `δ` and the cut-off fixed before `p` varies | a gap of the paper (E4) |
| Proposition 2.5, "⇐" | every dyadic prelaminate is the law of a rank-one Rademacher martingale (661–663) | Proposition 2.4's gluing argument run on the martingales | that step is false under the reading Proposition 2.4 needs (E10) |
| Proposition 5.1 | "`Q` is rank-one affine at `0`. It follows that `Q` is rank-one affine" | a prelaminate centred at `0` with an atom at `A`, split once more | a gap of the paper (E9) |
| Proposition 7.2 | the identity `Q(∇u) = Σ ρ^{N−j} 𝓑^{N+1−j} h_j` for smooth periodic `u` | for trigonometric test maps, then Fejér means to reach Lipschitz test maps | the operator norm is defined on trigonometric polynomials (representation), and the density step is not in the paper (E28) |
| Corollary 1.6 | rank-one convexity from the distributional second derivative of `G ∘ A` | the same bounds for second differences, then a maximum principle for locally midpoint-convex functions; the witness is the Lipschitz periodic one of Lemma 2.2, with `‖B‖² = 2` | Mathlib has no distributional second derivatives of convex functions |

Choices that are mechanics, not departures, are described in the docstrings: the regularization
in the zig-zag step of Proposition 4.2 (a supporting majorant instead of mollification), Hölder
replaced by a pointwise Young bound in Theorem 1.3 (a), explicit constants (`c = 6`-type choices,
Corollary 5.3's `c = 75/8`, `C = 4·10⁶`), and the closed form of `ζ` in Proposition 5.2.

The cited results are proved by their sources' standard arguments, with these differences, each
stated in its docstring: Burkholder's inequality smooths the kinks of the special function and
uses `H^{n+1}` for `ℓ²(H)`; Dacorogna's Theorem 5.25 (i) applies Plancherel to smooth maps and
mollifies; his Theorem 5.20 is proved by an induction on the rows (the book was not consulted);
his formula for the quasiconvex envelope glues test maps at points of differentiability;
Rindler's "quasiconvex ⇒ rank-one convex" uses laminates in integer directions and density;
Kristensen's smoothing writes the cut-offs as functions of `|X|²` and adds a constant; the triangle
inequality of Schatten norms goes through Bessel's inequality instead of Ky Fan's dominance.

## 8. What each result depends on

From [`scripts/Audit.lean`](../../scripts/Audit.lean), which also checks every declaration of the
library: every result below depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). The
third column lists the results from prior work each one uses, proved or assumed; an assumed result
appears there as the named hypothesis of the statement.

| Result | Lean | Results from prior work used (proved, or assumed: see Section 2) |
| --- | --- | --- |
| Section 1.1 (monotonicity) | [`Cassese.morreyPositive_mono`](../../Morrey/Cassese/Introduction.lean#L404) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567) |
| Section 1.1 (min (d, m) = 1) | [`Cassese.rankOneConvex_iff_convexOn_of_min_eq_one`](../../Morrey/Cassese/Introduction.lean#L430) | – |
| Section 1.1 (min (d, m) = 1) | [`Cassese.quasiconvex_iff_convexOn_of_min_eq_one`](../../Morrey/Cassese/Introduction.lean#L459) | [`External.Rindler.rankOneConvex_of_quasiconvex`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1125) |
| Section 1.1 (min (d, m) = 1) | [`Cassese.morreyPositive_of_min_le_one`](../../Morrey/Cassese/Introduction.lean#L474) | – |
| Section 1.1 (Šverák's example) | [`Cassese.sverak_example`](../../Morrey/Cassese/Sverak.lean#L32) | – |
| Thm 1.1 (Kirchheim–Kristensen, quoted) | [`External.KirchheimKristensen.Theorem1_1`](../../Morrey/Common/External/KirchheimKristensen/Theorem.lean#L25) | – |
| Section 1.3 (homogeneous monotonicity) | [`Cassese.homMorreyPositive_mono`](../../Morrey/Cassese/Introduction.lean#L418) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567) |
| Thm 1.2 | [`Cassese.theorem1_2`](../../Morrey/Cassese/Introduction.lean#L2046) | [`External.Burkholder.scalarFunctionQ_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L581), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Thm 1.2 (the paper's proof) | [`Cassese.theorem1_2_umd`](../../Morrey/Cassese/Introduction.lean#L2007) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L373), [`Cassese.PisierLpUMD`](../../Morrey/Cassese/Defs.lean#L465), [`Cassese.YaroslavtsevComplexUMD`](../../Morrey/Cassese/Defs.lean#L473) |
| Thm 1.3 (a) | [`Cassese.theorem1_3_a`](../../Morrey/Cassese/Introduction.lean#L2060) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Thm 1.3 (b) | [`Cassese.theorem1_3_b`](../../Morrey/Cassese/Introduction.lean#L2085) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Section 1.4 (2 × 2 landscape) | [`Cassese.morrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2279) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Section 1.4 (homogeneous landscape) | [`Cassese.homMorrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2307) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Thm 1.4 | [`Cassese.theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2119) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L373), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L386), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L397), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L441) |
| Thm 1.5 | [`Cassese.theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2205) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393), [`Cassese.HNVWTransference`](../../palomar/Cassese/Challenge.lean#L456), [`Cassese.DragicevicLowerBound`](../../palomar/Cassese/Challenge.lean#L462) |
| Cor 1.6 | [`Cassese.corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2253) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393), [`Cassese.HNVWTransference`](../../palomar/Cassese/Challenge.lean#L456), [`Cassese.DragicevicLowerBound`](../../palomar/Cassese/Challenge.lean#L462) |
| Lemma 2.1 (Rindler, cited) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) | – |
| Lemma 2.2 (Rindler, cited) | [`External.Rindler.rankOneConvex_of_quasiconvex`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1125) | – |
| Lemma 2.2 (Rindler, cited) | [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544) | – |
| Lemma 2.2 (Rindler, cited) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567) | – |
| Prop 2.1 | [`Cassese.proposition2_1`](../../Morrey/Cassese/Toolkit.lean#L779) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Prop 2.2 (Kinderlehrer–Pedregal, cited) | [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) | – |
| Section 2.1 (quasiconvex minorants) | [`Cassese.quasiconvexAt_iff_exists_minorant`](../../Morrey/Cassese/Toolkit.lean#L1176) | [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Prop 2.3 (a) | [`Cassese.proposition2_3_a`](../../Morrey/Cassese/Toolkit.lean#L1285) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Prop 2.3 (b) | [`Cassese.proposition2_3_b`](../../Morrey/Cassese/Toolkit.lean#L1457) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Prop 2.3 (c) | [`Cassese.proposition2_3_c`](../../Morrey/Cassese/Toolkit.lean#L1564) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.rankOneConvex_of_quasiconvex`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1125), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Prop 2.3 (c), one direction | [`Cassese.proposition2_3_c_left`](../../Morrey/Cassese/Toolkit.lean#L1595) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.envelope_zero`](../../Morrey/Cassese/Toolkit.lean#L1607) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.rankOneConvexAt_zero_of_rankOneConvexAt`](../../Morrey/Cassese/Toolkit.lean#L1638) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.quasiconvexAt_zero_of_quasiconvexAt`](../../Morrey/Cassese/Toolkit.lean#L1660) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Section 2.1 (consequences of Prop 2.3) | [`Cassese.nowhereQuasiconvex_of_not_quasiconvexAt_zero`](../../Morrey/Cassese/Toolkit.lean#L1682) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Prop 2.4 | [`Cassese.proposition2_4`](../../Morrey/Cassese/Toolkit.lean#L761) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Prop 2.5 | [`Cassese.proposition2_5`](../../Morrey/Cassese/Toolkit.lean#L1934) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Thm 2.3 (1) (Burkholder, cited) | [`Cassese.burkholderInequality_holds`](../../Morrey/Cassese/Hypotheses.lean#L65) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050) |
| Thm 2.3 (2) (Burkholder, cited) | [`Cassese.burkholderSquareFunction_holds`](../../Morrey/Cassese/Hypotheses.lean#L74) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224) |
| Prop 2.6 (Osękowski, quoted) | [`External.Osekowski.HilbertCharacterization`](../../Morrey/Common/External/Osekowski/HilbertCharacterization.lean#L42) | – |
| Prop 2.7 (1) (HNVW, assumed) | [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L373) | – |
| Prop 2.7 (2) (Randrianantoanina, assumed) | [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L386) | – |
| Prop 2.7 (3) (Pisier, assumed) | [`Cassese.PisierLpUMD`](../../Morrey/Cassese/Defs.lean#L465) | – |
| Prop 2.7 (4) (HNVW, assumed) | [`Cassese.HNVWDyadicUMD`](../../Morrey/Cassese/Toolkit.lean#L1980) | – |
| Prop 2.7 (5) (Yaroslavtsev, assumed) | [`Cassese.YaroslavtsevComplexUMD`](../../Morrey/Cassese/Defs.lean#L473) | – |
| Prop 2.7 (6) (HNVW, Yaroslavtsev, assumed) | [`Cassese.HNVWZigZag`](../../Morrey/Cassese/Toolkit.lean#L2003) | – |
| Prop 2.8 (Cox–Veraar, assumed) | [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L397) | – |
| Lemma 4.1 | [`Cassese.lemma4_1`](../../Morrey/Cassese/TwoByM.lean#L226) | – |
| Prop 4.1 | [`Cassese.proposition4_1`](../../Morrey/Cassese/TwoByM.lean#L428) | – |
| Prop 4.1 (nonnegativity) | [`Cassese.proposition4_1_nonneg`](../../Morrey/Cassese/TwoByM.lean#L629) | – |
| Eq. (10) | [`Cassese.equation10`](../../Morrey/Cassese/TwoByM.lean#L664) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Section 4.2 (UMD of ℓ_q) | [`Cassese.umdEllq_lt_top`](../../Morrey/Cassese/TwoByM.lean#L686) | [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L373), [`Cassese.PisierLpUMD`](../../Morrey/Cassese/Defs.lean#L465), [`Cassese.YaroslavtsevComplexUMD`](../../Morrey/Cassese/Defs.lean#L473) |
| Section 4.3 (limiting argument) | [`Cassese.twoByM_ratio_le_qcThreshold`](../../Morrey/Cassese/TwoByM.lean#L2924) | – |
| Lemma 4.2 | [`Cassese.lemma4_2`](../../Morrey/Cassese/TwoByM.lean#L1580) | – |
| Eqs. (13), (14) (Burkholder, cited) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L249) | – |
| Prop 4.2 | [`Cassese.proposition4_2`](../../Morrey/Cassese/TwoByM.lean#L2110) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L249) |
| Prop 4.2 (the minorant) | [`Cassese.proposition4_2_minorant`](../../Morrey/Cassese/TwoByM.lean#L2068) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L249) |
| Section 4.3 (limiting argument, for f_n) | [`Cassese.twoByM_not_qc_explicitF`](../../Morrey/Cassese/TwoByM.lean#L2515) | – |
| Prop 4.3 | [`Cassese.proposition4_3`](../../Morrey/Cassese/TwoByM.lean#L2712) | [`External.Burkholder.scalarFunction_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L249), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Remark 4.5 (Thm 1.2, elementary route) | [`Cassese.theorem1_2_elementary`](../../Morrey/Cassese/TwoByM.lean#L3465) | [`External.Burkholder.scalarFunctionQ_holds`](../../Morrey/Common/External/Burkholder/ScalarFunction.lean#L581), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Prop 5.1 | [`Cassese.proposition5_1`](../../Morrey/Cassese/TwoByThree/Folklore.lean#L215) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Dacorogna.rankOneAffineMinors_holds`](../../Morrey/Common/External/Dacorogna/Minors.lean#L774), [`External.Dacorogna.quadraticForm_quasiconvex`](../../Morrey/Common/External/Dacorogna/Minors.lean#L109) |
| Section 5.1 (q rank-one convex on 𝓛) | [`Cassese.quarticQ_rankOneConvexOn_calL`](../../Morrey/Cassese/TwoByThree/Basic.lean#L359) | – |
| Section 5.2 (q₃ rank-one convex on 𝓛₃) | [`Cassese.q3_rankOneConvexOn_L3`](../../Morrey/Cassese/TwoByThree/Basic.lean#L367) | – |
| Eq. (24) | [`Cassese.equation24`](../../Morrey/Cassese/TwoByThree/Basic.lean#L381) | – |
| Prop 5.2 | [`Cassese.proposition5_2`](../../Morrey/Cassese/TwoByThree/Witness.lean#L1189) | – |
| Lemma 5.1 (1) | [`Cassese.lemma5_1_part1`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L436) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Lemma 5.1 (1), with constants | [`Cassese.lemma5_1_part1_quant`](../../Morrey/Cassese/TwoByThree/ExtensionOne.lean#L324) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Lemma 5.1 (2) | [`Cassese.lemma5_1_part2`](../../Morrey/Cassese/TwoByThree/Extension.lean#L276) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Proof of Thm 1.3 (κ = 2) | [`Cassese.tbt_correction_identity`](../../Morrey/Cassese/TwoByThree/Basic.lean#L459) | – |
| Proof of Thm 1.3 (κ = 2) | [`Cassese.L3_rankOneCorrection`](../../Morrey/Cassese/TwoByThree/Basic.lean#L481) | – |
| Proof of Thm 1.3 (q_{δ,K/δ} rank-one convex) | [`Cassese.qDeltaLambda_rankOneConvex`](../../Morrey/Cassese/TwoByThree/Extension.lean#L542) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Proof of Thm 1.3 (a) (the witness) | [`Cassese.twoByThree_not_quasiconvexAt_qDeltaLambda`](../../Morrey/Cassese/TwoByThree/WitnessCutoff.lean#L729) | – |
| Proof of Thm 1.3 (b) (the witness) | [`Cassese.twoByThree_theorem1_3_b_witness`](../../Morrey/Cassese/TwoByThree/NearFour.lean#L860) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Cor 5.2 | [`Cassese.corollary5_2`](../../Morrey/Cassese/NonLocality.lean#L32) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393), [`External.Kristensen.smoothing_holds`](../../Morrey/Common/External/Kristensen/Smoothing.lean#L505) |
| Cor 5.3 | [`Cassese.corollary5_3`](../../Morrey/Cassese/TwoByThree/Transpose.lean#L179) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Cor 5.4 | [`Cassese.corollary5_4`](../../Morrey/Cassese/TwoByThree/HessianCutoff.lean#L473) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Prop 6.1 | [`Cassese.proposition6_1`](../../Morrey/Cassese/Square.lean#L2627) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567) |
| Prop 6.2 | [`Cassese.proposition6_2`](../../Morrey/Cassese/Square.lean#L1018) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L386), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L397), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L441) |
| Prop 6.3 (Pisier–Xu, assumed) | [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416) | – |
| Prop 6.4 (Kahane–Khintchine, assumed) | [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L441) | – |
| Eq. (31) | [`Cassese.equation31`](../../Morrey/Cassese/Square.lean#L815) | [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L441) |
| Remark 6.3 | [`Cassese.remark6_3`](../../Morrey/Cassese/Square.lean#L1226) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L386), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L397), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416), [`Cassese.KahaneKhintchineHypercontractive`](../../Morrey/Cassese/Defs.lean#L424) |
| Prop 6.5 | [`Cassese.proposition6_5`](../../Morrey/Cassese/Square.lean#L1909) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L373), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L386), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L397), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L441), [`Cassese.KahaneKhintchineHypercontractive`](../../Morrey/Cassese/Defs.lean#L424) |
| Prop 6.5 (q < ∞) | [`Cassese.proposition6_5_finite`](../../Morrey/Cassese/Square.lean#L1730) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L373), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L386), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L397), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L441) |
| Prop 6.5 (q = ∞) | [`Cassese.proposition6_5_infty`](../../Morrey/Cassese/Square.lean#L1778) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L373), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L386), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L397), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416), [`Cassese.KahaneKhintchineHypercontractive`](../../Morrey/Cassese/Defs.lean#L424) |
| Cor 6.1 | [`Cassese.corollary6_1`](../../Morrey/Cassese/Square.lean#L2280) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L373), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L386), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L397), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L441) |
| Cor 6.1 (every large d) | [`Cassese.corollary6_1_ge`](../../Morrey/Cassese/Square.lean#L2298) | [`External.Burkholder.squareFunction`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1224), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393), [`Cassese.HNVWExtrapolation`](../../palomar/Cassese/Challenge.lean#L373), [`Cassese.RandrianantoaninaSchattenUMD`](../../palomar/Cassese/Challenge.lean#L386), [`Cassese.CoxVeraarDecoupling`](../../palomar/Cassese/Challenge.lean#L397), [`Cassese.PisierXuKhintchine`](../../palomar/Cassese/Challenge.lean#L416), [`Cassese.KahaneKhintchine`](../../palomar/Cassese/Challenge.lean#L441) |
| Proof of Cor 6.1 (periodic Hessian test maps) | [`Cassese.not_hessianQuasiconvexAt_of_periodic`](../../Morrey/Cassese/Square.lean#L1942) | – |
| Proof of Cor 6.1 (periodic Hessian test maps) | [`Cassese.square_not_hessianQuasiconvexAt_of_periodic`](../../Morrey/Cassese/Square/Hessian.lean#L204) | – |
| Prop 6.6 | [`Cassese.proposition6_6`](../../Morrey/Cassese/Square.lean#L2777) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567) |
| Thm 6.2 | [`Cassese.theorem6_2`](../../Morrey/Cassese/Square.lean#L2830) | – |
| Cor 6.3 (lower bound) | [`Cassese.corollary6_3_lower`](../../Morrey/Cassese/Square.lean#L2967) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`Cassese.burkholderSharpness_holds`](../../Morrey/Cassese/Square/Sharpness.lean#L878) |
| Cor 6.3 (upper bound) | [`Cassese.corollary6_3_upper`](../../Morrey/Cassese/Square.lean#L3103) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Cor 6.3 (separation) | [`Cassese.corollary6_3_separation`](../../Morrey/Cassese/Square.lean#L3201) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567) |
| Cor 6.4 | [`Cassese.corollary6_4`](../../Morrey/Cassese/Square.lean#L3502) | – |
| Cor 6.4 (not quasiconvex) | [`Cassese.corollary6_4_not_quasiconvexAt`](../../Morrey/Cassese/Square.lean#L3551) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567) |
| Thm 1.4, p = 4 (Section 6.4) | [`Cassese.theorem1_4_four`](../../Morrey/Cassese/Square.lean#L3613) | [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1544), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`External.KinderlehrerPedregal.dacorognaFormula_holds`](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean#L393) |
| Prop 7.1 | [`Cassese.proposition7_1`](../../Morrey/Cassese/FourByTwo.lean#L333) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84) |
| Prop 7.2 | [`Cassese.proposition7_2`](../../Morrey/Cassese/FourByTwo.lean#L1407) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567) |
| Prop 7.2 (lower bound) | [`Cassese.proposition7_2_lower`](../../Morrey/Cassese/FourByTwo.lean#L1420) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`Cassese.HNVWTransference`](../../palomar/Cassese/Challenge.lean#L456) |
| Thm 7.1 | [`Cassese.theorem7_1`](../../Morrey/Cassese/FourByTwo.lean#L1552) | [`External.Burkholder.inequality`](../../Morrey/Common/External/Burkholder/Inequality.lean#L1050), [`External.Rindler.lemma5_6`](../../Morrey/Common/External/Rindler/Lemmas.lean#L84), [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`Cassese.HNVWTransference`](../../palomar/Cassese/Challenge.lean#L456), [`Cassese.DragicevicLowerBound`](../../palomar/Cassese/Challenge.lean#L462) |
| Cor 7.2 | [`Cassese.corollary7_2`](../../Morrey/Cassese/FourByTwo.lean#L1893) | [`External.Rindler.quasiconvexAtOn_iff_periodic`](../../Morrey/Common/External/Rindler/Lemmas.lean#L1567), [`Cassese.HNVWTransference`](../../palomar/Cassese/Challenge.lean#L456), [`Cassese.DragicevicL4Bound`](../../Morrey/Cassese/FourByTwo.lean#L109) |
| Conjecture 1 (stated) | [`Cassese.Conjecture1`](../../Morrey/Cassese/Conclusion.lean#L18) | – |

## 9. Not formalized

- Claims stated without proof and used by no argument: the `p > 2` variant of Corollary 1.6
  (2956–2966); Remark 6.1 (sharpness up to `d^{1/(2q)}`); the versions for `Sym₀`/`Skew_tr` and
  `h_{p,q,C}` (2521–2549); "`g(AJ)` gives another Hessian counterexample" (2691–2692); Remarks 4.1–4.4,
  6.4, 6.5, 7.1, 7.2; taking `p = 4` in the proof of Theorem 7.1 (2882–2884).
- Context only: Kirchheim–Kristensen's theorem (Theorem 1.1) and its consequence at lines 186–188,
  Grabovsky's examples (196–199), Iwaniec's `C^{rc} ≤ p* − 1` (763–765), Remark 2.2.
- Conjecture 1 is stated as a definition ([`Conjecture1`](../../Morrey/Cassese/Conclusion.lean#L18)), not proved.

## 10. The paper in the literature

### Before the paper

- Morrey (1952) introduced quasiconvexity and asked whether rank-one convexity implies it. Ball
  (1990) gave a counterexample among extended-valued integrands; Šverák (1992) gave the first
  real-valued one, on `ℝ^{3×2}`, hence for `d ≥ 3` components ([formalized here](../Sverak/README.md)).
  For two components the question stayed open: positive results in special classes (Müller 1999,
  diagonal matrices; Chaudhuri–Müller 2003; Harris–Kirchheim–Lin 2018), Kristensen's non-locality
  theorem (1999), the connection with Burkholder's function and Iwaniec's conjecture (Astala,
  Iwaniec, Prause, Saksman 2012), Sebestyén and Székelyhidi's theorem that Šverák's mechanism cannot
  work in `2 × 2` (2017), numerical evidence (Guerra and Teixeira da Costa 2022).
- Grabovsky (2018) gave the only other finite-valued family before 2026, on `ℝ^{8×2}`; its examples
  are nonnegative, hence quasiconvex at `0`.
- Kirchheim and Kristensen (2016) proved that positively 1-homogeneous rank-one convex integrands
  are convex at rank-one matrices, and asked the homogeneous problem for `p > 1`.
- The method rests on the author's earlier correspondence between laminates and martingales
  (Cassese, J. Math. Pures Appl. 213 (2025)) and on Burkholder's martingale inequalities.

### The paper's versions

- v1 (4 August 2026): `2 × m` for large `m`.
- v2 (28 August 2026): adds `2 × 4`.
- v3 (16 September 2026, formalized here): adds the `2 × 3` quartic and its transpose, and with
  Šverák's theorem the claim that only `2 × 2` remains.

### Concurrent and later work

- Agazzi, Bruno, Guerra and Pasqualotto ([arXiv:2608.12298](https://arxiv.org/abs/2608.12298),
  12 August 2026, between v1 and v2): a non-homogeneous example on `ℝ^{2×4}` from Grabovsky's
  integrand, and examples on symmetric matrices.
- Gennaioli and Rindler ([arXiv:2608.20899](https://arxiv.org/abs/2608.20899)): the Vanishing Mass
  Conjecture; the paper contrasts it with Corollary 1.6.
- Guerra ([arXiv:2608.23388](https://arxiv.org/abs/2608.23388)): the Burkholder function is
  quasiconvex on symmetric matrices. Bruno and Pasqualotto
  ([arXiv:2608.06367](https://arxiv.org/abs/2608.06367)) and Guerra–Kristensen (2022): symmetry can
  force quasiconvexity, the background of Conjecture 1.
- Conti, Dolzmann and Dondl ([arXiv:2610.31886](https://arxiv.org/abs/2610.31886), October 2026): a
  frame-indifferent example on `ℝ^{3×3}`.
- Pedregal's claimed proof for `2 × 2` (arXiv:1905.06571, [audited here](../Pedregal/README.md)):
  the paper does not cite it; if Cassese's `2 × 3` example is correct, it contradicts the claim of
  Pedregal's versions 1–2 for two-component maps in dimension three and more.

### Formalizations

- The author formalized Theorem 1.2 and Theorem 1.3 at `p = 4` in Lean
  ([MorreyTwoComponentsLean](https://github.com/Gabriele-Cassese/MorreyTwoComponentsLean)), with an
  AI system (the paper's declaration names ChatGPT 5.6 Sol), released without a license. It was not
  consulted. This formalization covers the whole paper, including the results that the author's
  does not: Theorems 1.4 and 1.5, Corollaries 1.6 and 5.2–5.4, Sections 6 and 7, and the cited
  results the paper's proofs use.
- Conti, Dolzmann and Dondl's Lean code for their `3 × 3` example
  ([sergioconti/so3-r1c-and-not-qc](https://github.com/sergioconti/so3-r1c-and-not-qc)) shares the
  subject, not the results.

## 11. What's next

### Open directions (from the paper and the formalization)

- **`2 × 2`.** The homogeneous problem in `2 × 2` is open; the paper expects a positive answer, and
  notes that it would imply Iwaniec's conjecture, so a proof must use features of the plane (§8.1).
- **Quantitative `m₀`.** The proof gives no value of `m₀(p)` (and `n₀ ≈ 10^{80}` at `p = 3`); the
  paper expects `m₀(p) ≤ 4` and conjectures `3`.
- **`2 × 3` and `3 × 2` for every `p`.** Claimed for `p ∈ (3.6, 5.15)` (Remark 5.4), proved here near
  `4`.
- **`d₀ = 588`** in Theorem 1.4 is not optimal (numerics suggest `260`; `d = 3` is expected).
- **Conjecture 1**: isotropic `p`-homogeneous rank-one convex integrands are quasiconvex at `0`.

### Simpler proofs

- The constant of Section 5 is `√2`, not `2`: keep the column vector of `R` (E5).
- Proposition 4.3 does not need Dacorogna's formula: `g ≤ f`, `g(0) = f(0)` and `g` quasiconvex at
  `0` give `∫ f(∇φ) ≥ ∫ g(∇φ) ≥ g(0) = f(0)` directly.
- Theorem 1.3 (a) does not need `q₃(∇u) ∈ L¹`: the integral over the unit ball is already negative.
- Corollary 7.2: `f_{4,√2,C₀} − 𝒫 = (30|P|² − |Q|²)²`, which gives the bound `2U ≥ |y|⁴ − 130|x|⁴` in one
  line, and the zig-zag concavity of `U` has an explicit sum-of-squares certificate.
- Burkholder's inequality as the paper uses it never needs the separability of the Hilbert space.

### The formalization

- The remaining hypotheses are the frontier: UMD theory (extrapolation, `L^p` and Schatten classes),
  decoupling, non-commutative Khintchine, transference and Dragičević's bound. Dragičević's
  `‖𝓑²‖_{L⁴} ≥ 21/5` could be replaced by explicit truncated test functions (the value `21/5` is the
  multiplier on `r^{−1/2}e^{4iθ}`); the margin in Corollary 7.2 is only 1.6 %.
- Burkholder's inequality, Dacorogna's formula and the Fourier facts on the torus built here are
  general and could go to Mathlib.
