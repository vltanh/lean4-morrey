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
| Theorem 1.2 | `theorem1_2` ⭐ | every `p > 1`: a `p`-homogeneous, rank-one convex, nowhere quasiconvex integrand on `ℝ^{2×m}` for `m ≥ m₀(p)` | nothing (by the paper's Remark 4.5) |
| Theorem 1.2 | `theorem1_2_umd` | the same, by the paper's main proof | Pisier, Yaroslavtsev, HNVW extrapolation |
| Theorem 1.3 | `theorem1_3_a`, `theorem1_3_b` ⭐ | a quartic polynomial on `ℝ^{2×3}`, rank-one convex and nowhere quasiconvex; and for `p` near `4` | nothing |
| Corollary 5.3 | `corollary5_3` ⭐ | its transpose, on `ℝ^{3×2}` | nothing |
| lines 251–254 | `morrey_landscape` ⭐ | with Šverák's theorem: Morrey's problem fails in every `d × m` with `d, m ≥ 2` except `2 × 2` | nothing |
| lines 254–256 | `homMorrey_landscape` ⭐ | at `p = 4` the homogeneous problem fails in every such size except `2 × 2` | nothing |
| Theorem 1.4 | `theorem1_4_four` ⭐ | at `p = 4`: a conjugation- and transposition-invariant example on `ℝ^{d×d}` for every `d ≥ 588` | nothing |
| Theorem 1.4 | `theorem1_4` ⭐ | every `p > 1`: such an example for `d ≥ d₀(p)` | HNVW extrapolation, Randrianantoanina, Cox–Veraar, Pisier–Xu, Kahane–Khintchine |
| Theorem 1.5 | `theorem1_5` ⭐ | every `p ≠ 2`: an example on `ℝ^{4×2}` | transference, Dragičević |
| Corollary 1.6 | `corollary1_6` ⭐ | a nonnegative 1-homogeneous rank-one convex integrand on `ℝ^{4×4}`, not quasiconvex at a matrix of rank two | transference, Dragičević |

⭐ in [`Challenge.lean`](../../palomar/Cassese/Challenge.lean), checked by Comparator against
[`Solution.lean`](../../palomar/Cassese/Solution.lean).

The proofs follow the paper's arguments. One departure replaces a whole argument, with the user's
approval: Theorem 1.2 is proved unconditionally by the route the paper itself announces in
Remark 4.5 (Burkholder's scalar functions instead of UMD constants); the paper's main proof is
formalized too, as `theorem1_2_umd`, conditional on the UMD results. The other departures are local
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
| Burkholder's inequality, Hilbert-valued (Theorem 2.3 (1)) | Lemma 5.1, Theorem 1.3 (b), Prop 7.1 | Burkholder 1984; Osękowski 2012, Thm 3.5 | `External.Burkholder.inequality` |
| Burkholder's square function inequality (Theorem 2.3 (2)) | Prop 6.5 | Osękowski 2012, Thm 8.6 | `External.Burkholder.squareFunction` |
| Burkholder's function `u₆` and `u_q`, (13), (14) | Prop 4.2, Theorem 1.2 by Remark 4.5 | Burkholder 1988 | `External.Burkholder.scalarFunction_holds`, `scalarFunctionQ_holds` |
| a rank-one convex function is locally Lipschitz (Lemma 2.1) | the envelopes, Cor 1.6 | Rindler 2018, Lemma 5.6 | `External.Rindler.lemma5_6` |
| quasiconvexity: rank-one convexity, domains, periodic test maps (Lemma 2.2) | Prop 2.3, the thresholds, the lifting | Rindler, Props 5.1, 5.3; Dacorogna 2008, Props 5.11, 5.13 | `External.Rindler.*` |
| Dacorogna's formula for the quasiconvex envelope (Prop 2.2) | line 559, Prop 2.3, Prop 4.3 | Kinderlehrer–Pedregal 1991; Dacorogna 2008, Thm 6.9 | `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| rank-one affine functions are affine in the minors | Prop 5.1 | Dacorogna 2008, Thm 5.20 | `External.Dacorogna.rankOneAffineMinors_holds` |
| rank-one convex quadratic forms are quasiconvex | Prop 5.1 | Dacorogna 2008, Thm 5.25 (i) | `External.Dacorogna.quadraticForm_quasiconvex` |
| a smoothing that keeps the failure of quasiconvexity | Cor 5.2 | Kristensen 1999, Prop. 2 | `External.Kristensen.smoothing_holds` |
| separately convex functions are locally Lipschitz | Lemma 2.1, Prop 2.2 | Dacorogna 2008, Thm 2.31 | `Matrix.locallyLipschitz_of_convexOn_single` |
| Fourier coefficients of Lipschitz periodic maps, Fejér means | Prop 7.2 | standard | `Morrey/Common/Basic/Analysis/Fourier/TorusLipschitz.lean` |

The Schatten-norm facts of Section 1.5 (with the triangle inequality and Weyl's monotonicity), the
Bernstein–Doetsch theorem (midpoint convex and continuous implies convex, used without citation)
and the uniform convexity of `|·|^p` (used without citation in (29)) are proved in the paper's
library.

### Assumed: named hypotheses

Each is a hypothesis of exactly the statements whose proofs use it, under its source's name.

| Hypothesis | Source | Used by |
| --- | --- | --- |
| `HNVWExtrapolation` | Hytönen–van Neerven–Veraar–Weis I, Thm 4.2.7 | `theorem1_2_umd`, Props 6.2, 6.5, `theorem1_4` |
| `PisierLpUMD` | Pisier 2016, Cor 5.22 | `theorem1_2_umd` |
| `YaroslavtsevComplexUMD` | Yaroslavtsev 2018, Lemma 3.2 | `theorem1_2_umd` |
| `RandrianantoaninaSchattenUMD` | Randrianantoanina 2002, Cor 4.5 | Props 6.2, 6.5, `theorem1_4` |
| `CoxVeraarDecoupling` | Cox–Veraar 2007 | Props 6.2, 6.5, `theorem1_4` |
| `PisierXuKhintchine` | Pisier–Xu 2003, Thm 6.1 | eq (31), Props 6.2, 6.5, `theorem1_4` |
| `KahaneKhintchine` | HNVW II, Thm 6.2.4 | eq (31), Props 6.2, 6.5, `theorem1_4` |
| `HNVWTransference` | HNVW I, Cor 5.7.6 | Prop 7.2 (lower bound), Thm 7.1, `theorem1_5`, `corollary1_6` |
| `DragicevicLowerBound`, `DragicevicL4Bound` | Dragičević 2011, Thm 1.1 | Thm 7.1, Cor 7.2, `theorem1_5`, `corollary1_6` |

ASSUMED-TBD (the fix round may split Kahane–Khintchine and build Burkholder's sharpness).

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
| E4 | 2031–2046 | Theorem 1.3 (b): "continuity of the estimates" in `p` needs the constant `Λ` of Lemma 5.1 (1) uniform for `p` near `4`, and the cut-off fixed before `p` varies | a uniform quantitative Lemma 5.1 (1) (`lemma5_1_part1_quant`) |
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
| E23 | 1047–1053 | the "straightforward limiting argument" from Schwartz test maps to Definition 2.1 is not given | proved (`twoByM_ratio_le_qcThreshold`) |
| E24 | 1891–1895 | Lemma 5.1 (1): "by homogeneity and Young's inequality" needs a Lipschitz bound on `g`, which is only continuous | uniform continuity on a compact set and homogeneity |
| E25 | 1849, 1956, 1991 | Lemma 5.1 (2) is stated for `δ ∈ (0, 1)` and used at `δ = 1` | covered |
| E26 | Remark 4.5 | gives no constant: `K = 2(q − 1)^{p+1}/(p − 1)`, and (13) for `u_q` needs `q ≥ 2` | supplied (`q = p + 3`) |
| E27 | 2425–2437, 2477–2479 | Remark 6.3 and Proposition 6.5 at `q = ∞` need Kahane–Khintchine constants polynomial in `q`; Proposition 6.4 gives none and no source is named | the hypercontractive bound, assumed |
| E28 | 2807–2821, 2211–2216 | Proposition 7.2 "≤" argues with smooth maps, Lemma 2.2 tests with Lipschitz periodic maps; the density step is not stated | Fejér means |
| E29 | 2489–2520 | Corollary 6.1: the reduction from periodic to compactly supported Hessian test maps is not stated, and "the calculation of Proposition 6.1" does not carry over (the skew part of `JD²φ` has two distinct doubled singular values) | supplied (rank `≤ 4`, `S₂` against `S₄`) |
| E30 | 2624–2633 | Corollary 6.3's lower bound cites the sharpness of `p* − 1` only through "see also [Cassese 2025]" | E30-TBD |

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
  bounded (`IsIntegrand`). `W^{1,∞}_0([0, 1]^m)` maps are Lipschitz maps vanishing outside the open
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
  `∃ K₀ ∀ K ≥ K₀ ∃ δ₀ > 0 ∀ δ ∈ (0, δ₀)`, `Λ = K/δ`. Proposition 6.5 at `q = ∞`: READING-TBD.
  Corollary 6.1: READING-TBD.
- **Theorem 1.4** (general `p`) fixes `q = 4` among the paper's `q ∈ (2, ∞)`.

## 7. Departures from the paper's proofs

DEPARTURES-TBD

## 8. What each result depends on

DEPTABLE-TBD

## 9. Not formalized

- Claims stated without proof and used by no argument: the `p > 2` variant of Corollary 1.6
  (2956–2966); Remark 6.1 (sharpness up to `d^{1/(2q)}`); the versions for `Sym₀`/`Skew_tr` and
  `h_{p,q,C}` (2521–2549); "`g(AJ)` gives another Hessian counterexample" (2691–2692); Remarks 4.1–4.4,
  6.4, 6.5, 7.1, 7.2; taking `p = 4` in the proof of Theorem 7.1 (2882–2884).
- Context only: Kirchheim–Kristensen's theorem (Theorem 1.1) and its consequence at lines 186–188,
  Grabovsky's examples (196–199), Iwaniec's `C^{rc} ≤ p* − 1` (763–765), Remark 2.2.
- Conjecture 1 is stated as a definition (`Conjecture1`), not proved.

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
