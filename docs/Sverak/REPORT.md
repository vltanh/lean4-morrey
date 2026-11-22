# Šverák (1992) in Lean: audit report

V. Šverák, *Rank-one convexity does not imply quasiconvexity*, Proc. Roy. Soc. Edinburgh Sect. A
120 (1992), 185–189. Formalized in Lean 4 with Mathlib (`v4.36.0-rc2`) from the published article,
on 21–22 November 2026, in a repository that also formalizes two later papers on Morrey's problem
([overview](../../README.md)). The paper has no TeX source; the labels `sv-…` used in the code and in
[`paper_routes.tsv`](paper_routes.tsv) are ours.

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

The paper proves that rank-one convexity does not imply quasiconvexity for maps with at least three
components. Its integrand is an explicit quartic polynomial on `3 × 2` matrices:

`F(X) = f(PX) + ε|X|² + ε|X|⁴ + k|X − PX|²`,

where `P` is the orthogonal projection onto the subspace `L = {(r 0; 0 s; t t)}` and
`f(r 0; 0 s; t t) = −rst`.

Every result of the paper is formalized and proved, and nothing is assumed:

- Lemma 1: periodic test maps suffice;
- the structure of `L` and the computation (4);
- Lemma 2: the extension of `f` to a rank-one convex `F`;
- the Theorem, the Remark and the Corollary.

Every proof follows the paper's argument (Section 7). No statement of the paper is false. Its gaps
are steps it leaves to the reader (Section 3); the formalization supplies each along the paper's
lines. The largest is the limit in the proof of Lemma 1, which the paper calls "easily seen".

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem | [`theorem_main`](../../Morrey/Sverak/Theorem.lean#L187) ⭐ | there are `ε > 0` and `k > 0` such that `F` is rank-one convex and not quasiconvex |
| Corollary | [`corollary`](../../Morrey/Sverak/Theorem.lean#L341) ⭐ | for `m ≥ 3` and `n ≥ 2`, `X ↦ F(TX)` on `M^{m×n}` is rank-one convex and not quasiconvex |
| Remark | [`remark_polynomial`](../../Morrey/Sverak/Theorem.lean#L360) ⭐ | `F` is a polynomial of degree four (for `ε ≠ 0`) |
| Lemma 1 | [`lemma1`](../../Morrey/Sverak/Lemma1.lean#L717) | a continuous `f` is quasiconvex if and only if `∫_{[0,1]^n} f(A + Du) ≥ f(A)` for every smooth `ℤ^n`-periodic `u` |
| Lemma 2 | [`lemma2`](../../Morrey/Sverak/Lemma2.lean#L504) | for each `ε > 0` there is `k > 0` such that `F` is rank-one convex |
| (4) | [`equation4`](../../Morrey/Sverak/Construction.lean#L177) | `∫_{[0,1]²} f(Dw) = −∫ (cos 2πx₁)² (cos 2πx₂)² < 0 = f(0)` |

⭐ in [`Challenge.lean`](../../palomar/Sverak/Challenge.lean), checked by Comparator against
[`Solution.lean`](../../palomar/Sverak/Solution.lean).

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

None. The paper's proofs use no result from the literature.

### Cited results

- Lemma 1 "can be found for example in [5] or [8]" (Ball, Currie and Olver 1981; Kohn 1991) and
  "also follows from the result of Morrey". The paper sketches a proof, and the formalization proves
  Lemma 1 by that sketch.
- "The class of quasiconvex functions is independent of `Ω` (see [3], [10])." The paper relies on
  it silently when it proves Lemma 1 and the Theorem on the unit cube. The formalization states
  quasiconvexity on a given domain and proves the Theorem and the Corollary on the unit cube, so it
  does not need the cited fact (Section 6).
- The introduction's results ((iii) ⇒ (ii) ⇒ (i), quadratic forms, `2 × 2` quadratic forms,
  Morrey's semicontinuity theorem, Ball's extended-valued counterexample) are context; no proof uses
  them.

### Standard facts used without citation

All are proved, from Mathlib or in the library:

- the trigonometric identity behind (4), and Fubini on the square;
- a function whose second derivative is nonnegative is convex;
- Bolzano–Weierstrass in `M^{3×2} × M^{3×2}`;
- the rank of a matrix through its minors;
- the existence of the cut-off `η_ε` of Lemma 1 (Section 6), by mollification: Mathlib's
  convolution with a normed bump function, and the lemmas of the shared module
  [`Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean`](../../Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean) (smoothness, values in `[0, 1]`,
  locality, and the derivative bound by the Lipschitz constant,
  [`ContDiffBump.norm_fderiv_normed_convolution_le`](../../Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean#L334));
- periodic averages and dominated convergence (in the limit of Lemma 1);
- the chain rule for `T` in the Corollary.

No package beyond Mathlib is used.

### Does the paper use each cited result correctly?

Yes. Lemma 1 is the standard characterization, and the sketch proves it for continuous `f`, as
stated.

## 3. Errors and gaps in the paper

No statement is false. The items below are steps the paper leaves to the reader, a typo, and
imprecisions; the formalization supplies each.

### E1. Lemma 1: the limit "is easily seen"

The proof of the "only if" part ends: "It is easily seen that for `ε → 0` the limit of the
integrals on the right-hand side of (2) is `∫_{[0,1]^n} f(Du(x)) dx`." No argument is given. It
needs three things:

- a uniform bound on `Du_ε`, from `|Dη_ε| = O(1/ε)`;
- the convergence of `f(Du_ε(x))` to `f(Du(x/ε²))` off a boundary layer of measure `O(ε)`;
- the averaging `∫_{[0,1]^n} G(x/ε²) dx → ∫_{[0,1]^n} G` for continuous periodic `G`.

The formalization proves the limit as `ε → 0⁺`, as the paper states it ([`lemma1_limit`](../../Morrey/Sverak/Lemma1.lean#L541)): by
dominated convergence, with the averaging lemma for every real scale `N = 1/ε² → ∞` (the
`⌊N⌋^n` whole cells, and a boundary layer of relative measure `1 − (⌊N⌋/N)^n`). The "only if"
part of Lemma 1 then follows from (2) by passing to the limit, as in the paper.

### E2. Lemma 1: `u_ε : B → ℝ^m`

`B` is not defined. The map is meant on `ℝ^n` (or on `[0,1]^n`, extended by `0`), and it is
supported in `(0,1)^n`.

### E3. Lemma 1 is proved only at `A = 0`

The proof writes `f(0) ≤ ∫ f(Du_ε)`, the case `A = 0`. The general case follows by applying it to
`X ↦ f(A + X)`. The formalization proves it for every `A`.

### E4. Implicit steps in Lemma 2

- "The set `𝒦` is clearly a compact subset of `M^{3×2} × M^{3×2}`." The rank-one matrices do not
  form a closed set (`0` is a limit of them); within `𝒦` they do, because `|Y| = 1` excludes
  `Y = 0` and `rank Y ≤ 1` is closed.
- "It follows immediately that `Ȳ = PȲ`." This needs the first term of `g` to be bounded below on
  `𝒦`, so that `k|Y⁽ᵏ⁾ − PY⁽ᵏ⁾|²` stays bounded as `k → ∞`.
- The conclusion passes from `|Y| = 1` to every rank-one `Y`, by the homogeneity of the second
  derivative in `Y`, and applies the bound at every point `A + tY` of a line.

### E5. The Corollary: "`T` maps rank-one lines to rank-one lines"

Or to points: when `m ≥ 4` or `n ≥ 3`, a rank-one `B` can have `TB = 0` (`B = e₄e₁ᵀ`), and then
`F̃` is constant on the line. The proof of rank-one convexity covers this case. The proof also uses
Lemma 1 without naming it, the continuity of `F̃`, and Fubini, to integrate a function of
`(x₁, x₂)` over `(0,1)^n`.

### E6. Numbering

The displayed equations are numbered (1)–(8), (10), (11): there is no (9), and the unnumbered (*)
sits between (7) and (8). This is cosmetic, and as transcribed from the article.

## 4. Missing hypotheses

None.

## 5. Redundant hypotheses

None. The Remark needs `ε ≠ 0` (for `ε = 0`, `F` has degree three), which the Theorem's `ε > 0`
provides.

## 6. How the formalization reads the paper

- **Matrices and gradients.** `M^{m×n}` is `Matrix (Fin m) (Fin n) ℝ`, `ℝ^n` is `Fin n → ℝ`, and
  the gradient of `φ : ℝ^n → ℝ^m` is [`Sverak.jac`](../../palomar/Sverak/Challenge.lean#L46), whose rows are the
  derivatives of the components. `|X|²` is the sum of the squares of the entries
  ([`frobSq`](../../palomar/Sverak/Challenge.lean#L73)).
- **Rank-one convexity** ([`RankOneConvex`](../../palomar/Sverak/Challenge.lean#L52)) is the paper's (i), word for word.
- **Quasiconvexity** ([`QuasiconvexOn`](../../palomar/Sverak/Challenge.lean#L65)) is the paper's (ii) on a given set `Ω`:
  smooth means `C^∞`, and "compactly supported in `Ω`" means a compact support contained in `Ω`. The
  definition also asks the integral `∫_Ω f(A + Dφ)` to exist. For a continuous `f` and a bounded
  `Ω` this is automatic, and it makes a failure of quasiconvexity a statement about a genuine
  integral (Lean's integral of a non-integrable function is `0`).
- **The domain.** The paper says that the class of quasiconvex functions does not depend on `Ω`, and
  its proofs use the unit cube. The Theorem and the Corollary are stated and proved on the open unit
  cube `(0,1)^n`. Failure on the cube is failure of quasiconvexity in the paper's sense whatever the
  domain, by the cited independence, which is not formalized for the paper's smooth test maps
  (Section 11).
- **Lemma 1** is stated for continuous `f`, as in the paper, and for every matrix `A` (E3).
  "Periodic" is periodic with respect to `ℤ^n`.
- **`P` and `f`.** `P` is given by its formula, and [`sverakP_orth`](../../Morrey/Sverak/Construction.lean#L50) proves that it is the orthogonal
  projection onto `L`. The function `f` of (3), defined on `L`, is used through `X ↦ f(PX)`
  ([`sverakf`](../../palomar/Sverak/Challenge.lean#L81)).
- **The cut-off of Lemma 1.** The paper takes a smooth `η_ε`, equal to `1` on `[ε, 1 − ε]^n`,
  vanishing in a neighbourhood of the boundary of `[0, 1]^n`, with `|Dη_ε| ≤ 2/ε`, and does not
  construct it. The formalization builds one with these properties ([`l1_eta`](../../Morrey/Sverak/Lemma1.lean#L137), for `ε = 1/K`):
  the mollification, at radius `ε/16`, of the Lipschitz profile
  `min(1, max(0, (d − ε/8)·8/(5ε)))`, with `d` the distance to the boundary of the cube for the
  sup norm. It equals `1` on `[ε, 1 − ε]^n` ([`l1_eta_eq_one`](../../Morrey/Sverak/Lemma1.lean#L156)), vanishes off
  `(ε/16, 1 − ε/16)^n` ([`l1_eta_eq_zero`](../../Morrey/Sverak/Lemma1.lean#L173)), and `‖Dη_ε‖ ≤ 8/(5ε) ≤ 2/ε`
  ([`l1_eta_fderiv_bound`](../../Morrey/Sverak/Lemma1.lean#L191)). The norm there is the operator norm for the sup norm on `ℝ^n`,
  the `ℓ¹` norm of the gradient, which dominates the Euclidean `|Dη_ε|`. The proof of the limit
  uses this bound.
- **Constants the paper leaves open.** The bound in Lemma 2 holds with `c = 6`, and the claim of its
  proof holds with `k₀ = n + 1` for some `n ∈ ℕ`, the paper's "`k = 1, 2, …`".
- **The Corollary.** `T` is the upper left `3 × 2` block
  ([`topLeft`](../../palomar/Sverak/Challenge.lean#L89)), and `ε`, `k` are chosen before `m` and `n`, as "the function
  from the theorem above" requires.
- **The Remark.** "A polynomial of degree four" is `MvPolynomial.totalDegree P = 4`, for `ε ≠ 0`.

## 7. Departures from the paper's proofs

None. Every proof follows the paper's argument: the same intermediate claims, constructions and
cited steps, checked by the route check with no recorded difference
([`route_differences.tsv`](route_differences.tsv) is empty). Where the paper leaves a
step to the reader, the formalization supplies it along the paper's lines (Section 3); the objects
it takes for granted, such as the cut-off of Lemma 1, are built with the properties it states; and
the constants it leaves open are fixed as in Section 6.

## 8. What each result depends on

From [`scripts/Audit.lean`](../../scripts/Audit.lean), which also checks every declaration of the
library (only the three standard axioms). No result uses a result from prior work: the paper's
proofs cite none.

| Result | Lean | Results from prior work used | Axioms |
| --- | --- | --- | --- |
| Lemma 1 | [`Sverak.lemma1`](../../Morrey/Sverak/Lemma1.lean#L717) | – | propext, Classical.choice, Quot.sound |
| Lemma 1 (limit) | [`Sverak.lemma1_limit`](../../Morrey/Sverak/Lemma1.lean#L541) | – | propext, Classical.choice, Quot.sound |
| Lemma 1 (witness) | [`Sverak.lemma1_witness`](../../Morrey/Sverak/Lemma1.lean#L636) | – | propext, Classical.choice, Quot.sound |
| rank-one directions of L | [`Sverak.rank_ofRST_eq_one`](../../Morrey/Sverak/Construction.lean#L75) | – | propext, Classical.choice, Quot.sound |
| f affine on rank-one lines of L | [`Sverak.sverakf_affine_of_rankOne`](../../Morrey/Sverak/Construction.lean#L112) | – | propext, Classical.choice, Quot.sound |
| (4) | [`Sverak.equation4`](../../Morrey/Sverak/Construction.lean#L177) | – | propext, Classical.choice, Quot.sound |
| (6) | [`Sverak.equation6`](../../Morrey/Sverak/Lemma2.lean#L162) | – | propext, Classical.choice, Quot.sound |
| (7) | [`Sverak.equation7`](../../Morrey/Sverak/Lemma2.lean#L233) | – | propext, Classical.choice, Quot.sound |
| (*) | [`Sverak.equation_star`](../../Morrey/Sverak/Lemma2.lean#L249) | – | propext, Classical.choice, Quot.sound |
| (8) | [`Sverak.equation8`](../../Morrey/Sverak/Lemma2.lean#L312) | – | propext, Classical.choice, Quot.sound |
| Lemma 2 | [`Sverak.lemma2`](../../Morrey/Sverak/Lemma2.lean#L504) | – | propext, Classical.choice, Quot.sound |
| (10) | [`Sverak.equation10`](../../Morrey/Sverak/Theorem.lean#L111) | – | propext, Classical.choice, Quot.sound |
| (11) | [`Sverak.equation11`](../../Morrey/Sverak/Theorem.lean#L160) | – | propext, Classical.choice, Quot.sound |
| Theorem | [`Sverak.theorem_main`](../../Morrey/Sverak/Theorem.lean#L187) | – | propext, Classical.choice, Quot.sound |
| Remark | [`Sverak.remark_polynomial`](../../Morrey/Sverak/Theorem.lean#L360) | – | propext, Classical.choice, Quot.sound |
| Corollary | [`Sverak.corollary`](../../Morrey/Sverak/Theorem.lean#L341) | – | propext, Classical.choice, Quot.sound |

## 9. Not formalized

- The independence of quasiconvexity from the domain (cited from [3] and [10]), for the paper's
  smooth test maps; the Theorem and the Corollary are proved on the unit cube (Sections 6 and 11).
- The introduction's survey: polyconvexity implies quasiconvexity, the quadratic case, Morrey's
  semicontinuity theorem.

## 10. The paper in the literature

### Before the paper

- C. B. Morrey (1952) introduced quasiconvexity, proved that it characterizes the weak-∗ lower
  semicontinuity of `∫ f(∇u)` on `W^{1,∞}`, and conjectured that rank-one convexity does not imply
  it for `m ≥ 2` components and `n ≥ 2` variables; his 1966 book is less sure.
- J. M. Ball (1977) introduced polyconvexity, which implies quasiconvexity, and asked the question
  again in *Does rank-one convexity imply quasiconvexity?* (1987). For quadratic forms
  rank-one convexity implies quasiconvexity, and on `2 × 2` matrices every quasiconvex quadratic
  form is polyconvex (Terpstra 1938, Serre 1983); among general functions on `2 × 2` matrices,
  quasiconvexity does not imply polyconvexity (the paper's [2] and [14]).
- Ball (1990, *Sets of gradients with no rank-one connections*) showed that rank-one convexity does
  not imply quasiconvexity when the integrand may be discontinuous and take the value `+∞`, for
  `n ≥ 3, m ≥ 3` or `n ≥ 2, m ≥ 4`.
- The paper says that its example "is reminiscent of" one of Tartar's in compensated compactness,
  and relates it to Example 3.5 of Ball, Currie and Olver (1981).

### Since the paper

- The paper settled Morrey's problem for `m ≥ 3` components. Its example became the reference
  counterexample, and its mechanism — a periodic map whose gradients lie in a subspace with few
  rank-one directions — became a test for the two-component case.
- That mechanism cannot work in `2 × 2`. Analogues of the example's gradient measure in `2 × 2`
  turned out to be laminates (Pedregal 1996, Pedregal–Šverák 1998, Bandeira–Ornelas 2011), and
  Sebestyén and Székelyhidi (J. Convex Anal. 2017) proved it for the whole class: the gradient
  measure of a sum of three sawtooth waves along pairwise non-collinear directions in `2 × 2` is a
  laminate. Nor can the example be transposed: quasiconvexity is not invariant under transposition
  (Kružík 1999), and Müller (2000; announced in his 1998 lecture notes, Section 4.7) showed that
  Šverák's `F`, for `ε` small and `k ≥ k(ε)`, becomes quasiconvex after transposition.
- Kristensen (1999) proved that quasiconvexity is equivalent to a local condition among smooth
  integrands only if it equals rank-one convexity; with Šverák's example, it is not local for three
  or more components.
- Grabovsky (ARMA 2018) found a second family of rank-one convex, non-quasiconvex integrands, from
  the theory of `G`-closures; the smallest is on `ℝ^{8×2}`.
- In 2026 three preprints went further, two of them along Šverák's lines.
  - G. Cassese ([arXiv:2608.03488](https://arxiv.org/abs/2608.03488)) claims the two-component case
    outside `2 × 2`, so that, with Šverák's theorem, only `2 × 2` would remain open. The paper is
    formalized in this repository ([`docs/Cassese/`](../Cassese/README.md)), and the combined
    statement is proved there from this paper's theorem ([`CasseseChallenge.morrey_landscape`](../../palomar/Cassese/Challenge.lean#L296)). Its `2 × 3`
    quartic (Theorem 1.3) follows Šverák's architecture: a polynomial rank-one convex on a subspace
    with few rank-one directions, extended by a projection and a penalty (a homogeneous analogue of
    `k|X − PX|²`), and a witness with gradients in the subspace. Its transpose on `ℝ^{3×2}`
    (Corollary 5.3, sketched) stays non-quasiconvex, and gives a homogeneous proof of Šverák's
    theorem. Cassese answers Kirchheim and Kristensen's homogeneous problem negatively, which
    Šverák's example cannot do, since its quartic part at infinity, `ε|X|⁴`, is convex; his
    Remark 5.2 says, without proof, that his extension lemma turns Šverák's example into a
    positively 3-homogeneous one. Both examples are quartic, the least possible degree: a
    polynomial of degree at most three that is rank-one convex at `0` is quasiconvex (Cassese,
    Proposition 5.1, "folklore"). Cassese restates Šverák's example as failing quasiconvexity at
    `0`, which [Cassese/Sverak.lean](../../Morrey/Cassese/Sverak.lean) proves in Cassese's definitions.
  - Agazzi, Bruno, Guerra and Pasqualotto ([arXiv:2608.12298](https://arxiv.org/abs/2608.12298))
    gave a counterexample on `ℝ^{2×4}`, from Grabovsky's integrand, and one on symmetric `3 × 3`
    matrices by modifying Šverák's example.
  - Conti, Dolzmann and Dondl ([arXiv:2610.31886](https://arxiv.org/abs/2610.31886)) gave a
    frame-indifferent example on `ℝ^{3×3}`, whose failure of quasiconvexity uses Šverák's plane `L`
    and test map.

### Formalizations

- Conti, Dolzmann and Dondl's Lean formalization of their `3 × 3` example
  ([sergioconti/so3-r1c-and-not-qc](https://github.com/sergioconti/so3-r1c-and-not-qc), October
  2026) includes adaptations of parts of this paper's argument to `ℝ³`: of the test map `w`
  (`φ(x) = (sin x₁, sin x₂, −sin(x₁ + x₂))`), of its gradients in `L` and of the integral (4), and
  the "only if" half of Lemma 1. It does not have Lemma 2, the Theorem or the Corollary. No
  formalization of the whole paper was found.
- Cassese formalized parts of his own paper in Lean.
- The proofs here were written without consulting either, and nothing from them was used. Parts of
  both were displayed on 21 and 22 November 2026 by searches for earlier formalizations and for the
  literature, and by checks of the documents
  ([`docs/Cassese/CREDITS.md`](../Cassese/CREDITS.md) says which).

## 11. What's next

Plans for follow-up papers are kept in `NEXT.md`, which is not published.

### Open directions

- **`2 × 2`.** Morrey's problem for two components in the plane is open. Šverák's mechanism cannot
  settle it (Sebestyén–Székelyhidi), and the claimed proof formalized in this repository fails
  ([`docs/Pedregal/REPORT.md`](../Pedregal/REPORT.md), E13).
- **Homogeneous examples.** Šverák's `F` is not homogeneous. Cassese's Corollary 5.3 gives a
  homogeneous quartic on `ℝ^{3×2}` that is rank-one convex and nowhere quasiconvex; whether a
  `p`-homogeneous example exists on `ℝ^{3×2}` for every `p > 1` is open (Cassese, Remark 5.4).
- **Symmetric examples.** Conti, Dolzmann and Dondl's frame-indifferent example on `ℝ^{3×3}` adds
  a symmetry constraint to a Šverák-type construction; Cassese's Conjecture 1 asks whether isotropy
  forces quasiconvexity at `0` for homogeneous integrands.

### Simpler proofs

- **An explicit `k(ε)` in Lemma 2.** The compactness argument gives no value of `k`; a
  quantitative form of "`f` is linear on the rank-one lines of `L`" gives one. For rank-one `R`,
  let `R_L` be the orthogonal projection of `PR` on a suitable one of the three rank-one lines of
  `L`; the bound `|PR − R_L| ≤ κ|R − PR|` holds with `κ = 1 + 1/√2`, the constant used below.
  Since `D²f(PA)[R_L, R_L] = 0` and `‖D²f(PA)‖ ≤ √(2/3)|PA|`, polarization gives
  `|D²f(PA)[PY, PY]| ≤ 2√(2/3)κ|A||Y||Y − PY|` for rank-one `Y`, and the arithmetic–geometric
  mean inequality against `4ε|A|²|Y|² + 2k|Y − PY|²` makes `F` rank-one convex for
  `k ≥ κ²/(12ε) = (3 + 2√2)/(24ε) ≈ 0.25/ε`. With `∫ f(Dw) = −1/4`, `∫|Dw|² = 2` and
  `∫|Dw|⁴ = 19/4`, every `ε < 1/27` keeps `∫ F(Dw) < 0`; so
  `F(X) = −rst(PX) + (|X|² + |X|⁴)/30 + 13|X − PX|²` is an explicit example. Checked on paper and
  numerically (random rank-one directions), not in Lean.

### The formalization

- **The domain.** The independence of quasiconvexity from the domain is proved, for Lipschitz test
  maps vanishing outside the domain, in the package
  [lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations)
  (`CalculusOfVariations.quasiconvexAtOn_iff`), which Cassese's formalization uses. With
  [`Cassese.not_quasiconvexAt_of_smooth`](../../Morrey/Cassese/Bridges.lean#L98) (a smooth witness on the cube is a Lipschitz one), it would
  give that Šverák's `F` fails quasiconvexity with Lipschitz test maps on every bounded open set;
  that combination is not stated in Lean. Stating the Theorem on every bounded open `Ω` with the
  paper's smooth test maps needs, in addition, the approximation of Lipschitz test maps by smooth
  compactly supported ones.
- **Mollification.** [`Morrey/Common/Basic`](../../Morrey/Common/Basic) holds the mollification lemmas that the cut-off of Lemma 1 uses
  ([`Mollify.lean`](../../Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean), for `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`); they depend
  only on Mathlib.
- Morrey's semicontinuity theorem, which the paper's introduction recalls, is not in Mathlib.
