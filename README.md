# Morrey's problem in Lean

An integrand `f : ℝ^{d×m} → ℝ` is *quasiconvex* if affine maps minimize `∫ f(∇u)` among maps
with the same boundary values: `∫_{(0,1)^m} f(A + ∇φ) ≥ f(A)` for every matrix `A` and every
Lipschitz `φ : (0,1)^m → ℝ^d` vanishing on the boundary. It is *rank-one convex* if it is convex
along every line `t ↦ A + tB` with `rank B = 1`. Morrey (1952) showed that quasiconvexity is the
condition under which `∫ f(∇u)` is weakly-∗ lower semicontinuous, and that it implies rank-one
convexity; he asked whether the converse holds. This is *Morrey's problem*. Here `d` is the number
of components of `u` and `m` the number of variables.

This repository formalizes, in Lean 4 with Mathlib, three papers on the problem:

- a theorem that settles it for three or more components (Šverák 1992);
- a claimed proof for `2 × 2` matrices (Pedregal);
- a recent preprint on the two-component case in higher dimension and on the homogeneous problem
  (Cassese 2026).

**Every result that Šverák's and Cassese's papers prove is proved here, and nothing is assumed.**
Pedregal's proof fails at a corollary, refuted here; his main theorems, the open `2 × 2` case, are
stated and not proved. Each paper is audited on its own, with its own Challenge, report and Palomar
submission; the papers share general lemmas, the cited results and the checks.

The repository also proves a result of its own on the open `2 × 2` case
([HomogeneousIsotropic](docs/HomogeneousIsotropic/README.md)): for every exponent `p > 0`, an
isotropic, positively `p`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is quasiconvex.
A nonnegative one is even polyconvex if `p ≥ 2`, so the integrands whose quasiconvexity was in
question are those that take negative values. The proof uses one
result from outside, the quasiconvexity of the truncated determinant, claimed in a 2026 preprint
that we audited with a Lean formalization,
[lean4-iwaniec](https://github.com/vltanh/lean4-iwaniec); the proof takes it from there.

## The state of the problem

**Morrey's problem**: does rank-one convexity imply quasiconvexity for `f : ℝ^{d×m} → ℝ`? A
positive answer in `d × m` gives one in every smaller size, and a counterexample gives one in every
larger size (Cassese, Section 1.1), so the answer is decided by a few sizes:

| Size | Answer | Settled by | Here |
| --- | --- | --- | --- |
| `d = 1` or `m = 1` | yes: both notions are convexity | classical | **proved** (Cassese, Section 1: [`Cassese.morreyPositive_of_min_le_one`](Morrey/Cassese/Introduction.lean#L476)) |
| `d ≥ 3`, `m ≥ 2` | no | Šverák (1992), on `ℝ^{3×2}` | **proved** ([Šverák](docs/Sverak/README.md)) |
| `d = 2`, `m ≥ 3` | no, claimed in two 2026 preprints | Cassese, on `ℝ^{2×3}`; Agazzi, Bruno, Guerra and Pasqualotto, on `ℝ^{2×4}` | **proved**: Cassese's quartic and the monotonicity ([Cassese](docs/Cassese/README.md)) |
| `2 × 2` | **open** | Pedregal (2019–2026, preprint) claims yes | the proof fails: its Corollary 7.2 is **refuted** ([Pedregal](docs/Pedregal/README.md)) |

That every size but `2 × 2` fails is proved here as one theorem, from Šverák's example and Cassese's
([`CasseseChallenge.morrey_landscape`](palomar/Cassese/Challenge.lean#L296)).

In `2 × 2` the answer is yes for isotropic, positively `p`-homogeneous integrands, for every
`p > 0`. This is proved here
([HomogeneousIsotropic](docs/HomogeneousIsotropic/README.md), below).

**The homogeneous problem** (Kirchheim–Kristensen 2016): for `p ∈ (1, ∞)`, is every rank-one
convex, `p`-homogeneous `f` (`f(tA) = |t|^p f(A)`) quasiconvex at `0`? For a continuous
homogeneous `f`, failure at `0` is failure at every matrix. All the negative answers below are
claims of Cassese's preprint, and all are proved here.

| Exponent and size | Answer | Source | Here |
| --- | --- | --- | --- |
| `p = 1`, every size | yes, at every matrix of rank at most one | Kirchheim–Kristensen (2016) | stated, not proved (cited by Cassese as context; used by no proof) |
| `p = 1`, `4 × 4`, at a matrix of rank two | no (a nonnegative example) | Cassese, Corollary 1.6 | **proved** |
| every `p > 1`, `2 × m` with `m ≥ m₀(p)` | no | Cassese, Theorem 1.2 | **proved**, by the paper's UMD route, and also by the route of its Remark 4.5 |
| `p = 4`, `2 × 3` (a quartic polynomial) and `3 × 2` (its transpose), hence every size above `2 × 2` | no | Cassese, Theorem 1.3 and Corollary 5.3 (the latter sketched) | **proved** |
| `p` near `4`, `2 × 3` | no | Cassese, Theorem 1.3 | **proved** |
| every `p > 1`, `d × d` with `d ≥ d₀(p)`, conjugation- and transposition-invariant | no | Cassese, Theorem 1.4 | **proved**; at `p = 4` also by the paper's quantitative proof, for every `d ≥ 588` |
| `p ∈ (1, ∞)`, `p ≠ 2`, `4 × 2` | no | Cassese, Theorem 1.5 | **proved** |
| `2 × 3` and `3 × 2` for `p` away from `4`; `p = 2` in `2 × 3`, `3 × 2`, `3 × 3` | open (Cassese expects no) | — | — |
| `2 × 2`, every `p` | open (Cassese expects yes) | — | — |

## The papers

| Paper | Claim | Formalization | Main finding | Documents |
| --- | --- | --- | --- | --- |
| V. Šverák, *Rank-one convexity does not imply quasiconvexity*, Proc. Roy. Soc. Edinburgh 120A (1992) | a quartic polynomial on `ℝ^{3×2}`, rank-one convex and not quasiconvex; hence no for `d ≥ 3`, `m ≥ 2` | **proved**, every step by the paper's argument | no false statement; the steps left to the reader are supplied, chief among them the limit in Lemma 1, "easily seen" | [README](docs/Sverak/README.md), [REPORT](docs/Sverak/REPORT.md), [Challenge](palomar/Sverak/Challenge.lean) |
| P. Pedregal, *Morrey's conjecture: rank-one convexity implies quasi-convexity for two-dimensional, two-component maps*, [arXiv:1905.06571v5](https://arxiv.org/abs/1905.06571v5) (2026) | yes for `2 × 2` | three statements **false**; the main theorems stated, not proved; most of Sections 3–7 proved (below) | the paper's use of Kakutani's theorem needs Corollary 7.2, which an explicit counterexample, checked in Lean, refutes; the claim stays open | [README](docs/Pedregal/README.md), [REPORT](docs/Pedregal/REPORT.md), [Challenge](palomar/Pedregal/Challenge.lean) |
| G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*, [arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3) (2026) | no for `2 × m`, `m ≥ 3`; the homogeneous problem fails at `p = 4` in every size above `2 × 2`, and at every `p > 1` in suitable sizes | every result that the paper proves is **proved**, with nothing assumed (below) | no false statement; gaps, all filled (below) | [README](docs/Cassese/README.md), [REPORT](docs/Cassese/REPORT.md), [Challenge](palomar/Cassese/Challenge.lean) |

The formalization of Pedregal's paper:

- Proposition 7.1, Corollary 7.2 and the summary of Step 2 of the proof are **false**;
- the rest of Sections 3–7, except Claim 7.3, is proved;
- Theorems 1.1 (2) and 1.2 are stated, not proved.

In the formalization of Cassese's paper, every result that the paper proves is **proved**, with
nothing assumed:

- Theorem 1.2 by the paper's UMD route;
- the UMD, Khintchine and Beurling–Ahlfors results behind Theorems 1.2, 1.4, 1.5 and Corollary 1.6
  proved in packages.

Cassese's paper has no false statement; it leaves gaps, all filled:

- the uniformity in `p` behind Theorem 1.3 (b);
- the constant `κ` of Section 5;
- a step of Proposition 2.5 false under the reading of prelaminates the paper needs;
- Proposition 6.6 and Corollary 5.2 without proof.

Each paper's report (`docs/<Paper>/REPORT.md`) gives:

- its findings;
- how the formalization reads it;
- its departures from the paper's proofs;
- what each result depends on;
- its place in the literature;
- what comes next.

Each paper's credits (`CREDITS.md`) say how it was made.

## A result of this repository: homogeneous isotropic integrands in `2 × 2`

[`Morrey/HomogeneousIsotropic/`](Morrey/HomogeneousIsotropic) answers Morrey's problem for a
class of integrands `F` on `ℝ^{2×2}`. Four hypotheses occur:

- **H1**, isotropy: `F(QAR) = F(A)` for all rotations `Q`, `R`;
- **H2**, positive `p`-homogeneity: `F(λA) = λ^p F(A)` for `λ > 0`;
- **H3**, rank-one convexity;
- **N**, the sign condition: `F ≥ 0`.

The Burkholder function `B_p(A) = (|1 − 2/p| |A|² + det A) |A|^{p−2}` (`|A|` the operator norm)
satisfies H1, H2 and H3. Guerra and Kristensen (2022) proved that, for `p ≥ 2`, the integrands
with H1, H2, H3 and N are polyconvex at the multiples of orthogonal matrices, and asked whether
they are polyconvex everywhere (their Question 1.7). They are. Without N, every integrand with
H1, H2 and H3 is quasiconvex (Theorem A). What each range of the exponent needs, and what it
gives (`J = diag(1, −1)`):

| Exponent | Hypotheses | Conclusion | Here |
| --- | --- | --- | --- |
| `0 < p < 1` | H2, H3 | `F = 0` | **proved** |
| `p = 1` | H1, H2, H3 | `F ≥ 0`, and `F` is convex (Dacorogna 1995) | **proved** |
| `1 < p < 2` | H1, H2, H3 | `F` is quasiconvex | **proved** |
| `1 < p < 2` | H1, H2, H3, N | at every matrix `F` has a touching minorant `α B_p(A) + β B_p(JA)` with `α, β ≥ 0` | **proved** |
| `p = 2` | H1, H2, H3 | `F` is polyconvex | **proved** |
| `p > 2` | H1, H2, H3 | `F` is quasiconvex | **proved** |
| `p > 2` | H1, H2, H3, N | `F` is polyconvex, with a polyaffine support at every matrix in closed form | **proved** |
| `p > 2` | H1, H2, and `F < 0` somewhere | `F` is not polyconvex | **proved** |
| every `p > 0` | H1, H2, H3 | `F` is quasiconvex (Theorem A) | **proved** |

The proof uses one result from outside: the quasiconvexity of the truncated determinant, claimed
as Theorem 1 of the preprint of Agazzi et al., [arXiv:2609.28311](https://arxiv.org/abs/2609.28311).
A radial integration over scales (Proposition 6.8 of the paper) turns it into the minorants that the proof needs,
and also into the quasiconvexity of the Burkholder function for every `p > 1`, which the preprint
claims as its Corollary 2. We audited that preprint with a Lean formalization,
[lean4-iwaniec](https://github.com/vltanh/lean4-iwaniec), which proves its results; this
repository requires that package, so the Lean proofs here assume nothing. The argument for
integrands that change sign is due to ChatGPT Chat 6 Extra High.

Integrands that are not isotropic or not homogeneous are not covered. The rest of the proof uses
the definition of rank-one convexity and one-variable calculus:

- [the statements, the proof in outline and the files](docs/HomogeneousIsotropic/README.md);
- the paper, [`docs/HomogeneousIsotropic/paper/main.tex`](docs/HomogeneousIsotropic/paper/main.tex)
  ([PDF](docs/HomogeneousIsotropic/paper/main.pdf));
- the statements of record, [`palomar/HomogeneousIsotropic/Challenge.lean`](palomar/HomogeneousIsotropic/Challenge.lean);
- [how it was made](docs/HomogeneousIsotropic/CREDITS.md).

## How the papers connect

### Before Šverák

Morrey introduced quasiconvexity (1952), proved that it characterizes weak-∗ lower semicontinuity
of `∫ f(∇u)` on `W^{1,∞}`, and conjectured that rank-one convexity does not imply it; his 1966 book
is less sure. J. M. Ball (1977) introduced polyconvexity (convexity in the minors), which implies
quasiconvexity and made the direct method work in nonlinear elasticity; ten years later he asked
the question in print again (*Does rank-one convexity imply quasiconvexity?*, 1987). For quadratic
forms the answer is yes, and on `2 × 2` matrices every quasiconvex quadratic form is even
polyconvex (Terpstra 1938, Serre 1983). Ball (1990) gave a counterexample among integrands that may
be discontinuous and take the value `+∞`, for `d ≥ 3, m ≥ 3` or `d ≥ 4, m ≥ 2`.

### Šverák (1992): three components

Šverák's paper is five pages long. The map `w(x) = (1/2π)(sin 2πx₁, sin 2πx₂, sin 2π(x₁ + x₂))`
from `ℝ²` to `ℝ³` has gradients in a three-dimensional subspace `L` of `ℝ^{3×2}` that contains only
three rank-one directions. On `L`, `f = −rst` is linear along those directions, so rank-one convex
on `L`, while `∫ f(∇w) < 0 = f(0)`: the oscillation of `∇w` lowers the energy, which a quasiconvex
function forbids (Lemma 1, for periodic test maps). Lemma 2 makes `X ↦ f(PX)`, with `P` the
projection onto `L`, rank-one convex on all of `ℝ^{3×2}` by adding `ε|X|² + ε|X|⁴ + k|X − PX|²`:
this works for every `ε > 0` with `k = k(ε)` large, and for small `ε` the integral along `∇w`
stays negative. The result is a quartic polynomial that is rank-one convex and not quasiconvex.
Composing with the projection onto the upper left `3 × 2` block gives the same in every `d × m`
with `d ≥ 3`, `m ≥ 2`. As Tartar pointed out to Šverák, the example is reminiscent of one of
Tartar's in compensated compactness.

The formalization here follows every step, including the compactness argument of Lemma 2 and the
cut-off argument of Lemma 1: it builds the cut-off with the paper's bound `|Dη_ε| ≤ 2/ε`, and
proves the limit that the paper leaves to the reader.

### Two components: thirty years of partial results

Šverák's example does not carry over to two components. It cannot be transposed: rank-one
convexity is invariant under `A ↦ Aᵀ`, quasiconvexity is not (Kružík 1999, for integrands with
infinite values), and Müller (2000) showed that Šverák's own example, for small `ε` and large `k`,
becomes quasiconvex after transposition. In `2 × 2`, its mechanism cannot detect a failure of quasiconvexity at all
(Sebestyén–Székelyhidi, below). The two-component case drew a long line of work:

- positive results in special classes:
  - diagonal matrices (Müller 1999);
  - some hypersurfaces (Chaudhuri–Müller 2003);
  - upper triangular matrices (Harris, Kirchheim and Lin 2018);
  - isotropic planar energies that are isochoric or incompressible, for which rank-one convexity
    even implies polyconvexity (Martin, Ghiba and Neff, 2017–2018);
- the quasiconvex hull of compact sets of `2 × 2` matrices, localized by Faraco and Székelyhidi
  (2008);
- Kristensen (1999): quasiconvexity is equivalent to a local condition among smooth integrands only
  if it equals rank-one convexity;
- the Burkholder function: Astala, Iwaniec, Prause and Saksman (2012) related the `2 × 2` problem
  to Burkholder's martingale inequalities; a positive answer in `2 × 2` would prove Iwaniec's
  conjecture on the norm of the Beurling–Ahlfors transform. That conjecture is now claimed proved,
  by a preprint of twenty authors, Cassese and Šverák among them
  ([arXiv:2609.28311](https://arxiv.org/abs/2609.28311), September–October 2026), which we
  audited with a Lean formalization, [lean4-iwaniec](https://github.com/vltanh/lean4-iwaniec);
  the converse is not known, so the claim leaves the `2 × 2` problem open;
- analogues of Šverák's gradient measure in `2 × 2` (Pedregal 1996, Pedregal–Šverák 1998,
  Bandeira–Ornelas 2011) turned out to be laminates, and Sebestyén and Székelyhidi (2017) proved it
  for the whole class: in `2 × 2`, the gradient measure of a sum of three sawtooth waves along
  pairwise non-collinear directions is a laminate, so this construction cannot detect a failure of
  quasiconvexity;
- numerical studies (Guerra and Teixeira da Costa 2022, and others) found no counterexample in
  `2 × 2`.

Grabovsky (2018), from the theory of `G`-closures, found the only other known family of
finite-valued rank-one convex, non-quasiconvex integrands before 2026. The smallest is on
`ℝ^{8×2}`, eight components; it bears on two components through its transpose, which Agazzi,
Bruno, Guerra and Pasqualotto used in 2026.

### Pedregal (2014–2026): a claimed proof in `2 × 2`

Pedregal's approach is dual. Quasiconvexity in `2 × 2` would follow if every homogeneous gradient
Young measure of a two-component map were a laminate (in the sense of Jensen's inequality for
rank-one convex functions); laminates of finite order are obtained from Dirac masses by splitting
along rank-one segments (Kinderlehrer–Pedregal 1991, Pedregal 1993). A first preprint (2014,
withdrawn in 2018) argued in the opposite direction, and its withdrawal cites Sebestyén and
Székelyhidi's theorem. From 2019 the paper formalized here claims a proof: for maps in `ℙ_l`
(1-periodic, affine on the triangles of a dyadic triangulation) the gradient measure is a laminate
of finite order, obtained as a fixed point, by Kakutani's theorem, of a set-valued map between the
weights of the two components' `(H_n)`-conditions. The paper's versions:

- versions 1–2 claimed this for two-component maps in every dimension;
- version 3 was withdrawn;
- versions 4–5 restrict the claim to `2 × 2`.

The audit ([`docs/Pedregal/REPORT.md`](docs/Pedregal/REPORT.md)) proves:

- the paper's reduction (a fixed point gives a laminate);
- the properties of the map;
- Kakutani's theorem.

However, the audit finds that Corollary 7.2, which says that the map has nonempty values, is false: an
explicit counterexample at the coarsest level, checked in Lean, and empty values in every random
instance tested numerically. The claim is neither proved nor refuted. At the coarsest level the
gradient measure is uniform on the vertices of a cube of rank-one directions, a laminate by three
symmetric splittings, and the formalization proves the paper's Theorem 1.1 (1) there directly;
Sebestyén and Székelyhidi's theorem covers the same cube measures with unequal weights.

### Cassese (2026): two components in higher dimension, and the homogeneous problem

Cassese claims to settle the two-component case outside `2 × 2`. With Šverák's theorem and the
monotonicity in the dimensions, `2 × 2` would then be the only size left open (lines 251–254 of the
TeX source). The preprint grew in three versions:

- v1 (4 August 2026) gave `2 × m` for large `m`;
- v2 (28 August) added `2 × 4`, after Agazzi, Bruno, Guerra and Pasqualotto's `2 × 4` example
  (12 August);
- v3 (16 September) added `2 × 3`.

Most of the paper uses a method of its own:

- the integrands are real functions `C^p ‖P(A)‖^p − ‖Q(A)‖^p`, with `P` and `Q` taking values in a
  Banach space, or their rank-one convex envelopes;
- their rank-one convexity is controlled through the correspondence between laminates and
  martingales (UMD estimates, Burkholder's functions);
- their failure of quasiconvexity is witnessed by explicit vector fields.

All four theorems, 1.2–1.5, follow this scheme. Symmetry can force quasiconvexity:

- Guerra and Kristensen (2022) proved it for nonnegative homogeneous isotropic integrands at the
  multiples of orthogonal matrices (at every matrix:
  [above](#a-result-of-this-repository-homogeneous-isotropic-integrands-in-2--2));
- Bruno and Pasqualotto (2026, a preprint) show that the planar Dacorogna–Marcellini energy is
  quasiconvex exactly when it is rank-one convex (`|γ| ≤ 2/√3`), and that quasiconvexity is
  equivalent to rank-one convexity for homogeneous quartics on `2 × 2` invariant under left and
  right rotations.

Cassese conjectures that isotropic homogeneous rank-one convex integrands are
quasiconvex at `0` (Conjecture 1); Theorem 1.4's examples have only the weaker conjugation and
transposition invariance. For integrands on `ℝ^{2×2}` that are positively homogeneous, this
repository proves quasiconvexity at every matrix
([above](#a-result-of-this-repository-homogeneous-isotropic-integrands-in-2--2)). The paper also answers
Kirchheim and Kristensen's homogeneous problem negatively, which Šverák's example cannot do: its
quartic part at infinity, `ε|X|⁴`, is convex. Grabovsky's examples cannot either: they are
nonnegative, hence quasiconvex at `0`.

How Cassese relates to the other two papers:

- **Šverák.** The `2 × 3` quartic of Theorem 1.3 follows Šverák's architecture: a polynomial that
  is rank-one convex on a subspace `L₃` with few rank-one directions, extended to all matrices by a
  projection and a penalty `δ(|πA|² + Λ²|π^⊥A|²)²` (Lemma 5.1, a homogeneous analogue of Šverák's
  `k|X − PX|²`), and a witness whose gradients lie in `L₃`. Its transpose on `ℝ^{3×2}`
  (Corollary 5.3, sketched) stays non-quasiconvex, unlike Šverák's example, and gives a homogeneous
  proof of Šverák's theorem. Remark 5.2 adds, without proof, that Lemma 5.1 turns Šverák's example
  into a positively 3-homogeneous one. Both examples are quartic, the least possible degree: a
  polynomial of degree at most three that is rank-one convex at `0` is quasiconvex (Proposition 5.1,
  "folklore"). Cassese's Section 1.1 restates Šverák's example as failing quasiconvexity *at `0`*,
  in Cassese's definitions (Lipschitz test maps on the unit cube, rank-one convexity on segments);
  Šverák uses smooth test maps on a domain and convexity along lines. The repository proves:
  - the two forms of rank-one convexity equivalent;
  - Cassese's quasiconvexity stronger than Šverák's on the cube;
  - Šverák's example in Cassese's form ([`Morrey/Cassese/Sverak.lean`](Morrey/Cassese/Sverak.lean)).
- **Pedregal.** Cassese does not cite Pedregal's claimed proof (arXiv:1905.06571). Cassese's
  `2 × 3` example, proved here, refutes the claim of Pedregal's versions 1–2 for two-component maps in dimension `3` and more (an inference of
  this repository: Pedregal report, E17); the current version's `2 × 2` claim is untouched. Both papers rest on the same
  duality: the rank-one convex envelope is computed by (pre)laminates, Pedregal's starting point and
  Cassese's Proposition 2.1. Cassese expects the `2 × 2` homogeneous problem to have a positive
  answer, and notes that a positive answer would imply Iwaniec's conjecture; for the integrands
  behind Theorem 1.2, the question in `2 × 2` (the case `n = 1`) is equivalent to Iwaniec's
  conjecture, so a proof of it must use features specific to `2 × 2`. Iwaniec's conjecture has
  since been claimed proved ([arXiv:2609.28311](https://arxiv.org/abs/2609.28311)), and the
  proof passes our audit by formalization
  ([lean4-iwaniec](https://github.com/vltanh/lean4-iwaniec)); by it, those integrands give no
  counterexample in `2 × 2`.
- **Kristensen.** Cassese's Corollary 5.2 (by Kristensen's smoothing) states a smooth integrand on
  `ℝ^{2×m}`, `m ≥ 3`, uniformly rank-one convex with quadratic growth, that is not quasiconvex at
  `0`. With Kristensen's theorem, quasiconvexity is then not a local condition on `ℝ^{2×m}`,
  `m ≥ 3`, as Šverák's example showed for three or more components.

### Since then

- Agazzi, Bruno, Guerra and Pasqualotto ([arXiv:2608.12298](https://arxiv.org/abs/2608.12298),
  August 2026): a non-homogeneous counterexample on `ℝ^{2×4}`, from an affine slice of the
  transpose of Grabovsky's integrand, and examples on symmetric matrices (`ℝ^{4×4}_sym`, and
  `ℝ^{3×3}_sym` by modifying Šverák's example).
- Conti, Dolzmann and Dondl ([arXiv:2610.31886](https://arxiv.org/abs/2610.31886), October 2026): a
  frame-indifferent rank-one convex function on `ℝ^{3×3}` that is not quasiconvex; the failure of
  quasiconvexity uses Šverák's plane `L` and his test map.
- Gennaioli and Rindler ([arXiv:2608.20899](https://arxiv.org/abs/2608.20899)) prove Bouchitté's
  Vanishing Mass Conjecture and show that the analogue of Morrey's conjecture for pure
  concentrations fails; Cassese contrasts this with his Corollary 1.6. Guerra
  ([arXiv:2608.23388](https://arxiv.org/abs/2608.23388)) proves the Burkholder function
  quasiconvex on symmetric matrices.

### Other formalizations

- Conti, Dolzmann and Dondl formalized their `3 × 3` example in Lean 4
  ([sergioconti/so3-r1c-and-not-qc](https://github.com/sergioconti/so3-r1c-and-not-qc),
  Apache-2.0), with its own definitions of rank-one convexity and quasiconvexity; by its README,
  the code was written by Claude Opus 5.5 under the authors' guidance. It includes the following,
  but not Lemma 2 or the Theorem:
  - adaptations of Šverák's test map (`φ(x) = (sin x₁, sin x₂, −sin(x₁ + x₂))` on `ℝ³`), of its
    gradients in `L` and of the integral (4);
  - the "only if" half of his Lemma 1.
- Cassese formalized his Theorem 1.2 and Theorem 1.3 at `p = 4` in Lean, with an AI system (the
  paper names ChatGPT 5.6 Sol), and released the code without a license.
- This repository does not use either: its proofs were written without consulting them. Parts of both
  were displayed on 21 and 22 November 2026 by searches for earlier formalizations and for the
  literature, and by checks of the documents; [Cassese's credits](docs/Cassese/CREDITS.md#who) say which.
- We found no earlier formalization of Šverák's theorem or of Pedregal's paper.

## What the repository adds to the papers

- A theorem of its own in `2 × 2`: for isotropic, positively `p`-homogeneous integrands,
  rank-one convexity implies quasiconvexity for every `p > 0`
  ([above](#a-result-of-this-repository-homogeneous-isotropic-integrands-in-2--2)):
  - polyconvexity for nonnegative integrands with `p ≥ 2`, and for all with `p = 2`;
  - convexity for `p = 1`;
  - `F = 0` for `0 < p < 1`.
- The refutation of Pedregal's Corollary 7.2, Proposition 7.1 and the summary of Step 2 of its
  proof, with an exact counterexample ([`docs/Pedregal/REPORT.md`](docs/Pedregal/REPORT.md), E13–E14).
- Bridges between Šverák's and Cassese's definitions, which differ in their test maps and in how
  they test convexity along rank-one directions ([`Morrey/Cassese/Bridges.lean`](Morrey/Cassese/Bridges.lean)).
- Šverák's example in Cassese's terms: not quasiconvex at `0` ([`Cassese.sverak_example`](Morrey/Cassese/Sverak.lean#L32)).
- The landscape as theorems: with Šverák's example and Cassese's, rank-one convexity does not imply
  quasiconvexity in any size `d × m` with `d, m ≥ 2` except `2 × 2`, and at `p = 4` the homogeneous
  problem fails in all those sizes ([`CasseseChallenge.morrey_landscape`](palomar/Cassese/Challenge.lean#L296), `homMorrey_landscape`).
- Every cited result that the papers' proofs use, proved:
  - Kakutani's theorem;
  - Burkholder's inequality, square-function inequality and functions `u_q`, and the sharpness of
    his constant;
  - the properties of UMD spaces that Cassese uses (extrapolation, `L^p`, Schatten classes, dyadic
    and complex constants, zig-zag concavity) and decoupling;
  - the non-commutative and the Kahane–Khintchine inequalities, with hypercontractive constants;
  - transference for homogeneous multipliers and Dragičević's lower bound for the Beurling–Ahlfors
    transform;
  - Dacorogna's formula for the quasiconvex envelope and his theorems on minors and quadratic
    forms;
  - Rindler's lemmas;
  - Kristensen's smoothing.
- The general theories are in four packages (below);
  [`Morrey/Common/External/`](Morrey/Common/External) states each result in its source's terms and proves it from them, by the
  source's own argument. Cassese's report lists:
  - the sources;
  - the differences;
  - the named substitutes for steps that a source takes from a work that was not read, only
    recalls, or states without proof.

## Trust

- `lake build` passes. No `sorry` outside the Challenges, no `axiom`, no `native_decide`.
- [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of the libraries
  uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and lists what each numbered result
  depends on. The check covers the packages' proofs that the libraries use; each package also has
  an audit of its own.
- [`scripts/route_check.py`](scripts/route_check.py) checks, paper by paper, that each proof uses
  the results that the paper's proof cites, except the differences recorded with their reasons in
  each paper's `docs/<Paper>/route_differences.tsv`.
- Every proof follows its paper's argument, except the departures that each report lists in its
  Section 7, each with the reason that forces it:
  - none for Šverák;
  - three for Pedregal, all forced by errors of the paper;
  - Cassese's in [its report](docs/Cassese/REPORT.md).
- Comparator accepts each paper's Solution against its Challenge, and the Solution of the
  repository's own result against its Challenge.
- Independent AI agents checked:
  - the statements against the papers;
  - the formal proofs against the papers' proofs and, for the cited results, against the sources';
  - every recorded departure;
  - the documents.
- No person has reviewed the proofs.

## Shared code and dependencies

[`Morrey/Common/`](Morrey/Common) holds what the papers share:

- [`Basic/`](Morrey/Common/Basic), general lemmas in Mathlib's namespaces (the rank of `2 × 2` matrices, for
  Pedregal; mollification by bump functions, for Šverák's cut-off and Cassese; supporting lines of
  convex functions and convex functions of sublinear growth, for the homogeneous isotropic
  integrands);
- `External/<Source>/`, one directory per cited source, with its statements in the source's terms,
  their proofs from a package, and a README.

Besides Mathlib, the proofs use five packages:

| Package | Lean library | Provides | Used by |
| --- | --- | --- | --- |
| [lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point) | `FixedPoint` | Kakutani's fixed-point theorem, by Kakutani's argument | Pedregal |
| [lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations) | `CalculusOfVariations` | rank-one convexity, quasiconvexity and more (below) | Cassese, HomogeneousIsotropic |
| [lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis) | `HarmonicAnalysis` | scalar and vector-valued harmonic analysis (below) | Cassese |
| [lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability) | `BanachProbability` | martingales, UMD spaces and more (below) | Cassese |
| [lean4-iwaniec](https://github.com/vltanh/lean4-iwaniec) | `Agazzi` | the audit by formalization of Agazzi et al., arXiv:2609.28311: the quasiconvexity of the truncated determinant and of the Burkholder function | HomogeneousIsotropic |

`CalculusOfVariations` provides:

- rank-one convexity and quasiconvexity (independence of the domain, periodic test maps,
  laminates);
- Dacorogna's formula for the quasiconvex envelope;
- minors, null Lagrangians and quadratic forms;
- Kristensen's smoothing;
- distributions on `ℝ`;
- mollification;
- piecewise affine maps.

`HarmonicAnalysis` provides:

- scalar:
  - Fourier multipliers on `ℝ²` and `𝕋²`;
  - transference from `𝕋²` to `ℝ²`;
  - the Beurling–Ahlfors transform and Dragičević's lower bound;
  - smooth periodic functions;
- vector-valued:
  - the Hilbert transform, Mihlin multipliers and Littlewood–Paley inequalities in UMD spaces;
  - transference from `ℝ` to `𝕋`;
  - matrix-valued Hardy functions;
  - Szegő's theorem and Sarason's factorization of `H¹`;
  - Paley's inequality in the Schatten classes;
  - the non-commutative Khintchine inequality.

`BanachProbability` provides:

- Rademacher sums and the Kahane–Khintchine inequality;
- martingales and Burkholder's inequalities with their sharpness;
- UMD spaces;
- Schatten classes (real and complex) and Randrianantoanina's martingale transforms;
- type 2 and K-convexity;
- also the non-commutative Khintchine inequality by exchangeable pairs, which is not used here.

Šverák's library uses only Mathlib and `Common/Basic`. The dependencies run one way: no package
imports this repository. Among the packages, the vector-valued part of `HarmonicAnalysis` imports
`BanachProbability`; the others use only Mathlib.

## Building

Lean and Mathlib `v4.36.0-rc2`. [`lakefile.toml`](lakefile.toml) requires the five packages from
their GitHub repositories, each pinned by its commit. Lake fetches all five into
`.lake/packages`, whichever part of the repository is built. From the root:

```sh
lake exe cache get && lake build
lake env lean scripts/Audit.lean
python3 scripts/route_check.py check docs/Pedregal/paper_routes.tsv --accept docs/Pedregal/route_differences.tsv
python3 scripts/route_check.py check docs/Sverak/paper_routes.tsv --accept docs/Sverak/route_differences.tsv
python3 scripts/route_check.py check docs/Cassese/paper_routes.tsv --accept docs/Cassese/route_differences.tsv
lake env lake comparator --config=palomar/Pedregal/comparator.json
lake env lake comparator --config=palomar/Sverak/comparator.json
lake env lake comparator --config=palomar/Cassese/comparator.json
lake env lake comparator --config=palomar/HomogeneousIsotropic/comparator.json
```

## Layout

```text
Morrey/                       the Lean code
  Common/Basic/               general lemmas, shared (the rank of 2 × 2 matrices, mollification)
  Common/External/<Source>/   the cited results, in their sources' terms, proved from the packages
  Pedregal/                   Pedregal's paper: its library, by section
  Sverak/                     Šverák's paper
  Cassese/                    Cassese's paper, with the bridges to Šverák's definitions
  HomogeneousIsotropic/       the repository's result on homogeneous isotropic integrands
palomar/<Paper>/              one Palomar submission per paper, and one for the repository's
                              result: Challenge.lean, Solution.lean, comparator.json,
                              formalization.yaml
docs/<Paper>/                 each paper's README.md, REPORT.md, CREDITS.md, the routes of its
                              proofs; numerics/ for Pedregal
docs/HomogeneousIsotropic/    the repository's result: README.md, CREDITS.md, paper/
scripts/                      the audit, the route check, the documentation checks
.github/workflows/            CI for all; one Palomar preflight workflow per submission
```

Each preflight workflow names its submission's `comparator.json` and `formalization.yaml`.

## Credits

- Pedregal: formalized on 21 November 2026; a departure audit, with no change to its proofs, on
  21–22 November: [`docs/Pedregal/CREDITS.md`](docs/Pedregal/CREDITS.md).
- Šverák: formalized on 21 November 2026; Lemma 1's cut-off rebuilt as the paper's on 21–22
  November: [`docs/Sverak/CREDITS.md`](docs/Sverak/CREDITS.md).
- Cassese: formalized on 21 November 2026; every assumed result proved, and Theorem 1.2 by the
  paper's route, on 21–22 November; the cited results by their sources' proofs on 22 November:
  [`docs/Cassese/CREDITS.md`](docs/Cassese/CREDITS.md).
- HomogeneousIsotropic: the research in pull request 1, with ChatGPT Chat 6 Extra High (OpenAI)
  and Claude (Anthropic), the argument for integrands that change sign by ChatGPT Chat 6 Extra
  High; proved in Lean and written up on 23–24 November 2026 by Claude Fable 5.2 and Claude
  Opus 5.5 in Claude Code: [`docs/HomogeneousIsotropic/CREDITS.md`](docs/HomogeneousIsotropic/CREDITS.md).
- The three papers were formalized by Claude (Anthropic): Claude Opus 5.5 in Claude Code (and Claude Haiku 5.5 for
  reading web pages), at the request of The-Anh Vu-Le, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure. No person has
  reviewed the proofs.
- License: Apache-2.0 ([`LICENSE`](LICENSE)).
