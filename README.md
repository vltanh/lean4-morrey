# Morrey's problem in Lean

An integrand `f : ℝ^{d×m} → ℝ` is *quasiconvex* if affine maps minimize `∫ f(∇u)` among maps
with the same boundary values: `∫_{(0,1)^m} f(A + ∇φ) ≥ f(A)` for every matrix `A` and every
Lipschitz `φ : (0,1)^m → ℝ^d` vanishing on the boundary. It is *rank-one convex* if it is convex
along every line `t ↦ A + tB` with `rank B = 1`. Morrey (1952) showed that quasiconvexity is the
condition under which `∫ f(∇u)` is weakly-∗ lower semicontinuous, and that it implies rank-one
convexity; he asked whether the converse holds. This is *Morrey's problem*. Here `d` is the number
of components of `u` and `m` the number of variables.

This repository formalizes, in Lean 4 with Mathlib, three papers on the problem: a theorem that
settles it for three or more components, a claimed proof for `2 × 2` matrices, and a recent
preprint on the two-component case in higher dimension. Each paper is audited on its own, with its
own Challenge, report and Palomar submission; the papers share general mathematics and the checks.

## The state of the problem

**Morrey's problem**: does rank-one convexity imply quasiconvexity for `f : ℝ^{d×m} → ℝ`? A
positive answer in `d × m` gives one in every smaller size, and a counterexample gives one in every
larger size (Cassese, Section 1.1), so the answer is decided by a few sizes:

| Size | Answer | Settled by | Here |
| --- | --- | --- | --- |
| `d = 1` or `m = 1` | yes: both notions are convexity | classical | **proved** (Cassese, Section 1) |
| `d ≥ 3`, `m ≥ 2` | no | Šverák (1992), on `ℝ^{3×2}` | **proved** ([Šverák](docs/Sverak/README.md)) |
| `d = 2`, `m ≥ 3` | no, claimed in two 2026 preprints | Cassese, on `ℝ^{2×3}`; Agazzi, Bruno, Guerra and Pasqualotto, on `ℝ^{2×4}` | **proved**: Cassese's quartic and the monotonicity ([Cassese](docs/Cassese/README.md)) |
| `2 × 2` | **open** | Pedregal (2019–2026, preprint) claims yes | the proof fails: its Corollary 7.2 is **refuted** ([Pedregal](docs/Pedregal/README.md)) |

That every size but `2 × 2` fails is proved here as one theorem, from Šverák's example and Cassese's
([`CasseseChallenge.morrey_landscape`](palomar/Cassese/Challenge.lean#L542)).

**The homogeneous problem** (Kirchheim–Kristensen 2016): for `p ∈ (1, ∞)`, is every rank-one
convex, `p`-homogeneous `f` (`f(tA) = |t|^p f(A)`) quasiconvex at `0`? For a continuous
homogeneous `f`, failure at `0` is failure at every matrix. All the negative answers below are
claims of Cassese's preprint.

| Exponent and size | Answer | Source | Here |
| --- | --- | --- | --- |
| `p = 1`, every size | yes, at every matrix of rank at most one | Kirchheim–Kristensen (2016) | not formalized (cited by Cassese) |
| `p = 1`, `4 × 4`, at a matrix of rank two | no (a nonnegative example) | Cassese, Corollary 1.6 | proved, assuming transference and Dragičević's bound |
| every `p > 1`, `2 × m` with `m ≥ m₀(p)` | no | Cassese, Theorem 1.2 | **proved** (by the paper's Remark 4.5) |
| `p = 4`, `2 × 3` (a quartic polynomial) and `3 × 2` (its transpose), hence every size above `2 × 2` | no | Cassese, Theorem 1.3 and Corollary 5.3 (the latter sketched) | **proved** |
| `p` near `4`, `2 × 3` | no | Cassese, Theorem 1.3 | **proved** |
| every `p > 1`, `d × d` with `d ≥ d₀(p)`, conjugation- and transposition-invariant | no | Cassese, Theorem 1.4 | **proved** at `p = 4` for every `d ≥ 588`; for general `p`, assuming UMD results for Schatten classes and non-commutative Khintchine inequalities |
| `p ∈ (1, ∞)`, `p ≠ 2`, `4 × 2` | no | Cassese, Theorem 1.5 | proved, assuming transference and Dragičević's bound |
| `2 × 3` and `3 × 2` for `p` away from `4`; `p = 2` in `2 × 3`, `3 × 2`, `3 × 3` | open (Cassese expects no) | — | — |
| `2 × 2`, every `p` | open (Cassese expects yes) | — | — |

## The papers

| Paper | Claim | Formalization | Main finding |
| --- | --- | --- | --- |
| V. Šverák, *Rank-one convexity does not imply quasiconvexity*, Proc. Roy. Soc. Edinburgh 120A (1992) | a quartic polynomial on `ℝ^{3×2}`, rank-one convex and not quasiconvex; hence no for `d ≥ 3`, `m ≥ 2` | **proved**, every step by the paper's argument | no false statement; the steps left to the reader are supplied, chief among them the limit in Lemma 1, "easily seen" |
| P. Pedregal, *Morrey's conjecture: rank-one convexity implies quasi-convexity for two-dimensional, two-component maps*, [arXiv:1905.06571v5](https://arxiv.org/abs/1905.06571v5) (2026) | yes for `2 × 2` | Proposition 7.1, Corollary 7.2 and the summary of Step 2 of the proof are **false**; the rest of Sections 3–7, except Claim 7.3, is proved; Theorems 1.1 (2) and 1.2 are stated, not proved | the paper's use of Kakutani's theorem needs Corollary 7.2, which an explicit counterexample, checked in Lean, refutes; the claim stays open |
| G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*, [arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3) (2026) | no for `2 × m`, `m ≥ 3`; the homogeneous problem fails at `p = 4` in every size above `2 × 2`, and at every `p > 1` in suitable sizes | every result **proved**; Theorem 1.4 for general `p`, Theorem 1.5 and Corollary 1.6 assume results out of reach of Lean (UMD theory, non-commutative Khintchine, transference, Dragičević's bound), as named hypotheses | no false statement; the paper leaves gaps (the uniformity in `p` behind Theorem 1.3 (b), the constant `κ` of Section 5, a step of Proposition 2.5 false under the reading of prelaminates the paper needs, Proposition 6.6 and Corollary 5.2 without proof), all filled |

Each paper has a README, a report (`REPORT.md`: its findings, how the formalization reads it, what
each result depends on, its place in the literature, what comes next) and credits in
`docs/<paper>/`: [Pedregal](docs/Pedregal/README.md), [Šverák](docs/Sverak/README.md),
[Cassese](docs/Cassese/README.md).

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
cutoff argument of Lemma 1, whose limit the paper leaves to the reader.

### Two components: thirty years of partial results

Šverák's example does not carry over to two components. It cannot be transposed: rank-one
convexity is invariant under `A ↦ Aᵀ`, quasiconvexity is not (Kružík 1999, for integrands with
infinite values), and Müller (2000) showed that Šverák's own example becomes quasiconvex after
transposition. In `2 × 2`, its mechanism cannot detect a failure of quasiconvexity at all
(Sebestyén–Székelyhidi, below). The two-component case drew a long line of work:

- positive results in special classes: diagonal matrices (Müller 1999), some hypersurfaces
  (Chaudhuri–Müller 2003), upper triangular matrices (Harris, Kirchheim and Lin 2018), and
  isotropic planar energies that are isochoric or incompressible, for which rank-one convexity even
  implies polyconvexity (Martin, Ghiba and Neff, 2017–2018);
- the quasiconvex hull of compact sets of `2 × 2` matrices, localized by Faraco and Székelyhidi
  (2008);
- Kristensen (1999): quasiconvexity is equivalent to a local condition among smooth integrands only
  if it equals rank-one convexity;
- the Burkholder function: Astala, Iwaniec, Prause and Saksman (2012) related the `2 × 2` problem
  to Burkholder's martingale inequalities; a positive answer in `2 × 2` would prove Iwaniec's
  conjecture on the norm of the Beurling–Ahlfors transform, which is the stake of any claimed
  proof;
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
weights of the two components' `(H_n)`-conditions. Versions 1–2 claimed this for two-component maps
in every dimension; version 3 was withdrawn; versions 4–5 restrict the claim to `2 × 2`.

The audit ([`docs/Pedregal/REPORT.md`](docs/Pedregal/REPORT.md)) proves the paper's reduction (a fixed point
gives a laminate), the properties of the map and Kakutani's theorem, but finds that Corollary 7.2,
which says that the map has nonempty values, is false: an explicit counterexample at the coarsest
level, checked in Lean, and empty values in every random instance tested numerically. The claim is
neither proved nor refuted. At the coarsest level the gradient measure is uniform on the vertices of
a cube of rank-one directions, a laminate by three symmetric splittings, and the formalization
proves the paper's Theorem 1.1 (1) there directly; Sebestyén and Székelyhidi's theorem covers the
same cube measures with unequal weights.

### Cassese (2026): two components in higher dimension, and the homogeneous problem

Cassese claims to settle the two-component case outside `2 × 2`. With Šverák's theorem and the
monotonicity in the dimensions, `2 × 2` would then be the only size left open (lines 251–253 of the
TeX source). The preprint grew in three versions: v1 (4 August 2026) gave `2 × m` for large `m`;
Agazzi, Bruno, Guerra and Pasqualotto's `2 × 4` example followed (12 August); v2 (28 August) added
`2 × 4`, and v3 (16 September) `2 × 3`.

Most of the paper uses a method of its own. The integrands are real functions
`C^p ‖P(A)‖^p − ‖Q(A)‖^p`, with `P` and `Q` taking values in a Banach space, or their rank-one convex
envelopes; their rank-one convexity is controlled through the correspondence between laminates and
martingales (UMD estimates, Burkholder's functions), and their failure of quasiconvexity is
witnessed by explicit vector fields. That gives Theorems 1.2, 1.4 and 1.5. Symmetry can force
quasiconvexity (Guerra–Kristensen 2022, for homogeneous isotropic integrands; Bruno–Pasqualotto
2026), and Cassese conjectures that isotropic homogeneous rank-one convex integrands are
quasiconvex at `0` (Conjecture 1); Theorem 1.4's examples have only the weaker conjugation and
transposition invariance. The paper also answers
Kirchheim and Kristensen's homogeneous problem negatively, which Šverák's example cannot do: its
quartic part at infinity, `ε|X|⁴`, is convex. Grabovsky's examples cannot either: they are
nonnegative, hence quasiconvex at `0`.

How Cassese relates to the other two papers:

- **Šverák.** The `2 × 3` quartic of Theorem 1.3 follows Šverák's architecture: a polynomial that
  is rank-one convex on a subspace `L₃` with few rank-one directions, extended to all matrices by a
  projection and a penalty `Λ²|π^⊥A|²` (Lemma 5.1, a homogeneous analogue of Šverák's
  `k|X − PX|²`), and a witness whose gradients lie in `L₃`. Its transpose on `ℝ^{3×2}`
  (Corollary 5.3, sketched) stays non-quasiconvex, unlike Šverák's example, and gives a homogeneous
  proof of Šverák's theorem. Remark 5.2 adds, without proof, that Lemma 5.1 turns Šverák's example
  into a positively 3-homogeneous one. Both examples are quartic, the least possible degree: a
  polynomial of degree at most three that is rank-one convex at `0` is quasiconvex (Proposition 5.1,
  "folklore"). Cassese's Section 1.1 restates Šverák's example as failing quasiconvexity *at `0`*,
  in Cassese's definitions (Lipschitz test maps on the unit cube, rank-one convexity on segments);
  Šverák uses smooth test maps on a domain and convexity along lines. The repository proves the two
  forms of rank-one convexity equivalent, Cassese's quasiconvexity stronger than Šverák's on the
  cube, and Šverák's example in Cassese's form ([`Morrey/Cassese/Sverak.lean`](Morrey/Cassese/Sverak.lean)).
- **Pedregal.** Cassese does not cite Pedregal. Cassese's `2 × 3` example, proved here, refutes the
  claim of Pedregal's versions 1–2 for two-component maps in dimension `3` and more (an inference of
  this repository: Pedregal report, E17); the current version's `2 × 2` claim is untouched. Both papers rest on the same
  duality: the rank-one convex envelope is computed by (pre)laminates, Pedregal's starting point and
  Cassese's Proposition 2.1. Cassese expects the `2 × 2` homogeneous problem to have a positive
  answer, and notes that a positive answer would imply Iwaniec's conjecture; for the integrands
  behind his Theorem 1.2, the question in `2 × 2` (the case `n = 1`) is equivalent to Iwaniec's
  conjecture, so a proof of it must use features specific to `2 × 2`.
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
  the code was written by Claude Opus 5.5 under the authors' guidance. It includes parts of
  Šverák's argument: his test map, its gradients in `L`, the integral (4), and the "only if" half
  of his Lemma 1; not Lemma 2 or the Theorem.
- Cassese formalized his Theorem 1.2 and Theorem 1.3 at `p = 4` in Lean, with an AI system (the
  paper names ChatGPT 5.6 Sol), and released the code without a license.
- This repository does not use either: its definitions and proofs were written independently.
- We found no earlier formalization of Šverák's theorem or of Pedregal's paper.

## What the repository adds to the papers

- The refutation of Pedregal's Corollary 7.2, Proposition 7.1 and the summary of Step 2 of its
  proof, with an exact counterexample ([`docs/Pedregal/REPORT.md`](docs/Pedregal/REPORT.md), E13–E14).
- Bridges between Šverák's and Cassese's definitions, which differ in their test maps and in how
  they test convexity along rank-one directions ([`Morrey/Cassese/Bridges.lean`](Morrey/Cassese/Bridges.lean)).
- Šverák's example in Cassese's terms: not quasiconvex at `0` ([`Cassese.sverak_example`](Morrey/Cassese/Sverak.lean#L32)).
- The landscape as theorems: with Šverák's example and Cassese's, rank-one convexity does not imply
  quasiconvexity in any size `d × m` with `d, m ≥ 2` except `2 × 2`, and at `p = 4` the homogeneous
  problem fails in all those sizes ([`CasseseChallenge.morrey_landscape`](palomar/Cassese/Challenge.lean#L542), `homMorrey_landscape`).
- The cited results that the papers' proofs use, proved in [`Morrey/Common/`](Morrey/Common):
  Burkholder's inequality and square function inequality for Hilbert-space-valued martingales, the
  sharpness of Burkholder's constant, Burkholder's functions `u_q`, Dacorogna's formula for the
  quasiconvex envelope, Dacorogna's theorems on rank-one affine functions and on quadratic forms,
  Rindler's lemmas on quasiconvexity, Kristensen's smoothing, Kakutani's theorem, and Fourier series
  of Lipschitz periodic maps on the torus.

## Trust

- `lake build` passes. No `sorry` outside the Challenges, no `axiom`, no `native_decide`.
- [`scripts/Audit.lean`](scripts/Audit.lean) checks that every declaration of the three libraries
  uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and lists what each numbered result
  depends on.
- [`scripts/route_check.py`](scripts/route_check.py) checks, paper by paper, that each proof uses
  the results that the paper's proof cites, except the differences recorded with their reasons in
  each paper's `docs/route_differences.tsv`.
- Comparator accepts each paper's Solution against its Challenge.
- Independent AI agents checked the statements against the papers, the formal proofs against the
  papers' proofs, and the documents. No person has reviewed the proofs.

## Layout and building

```text
Morrey/                 the Lean code
  Common/Basic/         general mathematics, shared (the rank of 2 × 2 matrices)
  Common/External/      cited results, shared (Kakutani's theorem, from lean4-fixed-point)
  Pedregal/             Pedregal's paper: its library, by section
  Sverak/               Šverák's paper
  Cassese/              Cassese's paper, with the bridges to Šverák's definitions
palomar/                one Palomar submission per paper
  Pedregal/             Challenge.lean, Solution.lean, comparator.json, formalization.yaml
  Sverak/, Cassese/     the same
docs/                   the documents of each paper
  Pedregal/             README.md, REPORT.md, CREDITS.md, the routes of the paper's proofs, numerics/
  Sverak/, Cassese/     the same
scripts/                the audit, the route check, the documentation checks
.github/workflows/      CI for all papers; one Palomar preflight workflow per paper
```

The papers' documents: [Pedregal](docs/Pedregal/README.md), [Šverák](docs/Sverak/README.md),
[Cassese](docs/Cassese/README.md). Their Palomar files: [`palomar/`](palomar). Each preflight workflow names its
paper's `comparator.json` and `formalization.yaml`. Lean and Mathlib `v4.36.0-rc2`.

```sh
lake exe cache get && lake build
lake env lean scripts/Audit.lean
python3 scripts/route_check.py check docs/Pedregal/paper_routes.tsv --accept docs/Pedregal/route_differences.tsv
python3 scripts/route_check.py check docs/Sverak/paper_routes.tsv --accept docs/Sverak/route_differences.tsv
python3 scripts/route_check.py check docs/Cassese/paper_routes.tsv --accept docs/Cassese/route_differences.tsv
lake env lake comparator --config=palomar/Pedregal/comparator.json
lake env lake comparator --config=palomar/Sverak/comparator.json
lake env lake comparator --config=palomar/Cassese/comparator.json
```

## Credits

- Pedregal, first round (21 November 2026): [`docs/Pedregal/CREDITS.md`](docs/Pedregal/CREDITS.md).
- Šverák and Cassese, second round (21 November 2026): [`docs/Sverak/CREDITS.md`](docs/Sverak/CREDITS.md),
  [`docs/Cassese/CREDITS.md`](docs/Cassese/CREDITS.md).
- Formalized by Claude (Anthropic), with Claude Code, at the request of The-Anh Vu-Le, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure. No person has
  reviewed the proofs.
- License: Apache-2.0 ([`LICENSE`](LICENSE)).
