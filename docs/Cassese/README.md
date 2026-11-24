# Cassese (2026): Morrey's problem in `ℝ^{2×m}`, in Lean

**The formalization is complete and unconditional.** Every result that G. Cassese proves in *A
solution to Morrey's problem in `ℝ^{2×m}`*, [arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3)
(16 September 2026, a preprint), is proved in Lean 4 with Mathlib, and so is every result of other
works that its proofs use. Nothing is assumed: no statement takes a result of another work as a
hypothesis, and the proofs use only Lean's standard axioms.

The paper constructs rank-one convex integrands on `ℝ^{2×m}`, `m ≥ 3`, that are nowhere
quasiconvex. With Šverák's theorem ([formalized here](../Sverak/README.md)) this leaves `2 × 2` as
the only size in which Morrey's problem can have a positive answer. It also answers Kirchheim and
Kristensen's homogeneous problem negatively: there are `p`-homogeneous, rank-one convex, nowhere
quasiconvex integrands for every `p > 1` in suitable sizes, and at `p = 4` in every `d × m` with
`d, m ≥ 2` other than `2 × 2`. The repository formalizes other papers on Morrey's problem too;
the [overview](../../README.md) describes the problem and how the papers relate.

## Status

| Part of the paper | Status |
| --- | --- |
| §1: Theorems 1.2–1.5, Corollary 1.6, the consequences drawn after Theorem 1.3 (only `2 × 2` remains) | proved |
| §2: Lemmas 2.1, 2.2, Propositions 2.1–2.5, 2.7, 2.8, Theorem 2.3 | proved; the cited ones, except Proposition 2.1, in [`Morrey/Common/External/`](../../Morrey/Common/External) |
| §4 (`2 × m`): Lemmas 4.1, 4.2, Propositions 4.1–4.3, (10); the route of Remark 4.5 | proved |
| §5 (`2 × 3`): Propositions 5.1, 5.2, Lemma 5.1, Corollaries 5.2–5.4 | proved |
| §6 (`d × d`): Propositions 6.1–6.6, Remark 6.3, Corollaries 6.1, 6.3, 6.4, Theorem 6.2 | proved |
| §7 (`4 × 2`): Propositions 7.1, 7.2, Theorem 7.1, Corollary 7.2 | proved |
| Theorem 1.1 (Kirchheim–Kristensen) and Proposition 2.6 (Osękowski), quoted as context | stated; no proof uses them |
| Conjecture 1 | stated |
| The other remarks, and claims that the paper asserts without proof (such as Corollary 1.6 for `p > 2`) | not formalized ([REPORT.md, Section 9](REPORT.md#9-not-formalized)) |

## Main results

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem 1.2 | [`theorem1_2`](../../Morrey/Cassese/Introduction.lean#L1989) ⭐ | every `p > 1`: a `p`-homogeneous, rank-one convex, nowhere quasiconvex integrand on `ℝ^{2×m}` for every `m ≥ m₀(p)` (the paper's proof, through UMD constants) |
| Theorem 1.2, by Remark 4.5 | [`theorem1_2_elementary`](../../Morrey/Cassese/TwoByM.lean#L3480) | the same statement, by the paper's elementary route (Burkholder's scalar function `u_q`) |
| Theorem 1.3 | [`theorem1_3_a`](../../Morrey/Cassese/Introduction.lean#L2027) ⭐, [`theorem1_3_b`](../../Morrey/Cassese/Introduction.lean#L2052) ⭐ | a quartic polynomial on `ℝ^{2×3}`, rank-one convex and nowhere quasiconvex; a `p`-homogeneous one for every `p` near `4` |
| Corollary 5.3 | [`corollary5_3`](../../Morrey/Cassese/TwoByThree/Transpose.lean#L197) ⭐ | its transpose, on `ℝ^{3×2}` |
| lines 251–254 | [`morrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2241) ⭐ | with Šverák's theorem: for `d, m ≥ 2` other than `2 × 2`, some rank-one convex integrand on `ℝ^{d×m}` is not quasiconvex |
| lines 254–256 | [`homMorrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2269) ⭐ | at `p = 4` the homogeneous problem has a negative answer in every such size |
| Theorem 1.4 | [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2084) ⭐ | every `p > 1`: a conjugation- and transposition-invariant example on `ℝ^{d×d}` for every `d ≥ d₀(p)` |
| Theorem 1.4 at `p = 4` | [`theorem1_4_four`](../../Morrey/Cassese/Square.lean#L3586) ⭐ | the same at `p = 4`, for every `d ≥ 588` (Section 6.3) |
| Theorem 1.5 | [`theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2167) ⭐ | every `p > 1` other than `2`: a `p`-homogeneous, rank-one convex, nowhere quasiconvex integrand on `ℝ^{4×2}` |
| Corollary 1.6 | [`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2215) ⭐ | a nonnegative `1`-homogeneous rank-one convex integrand on `ℝ^{4×4}`, not quasiconvex at a matrix of rank two |
| Corollary 5.2 | [`corollary5_2`](../../Morrey/Cassese/NonLocality.lean#L32) | a smooth, uniformly Legendre–Hadamard integrand of quadratic growth on `ℝ^{2×m}`, `m ≥ 3`, not quasiconvex at `0` |

⭐ in [`Challenge.lean`](../../palomar/Cassese/Challenge.lean), which Comparator checks against
[`Solution.lean`](../../palomar/Cassese/Solution.lean), with [`projL3_mem`](../../Morrey/Cassese/TwoByThree/Basic.lean#L57), a check of the
definitions of Section 5. The Challenge's theorems have no hypotheses beyond the paper's.

## What the audit found

No statement of the paper is false. The main findings
([REPORT.md, Section 3](REPORT.md#3-errors-and-gaps-in-the-paper)):

| | Finding |
| --- | --- |
| E10 | with the reading of prelaminates that Proposition 2.4 needs, the step of Proposition 2.5 at lines 661–663 is false; the other reading breaks Proposition 2.4 |
| E4 | Theorem 1.3 (b): "by continuity" in `p` needs the constants of Lemma 5.1 (1) uniform for `p` near `4` |
| E27 | Remark 6.3 and Proposition 6.5 at `q = ∞` need Kahane–Khintchine constants polynomial in `q`; Proposition 6.4 leaves them out, the theorem it cites has them |
| E30 | the sharpness of `p* − 1` behind Corollary 6.3 has only "see also [Cassese 2025]" as a source; the chain ends at Burkholder (1984) and Osękowski (2012), whose proof is followed |
| E5 | the constant `κ = 2` of Section 5 is asserted without proof; it holds, and `√2` already works |
| E6, E19 | Proposition 6.6 and Corollary 5.2 have no proof in the paper |
| E28, E29 | Proposition 7.2 and Corollary 6.1 pass from smooth to Lipschitz or compactly supported test maps without saying how |

41 findings in all (E2–E42), most of them:

- steps left to the reader;
- sketched proofs;
- misprints;
- citations that say more or less than their sources.

Every proof follows the paper's argument except three, which repair a gap or a false step (E4, E9,
E10). The cited results follow their sources' proofs, with the gaps and slips of the sources
repaired; some steps that the sources of the non-commutative Khintchine inequality take from works
that were not read, only recall, or state without proof, follow named substitutes. The report lists
each source, how it was read, and what is different
([REPORT.md, Section 7](REPORT.md#7-departures-from-the-papers-proofs)).

## Trust

- `lake build` passes, with no `sorry` outside the Challenges and no `axiom`; each of the three
  packages below has its own audit of the same kind.
- The repository's audit, [`scripts/Audit.lean`](../../scripts/Audit.lean), checks that every
  declaration of the library uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and lists
  the results of other works that each result uses
  ([REPORT.md, Section 8](REPORT.md#8-what-each-result-depends-on)).
- The route check, with [`paper_routes.tsv`](paper_routes.tsv) and
  [`route_differences.tsv`](route_differences.tsv), checks that each proof uses the results that
  the paper's proof cites; every difference is recorded with its reason.
- Comparator checks that the Solution proves exactly the Challenge's statements with those axioms
  ([`comparator.json`](../../palomar/Cassese/comparator.json)).
- Independent AI agents checked:
  - the statements against the TeX source;
  - the formal proofs against the paper's;
  - the packages' proofs against the cited sources;
  - the departures from the paper;
  - the documents.
- No person has reviewed the proofs.

## Dependencies

Mathlib `v4.36.0-rc2`, and three Lake packages written for this formalization, published on GitHub.
[`lakefile.toml`](../../lakefile.toml) pins each by its commit, and Lake fetches them (see the
[overview's building instructions](../../README.md#building)):

| Package | What this paper uses from it |
| --- | --- |
| [`lean4-harmonic-analysis`](https://github.com/vltanh/lean4-harmonic-analysis) | harmonic analysis, for Section 7 and for Proposition 6.3 (below) |
| [`lean4-banach-probability`](https://github.com/vltanh/lean4-banach-probability) | martingales, UMD theory and Schatten classes, for Sections 2, 4–7 (below) |
| [`lean4-calculus-of-variations`](https://github.com/vltanh/lean4-calculus-of-variations) | the calculus of variations, for Section 2 (used throughout), Section 5, Corollary 1.6 and Proposition 7.2 (below) |

What this paper uses from `lean4-harmonic-analysis`, for Section 7:

- Fourier multipliers and duality;
- transference from `𝕋²` to `ℝ²` (HNVW I, Corollary 5.7.6);
- Poisson summation;
- Dragičević's lower bound for `𝓑²`;
- Fourier series of smooth periodic functions.

What this paper uses from `lean4-harmonic-analysis`, for Proposition 6.3 (used by Section 6), is the
non-commutative Khintchine inequality, with:

- the Hilbert transform, multipliers and Littlewood–Paley theory in UMD spaces;
- matrix-valued Hardy functions;
- Paley's inequality in the Schatten classes.

What this paper uses from `lean4-banach-probability`, for Sections 2, 4–7:

- Burkholder's inequality, its sharpness and Burkholder's function;
- UMD theory (the dyadic and the complex constants, decoupling, extrapolation, `L^p`, zig-zag
  concavity);
- Kahane–Khintchine and hypercontractivity;
- Schatten classes, real and complex;
- type 2 of the Schatten classes and K-convexity (for Proposition 6.3);
- Randrianantoanina's non-commutative martingale transforms.

What this paper uses from `lean4-calculus-of-variations`, for Lemmas 2.1, 2.2 and Proposition 2.2
(used throughout), Section 5, Corollary 1.6 and Proposition 7.2:

- rank-one convexity and quasiconvexity;
- Dacorogna's formula for the quasiconvex envelope;
- minors and null Lagrangians;
- quadratic forms;
- Kristensen's smoothing;
- distributional second derivatives on `ℝ`.

The vector-valued part of `lean4-harmonic-analysis` uses `lean4-banach-probability`; otherwise the
packages depend only on Mathlib. At the pinned commits they have Palomar entries of their own, not
submitted:

- eight in `lean4-banach-probability`;
- four in `lean4-harmonic-analysis` (one for its scalar part, three for its vector-valued part);
- three in `lean4-calculus-of-variations`.

[`Morrey/Common/External/`](../../Morrey/Common/External) states each cited result in its source's terms and proves it from these
packages; [`Morrey/Cassese/Hypotheses.lean`](../../Morrey/Cassese/Hypotheses.lean) restates it in
the paper's terms.

## Building and Palomar

This paper is its own Palomar submission: [`palomar/Cassese/`](../../palomar/Cassese) holds the
Challenge, the Solution, `comparator.json` and
[`formalization.yaml`](../../palomar/Cassese/formalization.yaml), named by the workflow
[`palomar_preflight_cassese.yml`](../../.github/workflows/palomar_preflight_cassese.yml). From the
repository root:

```sh
lake exe cache get && lake build
lake env lean scripts/Audit.lean
python3 scripts/route_check.py check docs/Cassese/paper_routes.tsv --accept docs/Cassese/route_differences.tsv
lake env lake comparator --config=palomar/Cassese/comparator.json
```

| Path | Content |
| --- | --- |
| [`Morrey/Cassese/`](../../Morrey/Cassese) | the library, by module (below) |
| [`Morrey/Common/External/`](../../Morrey/Common/External) | the cited results, one directory per source, each with a README naming the argument used |
| [`Morrey/Common/Basic/`](../../Morrey/Common/Basic) | general lemmas: `2 × 2` matrices of rank one, mollification |
| [`palomar/Cassese/`](../../palomar/Cassese) | the Palomar submission |
| this directory | the report, the credits, the routes |

The library:

- `Defs` (the definitions that the Challenge copies);
- `Introduction` (§1);
- `Toolkit` (§2);
- `Hypotheses` (the cited results in the paper's terms, and the bridges to the packages);
- `TwoByM` (§4);
- `TwoByThree/` (§5);
- `NonLocality` (Corollary 5.2);
- `Square/` (§6);
- `FourByTwo` (§7);
- `Conclusion` (Conjecture 1);
- `Bridges`;
- `Lifting`;
- `Rademacher`;
- `Sverak` (Šverák's example in Cassese's terms).

## Related work and credits

- Related work, in [REPORT.md, Section 10](REPORT.md#10-the-paper-in-the-literature):
  - the paper's place among the work on Morrey's problem;
  - the concurrent and later papers (among them a claimed proof of Iwaniec's conjecture);
  - other formalizations, including the author's own Lean code for Theorems 1.2 and 1.3, which the
    proofs did not consult (parts of it were displayed by searches for earlier formalizations and
    for the literature, and by checks of the documents: [CREDITS.md](CREDITS.md#who)).
- Formalized by Claude (Anthropic), with Claude Code, at the request of The-Anh Vu-Le, following
  the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure, in
  November 2026. No person has reviewed the proofs. See [CREDITS.md](CREDITS.md).
- License: Apache-2.0 ([`LICENSE`](../../LICENSE)).
