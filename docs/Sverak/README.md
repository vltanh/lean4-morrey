# Šverák (1992): rank-one convexity does not imply quasiconvexity, in Lean

One of the papers on Morrey's problem formalized in this repository; the
[overview](../../README.md) describes the problem, the state of each case and how the papers relate.

V. Šverák, *Rank-one convexity does not imply quasiconvexity*, Proc. Roy. Soc. Edinburgh Sect. A
120 (1992), 185–189, answers Morrey's problem negatively for maps with three or more components.
Its integrand is a quartic polynomial on `3 × 2` matrices,

`F(X) = f(PX) + ε|X|² + ε|X|⁴ + k|X − PX|²`,

with `P` the orthogonal projection onto `L = {(r 0; 0 s; t t)}` and `f(r 0; 0 s; t t) = −rst`. The
periodic map `w(x) = (1/2π)(sin 2πx₁, sin 2πx₂, sin 2π(x₁ + x₂))` has its gradients in `L`, and
`∫ F(Dw) < F(0)`, so `F` is not quasiconvex; yet `F` is rank-one convex for a suitable `k`.

This directory formalizes the whole paper in Lean 4 with Mathlib. **Every result is proved, by the
paper's argument, and nothing is assumed.** The paper has no false statement; the formalization
supplies the steps it leaves to the reader, chief among them the limit in the proof of Lemma 1, and
builds the objects it takes for granted, such as Lemma 1's cut-off `η_ε` with `|Dη_ε| ≤ 2/ε`.

## Status

| Part of the paper | Status |
| --- | --- |
| Lemma 1 (periodic test maps suffice) | proved |
| The rank-one directions of `L`; `f` linear on rank-one lines of `L` | proved |
| `Dw` and (4) | proved |
| Lemma 2 ((6)–(8), the compactness argument) | proved |
| Theorem ((10), (11)) | proved |
| Remark (`F` has degree four) | proved |
| Corollary (`m ≥ 3`, `n ≥ 2`) | proved |

## Main results

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem | [`theorem_main`](../../Morrey/Sverak/Theorem.lean#L187) ⭐ | there are `ε > 0` and `k > 0` such that `F` is rank-one convex and not quasiconvex |
| Corollary | [`corollary`](../../Morrey/Sverak/Theorem.lean#L341) ⭐ | for `m ≥ 3`, `n ≥ 2`, `X ↦ F(TX)` (`TX` the upper left `3 × 2` block) is rank-one convex and not quasiconvex |
| Remark | [`remark_polynomial`](../../Morrey/Sverak/Theorem.lean#L360) ⭐ | `F` is a polynomial of degree four (`ε ≠ 0`) |
| Lemma 1 | [`lemma1`](../../Morrey/Sverak/Lemma1.lean#L717) | a continuous `f` is quasiconvex if and only if `∫_{[0,1]^n} f(A + Du) ≥ f(A)` for all smooth periodic `u` |
| Lemma 2 | [`lemma2`](../../Morrey/Sverak/Lemma2.lean#L504) | for each `ε > 0` there is `k > 0` such that `F` is rank-one convex |
| (4) | [`equation4`](../../Morrey/Sverak/Construction.lean#L177) | `∫_{[0,1]²} f(Dw) < 0 = f(0)` |

⭐ in [`Challenge.lean`](../../palomar/Sverak/Challenge.lean). Quasiconvexity is stated on a given domain, and the
Theorem and the Corollary on the unit cube, the domain of the paper's proofs (the paper cites that
the class does not depend on the domain).

## What the audit found

| | Finding |
| --- | --- |
| E1 | Lemma 1: the limit as `ε → 0`, "easily seen", is not proved in the paper |
| E2 | Lemma 1: `u_ε` is defined on an undefined set `B` |
| E3 | Lemma 1 is proved only at `A = 0` |
| E4 | Lemma 2: three implicit steps (compactness of `𝒦`, `Ȳ = PȲ`, the passage to every rank-one `Y`) |
| E5 | the Corollary: `T` can map a rank-one line to a point; Lemma 1 is used without being named |

Every proof follows the paper's argument: there is no departure
([REPORT.md, Section 7](REPORT.md#7-departures-from-the-papers-proofs)). Details, how the
formalization reads the paper, its place in the literature and what comes next:
[REPORT.md](REPORT.md).

## Trust

- `lake build` passes; no `sorry` outside [`Challenge.lean`](../../palomar/Sverak/Challenge.lean), no `axiom`.
- The repository's audit, [`scripts/Audit.lean`](../../scripts/Audit.lean), checks that every result
  uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- The route check, with [`paper_routes.tsv`](paper_routes.tsv) and
  [`route_differences.tsv`](route_differences.tsv) (empty), checks that each proof uses the
  results that the paper's proof cites.
- Comparator accepts [`Solution.lean`](../../palomar/Sverak/Solution.lean) against [`Challenge.lean`](../../palomar/Sverak/Challenge.lean)
  ([`comparator.json`](../../palomar/Sverak/comparator.json)).
- Independent AI agents checked the statements against the paper, the formal proofs against the
  paper's, every recorded departure from the paper, and the documents. No person has reviewed the
  proofs.

## Building and Palomar

The library uses only Mathlib, and one module shared with the other papers,
[`Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean`](../../Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean)
(mollification, for the cut-off of Lemma 1). It uses none of the packages that Cassese's
formalization needs, but Lake loads them to build any part of the repository: see the
[overview's building instructions](../../README.md#building). Lean and Mathlib `v4.36.0-rc2`.

This paper is its own Palomar submission: [`Challenge.lean`](../../palomar/Sverak/Challenge.lean),
[`Solution.lean`](../../palomar/Sverak/Solution.lean), [`comparator.json`](../../palomar/Sverak/comparator.json) and
[`formalization.yaml`](../../palomar/Sverak/formalization.yaml), named by the workflow
[`palomar_preflight_sverak.yml`](../../.github/workflows/palomar_preflight_sverak.yml). From the
repository root, with the packages in place (and, for Comparator, the copies that the overview
describes):

```sh
lake exe cache get && lake build
lake env lean scripts/Audit.lean
python3 scripts/route_check.py check docs/Sverak/paper_routes.tsv --accept docs/Sverak/route_differences.tsv
lake env lake comparator --config=palomar/Sverak/comparator.json
```

The library is [`Morrey/Sverak/`](../../Morrey/Sverak), the Palomar submission
[`palomar/Sverak/`](../../palomar/Sverak), and the documents and routes are in this directory.

| File | Content |
| --- | --- |
| [`Defs.lean`](../../Morrey/Sverak/Defs.lean) | the definitions that the Challenge copies: `jac`, [`RankOneConvex`](../../palomar/Sverak/Challenge.lean#L52), [`QuasiconvexOn`](../../palomar/Sverak/Challenge.lean#L65), [`unitCube`](../../palomar/Sverak/Challenge.lean#L56), [`frobSq`](../../palomar/Sverak/Challenge.lean#L73), `P`, `f`, `F`, `T` |
| [`Cube.lean`](../../Morrey/Sverak/Cube.lean) | the unit cube and smooth test maps |
| [`Lemma1.lean`](../../Morrey/Sverak/Lemma1.lean) | Lemma 1: the cut-off `η_ε`, the test maps `u_ε`, the limit, the equivalence |
| [`Construction.lean`](../../Morrey/Sverak/Construction.lean) | `L`, its rank-one directions, `w`, `Dw`, (4) |
| [`Lemma2.lean`](../../Morrey/Sverak/Lemma2.lean) | Lemma 2 |
| [`Theorem.lean`](../../Morrey/Sverak/Theorem.lean) | (10), (11), the Theorem, the Remark, the Corollary |
| [`paper_routes.tsv`](paper_routes.tsv), [`route_differences.tsv`](route_differences.tsv) | the routes of the paper's proofs (labels `sv-…`, ours: the paper has no TeX source) |

Cassese's library builds on this one: [`Morrey/Cassese/Sverak.lean`](../../Morrey/Cassese/Sverak.lean) restates the
example in Cassese's definitions, and Cassese's periodic test maps
([`Morrey/Cassese/Square/Hessian.lean`](../../Morrey/Cassese/Square/Hessian.lean)) use the cut-off and the averaging lemma of Lemma 1.

## Credits

- Formalized by Claude (Anthropic), with Claude Code, at the request of The-Anh Vu-Le, following
  the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure, on 21
  November 2026; Lemma 1's cut-off was rebuilt as the paper's on 22 November 2026. No person has
  reviewed the proofs. See [CREDITS.md](CREDITS.md).
- License: Apache-2.0 ([`LICENSE`](../../LICENSE)).
