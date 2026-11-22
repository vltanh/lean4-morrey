# Pedregal's proof of Morrey's conjecture in 2 × 2: an audit in Lean

One of the papers on Morrey's problem formalized in this repository; the
[overview](../../README.md) describes the problem, the state of each case and how the papers relate.

Morrey's problem asks whether every rank-one convex function `ψ : ℝ^{m×N} → ℝ` is quasiconvex.
It is false for `m ≥ 3` (Šverák 1992, [formalized here](../Sverak/README.md)) and open for `2 × 2`
matrices. P. Pedregal,
[arXiv:1905.06571v5](https://arxiv.org/abs/1905.06571v5) (2026), claims a proof for
`2 × 2`: every gradient measure of a periodic piecewise affine map `ℝ² → ℝ²` is a laminate,
obtained as a fixed point, by Kakutani's theorem, of a set-valued map `𝐓` between the weights of
`(H_n)`-conditions of the two components.

This repository formalizes the paper in Lean 4 with Mathlib. **The paper's proof does not work:
Corollary 7.2, which the use of Kakutani's theorem needs, is false**, and so are Proposition 7.1
and the summary of Step 2 of its proof (checked in Lean, with an explicit counterexample). Every
other numbered result of Sections 3–7 except Claim 7.3 is correct and proved, including the
reduction "if every `𝐓(t)` is nonempty, then the gradient measure is a laminate". The main
theorems are neither proved nor refuted: Theorem 1.1 (2) and Theorem 1.2 are the open `2 × 2`
case of Morrey's problem, and Theorem 1.1 (1) implies it. Nothing is assumed.

## Status

| Part of the paper | Status |
| --- | --- |
| §3 `(H_n)`-conditions, molds, Proposition 3.3 | proved |
| §4 tri-dyadic molds for `τ_l` (Definition 4.1) | formalized; its conditions proved |
| §5 the weights `Θ_l` (Definition 5.1, eqs. (5.10)–(5.15)) | proved; (5.10) in corrected form (a missing factor `3^{−1}`, E6) |
| §6 the map `𝐓`: Proposition 6.1, Subsection 6.1, Proposition 6.3 | proved |
| §6 Kakutani's theorem (Theorem 6.2, cited) | proved, from [lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point) |
| §7 Proposition 7.1, Corollary 7.2, Step 2 of the proof (with Claim 7.5) | **false**: refuted |
| §7 Claim 7.4 | proved |
| §7 Claim 7.3 (a step of the refuted proof) | not formalized |
| §8 Theorem 1.1 (1), by the paper's argument | proved with the conclusion of Corollary 7.2 as a hypothesis |
| Theorem 1.1 (1) at `l = 1` | proved, by an explicit lamination |
| Theorem 1.1 (2), Theorem 1.2 | open (stated, not proved) |

## Main results

| Paper | Lean | Statement |
| --- | --- | --- |
| Cor 7.2 | [`corollary7_2_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L230) ⭐ | Corollary 7.2 as stated is false |
| Cor 7.2 | [`exists_T_eq_empty`](../../palomar/Pedregal/Challenge.lean#L272) ⭐ | for `l = 1`, a tri-dyadic mold, `u, v ∈ ℙ_1` and `t ∈ Θ_1` with `𝐓(t) = ∅` |
| Prop 7.1 | [`proposition7_1_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L237) | Proposition 7.1 as stated is false |
| Step 2, Claim 7.5 | [`step2Claim_false`](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean#L246) | the summary of Step 2 is false |
| Thm 1.1 (1) | [`theorem1_1_of_nonempty`](../../Morrey/Pedregal/Reduction.lean#L24) ⭐ | if `𝐓(t) ≠ ∅` for every `t ∈ Θ_l`, then `ν` is a laminate (the paper's argument) |
| Thm 1.1 (1), `l = 1` | [`theorem1_1_part1_levelOne`](../../Morrey/Pedregal/LevelOne.lean#L156) ⭐ | for `u, v ∈ ℙ_1`, `ν` is a laminate |
| Prop 6.1 | [`proposition6_1`](../../Morrey/Pedregal/Map.lean#L365) | a fixed point of `𝐓` makes `ν` a laminate |
| Prop 6.3 | [`proposition6_3`](../../Morrey/Pedregal/Map.lean#L285) | the values of `𝐓` are convex (and the directions are linear on `Θ_l`) |
| Thm 6.2 | [`External.Kakutani.exists_fixedPoint`](../../Morrey/Common/External/Kakutani/Theorem.lean#L38) | Kakutani's fixed-point theorem |

⭐ in [`Challenge.lean`](../../palomar/Pedregal/Challenge.lean), with two checks of the definitions ([`mem_T_self`](../../Morrey/Pedregal/Checks.lean#L20), [`card_C`](../../palomar/Pedregal/Challenge.lean#L296)). The Challenge
does not state Morrey's problem, which is not proved: its standard `2 × 2` form (continuous `ψ`,
Lipschitz test maps vanishing outside a bounded domain) is the proposition [`Theorem1_2`](../../Morrey/Pedregal/Introduction.lean#L65) of
[`Morrey/Pedregal/Introduction.lean`](../../Morrey/Pedregal/Introduction.lean).

The counterexample: `l = 1`, the mold that numbers the interfaces kind by kind, uniform weights,
`u = τ(x₀) − τ(x₁) − τ(x₀ + x₁)` and `v(x₀, x₁) = u(x₁, x₀)` with `τ(x)` the distance to the
nearest integer. At the mixture of two vertical interfaces, the second coordinates of the mass
points are tangential derivatives, the same for every choice of weights; the decomposition
directions are `(2, 0)` for `u` and `(∗, 4)` for `v`, never parallel. The failure looks generic:
`𝐓(t)` is cut out by more linear conditions than `Θ_l` has dimensions, and numerically it is empty
for random instances and, for a generic instance at `l = 1`, for every mold
([REPORT.md, E13](REPORT.md#e13-proposition-71-and-corollary-72-are-false)).

## What the audit found

| | Finding |
| --- | --- |
| E13 | Proposition 7.1 and Corollary 7.2 are false; the proof of Theorem 1.1 fails |
| E14 | the summary of Step 2 of the proof of Proposition 7.1, with Claim 7.5, is false |
| E15 | the gaps in the proof of Proposition 7.1: the dimension count, the positivity, the starting barycenter, the averaging over translates |
| E16 | Theorem 1.1 (2) from (1), "a standard density argument", is not given |
| E17 | later work: the claim of v1–v2 for two-component maps in dimension `N ≥ 3` is false; Cassese's `2 × 3` counterexample (2026) is proved in this repository |
| E4 | Theorem 1.2's "arbitrary function" needs to be measurable |

18 findings in all, with the misprints: see [REPORT.md](REPORT.md). Every proof of a correct
result follows the paper's argument. There are three departures, each forced by an error of the
paper: the reduction takes the conclusion of the false Corollary 7.2 as a hypothesis, the case
`l = 1` is proved by an explicit lamination, and the false statements are refuted instead of proved
([REPORT.md, Section 7](REPORT.md#7-departures-from-the-papers-proofs)).

## Trust

- `lake build` passes; no `sorry` outside [`Challenge.lean`](../../palomar/Pedregal/Challenge.lean), no `axiom`, no `native_decide`.
- [`scripts/Audit.lean`](../../scripts/Audit.lean) checks that every declaration uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and lists what each result depends on.
- [`scripts/route_check.py`](../../scripts/route_check.py) checks that each proof uses the results the paper's proof cites,
  except the differences recorded with their reasons in
  [`route_differences.tsv`](route_differences.tsv).
- Comparator accepts [`Solution.lean`](../../palomar/Pedregal/Solution.lean) against [`Challenge.lean`](../../palomar/Pedregal/Challenge.lean)
  ([`comparator.json`](../../palomar/Pedregal/comparator.json)).
- Independent AI agents checked the statements and the counterexample against the TeX source,
  the formal proofs against the paper's, the report, every recorded departure, and the documents.
  No person has reviewed the proofs.

## Dependencies, Palomar, building

- [Mathlib](https://github.com/leanprover-community/mathlib4) `v4.36.0-rc2`, Lean
  `v4.36.0-rc2`.
- [lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point) (commit `5f650f0`):
  Kakutani's theorem, used only by the proofs. No other package: the three packages that Cassese's
  formalization needs are not used here, but Lake loads them to build any part of the repository
  (see the [overview's building instructions](../../README.md#building)).
- Palomar: this paper is its own submission: [`Challenge.lean`](../../palomar/Pedregal/Challenge.lean) (statements, in
  Mathlib's vocabulary), [`Solution.lean`](../../palomar/Pedregal/Solution.lean) (proofs), [`comparator.json`](../../palomar/Pedregal/comparator.json) and
  [`formalization.yaml`](../../palomar/Pedregal/formalization.yaml), named by the workflow
  [`palomar_preflight_pedregal.yml`](../../.github/workflows/palomar_preflight_pedregal.yml).

From the repository root, with the packages in place (and, for Comparator, the copies that the
overview describes):

```sh
lake exe cache get && lake build
lake env lean scripts/Audit.lean
python3 scripts/route_check.py check docs/Pedregal/paper_routes.tsv --accept docs/Pedregal/route_differences.tsv
lake env lake comparator --config=palomar/Pedregal/comparator.json
```

| Path | Content |
| --- | --- |
| [`Morrey/Pedregal/`](../../Morrey/Pedregal) | the library: `Defs` (the definitions that the Challenge copies), [`Hn/`](../../Morrey/Pedregal/Hn) (§3), `MoldTau` (§4), `Weights` (§5), `Triangulation`, `Map` (§6), `Reduction` (§8), [`NonEmptiness/`](../../Morrey/Pedregal/NonEmptiness) (§7), `LevelOne`, `Introduction` (§1) |
| [`palomar/Pedregal/`](../../palomar/Pedregal) | the Palomar submission: Challenge, Solution, `comparator.json`, `formalization.yaml` |
| [`docs/Pedregal/`](.) | this README, the report, the credits, the routes of the paper's proofs and the recorded differences, and [`numerics/`](numerics), the numerical checks behind the report |
| [`Morrey/Common/`](../../Morrey/Common) | shared with the other papers; this paper uses [`Basic/LinearAlgebra/Matrix/RankTwo.lean`](../../Morrey/Common/Basic/LinearAlgebra/Matrix/RankTwo.lean) (the rank of `2 × 2` matrices) and [`External/Kakutani/`](../../Morrey/Common/External/Kakutani) (Kakutani's theorem, from lean4-fixed-point) |
| [`scripts/`](../../scripts) | shared: the audit, the route check, the documentation checks |

## Related work and credits

- The literature, the versions of the paper and the 2026 counterexamples in higher dimension:
  [REPORT.md, Section 10](REPORT.md#10-the-paper-in-the-literature).
- Formalized by Claude (Anthropic), with Claude Code, at the request of The-Anh Vu-Le, following
  the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure, on 21
  November 2026. No person has reviewed the proofs. See [CREDITS.md](CREDITS.md).
- License: Apache-2.0.
