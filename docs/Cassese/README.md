# Cassese (2026): Morrey's problem in `ℝ^{2×m}`, in Lean

One of the papers on Morrey's problem formalized in this repository; the
[overview](../../README.md) describes the problem, the state of each case and how the papers relate.

G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*,
[arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3) (16 September 2026), a preprint, constructs
rank-one convex integrands on `ℝ^{2×m}`, `m ≥ 3`, that are nowhere quasiconvex. With Šverák's
theorem ([formalized here](../Sverak/README.md)) this leaves `2 × 2` as the only size in which
Morrey's problem can have a positive answer. The paper also answers Kirchheim and Kristensen's
homogeneous problem negatively: `p`-homogeneous, rank-one convex, nowhere quasiconvex integrands,
for every `p > 1` in suitable sizes, and at `p = 4` in every size above `2 × 2`.

**Every result of the paper is proved, some of them conditionally, and no statement of the paper
is false.** The paper's two-component theorems are unconditional here: Theorem 1.2 (every `p`, `2 × m`), Theorem 1.3 (the
quartic on `2 × 3`, and `p` near `4`), Corollary 5.3 (its transpose on `3 × 2`), and the theorem that
only `2 × 2` remains. Some results rest on mathematics that no Lean library has, each a named hypothesis of
the statements that use it: Theorem 1.4 for general `p`, with Propositions 6.2, 6.5, eq (31),
Remark 6.3 and Corollary 6.1 (UMD theory for Schatten classes, decoupling, non-commutative and
Kahane–Khintchine inequalities); Theorem 1.5 and Corollary 1.6, with Theorem 7.1, Corollary 7.2 and
the lower bound of Proposition 7.2 (transference, and Dragičević's bound for the Beurling–Ahlfors
transform); and the paper's own UMD route to Theorem 1.2, formalized beside the unconditional one. Theorem 1.4 at `p = 4` is
unconditional.

## Main results

| Paper | Lean | Statement | Assumes |
| --- | --- | --- | --- |
| Theorem 1.2 | [`theorem1_2`](../../Morrey/Cassese/Introduction.lean#L1988) ⭐ | every `p > 1`: a `p`-homogeneous, rank-one convex, nowhere quasiconvex integrand on `ℝ^{2×m}`, `m ≥ m₀(p)` | — (by the paper's Remark 4.5) |
| Theorem 1.3 | [`theorem1_3_a`](../../Morrey/Cassese/Introduction.lean#L2026), [`theorem1_3_b`](../../Morrey/Cassese/Introduction.lean#L2051) ⭐ | a quartic polynomial on `ℝ^{2×3}`, rank-one convex and nowhere quasiconvex; and for `p` near `4` | — |
| Corollary 5.3 | [`corollary5_3`](../../Morrey/Cassese/TwoByThree/Transpose.lean#L197) ⭐ | its transpose on `ℝ^{3×2}` | — |
| lines 251–254 | [`morrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2240) ⭐ | with Šverák: in every `d × m`, `d, m ≥ 2`, except `2 × 2`, rank-one convexity does not imply quasiconvexity | — |
| lines 254–256 | [`homMorrey_landscape`](../../Morrey/Cassese/Introduction.lean#L2268) ⭐ | at `p = 4`, the homogeneous problem fails in every such size except `2 × 2` | — |
| Theorem 1.4 | [`theorem1_4_four`](../../Morrey/Cassese/Square.lean#L3589) ⭐ | at `p = 4`: conjugation- and transposition-invariant examples on `ℝ^{d×d}`, every `d ≥ 588` | — |
| Theorem 1.4 | [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L2083) ⭐ | every `p > 1`, `d ≥ d₀(p)` | UMD extrapolation, Randrianantoanina, Cox–Veraar, Pisier–Xu, Kahane–Khintchine |
| Theorem 1.5 | [`theorem1_5`](../../Morrey/Cassese/Introduction.lean#L2166) ⭐ | every `p ≠ 2`: an example on `ℝ^{4×2}` | transference, Dragičević |
| Corollary 1.6 | [`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L2214) ⭐ | a nonnegative 1-homogeneous rank-one convex integrand on `ℝ^{4×4}`, not quasiconvex at a rank-two matrix | transference, Dragičević |

⭐ in [`Challenge.lean`](../../palomar/Cassese/Challenge.lean), checked by Comparator against
[`Solution.lean`](../../palomar/Cassese/Solution.lean). The Challenge states each assumed result in
its docstring, with its source and why it is out of reach.

## What the audit found

No statement is false. The paper leaves gaps, which the formalization fills
([REPORT.md, Section 3](REPORT.md#3-errors-and-gaps-in-the-paper)); the main ones:

| | Finding |
| --- | --- |
| E4 | Theorem 1.3 (b): "by continuity" in `p` needs the constants of Lemma 5.1 (1) uniform for `p` near `4` |
| E5 | the constant `κ = 2` of Section 5 is asserted without proof; it is true, and `√2` already works |
| E10 | with the reading of prelaminates that Proposition 2.4 needs, the step of Proposition 2.5 at lines 661–663 is false |
| E6, E19 | Proposition 6.6 and Corollary 5.2 have no proof in the paper (both proved here) |
| E27 | Remark 6.3 needs Kahane–Khintchine constants polynomial in `q`, which the cited result does not give |
| E28, E29 | Proposition 7.2 and Corollary 6.1 pass from smooth to Lipschitz or compactly supported test maps without saying how |

33 findings in all, with the misprints and the proofs the paper only sketches. The cited results the paper's proofs use are proved here
where Lean can reach them: Burkholder's inequality and square function inequality, Burkholder's
functions `u_q`, the sharpness of Burkholder's constant, Dacorogna's formula for the quasiconvex
envelope, Dacorogna's theorems on rank-one affine functions and quadratic forms, Rindler's lemmas,
and Kristensen's smoothing. Every proof follows the paper's argument except six recorded
departures, one of them, the route of Remark 4.5 for Theorem 1.2, approved by the user
([REPORT.md, Section 7](REPORT.md#7-departures-from-the-papers-proofs)).

## Trust

- `lake build` passes; no `sorry` outside the Challenges, no `axiom`.
- The repository's audit, [`scripts/Audit.lean`](../../scripts/Audit.lean), checks that every
  declaration uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and lists what each result
  depends on ([REPORT.md, Section 8](REPORT.md#8-what-each-result-depends-on)).
- The route check, with [`paper_routes.tsv`](paper_routes.tsv) and
  [`route_differences.tsv`](route_differences.tsv), checks that each proof uses the results that
  the paper's proof cites.
- Comparator accepts the Solution against the Challenge ([`comparator.json`](../../palomar/Cassese/comparator.json)).
- Independent AI agents checked the statements against the TeX source twice, the formal proofs
  against the paper's, and the report. No person has reviewed the proofs.

## Building and Palomar

This paper is its own Palomar submission: [`palomar/Cassese/`](../../palomar/Cassese) holds the
Challenge, the Solution, `comparator.json` and [`formalization.yaml`](../../palomar/Cassese/formalization.yaml),
named by the workflow [`palomar_preflight_cassese.yml`](../../.github/workflows/palomar_preflight_cassese.yml).
From the repository root:

```sh
lake exe cache get && lake build
lake env lean scripts/Audit.lean
python3 scripts/route_check.py check docs/Cassese/paper_routes.tsv --accept docs/Cassese/route_differences.tsv
lake env lake comparator --config=palomar/Cassese/comparator.json
```

| Path | Content |
| --- | --- |
| [`Morrey/Cassese/`](../../Morrey/Cassese) | the library: `Defs` (the definitions the Challenge copies, and most named hypotheses; [`DragicevicL4Bound`](../../Morrey/Cassese/Hypotheses.lean#L146) is in `Hypotheses`, two unused ones in `Toolkit`), `Introduction` (§1), `Toolkit` (§2), `TwoByM` (§4), `TwoByThree/` (§5), `NonLocality` (Cor 5.2), `Square/` (§6), `FourByTwo` (§7), `Bridges` (to Šverák's and the textbook definitions), `Sverak` (Šverák's example in Cassese's terms), `Hypotheses`, `Lifting`, `Rademacher` |
| [`Morrey/Common/External/`](../../Morrey/Common/External) | the cited results: Burkholder, Rindler, Dacorogna, Kinderlehrer–Pedregal, Kristensen (statements of Kirchheim–Kristensen and Osękowski for context) |
| [`Morrey/Common/Basic/`](../../Morrey/Common/Basic) | general mathematics: the calculus-of-variations definitions of the cited results, Fourier series of Lipschitz periodic maps, separately convex functions |
| [`palomar/Cassese/`](../../palomar/Cassese) | the Palomar submission |
| this directory | the report, the credits, the routes |

## Credits

- Formalized by Claude (Anthropic), with Claude Code, at the request of The-Anh Vu-Le, following
  the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure,
  independently of the author's own Lean formalization. No person has reviewed the proofs. See
  [CREDITS.md](CREDITS.md).
- License: Apache-2.0 ([`LICENSE`](../../LICENSE)).
