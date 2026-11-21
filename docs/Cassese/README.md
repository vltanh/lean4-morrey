# Cassese (2026): Morrey's problem in `ℝ^{2×m}`, in Lean (in progress)

One of the papers on Morrey's problem formalized in this repository; the
[overview](../../README.md) describes the problem, the state of each case and how the papers relate.

G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*,
[arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3) (16 September 2026), a preprint, claims
rank-one convex integrands on `ℝ^{2×m}` that are not quasiconvex. With Šverák's theorem
([Šverák](../Sverak/README.md)) this would leave `2 × 2` as the only size in which Morrey's problem can
have a positive answer. The paper also answers the homogeneous problem of Kirchheim and Kristensen
negatively: `p`-homogeneous, rank-one convex integrands that are nowhere quasiconvex, at every
exponent `p > 1` in suitable sizes, and at `p = 4` in every size above `2 × 2`.

**Status: the statements are written and checked; the proofs are not.** Every numbered result of
the paper, and the unnumbered claims its argument uses, is stated in Lean, in the paper's own
definitions, and was checked against the TeX source by two independent agents. The main theorems
are conditional: the paper cites deep results of martingale theory and Banach-space geometry that
no Lean library has, and each is a named hypothesis of the theorems whose proofs use it.

## What is proved

- Šverák's example in Cassese's definitions, as the paper's Section 1.1 states it: for every small
  `ε > 0` there is `k` such that Šverák's integrand is rank-one convex and not quasiconvex at `0`
  ([`sverak_example`](../../Morrey/Cassese/Sverak.lean#L32), from the formalization of Šverák's paper).
- Bridges between Cassese's definitions and Šverák's (rank-one convexity on segments and along
  lines; Lipschitz test maps on the cube and smooth test maps on a domain), and with the textbook
  forms in which the cited results are stated ([`Bridges.lean`](../../Morrey/Cassese/Bridges.lean)).
- The orthogonal projection onto the subspace `L₃` of Section 5, and that `L₃` satisfies the
  hypothesis of Lemma 5.1.

## The main theorems and what they assume

| Paper | Lean | Statement | Assumes |
| --- | --- | --- | --- |
| Theorem 1.2 | [`theorem1_2`](../../Morrey/Cassese/Introduction.lean#L86) ⭐ | every `p > 1`: on `ℝ^{2×m}`, `m ≥ m₀(p)`, a `p`-homogeneous, rank-one convex, nowhere quasiconvex integrand | Pisier's and Yaroslavtsev's UMD bounds, the HNVW extrapolation |
| Theorem 1.3 | [`theorem1_3_a`](../../Morrey/Cassese/Introduction.lean#L95), [`theorem1_3_b`](../../Morrey/Cassese/Introduction.lean#L103) ⭐ | a quartic homogeneous polynomial on `ℝ^{2×3}`, rank-one convex and nowhere quasiconvex; and for `p` near `4` | Burkholder's inequality |
| Theorem 1.4 | [`theorem1_4`](../../Morrey/Cassese/Introduction.lean#L115) ⭐ | every `p > 1`: on `ℝ^{d×d}`, `d ≥ d₀(p)`, a conjugation- and transposition-invariant example | Burkholder's square function inequality, HNVW extrapolation, Randrianantoanina, Cox–Veraar decoupling, Pisier–Xu, Kahane–Khintchine |
| Theorem 1.5 | [`theorem1_5`](../../Morrey/Cassese/Introduction.lean#L129) ⭐ | every `p ≠ 2`: an example on `ℝ^{4×2}` | Burkholder's inequality, transference, Dragičević's lower bound |
| Corollary 1.6 | [`corollary1_6`](../../Morrey/Cassese/Introduction.lean#L139) ⭐ | a nonnegative 1-homogeneous rank-one convex integrand on `ℝ^{4×4}`, not quasiconvex at a matrix of rank two | as Theorem 1.5 |
| Corollary 5.3 | [`corollary5_3`](../../Morrey/Cassese/TwoByThree.lean#L227) ⭐ | the transposed quartic on `ℝ^{3×2}` | Burkholder's inequality |
| Section 1.1, lines 251–254 | [`morrey_landscape`](../../Morrey/Cassese/Introduction.lean#L149) ⭐ | with Šverák: Morrey's problem fails in every size `d × m` with `d, m ≥ 2` except `2 × 2` | Burkholder's inequality |
| Lines 254–256 | [`homMorrey_landscape`](../../Morrey/Cassese/Introduction.lean#L159) ⭐ | at `p = 4`, the homogeneous problem fails in every such size except `2 × 2` | Burkholder's inequality |

⭐ in [`Challenge.lean`](../../palomar/Cassese/Challenge.lean), with a check of the definitions ([`projL3_mem`](../../Morrey/Cassese/TwoByThree.lean#L61)). The
named hypotheses are defined in [`Defs.lean`](../../Morrey/Cassese/Defs.lean), each with its source; the results the
project could prove (Rindler's and Dacorogna's lemmas, the Kirchheim–Kristensen theorem as context)
are stated in [`External/`](../../Morrey/Common/External).

## What comes next

The proofs, in order of value and feasibility, from the inventory of the paper:

- Theorem 1.3 (a) and Corollary 5.3, the `2 × 3` quartic and its transpose: large but elementary.
  With Šverák's theorem they give [`morrey_landscape`](../../Morrey/Cassese/Introduction.lean#L149) and [`homMorrey_landscape`](../../Morrey/Cassese/Introduction.lean#L159). Burkholder's
  inequality enters only through Lemma 5.1, at exponent 4.
- Theorem 1.2: large but feasible through the elementary route of the paper's Remark 4.5
  (Burkholder's scalar function instead of UMD constants).
- Theorem 1.4 at `p = 4`, `d ≥ 588`: feasible through Proposition 6.6 and Corollary 6.4. General
  `p` needs non-commutative Khintchine inequalities and Schatten-class UMD bounds, out of reach.
- Theorem 1.5 and Corollary 1.6: need Burkholder's inequality and Dragičević's bound for powers of
  the Beurling–Ahlfors transform.

No statement of the paper was found false. The inventory and the two reviews found gaps (the
uniformity in `p` that Theorem 1.3 (b) needs, an unstated cancellation in Lemma 5.1, the constant
`κ = 2` of Section 5 asserted without proof, Proposition 6.6 and Corollary 5.2 without proof);
they will be the report's findings.

## Building

From the repository root, on this branch:

```sh
lake exe cache get && lake build
```

The shared audit fails on this branch until Cassese's proofs are done (the statements carry
`sorry`); the finished papers, Pedregal's and Šverák's, are on `main`.

## Credits

- Formalized by Claude (Anthropic), with Claude Code, at the request of The-Anh Vu-Le, following
  the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure,
  independently of the author's own Lean formalization. No person has reviewed the statements.
- License: Apache-2.0 ([`LICENSE`](../../LICENSE)).
