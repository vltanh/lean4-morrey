# Cassese (2026) in Lean: audit report

Paper: G. Cassese, *A solution to Morrey's problem in `ℝ^{2×m}`*,
[arXiv:2608.03488v3](https://arxiv.org/abs/2608.03488v3) (16 September 2026), a preprint. The
audit was made against the arXiv LaTeX source of that version. Section, result and equation numbers
are the paper's, and "lines" are lines of its TeX source. Labels in backticks are the paper's TeX
labels; labels `cs-…` are ours, for results the paper does not label
([`paper_routes.tsv`](paper_routes.tsv)). The main theorems are numbered 1.2–1.5 because
Theorem 1.1 is Kirchheim and Kristensen's cited theorem. The repository also formalizes Šverák
(1992) and audits Pedregal's claimed `2 × 2` proof ([overview](../../README.md)). This
formalization was written independently of the author's own Lean code, which was not consulted.

Status of the formalization:

- **Every result of the paper is proved**: Theorems 1.2–1.5, Corollary 1.6, the consequences
  drawn after Theorem 1.3 (only `2 × 2` remains, for Morrey's problem and, at `p = 4`, for the
  homogeneous problem), every numbered lemma, proposition and corollary (Proposition 2.6, quoted
  from Osękowski as context, aside), and the claims of the running text that the proofs use. Theorem 1.2 is proved by the paper's own route (Section 4.4,
  through UMD constants); the elementary route of Remark 4.5 is formalized as a second theorem,
  `theorem1_2_elementary`.
- **The results of other works that the proofs use are proved too.** Each is stated in its
  source's terms in `Morrey/Common/External/<Source>/` and restated in the paper's terms in
  `Morrey/Cassese/Hypotheses.lean`. The proofs come from three Lake packages written for this
  formalization: [lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis),
  [lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability) and
  [lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations).
- **Nothing is assumed.** No statement takes a result of another work as a hypothesis. Two cited
  theorems that the paper quotes only as context, Kirchheim–Kristensen's Theorem 1.1 and
  Osękowski's characterization of Hilbert spaces (Proposition 2.6), are stated and not proved; no
  proof uses them. Conjecture 1 is stated.
- `lake build` passes, with no `sorry` outside the Challenges and no `axiom`.
  [`scripts/Audit.lean`](../../scripts/Audit.lean) checks that every declaration of the
  repository's library (3,549 at commit `6ae4899`, for the three papers and the shared code) uses
  only `propext`, `Classical.choice` and `Quot.sound`, and lists the results of other works that
  each result of the paper uses (Section 8). Each package has an audit of the same kind.
- [`palomar/Cassese/Challenge.lean`](../../palomar/Cassese/Challenge.lean) states the main results
  in Mathlib's vocabulary, with no hypotheses beyond the paper's;
  [`Solution.lean`](../../palomar/Cassese/Solution.lean) proves them from the library, and
  Comparator compares the two ([`comparator.json`](../../palomar/Cassese/comparator.json)).
- No statement of the paper had to change (Section 4).
- Every proof follows the paper's argument, except three that repair a gap or a false step
  (Section 7). The cited results follow their sources' proofs, or, where a source was not
  accessible, a named argument from an open source (Section 7).

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

The paper constructs rank-one convex integrands on `ℝ^{2×m}`, `m ≥ 3`, that are nowhere
quasiconvex. With Šverák's theorem, this leaves `2 × 2` as the only size in which Morrey's problem
can have a positive answer. It also answers Kirchheim and Kristensen's homogeneous problem
negatively in many sizes: there are `p`-homogeneous, rank-one convex, nowhere quasiconvex
integrands. Its proofs rest on Burkholder's martingale inequalities, UMD theory for `L^p` and the
Schatten classes, the non-commutative Khintchine inequality, transference and Dragičević's lower
bound for the Beurling–Ahlfors transform, and the standard facts of the calculus of variations;
all are proved here.

The audit found no false statement. The findings are steps that the paper leaves to the reader or
only sketches, one intermediate claim that is false under the reading that the proof around it
needs, and misprints:

| Kind | Findings |
| --- | --- |
| Errors | none: no statement is false. One intermediate claim, at lines 661–663, is false under the reading of prelaminates that Proposition 2.4 needs (E10) |
| Gaps that change what must be proved | E4: Theorem 1.3 (b) needs the constants of Lemma 5.1 (1) uniform in `p`; E10: Proposition 2.5 "⇐" rests on the claim of lines 661–663; E27: Remark 6.3 and Proposition 6.5 at `q = ∞` need Kahane–Khintchine constants polynomial in `q` |
| Results stated without proof | E5: `κ = 2` for `𝓛₃`; E6: Proposition 6.6; E8: Proposition 2.3; E19: Corollary 5.2 |
| Proofs only sketched | E17: Corollary 5.3; E26: Remark 4.5; E31: Corollary 6.4; E32: Corollary 7.2 |
| Steps left to the reader | E2, E3, E7, E9, E16, E21–E25, E28, E29, E33–E35 (Section 3) |
| Claims without proof, not formalized | E18: Corollary 1.6 for `p > 2` |
| Not errors | E14: no value of `n₀` in Proposition 4.3; E20: `q₃(∇u) ∈ L¹` |
| Misprints and wording | E11, E12, E13, E15 |
| Missing hypotheses | none (Section 4) |
| Redundant hypotheses | eight, among them the evenness in Lemma 5.1 (2), which Remark 5.2 needs to drop, and `ρ > 0` in Proposition 7.2 (Section 5) |
| Use of cited results | correct, with five reservations: E27, E30, Randrianantoanina's Corollary 4.5, Kristensen's growth bound, Dragičević's theorem for `p < 2` (Section 2) |

## 2. Results from prior work and how the paper uses them

### Proved in `Morrey/Common/External/`

Each result is stated in its source's terms in `Morrey/Common/External/<Source>/`, whose README
gives the source, the statement, the argument and the users, and is proved there from the package
named in the last column: HA = `lean4-harmonic-analysis`, BP = `lean4-banach-probability`,
CV = `lean4-calculus-of-variations`. Section 7 says which argument replaces a source that was not
accessible.

| Result | Where the paper uses it | Source cited by the paper | Lean |
| --- | --- | --- | --- |
| Lemma 2.1: a rank-one convex function is locally Lipschitz | Propositions 2.3–2.5, Corollary 1.6 | Rindler 2018, Lemma 5.6 | `External.Rindler.lemma5_6` (CV) |
| Lemma 2.2: quasiconvexity implies rank-one convexity, does not depend on the domain, and may be tested with periodic maps | Proposition 2.3, the thresholds, the lifting, Propositions 6.1, 7.2 | Rindler, Propositions 5.1, 5.3; Dacorogna 2008, Propositions 5.11, 5.13 | `External.Rindler.rankOneConvex_of_quasiconvex`, `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic` (CV) |
| Proposition 2.1: the rank-one convex envelope by prelaminates | Propositions 2.3, 5.1 | Pedregal 1993, §4; Dacorogna 2008, Theorem 6.10 | `proposition2_1`, in the library, by the paper's own route of Remark 2.1 (through Proposition 2.4) |
| Proposition 2.2: Dacorogna's formula for the quasiconvex envelope | line 559, Propositions 2.3, 4.3 | Kinderlehrer–Pedregal 1991, Proposition 8.1 | `External.KinderlehrerPedregal.dacorognaFormula_holds` (CV) |
| Theorem 2.3 (1): Burkholder's inequality, Hilbert-valued | Lemma 5.1, Theorem 1.3 (b), Proposition 7.1 | Osękowski 2012, Theorem 3.5 (Burkholder 1984) | `External.Burkholder.inequality` (BP) |
| Theorem 2.3 (2): Burkholder's square function inequality | Proposition 6.5 | Osękowski 2012, Theorem 8.6 | `External.Burkholder.squareFunction` (BP) |
| Proposition 2.7 (1): extrapolation of the UMD property, with constants | Section 4.4 (Theorem 1.2), Proposition 6.5, Corollary 6.1 | HNVW I, Theorem 4.2.7 | `External.HNVW.theorem4_2_7` (BP) |
| Proposition 2.7 (2): `UMD₂(S_q) ≤ C (q* − 1)` | Propositions 6.2, 6.5, Remark 6.3 | Randrianantoanina 2002, Corollary 4.5 | `External.Randrianantoanina.remark4_6`, with `External.Randrianantoanina.corollary4_5` (BP) |
| Proposition 2.7 (3): `L^p` is UMD | Section 4.2 (Theorem 1.2) | Pisier 2016, Corollary 5.22 | `External.Pisier.corollary5_22` (BP) |
| Proposition 2.7 (4): the dyadic and the general UMD constants agree | no proof | HNVW I, Theorem 4.2.5 | `External.HNVW.theorem4_2_5` (BP) |
| Proposition 2.7 (5): `UMD_p ≤ UMD_{ℂ,p} ≤ (π/2) UMD_p` | Section 4.2 (Theorem 1.2) | Yaroslavtsev 2018, Lemma 3.2 | `External.Yaroslavtsev.lemma3_2` (BP) |
| Proposition 2.7 (6): zig-zag concave functions bound the UMD constants | no proof | HNVW I, Theorem 4.5.6; Yaroslavtsev 2018, Proposition 3.7 | `External.HNVW.theorem4_5_6`, `External.Yaroslavtsev.proposition3_7` (BP) |
| Proposition 2.8: decoupling with the UMD constant | Propositions 6.2, 6.5, Remark 6.3 | Cox–Veraar 2007; HNVW I, Proposition 4.2.3 | `External.CoxVeraar.decoupling` (BP) |
| (13), (14): Burkholder's functions `u = u₆` and `u_q` | Propositions 4.2, 4.3; Remark 4.5 | Burkholder 1988 | `External.Burkholder.scalarFunction_holds`, `External.Burkholder.scalarFunctionQ_holds` (BP) |
| rank-one affine functions are affine combinations of minors, and minors are quasiaffine | Proposition 5.1 | Dacorogna 2008, Theorem 5.20 | `External.Dacorogna.rankOneAffineMinors_holds`, `External.Dacorogna.minor3_quasiaffine` (CV) |
| rank-one convex quadratic forms are quasiconvex | Proposition 5.1 | Dacorogna 2008, Theorem 5.25 (i) | `External.Dacorogna.quadraticForm_quasiconvex` (CV) |
| a smoothing that keeps the failure of quasiconvexity | Corollary 5.2 | Kristensen 1999, Proposition 2; Heinz 2008 | `External.Kristensen.smoothing_holds` (CV) |
| Proposition 6.3: the non-commutative Khintchine inequality | (31) | Pisier–Xu 2003, Theorem 6.1; Lust-Piquard 1986; Lust-Piquard–Pisier 1991 | `External.PisierXu.theorem6_1` (BP) |
| Proposition 6.4: the Kahane–Khintchine inequality | (31) | HNVW II, Theorem 6.2.4 | `External.HNVW.theorem6_2_4_seminorm` (BP) |
| the hypercontractive constants `κ_{q,p} ≤ √((q − 1)/(p − 1))` | Remark 6.3, Proposition 6.5 at `q = ∞` | none (E27); Borell 1979 | `External.Borell.kahaneKhintchine_hypercontractive` (BP) |
| the sharpness of `p* − 1` for dyadic `±1`-transforms | Corollary 6.3, lower bound | "see also [Cassese 2025]" (E30) | `burkholderSharpness_holds`, in the library (`Morrey/Cassese/Square/Sharpness.lean`) |
| the bound `C^{rc} ≤ (p* − 1) sup ‖Q‖/‖P_ρ‖` | Proposition 7.1 | "the results of [Cassese 2025]" | from Burkholder's inequality, in `proposition7_1` |
| transference: `‖𝓑^k‖_{L^p(ℝ²)} ≤ ‖𝓑^k‖_{L^p_0(𝕋²)}` | Proposition 7.2, lower bound | HNVW I, Corollary 5.7.6 | `External.HNVW.transference_beurlingPow` (HA) |
| Dragičević's lower bound `‖𝓑²‖_p ≥ κ₂(p*) > p* − 1`, and `‖𝓑²‖₄ ≥ 21/5` | Theorem 7.1, Corollary 7.2 | Dragičević 2011, Theorem 1.1 | `External.Dragicevic.theorem1_1_two_pStar`, `External.Dragicevic.theorem1_1_two` (HA) |

Quoted for context, stated and not proved, used by no proof: Kirchheim–Kristensen 2016 (the
paper's Theorem 1.1, `External.KirchheimKristensen.Theorem1_1`) and Osękowski 2012, Theorem 3.24
(Proposition 2.6, `External.Osekowski.HilbertCharacterization`).

### Assumed

Nothing.

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| the Schatten-norm facts (1)–(3) of Section 1.5, "immediate consequences of the definitions (see also [Bhatia, Chapter 4])", and the triangle inequality | Section 6 | proved: `schattenNorm_mul_self` (fact (1), for every `q ≥ 1`: E2), `schattenNorm_add_le` (through doubly substochastic matrices), Weyl's monotonicity by Courant–Fischer (`Morrey/Cassese/Square/Weyl.lean`) |
| the Bernstein–Doetsch theorem: a midpoint convex function, locally bounded above, is convex | lines 643–646 (Proposition 2.4) | proved, in `tk_midpoint_principle` |
| the uniform convexity of `\|·\|^p` | (29) | proved, `tbt2_gain` (E3) |
| the strong law of large numbers with infinite mean, Fatou's lemma, Jensen's inequality | Lemma 4.2 | Mathlib, in `lemma4_2` |
| mollification of continuous and of Lipschitz functions | Propositions 4.2, 7.2, Remark 4.5, Corollary 1.6 | `Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean`; `CalculusOfVariations.mollifyPi` (CV) |
| the implicit function theorem; the change of variables `(ζ, τ) ↦ (w, t)` | Proposition 5.2 | Mathlib's `ContDiffAt.implicitFunction`; the change of variables is proved in `Morrey/Cassese/TwoByThree/Witness.lean` |
| Hölder's inequality; polar coordinates | Theorem 1.3 (a), Corollaries 5.3, 5.4 | Mathlib |
| the multinomial theorem and the orthogonality of the characters of the torus | Proposition 6.1 | Mathlib, in `Morrey/Cassese/Square/Torus.lean` |
| Fourier series of smooth periodic functions; `∂̄` is invertible on smooth mean-zero functions; `𝓑(∂̄w) = ∂w` | Proposition 7.2 | HA (`UnitAddTorus.exists_dzbarPi_eq`, `periodicMultiplier_beurlingSymbol_dzbarPi`) |
| distributional second derivatives on `ℝ`: the Leibniz rule, and convexity from a nonnegative second derivative | Corollary 1.6 | CV (`CalculusOfVariations.convexOn_of_distribNonneg`) |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Theorem 2.3 (Burkholder) | Sections 5–7 | correct. The paper asks for a separable Hilbert space; the proofs do not use separability (Section 5) |
| (13), (14) (Burkholder's `u`, `u_q`) | Proposition 4.2, Remark 4.5 | correct |
| Lemma 2.1 (Rindler) | Propositions 2.4, 2.5, the envelopes | correct in Rindler's form, for every real-valued rank-one convex function; the paper states it for integrands and applies it to an infimum `G` before `G` is known to be one (E21) |
| Lemma 2.2 (Rindler, Dacorogna) | Sections 2, 4, 6, 7 | correct; the domain must be nonempty, which the paper does not say |
| Proposition 2.1 (Pedregal, Dacorogna) | Propositions 2.3, 5.1 | correct; the paper's Remark 2.1 removes the sources' assumption that `f` is bounded below |
| Proposition 2.2 (Kinderlehrer–Pedregal) | line 559 | correct; the passage from the ball of the formula to the cube of Definition 2.1 is silent (E22) |
| Dacorogna, Theorems 5.20 and 5.25 (i) | Proposition 5.1 | correct |
| Kristensen, Proposition 2 | Corollary 5.2 | applied loosely but correctly: the paper's form asks `c ‖A‖² ≤ h(A)` for every `A`, which Kristensen's function need not satisfy, since the cut-off polynomial can be negative; adding a constant repairs it and changes neither the second derivatives nor quasiconvexity at `0` |
| Proposition 2.7 (1), (3), (5) | Section 4.2 | correct. Remark 4.2 writes `UMD_p` where the argument gives `UMD_{ℂ,p}`, harmless under `≲` (E11) |
| Proposition 2.7 (2) (Randrianantoanina) | Propositions 6.2, 6.5 | applied loosely but correctly: Corollary 4.5 bounds `UMD_q(S_q)` by `C q²/(q − 1)`; the bound at the exponent `2`, linear in `q*`, is the source's Remark 4.6 (1), through extrapolation |
| Proposition 2.8 (Cox–Veraar, HNVW) | Propositions 6.2, 6.5 | correct; the case used is the Paley–Walsh case of Cox–Veraar's statement |
| Propositions 6.3, 6.4 | (31) | correct; but Remark 6.3 and Proposition 6.5 at `q = ∞` need Kahane–Khintchine constants that grow polynomially in `q`, which Proposition 6.4 as stated does not give and for which no source is named (E27) |
| the sharpness of `p* − 1` | Corollary 6.3 | correct, with only "see also [Cassese 2025]" as a source (E30) |
| transference (HNVW I, Corollary 5.7.6) | Proposition 7.2 | correct for the direction used (from `𝕋²` to `ℝ²`); the exact form of the corollary could not be checked, since the book was not accessible |
| Dragičević, Theorem 1.1 | Theorem 7.1, Corollary 7.2 | applied loosely but correctly: the theorem is stated for `p > 2` (as read in Dragičević's lecture notes); for `p < 2` it follows from the duality `‖𝓑^n‖_p = ‖𝓑^n‖_{p'}` of Carbonaro–Dragičević–Kovač, §1.3.1, the paper's "see also [Dragicevic1]"; and `κ₂(p*) − (p* − 1) = (p* − 1)(p* − 2)/(p* + 1) > 0` for `p* > 2` |

The other citations give context and are used in no proof: the history of Morrey's problem and of
Burkholder's method in the calculus of variations (Sections 1, 2 and 8, Remarks 2.3 and 3.1),
Grabovsky's examples, Gennaioli–Rindler, Guerra–Kristensen, and the literature on Iwaniec's
conjecture.

## 3. Errors and gaps in the paper

No statement is false. The items below are gaps (steps that need an argument the paper does not
give, or only sketches), one intermediate claim that is false under a natural reading (E10), and
misprints, collected at the end. The numbers are those of the inventory of the paper, which the
docstrings of the code cite; E1 of the inventory is the remark on numbering in the preamble, not a
finding. In every case the result holds, and the formalization supplies the missing argument.

### E2. Lines 375–377, 2350–2378: Schatten fact (1)

Fact (1) of Section 1.5, `‖A²‖_{S_q} = ‖A‖²_{S_{2q}}` for self-adjoint `A`, is stated for `q ≥ 2`,
but the proof of Proposition 6.2 uses it at the exponent `q/2`, below `2` when `q < 4`. The
identity holds for every `q ≥ 1`, since the singular values of `A²` are the squares of those of
`A`. The formalization proves it for `q ≥ 1` (`schattenNorm_mul_self`).

### E3. Lines 1914–1929: Lemma 5.1 (2), inequality (28)

Comparing `E f(π M_n)` with `E f(M̃_n)` needs the first-order cancellation
`E [Df(X) · 𝓔_n] = 0` (`𝓔` is a martingale started at `0`, and `X = π M_0` is deterministic), which
the paper does not mention; without it a term `|X|^{p−1} E |𝓔_n|` appears that (28) does not
contain. The remainder also needs a Lipschitz bound on `Df` across the origin,
`‖Df(Y) − Df(Y')‖ ≤ C max(|Y|, |Y'|)^{p−2} |Y − Y'|`, which follows from the `C²` regularity and the
homogeneity. Both are supplied in `lemma5_1_part2`, which follows the paper's `n`-step argument;
(29), "uniform convexity of `|·|^p`", neither proved nor cited in the paper, is proved there too.

### E4. Lines 2031–2046: Theorem 1.3 (b)

The proof ends "by continuity of the rank-one convexity and quasiconvexity estimates" in `p`.
This needs the constant `Λ` of Lemma 5.1 (1), which is stated for a fixed `p`, to be uniform for
`p` near `4`, and the cut-off of the witness to be fixed before `p` varies: for `p < 4` the
uncut integrand is positive far away, since `r* − 1 > 1` and `|H|/|2D| → 1`. The theorem holds:
the formalization proves Lemma 5.1 (1) with explicit constants (`lemma5_1_part1_quant`), so that
`Λ₀(p, δ)` is continuous in `p`, fixes `K`, `δ` and the cut-off first, and passes to the limit in
`p` by dominated convergence (`twoByThree_theorem1_3_b_witness`; Section 7).

### E5. Lines 1978–1979: `κ = 2` for `𝓛₃`

"`𝓛₃` satisfies the hypothesis of Lemma 5.1 with `κ = 2`" has no proof. It is true: for
`R = v wᵀ`, the correction `R_L = x v uᵀ`, `u = (v₀² − v₁², 2 v₀ v₁, |v|²)`,
`x = ⟨w, u⟩/(2 |v|⁴)`, lies in `𝓛₃` and gives `|π R − R_L|² ≤ 2 |π^⊥ R|²`, so even `κ = √2`
(`tbt_correction_identity`); numerically the best constant is about `1.054`. When `⟨w, u⟩ = 0`, a
small `x ≠ 0` keeps `R_L` of rank one, and `κ = 2` covers it (`L3_rankOneCorrection`).

### E6. Lines 2558–2563: Proposition 6.6

Proposition 6.6 has no proof. It is correct: for `u_i = Σ_{j≠i} cos(x_i − x_j)`, exact
trigonometric moments give `E ‖Skew ∇u‖⁴_{S_4} = d(d − 1)(d² − d + 1)/8` and
`E ‖Sym ∇u‖⁴_{S_4} = d(d − 1)(6d − 9)/8`. Proved in `proposition6_6`.

### E7. Lines 2683–2684: Corollary 6.4

The bound `⟨W, Z⟩ ≤ (1/3)(2ae + 2bc) + (2/3)(2aρ)` does not follow "by the assumption on
`(E, D)`", which gives only `a ≤ b`, `c ≤ e`. It holds by a trace argument,
`tr(YEXD) = −⟨YD, EX⟩ ≤ bc` and `tr(YEDX) = ⟨XD, YE⟩ ≤ ae`, together with
`⟨W, Z⟩ ≤ ‖W‖ ρ ≤ 2aρ`. Supplied in `corollary6_4`.

### E8. Lines 562–578: Proposition 2.3

Proposition 2.3 has no proof ("follows directly"). The direction "`f` quasiconvex at `0` ⇒ `f^{rc}`
quasiconvex at `0`" of (c) and the conjugation invariance of `f^{qc}` in (b) need Dacorogna's
formula (line 559) and Lemma 2.2 (ii); what the main theorems use is elementary. Proved: (a) and
(b) from the dual formulas of the envelopes, (c) through line 559 (`proposition2_3_a`,
`proposition2_3_b`, `proposition2_3_c`).

### E9. Lines 1406–1411: Proposition 5.1

Two steps are skipped: "`Q` is rank-one affine at `0`. It follows that `Q` is rank-one affine", and
"since `P''(0) = (P − Q)''(0)`, `P − Q` is rank-one convex". Both hold: a prelaminate centred at
`0` with an atom at an arbitrary `A`, split once more along `±hR`, gives
`Q(A + hR) + Q(A − hR) = 2 Q(A)`, and the same device gives the Legendre–Hadamard condition for
the quadratic part. Supplied in `proposition5_1` (Section 7).

### E10. Lines 504–530, 661–663: prelaminates and Proposition 2.5

Definition 2.4 does not say whether the atoms `A_i` of `Σ c_i δ_{A_i}` are distinct, and neither
reading makes both Proposition 2.4 and Proposition 2.5 work. The gluing in the proof of
Proposition 2.4 ("a midpoint split followed by dyadic splittings at `B` and `C`") needs repeated
atoms: with distinct atoms, coinciding atoms of `μ_B` and `μ_C` are split together. With repeated
atoms, the claim of lines 661–663, "every dyadic prelaminate is the law of a rank-one Rademacher
martingale", is false: splitting a third of `δ₀` with `t = 1/2` gives the weight `1/6`, which is
not dyadic. Only a reading on split trees makes both steps work. Proposition 2.5 still holds: the
formalization reads Definition 2.4 with repeated atoms and proves "⇐" by running the argument of
Proposition 2.4 on the infimum of `E f(M_N)` over rank-one Rademacher martingales
(`proposition2_5`; Section 7).

### E14. Lines 1355–1366: Proposition 4.3

No value of `n₀` is given. Not an error: the proofs are existence proofs. With `p = 3`, `q = 6`,
`C^{qc}(3, 6, n)` grows like `n^{1/30}` (Remark 4.2), so a heuristic gives `n` of order `10^{80}`
to pass `5⁴`.

### E16. Lines 1821–1832: Lemma 5.1, hypothesis (25)

The hypothesis asks for a rank-one `R_L ∈ 𝓛`. When `π R = 0` the natural choice is `R_L = 0`,
which the hypothesis excludes; a rank-one `R_L` of small norm serves as well, as long as `𝓛`
contains a rank-one matrix, and the proof only uses increments of rank at most one. The
formalization keeps the hypothesis as stated (`HasRankOneCorrection`), and meets it for `𝓛₃` with
`κ = 2` (E5).

### E17. Lines 2090–2102, 2121–2123: Corollary 5.3

The proof is a sketch: "cutting off `φ` smoothly at radii `1` and `R`", and constants `c, C > 0`
that are only said to exist. The formalization completes it with explicit cut-offs and the
constants `c = 75/8`, `C = 4·10⁶`, `δ₀ = 75/(64·10⁶)` (`corollary5_3`); a numerical evaluation of
the paper's "direct calculation" gives the sharper `c ≈ 1029.8`, `C ≈ 62938`.

### E18. Lines 2956–2966: Corollary 1.6 for `p > 2`

The variant for `p > 2` (`N_p` and `G = Λ N_p + det(YᵀY)^{p/2} N_p^{1−3p} F`) is asserted ("a
similar construction goes through") without proof. `N_p` degenerates where `X` or `Y` vanishes,
so the rank-one convexity estimate is not a copy of the case `p < 2`. Not formalized.

### E19. Lines 2051–2065: Corollary 5.2

Corollary 5.2 has no proof, only references to smoothing arguments. Proved, by Kristensen's
smoothing applied to the quartic of Theorem 1.3 lifted to `ℝ^{2×m}` (`corollary5_2`;
`External.Kristensen.smoothing_holds`).

### E20. Lines 1602–1614, 1995: `q₃(∇u) ∈ L¹`

Proposition 5.2 asserts `q₃(∇u) ∈ L¹(ℝ³)`, and the proof of Theorem 1.3 (a) uses it through
`I = ∫_{ℝ³} q₃(∇u) < 0`. It holds: the paper's formula gives `I ≈ −0.3636`, which a direct
quadrature confirms. Not an error. The formalization proves the integrability
(`proposition5_2`) and follows the paper's proof of Theorem 1.3 (a), with `I` and Hölder's
inequality (`twoByThree_not_quasiconvexAt_qDeltaLambda`). Theorem 1.3 (a) can avoid the
integrability (Section 11).

### E21. Lines 468–470, 616–659: the minorant `G` of Propositions 2.3–2.5

The minorant `G` is used as a competitor in `f^{rc}` (lines 643–658), so it must be an integrand,
and the paper does not say why it is one; Lemma 2.1, as the paper states it (for integrands), does
not apply before that is known. `G` is real-valued and rank-one convex, and Lemma 2.1 in Rindler's
form, for every real-valued rank-one convex function, makes it continuous. The formalization
proves Lemma 2.1 in that form (`External.Rindler.lemma5_6`).

### E22. Line 559: from the ball to the cube

Dacorogna's formula (Proposition 2.2) averages over the unit ball, and Definition 2.1 tests on the
unit cube; the passage, silent in the paper, needs Lemma 2.2 (ii). Supplied
(`quasiconvexAt_iff_exists_minorant`, with `External.Rindler.quasiconvexAtOn_iff`).

### E23. Lines 1047–1053: the limiting argument of Section 4.3

The "straightforward limiting argument" from Schwartz test maps to Definition 2.1 is not given.
Proved: a cut-off of `u_n`, Fatou's lemma, and a rescaling into the unit cube
(`twoByM_ratio_le_qcThreshold`, `twoByM_not_qc_explicitF`).

### E24. Lines 1891–1895: Lemma 5.1 (1)

"By homogeneity and Young's inequality" needs a Lipschitz bound on `g`, which is only continuous.
Uniform continuity on a compact set and homogeneity give the estimate (`lemma5_1_part1`).

### E25. Lines 1855, 1956, 1991: `δ = 1` in Lemma 5.1 (2)

Lemma 5.1 (2) is stated for `δ ∈ (0, 1)`, and the proof of Theorem 1.3 uses it for `0 < δ ≤ 1`.
Harmless: `q_{1,K} = q_{1/2,K} + ½ (|π A|² + K² |π^⊥ A|²)²`, a rank-one convex function plus a
convex one (`qDeltaLambda_rankOneConvex`).

### E26. Lines 1367–1375: Remark 4.5

The elementary route to Theorem 1.2 is sketched without the function `U` or the constant `K`
("such a `U` can also be constructed"). Supplied: `q = p + 3`, `U = R^{p/q} − K B^{p/q}` with
Burkholder's `u_q`, `K = 2 (q − 1)^{p+1}/(p − 1)` (`theorem1_2_elementary`).

### E27. Lines 2425–2437, 2477–2479: Kahane–Khintchine constants

Remark 6.3, and Proposition 6.5 at `q = ∞` ("all the implied multiplicative constants in the above
inequalities are at most polynomial in `q`"), use (31) with constants that grow at most
polynomially in `q`. This needs the Kahane–Khintchine constants `κ_{q,p}` to grow so, which
Proposition 6.4 as stated (constants `k_{p,q}`, HNVW II, Theorem 6.2.4) does not give, and the paper
names no source. It holds by Borell's hypercontractive bound
`κ_{q,p} ≤ √((q − 1)/(p − 1))`, proved here (`External.Borell.kahaneKhintchine_hypercontractive`,
from O'Donnell's proof). Theorem 1.4 uses Proposition 6.5 only at `q = 4` and does not need it.

### E28. Lines 2807–2821, 2211–2216: Proposition 7.2

The inequality "`≤`" is argued with smooth periodic maps, while Lemma 2.2 tests with Lipschitz
periodic maps; the density step between them is not stated. It holds: the mollification of a
Lipschitz periodic map is smooth and periodic, its gradients converge almost everywhere and stay
bounded, and dominated convergence carries the inequality over
(`fourByTwo_qcThreshold_le_chainOpNorm`).

### E29. Lines 2489–2520: Corollary 6.1

The reduction from periodic to compactly supported Hessian test maps is not stated, and "the
calculation of Proposition 6.1" does not carry over: the skew part of `J D²φ` has two distinct
doubled singular values. Supplied, with matrices of rank at most `4` and `S₂` compared with `S₄`
(`not_hessianQuasiconvexAt_of_periodic`, `square_not_hessianQuasiconvexAt_of_periodic`).

### E30. Lines 2624–2633: Corollary 6.3, lower bound

The lower bound uses the sharpness of `p* − 1` for dyadic `±1`-transforms, with only "by choosing
the martingale-transform pair suitably (see also [Cassese 2025])" as a source. The sharpness goes
back to Burkholder (Bull. London Math. Soc. 17 (1985); it also follows from Ann. Probab. 12 (1984)
and Maurey's theorem); neither paper was accessible. Proved here by an explicit dyadic
construction, the standard extremal examples with a potential function
(`burkholderSharpness_holds`).

### E31. Lines 2658–2659, 2670: Corollary 6.4

The corollary is "only sketched", and `8/5 U ≥ ‖Y‖⁴ − 98 ‖X‖⁴` is left to "standard
calculations". Completed (`corollary6_4`, `corollary6_4_not_quasiconvexAt`).

### E32. Lines 2891–2892: Corollary 7.2

The zig-zag concavity of `U` and `2U ≥ ‖y‖⁴ − 130 ‖x‖⁴` are left to "standard calculations".
Proved (`corollary7_2`). The bound is the identity
`2U − (|y|⁴ − 130 |x|⁴) = (|y|² − 10 |x|²)²`; with `C₀⁴ = 1170` it gives
`f_{4,√2,C₀} − 𝒫 = (30 |P_{√2}|² − |Q|²)² ≥ 0`. The zig-zag concavity reduces to a polynomial
inequality in `|x|²`, `|y|²`, `Re⟨x, h⟩`, `Re(y k̄)`, `|h|²`, `|k|²` (`fourByTwo_U_core`). The
margin of `C₀ = 1170^{1/4}` under Dragičević's `21√2/5` is about 1.6 %.

### E33. Lines 2184–2185: Corollary 5.4

"The negativity and integrability estimates for `u` in Proposition 5.2 still apply": the proof
reuses estimates from inside the proof of Proposition 5.2, for another profile, `F'(z) = 1 + z`.
They hold; the formal proof reruns them for that profile (`corollary5_4`; a route difference
recorded in [`route_differences.tsv`](route_differences.tsv)).

### E34. Lines 2552–2554, 2660–2668: the invariances in Theorem 1.4 at `p = 4`

Theorem 1.4 at `p = 4` needs Corollary 6.4's quartic to be invariant under conjugation and
transposition, which the paper does not state. Proved (`theorem1_4_four`).

### E35. Lines 2945–2947: the witness of Corollary 1.6

The proof takes "a smooth periodic `φ : 𝕋² → ℝ⁴` satisfying `∫_{𝕋²} F(∇φ) < 0`" without saying
where it comes from. Since `F` is not quasiconvex at `0`, Lemma 2.2 gives a Lipschitz periodic
`φ`; a smooth one needs a density step. It holds: the mollifications of the Lipschitz witness are
smooth, Lipschitz and periodic, and by dominated convergence one of them still has
`∫ F(∇φ) < 0` (`corollary1_6`). This item is not in the inventory, hence its number.

### Misprints and wording: E11, E12, E13, E15

- E11 (line 1130): Remark 4.2 bounds `C^{rc}` by `UMD_p` where the argument gives `UMD_{ℂ,p}`;
  equivalent up to `π/2` (Proposition 2.7 (5)), so harmless under `≲`.
- E12 (lines 245, 1376): the TeX labels `thm:2x4` and `sec:2x4`, invisible in the PDF, are
  leftovers of v2; the content is `2 × 3`.
- E13 (lines 68, 242–243): the abstract and the introduction call the quartic "explicit", but it
  depends on unspecified `K` and `δ`.
- E15 (lines 1595–1596, 1722–1723): the wave equation that the proof mentions, `u_tt = Δu`
  (implied by `u_t = 2 conj(∂u)`), is never stated.

The constants of Corollary 6.3 (`d₀ = 588`, the least that works) check out.

## 4. Missing hypotheses

None. Every statement is formalized as printed, with the readings of Section 6.

## 5. Redundant hypotheses

The proofs do not use the following hypotheses. All but the last are kept in the Lean statements,
as the paper states them.

| Result | Hypothesis that the proof does not use | Lean |
| --- | --- | --- |
| Section 5.1: `q` is rank-one convex on `𝓛` (`cs-q-rc`) | `A ∈ 𝓛`: only the direction `R` must lie in `𝓛` | kept (`quarticQ_rankOneConvexOn_calL`) |
| Lemma 5.1 (2) | the evenness of `f`: "`p`-homogeneous" means `f(tX) = \|t\|^p f(X)` for every real `t` (lines 158–163), and the proof uses it only for `t > 0`. Remark 5.2 applies the lemma to Šverák's `−rst`, which is only positively homogeneous, so it needs this | kept (`lemma5_1_part2`), as the paper states it |
| Corollary 6.3, upper bound | `d ≥ 2` | kept (`corollary6_3_upper`) |
| Proposition 2.3 | the homogeneity in (a); the homogeneity and `p > 1` in (b), (c) | kept |
| Section 1.3: monotonicity of the homogeneous problem | `1 < p` | kept (`homMorreyPositive_mono`) |
| Theorem 2.3 | the separability of the Hilbert space | kept in `External.Burkholder.inequality` and `External.Burkholder.squareFunction`; `External.Burkholder.inequality_of_subordinate` and `External.Burkholder.squareFunction_of_martingale` do without it |
| Proposition 4.1 | the standing assumption `q > p + 2` of Section 4 | not assumed: `proposition4_1` asks only `1 < q` (Lemma 4.1 has no `q`) |
| Proposition 7.2 | `ρ > 0`, the setting of Section 7 | dropped: `proposition7_2` holds for every real `ρ`, a generalization of the paper's statement. Its lower bound, `proposition7_2_lower`, keeps `ρ > 0`, which its proof uses (`‖ρ^N h‖ = ρ^N ‖h‖`) |

## 6. How the formalization reads the paper

- **Integrands and test maps.** Matrices `ℝ^{d×m}` are `Matrix (Fin d) (Fin m) ℝ`; the gradient of
  `φ` is `jac φ` (rows are components). An "integrand" (line 348) is lower semicontinuous and
  locally bounded (`IsIntegrand`). `W^{1,∞}_0([0, 1]^m)` maps are Lipschitz maps vanishing outside
  the open cube, with the gradient `fderiv`, defined almost everywhere by Rademacher's theorem.
  The formal Definition 2.1 also asks the integral to exist, which the paper does not; it is
  automatic for integrands, and it makes a failure of quasiconvexity a genuine integral.
- **Homogeneity.** `IsPHomogeneous p f` is `f(tA) = |t|^p f(A)` for every real `t`, the paper's
  `p`-homogeneity (lines 158–163); positive homogeneity is a separate predicate.
- **Rank-one convexity** is Definition 2.2, on segments. Bridges prove it equivalent to convexity
  along lines (Šverák's form) and to the textbook definitions of the package
  `lean4-calculus-of-variations`, in which the cited results of the calculus of variations are
  stated (`Morrey/Cassese/Bridges.lean`).
- **Prelaminates** (Definition 2.4) allow repeated atoms, the reading that Proposition 2.4's gluing
  needs (E10).
- **Rademacher martingales** live on `Fin N → Bool` with the uniform measure; the thresholds
  `C^{rc}`, `C^{qc}` are infima in `[0, ∞]`.
- **UMD constants** (Definition 2.5, and (5) of Proposition 2.7) are best constants over every
  probability space in `Type`, every filtration, every martingale started at `0` (Mathlib's
  `MeasureTheory.Martingale`), and every predictable sequence of signs, or of unimodular
  multipliers for `UMD_{ℂ,p}`. Banach spaces are real (complex for `UMD_{ℂ,p}`). The Schatten
  class `S_q^{d×d}` is `Fin d → Fin d → ℝ` renormed by `‖·‖_{S_q}` (`umdConstWith`). These
  definitions are the package's, definitionally (`Morrey/Cassese/Hypotheses.lean`).
- **Schatten norms** are defined from the singular values, `s_i = √λ_i(AᵀA)`.
- **The Beurling–Ahlfors transform.** `𝓑^k` is the Fourier multiplier with symbol `(ξ̄/ξ)^k`.
  `‖𝓑^k‖_{L^p(ℝ²)}` is the supremum of `‖𝓑^k f‖_p / ‖f‖_p` over Schwartz functions
  (`beurlingPowNorm`), and `‖𝓑^k‖_{L^p_0(𝕋²)}` over mean-zero trigonometric polynomials
  (`torusBeurlingPowNorm`). The operator norm of Proposition 7.2 is the supremum over smooth
  mean-zero periodic tuples (`chainOpNorm`), as in the paper's proof.
- **Hessian quasiconvexity** (Corollaries 5.4, 6.1), undefined in the paper, is
  `∫_{(0,1)^n} F(A + D²φ) ≥ F(A)` for smooth compactly supported `φ`.
- **Quantifiers.** Theorem 1.3 (b): `∃ ε > 0, ∀ p, |p − 4| < ε → …`. Corollaries 5.3, 5.4:
  `∃ K₀ ∀ K ≥ K₀ ∃ δ₀ > 0 ∀ δ ∈ (0, δ₀)`, with `Λ = K/δ`. Proposition 6.5 at `q = ∞`: one exponent
  `α` for every `p` (the proof gives `α = 3`), which covers both readings of the paper.
  Corollary 6.1: the paper's `d(p)`, with `d = 2n`; the formalization takes `n = m⁸` and proves
  every larger `d` as an extra lemma (`corollary6_1_ge`).
- **Theorem 1.4** for general `p` fixes the Schatten exponent `q = 4` among the paper's
  `q ∈ (2, ∞)`.
- **The cited results** are stated in their sources' terms in `Morrey/Common/External/`, and in the
  paper's terms in `Morrey/Cassese/Hypotheses.lean` (`burkholderInequality_holds`,
  `hnvwExtrapolation_holds`, …, `dragicevicLowerBound_holds`). Some are stated more generally than
  the paper quotes them: Lemma 2.1 for every real-valued rank-one convex function (E21);
  Burkholder's inequalities without separability (Section 5); Kahane–Khintchine for any seminorm
  on a real vector space; Kristensen's smoothing for every smooth rank-one convex integrand on
  `ℝ^{d×m}` that is not quasiconvex at `0`. Others are stated in the case the paper uses:
  Randrianantoanina's bounds for real square matrices, uniformly in the size; Pisier's for the
  complex `L^p(μ)` as a real Banach space; transference in the direction from `𝕋²` to `ℝ²`, for
  symbols homogeneous of degree `0`; Dragičević's theorem for `𝓑²`.

No statement of the paper had to be corrected.

## 7. Departures from the paper's proofs

### The paper's proofs

Every proof follows the paper's argument except the three below. Each repairs a step that is
false (E10) or missing (E4, E9), and each is described in its declaration's docstring; the one that
changes the results a proof uses (E10) is also in [`route_differences.tsv`](route_differences.tsv).

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| Theorem 1.3 (b) (`twoByThree_theorem1_3_b_witness`) | "by continuity of the rank-one convexity and quasiconvexity estimates" in `p` | the same continuity, made explicit: Lemma 5.1 (1) with explicit constants (`lemma5_1_part1_quant`), so that `Λ₀(p, δ)` is continuous in `p`; `K`, `δ` and the cut-off fixed before `p` varies; dominated convergence in `p` | the continuity needs constants uniform in `p`, which Lemma 5.1 (1), stated for a fixed `p`, does not give (a gap) | E4 |
| Proposition 2.5, "⇐" (`proposition2_5`) | Proposition 2.4 and the claim of lines 661–663 that every dyadic prelaminate is the law of a rank-one Rademacher martingale | Proposition 2.4's gluing argument, run on the infimum `G(A) = inf E f(M_N)` over rank-one Rademacher martingales started at `A` | the claim is false under the reading of prelaminates that Proposition 2.4 needs, and the gluing of Proposition 2.4 fails under the other reading | E10 |
| Proposition 5.1 (`proposition5_1`) | "`Q` is rank-one affine at `0`. It follows that `Q` is rank-one affine"; "`P − Q` is rank-one convex, since `P''(0) = (P − Q)''(0)`" | a prelaminate centred at `0` with an atom at an arbitrary `A`, split once more along `±hR`; the Legendre–Hadamard condition for the quadratic part by the same device | both steps are skipped (a gap) | E9 |

Not departures: Theorem 1.2 is proved by the paper's route, and the route of Remark 4.5 is a
second theorem, `theorem1_2_elementary`, which takes `f = g` (its `g` is already globally rank-one
convex, so no envelope is needed); the gaps that the formalization fills along the paper's own
lines, recorded as findings in Section 3, among them the density steps from smooth to Lipschitz
periodic test maps in Proposition 7.2 (E28) and Corollary 1.6 (E35), by mollification and
dominated convergence; the explicit constants and cut-offs that complete the sketched proofs (Corollary 5.3's `c = 75/8`, `C = 4·10⁶`, E17; Remark 4.5's `U`, `K`, `q`, E26;
Corollaries 6.4 and 7.2, E31, E32); and the route differences where the paper cites the proof of a
result rather than its statement (Corollaries 5.4 and 6.1, Remark 6.3, Proposition 6.5), recorded
in `route_differences.tsv`.

### The cited results

Each cited result is proved by its source's argument, with the differences below, or, where the
source was not accessible, by a named argument from an open source. The READMEs of
`Morrey/Common/External/` and the packages' module docstrings give the details.

Sources read and followed, with their differences:

| Cited result | Source read | Difference from the source, and why |
| --- | --- | --- |
| Kristensen's smoothing (Corollary 5.2) | Kristensen 1999, proof of Proposition 2 (pp. 6–7, from a scan) | the cut-offs are functions of `\|X\|²` instead of `\|X\|`: Kristensen's `ξ_s` (convex, `0` below `s − 1`, `t²` above `s + 1`) exists only for `s < 3`, since convexity at `s + 1` gives `0 = ξ_s(s − 1) ≥ (s + 1)² − 4(s + 1)`, and he does not say how `s` is chosen (a slip of the source); a constant is added, since the paper's form asks `c ‖A‖² ≤ h(A)`; `ε` is chosen before the radius (the order of independent steps); his "it is not hard to see", the rank-one convexity of the cut-off function, is supplied along his lines |
| the non-commutative Khintchine inequality (Proposition 6.3) | Mackey–Jordan–Chen–Farrell–Tropp 2014 (arXiv:1201.6002), §§7–8 | their Remark 7.2 gives the constant `√(2(q − 1))` for `2 < q < 3` through a variant of the mean value trace inequality that the source does not prove; the package proves it (a gap fill) |
| Proposition 2.7 (2) | Randrianantoanina 2002 (arXiv:math/0111264), §§2–4 | Cuculescu's projections `q_{k+1} = 1_{[0,λ]}(q_k x_k q_k)` are read in the reduced algebra `q_k N q_k`, as the proof requires (read literally, the projections would not decrease); Theorem 4.3's step "by interpolation" is carried out in three ranges of exponents, so that the constant stays uniform near `2`; Lemma 3.2, whose proof uses generalized singular values, is used in a counting form for matrices, which gives the constant `52` in place of `14√3/3 + 28` |
| Dragičević's lower bound (Theorem 7.1, Corollary 7.2) | Dragičević's lecture notes, arXiv:2109.04555, Proposition 4.2; Carbonaro–Dragičević–Kovač, arXiv:2109.08369, §1.3.1 | his test functions `f_{2,α}` are not Schwartz functions, and the norm is a supremum over Schwartz functions: they are approximated by Schwartz functions, as the hint of his Exercise 2.19 does ("first consider smooth `h` and then approximate"); `p < 2` by the duality of §1.3.1 |
| Dacorogna, Theorem 5.20 (Proposition 5.1) | Conti–Dolzmann–Kirchheim–Müller 2006, Appendix, Theorem 6.1 | their distributional derivatives are taken as classical derivatives of mollifications |
| Dacorogna, Theorem 5.25 (i) (Proposition 5.1) | Morrey 1952, Theorem 5.2 | the smooth case by Plancherel's formula for Schwartz functions (Morrey cites Van Hove), then Lipschitz maps by mollification |
| Lemma 2.2, independence of the domain | Müller 1998, Definition 4.2, Remark 2 | the gradient of a Lipschitz map vanishes almost everywhere on its zero set, in place of Müller's assumption `\|∂U\| = 0`, which the paper does not make (a gap fill) |
| Proposition 2.7 (3) | Pisier's lecture notes (2011), Corollary 8.19 | the dyadic form of the source's Fubini argument, which needs neither σ-finiteness nor joint measurability |

Sources not accessible, and the argument used in place of each:

| Source | Cited for | Argument used |
| --- | --- | --- |
| Rindler 2018; Dacorogna 2008, Propositions 5.11, 5.13 | Lemmas 2.1, 2.2 | Müller's 1998 lecture notes: Definition 4.2, Remark 3 (separately convex functions are locally Lipschitz); Lemma 4.3 (laminates on a cube with faces orthogonal to the rank-one direction); Definition 4.2, Remark 2 (the domain); Proposition 4.19 (periodic test maps) |
| Kinderlehrer–Pedregal 1991; Dacorogna 1982 | Proposition 2.2 | the proof of Müller's Theorem 4.5 (iii), §4.8, with his (4.28), Lemma 4.3 and the density argument of his Theorem 4.4 (i) (mollification and Kuhn–Freudenthal interpolation) |
| Dacorogna 2008, Theorems 5.20, 5.25 (i) | Proposition 5.1 | Conti–Dolzmann–Kirchheim–Müller 2006, Theorem 6.1; Morrey 1952, Lemma 5.1 (minors are quasiaffine) and Theorem 5.2 |
| Burkholder 1984, 1988; Osękowski 2012, Theorems 3.5, 8.6 | Theorem 2.3, (13), (14) | Burkholder's method in its standard form: the majorization `U ≥ V`, the concavity of `U` along lines, with its pieces glued through one-sided derivatives at the kinks, and the integration of the concavity along the martingale |
| Burkholder 1984, 1985 | the sharpness of `p* − 1` (Corollary 6.3) | the standard extremal examples, in a dyadic form with an explicit potential function (`Morrey/Cassese/Square/Sharpness.lean`) |
| HNVW I, Theorem 4.2.5 | Proposition 2.7 (4) | Maurey's argument as in Pisier's lecture notes (2011), Lemmas 8.29–8.31, Theorem 8.32 |
| HNVW I, Theorem 4.2.7; Burkholder 1973, 1981 | Proposition 2.7 (1) | Burkholder's good-λ inequality, as in Pisier's lecture notes (Lemma 8.20, second proof of Theorem 8.12), with Doob's inequality and Maurey's theorem |
| HNVW I, Proposition 4.2.3 | Proposition 2.8 | the argument from the definition that Cox–Veraar (whose introduction was read) credit to Montgomery-Smith |
| HNVW I, Proposition 4.2.10 (Yaroslavtsev's source for his Lemma 3.2) | Proposition 2.7 (5) | the averaging of `sgn cos(θ − φ)` over `φ`, with Riemann sums |
| HNVW I, Theorem 4.5.6; Burkholder 1981 | Proposition 2.7 (6) | the Bellman-function argument; Yaroslavtsev's Proposition 3.7 by Burkholder's argument |
| HNVW I, Corollary 5.7.6; de Leeuw 1965 | transference (Proposition 7.2) | the standard argument for this direction of de Leeuw's theorem: Poisson summation on `ℤ²`, lattice Riemann sums, Fatou's lemma |
| Dragičević 2011 | Theorem 7.1, Corollary 7.2 | his lecture notes, arXiv:2109.04555, Proposition 4.2, which reproduces the 2011 theorem and its proof (previous table) |
| HNVW II, Theorem 6.2.4; Borell 1979 | Proposition 6.4; the constants of E27 | hypercontractivity, after O'Donnell, *Analysis of Boolean Functions*, §10.1 (Bonami's two-point inequality, then the passage to seminormed spaces and the tensorization) |
| Pisier–Xu 2003 (the Handbook chapter); Lust-Piquard 1986 | Proposition 6.3 | Mackey–Jordan–Chen–Farrell–Tropp 2014: exchangeable pairs (Corollary 7.3, Remark 7.2) and the Hermitian dilation (§8); the lower bound by convexity |
| Bhatia 1997 | the Schatten facts of Section 1.5 | Courant–Fischer for Weyl's inequalities; the triangle inequality through doubly substochastic matrices (Bessel's, Jensen's and Minkowski's inequalities), in place of Ky Fan's dominance theorem |

Yaroslavtsev 2018 was read for its statements only; Heinz 2008, cited with Kristensen, was not
consulted and is not needed.

## 8. What each result depends on

From [`scripts/Audit.lean`](../../scripts/Audit.lean), which also checks every declaration of the
library: every result below depends only on `propext`, `Classical.choice` and `Quot.sound`. The
third column lists the results of other works that each one uses, all proved
(Section 2); none is a hypothesis.

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Section 1.1 (monotonicity) | `Cassese.morreyPositive_mono` | `External.Rindler.quasiconvexAtOn_iff_periodic` |
| Section 1.1 (min (d, m) = 1) | `Cassese.rankOneConvex_iff_convexOn_of_min_eq_one` | – |
| Section 1.1 (min (d, m) = 1) | `Cassese.quasiconvex_iff_convexOn_of_min_eq_one` | `External.Rindler.rankOneConvex_of_quasiconvex` |
| Section 1.1 (min (d, m) = 1) | `Cassese.morreyPositive_of_min_le_one` | – |
| Section 1.1 (Šverák's example) | `Cassese.sverak_example` | – |
| Thm 1.1 (Kirchheim–Kristensen, quoted) | `External.KirchheimKristensen.Theorem1_1` | – |
| Section 1.3 (homogeneous monotonicity) | `Cassese.homMorreyPositive_mono` | `External.Rindler.quasiconvexAtOn_iff_periodic` |
| Thm 1.2 | `Cassese.theorem1_2` | `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.KinderlehrerPedregal.dacorognaFormula_holds`, `External.HNVW.theorem4_2_7`, `External.Pisier.corollary5_22`, `External.Yaroslavtsev.lemma3_2` |
| Thm 1.3 (a) | `Cassese.theorem1_3_a` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Thm 1.3 (b) | `Cassese.theorem1_3_b` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Section 1.4 (2 × 2 landscape) | `Cassese.morrey_landscape` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Section 1.4 (homogeneous landscape) | `Cassese.homMorrey_landscape` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Thm 1.4 | `Cassese.theorem1_4` | `External.Burkholder.squareFunction`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.KinderlehrerPedregal.dacorognaFormula_holds`, `External.HNVW.theorem4_2_7`, `External.Randrianantoanina.remark4_6`, `External.CoxVeraar.decoupling`, `External.PisierXu.theorem6_1`, `External.HNVW.theorem6_2_4_seminorm` |
| Thm 1.5 | `Cassese.theorem1_5` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.KinderlehrerPedregal.dacorognaFormula_holds`, `External.HNVW.transference_beurlingPow`, `External.Dragicevic.theorem1_1_two_pStar` |
| Cor 1.6 | `Cassese.corollary1_6` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.KinderlehrerPedregal.dacorognaFormula_holds`, `External.HNVW.transference_beurlingPow`, `External.Dragicevic.theorem1_1_two_pStar` |
| Lemma 2.1 (Rindler, cited) | `External.Rindler.lemma5_6` | – |
| Lemma 2.2 (Rindler, cited) | `External.Rindler.rankOneConvex_of_quasiconvex` | – |
| Lemma 2.2 (Rindler, cited) | `External.Rindler.quasiconvexAtOn_iff` | – |
| Lemma 2.2 (Rindler, cited) | `External.Rindler.quasiconvexAtOn_iff_periodic` | – |
| Prop 2.1 | `Cassese.proposition2_1` | `External.Rindler.lemma5_6` |
| Prop 2.2 (Kinderlehrer–Pedregal, cited) | `External.KinderlehrerPedregal.dacorognaFormula_holds` | – |
| Section 2.1 (quasiconvex minorants) | `Cassese.quasiconvexAt_iff_exists_minorant` | `External.Rindler.quasiconvexAtOn_iff`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Prop 2.3 (a) | `Cassese.proposition2_3_a` | `External.Rindler.lemma5_6`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Prop 2.3 (b) | `Cassese.proposition2_3_b` | `External.Rindler.lemma5_6`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Prop 2.3 (c) | `Cassese.proposition2_3_c` | `External.Rindler.lemma5_6`, `External.Rindler.rankOneConvex_of_quasiconvex`, `External.Rindler.quasiconvexAtOn_iff`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Prop 2.3 (c), one direction | `Cassese.proposition2_3_c_left` | `External.Rindler.lemma5_6` |
| Section 2.1 (consequences of Prop 2.3) | `Cassese.envelope_zero` | `External.Rindler.lemma5_6`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Section 2.1 (consequences of Prop 2.3) | `Cassese.rankOneConvexAt_zero_of_rankOneConvexAt` | `External.Rindler.lemma5_6`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Section 2.1 (consequences of Prop 2.3) | `Cassese.quasiconvexAt_zero_of_quasiconvexAt` | `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Section 2.1 (consequences of Prop 2.3) | `Cassese.nowhereQuasiconvex_of_not_quasiconvexAt_zero` | `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Prop 2.4 | `Cassese.proposition2_4` | `External.Rindler.lemma5_6` |
| Prop 2.5 | `Cassese.proposition2_5` | `External.Rindler.lemma5_6` |
| Thm 2.3 (1) (Burkholder, cited) | `Cassese.burkholderInequality_holds` | `External.Burkholder.inequality` |
| Thm 2.3 (2) (Burkholder, cited) | `Cassese.burkholderSquareFunction_holds` | `External.Burkholder.squareFunction` |
| Prop 2.6 (Osękowski, quoted) | `External.Osekowski.HilbertCharacterization` | – |
| Prop 2.7 (1) (HNVW, cited) | `Cassese.hnvwExtrapolation_holds` | `External.HNVW.theorem4_2_7` |
| Prop 2.7 (2) (Randrianantoanina, cited) | `Cassese.randrianantoaninaSchattenUMD_holds` | `External.Randrianantoanina.remark4_6` |
| Prop 2.7 (3) (Pisier, cited) | `Cassese.pisierLpUMD_holds` | `External.Pisier.corollary5_22` |
| Prop 2.7 (4) (HNVW, cited) | `Cassese.hnvwDyadicUMD_holds` | `External.HNVW.theorem4_2_5` |
| Prop 2.7 (5) (Yaroslavtsev, cited) | `Cassese.yaroslavtsevComplexUMD_holds` | `External.Yaroslavtsev.lemma3_2` |
| Prop 2.7 (6) (HNVW, Yaroslavtsev, cited) | `Cassese.hnvwZigZag_holds` | `External.HNVW.theorem4_5_6`, `External.Yaroslavtsev.proposition3_7` |
| Prop 2.8 (Cox–Veraar, cited) | `Cassese.coxVeraarDecoupling_holds` | `External.CoxVeraar.decoupling` |
| Lemma 4.1 | `Cassese.lemma4_1` | – |
| Prop 4.1 | `Cassese.proposition4_1` | – |
| Prop 4.1 (nonnegativity) | `Cassese.proposition4_1_nonneg` | – |
| Eq. (10) | `Cassese.equation10` | `External.Rindler.lemma5_6` |
| Section 4.2 (UMD of ℓ_q) | `Cassese.umdEllq_lt_top` | `External.HNVW.theorem4_2_7`, `External.Pisier.corollary5_22`, `External.Yaroslavtsev.lemma3_2` |
| Section 4.3 (limiting argument) | `Cassese.twoByM_ratio_le_qcThreshold` | – |
| Lemma 4.2 | `Cassese.lemma4_2` | – |
| Eqs. (13), (14) (Burkholder, cited) | `External.Burkholder.scalarFunction_holds` | `External.Burkholder.scalarFunctionQ_holds` |
| Prop 4.2 | `Cassese.proposition4_2` | `External.Burkholder.scalarFunction_holds` |
| Prop 4.2 (the minorant) | `Cassese.proposition4_2_minorant` | `External.Burkholder.scalarFunction_holds` |
| Section 4.3 (limiting argument, for f_n) | `Cassese.twoByM_not_qc_explicitF` | – |
| Prop 4.3 | `Cassese.proposition4_3` | `External.Burkholder.scalarFunction_holds`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Remark 4.5 (Thm 1.2, elementary route) | `Cassese.theorem1_2_elementary` | `External.Burkholder.scalarFunctionQ_holds`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Prop 5.1 | `Cassese.proposition5_1` | `External.Rindler.lemma5_6`, `External.Dacorogna.rankOneAffineMinors_holds`, `External.Dacorogna.minor3_quasiaffine`, `External.Dacorogna.quadraticForm_quasiconvex` |
| Section 5.1 (q rank-one convex on 𝓛) | `Cassese.quarticQ_rankOneConvexOn_calL` | – |
| Section 5.2 (q₃ rank-one convex on 𝓛₃) | `Cassese.q3_rankOneConvexOn_L3` | – |
| Eq. (24) | `Cassese.equation24` | – |
| Prop 5.2 | `Cassese.proposition5_2` | – |
| Lemma 5.1 (1) | `Cassese.lemma5_1_part1` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6` |
| Lemma 5.1 (1), with constants | `Cassese.lemma5_1_part1_quant` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6` |
| Lemma 5.1 (2) | `Cassese.lemma5_1_part2` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6` |
| Proof of Thm 1.3 (κ = 2) | `Cassese.tbt_correction_identity` | – |
| Proof of Thm 1.3 (κ = 2) | `Cassese.L3_rankOneCorrection` | – |
| Proof of Thm 1.3 (q_{δ,K/δ} rank-one convex) | `Cassese.qDeltaLambda_rankOneConvex` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6` |
| Proof of Thm 1.3 (a) (the witness) | `Cassese.twoByThree_not_quasiconvexAt_qDeltaLambda` | – |
| Proof of Thm 1.3 (b) (the witness) | `Cassese.twoByThree_theorem1_3_b_witness` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6` |
| Cor 5.2 | `Cassese.corollary5_2` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.KinderlehrerPedregal.dacorognaFormula_holds`, `External.Kristensen.smoothing_holds` |
| Cor 5.3 | `Cassese.corollary5_3` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Cor 5.4 | `Cassese.corollary5_4` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6` |
| Prop 6.1 | `Cassese.proposition6_1` | `External.Rindler.quasiconvexAtOn_iff_periodic` |
| Prop 6.2 | `Cassese.proposition6_2` | `External.Rindler.lemma5_6`, `External.Randrianantoanina.remark4_6`, `External.CoxVeraar.decoupling`, `External.PisierXu.theorem6_1`, `External.HNVW.theorem6_2_4_seminorm` |
| Prop 6.3 (Pisier–Xu, cited) | `Cassese.pisierXuKhintchine_holds` | `External.PisierXu.theorem6_1` |
| Prop 6.4 (Kahane–Khintchine, cited) | `Cassese.kahaneKhintchine_holds` | `External.HNVW.theorem6_2_4_seminorm` |
| Eq. (31) | `Cassese.equation31` | `External.PisierXu.theorem6_1`, `External.HNVW.theorem6_2_4_seminorm` |
| Remark 6.3 | `Cassese.remark6_3` | `External.Rindler.lemma5_6`, `External.Randrianantoanina.remark4_6`, `External.CoxVeraar.decoupling`, `External.PisierXu.theorem6_1`, `External.Borell.kahaneKhintchine_hypercontractive` |
| Prop 6.5 | `Cassese.proposition6_5` | `External.Burkholder.squareFunction`, `External.Rindler.lemma5_6`, `External.HNVW.theorem4_2_7`, `External.Randrianantoanina.remark4_6`, `External.CoxVeraar.decoupling`, `External.PisierXu.theorem6_1`, `External.HNVW.theorem6_2_4_seminorm`, `External.Borell.kahaneKhintchine_hypercontractive` |
| Prop 6.5 (q < ∞) | `Cassese.proposition6_5_finite` | `External.Burkholder.squareFunction`, `External.Rindler.lemma5_6`, `External.HNVW.theorem4_2_7`, `External.Randrianantoanina.remark4_6`, `External.CoxVeraar.decoupling`, `External.PisierXu.theorem6_1`, `External.HNVW.theorem6_2_4_seminorm` |
| Prop 6.5 (q = ∞) | `Cassese.proposition6_5_infty` | `External.Burkholder.squareFunction`, `External.Rindler.lemma5_6`, `External.HNVW.theorem4_2_7`, `External.Randrianantoanina.remark4_6`, `External.CoxVeraar.decoupling`, `External.PisierXu.theorem6_1`, `External.Borell.kahaneKhintchine_hypercontractive` |
| Cor 6.1 | `Cassese.corollary6_1` | `External.Burkholder.squareFunction`, `External.Rindler.lemma5_6`, `External.KinderlehrerPedregal.dacorognaFormula_holds`, `External.HNVW.theorem4_2_7`, `External.Randrianantoanina.remark4_6`, `External.CoxVeraar.decoupling`, `External.PisierXu.theorem6_1`, `External.HNVW.theorem6_2_4_seminorm` |
| Cor 6.1 (every large d) | `Cassese.corollary6_1_ge` | `External.Burkholder.squareFunction`, `External.Rindler.lemma5_6`, `External.KinderlehrerPedregal.dacorognaFormula_holds`, `External.HNVW.theorem4_2_7`, `External.Randrianantoanina.remark4_6`, `External.CoxVeraar.decoupling`, `External.PisierXu.theorem6_1`, `External.HNVW.theorem6_2_4_seminorm` |
| Proof of Cor 6.1 (periodic Hessian test maps) | `Cassese.not_hessianQuasiconvexAt_of_periodic` | – |
| Proof of Cor 6.1 (periodic Hessian test maps) | `Cassese.square_not_hessianQuasiconvexAt_of_periodic` | – |
| Prop 6.6 | `Cassese.proposition6_6` | `External.Rindler.quasiconvexAtOn_iff_periodic` |
| Thm 6.2 | `Cassese.theorem6_2` | – |
| Cor 6.3 (lower bound) | `Cassese.corollary6_3_lower` | `External.Rindler.lemma5_6`, `Cassese.burkholderSharpness_holds` |
| Cor 6.3 (upper bound) | `Cassese.corollary6_3_upper` | `External.Rindler.lemma5_6` |
| Cor 6.3 (separation) | `Cassese.corollary6_3_separation` | `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff_periodic` |
| Cor 6.4 | `Cassese.corollary6_4` | – |
| Cor 6.4 (not quasiconvex) | `Cassese.corollary6_4_not_quasiconvexAt` | `External.Rindler.quasiconvexAtOn_iff_periodic` |
| Thm 1.4, p = 4 (Section 6.3) | `Cassese.theorem1_4_four` | `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff`, `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.KinderlehrerPedregal.dacorognaFormula_holds` |
| Prop 7.1 | `Cassese.proposition7_1` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6` |
| Prop 7.2 | `Cassese.proposition7_2` | `External.Rindler.quasiconvexAtOn_iff_periodic` |
| Prop 7.2 (lower bound) | `Cassese.proposition7_2_lower` | `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.HNVW.transference_beurlingPow` |
| Thm 7.1 | `Cassese.theorem7_1` | `External.Burkholder.inequality`, `External.Rindler.lemma5_6`, `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.HNVW.transference_beurlingPow`, `External.Dragicevic.theorem1_1_two_pStar` |
| Cor 7.2 | `Cassese.corollary7_2` | `External.Rindler.quasiconvexAtOn_iff_periodic`, `External.HNVW.transference_beurlingPow`, `External.Dragicevic.theorem1_1_two` |
| Conjecture 1 (stated) | `Cassese.Conjecture1` | – |

The route check (`scripts/route_check.py` with [`paper_routes.tsv`](paper_routes.tsv)) finds 67
results of the paper in the Lean code and checks that each proof uses the results that the paper's
proof cites. It finds ten differences, all recorded with their reasons in
[`route_differences.tsv`](route_differences.tsv): the departure of Proposition 2.5 (E10), three
uses that the paper leaves implicit (Lemma 2.2 at line 559, E22; Lemma 2.1 for the minorant `G`,
E21; Lemma 4.1 in the proof of Theorem 1.3 (b)), and six places where the paper cites a proof or a
definition rather than a statement.

## 9. Not formalized

- Claims that the paper states without proof and that no argument uses: Corollary 1.6 for `p > 2`
  (E18) and the remark that the construction adapts to Theorems 1.2 and 1.4 (lines 2956–2958);
  Remarks 2.2, 2.4, 4.1–4.4, 5.1–5.4, 6.1, 6.2, 6.4, 6.5, 7.1 and 7.2 (5.2: a positively
  3-homogeneous example from Šverák's; 5.3: the Cayley hyperdeterminant and extremality; 5.4:
  examples on `2 × 3` and `3 × 2` for `p ∈ (3.6, 5.15)`); the versions for `Sym₀`, `Skew_tr` and
  `h_{p,q,C}` (lines 2521–2549); "`g(AJ)` gives another Hessian counterexample" (lines
  2691–2692); `p = 4` in the proof of Theorem 7.1 (lines 2882–2884); the failure of the
  vector-valued estimate for `q > 4` (§8.2).
- Interpretations that combine the paper with work not formalized here: "quasiconvexity is
  non-local among smooth integrands" (lines 2061–2064, through Kristensen's theorem), the
  concentration interpretation (lines 279–288), and the relation of Corollary 1.6 to Gennaioli and
  Rindler's work (lines 303–312).
- Context only: Kirchheim–Kristensen's theorem (Theorem 1.1) and its consequence at lines
  186–188, Osękowski's Proposition 2.6, Grabovsky's examples (lines 196–199), Iwaniec's bound
  `C^{rc} ≤ p* − 1` (lines 763–765), and the history of Remarks 2.3 and 3.1. Theorem 1.1 and
  Proposition 2.6 are stated (`External.KirchheimKristensen.Theorem1_1`,
  `External.Osekowski.HilbertCharacterization`) and not proved.
- Conjecture 1 is stated as a definition (`Conjecture1`), not proved.

## 10. The paper in the literature

Searched on 21 November 2026: arXiv (the paper's listing and versions, and the listings that cite
it), journal pages, zbMATH and Crossref, and GitHub for formalizations. Preprints are reported as
claimed, not as proved.

### Before the paper

- Morrey (1952) introduced quasiconvexity and asked whether rank-one convexity implies it. Ball
  (1990) gave a counterexample among extended-valued integrands; Šverák (1992) gave the first
  real-valued one, on `ℝ^{3×2}`, hence for `d ≥ 3` components ([formalized here](../Sverak/README.md)).
  For two components the question stayed open: positive results in special classes (Müller 1999,
  diagonal matrices; Chaudhuri–Müller 2003; Harris–Kirchheim–Lin 2018), Kristensen's non-locality
  theorem (1999), the connection with Burkholder's function and Iwaniec's conjecture (Astala,
  Iwaniec, Prause, Saksman, J. Amer. Math. Soc. 2012), Sebestyén and Székelyhidi's theorem (2017)
  that the gradient measures produced from periodic deformations by Šverák's procedure are
  laminates in `2 × 2`, and numerical evidence (Guerra and Teixeira da Costa, Rev. Mat. Iberoam.
  2022).
- Grabovsky (Arch. Ration. Mech. Anal. 2018) gave the only other finite-valued family before 2026,
  on `ℝ^{8×2}`; its examples are nonnegative, hence quasiconvex at `0`.
- Kirchheim and Kristensen (Arch. Ration. Mech. Anal. 221 (2016)) proved that positively
  1-homogeneous rank-one convex integrands are convex at rank-one matrices; according to the paper
  (lines 189–191), they asked the homogeneous problem for `p > 1`. Guerra and Kristensen (Arch.
  Ration. Mech. Anal. 245 (2022)) proved automatic quasiconvexity for homogeneous isotropic
  integrands, the background of Conjecture 1.
- Pedregal's claimed proof for two-component maps
  ([arXiv:1905.06571](https://arxiv.org/abs/1905.06571), [audited here](../Pedregal/README.md)):
  versions 1–2 (May and September 2019) claimed every `2 × N`; version 3 (August 2024) was a
  withdrawal; versions 4–5 (May 2025, June 2026) claim only `2 × 2`. The paper does not cite it.
  Its Theorem 1.2, and its `2 × 3` example, contradict the claim of the withdrawn versions 1–2 for
  `N ≥ 3`.
- The method rests on the author's correspondence between laminates and martingales (Cassese,
  *Martingales, laminates and minimal Korn inequalities*, J. Math. Pures Appl. 213 (2026),
  [arXiv:2512.02784](https://arxiv.org/abs/2512.02784)) and on Burkholder's martingale
  inequalities; Remarks 4.1 and 6.4 also use Cassese,
  [arXiv:2603.22431](https://arxiv.org/abs/2603.22431).

### The paper's versions

- v1 (4 August 2026): `2 × m` for large `m`, the square case `d × d` (now Theorem 1.4) and `4 × 2`
  (now Theorem 1.5).
- v2 (28 August 2026): adds a quartic on `2 × 4` and the Hessian corollary (now Corollary 6.1).
- v3 (16 September 2026, formalized here): replaces the `2 × 4` quartic by the `2 × 3` one, adds
  its transpose on `3 × 2` (as a sketch), Corollary 1.6, and the claim that only `2 × 2` remains.
  No journal version or erratum was found.

### Concurrent work

- Bruno and Pasqualotto ([arXiv:2608.06367](https://arxiv.org/abs/2608.06367), 6 August 2026):
  symmetry can force quasiconvexity.
- Agazzi, Bruno, Guerra and Pasqualotto ([arXiv:2608.12298](https://arxiv.org/abs/2608.12298),
  12 August 2026, between v1 and v2): a non-homogeneous example on `ℝ^{2×4}` from Grabovsky's
  integrand, and examples on symmetric matrices.
- Gennaioli and Rindler ([arXiv:2608.20899](https://arxiv.org/abs/2608.20899), 21 August 2026):
  the Vanishing Mass Conjecture; the paper relates it to Corollary 1.6.
- Guerra ([arXiv:2608.23388](https://arxiv.org/abs/2608.23388), 24 August 2026): the Burkholder
  function is quasiconvex on symmetric matrices; the paper uses it in Remark 6.4.

### Since the paper

- Scalabrino ([arXiv:2610.22560](https://arxiv.org/abs/2610.22560), 15 October 2026) uses
  Corollary 1.6; Conti, Dolzmann and Dondl ([arXiv:2610.31886](https://arxiv.org/abs/2610.31886),
  22 October 2026) give a frame-indifferent, non-isotropic example on `ℝ^{3×3}` and cite v3;
  Braides, Kristensen and Scalabrino ([arXiv:2610.32444](https://arxiv.org/abs/2610.32444),
  23 October 2026) cite the paper; Gammer ([arXiv:2610.35216](https://arxiv.org/abs/2610.35216),
  26 October 2026) uses its integrand. No correction of the paper and no counterexample to it were
  found.
- Agazzi, Astala, Bañuelos, Bruno, Cassese, Faraco, Guerra, Hormozi, Kirchheim, Koski, Kovač,
  Kristensen, Pasqualotto, Prause, Saksman, Šverák, Székelyhidi, Tione, Volberg and Yang
  ([arXiv:2609.28311](https://arxiv.org/abs/2609.28311), 23 September 2026, v2 8 October 2026)
  claim a proof of Iwaniec's conjecture, `‖𝓑‖_{L^p} = p* − 1`, which the paper treats as open
  (§1.3, Remarks 4.3, 6.4, 7.1, §8.1). By the paper's equivalence (lines 1158–1162), the
  integrands behind Theorem 1.2 would then give no counterexample in `2 × 2` (the case `n = 1`);
  the `2 × 2` problem itself stays open.

### Formalizations

- The author formalized Theorem 1.2 and Theorem 1.3 at `p = 4` in Lean (v4.32.2)
  ([MorreyTwoComponentsLean](https://github.com/Gabriele-Cassese/MorreyTwoComponentsLean)), with an
  AI system (the paper's declaration names ChatGPT 5.6 Sol), released without a license; the
  `2 × 3` file was added after v3 and is not in its default build. It was not consulted. This
  formalization covers the whole paper, including what the author's does not: Theorems 1.4 and
  1.5, Corollaries 1.6 and 5.2–5.4, Sections 6 and 7, and the cited results that the proofs use.
- The cited results are proved in three Lake packages written for this formalization, which
  depend only on Mathlib: [lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis),
  [lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability) and
  [lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations).
- Conti, Dolzmann and Dondl's Lean code for their `3 × 3` example
  ([sergioconti/so3-r1c-and-not-qc](https://github.com/sergioconti/so3-r1c-and-not-qc),
  Apache-2.0, written with Claude Opus 5.5 under the authors' guidance) shares the subject, not the
  results. It was not consulted.

## 11. What's next

Plans for follow-up papers are kept in `NEXT.md`, which is not published.

### Open directions

- **`2 × 2`.** The homogeneous problem in `2 × 2` is open; the paper expects a positive answer, and
  notes that it would imply Iwaniec's conjecture, so that a proof must use features of the plane
  (§8.1). Iwaniec's conjecture is now claimed proved
  ([arXiv:2609.28311](https://arxiv.org/abs/2609.28311), Section 10), which removes that
  obstruction but does not decide the problem.
- **A value of `m₀`.** The proof of Theorem 1.2 gives no value of `m₀(p)`; the paper expects
  `m_*(p) ≤ m₀(p) ≤ 4` and conjectures `m_*(p) ≤ 3` (line 1385).
- **`2 × 3` and `3 × 2` for every `p`.** Claimed for `p ∈ (3.6, 5.15)` (Remark 5.4); proved here
  on `2 × 3` for `p` near `4`, and on `3 × 2` at `p = 4`.
- **Theorem 1.4.** `d₀ = 588` for `h_{4,4,C}` is not optimal (numerics suggest `260`;
  Remark 6.4), and for the integrand (30) the paper expects `d = 3`.
- **Remark 7.2** (`ρ = √2` for every `p`); **Remark 5.3** (the extremality of `q` and `q₃`);
  **§8.2** (the Banach-space geometry viewpoint); **Corollary 1.6** for `p > 2` (E18) and in lower
  dimension; the claims for `Sym₀`, `Skew_tr` and `h_{p,q,C}` (lines 2521–2549).
- **Conjecture 1**: isotropic `p`-homogeneous rank-one convex integrands on `ℝ^{d×d}` are
  quasiconvex at `0`.

### Simpler proofs

Simpler arguments for steps of the paper or of the cited results, found while proving. The
formal proofs follow the paper; the column "checked" says where each simpler argument was checked.

| Step | The paper's argument | The simpler one, and what it saves | Checked |
| --- | --- | --- | --- |
| Proposition 4.3 (and the route of Remark 4.5) | if `g_n` were quasiconvex at `0`, `0 = g_n(0) = g_n^{qc}(0) ≤ f_n^{qc}(0) ≤ f_n(0) = 0`, which needs Dacorogna's formula for `g_n^{qc}(0) = g_n(0)` | for every test map, `∫ f_n(∇φ) ≥ ∫ g_n(∇φ) ≥ g_n(0) = f_n(0)`; no envelope, no Dacorogna's formula | in Lean: `twoByM_quasiconvexAt_of_minorant`, in the library, used by no proof |
| Theorem 1.3 (a) (and Corollary 5.4) | `I = ∫_{ℝ³} q₃(∇u) < 0`, and Hölder's inequality for `∫ q₃(π∇u_R) = ∫ χ_R⁴ q₃(∇u) + O(R^{−1/4}(log R)^{3/4})` | since `q₃(∇u) < 0` everywhere, `∫ χ_R⁴ q₃(∇u) ≤ ∫_{B₁} q₃(∇u) < 0`, and the cross terms are bounded pointwise by Young's inequality `a³b ≤ η a⁴ + η⁻³ b⁴`, `η = R^{−1/4}`; saves `q₃(∇u) ∈ L¹` and Hölder | in Lean, in an earlier version of this library's proof (commit `cde348b`) |
| Proposition 4.2's zig-zag step (and Remark 4.5's) | mollify `r` and `b`, prove (17), (18) and `(√r_η)'' ≤ 5⁴ (√b_η)''`, and let `η → 0` | at each `t₀`, replace `r` by the smooth majorant `κ(t₀) + m(t − t₀) + 2·5⁶ b` (`κ = r − 2·5⁶ b` is concave, `m` a supergradient at `t₀`), which satisfies (17) and touches `r` at `t₀`; `b` is already smooth and satisfies (18), and `x` is perturbed where `b` vanishes; the paper's computation makes the tangent at `t₀` a supporting line. Saves the convolution calculus and Minkowski's integral inequality | in Lean, commit `cde348b` |
| Proposition 5.2, smoothness of `ζ` | `ζ` is the unique root of `w̄ ζ² + 2(t + i)ζ + w = 0` in the disc, a simple one, hence smooth by the implicit function theorem | the closed form `ζ = i w / (1 − i t + s)`, `s` the principal square root of `(1 − i t)² + \|w\|²`, which lies off the negative axis, with `Re(1 − i t + s) > 0`; smoothness by composition | in Lean, commit `cde348b` |
| Corollary 1.6, the witness | a smooth periodic `φ` with `∫ F(∇φ) < 0` (E35) | the Lipschitz periodic `φ` that Lemma 2.2 gives: the expansion in `ε` needs only bounded `∇φ`; saves the density step | in Lean, commit `cde348b` |
| Lemma 5.1 (2) | `n`-step rank-one Rademacher martingales, Burkholder's inequality, Proposition 2.5, the estimates (27)–(29) | for `f` that is `C²` away from `0`, the second derivative along rank-one lines: with `D²f[R_L, R_L] ≥ 0` and `\|D²f(X)\| ≤ C\|X\|^{p−2}`, polarization gives `D²f(πA)[πR, πR] ≥ −C' \|πA\|^{p−2} \|π^⊥R\| (\|πR\| + \|π^⊥R\|)`, and the inequality of arithmetic and geometric means against `D²(‖·‖_Λ^p)(A)[R, R] ≥ p ‖A‖_Λ^{p−2} ‖R‖_Λ²`, `‖A‖_Λ² = \|πA\|² + Λ²\|π^⊥A\|²`, gives `Λ ≳ 1/δ`; saves the martingales and Burkholder's inequality | on paper only |
| Dacorogna, Theorem 5.20 (Proposition 5.1) | the book was not accessible; formalized by Conti–Dolzmann–Kirchheim–Müller's proof, which takes the derivatives of a continuous rank-one affine function in the sense of distributions | without continuity: a rank-one affine function is affine in each entry, hence a sum of products of distinct entries, and `t ↦ f(tF)` has degree `< k` when `F` is a sum of fewer than `k` rank-one matrices; saves the first half of their proof (the derivatives and the polynomial structure) | in Lean: `CalculusOfVariations.RankOneAffine.exists_eq_sum_minor`, in the package, used by no proof here |

### The formalization

- Nothing is assumed. What is not proved: the two theorems quoted only as context (Theorem 1.1,
  Proposition 2.6), Conjecture 1, and the claims of Section 9.
- The packages state their planned extensions: Dragičević's bound for every power `𝓑^n`, the
  reverse direction of transference and general dimension (`lean4-harmonic-analysis`);
  Randrianantoanina's Theorem 3.1 for general semifinite von Neumann algebras, and the
  non-commutative Khintchine inequality for rectangular and complex matrices
  (`lean4-banach-probability`); null Lagrangians of every order (`lean4-calculus-of-variations`).
- `Morrey/Common/Basic/` holds two Mathlib candidates: `Basic.LinearAlgebra.Matrix.RankTwo` (for
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`) and `Basic.Analysis.Calculus.BumpFunction.Mollify`
  (for `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`). The latter overlaps with the
  mollification of Lipschitz maps in `lean4-calculus-of-variations` (`Lipschitz/Mollify.lean`);
  the two should be merged before either is contributed. The packages themselves hold general
  theory that Mathlib lacks: Fourier multipliers and transference, Fourier series of smooth
  periodic functions, martingale inequalities in Banach spaces, UMD spaces, Schatten classes,
  quasiconvexity and distributions on `ℝ`.
- `Morrey/Common/External/` states each cited result in its source's terms, under its source's
  name (Burkholder, HNVW, Pisier, Randrianantoanina, Cox–Veraar, Yaroslavtsev, Pisier–Xu, Borell,
  Dragičević, Rindler, Dacorogna, Kinderlehrer–Pedregal, Kristensen), for reuse by other
  formalizations that cite the same sources.
