# Main formalization audit and global interfaces

**Audit date: 22 November 2026.** Audited main commit:
[`764256f7910b00551419fe71c35809e6b52d7ddd`](https://github.com/vltanh/lean4-morrey/tree/764256f7910b00551419fe71c35809e6b52d7ddd).
The unrestricted planar problem remains unresolved. This audit found no blocking semantic
defect in the reviewed central proof chains. It identifies reusable results, closes several
integration gaps in this PR, and separates those changes from the missing mathematical result.

## 1. Evidence and limits

All 141 files in the downloaded main snapshot matched their Git blob hashes. The Lean source
is unchanged from the previous baseline `cde348ba320b65d902c9f0f782f392e932ba507c`; subsequent main
commits changed documentation only.

The [main CI job](https://github.com/vltanh/lean4-morrey/actions/runs/44989900031/job/137108445876)
completed successfully. Its decoded log records **6,995 build jobs** and **4,166 library
declarations checked against the standard-axiom whitelist**. The audit imports all 83 library
modules and all three Solution modules, including private and auxiliary declarations.
Challenge definitions, proof routes, code links and Markdown-table checks also passed.

`scripts/Audit.lean` checks every library declaration separately with `collectAxioms`. Stopping
the *route* traversal at a named external result does not exempt that result from the axiom
check. The whitelist is `propext`, `Classical.choice` and `Quot.sound`. A named proposition
hypothesis is still a mathematical assumption even when its theorem passes this audit.

This was a review of definitions, theorem statements, central proof bodies and dependencies;
it was not an independent line-by-line review of every helper or of Mathlib. No local Lean
runtime was available. New modules are validated through the repository's existing CI, with
the result recorded below. No independent human review is claimed.

The regular workflow does not run Comparator or Nanoda. The repository has separate manual
Palomar preflight workflows; no completed preflight appeared among the 14 Actions runs returned
during this audit. That observation does not establish whether an external registry ran one.
The prior README's Comparator claim is therefore not newly certified by this audit.

## 2. What main actually proves

| Area | Audited conclusion | Limitation that matters for reuse |
| --- | --- | --- |
| Pedregal | Proposition 7.1, Corollary 7.2 and both Step 2 formulations are refuted. The conditional Kakutani reduction is sound. | The universal nonemptiness premise is false. Its conditional theorem cannot prove the main claim. |
| Pedregal endpoints | `Theorem1_1_part1`, `Theorem1_1_part2` and `Theorem1_2` are definitions of propositions. | Their names are not proofs. The existing level-one theorem does not establish arbitrary levels. |
| Cassese, quartic | `theorem1_3_a` is an unconditional homogeneous quartic counterexample in `2 × 3`. | It is not a planar counterexample or a concrete rational coefficient certificate. |
| Cassese, nearby exponents | `theorem1_3_b` is unconditional. Its envelope step supplies a globally rank-one-convex integrand. | An intermediate at-zero minorant result alone is not global rank-one convexity of that intermediate function. |
| Cassese, other dimensions | `theorem1_2`, `theorem1_4_four` and the nonplanar landscape have unconditional declarations. | The landscape explicitly excludes `2 × 2`; the fourth-power square result has its stated dimension bound. |
| Cassese, named hypotheses | General `theorem1_4`, `theorem1_5` and `corollary1_6` retain named external inputs. | Standard-axiom checking does not discharge those explicit hypotheses. |

Sources: [Pedregal Introduction](../../Morrey/Pedregal/Introduction.lean),
[Counterexample](../../Morrey/Pedregal/NonEmptiness/Counterexample.lean),
[Reduction](../../Morrey/Pedregal/Reduction.lean),
[Cassese Introduction](../../Morrey/Cassese/Introduction.lean), and
[Cassese Hypotheses](../../Morrey/Cassese/Hypotheses.lean).

### The higher-dimensional negative proof uses an actual gradient

The reviewed quartic chain combines global rank-one convexity of `qDeltaLambda`, an explicit
smooth compatible field `tbtWitness`, a compactly supported negative-energy test and the
integrability needed by quasiconvexity. The small parameter is constrained by both the
convexity and strict-gap theorems. This is not a sampled Hessian check or a moment-only law.
See [Extension](../../Morrey/Cassese/TwoByThree/Extension.lean),
[Witness](../../Morrey/Cassese/TwoByThree/Witness.lean),
[WitnessCutoff](../../Morrey/Cassese/TwoByThree/WitnessCutoff.lean) and
[Bridges](../../Morrey/Cassese/Bridges.lean).

The dimensional lifting theorems go to larger dimensions. They do not produce a planar
witness. For the naive zero-third-column restriction of `L3`, the planar matrices become
`[[a,b],[b,−a]]`. A periodic gradient taking values there has determinant `−a²−b²`, whose mean
is zero by the determinant null-Lagrangian identity; hence the gradient vanishes almost
everywhere. This explanatory hand argument shows why that direct restriction loses the
witness. It is not an additional Lean result or a general exclusion of every planar adaptation.

### Correct the meaning of `RankOneConvexAt`

In [Toolkit](../../Morrey/Cassese/Toolkit.lean), `Cassese.RankOneConvexAt f A₀` means existence
of a globally rank-one-convex integrand minorant touching `f` at `A₀`. It is not defined as
pointwise Hessian positivity. A martingale Jensen characterization is proved later under its
stated hypotheses. The previous F15 description conflated the definition and a characterization;
[FORMAL_STATUS.md](FORMAL_STATUS.md) now states the definition precisely.

## 3. General analysis already available

These results are in audited main and should be reused:

- `External.Rindler.lemma5_6`: finite-valued rank-one-convex integrands are locally Lipschitz.
- `External.KinderlehrerPedregal.kp_integrableOn`: a continuous integrand composed with a
  Lipschitz gradient is integrable on a set of finite volume. No polynomial-specific existence
  proof for that integral is needed.
- `External.Rindler.rd_quasiconvexAtOn_of_unitCube`: passes the unit-cube condition to bounded
  measurable domains, including the empty domain.
- `quasiconvexAtOn_iff` and `quasiconvexAtOn_iff_periodic`: domain independence and actual
  periodic **Lipschitz** test maps, under the stated regularity hypotheses.
- `External.Dacorogna.quadraticForm_quasiconvex`: the dimension-general quadratic result.
- `External.KinderlehrerPedregal.dacorognaFormula_holds`: the envelope formula, with its
  minus-infinity branch handled explicitly rather than discarded in conversion to real values.
- `External.Kristensen.SmoothingProof.exists_smoothing`: a smooth counterexample in any
  matrix dimension yields a smooth uniformly rank-one-convex counterexample of quadratic
  growth. Its transition-annulus compensation and retention of a strict gap are proved.

The last theorem starts with a smooth counterexample. It is not, by itself, a smoothing
theorem for every continuous candidate. Quadratic growth also does not mean a quadratic
polynomial. Sources: [Rindler](../../Morrey/Common/External/Rindler/Lemmas.lean),
[Envelope](../../Morrey/Common/External/KinderlehrerPedregal/Envelope.lean),
[Formula](../../Morrey/Common/External/KinderlehrerPedregal/Formula.lean),
[Dacorogna](../../Morrey/Common/External/Dacorogna/Minors.lean), and
[Smoothing](../../Morrey/Common/External/Kristensen/Smoothing.lean).

## 4. Global interfaces added by this PR

These are new modules in the PR, not claims about what was present at the pinned main commit.

| Module | Main exported result | Mathematical scope |
| --- | --- | --- |
| [Jensen](../../Morrey/Pedregal/Jensen.lean) | `IsLaminate.jensen`, `discrete_jensen_of_theorem1_1_part1` | Every finite-order laminate satisfies Jensen; translation and zero gradient barycenter give the discrete inequality at every dyadic level under the laminate-existence hypothesis. |
| [Bridges](../../Morrey/Pedregal/Bridges.lean) | `cov_quasiconvex_iff`, `theorem1_1_part2_iff_cov_morrey`, `theorem1_2_iff_theorem1_1_part2` | Pedregal's planar endpoint is exactly the shared universal implication. Continuity follows from rank-one convexity where needed. |
| [LegendreHadamard](../../Morrey/Common/Basic/CalculusOfVariations/LegendreHadamard.lean) | `rankOneConvex_iff_iteratedFDeriv_nonneg` | In every matrix dimension, for every `C²` integrand, global Hessian nonnegativity on rank-one directions is equivalent to rank-one convexity. |
| [CounterexampleCertificate](../../Morrey/Pedregal/CounterexampleCertificate.lean) | `not_cov_morrey_of_lh_periodic_gap` | A globally certified `C²` integrand plus a strict violation for an actual periodic Lipschitz map refutes the universal planar implication. |

The Jensen module also proves total mass one and nonnegative weights, including repeated atoms,
and the equivalence of the segment and whole-line rank-one-convexity definitions. The analytic
bridge handles the automatic integrability and domain conversion explicitly.

The negative acceptance theorem has **no degree or mesh restriction**. It does not manufacture
the global Hessian certificate, an admissible test map, or a negative gap. In particular, the
Python rational-certificate format has not yet been given a Lean parser/evaluator, and the
finite-element gradient-sum-to-integral identity remains to be formalized.

**Validation of additions:** pending branch CI. All four modules are included in the full
declaration audit. Existing paper definitions and proof bodies, Challenges and CI workflows
are unchanged. The main documentation updates are preserved.

## 5. Remaining work in order of consequence

### Negative route: certify an actual global candidate

1. Complete the discovery work already specified in [PIPELINE_AUDIT.md](PIPELINE_AUDIT.md):
   range-sensitive base minimization, boundary Gram handling, weighted-Gram discovery and
   rational certificate extraction. The current exact verifier is not a discovery engine.
2. For any strict candidate, prove its polynomial Hessian identity and exact nonnegative
   certificate in Lean. Instantiate the general LH equivalence; do not replace global
   nonnegativity by finitely many sampled directions or base matrices.
3. Define the actual periodic PL map, prove periodicity and a global Lipschitz bound, identify
   its almost-everywhere gradients, and convert the finite rational sum to the integral.
4. Apply the periodic-gap/acceptance theorem. A successful instance resolves the negative route;
   a failed finite search gives no positive theorem.

### Positive route: retain the universal quantifiers

The new Jensen theorem closes the finite-laminate algebra. What remains is:

1. **Discrete-to-integral identity.** For arbitrary `l,u,v ∈ PL l`, prove Lipschitz regularity,
   almost-everywhere affine gradients, equal triangle areas and null overlaps, then identify
   the periodic energy integral with the normalized triangle sum. The current centroid-gradient
   lemmas alone do not prove this identity.
2. **Controlled dyadic approximation.** Approximate a periodic Lipschitz map with a common
   gradient bound and sufficient convergence for continuous integrands on that common compact
   range; pass the discrete Jensen inequality to the limit. A direct route uses nodal
   interpolation: edge differences bound its slopes, while the Taylor remainder at almost
   every differentiability point gives gradient convergence off the grid skeletons. Dominated
   convergence then applies. Uniform gradient convergence for Lipschitz maps is not required.
3. **The central open theorem.** Supply the discrete Jensen inequality for every level and
   every admissible pair, or prove an equivalent all-gradient inequality directly. Universal
   finite-order laminate existence is sufficient but stronger than necessary.

The first two are substantial formal integration tasks. Completing them would expose an exact
remaining universal premise; it would not establish that premise. The all-degree positive
certificate approach in [GLOBAL_CERTIFICATES.md](GLOBAL_CERTIFICATES.md) likewise still needs
universal feasibility. Its hand compactness argument is not already a Lean theorem.

Neither more special finite trees nor more higher-dimensional corollaries closes the planar
problem. The next mathematical advance must meet one of the two global acceptance conditions.
