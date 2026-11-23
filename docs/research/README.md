# Research ledger and completion roadmap

**Research update: 23 November 2026. The unrestricted planar Morrey problem remains OPEN.** A new AI-produced [hand proof](IWANIEC_MORREY_PGE2_POLYCONVEXITY.md) claims global rank-one-convex⇒polyconvex for every **nonnegative, SO(2)×SO(2)-isotropic, positively p-homogeneous** integrand with p≥2. An [independent AI logic audit](IWANIEC_MORREY_PGE2_INDEPENDENT_AUDIT.md) found no fatal gap, but neither Lean certification nor independent mathematical referee review has occurred. Removing homogeneity or isotropy while retaining **polyconvexity is false**, as the [exact obstruction](IWANIEC_MORREY_NONHOMOG_PC_NOGO.md) and the earlier [anisotropic example](IWANIEC_MORREY_P2_SIGNED.md) show. For unrestricted Morrey the target must be **quasiconvexity**, not polyconvexity.
No verified rank-one-convex, non-quasiconvex integrand on `ℝ²ˣ²` has been produced.
Pedregal's nonemptiness lemma is refuted, but that does not refute Morrey's implication.

**Latest independent logic re-audit:** [p≥2 theorem and unrestricted-bridge audit](IWANIEC_MORREY_PGE2_BRIDGE_LOGIC_AUDIT.md). Its seven symbolic identities and the global nonhomogeneous rank-one SOS/minors checks pass; the claimed isotropic theorem remains a provisional hand proof. **New beyond-isotropy consequence:** a [genuine infinite-dimensional bounded-C² neighborhood of positive, coercive, anisotropic and nonhomogeneous QC but non-PC integrands](IWANIEC_MORREY_ANISOTROPIC_OPEN_QC_NONPC.md), conditional on the external Bruno–Pasqualotto 2026 QC theorem. Neither resolves unrestricted Morrey.

Start with these documents:

| Document | Purpose |
| --- | --- |
| [Main formalization audit](MAIN_FORMALIZATION_AUDIT.md) | 22 November review of theorem scope and trust, plus global Lean interfaces added in this PR. |
| [Completion audit](COMPLETION_AUDIT.md) | New findings, numerical blind spots and the strongest remaining global routes. |
| [Global certificates](GLOBAL_CERTIFICATES.md) | Complete negative-witness hierarchy, local-to-global stabilization and positive-certificate compactness. |
| [Structural audit](STRUCTURAL_AUDIT.md) | Rechecked exclusions and the explicit all-field P₂ benchmark. |
| [Pipeline audit](PIPELINE_AUDIT.md) | Affected optimizer functions, certificate restrictions and unfinished implementation. |
| [Audit checkers](../../research/audit/README.md) | New exact rational certificate interfaces and regression controls. |
| [Ledger](LEDGER.md) | Current verdict for each result, conjecture, obstruction and search; stable research IDs and evidence links. |
| [Roadmap](ROADMAP.md) | The missing global theorem or counterexample, acceptance gates, priorities and stopping rules. |
| [Formal status](FORMAL_STATUS.md) | What is actually in the inspected Lean source, including reusable boundary-conversion infrastructure. |
| [Experiments](EXPERIMENTS.md) | Candidate families, budgets, attained values, exclusions and numerical limitations. |
| [Reproducing](REPRODUCING.md) | Commands for exact checks and numerical audits without rerunning every optimization. |
| [Sources and priority](SOURCES.md) | Primary literature, scope of external results and unresolved novelty questions. |
| [Iwaniec–Morrey connection](IWANIEC_MORREY.md) | 2026 Iwaniec result, moving calibrations, and the all-F conformal Morrey consequence of Guerra–Kristensen (2022) with an explicit global quasiconvex minorant; unrestricted Morrey remains open. |
| [Proposed universal isotropic theorem](IWANIEC_MORREY_UNIVERSAL.md) | New candidate complete hand proof: all-matrix quasiconvexity for nonnegative isotropic p-homogeneous rank-one-convex integrands when 1<p<2, conditional on 2026 Burkholder; p=2 polyconvexity; p>2 obstruction. Independent review pending. |
| [Exponent-range and novelty audit](IWANIEC_MORREY_EXPONENT_AUDIT.md) | Clarifies p<1 is identically zero in every dimension, p=1 is Dacorogna (1989), and separates the potentially new 1<p<2 all-matrix Burkholder representation and signed p=2 result from elementary endpoints. |
| [Hybrid Burkholder–polyconvex hierarchy](IWANIEC_MORREY_GENERAL.md) | New all-p>2 scalar quasiconvex envelope lower bound, touching support tests, an exact degree-six counterexample to naive completeness, fractional-power lifting, anisotropic closure and open unrestricted gates. |
| [Signed isotropic p=2 theorem and source repair](IWANIEC_MORREY_P2_SIGNED.md) | Proposed global polyconvexity theorem for **all real-valued**, isotropic 2-homogeneous rank-one-convex energies; exact correction to Guerra–Kristensen Proposition 3.7 and a rigorous anisotropic no-go. |
| [Global no-go for Iwaniec-L support cone](IWANIEC_MORREY_CONE_NOGO.md) | Proves L is QC but nonpolyconvex (conditional on the 2026 paper), yet the full positive cone of GL/translates of L plus all polyconvex functions has exact envelope gap **1** on a known anisotropic rank-one-convex 2-homogeneous energy. |
| [Smooth coercive quasiconvex nonpolyconvex examples](IWANIEC_MORREY_SMOOTH_QC.md) | Explicit (W_ε=1+L+ε\|A\|_F^2), exact four-atom rational minor-Jensen gap -1/17, smoothing and strong rank-one convexity; QC conditional on Iwaniec 2026. |
| [Exact one-variable acoustic criterion](IWANIEC_MORREY_ACOUSTIC.md) | Hand rank-one convexity characterization for smooth isotropic p-homogeneous 2×2 integrands via a scalar acoustic inequality and endpoint conditions, reducing all rank-one directions; exact symbolic verifier. |
| [Exact p=4 hybrid-envelope no-go](IWANIEC_MORREY_HYBRID_NOGO.md) | Fully rational polynomial and Bernstein certificate disprove universal completeness of the p>2 Burkholder–polyconvex hybrid envelope; exact two-point gap. **Not** a Morrey counterexample. |
| [Open-family global no-go](IWANIEC_MORREY_HYBRID_OPEN.md) | Exact p=4 obstruction extends by strict compactness to an open (C^2) class of profiles and an interval of exponents; refutes the hybrid method, not Morrey. |
| [Actual periodic-gradient stress test](../../research/experiments/2026-11-22/README.md) | Reproducible compatible-gradient PL search for the exact p=4 profile, five bases, 147 local runs, and no negative energy gap observed; nonexhaustive numerical evidence only. |
| [Exact uniform local-gradient stability](IWANIEC_MORREY_LOCAL_STABILITY.md) | Explicit 1/6 strict Legendre–Hadamard margin at the p=4 candidate base and a frequency-independent Jensen lower bound for all small periodic gradients; exact rational checker and compact-base extension. |
| [Exact all-amplitude support at rank-one bases](IWANIEC_MORREY_RANKONE_SUPPORT.md) | For the exact p=4 test integrand, a global rational Bernstein certificate proves polyconvexity at **every rank-one matrix**, even though the old homogeneous hybrid support cone misses it. |
| [Nonrealizability of old two-point separator](IWANIEC_MORREY_SEPARATOR_NONREALIZABLE.md) | Exact SOS inequalities force operator-norm barycenter at most 59/60 despite the required value 1; not even a minor-compatible matrix probability law. |
| [Universal nonconformal scalar support criterion](IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md) | Global poly-affine supporting at arbitrary signed ratio reduces to one determinant multiplier, a one-dimensional feasible interval, and **at most two test points** to certify failure; includes an open p>2 full-rank positive family. |
| [New p≥2 isotropic global PC hand proof](IWANIEC_MORREY_PGE2_POLYCONVEXITY.md) | AI-produced claimed affirmative solution to Guerra–Kristensen Question 1.7; provisional hand result pending Lean and external referee audit. Does not settle unrestricted Morrey. |
| [Independent logic audit of new proof](IWANIEC_MORREY_PGE2_INDEPENDENT_AUDIT.md) | Verifies signed-conformal rank-one directions, all three supporting cases, exact Burkholder identities, nondifferentiable and conformal cases; identifies precisely why anisotropy/homogeneity cannot be deleted. |
| [Exact positive isotropic nonhomogeneous non-PC obstruction](IWANIEC_MORREY_NONHOMOG_PC_NOGO.md) | Explicit W=exp(q), global rank-one Hessian SOS, four compatible **minors** atoms and exact rational exponential Jensen deficit; proves the PC conclusion cannot survive removing homogeneity. NOT non-QC. |
| [Global isotropic all-p sublevel theorem](IWANIEC_MORREY_LEVELSETS.md) | Every nonnegative isotropic homogeneous rank-one-convex integrand has polyconvex sublevel sets (even without coercivity), giving universal (L^\infty) quasiconvexity; **not** ordinary integral quasiconvexity. Deduction from Conti et al. (2003). |
| [Four-diagonal-atom global p>2 reduction](IWANIEC_MORREY_FOUR_ATOM.md) | Global polyconvexity in the nonnegative isotropic p>2 class reduces to **three- and four-atom signed-diagonal minor-preserving Jensen inequalities**, with no degree, exponent or amplitude cutoff; exact rational cost-monotone sparsifier. |
| [1993 four-atom priority correction](IWANIEC_MORREY_PRIOR_ART_1993.md) | Original Dacorogna–Koshigoe Theorem 2.1 already gave the exact four-atom diagonal criterion and global poly-affine supports; separates established results from the remaining p>2 inequality. |
| [Global nonnegative DM-quartic stabilization cone](IWANIEC_MORREY_QUARTIC_STABILIZATION.md) | Exact all-parameter polyconvexity of nonnegative determinant-square stabilizations for 1≤|γ|≤2, and a wider sufficient cone for |γ|<1; positive powers extend it to all p≥4. A global counterexample-search exclusion, not a Morrey solution. |
| [Uniform quartic shear bound](IWANIEC_MORREY_QUARTIC_SHEAR_BOUND.md) | Every globally rank-one-convex isotropic quartic polynomial obeys \(|b|\le4a\) and a parabolic curvature bound; **all nonnegative high-coupling RC quartics** are polyconvex, with powers covering all \(p\ge4\). |
| [Global all-integrand quadratic deficit bound](IWANIEC_MORREY_GLOBAL_QUADRATIC_DEFICIT.md) | For every nonnegative isotropic rank-one-convex \(p\)-homogeneous \(C^2\) integrand near the conformal loci, the possible QC deficit is bounded globally by \(K\sigma_1^{p-2}(\sigma_1-\sigma_2)^2\); not a proof that it vanishes. |
| [Fractional-power interpolation no-go](IWANIEC_MORREY_FRACTIONAL_POWER_NOGO.md) | Exact rank-one-line calculation shows \([\|A\|_F^2(\|A\|_F^2-2\det A)]^{p/4}\) is **not rank-one convex** for all \(2<p<11/4\). Power interpolation cannot establish the whole p>2 class. |
| [Exact homogeneous heat-flow method no-go](IWANIEC_MORREY_P4_HEATFLOW_NOGO.md) | Actual three-wave compatible periodic heat trajectory for \(F=(\det A)^2\) has exact energy derivative **+920**; continuity extends the method obstruction to an open interval around p=4 of polyconvex determinant powers. |
| [Global p≥4 rational counterexample hierarchy](IWANIEC_MORREY_PGE4_EXACT_HIERARCHY.md) | Complete negative semidecision **within C² isotropic homogeneous profiles**: strict rational p/polynomial global acoustic certificates and ≤4 rational diagonal atoms, with algebraic Jensen sign checks. Does not settle QC/Morrey. |
| [All-p≥4 Fenchel support and finite-amplitude reduction](IWANIEC_MORREY_PGE4_CONJUGATE.md) | Eliminates the signed-ratio variable from the universal pointwise poly-affine support test, gives an explicit global tail cutoff for positive profiles, and reduces the universal conjecture to strictly positive profiles. The central inequality remains open. |
| [All-integrand frequency resonance sieve](IWANIEC_MORREY_RESONANCE_SIEVE.md) | Arbitrary rank-one-convex F (anisotropic, signed, nonhomogeneous) satisfies exact plane-wave Jensen without short polynomial-frequency resonance; a global Bernstein estimate bounds possible deficits for every F. Exact rational checks; unrestricted Morrey still open. |
| [Complete rational-polynomial input decision](IWANIEC_MORREY_PGE4_INSTANCE_QE.md) | All-degree rational p≥4 input-wise QE encoding of **nonnegativity, global rank-one convexity and global polyconvexity**. No CAD solver or universal p≥4 theorem; not a general quasiconvexity decision. |
| [Reduced five/seven-variable polyconvexity test](IWANIEC_MORREY_PGE4_TWO_TEST_QE.md) | Exact two-support-test Helly/interval encoding for **any fixed rational p≥4 and polynomial h**; local solver produced UNSAT/SAT/SAT controls, while a noninteger test timed out. Universal p≥4 remains open. |
| [All-exponent p>4 demotion no-go](IWANIEC_MORREY_EXPONENT_DEMOTION_NOGO.md) | Even the polyconvex family \((\det A)_+^{p/2}\) loses rank-one convexity when its signed-singular profile is given any smaller homogeneity q<p. Proves p=4 cannot solve all p>4 by profile-preserving descent. |
| [Three-atom gradient rigidity audit](IWANIEC_MORREY_THREE_ATOM_RIGIDITY.md) | Every homogeneous planar W¹∞ gradient Young measure on ≤3 atoms is a laminate/Dirac. Three incompatible minor-compatible atoms can still obstruct PC but cannot be an actual gradient law; classical Šverák/BFJK rigidity. |
| [Strict global supremal Jensen principle](IWANIEC_MORREY_STRICT_SUPREMAL.md) | For every nonnegative isotropic p-homogeneous rank-one-convex integrand, a compact minors-compatible law with atom energies ≤ base energy must have all atom energies equal when the base energy is positive; any fixed violating law loses its violation under sufficiently high positive powers. |
| [Archive guide](../../research/archive/README.md) | Original earlier notes and code, including superseded claims. |
| [Source manifest](../../research/source_manifest.json) | Checksums and coverage of all 36 recovered source artifacts, deduplicated into 139 payloads. |

The ledger is the authoritative interpretation of this research snapshot. The archive preserves
earlier wording and code; an old heading saying “proved”, “global” or “next target” is not a new
trust claim. Some draft targets were subsequently disproved. The latest search package is
preserved separately under [research/experiments/2026-11-21](../../research/experiments/2026-11-21).

## Reading the evidence

- **Lean source:** a proof body is present; distinguish the audited main baseline from additions
  in this PR. The [formalization audit](MAIN_FORMALIZATION_AUDIT.md) records the exact CI evidence.
  Kernel checking of Lean modules does not certify the adjacent Python or prose.
- **Exact check:** a rational, integer or symbolic identity has a replayable checker. Its scope
  is the statement checked; an analytic theorem used around it still needs its own proof.
- **Hand proof / external input:** a written mathematical argument, with dependencies stated,
  awaiting independent review and any proposed Lean translation.
- **Numerical:** a solver result or floating-point validation. An attained positive minimum
  is not a certified lower bound; an approximate Gram matrix is not an exact SOS certificate.
- **Refuted / superseded:** retain the original record and point to the counterexample or
  replacement. Do not silently revive it as a completion gate.
- **Open / conditional:** the universal claim or its central hypothesis remains unproved.

## Conventions and scope

Matrices have output components in rows. The Jensen gap throughout the curated documents is
`J_f(F,u) = average f(F + Du) − f(F)`: a negative value is a violation. One historical polynomial
checker uses the opposite sign; [the ledger](LEDGER.md#corrections-and-interpretation-rules)
explains that case.

Finite-order laminates, measures satisfying all rank-one-convex Jensen inequalities, and actual
gradient laws must remain distinct. A rank-one-convex function that is not polyconvex is not
automatically a counterexample to quasiconvexity. Neither a higher-dimensional counterexample
nor the failure of a particular mold settles the planar question.

This consolidation originally used `cde348ba320b65d902c9f0f782f392e932ba507c` after the Cassese
merge and the recovered research artifacts. The 22 November formalization audit updates the
baseline to `764256f7910b00551419fe71c35809e6b52d7ddd` and adds four global Lean interface modules.
Existing paper theorem statements and proof bodies are preserved.
The earlier [Pedregal report](../Pedregal/REPORT.md) remains the detailed audit of that paper.

The follow-up notes, searches and this consolidation were produced in an AI-assisted research
session at the maintainer's direction. Existing formalization credits remain in the paper-specific
documents. The checks recorded here are reproducible computation and source review; they do not
claim independent human review of the new hand arguments.

## Updating the record

Give every new result a ledger ID, precise quantifiers, evidence level, source/certificate path,
and the claim it supersedes. A search run should record its seed, budget, termination status,
normalization, accepted/excluded cases and independent checks. Record failures as well as
successes. Keep a mathematical completion claim separate from a build or solver success.
