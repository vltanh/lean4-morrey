# Research ledger and completion roadmap

**Cutoff: 21 November 2026. The unrestricted planar problem is unresolved in this work.**
No verified rank-one-convex, non-quasiconvex integrand on `ℝ²ˣ²` has been produced.
Pedregal's nonemptiness lemma is refuted, but that does not refute Morrey's implication.

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
