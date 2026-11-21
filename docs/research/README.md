# Research ledger and completion roadmap

**Cutoff: 21 November 2026. The unrestricted planar problem is unresolved in this work.**
No verified rank-one-convex, non-quasiconvex integrand on `ℝ²ˣ²` has been produced.
Pedregal's nonemptiness lemma is refuted, but that does not refute Morrey's implication.

Start with these documents:

| Document | Purpose |
| --- | --- |
| [Ledger](LEDGER.md) | Current verdict for each result, conjecture, obstruction and search; stable research IDs and evidence links. |
| [Roadmap](ROADMAP.md) | The missing global theorem or counterexample, acceptance gates, priorities and stopping rules. |
| [Formal status](FORMAL_STATUS.md) | What is actually in the inspected Lean source, including reusable boundary-conversion infrastructure. |
| [Experiments](EXPERIMENTS.md) | Candidate families, budgets, attained values, exclusions and numerical limitations. |
| [Reproducing](REPRODUCING.md) | Commands for exact checks and numerical audits without rerunning every optimization. |
| [Sources and priority](SOURCES.md) | Primary literature, scope of external results and unresolved novelty questions. |
| [Archive guide](../../research/archive/README.md) | Original earlier notes and code, including superseded claims. |
| [Source manifest](../../research/source_manifest.json) | Checksums and coverage of all 36 recovered source artifacts, deduplicated into 139 payloads. |

The ledger is the authoritative interpretation of this research snapshot. The archive preserves
earlier wording and code; an old heading saying “proved”, “global” or “next target” is not a new
trust claim. Some draft targets were subsequently disproved. The latest search package is
preserved separately under [research/experiments/2026-11-21](../../research/experiments/2026-11-21).

## Reading the evidence

- **Lean source:** a proof body is present in the existing formalization. This PR inspects that
  source; it does not claim a fresh Lean build or extend kernel checking to Python or prose.
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

This consolidation uses the repository at commit
`d0471a6f174c8d5851398ec8069cd5bb2defbb54` and the recovered research artifacts. It adds documentation,
research code, data and checkers; it makes no changes to Lean theorem statements or proof bodies.
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
