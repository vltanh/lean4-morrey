# Credits

How the formalization of Šverák (1992) was made, from the run log and the session transcript.

## Who

- Author and maintainer: The-Anh Vu-Le, who supplied the paper's PDF and asked for it to be
  formalized in this repository, independently of other formalizations.
- Formalization: Claude Opus 5.5 (`claude-opus-5-5`, Anthropic), in Claude Code 2.1.330 (the
  VS Code extension, Claude Agent SDK), in one session: the main session and its sub-agents. It was
  the second round of the session, after the audit of Pedregal's paper; there was no earlier draft.
- Procedure: the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill,
  commit `020f253` for the second round, version 4.2.0 (commit `f5e7420`) for the third.
- Review: no person has reviewed the proofs. Independent AI agents checked the statements against
  the paper, the formal proofs against the paper's, the repository's README against the sources,
  and, in the third round, every recorded departure and the rebuilt cut-off.

## Second round (21 November 2026)

How it was made:

- The main session transcribed the paper for the agents, wrote the definitions and the statements
  (Šverák's notions in his terms, shared at first with the other papers' and later split into
  [`Defs.lean`](../../Morrey/Sverak/Defs.lean)), and the Challenge.
- An independent agent checked every statement against the paper. Its main finding: without an
  integrability premise, a failure of quasiconvexity could be witnessed by a non-integrable test
  map, whose Lean integral is `0`. The definitions now require the integral to exist.
- Four agents proved the statements in parallel, each owning whole files: the cube facts, the
  construction and (4); Lemma 1; Lemma 2; the Theorem, the Remark and the Corollary.
- The main session moved the repository to one directory per paper, and integrated, built and
  audited the proofs.
- An independent agent compared the formal proofs with the paper's. It found the statements and the
  routes faithful, and some choices that were not reported. An agent then restated (7), (*) and (8)
  for the second derivative itself, stated (10), and proved the limit of Lemma 1 for `ε → 0`, as
  the paper states it.
- The main session wrote the report, the README and the metadata; an independent agent checked the
  literature in the repository's README, whose corrections also apply to the report.

Figures, from 2026-11-21 11:56:52 (UTC−6), the start of the second round, to the commit that
completes [`REPORT.md`](REPORT.md) (13:41):

- elapsed time: 1.7 h, for the whole round. The work on Šverák ran in parallel with the work on
  Cassese's paper and with an update of the procedure, so it has no elapsed time of its own;
- sub-agents on this paper: 7 (1 statement checker, 4 provers, 1 proof checker, 1 cleanup agent),
  1.4 h of working time in all; and 1 web-reading checker of the repository's README (0.25 h),
  shared with the other papers;
- the whole round, so far: 15 sub-agents, at most 8 running at once, 3.7 h of working time, 615
  tool calls, 1.38 M output tokens, 3.42 M input tokens, 102 M cache reads; main session: 190 tool
  calls, 0.27 M output, 0.54 M input, 72 M cache reads. Besides the Šverák agents, these include
  the inventory and the statements of Cassese's paper (2 agents, 1.5 h) and five agents that tested
  the procedure's update (0.5 h);
- model calls: `claude-opus-5-5`, 192 by the main session and 554 by the sub-agents.

From `scripts/session_stats.py` on the session transcript, and the run times of the sub-agents.

## Third round (21–22 November 2026)

In the round that made Cassese's formalization unconditional, at the user's request, the procedure
moved to its version 4.2.0, under which a proof may depart from the paper's only for an error or a
gap of the paper, a representation the formalization must use, or the user's decision. This round
changed one construction of this paper: the cut-off of Lemma 1.

How it was made (all agents Claude Opus 5.5, `claude-opus-5-5`, in Claude Code 2.1.330):

- An independent agent audited, read-only, every recorded departure of the three papers. For this
  paper it found that the cut-off of Lemma 1, a product of one-dimensional profiles with
  `‖Dη_ε‖ ≤ 4nB/ε`, was not the paper's object (`|Dη_ε| ≤ 2/ε`), and that the docstrings misquoted
  the paper's support condition.
- In a run that also redid six of Cassese's proofs, one prover rebuilt the cut-off as the paper's:
  the mollification of a Lipschitz profile, with `‖Dη_ε‖ ≤ 8/(5ε) ≤ 2/ε`. Another prover proved
  the general mollification lemmas it uses, in
  [`Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean`](../../Morrey/Common/Basic/Analysis/Calculus/BumpFunction/Mollify.lean). The statements of Lemma 1 did not
  change. An independent agent reviewed the run's commits against the papers and found no
  remaining departure; the build, the audit, the route check and Comparator passed.
- An agent updated this paper's documents.

Figures, from the session transcript (`scripts/session_stats.py` on each sub-agent's transcript):

- the cut-off: one prover, 0.16 h (22 November, 00:04 to 00:14, UTC−6), 40 tool calls, 0.06 M
  output tokens, 0.15 M input, 4 M cache reads, 39 model calls;
- the mollification module: one prover, 0.10 h, 32 tool calls, 0.04 M output, 0.09 M input, 2 M
  cache reads; the module also serves Cassese's proofs;
- shared with Cassese's paper, not separated: the departure audit (0.33 h, for the three papers),
  the lead of the run (1.16 h) and its reviewer (0.13 h), and the main session.
