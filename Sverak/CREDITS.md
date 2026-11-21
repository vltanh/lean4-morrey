# Credits

How the formalization of Šverák (1992) was made, from the run log and the session transcript.

## Who

- Author and maintainer: The-Anh Vu-Le, who supplied the paper's PDF and asked for it to be
  formalized in this repository, independently of other formalizations.
- Formalization: Claude Opus 5.5 (`claude-opus-5-5`, Anthropic), in Claude Code 2.1.330 (the
  VS Code extension, Claude Agent SDK), in one session: the main session and its sub-agents. It was
  the second round of the session, after the audit of Pedregal's paper; there was no earlier draft.
- Procedure: the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill,
  commit `020f253`.
- Review: no person has reviewed the proofs. Independent AI agents checked the statements against
  the paper, the formal proofs against the paper's, and the repository's README against the
  sources.

## Second round (21 November 2026)

How it was made:

- The main session transcribed the paper for the agents, wrote the definitions and the statements
  (Šverák's notions in his terms, shared at first with the other papers' and later split into
  [`Defs.lean`](Defs.lean)), and the Challenge.
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
