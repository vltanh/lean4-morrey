# Credits

How this formalization was made, from the run log and the session transcripts.

## Who

- Author and maintainer: The-Anh Vu-Le, who asked for the formalization of
  [arXiv:1905.06571](https://arxiv.org/abs/1905.06571) and chose the paper.
- Formalization: Claude Opus 5.5 (`claude-opus-5-5`, Anthropic), in Claude Code 2.1.330 (the
  VS Code extension, Claude Agent SDK), in one session: the main session and its sub-agents. Web
  pages were read by sub-agents on Claude Haiku 5.5 (`claude-haiku-5-5`). There was no earlier
  draft.
- Procedure: the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill,
  commit `020f253`.
- Kakutani's theorem comes from [lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point)
  (commit `5f650f0`), an earlier project made with the same procedure.
- Review: no person has reviewed the proofs. Independent AI agents checked:
  - the statements and the counterexample against the TeX source;
  - the formal proofs against the paper's;
  - the report's findings and literature section;
  - in a later round, every recorded departure and the documents of the three papers.

## First formalization (21 November 2026)

How it was made:

- The main session:
  - read the TeX source;
  - made the inventory;
  - found the counterexample to Corollary 7.2 numerically and then a transparent one (exact
    rational arithmetic);
  - set up the project;
  - wrote every definition and statement, the Challenge and the Solution.
- An independent agent checked every statement against the TeX and recomputed the counterexample
  by hand.
- Six agents proved the statements in parallel, each owning whole files:
  - the general lemmas and Kakutani's theorem with Section 3;
  - the triangulation;
  - Sections 4 and 5;
  - Section 6, the reduction and Section 7's correct claims;
  - the counterexample;
  - the case `l = 1` of Theorem 1.1 (1).
- The main session integrated their work, cleaned up, and ran the audit, the route check and
  Comparator. An independent agent compared the formal proofs with the paper's.
- Web-reading agents gathered the paper's versions and the literature; the main session wrote the
  report, and an independent agent checked its findings and its literature section.

Figures, from 2026-11-21 09:52 (UTC−6) to the commit that completes [`REPORT.md`](REPORT.md):

- elapsed time: 1.86 h (09:52 to 11:44, UTC−6);
- sub-agents: 13 (6 provers, 4 independent checkers, 3 web readers), at most 7 running at once,
  2.4 h of working time in all;
- tool calls: 432 by the sub-agents, 234 by the main session;
- tokens, sub-agents: 0.73 M output, 2.16 M input, 51 M cache reads; main session: 0.44 M output,
  0.72 M input, 104 M cache reads;
- model calls: `claude-opus-5-5` 218 (main session) and 369 (sub-agents), `claude-haiku-5-5` 11
  (web-reading sub-agents).

From `scripts/session_stats.py` on the session transcript. The figures leave out the numerical
experiments' running time outside the agents' tool calls, and the work after that commit
([`CREDITS.md`](CREDITS.md), packaging).

## Reorganization (21 November 2026)

When Šverák (1992) and Cassese (2026) joined the repository, the paper's files moved into
`Pedregal/` and its namespaces were renamed (Morrey to `Pedregal`, MorreyChallenge to
`PedregalChallenge`). No statement or proof changed: the statement diff against the commit before
the move shows only the renames, and the build, the audit, the route check and Comparator pass as
before. The work is counted in the second round's figures
([`../Sverak/CREDITS.md`](../Sverak/CREDITS.md)).

## Departure audit (21–22 November 2026)

In a later round, which made Cassese's formalization unconditional, the procedure moved to its
version 4.2.0 (commit `f5e7420`), under which a proof may depart from the paper's only for an error
or a gap of the paper, a representation the formalization must use, or the user's decision.

- An independent agent (Claude Opus 5.5, `claude-opus-5-5`, in Claude Code 2.1.330) audited,
  read-only, every recorded departure of the three papers against their sources (21 November,
  23:08 to 23:27, UTC−6; 0.33 h for the three papers). For this paper it found the three departures
  allowed, each forced by an error of the paper, and nothing to redo.
- No proof or statement of this paper changed in that round. An agent updated this paper's
  documents on 22 November to match: the table of departures and the dependencies.
