# Credits

How the formalization of Cassese (2026) was made, from the run log and the session transcript.

## Who

- Author and maintainer: The-Anh Vu-Le, who asked for the paper to be formalized in this
  repository, independently of the author's own Lean code, and chose to build every cited result
  that was large but feasible.
- Formalization: Claude Opus 5.5 (`claude-opus-5-5`, Anthropic), in Claude Code 2.1.330 (the VS Code
  extension, Claude Agent SDK), in one session: the main session and its sub-agents. A web page
  was read by a sub-agent. It was the second round of the session, after the audit of Pedregal's
  paper, run in parallel with the formalization of Šverák's.
- Procedure: the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill,
  commit `020f253`, with the reference for several papers in one repository that this round wrote
  (commits `d385092`, `b04ce21`).
- Not consulted: the author's Lean formalization
  ([MorreyTwoComponentsLean](https://github.com/Gabriele-Cassese/MorreyTwoComponentsLean)) and
  Conti, Dolzmann and Dondl's.
- Review: no person has reviewed the proofs. Independent AI agents checked the statements against
  the TeX source (twice), the formal proofs against the paper's (three reviewers), and the report.

## Second round (21 November 2026)

How it was made:

- An agent read the whole TeX source and made the inventory: the numbered results, the cited
  results classed by how far they are from Lean, the suspected errors (no false statement), and
  the routes of the proofs.
- An agent wrote every statement, with the cited results out of reach as named hypotheses; two
  independent agents checked them against the TeX (one false context-only statement of a cited
  result was corrected), and an agent applied their findings.
- The user chose to build every cited result that was large but feasible. Eight agents proved the
  paper in parallel, one file group each (Burkholder's inequality; Section 2 and Rindler's lemmas;
  Section 5; Section 1; Section 4; Section 6; Section 7; Dacorogna's results), against private
  snapshots of the build. Four more finished what remained: the elementary route of Theorem 1.2,
  the open items of Section 6, the density step of Proposition 7.2, and Kristensen's smoothing
  (whose source, a scanned article on Numdam, the main session read page by page).
- An agent integrated the work: it removed the hypotheses that had become theorems, wrote the
  Challenge's Solution, the audit's lists and the routes, and cleaned up; another merged the
  remaining duplicates.
- Three independent agents compared the proofs with the paper, section by section. Four agents
  applied their findings: the departures that were not forced were replaced by the paper's own
  arguments (Lemma 5.1 (2), Proposition 5.2, Proposition 2.3), and Burkholder's sharpness was
  proved.
- The main session wrote the report, the README and the metadata; an independent agent checked
  the report.

Figures, from 2026-11-21 11:56:52 (UTC−6), the start of the second round, to the commit that
completes [`REPORT.md`](REPORT.md):

- elapsed time: 8.3 h for the whole second round. The work on this paper ran in parallel with
  Šverák's, the reorganization of the repository and an update of the procedure, so it has no
  elapsed time of its own;
- sub-agents on this paper: 28 launched by the main session (an inventory, a statement writer, 2
  statement reviewers and a fixer, 12 provers, an integrator, a cleanup agent, 3 proof reviewers,
  4 fixers, a web reader, and the report's checker), about 21 h of working time, plus helpers that
  two provers forked;
- the whole round: 48 sub-agents (40 launched by the main session), at most 12 running at once,
  34.3 h of working time, 4,122 tool calls, 8.16 M output tokens, 20.23 M input tokens, 1,371 M
  cache reads; main session: 368 tool calls, 0.49 M output, 0.94 M input, 189 M cache reads;
- model calls: `claude-opus-5-5`, 379 by the main session and 3,999 by the sub-agents;
  `claude-haiku-5-5`, 4 (the web reader).

From `scripts/session_stats.py` on the session transcript, and the run times of the sub-agents.
