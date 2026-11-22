# Credits

How the formalization of Cassese (2026) was made, from the run log and the session transcript.

## Who

- Author and maintainer: The-Anh Vu-Le, who asked for the paper to be formalized in this
  repository, independently of the author's own Lean code; chose, in the second round, to build
  every cited result that was large but feasible; and asked, in the third round, for every result
  to be proved unconditionally.
- Formalization: Claude Opus 5.5 (`claude-opus-5-5`, Anthropic), in Claude Code 2.1.330 (the VS Code
  extension, Claude Agent SDK), in one session: the main session, its sub-agents, and the
  sub-agents that lead agents launched. Web pages were read by sub-agents. The same system wrote
  the three Lake packages that prove the cited results:
  [lean4-harmonic-analysis](https://github.com/vltanh/lean4-harmonic-analysis),
  [lean4-banach-probability](https://github.com/vltanh/lean4-banach-probability) and
  [lean4-calculus-of-variations](https://github.com/vltanh/lean4-calculus-of-variations).
- Procedure: the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill:
  commit `020f253` in the second round, with the reference for several papers in one repository
  that the round wrote (commits `d385092`, `b04ce21`); version 4.2.0 (commit `f5e7420`) in the third
  round, which it wrote: the mathematics that Lean lacks is built, and is no reason to depart
  from a proof.
- Not consulted: the author's Lean formalization
  ([MorreyTwoComponentsLean](https://github.com/Gabriele-Cassese/MorreyTwoComponentsLean)) and
  Conti, Dolzmann and Dondl's.
- Review: no person has reviewed the proofs. Independent AI agents checked the statements against
  the TeX source (twice), the formal proofs against the paper's (three reviewers) and the report,
  in the second round. In the third: the statements of each package (and the bridges between
  `lean4-banach-probability` and the project), package proofs against their sources, the
  statements of the Challenge and of Proposition 7.2 that changed (against the TeX source), the
  redone proofs of the paper, the proof of Dacorogna's Theorem 5.20 against
  Conti–Dolzmann–Kirchheim–Müller's (two reviews), and every recorded departure under version
  4.2.0 of the procedure (an audit). Then an independent agent checked the rewritten documents of
  the three papers (README, report, credits, metadata) against the code, the audit output, the TeX
  source and the cited works.

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

## Third round: every result unconditional (21–22 November 2026)

The user asked for every result to be proved unconditionally ("I think you need to formalize all
of them unconditionally"), that is, for the named hypotheses that the second round had left
unproved to be proved: eleven assumed by statements of the paper (UMD theory and decoupling, the
Khintchine inequalities, transference, Dragičević's bound) and two that no statement used. The
user let the session decide the rest without asking. During the round the procedure was revised
(version 4.2.0): the mathematics that Lean lacks is built, so the departures that the second
round had recorded for that reason, or for convenience, were redone by the paper's arguments.

How it was made:

- Three agents scoped the missing mathematics (transference and Dragičević's bound; UMD theory;
  the Khintchine inequalities), with plans and size estimates, and a fourth the calculus of
  variations. A read-only agent audited every recorded departure of the three papers under
  version 4.2.0 and listed the proofs to redo.
- The main session decided, as the user had asked: one package per area; the sources' arguments
  wherever a source was accessible (Dragičević's test functions with a density step,
  Randrianantoanina's route for general filtrations, and, once an agent had found an open source,
  Conti–Dolzmann–Kirchheim–Müller's proof of Dacorogna's Theorem 5.20), named arguments from open
  sources where it was not; and Theorem 1.2 by the paper's route once that route was
  unconditional, with the route of Remark 4.5 kept as a second theorem.
- `lean4-harmonic-analysis`: an agent wrote the statements (two independent checks found nothing
  false), and a lead agent with eleven provers proved them; the hypotheses of Section 7 were then
  dropped from the library and from the Challenge, whose new statements were reviewed against the
  TeX source.
- `lean4-banach-probability`: an agent wrote the statements and the bridges to the project
  (checked by an independent agent); two lead agents, for the Khintchine inequalities and for UMD
  theory, proved them in separate worktrees with their own provers, and a third finished
  Randrianantoanina's Corollary 4.5 by his route. An integration agent proved and dropped the ten
  remaining hypotheses (the Challenge's Theorem 1.4 reviewed against the TeX source) and moved
  Theorem 1.2 to the paper's route.
- `lean4-calculus-of-variations`: an agent copied the project's general calculus of variations
  into the package (checked by an independent agent), and provers proved what remained, among
  them Müller's laminates, Kuhn–Freudenthal interpolation and Dacorogna's formula by Müller's
  proof. An integration agent moved the project onto the package and redid Corollary 1.6 by
  distributional second derivatives and Proposition 7.2 with smooth test maps (reviewed against
  the TeX source); another agent redid Dacorogna's Theorem 5.20 by
  Conti–Dolzmann–Kirchheim–Müller's proof (two reviews against the source).
- A lead agent, in a worktree, redid with its provers the departures that needed no package:
  Corollary 5.3 (polar coordinates), Theorem 1.3 (a) and Corollary 5.4 (Hölder's inequality and
  `∫_{ℝ³}`), the witness of Corollary 1.6, Proposition 5.2 (the implicit function theorem),
  Proposition 6.1 (the multinomial moments), Proposition 4.2 and Remark 4.5 (mollification), and
  one step of Šverák's Lemma 1; an independent reviewer found no departure left.
- The main session merged the work, built, and ran the audit, the route check and Comparator (the
  last with copies of the packages, which its sandbox needs until they are pinned by git). An agent
  wrote the READMEs of `Morrey/Common/External/`, and a final pass cleaned up the project and the
  packages. Then an agent rewrote this paper's README, report, credits and metadata.
- Afterwards, `lean4-banach-probability` re-proved the triangle inequality for Schatten norms by
  the argument of an open source (Bourin and Zhang, arXiv:2610.30538, Proposition 3.13), and the
  project's `schattenNorm_add_le` became the package's theorem (commit `452cccc`). The documents
  were then checked independently (see Review) and corrected.

Figures, from 2026-11-21 22:36 (UTC−6), the user's request, to commit `6ae4899`
(2026-11-22 05:26 UTC−6), the last commit of the proofs before the documents were rewritten:

- elapsed time: 6.8 h;
- sub-agents: 103 (29 launched by the main session, the others by lead agents), at most 17 running
  at once, 2 resumptions, 37.3 h of working time; 6,105 tool calls; tokens: 10.22 M output,
  38.89 M input, 1,186 M cache reads;
- main session: 141 tool calls; tokens: 0.17 M output, 0.37 M input, 68 M cache reads;
- model calls: `claude-opus-5-5`, 168 by the main session and 5,722 by the sub-agents;
  `claude-haiku-5-5`, 2 (sub-agents).

These are the figures of the whole session in that window. Besides this paper, they include the
follow-up notes (`NEXT.md`) of this paper and of Šverák's with their checkers, the redone step of
Šverák's Lemma 1, and the revision of the procedure with its evaluation runs. They leave out the
rewriting and the check of the documents and the re-proof of the Schatten triangle inequality,
which came after. From `scripts/session_stats.py` on the session transcript, with `--since` and
`--until` at the two times above.
