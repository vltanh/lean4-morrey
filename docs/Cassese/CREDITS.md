# Credits

How the formalization of Cassese (2026) was made, from the run log and the session transcript.

## Who

- Author and maintainer: The-Anh Vu-Le, who asked for the paper to be formalized in this
  repository, independently of the author's own Lean code; chose, in the second round, to build
  every cited result that was large but feasible; asked, in the third round, for every result to be
  proved unconditionally; obtained, for the fourth, most of the cited books and articles that the
  session could not, for the fifth, Sarason (1967) and Helson–Lowdenslager (1961), and, for the sixth,
  McConnell (1984), so that the cited results could follow them; and asked, for the fifth, for the sources'
  proof of the non-commutative Khintchine inequality, with its general theory made reusable.
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
  from a proof; versions 4.2.1 to 4.3.1 (commits `8d291b1` to
  `f9198d5`) in the fourth; versions 4.3.1 and 4.3.2 (commit `8e884d5`) in the fifth; version 4.3.2 in the
  sixth, after which version 4.3.3 (commit `80b7f6f`) was written.
- Other Lean code: the proofs were written without consulting the author's Lean formalization
  ([MorreyTwoComponentsLean](https://github.com/Gabriele-Cassese/MorreyTwoComponentsLean)) or Conti,
  Dolzmann and Dondl's ([so3-r1c-and-not-qc](https://github.com/sergioconti/so3-r1c-and-not-qc)), and
  nothing from them was used; by the session's transcripts, no sub-agent that wrote proofs opened
  either. Files of both were downloaded, and parts of them displayed, by the searches for earlier
  formalizations and for the literature, and by the checks of the documents:
  - on 21 November 2026, before the proofs of Šverák's and Cassese's papers, by the main session:
    metadata, file lists, READMEs and first lines of declarations of both, and docstrings and the
    beginning of `Sverak.lean` in so3-r1c-and-not-qc. The main session then wrote Šverák's
    definitions and statements, the first version of Cassese's `Defs.lean`, and a few short lemmas on
    the definitions;
  - on 21 and 22 November 2026, by agents that wrote no proofs: the same, and, of so3-r1c-and-not-qc,
    `Statement.lean`, the beginning of `Defs.lean` and passages of `Sverak.lean` and `Periodic.lean`,
    and, of MorreyTwoComponentsLean, about 180 lines of `Morrey2x3.lean` (a search for follow-up work,
    on 21 November); whether these passages contain proofs was not checked;
  - on 22 November 2026, after the proofs that overlap with them had been committed, by two
    literature searches for the packages. MorreyTwoComponentsLean: repository metadata, the file
    list, the first 80 lines of the README, the first lines of definitions (some with a one-line
    body) and of some theorem statements, one docstring line, no proof. so3-r1c-and-not-qc:
    metadata, README passages, `Statement.lean` and `Defs.lean` in part, the docstrings of eight
    files, the first lines of declarations, the proofs of six lemmas of one to three lines, and the
    beginning of two others.

  A mechanical comparison on 22 November 2026 looked for common runs of 20 tokens (comments and
  imports removed) between the Lean code of this repository and its packages (775,356 tokens) and
  each of the two: 702 of those tokens are in such a run with MorreyTwoComponentsLean, in 11 files,
  the longest run 33 tokens (two lines), and 123 with so3-r1c-and-not-qc, in 3 files, the longest
  22. (For parts of Mathlib of the same size: 0 to 227.) The downloaded copies were then deleted. That
  comparison (11:41) is older than the code of the fifth and sixth rounds in `lean4-harmonic-analysis` and
  `lean4-banach-probability`; by the transcripts, no sub-agent that worked on the proofs of these rounds
  opened either repository, and the literature searches of the fifth excluded both.
- Review: no person has reviewed the proofs. Independent AI agents checked the statements against
  the TeX source (twice), the formal proofs against the paper's (three reviewers) and the report,
  in the second round. In the third: the statements of each package (and the bridges between
  `lean4-banach-probability` and the project), package proofs against their sources, the
  statements of the Challenge and of Proposition 7.2 that changed (against the TeX source), the
  redone proofs of the paper, the proof of Dacorogna's Theorem 5.20 against
  Conti–Dolzmann–Kirchheim–Müller's (two reviews), and every recorded departure under version
  4.2.0 of the procedure (an audit). Then an independent agent checked the rewritten documents of
  the three papers (README, report, credits, metadata) against the code, the audit output, the TeX
  source and the cited works. Last, two independent reviewers checked the package's redone proofs
  of Borell's and Burkholder's results against Borell (1979) and Burkholder (1988). In the fourth:
  agents compared the cited results with their sources, and independent reviewers checked the
  packages' redone proofs against the sources, the statements of [`Morrey/Common/External/`](../../Morrey/Common/External), the
  restated Proposition 2.7 (6) and the updated documents. In the fifth: independent reviewers checked
  the new statements of the packages, and their proofs against the sources; another checked the updated
  documents. In the sixth: the same, for McConnell's theorems.

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
  last with copies of the packages, which its sandbox needed while the lakefile required them by
  path; the packages are now published and pinned by commit, and Comparator runs without copies).
  An agent wrote the READMEs of [`Morrey/Common/External/`](../../Morrey/Common/External), and a final pass cleaned up the project and the
  packages. Then an agent rewrote this paper's README, report, credits and metadata.
- Afterwards, `lean4-banach-probability` re-proved the triangle inequality for Schatten norms by
  the argument of an open source (Bourin and Zhang, arXiv:2610.30538, Proposition 3.13), and the
  project's [`schattenNorm_add_le`](../../Morrey/Cassese/Square.lean#L441) became the package's theorem (commit `452cccc`). The documents
  were then checked independently (see Review) and corrected.
- A check of the sources followed. Borell (Séminaire de Probabilités XIII, 1979) and Burkholder
  (Astérisque 157–158, 1988) were obtained from Numdam, and the package's proofs of
  hypercontractivity and of Burkholder's inequality and function were redone by their arguments
  (the square function inequality already followed Burkholder's), with the statements unchanged
  (`lean4-banach-probability` commits `e8ecfc0`, `db668a4`, `44382e8`; the project's
  [`Morrey/Common/External/`](../../Morrey/Common/External) READMEs and docstrings in commit `3a9f2dd`). Burkholder's
  Annals of Probability papers (1973, 1981, 1984), open access on Project Euclid, could not be
  obtained (the site refused automated download); the user supplied them in the fourth round. Two independent reviewers checked the redone
  proofs against these sources and found no departure.

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
rewriting and the check of the documents, the re-proof of the Schatten triangle inequality and
the check of the sources, which came after. From `scripts/session_stats.py` on the session
transcript, with `--since` and `--until` at the two times above.

## Fourth round: the cited sources (22 November 2026)

The user obtained most of the cited books and articles that the session could not (Section 7 of the
report lists those that are still missing), so that the cited results could be proved by their
sources' arguments.

How it was made:

- Five agents compared, read-only, the proofs of the cited results with their sources: Burkholder's
  papers and Osękowski; HNVW I and II; Bhatia and Pisier–Xu; de Leeuw and Dragičević; Dacorogna,
  Rindler, Kinderlehrer and Pedregal. A sixth compared the Khintchine inequality with Lust-Piquard
  and Pisier, when that article arrived. Two more read Burkholder's Annals articles for the first.
- Four lead agents redid, in worktrees of the packages, every proof that differed from its source
  (except the Khintchine inequality's), with six provers: in `lean4-banach-probability`, the items of HNVW (extrapolation, dyadic and
  complex UMD constants, zig-zag functions, decoupling, Kahane–Khintchine), and Burkholder's
  inequality and the sharpness of its constant by Osękowski's proofs; in `lean4-harmonic-analysis`,
  the transference by HNVW's proof; in `lean4-calculus-of-variations`, Rindler's lemmas,
  Dacorogna's formula by Kinderlehrer and Pedregal's proof, and Dacorogna's Theorem 5.20 by his own.
  These replaced, among others, the proofs of the third round by Borell, Burkholder (1988; kept for
  (13) and (14)), Müller, Conti–Dolzmann–Kirchheim–Müller and Pisier. The upper bound of the
  non-commutative Khintchine inequality was redone in the fifth round.
- Five independent agents compared the redone proofs with the sources; they found no wrong step, and
  their findings on the documentation, and a few on the code, were applied.
- An integration agent moved the project onto the new packages: [`Morrey/Common/External/Osekowski`](../../Morrey/Common/External/Osekowski)
  holds Theorem 2.3 and the sharpness, the directory of Borell's results was removed, Dacorogna's
  Theorem 5.20 is stated without continuity, and Proposition 2.7 (6) with the equivalence for complex
  spaces (commits `d065590` to `7b2462d`). Three independent agents checked the statements of
  [`Morrey/Common/External/`](../../Morrey/Common/External) against the sources and Proposition 2.7 (6) against the TeX source.
- An agent updated the documents of the three papers, and two independent agents checked the changed
  passages against the TeX source, the sources, the code and the transcripts; their findings were
  applied.

Figures, from 2026-11-22 08:04:48 (UTC−6), when the user supplied the sources, to commit `7b2462d`
(11:02:24 UTC−6), the last commit of the proofs:

- elapsed time: 2.95 h;
- on the steps above, up to the integration: 27 sub-agents (8 for the comparisons, 4 leads and 6
  provers, 5 reviewers, the integrator and its 3 reviewers), 8.7 h of working time, 2,183 tool calls;
  tokens: 2.9 M output, 16.3 M input, 410 M cache reads; 1,305 model calls;
- the whole session in that window: 60 sub-agents (27 launched by the main session), at most 12
  running at once, 6 resumptions, 17.4 h of working time; 4,437 tool calls; tokens: 5.45 M output,
  28.73 M input, 655 M cache reads. Besides the steps above, it includes the publication of the
  packages, their literature reviews and Palomar entries, the revision of the procedure with its
  evaluation runs, and the first part of the fifth round;
- main session: 166 tool calls; tokens: 0.16 M output, 1.50 M input, 104 M cache reads;
- model calls: `claude-opus-5-5`, 168 by the main session and 2,343 by the sub-agents.

From `scripts/session_stats.py` on the session transcript and on the sub-agents' transcripts, with
`--since` and `--until` at the two times above. The figures leave out this update of the documents
and its check.

## Fifth round: the non-commutative Khintchine inequality (22 November 2026)

The comparison of the fourth round had shown that the upper bound of Proposition 6.3 followed none of
the sources that the paper cites. The user asked for their proof, with its general theory made reusable
and the shorter proof documented ("can we pull out the general theory part for reuse? and just
faithfully follow, with documented shortcut?"). The theory was first written as a package of its own; the
user then agreed to include it in `lean4-harmonic-analysis`.

Sources: Lust-Piquard–Pisier (1991), Sarason (1967) and Helson–Lowdenslager (1961) were supplied by the
user, as Pisier–Xu and the two volumes of HNVW had been; Astérisque 247 (1998), Tomczak-Jaegermann
(1974), Maurey–Pisier (1976) and Helson–Lowdenslager (1958) were found by the session in open archives.
Lust-Piquard (1986) and Bourgain (1986), for which the user looked, were not found. Section 7 of the
report lists the other works behind the sources that were not read (Simon, Gohberg–Krein, Rubio de
Francia, the books of Helson and Hoffman and, since the sixth round, Burkholder (1983); no attempt to
obtain them is recorded), with what stands for them. McConnell (1984) was one of them; it was supplied in
the sixth round.

How it was made:

- One lead agent, with 45 sub-agents that it launched: 20 provers, 3 checkers of statements, 11
  reviewers that compared the proofs with the sources, 10 for revisions and one that checked the
  documents. They worked in a worktree of `lean4-banach-probability` and in the new package.
- First version: statements (commits `f3b4bc0`, now in the history of `lean4-harmonic-analysis`, and
  `3b05655` of `lean4-banach-probability`, 10:12), every proof (`d0d081b`, `0a4084a`, 10:49), with the
  factorization of `H¹` functions by Bekjan and Xu's argument; then, after three reviews, the
  transference by HNVW's proof and the revisions (`f119fde`, `6fb92de`, 11:27–11:28; `a1bc4f2`, `8962532`, 11:54).
- Second version: type 2 of the Schatten classes by Tomczak-Jaegermann's proof, K-convexity by HNVW's,
  and Lust-Piquard and Pisier's duality for matrices that need not be symmetric (`3ecee00`, `434bb1e`,
  12:17); reviewed and revised (`3efa520`, 12:44).
- Third version: the factorization by Sarason's Theorem 4, with the theory of Helson and Lowdenslager
  that it rests on (`1fecd57`, 13:55); compared with the sources (`e012030`, 14:10); Paley's inequality
  with the exact factorization (`6760549`, 14:22).
- The package was merged, with its history, into `lean4-harmonic-analysis`, which now requires
  `lean4-banach-probability` (`46e966b`, 14:23, to `72d9c71`, 14:46); a last review of the redone proofs
  and the revisions after it: `ec00cb2`, 15:12. The proof by exchangeable pairs stays in
  `lean4-banach-probability` (`ncKhintchine_upper`).
- The main session moved [`Morrey/Common/External/PisierXu`](../../Morrey/Common/External/PisierXu) onto the new proof, and stated Theorem 6.1
  for all real square matrices as one theorem, [`External.PisierXu.theorem6_1_general`](../../Morrey/Common/External/PisierXu/Khintchine.lean#L59), in place of two
  (`af922cc`, 15:20).
- Besides, an agent reviewed the literature and the formalizations of the vector-valued part (checked by
  another), and an agent with two reviewers made the eight Palomar entries of `lean4-banach-probability`
  (not submitted). An agent updated the documents of this repository, and an independent agent checked
  the changed passages.

Figures, by the times of the commits (UTC−6): 5.1 h from `f3b4bc0` (10:12:27) to `af922cc` (15:20:06), of
which the first 50 minutes are in the window of the fourth round. From the transcripts, to the same
commit:

- the lead agent and its sub-agents (launched from 09:48 on): 46 agents, at most 6 running at once,
  13.8 h of working time; 3,078 tool calls; tokens: 4.02 M output, 23.93 M input, 367 M cache reads;
  1,557 model calls, all `claude-opus-5-5`;
- the whole session after the window of the fourth round (from 11:02:24): 46 sub-agents, at most 8
  running at once, 3 resumptions, 15.0 h of working time; 3,342 tool calls; tokens: 4.04 M output,
  28.21 M input, 559 M cache reads; main session: 124 tool calls; tokens: 0.11 M output, 0.49 M input,
  53 M cache reads; model calls: `claude-opus-5-5`, 109 by the main session and 1,777 by the sub-agents.
  Besides the work above, these include the documents of the fourth round and the end of the work on
  the Palomar entries of the other two packages.

The figures leave out the update of the documents and its check.

## Sixth round: (III.3) by McConnell's theorem (22 November 2026)

For (III.3), the bound for every choice of signs on which their proof of Paley's inequality rests,
Lust-Piquard and Pisier refer to Bourgain (1986), "see also" McConnell (1984). The fifth round had used
HNVW I, Theorem 5.7.10 (2), instead, which gives (III.3) on average over the signs. When it ended, the
session named McConnell's article to the user as optional, and did not recommend it: its proof, as far as
the session knew, uses stochastic integration. It had not read the article. The user supplied it, and the
session's statement proved wrong: the proofs of the theorems use only the finite-dimensional
distributions of the hitting places of a Brownian motion, that is, chains with independent Cauchy
increments. The step was then redone by McConnell's proof.

How it was made:

- The lead agent of the fifth round, resumed, read the article and wrote the statements; an agent checked
  them, and five provers proved them in a worktree of `lean4-harmonic-analysis` (commit `beab475`, 16:40).
- Two reviewers compared the proofs of Theorems 1.1 and 1.3 with the article, and two agents applied their
  findings (`d63fd67`, 17:21). (III.3) for every choice of signs (`0be3345`, 17:24); two more statements in
  the Palomar entry VectorValuedLittlewoodPaley, and the documents of the package (`0d11d96`, 17:27). A last
  reviewer compared the whole change with the sources; all its remarks but one, on a commit message, were
  applied (`8af8279`, 17:40), and these last edits were not reviewed again.
- The averaged route stays in the history of the package (`ec00cb2`).
- The main session moved this repository onto `8af8279` (`fd2c773`, 17:55). An agent updated the
  documents, and an independent agent checked the changed passages.
- Besides, from 15:17 to 16:22, an agent with a reviewer made three Palomar entries of
  `lean4-harmonic-analysis` for its vector-valued part (`bf0b7eb`, `0c13109`, `bebc047`; not submitted), one
  of them VectorValuedLittlewoodPaley.

Figures, from 15:59:00 (UTC−6), when the user supplied the article, to `8af8279` (17:40:41):

- elapsed time: 1.7 h, between the two times;
- the lead agent and its sub-agents: 12 agents (the lead, the checker of the statements, 5 provers, 3
  reviewers, 2 for revisions), at most 6 running at once, 3.9 h of working time; 674 tool calls; tokens:
  1.04 M output, 8.24 M input, 93 M cache reads; 355 model calls, all `claude-opus-5-5`;
- the whole session in that window, with the end of the work on the three entries: 14 sub-agents, 4.3 h
  of working time, 753 tool calls; tokens: 1.14 M output, 9.93 M input, 121 M cache reads; main session: 6
  tool calls; 7 and 402 model calls (main session and sub-agents), all `claude-opus-5-5`.

From `scripts/session_stats.py` on the session transcript, with `--since` and `--until` at the two times
above, and from the sub-agents' transcripts. The figures leave out the update of the documents and its
check.
