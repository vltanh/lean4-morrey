# Credits

How the result on nonnegative homogeneous isotropic integrands, its formal proof and its paper
were made.

## Who

- Author and maintainer: The-Anh Vu-Le, who directed the research and asked for the proof to be
  validated in Lean, extended to every exponent `p > 0`, written up and packaged for Palomar.
- Research: the author with two AI systems, ChatGPT Chat 6 Extra High (OpenAI) and Claude
  (Anthropic).
- Formal proof, Palomar files and the paper: Claude Fable 5.2 (Anthropic).
- Review: no person has reviewed the proofs or the paper.

## The research (before 23 November 2026)

- The argument for `p ≥ 2` was first written as a research note in
  [pull request 1](https://github.com/vltanh/lean4-morrey/pull/1) of this repository
  (`docs/research/IWANIEC_MORREY_PGE2_POLYCONVEXITY.md` on the branch
  `research/ledger-roadmap-2026-11-21`). The same pull request holds:
  - a second AI pass that checked the note
    (`docs/research/IWANIEC_MORREY_PGE2_INDEPENDENT_AUDIT.md`);
  - an addendum for `1 < p < 2`
    (`docs/research/IWANIEC_MORREY_ISOTROPIC_EXTENSIONS.md`);
  - numerical checks, described in the note.
- The notes were written in AI-assisted sessions with Claude. The author reports that ChatGPT
  Chat 6 Extra High worked on the problem as well; the notes do not say which part is whose.
- The pull request is not merged. This library was written from the note and the addendum.

## The formalization (23 November 2026)

- Made by Claude Fable 5.2 (`claude-fable-5-2`) in Claude Code, in one session: the main session
  and two sub-agents.
- The main session:
  - checked the note's argument by hand;
  - reorganized it so that it needs no derivative of the profile (below);
  - wrote the definitions, the one-variable inequalities, the results on profiles and the
    theorems;
  - added the exponents `0 < p < 1` (Proposition 1.7) and the statement for every `p > 0`
    (Corollary 1.8), at the author's request;
  - wrote the Palomar files: the Challenge, the Solution, the Comparator configuration and the
    metadata;
  - made the result unconditional for `1 < p < 2`, at the author's request: when the
    formalization of arXiv:2609.28311 was finished
    ([lean4-iwaniec](https://github.com/vltanh/lean4-iwaniec), made in the same session by a
    lead agent and ten sub-agents on Claude Opus 5.5), required it and removed the hypothesis on
    the Burkholder function from Corollaries 1.6 (a) and 1.8;
  - made the paper and the Lean statements say the same thing, at the author's request, taking
    the more general version where they differed: the operator norm and the paper's Burkholder
    function as Lean definitions, the equivalences of Lemma 2.1 and of isotropy in both
    directions, and a Lean theorem for each "with equality at" of the paper.
- One sub-agent proved the lemmas on conformal coordinates ([`Morrey.HomogeneousIsotropic.Coordinates`](../../Morrey/HomogeneousIsotropic/Coordinates.lean)),
  and one the lemmas on polyaffine supports ([`Morrey.HomogeneousIsotropic.Polyaffine`](../../Morrey/HomogeneousIsotropic/Polyaffine.lean)), each from
  statements given by the main session.
- The library was first named `Isotropic`. It was renamed `HomogeneousIsotropic` at the author's
  suggestion, since the results need homogeneity as much as isotropy.

How the formal proof differs from the note:

- The note differentiates the profile `h`, and treats the points where `h` is not differentiable
  by approximation. The formal proof takes any supporting line of `h`, so that no approximation
  is needed.
- The note derives the Baker–Ericksen inequality from the monotonicity along hyperbolas. The
  formal proof derives it from the first-order inequality along the chord to a rotated copy of
  the base matrix ([`IsProfile.baker_ericksen`](../../Morrey/HomogeneousIsotropic/Profile.lean#L245)).
- The note proves the Burkholder-type inequality by studying a one-parameter family. The formal
  proof uses two identities and Bernoulli's inequality ([`burkholder_support_le`](../../Morrey/HomogeneousIsotropic/Inequalities.lean#L73)).
- The statements for `p = 1`, for `p = 2` without sign condition, and the necessity of
  nonnegativity for `p > 2` are remarks in the note or the addendum; here they are theorems.
- The case `0 < p < 1` is not in the note.

## The paper (23 November 2026)

- [`paper/main.tex`](paper/main.tex) was written by the main session after the formalization, and follows the
  formal proof.
- A sub-agent checked the citations and searched the literature for earlier proofs: it read
  Guerra and Kristensen's paper (arXiv version and accepted manuscript), Dacorogna and Koshigoe's,
  and the 2026 preprints, and found no earlier proof.
- An independent sub-agent refereed the first version of the paper and the Lean statements:
  - it restated every definition and theorem of the library and looked for vacuous statements;
  - it recomputed the paper's identities symbolically and tested the supports numerically;
  - it compared each row of the paper's table with the Lean declaration;
  - it found no error in a theorem or a proof, one false remark at `p = 1`, and inaccuracies in
    remarks and in the account of the formalization, all corrected;
  - it wrote the example `(det A)²` ([`Morrey.HomogeneousIsotropic.Example`](../../Morrey/HomogeneousIsotropic/Example.lean)).
- After the review, at the author's request, the main session rewrote the paper as a main text
  with the proofs in appendices, with a table of the hypotheses that each range of the exponent
  needs, and added the case `0 < p < 1`. It then stated the results for `1 < p < 2` with no
  hypothesis on the Burkholder function, and revised the wording of the whole paper. The
  rewritten paper has not been refereed again.
