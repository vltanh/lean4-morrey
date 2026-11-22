module

public import CalculusOfVariations.RankOneConvex.LocallyLipschitz
public import CalculusOfVariations.Quasiconvex.RankOneConvex
public import CalculusOfVariations.Quasiconvex.Domain
public import CalculusOfVariations.Quasiconvex.Periodic

/-!
# Rindler and Dacorogna: rank-one convex functions and quasiconvexity

F. Rindler, *Calculus of variations*, Springer 2018; B. Dacorogna, *Direct methods in the calculus
of variations*, 2nd ed., Springer 2008. Cassese quotes Lemma 2.1 from Rindler, Lemma 5.6, and
Lemma 2.2 from Rindler, Propositions 5.1 and 5.3, and Dacorogna 2008, Propositions 5.11 and 5.13,
cited together for the three assertions of the lemma (TeX 468–487).

What was read. Dacorogna 2008 ([D08]), and the second edition of Rindler's book (Graduate Texts in
Mathematics 310, Springer, 2026; [R2]); the first edition, which the paper cites, was not obtained,
so its results are matched with those of the second edition by content. Lemma 5.6, as the paper
quotes it, is Lemma 5.9 of [R2]. Of the three assertions of Lemma 2.2, [R2] has the first as
Proposition 5.6, the second as Lemma 5.2 (i), and the third as an exercise; its Proposition 5.1 is
"all convex functions are quasiconvex", so whether the numbers 5.1 and 5.3 of the first edition are
these results could not be checked. Each statement is proved, in the textbook terms of the package
`CalculusOfVariations`, by its source's argument:

* Lemma 2.1 (`lemma5_6`): [R2], Lemma 5.9 (pp. 114–115), through the bound along rank-one lines
  (5.10) and the singular value decomposition;
* "quasiconvex ⇒ rank-one convex" (`rankOneConvex_of_quasiconvex`): [R2], Proposition 5.6 (pp.
  111–113), laminates on a cube with faces orthogonal to the rank-one direction, cut off near its
  boundary;
* the independence of the domain (`quasiconvexAtOn_iff`): [D08], Proposition 5.11 (pp. 172–173), and
  [R2], Lemma 5.2 (i) (p. 106), extension by zero and rescaling;
* the periodic form (`quasiconvexAtOn_iff_periodic`): [D08], Proposition 5.13 (pp. 173–174); [R2]
  has it as an exercise (Problem 5.2).

The last two are stated at one matrix `A`, as in the paper; the sources state them for functions
that are quasiconvex at every matrix, and their proofs fix the matrix.

Integrands are lower semicontinuous and locally bounded, as in Cassese (Section 1.5). The sources
ask for Borel measurability and local boundedness; only the measurability is used of the lower
semicontinuity. Quasiconvexity is tested on the unit cube, as in Cassese's Definition 2.1 ([R2]: on
the unit ball, [D08]: on every bounded open set), with Lipschitz test maps that vanish outside the
domain.
-/

@[expose] public section

namespace External.Rindler

open CalculusOfVariations

variable {d m : ℕ}

/-- **Lemma 2.1** (`cs-lem2.1`) of Cassese, citing Rindler, Lemma 5.6: a rank-one convex
function `f : ℝ^{d×m} → ℝ` is locally Lipschitz. (`Matrix.of` identifies `ℝ^{d×m}` with
`Fin d → Fin m → ℝ`, with its product metric.)

The statement assumes only that `f` is real-valued and rank-one convex; the paper states the lemma
for rank-one convex *integrands* (lower semicontinuous and locally bounded), a weaker statement, and
Rindler's definition of rank-one convexity asks for local boundedness and Borel measurability. The
stronger form is the one needed: in Proposition 2.4 the paper uses the infimum `G`, real-valued and
rank-one convex, as a rank-one convex minorant, without showing that it is an integrand (a gap of
the paper, inventory E21). The formal proofs of Propositions 2.4 and 2.5 and of the envelope steps
get its continuity from this lemma.

Proof: [R2], Lemma 5.9 (quoted by the paper as Lemma 5.6 of the first edition), in the package
(`CalculusOfVariations.RankOneConvex.locallyLipschitz`): for `A, B ∈ B_r (F)` with
`rank (A − B) ≤ 1`, convexity along the ray from `B` through `A` bounds `|f (A) − f (B)|` by
`osc (f; B̄_{2r} (F)) / r · |A − B|` (5.10); for general `A, B`, the singular value decomposition of
`B − A` gives a path of `min d m` Frobenius-orthogonal rank-one steps, and the Cauchy–Schwarz
inequality the bound (5.9). Gap fill: the local boundedness, which in [R2] is part of the
definition, is proved (`f` is convex in each entry). -/
theorem lemma5_6 {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f) :
    LocallyLipschitz fun X : Fin d → Fin m → ℝ => f (Matrix.of X) :=
  RankOneConvex.locallyLipschitz hf

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, first assertion: a quasiconvex integrand is rank-one
convex. Cassese cites Rindler, Propositions 5.1 and 5.3, and Dacorogna 2008, Propositions 5.11
and 5.13, for the whole of Lemma 2.2 (see the module docstring).

Proof: [R2], Proposition 5.6, in the package (`CalculusOfVariations.rankOneConvex_of_quasiconvex`):
a rank-one matrix is `a ⊗ n`; on a cube with two faces orthogonal to `n` (the unit cube after an
orthogonal change of variables, a Householder reflection, through the independence of the domain)
the laminates `x ↦ F x + k⁻¹ h (k x · n) a` (`h` the sawtooth with slopes `1 − λ` and `−λ`) have the
gradients `F + (1 − λ) a ⊗ n` and `F − λ a ⊗ n`; cut off near the boundary, with a diagonal choice
of the cut-off and of `k`, they are test maps whose energies converge, which gives
`f (F) ≤ λ f (F + (1 − λ) a ⊗ n) + (1 − λ) f (F − λ a ⊗ n)` at every `F`, that is, convexity along
every rank-one line. -/
theorem rankOneConvex_of_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (hf : Quasiconvex f) :
    RankOneConvex f :=
  CalculusOfVariations.rankOneConvex_of_quasiconvex hlsc hbdd hf

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, second assertion: quasiconvexity at `A` does not depend
on the bounded open domain of the test maps. Cassese cites Rindler, Propositions 5.1 and 5.3, and
Dacorogna 2008, Propositions 5.11 and 5.13, for the whole of Lemma 2.2 (see the module docstring).
The domain is assumed nonempty (`hne`), which the paper does not say but needs: for `Ω = ∅` the
condition holds for every `f` (the only test map is `0`, and both sides vanish), so the equivalence
would fail for every `f` that is not quasiconvex at `A`. ([D08], Proposition 5.11, does not say it
either.)

Proof: [D08], Proposition 5.11, and [R2], Lemma 5.2 (i), in the package
(`CalculusOfVariations.quasiconvexAtOn_iff`): extend the test map by zero and put a translated and
scaled copy of its domain inside the other domain; the unit cube is the intermediate domain. "⇒":
`Ω` lies in a large cube; "⇐": `Ω` contains a small cube. Gap fill: the extended map's gradient
vanishes almost everywhere outside the domain of the test map; in [D08] this is in the definition of
the test maps and in [R2] the domains are Lipschitz, and for Lipschitz maps vanishing outside an
arbitrary bounded open set it is proved (a Lipschitz map has zero gradient almost everywhere on its
zero set). -/
theorem quasiconvexAtOn_iff {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hlsc : LowerSemicontinuous f)
    (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) {Ω : Set (Fin m → ℝ)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtOn Ω f A :=
  CalculusOfVariations.quasiconvexAtOn_iff hlsc hbdd A hΩ hb hne

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, third assertion: quasiconvexity at `A` is equivalent
to the inequality for periodic Lipschitz test maps on the torus `𝕋^m = ℝ^m / ℤ^m`. Cassese cites
Rindler, Propositions 5.1 and 5.3, and Dacorogna 2008, Propositions 5.11 and 5.13, for the whole of
Lemma 2.2 (see the module docstring).

Proof: [D08], Proposition 5.13, in the package
(`CalculusOfVariations.quasiconvexAtOn_iff_periodic`). "⇒": for a periodic `φ`, the maps
`ν⁻¹ φ (ν x)` have the energy of `φ` by periodicity, and converge to `0` uniformly with bounded
gradients; multiplied by cut-offs `η` equal to `1` on `[1/j, 1 − 1/j]^m` they are test maps with
bounded gradients, and the energies differ by at most a constant times the measure of the boundary
layer, since `f` is locally bounded. "⇐": a test map on the cube extends periodically, Lipschitz
because it vanishes on the boundary of the cube. ([D08] takes the same scale for the cut-off and for
the period; the package chooses them separately.) -/
theorem quasiconvexAtOn_iff_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtPeriodic f A :=
  CalculusOfVariations.quasiconvexAtOn_iff_periodic hlsc hbdd A

end External.Rindler
