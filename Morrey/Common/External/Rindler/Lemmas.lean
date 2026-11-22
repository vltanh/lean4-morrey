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
cited together for the three assertions of the lemma (TeX 466–488). Both books are paywalled and
were not consulted, so the citations below are the paper's ("as cited by the paper"), and which of
the four results gives which assertion is not verified. Each statement is proved, in the
textbook terms of the package `CalculusOfVariations`, by a named standard argument from an open
source (S. Müller, *Variational models for microstructure and phase transitions*, lecture notes,
MPI MiS Leipzig, 1998), as the rules allow when a source's proof is not accessible (reason (d)):

* Lemma 2.1 (`lemma5_6`): Müller, Definition 4.2, Remark 3 (separately convex functions are
  locally Lipschitz);
* "quasiconvex ⇒ rank-one convex" (`rankOneConvex_of_quasiconvex`): Müller, Lemma 4.3 (laminates
  on a cube with faces orthogonal to the rank-one direction);
* the independence of the domain (`quasiconvexAtOn_iff`): Müller, Definition 4.2, Remark 2
  (extend by zero, translate and scale the domain), with the vanishing of the gradient of a
  Lipschitz map almost everywhere on its zero set in place of Müller's assumption `|∂U| = 0`,
  which the paper does not make (a gap fill of the cited argument, reason (a));
* the periodic form (`quasiconvexAtOn_iff_periodic`): Müller, Proposition 4.19 (a cut-off near the
  boundary and a rescaled periodic map).

The proofs are in the package; each statement here is the package's, under the paper's name.
Integrands are lower semicontinuous and locally bounded, as in Cassese (Section 1.5).
-/

@[expose] public section

namespace External.Rindler

open CalculusOfVariations

variable {d m : ℕ}

/-- **Lemma 2.1** (`cs-lem2.1`) of Cassese, citing Rindler, Lemma 5.6: a rank-one convex
function `f : ℝ^{d×m} → ℝ` is locally Lipschitz. (`Matrix.of` identifies `ℝ^{d×m}` with
`Fin d → Fin m → ℝ`, with its product metric.)

The statement assumes only that `f` is real-valued and rank-one convex, as in Rindler; the paper
states the lemma for rank-one convex *integrands* (lower semicontinuous and locally bounded), a
weaker statement. The stronger form is the one the paper needs: Propositions 2.4 and 2.5 and the
envelope formulas apply Lemma 2.1 to the infimum `G`, which is real-valued and rank-one convex but
not yet known to be an integrand (its continuity is what makes it one); the paper does not note
this (a gap of the paper, inventory E21).

Proof: Rindler's book was not accessible; the standard argument of Müller 1998, Definition 4.2,
Remark 3 (`CalculusOfVariations.RankOneConvex.locallyLipschitz`): a rank-one convex `f` is convex
along every coordinate direction `E_{ij}` (a matrix of rank one), and a function convex in each
entry is locally Lipschitz (`Matrix.locallyLipschitz_of_convexOn_single`: bounds above at the
vertices of a cube and below by reflection, a Lipschitz bound along each coordinate line, and a
path that changes one entry at a time). -/
theorem lemma5_6 {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hf : RankOneConvex f) :
    LocallyLipschitz fun X : Fin d → Fin m → ℝ => f (Matrix.of X) :=
  RankOneConvex.locallyLipschitz hf

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, first assertion: a quasiconvex integrand is rank-one
convex. Cassese cites Rindler, Propositions 5.1 and 5.3, and Dacorogna 2008, Propositions 5.11
and 5.13, for the whole of Lemma 2.2 (as cited by the paper; see the module docstring).

Proof: the books were not accessible; the argument is the laminate argument of Müller 1998,
Lemma 4.3 (which credits Fonseca 1988, Theorem 2.4), in the package
(`CalculusOfVariations.rankOneConvex_of_quasiconvex`): a rank-one matrix is `a ⊗ q`; on a cube
with faces orthogonal to `q` (the unit cube after an orthogonal change of variables, a Householder
reflection, through the independence of the domain), the laminates
`v_k = min (k⁻¹ h (k x · q̂), dist_∞ (x, ∂Q)) a` (`h` the sawtooth with slopes `1 − λ` and `−λ`)
vanish on the boundary, and their gradients differ from those of the sawtooth laminate only on a
set of measure `→ 0`, which gives `f (P) ≤ λ f (P + (1 − λ) a ⊗ q) + (1 − λ) f (P − λ a ⊗ q)` at
every `P`, that is, convexity along every rank-one line. -/
theorem rankOneConvex_of_quasiconvex {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (hf : Quasiconvex f) :
    RankOneConvex f :=
  CalculusOfVariations.rankOneConvex_of_quasiconvex hlsc hbdd hf

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, second assertion: quasiconvexity at `A` does not
depend on the bounded open domain of the test maps. Cassese cites Rindler, Propositions 5.1 and
5.3, and Dacorogna 2008, Propositions 5.11 and 5.13, for the whole of Lemma 2.2 (as cited by the
paper; see the module docstring). The domain is assumed nonempty (`hne`), which the paper does not
say but needs: for `Ω = ∅` the condition holds for every `f` (the only test map is `0`, and both
sides vanish), so the equivalence would fail for every `f` that is not quasiconvex at `A`.

Proof: the books were not accessible; the argument is Müller 1998, Definition 4.2, Remark 2 ("if
`f` takes values in `ℝ` it suffices to extend `φ` by zero outside `U` and to translate and scale
`U`"), in the package (`CalculusOfVariations.quasiconvexAtOn_iff`): quasiconvexity on the unit cube
is quasiconvexity on every cube `x₀ + R (0, 1)^m` (change of variables); "⇒": `Ω` lies in a large
cube; "⇐": `Ω` contains a small cube. Gap fill of the cited argument (reason (a)): Müller assumes
`|∂U| = 0`, which the paper does not; quasiconvexity on a set passes to its measurable subsets
because the gradient of a Lipschitz map vanishes almost everywhere on its zero set (Lebesgue
density), so no condition on `∂Ω` is needed. -/
theorem quasiconvexAtOn_iff {f : Matrix (Fin d) (Fin m) ℝ → ℝ} (hlsc : LowerSemicontinuous f)
    (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) {Ω : Set (Fin m → ℝ)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtOn Ω f A :=
  CalculusOfVariations.quasiconvexAtOn_iff hlsc hbdd A hΩ hb hne

/-- **Lemma 2.2** (`cs-lem2.2`) of Cassese, third assertion: quasiconvexity at `A` is equivalent
to the inequality for periodic Lipschitz test maps on the torus `𝕋^m = ℝ^m / ℤ^m`. Cassese cites
Rindler, Propositions 5.1 and 5.3, and Dacorogna 2008, Propositions 5.11 and 5.13, for the whole of
Lemma 2.2 (as cited by the paper; see the module docstring).

Proof: the books were not accessible; the argument is Müller 1998, Proposition 4.19, in the package
(`CalculusOfVariations.quasiconvexAtOn_iff_periodic`). "⇒": for a periodic `φ`, the maps
`ψ_j = η_{1/j} · j⁻² φ (j² ·)` vanish off the cube, where `η_δ` is a Lipschitz cut-off equal to
`1` on `[δ, 1 − δ]^m`; their Lipschitz constants are bounded in `j`, they agree with
`j⁻² φ (j² ·)` on `(δ, 1 − δ)^m`, where `∫ f (A + ∇φ (j² x)) dx = ∫ f (A + ∇φ)` by periodicity,
and the boundary layer has measure `1 − (1 − 2/j)^m → 0`, on which the integrands are bounded;
so `f (A) ≤ ∫ f (A + ∇ψ_j) → ∫ f (A + ∇φ)`. "⇐": a test map on the cube extends periodically,
Lipschitz because it vanishes on the boundary of the cube. -/
theorem quasiconvexAtOn_iff_periodic {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hlsc : LowerSemicontinuous f) (hbdd : IsLocallyBounded f) (A : Matrix (Fin d) (Fin m) ℝ) :
    QuasiconvexAtOn (unitCube m) f A ↔ QuasiconvexAtPeriodic f A :=
  CalculusOfVariations.quasiconvexAtOn_iff_periodic hlsc hbdd A

end External.Rindler
