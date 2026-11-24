module

public import Morrey.HomogeneousIsotropic.Main
public import Agazzi.Quasiconvex

/-!
# The Burkholder function is quasiconvex: the exponents `1 < p < 2`, and every `p > 0`

For `1 < p < 2` the Burkholder function is quasiconvex. This is claimed as Corollary 2 of the
preprint of A. Agazzi et al., *Sharp higher integrability theory, Part I: the `L^p`-norm of the
Beurling–Ahlfors transform*, arXiv:2609.28311v2. The package lean4-iwaniec is the Lean
formalization with which that preprint was audited; it proves the statement
(`Agazzi.quasiconvex_burkholder`), and it is taken from there. With it:

* `quasiconvex_burkholder`: `burkholder p` is quasiconvex for `1 < p < 2`;
* `quasiconvex_of_rankOneConvex_of_lt_two` (**Corollary 1.6 (a)**): for `1 < p < 2`, a
  nonnegative, isotropic, positively `p`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is
  quasiconvex;
* `quasiconvex_of_rankOneConvex_of_pos` (**Corollary 1.8**): the same for every `p > 0`.

The numbers are those of the paper, `docs/HomogeneousIsotropic/paper/main.tex`.
-/

@[expose] public section

open CalculusOfVariations

namespace HomogeneousIsotropic

variable {p : ℝ} {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ}

/-- **The Burkholder function is quasiconvex for `1 < p < 2`** (Agazzi et al.,
arXiv:2609.28311v2, Corollary 2): `Agazzi.quasiconvex_burkholder` of the package lean4-iwaniec,
whose conformal and anticonformal parts are those of this library. -/
theorem quasiconvex_burkholder (hp1 : 1 < p) (hp2 : p < 2) : Quasiconvex (burkholder p) :=
  Agazzi.quasiconvex_burkholder p hp1 hp2

/-- **Corollary 1.6 (a).** For `1 < p < 2`, a nonnegative, isotropic, positively
`p`-homogeneous, rank-one convex integrand on `ℝ^{2×2}` is quasiconvex. -/
theorem quasiconvex_of_rankOneConvex_of_lt_two (hp1 : 1 < p) (hp2 : p < 2)
    (h0 : ∀ A, 0 ≤ F A) (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F)
    (hrc : RankOneConvex F) : Quasiconvex F :=
  quasiconvex_of_rankOneConvex_of_burkholder hp1.le hp2 h0 hiso hhom hrc
    (quasiconvex_burkholder hp1 hp2)

/-- **Corollary 1.8.** For every `p > 0`, a nonnegative, isotropic, positively `p`-homogeneous,
rank-one convex integrand on `ℝ^{2×2}` is quasiconvex. For `0 < p < 1` it is `0`, for `p = 1` it
is convex, for `1 < p < 2` this is Corollary 1.6 (a), and for `p ≥ 2` it is polyconvex. -/
theorem quasiconvex_of_rankOneConvex_of_pos (hp : 0 < p) (h0 : ∀ A, 0 ≤ F A)
    (hiso : IsIsotropic F) (hhom : IsPosHomogeneous p F) (hrc : RankOneConvex F) :
    Quasiconvex F :=
  quasiconvex_of_rankOneConvex_of_pos_of_burkholder hp h0 hiso hhom hrc
    fun h1 h2 => quasiconvex_burkholder h1 h2

end HomogeneousIsotropic
