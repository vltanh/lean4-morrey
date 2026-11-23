# Kristensen: smoothing a rank-one convex polynomial that is not quasiconvex

**Sources.** J. Kristensen, *On the non-locality of quasiconvexity*, Ann. Inst. H. Poincaré Anal.
Non Linéaire 16 (1999), Proposition 2 and its proof (pp. 6–7, read from a scan of the article);
S. Heinz, PhD thesis (2008), which was not consulted.

**Statement used by Cassese** (Corollary 5.2, "a standard smoothing argument applied to the
polynomial integrand"). For `m ≥ 3`, a homogeneous quartic polynomial `P : ℝ^{2×m} → ℝ` that is
rank-one convex and not quasiconvex at `0` gives a smooth `h` and `c, C > 0` with
`D²h (A) [H, H] ≥ c |H|²` for every `A` and every rank-one `H`, `c |A|² ≤ h (A) ≤ C (1 + |A|²)`,
and `h` not quasiconvex at `0`.

**Lean.** [`Smoothing.lean`](Smoothing.lean): the proposition `External.Kristensen.Smoothing`, in
the form Cassese applies it, proved by `smoothing_holds`, from
`CalculusOfVariations.Smoothing.exists_smoothing` of the package `CalculusOfVariations`, which
holds on every `ℝ^{d×m}` for every smooth rank-one convex integrand that is not quasiconvex at `0`
(homogeneity and `m ≥ 3` are not used).

**Proof.** Kristensen's:

- cut off the polynomial outside a large ball;
- add `k ξ (|X|)` with `ξ` convex, nondecreasing and quadratic far out to restore rank-one
  convexity on the transition annulus;
- then add `ε |X|²` for the uniform Legendre–Hadamard condition, with `ε` so small that the
  failure of quasiconvexity survives.

Kristensen leaves the rank-one convexity of the cut-off function ("it is not hard to see")
unwritten; it is supplied along his lines. Departures (see the module docstring):

- the cut-offs are functions of `|X|²` instead of `|X|` (Kristensen's `ξ_s` exists only for
  `s < 3`, and he does not say how `s` is chosen);
- an additive constant makes `h ≥ c |A|²` hold at `0`;
- `ε` is chosen independently of the cut-off radius.

**Who uses it.** Cassese's Corollary 5.2 (`Cassese.corollary5_2`,
[`Morrey/Cassese/NonLocality.lean`](../../../Cassese/NonLocality.lean)), applied to the quartic of
Theorem 1.3 lifted to `ℝ^{2×m}`.
