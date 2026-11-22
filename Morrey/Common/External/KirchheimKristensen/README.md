# Kirchheim–Kristensen: rank-one convex functions homogeneous of degree one

**Source.** B. Kirchheim and J. Kristensen, *On rank-one convex functions that are homogeneous of
degree one*, Arch. Rational Mech. Anal. 221 (2016).

**Statement.** Cassese quotes their theorem as Theorem 1.1: a continuous, positively
`1`-homogeneous, rank-one convex integrand has a subgradient (its epigraph has a global affine
supporting hyperplane) at every matrix of rank at most one; in particular it is quasiconvex at `0`.
It is context for Corollary 1.6, which shows that quasiconvexity can fail at a matrix of rank
two.

**Lean.** [`Theorem.lean`](Theorem.lean): the proposition
`External.KirchheimKristensen.Theorem1_1`, with no proof.

**Proof.** None: no proof of Cassese's paper uses the theorem, so it is a hypothesis of no
statement. It is stated so that every numbered result of the paper has a statement.

**Who uses it.** Nobody; the docstring of `Cassese.corollary1_6` refers to it.
