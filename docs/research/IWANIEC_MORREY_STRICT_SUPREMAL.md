# A strict global supremal Jensen principle and eventual power-Jensen restoration

Date: 23 November 2026. **Result:** a hand-proved all-integrand,
all-exponent consequence of *published polyconvexity of compact
connected isotropic sets*, with a precise strictness statement.
No new proof of the p≥4 global polyconvexity conjecture or
Morrey is claimed; no Lean/CI validation or independent review.
The convexity-of-sets input is Conti–De Lellis–Müller–Romeo (2003),
Theorem 2.1 (also Cardaliaguet–Tahraoui).

## 1. Stronger than the previously recorded supremal inequality

**Strict maximum principle.** Let p>0 and let
\(F:\mathbb R^{2\times2}\to[0,\infty)\) be finite-valued,
continuous, SO(2)×SO(2)-isotropic, positively
p-homogeneous and rank-one convex.
Let \(\mu\) be **any compactly supported probability
measure** satisfying the exact matrix and determinant
moment identities
\[
   \langle\mu,\mathrm{id}\rangle=A,\qquad
   \langle\mu,\det\rangle=\det A.
\]
Suppose \(c:=F(A)>0\). Then
\[
 \boxed{
 \mu(\{F>c\})=0
 \quad\Longrightarrow\quad
 \mu(\{F<c\})=0.}                              \tag{1}
\]
In words: when no support energy exceeds the
base energy, **all support energies must equal
the base energy almost surely**. Merely
requiring the determinant moment, not
gradient compatibility, is sufficient.

Equivalently,
\[
 \boxed{
 \mu(\{F<c\})>0
 \quad\Longrightarrow\quad
 \mu(\{F>c\})>0.}                              \tag{2}
\]
This is strictly stronger than the earlier
supremal Jensen inequality \(F(A)\le
\operatorname{ess\,sup}F\): it excludes
nonconstant energy laws that **saturate**
the supremal Jensen inequality at a
positive-energy base.

## 2. Proof: interior points in lifted minors space

Put \(\Phi(B)=(B,\det B)\in\mathbb R^5\) and
\(K_c=\{B:F(B)\le c\}\).

**Step 1 (published set theorem).**
By the [previous all-level note](IWANIEC_MORREY_LEVELSETS.md),
each \(K_c\) is polyconvex as a set.
Indeed positive homogeneity and F≥0 make K_c
star-shaped; finite rank-one convexity makes
it closed and lamination convex. Truncate by
a sufficiently large Frobenius ball,
preserving compactness, isotropy,
star-shaped connectedness and lamination
convexity, then apply Conti et al. (2003).
Thus for any R>0,
\(K_{c,R}=K_c\cap\overline B_R\) is
polyconvex, and
\[
 C_R=\operatorname{conv}\{\Phi(B):B\in K_{c,R}\}
 \quad\text{satisfies}\quad
 \Phi^{-1}(C_R)=K_{c,R},
 \tag{3}
\]
where inverse image is taken along the
physical minors graph.

**Step 2 (a strict sublevel point lifts to
the FIVE-DIMENSIONAL INTERIOR).**
Fix \(B\) with F(B)<c, choose R>|B|,
and take δ>0 sufficiently small that
all matrices in the δ-neighborhood of B
belong to K_{c,R}. For the four
coordinate rank-one matrices \(E_{ij}\),
\[
 \Phi(B\pm\delta E_{ij})-\Phi(B)
 =\pm\delta(E_{ij},\mathrm{cof}B:E_{ij}),
\]
since det E_{ij}=0. These give four
linearly independent tangent directions
in \(\mathbb R^5\). For
\(I=\operatorname{diag}(1,1)\) and
\(D=\operatorname{diag}(1,-1)\),
\[
 \frac{\Phi(B+\delta I)+\Phi(B-\delta I)}2
       =\Phi(B)+(0,\delta^2),
\]
\[
 \frac{\Phi(B+\delta D)+\Phi(B-\delta D)}2
       =\Phi(B)-(0,\delta^2).
\]
Both averages belong to \(C_R\).
Together with the ± coordinate
directions, they form the ten vertices
of a full-dimensional 5D crosspolytope
centered at \(\Phi(B)\).
Therefore
\[
                 \Phi(B)\in\operatorname{int} C_R.
\tag{4}
\]
This is the key point that fails for a
purely convex scalar graph such as y=x²:
the 2×2 determinant has both positive
and negative quadratic directions.

**Step 3 (integrate, then radially leave
the sublevel).** Suppose the premise
of (1) holds but \(\mu(\{F<c\})>0\).
Compactness of the support and
continuity permit choosing a positive-mass
set \(F\le c-\epsilon\), whose lifted
points have a **uniform** small interior
ball in a common \(C_R\) by Step 2.
The remaining support lies in \(C_R\).
A convex average with positive mass
on uniformly interior points is itself
an interior point, so the moment identity
gives \(\Phi(A)\in\operatorname{int} C_R\).

For sufficiently small \(t>0\),
\(\Phi((1+t)A)\in C_R\), because \(\Phi\)
is continuous. Polyconvexity of
\(K_{c,R}\) from (3) implies
\((1+t)A\in K_c\), so
\(F((1+t)A)\le c\).
But p-homogeneity gives
\(F((1+t)A)=(1+t)^p c>c\).
Contradiction. Hence (1)–(2). QED.

The proof needs c>0. At F(A)=0,
nonnegative energies already imply
ordinary Jensen at A, but there is
no analogous strict radial
boundary contradiction.

## 3. Universal consequence for powers: a fixed witness cannot persist forever

Let μ be as above and assume a **strict
average Jensen deficit** for F:
\(\int F\,d\mu < F(A)=c\), c>0.
Then \(\mu(F<c)>0\), so (2) forces
\(\mu(F>c)>0\).

Choose \(\eta>0\) and \(\theta>0\)
such that
\[
 \mu(\{F\ge(1+\eta)c\})\ge\theta.
\]
Such constants exist because
\(\{F>c\}\) is a countable union of
these stricter superlevels.
For every real
\[
             q\ge\max\left\{
 1,\frac{\log(1/\theta)}{\log(1+\eta)}
                              \right\},
\]
we have the **ordinary** Jensen inequality
for the **same fixed μ** and
the powered integrand \(F^q\):
\[
 \int F(B)^q\,d\mu(B)
 \ge\theta(1+\eta)^q c^q
 \ge c^q=F(A)^q.                              \tag{5}
\]
For q≥1, F^q remains nonnegative,
isotropic, positively pq-homogeneous
and rank-one convex, since powers
are convex and nondecreasing on
[0,∞).

Therefore a putative minors-Jensen
counterexample for F **cannot be
extended to all large p merely by
raising F to powers while keeping
one fixed minors-compatible law**.
Any family of counterexamples at
arbitrarily large powered exponents
would need to vary its witness
measure (or the underlying integrand).
The threshold q is **not uniform
over all μ or all F**, so this is
not a proof of polyconvexity of F^q
for any universal finite q.

The same argument applies to compactly
supported homogeneous gradient Young
measures, because their determinant
and matrix moments are compatible.
A finite law suffices for the
polyconvexity tests, but the principle
itself has no cardinality cutoff.

## 4. Scope and novelty

The strict maximum principle (1) is
global in dimension 2, p, F, base
and compactly supported measures.
It is a **deduction** from the
published 2003 isotropic-set
theorem and elementary geometry of
the determinant graph, rather than
a novel proof of that theorem.
The exact crosspolytope identities
can be replayed independently in
[the rational control](../../research/audit/iwaniec_strict_supremal_exact.py).

**Not established:** the desired
ordinary Jensen inequality
\(\int F\,d\mu\ge F(A)\)
for arbitrary μ, or the global
polyconvexity of every nonnegative
isotropic p≥4 rank-one-convex
integrand. A law can have some
energies above c and sufficiently
many below c to make the average
smaller. The result only
forces the distribution to cross
both sides of c, not that the
average is nonnegative.
No Lean build or independent
peer review of the hand argument
is claimed.
