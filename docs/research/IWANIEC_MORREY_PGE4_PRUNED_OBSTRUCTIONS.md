# Global pruning of the p≥4 two-test support obstruction

23 November 2026. **This is an exact simplification of the established
Dacorogna–Koshigoe (1993) support criterion, not a solution of
the universal p≥4 polyconvexity conjecture.**

Let p>2 and let F(A)=||A||op^p h(det A/||A||op²) be globally
rank-one convex, isotropic and nonnegative, with h differentiable
at an interior base t∈(-1,1). Let H=h(t), M=h'(t), and define

A(a,s)=a^p h(s)+(p-1)H-a[pH+M(s-t)],
K(a,s)=(a-1)(t-as),
L=((1+t)M-pH)/(1-t),
U=(pH+(1-t)M)/(1+t).

The global poly-affine support exists exactly when some
c∈[L,U] satisfies A(a,s)+cK(a,s)≥0 for every
a≥0 and s∈[-1,1].

## Global structural theorem

**All constraints with K(a,s)=0 are automatic** from rank-one
convexity. Furthermore **the orientation interval is nonempty**.
Consequently, the support fails **if and only if** at least
one of the following occurs:

1. A test with K>0 gives a lower bound
   c≥−A/K that strictly exceeds U.
2. A test with K<0 gives an upper bound
   c≤−A/K that is strictly below L.
3. Two tests, one K>0 and one K<0, give
   incompatible bounds
   −A₁/K₁>−A₂/K₂.

The proof works for *every* real p>2 and arbitrary differentiable
isotropic homogeneous rank-one-convex profile; it is independent
of the rational-polynomial and QE restrictions.

**Proof.** At a=1, K=0 and
A(1,s)=h(s)-h(t)-h'(t)(s-t)≥0
by convexity of h, which follows by restricting F
to the rank-one line diag(1,s).
For a≠1 and K=0, t=as; the matrix
diag(a,t) lies on the rank-one line
diag(z,t) through diag(1,t), and
A(a,t/a) equals the rank-one tangent gap
F(diag(a,t))−F(diag(1,t))−
(a−1)(pH−tM)≥0. At a=0, K=−t
unless t=0; when t=0, A(0,s)=(p−1)H≥0.
These cover every zero-K case.

For the orientation interval,
U−L=2[pH−2tM]/(1−t²).
The acoustic Legendre–Hadamard necessary condition
(or the conformal-orbit rank-one argument) yields
pH−2tM≥0 for a globally rank-one-convex isotropic F,
hence L≤U. Each K>0 test gives a lower half-line
for c; each K<0 gives an upper half-line.
An intersection of such half-lines with [L,U]
is empty exactly in one of the three cases above.
The two-test incompatibility inequality can be
written without division as A₁K₂>A₂K₁
when K₁>0>K₂. QED.

**Why this matters:** For a globally admissible integrand,
the general five-disjunct exact query in
[the prior two-test note](IWANIEC_MORREY_PGE4_TWO_TEST_QE.md)
contains two logically impossible branches
(K=0 and empty orientation interval).
The remaining three are *the entire*
global obstruction mechanism. This is a
sound exact reduction of the computational search,
not a finite enumeration of all profiles.
No general theorem excluding the three
remaining obstructions has been proved.

**Important:** This pruned query is equivalent to
polyconvexity failure **only after** independent
verification of global rank-one convexity and
nonnegativity, and use of the published conformal
support theorem. Without those premises,
retain the original unpruned/direct four-atom query.
A nonpolyconvexity witness is not automatically
a nonquasiconvexity witness.
