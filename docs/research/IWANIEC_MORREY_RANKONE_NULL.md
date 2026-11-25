# Anisotropic homogeneous integrands: rank-one-null recession, complete subquadratic null-line and quadratic null-plane theorems

24 November 2026. **New positive results without ANY rotational symmetry.**
The preceding one-sided degree-two theorem uses left rotations. This
note replaces that symmetry by a precise degeneracy of the rank-one
trace, and derives the exact recession in a null rank-one direction.

* For every degree 0<p<2, vanishing on one entire rank-one line
  forces ordinary convexity of a finite-valued rank-one-convex F.
* At degree two, the recession in any rank-one direction H with
  F(H)=0 is a convex piecewise-linear function of the single scalar
  cof(H):X. No isotropy, evenness, or global sign assumption is needed.
* Every finite signed positively 2-homogeneous RC integrand vanishing
  on a two-dimensional rank-one column (or row) subspace is globally
  polyconvex, with an exact convex representation using the other
  column (or row) and determinant.
* There is an all-exponent, all-direction rank-one trace inequality
  for arbitrary anisotropic profiles, with a sign consequence if the
  entire rank-one cone has zero energy.

These are hand proofs, not new Lean verification or a claim of
publication priority. The symbolic determinant and scalar algebra
checks in Section 6 were actually executed. The verified signed
homogeneous bi-SO(2) theorem remains closed. **Arbitrary homogeneous
anisotropic RC=>QC at every base remains OPEN.** These new results
cover degeneracies, not arbitrary strictly positive angular profiles.
The attempt to extend the rotation-orbit tangent support directly
to arbitrary p did not produce a general proof.

## 1. Quotient by a rank-one line

**Elementary quotient lemma.** A continuous rank-one-convex
function G on real 2x2 matrices that is invariant under translations
along a nonzero rank-one matrix H is ordinarily convex.

For any direction K with cof(H):K != 0, the determinant identity

    det(K+tH)=det K+t cof(H):K

allows a unique t making K+tH rank deficient. The restriction of G
to any line of direction K is the same as the restriction to the
corresponding line of rank-at-most-one direction K+tH, by invariance.
It is therefore convex. The directions with cof(H):K != 0 are dense,
because cof(H) is nonzero. Pass to a limit of such directions to
obtain the Jensen inequality on every line by continuity. QED.

This is specific to the 2x2 determinant relation. It is not a claim
that arbitrary directional convexity with a null direction implies
convexity in larger dimensions.

## 2. An entire exponent interval, with no symmetry

**Theorem A.** Let F be finite-valued, positively p-homogeneous
and globally RC, with 0<p<2. Suppose there exists a nonzero
rank-one H with F(H)=F(-H)=0. Then F(X+tH)=F(X) for every X
and real t. In particular F is convex and QC at every base.

**Proof.** Finite-valued rank-one convexity implies local Lipschitz
continuity (by separate convexity in the matrix entries). For fixed
X, as t tends to positive infinity,

    F(X+tH)=t^p F(H+X/t)=O(t^(p-1)),

using F(H)=0 and a Lipschitz constant in a neighborhood of H.
The analogous bound holds as t tends to negative infinity, by
F(-H)=0. Since p<2, both bounds are o(|t|). The real function
t -> F(X+tH) is convex on the whole line. Its secant slope between
any two finite points is trapped between the limiting slopes at
negative and positive infinity, both zero. Thus it is constant.
Apply the quotient lemma to prove convexity. QED.

If only F(H)=0 is known, the same argument at positive infinity
gives the useful one-sided conclusion that F(X+tH) is nonincreasing
in t. Both signs are needed for the full invariance assertion.

There is no sign assumption on the original F. For a frame-indifferent
F, the antipodal zero follows from left rotation by pi. But the
theorem itself applies with no frame indifference. This is a complete
classification of the subquadratic null-line case as a convex
function on the three-dimensional quotient. In fact every convex
function on that quotient pulls back to a convex function on matrix
space, and homogeneity is preserved.

## 3. Exact quadratic null-ray recession

Let F be finite-valued, positively 2-homogeneous and RC.
Fix any nonzero rank-one matrix H for which F(H)=0.

**Theorem B.** The finite recession

    R_H(X)=lim_{t -> +infinity} F(X+tH)/t

exists for every X and has the exact form

$$
\boxed{R_H(X)=a_H(\operatorname{cof}H:X)_+
                 +b_H(\operatorname{cof}H:X)_-}
\tag{1}
$$

for real a_H,b_H with a_H+b_H>=0.
Here r_+=max(r,0), r_-=max(-r,0).
If F>=0 then a_H,b_H>=0. No evenness is required.

### 3.1 Convexity of the recession

For fixed X, convexity on the line X+tH implies that the secant
slope (F(X+tH)-F(X))/t is nondecreasing for t>0. Homogeneity
and local Lipschitz continuity at H give

    |F(X+tH)|/t = t |F(H+X/t)-F(H)| <= C_H |X|

for all sufficiently large t, so the limit exists and is finite.
Equivalently,

    R_H(X)=lim_{eps -> 0+} [F(H+eps X)-F(H)]/eps.

The latter formula makes positive degree-one homogeneity and
rank-one convexity of R_H immediate: apply the RC inequality to
each fixed positive eps and pass to the finite pointwise limits.
It is finite-valued, hence continuous. The recession formula
also gives invariance in direction H, since replacing X by X+sH
merely shifts t by a constant in the limit. The quotient lemma
now proves that R_H is ordinarily convex.

### 3.2 The only possible nonzero variable is the determinant pairing

Write H=u tensor v. Consider the two linear subspaces

    U={u tensor w : w in R^2},
    V={w tensor v : w in R^2}.

Every matrix in either is rank deficient. On each subspace F
is an ordinary convex function, because every direction in that
subspace has rank at most one. It is nonnegative there: along
a rank-one ray, convexity and degree two imply F(K)>=0 by
comparison at tK, 0<t<1, with the segment from 0 to K.

For any K in U or V, midpoint convexity and homogeneity give
for t>=0

    0<=F(K+tH)=4F((K+tH)/2)
              <=2F(K)+2t^2F(H)=2F(K).

Consequently R_H(K)=0 on each of the two entire subspaces.
A finite convex positively degree-one function is subadditive.
If it vanishes on a linear subspace, adding a member of that
subspace does not change its value: apply subadditivity first
with that member and then with its negative. Hence R_H is
invariant along U+V.

These two subspaces have dimension two each and intersection
span(H), so their sum is three-dimensional. The determinant
pairing cof(H):K vanishes on both, and is nonzero as a linear
functional on the matrix space. Thus U+V is precisely its
kernel. The convex positively degree-one function R_H factors
through that one-dimensional quotient. Its form is (1);
convexity across zero is exactly a_H+b_H>=0. This proves
the theorem, including the nonnegative-coefficient assertion
when F>=0. QED.

### 3.3 Global implications, not only at the null ray

Convex secant slopes are bounded above by the recession, so

$$
F(X+tH)-F(X)\le t R_H(X)\qquad(t\ge0).
\tag{2}
$$

If also F(-H)=0, apply the same estimate in the opposite
direction. Since the determinant pairing is unchanged by adding
multiples of H, on every line X+R H we have two constant
bounds for all its slopes:

$$
-R_{-H}(X)\le
\frac{F(X+tH)-F(X+sH)}{t-s}
\le R_H(X)\qquad(t>s).
\tag{3}
$$

In particular, in normalized coordinates H=E11, writing the
matrix as [[a,b],[c,d]], the energy is independent of a when
d=0. Globally its dependence on a is convex and Lipschitz,
with Lipschitz constant at most C|d| for a single constant C
depending only on the four recession coefficients. This is
a structural statement for arbitrary anisotropic degree-two
RC functions with an antipodal rank-one zero.

If F is differentiable at both H and -H and F>=0, these are
global minimum points, so the two directional derivatives
R_H and R_-H vanish identically. Then (3) and the quotient
lemma give ordinary convexity on the WHOLE matrix space.
For arbitrary signed F, the previous degree-two origin theorem
permits subtracting a constant determinant to make F nonnegative.
This subtraction preserves differentiability, rank-one-null
rays, homogeneity and quasiconvexity, so in this differentiable
antipodal-null case the original F is globally polyconvex
(convex plus a determinant term). No need to assume a smooth
Hessian.

For a general nondifferentiable antipodal-null ray, (3) does
not establish full QC. For example the nonpolyconvex
Guerra--Kristensen rectified-product family has such a ray.
The remaining possible nonconvexity is the coupling of a and
d with other variables inside this exact recession bound.

## 4. Complete quadratic null-plane theorem

**Theorem C.** Let F:R^(2x2)->R be finite-valued, positively
2-homogeneous and globally RC. Suppose

    F([a,0])=0 for every a in R²,

where [a,b] denotes the matrix with columns a,b.
Then there exists a finite convex G:R² x R -> R with

$$
\boxed{F([a,b])=G(b,\det[a,b]).}
\tag{4}
$$

In particular F is polyconvex, hence QC at every matrix.
The same assertion holds for a null row subspace, or after any
invertible linear changes of input and output coordinates.
The theorem does not require F>=0, a single rotation symmetry,
or any regularity beyond finite RC.

### 4.1 Universal recession slopes in the free column

Apply Theorem B to every H=[u,0], u!=0. Its determinant
pairing with [a,b] is det[u,b]. For each u, this gives

    R_[u,0]([a,b])=A(u) det[u,b]_+ + B(u) det[u,b]_-.

Fix b. The function a -> F([a,b]) is ordinary convex,
because a variation in just one column is rank one.
Its recession as a function of u is

    r_b(u)=lim_{t -> +infinity} F([tu,b])/t,

which is finite by the preceding result (and zero for u=0).
It is convex positively degree-one by pointwise limits, and
vanishes for u parallel to b by the determinant formula.
For nonzero b, subadditivity therefore gives

    r_b(u)=A'(b) det[u,b]_+ + B'(b) det[u,b]_-.

Thus whenever det[u,b]>0 we have A(u)=A'(b), and whenever
det[u,b]<0 we have B(u)=B'(b).

For any two nonzero u1,u2 which are not negative multiples
of one another, there is a b with both determinants positive:
the two open half-planes for b intersect. Hence A(u1)=A(u2).
For negative multiples use an intermediate u3 independent of
them, applying the equality twice. This proves a universal
constant A. The same argument with negative determinants
proves a universal B. Therefore for every u,a,b,

    R_[u,0]([a,b])=r(det[u,b]),
    r(s)=A s_+ + B s_-,

with r convex by Theorem B. The case b=0 follows directly.

### 4.2 Exact shear invariance

If b!=0, apply (3) to H=[b,0]. Both recessions are zero,
since det[b,b]=0. Thus F([a+t b,b])=F([a,b]) for all t.

Every pair a,a' with det[a,b]=det[a',b] differs by a multiple
of b. Consequently the formula

    G(b,d)=F([-d J b/|b|²,b]),   b!=0,

with J the counterclockwise quarter-turn, defines a continuous
function on (R²\{0}) x R with F([a,b])=G(b,det[a,b]).
Here det[-Jb,b]=|b|². This uses no rotations of F.

The two recession inequalities between [0,b] and [a,b] give
the bounds

    F([0,b])-r(-d) <= G(b,d) <= F([0,b])+r(d).

Both bounds are locally bounded on the entire lifted space,
including b=0. Thus G has a uniform two-sided bound on every
bounded subset of its domain.

### 4.3 Convexity in all lifted variables, including the missing axis

Take independent nonzero vectors b1,b2 and any real d1,d2.
There is a unique a solving det[a,b1]=d1, det[a,b2]=d2
(two independent linear equations in a). The matrices
[a,b1] and [a,b2] are rank-one connected, since their first
columns agree. The determinant is affine on their segment.
For 0<=theta<=1, their mean column b_theta is nonzero.
Rank-one convexity proves

    G(b_theta, theta d1+(1-theta)d2)
      <=theta G(b1,d1)+(1-theta) G(b2,d2).

In particular the restriction of G to EVERY affine line in
the lifted three-dimensional space whose b-coordinate line
avoids zero and has independent endpoint b vectors is convex
on the entire line. By approximation this already proves
convexity along any segment staying in b!=0. The following
uniform bound handles the missing axis rigorously.

Fix L>0 and let M bound |G| on all points with b!=0 and
norm <=L+2 in the lifted Euclidean space; such an M exists
by the preceding two-sided bounds. For any pair of points
in the radius-L ball with b!=0 and independent b vectors,
extend the line segment by distance one beyond EACH end.
The extended line still avoids b=0 and remains in the
radius-(L+2) ball. Convexity on that line and the bound M
imply that the absolute secant slope on the original
segment is <=2M (compare with the length-one intervals at
the two ends). Thus G is 2M-Lipschitz on those pairs.
Approximate any pair with nonzero b coordinates by pairs
with independent b coordinates, using continuity away
from b=0 and the same bound on a slightly enlarged ball.
This gives a uniform local Lipschitz constant for all
pairs in the punctured ball.

Consequently G has a unique finite continuous extension to
b=0. Approximate arbitrary lifted endpoints, including those
on the missing axis, by independent b endpoints. The segment
Jensen inequality passes to the limit by continuity of the
extension. Hence the extended G is convex on ALL R² x R.
The bounds at d=0 and b->0 give G(0,0)=F(0)=0.
Therefore (4) also holds for matrices [a,0].
The representation is a globally finite convex function
of a linear column coordinate and the independent determinant
variable, which proves polyconvexity. QED.

The hypothesis can equivalently be that F vanishes on any
two-dimensional linear subspace all of whose matrices have
rank at most one. Such a subspace has a common left or right
factor: if two independent rank-one matrices have neither
factor proportional, their sum is invertible. Normalize the
common factor by an invertible coordinate change, using
transpose if necessary. Rank-one convexity and polyconvexity
are preserved by these transformations.

Thus this is an all-base theorem with NO rotation invariance
for a whole null-plane class. In comparison, the previously
proved rectified-product example vanishes at E11 and E22
individually but not on a whole common-factor plane. The
present result does not simply assume that individual null
rays can be joined into such a plane.

## 5. Universal rank-one trace estimate at every homogeneous degree

There is an additional elementary bound for arbitrary
anisotropic F, independent of any null-ray assumption.

Let p>1, let F be finite-valued positively p-homogeneous RC,
and decompose X=U+V into two rank-at-most-one matrices
(always possible, for example by the two columns).
Then

$$
\boxed{(2-p)F(X)\le F(U)+F(V).}
\tag{5}
$$

Proof. Put f(x,y)=F(xU+yV), which is separately convex and
positively p-homogeneous. For 0<t<1,

    f(t,1)<=(1-t)F(V)+t F(X),
    f(1,1/t)>=(1/t)F(X)-(1/t-1)F(U).

The second is the secant-slope inequality for the convex
function of y, between 0, 1 and 1/t. Multiply the second
by t^p and use f(t,1)=t^p f(1,1/t). Combining gives

    (t^(p-1)-t)F(X)<=(1-t)(F(V)+t^(p-1)F(U)).

Divide by 1-t and let t approach 1 from below to obtain
(5). No differentiability is needed.

For p>2, this is a global lower bound controlling the
negative part of F(X) by rank-one traces:

    F(X)>=-(F(U)+F(V))/(p-2).

It holds for EVERY rank-one decomposition, so one may
optimize over them. In particular if F vanishes on the
entire rank-one cone, F is globally nonnegative for
every p>2, despite no assumed sign or symmetry.

For 1<p<2, (5) bounds F from above instead. To get a
lower bound, use rank-one convexity at V=(X+(V-U))/2
and apply (5) to V-U:

    F(X)>=[(3-2p)F(V)-F(-U)]/(2-p).

Interchange U,V for the companion bound. Again all
rank-one values are nonnegative because p>1.

The coefficient 2-p is genuinely tied to homogeneity.
The estimate does not establish the integral Jensen
inequality for arbitrary rank-one traces. It is useful
for controlling signed energies and locating degenerate
directions, not a proof that negative parts are universally
paid for by a gradient-compatible law.

As a corollary, if the ENTIRE rank-one cone has zero
energy, then for p<2 F=0 (also directly by Theorem A,
which gives convexity and then the zero rank-one
decomposition bound). For p=2 Theorem C applies and
F([a,b])=G(b,d) is convex in (b,d). In fact in this
case G is independent of b: for each d, convexity and
the vanishing trace imply G(b,d)<=r(d), by Section 4.2
since F([0,b])=0. A finite convex function of b on all
R² bounded above is constant. Thus F depends only on
d, and degree-two homogeneity and convexity give

    F(X)=c_+ det(X)_+ + c_- det(X)_-,
    c_+ + c_- >=0.

This classification of the entire zero-rank-one-trace
degree-two case is completely anisotropic in its
hypotheses, although the conclusion forces isotropy.

## 6. Verification and next gate

The script [rankone_null_exact.py](../../research/audit/rankone_null_exact.py)
was executed using Python/SymPy. Output:

    Exact rank-one shift and common-column identities passed.
    Exact homogeneous rank-one trace bound identities passed.

These checks validate the determinant algebra, common-column
construction and scalar limit in (5). They do not replace
the analytic recession, convex-extension or quotient proofs.

**New closed gates at hand-proof level:** arbitrary subquadratic
RC with an antipodal null rank-one ray; degree-two RC with an
antipodal null rank-one ray differentiable at both rays; and
degree-two RC with an entire rank-one null plane. All three
are global all-base conclusions without any rotational symmetry.
The exact recession theorem (1)--(3) holds for every degree-two
null rank-one ray, including nonsmooth cases, and the trace
bound (5) holds for arbitrary p>1 and arbitrary RC profiles.

**Main remaining target:** the unrestricted homogeneous
anisotropic problem, in particular arbitrary positive
rank-one trace and the general nondifferentiable null-ray
case at p=2. We have NOT proved that every such integrand
can be decomposed into the new null-plane/null-ray families
plus known QC terms. The proof for one-sided rotation at
p=2 is unaffected. A direct extension of the scaled-rotation
tangent support to p!=2 did not close the frame-indifferent
all-degree gate. Do not present these partial advances as
removal of all isotropy for arbitrary homogeneous F.
