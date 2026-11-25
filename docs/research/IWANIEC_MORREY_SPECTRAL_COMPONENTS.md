# Nonhomogeneous isotropic Morrey: spectral-component selection and rank-deficient supremal Jensen

24 November 2026. **New hand theorem for arbitrary compact isotropic
lamination-convex sets, without connectedness, at every rank-deficient
base.** Also an explicit obstruction to universal heat dissipation
even for smooth uniformly strictly rank-one-convex polyconvex
integrands. The previous heat two-form criterion remains a sufficient
criterion for individual energies, but is not universally feasible.

The set theorem uses the formalized Agazzi truncated determinant
quasiconvexity and the published connected-set theorem of Conti,
De Lellis, Müller and Romeo (2003). It is independent of the signed
homogeneous candidate under separate audit. No new Lean verification,
independent referee review, or priority claim. **The integral Jensen
inequality for arbitrary nonhomogeneous isotropic rank-one-convex
functions remains open, even at the rank-deficient bases studied
here.** Do not confuse the supremal inequality with Morrey.

## 1. Stop rule for universal componentwise heat descent

The [previous note](IWANIEC_MORREY_VECTOR_DESCENT_NOGO.md) gives
a sufficient exact-two-form criterion for heat dissipation,
motivated by [Bruno--Pasqualotto, arXiv:2608.06367](https://arxiv.org/abs/2608.06367).
That criterion cannot hold for all isotropic RC integrands, even
if they are smooth and uniformly strictly RC.

Work on the 2pi-periodic two-torus, with normalized Lebesgue measure.
Let v=cos x+cos y and u_0=(v,v^2). Initially det Du_0=0 everywhere.
Under componentwise heat flow, putting a=e^(-t), b=e^(-4t), c=e^(-2t),
the components become

    u_t^1 = a (cos x+cos y),
    u_t^2 = 1+(b/2)(cos 2x+cos 2y)+2c cos x cos y.

Differentiation gives exactly

    det Du_t = 2a(c-b) sin x sin y (cos x-cos y).

Using the elementary averages E sin²=1/2, E sin² cos²=1/8,
E sin² cos=0, and independence of the two torus coordinates,

$$
\fint(\det Du_t)^2=\tfrac12 e^{-2t}(e^{-2t}-e^{-4t})^2.
$$

This is zero initially and positive for every finite t>0.
The integrand F(X)=(det X)^2 is polyconvex, hence QC and RC.
Thus universal heat descent already fails for a polyconvex energy.

For a uniform strict RC example use

    F_e(X)=(det X)^2+(1/1000)||X||_F².

Both terms are polyconvex. Along rank-one lines the second term
provides a uniform positive second-derivative lower bound.
Parseval (or direct integration) gives

    E||Du_t||_F² = a²+b²+2c².

At t=log 2 this is 97/256, compared with 4 initially, while
the determinant-square term has increased by 9/2048. Consequently

$$
\fint F_e(Du_{\log 2})-\fint F_e(Du_0)
=\frac9{2048}+\frac1{1000}\left(\frac{97}{256}-4\right)
=\boxed{\frac{99}{128000}}>0.
$$

These are actual smooth compatible periodic gradients with zero
affine base. They do not violate QC. Rescaling the spatial
period gives the same example on the unit torus. The two-form
criterion would imply heat monotonicity, so a globally valid
exact correction satisfying the pointwise PSD conditions cannot
exist for F_e. This rules out a universal proof by the *fixed
componentwise heat flow*; it does not exclude subtracting
already-QC terms, using energy-dependent flows, or other
integrated inequalities. Do not pursue universal feasibility
of the previously proposed heat PDE.

## 2. Spectral components of arbitrary compact isotropic sets

For X in R^(2x2) write s(X)=||X||op and delta(X)=det X/s(X)
(the signed smaller singular value; zero at X=0). Define its
interval of possible column norms

$$
I(X)=[|\delta(X)|,s(X)].
$$

The norm |Xv| for a unit vector v takes every value of I(X),
including both endpoints. Let K be a nonempty compact
SO(2)xSO(2)-invariant lamination-convex set. Define

$$
T(K)=\bigcup_{X\in K} I(X)\subset[0,\infty).
$$

Here lamination convexity means that every segment with
rank-one-connected endpoints in K stays in K. Rank-one convex
sublevel sets have this property.

**Component lemma.** The connected components of K correspond
exactly to the connected components J of the compact real set
T(K), by
$$
K_J=\{X\in K:I(X)\subset J\}.
$$
Every K_J is compact, connected, isotropic and lamination convex.
In particular it is polyconvex as a set by Theorem 1 of
[Conti--De Lellis--Müller--Romeo (2003)](https://doi.org/10.1016/S1631-073X(03)00333-9).
If a component J does not contain zero, then det has a strictly
constant sign on K_J.

**Proof.** For a fixed r in T(K), consider the set of all X in K
with r in I(X). Any two such X,Y can be linked by a path inside
this same set. Indeed choose proper right rotations so that the
norm of the first column of each is r, and proper left rotations
so that the first columns become the SAME vector r e_1. (For
r=0 both columns are zero without the latter rotations.)
The rotations can be connected to the identity by paths of
proper rotations, preserving I. The rotated matrices share
their first column, so the segment between them has rank at
most one and lies in K. Every point on that segment still has a
first column of norm r, hence its interval contains r. Rotate
back along the appropriate orbit. Thus the fiber is path
connected.

For a connected component J of T(K), define the compact graph
    E_J={(X,r):X in K, r in I(X) intersection J}.
Its projection onto J is continuous, surjective and has
connected fibers by the preceding argument. It follows that
E_J is connected: otherwise a decomposition into two nonempty
disjoint compact relatively open pieces would, by connectedness
of each fiber, give two disjoint nonempty compact images
covering J. This contradicts connectedness of J. Its image
under projection onto X is K_J, since every interval I(X)
belongs entirely to a single component of T(K). Therefore
K_J is connected. Conversely a connected subset of K cannot
span two such J: its continuous image under s would be a
connected subset of T(K) meeting both. This proves the
component correspondence.

A connected component of K is compact, invariant (the orbits
are connected), and lamination convex (each allowed segment
is connected). The cited connected-set theorem applies.
If zero is outside J, all |delta| in K_J are strictly positive,
so continuity of the determinant on the connected K_J gives
constant sign. QED.

## 3. Top spectral component selection for every base

We use the already proved quasiconvex kernels

$$
K_r^e(X)=(s(X)-r)_+(r+e\delta(X)),\qquad e\in\{-1,1\}.
$$

These are scaled or reflected copies of the truncated determinant
L plus a determinant term; see
[Agazzi.quasiconvex_integrandL at the pinned commit](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Quasiconvex.lean).
No sign assumption on the kernels is made.

**Theorem A (top spectral component).** Let nu be a compactly
supported probability law of matrices with barycenter A and
correct determinant moment. Assume it satisfies Jensen for
K_r^e for every r>0, e=+/-1 (in particular any compact homogeneous
gradient Young law does). Suppose supp nu is contained in a
compact isotropic lamination-convex K. Put

    R=max {s(X): X in supp nu},

and let J=[a,b] be the component of T(K) containing R.

(a) If a=0, the entire support belongs to K_J, and A belongs
to K_J.

(b) If a>0, let sigma in {+1,-1} be the determinant sign on K_J.
Then
$$
\boxed{\sigma\delta(A)\ge a,\qquad s(A)\le R.}
$$
In particular I(A) is contained in J and the base has the same
orientation as the top component. We do not claim A is in K_J
in this case, or that lower components have zero mass.

**Proof.** For a=0, J contains [0,R]. Every support matrix
has its interval entirely in J, so is in K_J. The component
lemma and correct matrix and determinant moments imply A in
K_J by its polyconvexity as a set.

For a>0, there are gap radii r in (0,a) outside T(K) arbitrarily
close to a from below: otherwise [a-epsilon,a] would belong
to T(K) and the component J would extend left. Every support
matrix of determinant sign different from sigma, or determinant
zero, has s<a. In fact these s values are bounded strictly
below a: the set of support matrices with sigma det<=0 is
compact, and if it is nonempty its maximum s cannot be in
[a,R], since that interval lies in J and K_J has sign sigma.

Choose the gap radii sufficiently near a that all these
other-sign matrices have s<r. Because r is outside T(K),
every X in supp nu with s(X)>r has |delta(X)|>r. It also
has determinant sign sigma. Consequently

    K_r^(-sigma)(X) < 0    if s(X)>r,
    K_r^(-sigma)(X) = 0    if s(X)<=r.

There is positive mass with s(X)>r, since a support point
attains R>r and this is an open condition. Thus the average
kernel is strictly negative. Jensen forces
K_r^(-sigma)(A)<0, hence sigma delta(A)>r. Take gap radii
tending to a. The norm Jensen inequality s(A)<=R follows
from ordinary convexity of the operator norm and the mean
matrix identity. This proves (b). QED.

**Corollary B (rank-deficient hull theorem).** For any compact
isotropic lamination-convex K, if a compact gradient Young law
is supported in K and its mean A has rank <=1, its ENTIRE
support and A belong to the component of K containing rank-one
or zero matrices. If no such component exists, there is no
such law.

Indeed delta(A)=0, so Theorem A(b) is impossible.
Theorem A(a) gives the conclusion. The component containing
rank-deficient matrices is unique if it exists, because all
such intervals contain 0. No finite bound on the number of
components of K, radii, support atoms, or gradient frequencies
is required. This conclusion works for the abstract law
defined by the indicated kernel tests, not just for actual
gradients.

This removes the connectedness requirement of the published
compact-set theorem for the rank-deficient-base quasiconvex
hull assertion. It does NOT remove connectedness for
polyconvexity or prove the full disconnected-set theorem
at invertible bases.

## 4. Consequences for arbitrary isotropic RC integrands

Let F be any finite-valued globally isotropic RC integrand
on real 2x2 matrices. It is continuous. Given a compact
gradient Young law nu with rank-deficient barycenter A,
put c=ess sup_nu F and choose R strictly greater than all
support radii and s(A). The compact set

    K={X: F(X)<=c, s(X)<=R}

is isotropic and lamination convex (F convex on rank-one
lines, and the norm ball convex). The law is supported in K.
Corollary B therefore gives

$$
\boxed{F(A)\le \operatorname{ess\,sup}_{\nu}F(X)
                 \quad(\operatorname{rank} A\le1).}
$$

This supremal Jensen inequality requires NO nonnegativity,
homogeneity, connected sublevel sets, differentiability,
or exponent restrictions. The same conclusion at arbitrary
A holds if the top component J has a=0. In any hypothetical
strict supremal violation at an invertible base, the top
component of the sublevel set must be separated from 0
and have the same orientation as A, and I(A) must be
contained in its spectral interval.

**Strict version.** If F is strictly rank-one convex,
rank A<=1, and F(X)<=F(A) almost surely, then F(X)=F(A)
almost surely. To see this, set c=F(A) and choose R as above.
The entire support lies in the single polyconvex component
K_0 containing A. Suppose a support point B satisfies F(B)<c.
A small full matrix ball about B is contained in K and, being
connected and containing B, in K_0.

For the minors lift M(X)=(X,det X), the point M(B) is interior
to conv M(K_0) in R^5. Indeed the lifts at B+/-eps E_ij
give opposite tangent directions spanning four dimensions,
because each E_ij has rank one; the averages of the lifts
at B+/-eps I and B+/-eps diag(1,-1) give opposite pure fifth
directions (0,+/-eps²). Their convex hull contains a small
five-dimensional neighborhood of M(B). The convex combination
of a positive-mass neighborhood of that lift, uniformly inside
conv M(K_0), with the remaining law makes the mean lift
M(A) interior as well. Thus some full matrix neighborhood
of A belongs to K_0, since K_0 is polyconvex and the minors
map continuous. In particular F<=F(A) on that neighborhood,
contradicting strict convexity on any rank-one segment through A.
QED.

**Integral Jensen is not established.** A law can put some
positive mass above F(A) and still have average below F(A).
Neither component selection nor the strict supremal
statement excludes that. One must control the probabilities
of different energy levels, rather than only the support.
The old affine-shell completeness obstruction remains valid
at rank-one nonzero bases.

## 5. A useful pointwise rank-one comparison at zero

There is also a direct consequence of the interval geometry
for every isotropic RC F at zero, independent of gradient
compatibility. Set U(r)=F(diag(r,0))-F(0), a nonnegative
nondecreasing function by rank-one convexity and evenness.
For X_+,X_- with det D_+>0 and det -D_-<0 (D_->0),
suppose their spectral intervals meet at r. Rotate both
to the same first column of norm r as in Section 2. Their
determinant-balanced barycenter is rank at most one and has
operator norm at least r. Thus rank-one Jensen gives
$$
\boxed{\frac{F(X_+)-F(0)}{D_+}+
       \frac{F(X_-)-F(0)}{D_-}
\ \ge\left(\frac1{D_+}+\frac1{D_-}\right)U(r).}
$$
In particular strictly negative-energy points on opposite
orientations have disjoint intervals. Theorem A is stronger
at the support level because the kernel inequalities enforce
a global component constraint, not merely pairwise
noninteraction. The displayed inequality by itself does
not yield an arbitrary-gradient integral Jensen theorem;
no universal matching of positive and negative determinant
mass on intersecting intervals is asserted.

## 6. Verification and disposition

The checker
[heat_spectral_component_exact.py](../../research/audit/heat_spectral_component_exact.py)
was run in Python/SymPy:
    Exact heat Jacobian identity, heat-energy increase, and strictified gap: 9/2048 99/128000
    Exact spectral-gap sign controls passed.

The component proof uses elementary topology, exact rank-one
geometry, the formalized L inequalities, and the published
connected-set theorem. Finite arithmetic checks are not
used to infer the component theorem. No Lean proof or novelty
claim for the new results.

**Next genuine target:** weighted/integral Jensen, beginning
with rank-deficient bases for arbitrary nonhomogeneous
isotropic F. The supremal problem at those bases is closed
at hand-proof level; the weights of different levels remain
uncontrolled. The top-component result also restricts the
full disconnected-set problem at invertible bases.
Do not continue the false universal fixed-heat dissipation
or fixed-vector-projection descent steps. No fixed-wave,
exponent, or number-of-components ladder is necessary for
the result above. General isotropic Morrey and unrestricted
Morrey remain open.
