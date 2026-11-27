# Exact reduction of the homogeneous Morrey problem to almost-everywhere saturated integrands

24 November 2026. We bypass the unproved regularity of extreme points.
**Every** finite-valued positively p-homogeneous rank-one convex
integrand on real 2x2 matrices, p>1, can be approximated locally
uniformly from above by exactly p-homogeneous rank-one convex
integrands whose absolutely continuous Hessians have minimum
rank-one curvature zero almost everywhere.

The approximants are rank-one convex envelopes of data on
finitely many rays through zero. They are viscosity saturated
away from those rays. This is an exact density reduction of the
entire homogeneous anisotropic problem, not an assumption that
extreme points are smooth or that their Hessians have zero trace.
There is no sign, material symmetry, or angular polynomial
assumption on the original integrand. A finite-gradient strict
counterexample can even be transferred EXACTLY to such an
envelope, without changing its energies at the gradient atoms.

We also prove second-order Taylor differentiability a.e. for
the entire homogeneous cone using the preceding weak-Hessian
theorem, and a global exterior-laminate representation for
viscosity-saturated homogeneous integrands. At p=2 this last
result forces a null rank-one trace direction even without
smoothness, provided saturation holds in the viscosity sense
on the whole punctured matrix space.

**Limits:** no assertion that all a.e.-saturated functions are
quasiconvex. They need not be smooth, and the approximants need
not be viscosity saturated on their finitely many obstacle rays.
The previous smooth saturation theorem does not cover them.
The new density theorem, unlike the earlier smooth strictification,
preserves exact almost-everywhere saturation. It identifies a
single full-cone sufficient target. No uniform ray count for
EXACT Jensen, no new Lean proof, no priority claim. The
general homogeneous anisotropic implication remains OPEN.

The arguments below are hand proofs. They use the preceding
[weak Hessian theorem](IWANIEC_MORREY_HOMOGENEOUS_WEAK_HESSIAN.md)
and standard BV Poincare and differentiation-of-measures facts.
The elementary finite-laminate and interpolation arithmetic
checks were actually executed in the working container.

## 1. Finite-ray envelopes from above

Use the Frobenius norm on V=R^(2x2), identified with R^4.
Let F be finite, positively p-homogeneous, globally RC, p>1.
In particular F is continuous, locally Lipschitz and F(0)=0.
Write M=max_{|X|=1}|F(X)|.

Let D be a finite collection of unit matrix directions.
Require that D contain the directions of all 16 coordinate
cube vertices (with entries +/-1, divided by 2 to have unit
norm). Write

    K_D={t v: t>=0, v in D}.

It is a closed union of finitely many positive rays and contains
zero. Prescribe the data F on K_D, and define

$$
E_D(X)=\inf\left\{\sum_i\theta_i F(X_i):
 \text{finite laminate rooted at }X,\ X_i\in K_D\right\}.
\tag{1}
$$

A finite laminate here is obtained by finitely many binary
rank-one splits, allowing a trivial one-atom laminate. Each
split replaces a matrix by a weighted pair of rank-one
connected matrices with that matrix as mean. All leaf weights
are nonnegative and sum to one.

**Theorem A.** E_D is finite-valued, continuous, globally RC,
positively p-homogeneous, and

    E_D>=F everywhere,   E_D=F on K_D.

It is the largest finite-valued globally RC function below
the prescribed F data on K_D. In particular it is the largest
such function even among nonhomogeneous competitors.

**Proof.** Jensen along every finite laminate gives the
lower bound by F. For an upper bound, put r=max_i|X_i| in
coordinate notation. Successively split each entry into
the endpoints -r,+r with weights giving its original
value as mean. Each is a rank-one split. After at most
four levels all leaves are cube vertices, hence in K_D.
Their norms are 2r, giving

$$
F(X)\le E_D(X)\le 2^p M|X|^p.
\tag{2}
$$

At zero use the trivial atom. This proves finiteness.
For any rank-one split X=theta Y+(1-theta)Z, choose
near-minimizing finite laminates at Y,Z and concatenate
them below this split. Taking the error to zero proves
the RC inequality for E_D. It is continuous and locally
Lipschitz by finite RC. Positive scaling bijectively
transforms the admissible finite laminates at X into
those at tX; all costs scale by t^p. Thus E_D is exactly
homogeneous. At a point of K_D the trivial atom proves
E_D<=F, giving equality. Finally any finite RC competitor
below the data obeys Jensen for every laminate in (1),
so lies below their infimum. QED.

This construction does not require the infimum in (1)
to be attained or the depth of its near-minimizers to
be uniformly bounded.

## 2. Viscosity saturation off the prescribed rays

Say that a continuous function G is viscosity saturated
on an open set U if for any C² test phi touching G from
below at X in U (in a neighborhood of X, with equality
there), one has

$$
\min_{|H|=1,\ \det H=0}D^2\phi(X)[H,H]\le0.
\tag{3}
$$

In combination with RC this is the supersolution half
of the equation with vanishing minimum rank-one curvature.
It does NOT require classical differentiability of G.
We use the touching-from-below formulation throughout.

**Theorem B.** Every envelope E_D in (1) is viscosity
saturated on V minus K_D.

Suppose instead that phi touches E_D from below at X outside
K_D with strictly positive minimum rank-one curvature.
By continuity and compactness of unit rank-one directions,
there is a ball about X, disjoint from K_D, on which phi
has a strictly positive lower bound for its rank-one Hessian.
Choose eta>0 small so that phi(Y)-eta|Y-X|² is still RC
on this ball. Shrink to a closed radius-r ball in the
touching neighborhood. The function

    psi(Y)=phi(Y)-eta|Y-X|²+eta r²/2

is strictly below E_D on its boundary, and strictly
above E_D at X. Set G=max(E_D,psi) inside the ball and
G=E_D outside. This is continuous and globally RC:
inside the ball it is the maximum of two functions
convex on every rank-one segment, and near the boundary
it agrees with E_D by the strict boundary gap and
compactness. Local convexity of its restriction to each
rank-one line implies global convexity of that restriction.
It leaves all prescribed data unchanged. This contradicts
the maximality in Theorem A. QED.

The competitor need not be homogeneous. This is why we
proved maximality among all RC functions, not just among
homogeneous ones.

## 3. A.e. classical second-order expansions from the weak Hessian

We use the previously proved weak-Hessian theorem:
for every finite positively p-homogeneous RC F on V,
p>1, DF is locally BV and D²F is a locally finite symmetric
matrix measure. Denote its absolutely continuous density
by Q. It is rank-one nonnegative a.e.

**Theorem C.** At almost every X, this density Q(X) is an
ordinary second-order Taylor coefficient:

$$
\boxed{F(X+Y)=F(X)+DF(X):Y+
         \tfrac12 Y:Q(X)Y+o(|Y|^2),\quad Y\to0.}
\tag{4}
$$

In particular the remainder is small in ALL directions,
not only in an averaged or approximate-differentiability
sense.

### 3.1 Obtain an averaged second-order expansion

Choose X which is a differentiability point of F,
a Lebesgue point of DF and Q, and a zero Lebesgue-density
point of the singular Hessian measure. Almost every X has
these properties by local Lipschitz continuity and the
differentiation theorem for Radon measures.

Subtract the constant, affine, and quadratic terms
in (4), defining g on a neighborhood of X. Thus
g(X)=0, Dg(X)=0 and

    |D²g|(B_r(X))=o(r^4).

For a locally BV function h in dimension four, the
standard BV Poincare inequality on balls is
    avg_{B_r}|h-h_{B_r}| <= C r |Dh|(B_r)/|B_r|,
where h_{B_r} denotes its mean. Apply it componentwise
to h=Dg. This gives

    avg_{B_r}|Dg-(Dg)_{B_r}|=o(r).

The means (Dg)_{B_r} tend to zero by the choice of X.
Moreover the difference of the means over B_r and
B_(r/2) is bounded in norm by 16 times the displayed
mean oscillation. Summing these differences over
dyadic radii proves (Dg)_{B_r}=o(r): for every fixed
small epsilon all the summands at radii s<=r are
bounded by C epsilon s, and their sum is O(epsilon r).
Consequently avg_{B_r}|Dg|=o(r).

The ordinary W^(1,1) Poincare inequality applied to g
now gives avg_{B_r}|g-g_{B_r}|=o(r²). Since g_{B_r}
tends to zero by continuity, the same dyadic telescoping,
this time summing squares of the radii, gives
g_{B_r}=o(r²). Hence

    avg_{B_r}|g|=o(r²).

Equivalently, the rescalings

    f_r(Z)=[F(X+rZ)-F(X)-r DF(X):Z]/r²

converge in L¹ on every fixed bounded ball to
q(Z)=Z:Q(X)Z/2.

### 3.2 Separate convexity upgrades this to uniform convergence

We give the local compactness argument for signed functions,
rather than assuming convexity in every direction.

Suppose separately convex finite functions on R^4 are
bounded in L¹ on each compact set. They are uniformly
bounded and equicontinuous on smaller compact sets.
It suffices by rescaling to use an L¹ bound L on
[-4,4]^4. For y in [-2,2]^4, independent uniform averaging
on y+[-1,1]^4 and four ordinary convex Jensen steps
give f(y)<=L/16. Write M=L/16.

For y in [-1,1]^4 and z in [-1/2,1/2]^4, express each z_i
as a convex combination of y_i and either 2 or -2.
Choose the endpoint beyond z_i from y_i. The weight on
y_i is at least 1/2 (use endpoint 2 when z_i>=y_i
and endpoint -2 otherwise). Independent coordinate
interpolation gives an upper bound on f(z) by a convex
combination of sixteen values in [-2,2]^4, with weight
at least 1/16 on f(y). All other values are <=M. Since
f(y)<=M, we obtain

    f(z)<=M+(f(y)-M)/16.

Integrate over the unit-volume cube [-1/2,1/2]^4 and use
int f>=-L there. This proves f(y)>=M-16(M+L),
uniformly on [-1,1]^4. Ordinary convex secant-slope
bounds along the coordinates now give uniform local
Lipschitz bounds on [-1/2,1/2]^4, by changing one
coordinate at a time. Rescaling or translating the
argument proves the stated local compactness.

Every f_r above is RC, hence separately convex, because
it is obtained from F by an affine variable change,
subtraction of an affine function and positive scaling.
Its L¹ convergence gives uniform local L¹ bounds.
By the compactness just proved, every sequence r_j->0
has a locally uniformly convergent subsequence, and its
limit must be q by the L¹ convergence and continuity.
Thus the whole family converges uniformly on compact
sets to q. Taking |Z|<=1 proves (4). QED.

Notice that the Taylor quadratic itself is not required
to be convex. It is the rescalings f_r that are separately
convex; we did NOT subtract q and assume the difference
retains rank-one convexity.

## 4. Exact global saturation reduction

Let Q_D be the ac Hessian density of E_D. By Theorem C,
a.e. X outside K_D has the expansion (4).
If at such a point min_rankone Q_D[H,H]>0, the quadratic
Taylor polynomial minus a sufficiently small positive
multiple of |Y-X|² touches E_D from below locally and
still has strictly positive rank-one Hessian. This
contradicts Theorem B. Because Q_D is rank-one
nonnegative a.e. and the finite union of rays is
Lebesgue null in V, we have

$$
\boxed{
\min_{|H|=1,\ \det H=0} Q_D(X)[H,H]=0
\quad\text{for a.e. }X\in V.}
\tag{5}
$$

Thus the finite-ray envelopes are EXACTLY saturated
in the absolutely continuous Hessian sense, not merely
asymptotically small in minimum rank-one curvature.

### 4.1 Uniform density with an explicit finite angular net

Take D to include a delta-net of the unit sphere, as well
as the cube-vertex directions. From (2) on the radius-two
ball, |E_D|<=4^p M and |F|<=2^p M. Separate convex secant
bounds using unit coordinate steps give a Lipschitz bound
4*4^p M for E_D and 4*2^p M for F on the unit ball:
at differentiability points each of their four coordinate
derivatives is bounded by twice the corresponding larger
ball bound. Local Lipschitz continuity and integration
after mollification give the stated Lipschitz bounds.
They also hold on the closed ball by continuity.

For unit X choose v in D with |X-v|<=delta. Equality of
the data at v and the Lipschitz bounds imply

    0<=E_D(X)-F(X)<=8*4^p M delta.

Scale this inequality homogeneously. We obtain, for all X,

$$
\boxed{
0\le E_D(X)-F(X)\le 8\,4^p M\delta |X|^p .
}
\tag{6}
$$

The net can be chosen once for all integrands with the
same angular norm bound. For example use all normalized
nonzero integer four-vectors with coordinates in [-n,n].
For unit X round nX coordinatewise to an integer k.
The rounding error is at most one in Frobenius norm,
and k!=0 for n>=2. Normalizing k adds at most another
1/n to the distance from X, by the reverse triangle
inequality. Thus this is a 2/n-net with at most
(2n+1)^4-1 rays, already including the cube-vertex
directions. Taking n->infinity proves local uniform
approximation from above with (5). If desired use
nested nets by union, giving decreasing envelopes.

For the full normalized signed cone of the earlier
[uniform-cone theorem](IWANIEC_MORREY_HOMOGENEOUS_UNIFORM_CONE.md),
the angular bound M is uniform (subtract the canonical
determinant at degree two). Thus both the ray directions
and their number at any prescribed positive accuracy can
be selected BEFORE F or the test gradient law is known.
The only free input data are the values of F on those
finitely many rays; the envelope itself need not be
piecewise polynomial or have finite lamination depth.

### 4.2 The whole homogeneous implication is equivalent to the saturated implication

**Theorem D (exact reduction).** Fix any p>1. The following
are equivalent:

(i) Every finite positively p-homogeneous RC integrand on
V is QC at every base.

(ii) The same statement for integrands satisfying (5)
with their own ac Hessian density.

(iii) The same statement for finite-ray envelopes (1)
of arbitrary positively p-homogeneous RC data, as above.

Proof: (i) implies (ii), and (ii) implies (iii) by (5).
If (iii) holds, apply it to the sequence of envelopes
in (6). For any fixed bounded compatible gradient X=A+Dphi,
local uniform convergence of E_D to F passes the integral
Jensen inequality to F. More generally the error in (6)
is controlled by the p-th moment of the law. Hence (iii)
implies (i). QED.

This reduction covers the entire homogeneous cone; it is
not a claim that arbitrary extreme points have smooth
characteristics or that their ac trace is zero.
In particular there is no loss from working only with
a.e. saturated integrands, even though smooth saturated
integrands at p=2 satisfy the much stronger convex-plus-
determinant conclusion proved earlier.

By the earlier regularization note, a full theorem at
all p>1 also yields degree one, using a linear support
at zero and positive convex powers tending to degree
one. Degrees below one are already settled.

### 4.3 Exact preservation of a strict finite-gradient violation

If a strict homogeneous counterexample is witnessed by
a piecewise-affine periodic or zero-boundary perturbation,
its gradient law has finitely many matrices X_i. Include
their nonzero directions in D (and optionally A/|A|).
Homogeneity and equality on K_D give

    E_D(X_i)=F(X_i),   E_D(A)>=F(A).

Therefore the original strict Jensen violation persists,
with at least its original deficit and exactly the
original energies on all gradient atoms. This is an
exact transfer, not a small-deficit approximation.
Any hypothetical homogeneous violation admits such a
finite-gradient witness by smoothing and piecewise-affine
interpolation, as proved in the earlier regularization
note. There is NO bound here on the number of gradient
atoms or ray constraints of such an exact witness.

There is also a uniform positive-accuracy version for
any compact or finite-p-moment gradient law. Because the
approximations are from above, their Jensen-gap change
is bounded ABOVE by 8*4^p M delta E|X|^p; there is no need
to add a second approximation error at the base when
transferring a violation. Thus one common finite ray set
detects every violation larger than this relative error,
via its envelope data, without assuming the law finite.
This is an integrand-side reduction, not a finite
decision algorithm for gradient compatibility.

## 5. Exterior-laminate representation for globally viscosity-saturated profiles

The following is a separate global consequence of viscosity
saturation on the ENTIRE punctured space. It does not
automatically apply to the finite-ray approximants on their
obstacle rays. We state the distinction explicitly.

**Theorem E.** Let F be finite, RC and positively p-homogeneous,
p>1. If it is viscosity saturated on V\{0}, then it is
viscosity saturated at zero as well. For every R>0 and
every base A,

$$
F(A)=\inf\left\{\sum_i\theta_i F(X_i):
 \text{finite laminate rooted at }A,\ |X_i|\ge R\right\}.
\tag{7}
$$

Consequently no such F can satisfy F(X)>=k |X|^p for a
positive constant k. At p=2, every globally viscosity-
saturated F has a zero rank-one trace direction, without
any smoothness or symmetry hypothesis.

### 5.1 Removable origin for viscosity saturation

Homogeneity and angular boundedness imply differentiability
at zero, with DF(0)=0, since p>1. Suppose phi touches F
from below at zero with strictly positive rank-one Hessian.
Then Dphi(0)=0. On a small radius-r ball phi remains
strictly rank-one convex. Subtract eta |X|² for small
eta>0 to retain this property and produce a strict boundary
gap at least eta r² from F. Add a nonzero linear function
L:X with |L| small enough to retain the boundary gap.
The minimum of F minus this new test on the closed ball
is attained in its interior, because its value at zero
is zero and all boundary values are positive. It cannot
be attained at zero, since the derivative of the
difference there is -L!=0. Adding the value of this
minimum to the test gives a lower touching at a nonzero
point with strictly positive rank-one curvature. This
contradicts punctured saturation.

### 5.2 Comparison with the exterior-data envelope

Let E_R denote the infimum on the right of (7).
As in Theorem A it is finite RC, E_R>=F everywhere,
and E_R=F for |X|>=R. For finiteness, every X is the root
of a four-level coordinate laminate on the vertices of
a cube large enough to contain X and have all its
vertices outside B_R. The other properties follow by
concatenating laminates and the trivial exterior atoms.

Suppose E_R(A)>F(A) for some |A|<R. Smooth E_R by ordinary
nonnegative convolution, obtaining a smooth RC function
U uniformly close to E_R on the closed ball. Let delta>0
bound this uniform approximation error, and define

    G(X)=U(X)-delta+epsilon(|X|²-R²),

with epsilon>0 sufficiently small. Then G<=F on the
boundary, G(A)>F(A) for sufficiently small smoothing
error and epsilon, and its rank-one Hessian is strictly
positive. The maximum of G-F on the closed ball is
positive and occurs in its interior. Subtract this
maximum from G to obtain a smooth lower touching of F
there with the same strictly positive rank-one Hessian.
This contradicts viscosity saturation, including at zero
by Section 5.1. Thus E_R=F, proving (7).

Conversely, if (7) holds for every R and base, the same
local maximum construction as in Theorem B proves global
viscosity saturation: a strict lower test allows a local
RC raising supported inside a ball, which would be a
competitor below the unchanged exterior data and violate
(7). Thus (7) is an equivalent global formulation.

If F>=k |X|^p with k>0, every laminate in (7) at A=0
costs at least k R^p>0=F(0), a contradiction.
At p=2, recall the previously proved
[positive-rank-one-trace normalization](IWANIEC_MORREY_HOMOGENEOUS_REGULARIZATION.md),
Theorem C: if min_{rank H=1,|H|=1} F(H)>0, then
F-c det>=k |X|² for some real c and k>0.
Subtracting c det preserves viscosity saturation because
the determinant Hessian is zero on rank-one directions.
The coercivity contradiction applied to the shifted F
therefore proves the rank-one null direction assertion.

No conclusion that the null direction is antipodally null,
or that F is smooth there, is asserted. The hypothesis
of Theorem E is stronger than a.e. ac-Hessian saturation:
a finite-ray envelope may fail the lower-touching condition
at one of its data rays. Do not conflate these two conditions.

## 6. Verification and remaining objective

The companion
[homogeneous_ray_envelope_exact.py](../../research/audit/homogeneous_ray_envelope_exact.py)
was run with Python, using exact rational arithmetic:

    625 exact rank-one coordinate splitting controls passed.
    153 exact signed separate-convex interpolation controls passed.

These checks verify the elementary coordinate-laminate weights
and the lower-bound interpolation geometry used in the local
compactness lemma. They are NOT numerical evidence for the
viscosity or global Jensen assertions. The preceding arguments
supply their analytic proofs.

**What changed in the main gate:** we have a rigorous
whole-cone reduction to exactly a.e.-saturated ac Hessian
profiles, with viscosity saturation except on finitely many
rays. No regularity theorem for extreme points is required.
The a.e. Taylor expansion theorem validates using the weak
Hessian density in this reduction. The exterior-laminate
theorem is an additional global result for everywhere
viscosity-saturated profiles.

**Still missing:** prove Jensen for the saturated envelopes
without assuming smoothness or a fixed finite obstacle
configuration. Neither (5) nor (7) implies that the original
energy decreases under an arbitrary compatible gradient.
The determinant multiplier can vary in the ac Hessian;
saturation is about its minimum rank-one curvature, not
its trace. No finite obstacle-count bound for exact
Morrey, no proof for all a.e.-saturated functions, and no
new Lean verification. The goal remains the entire
homogeneous anisotropic problem. The formally verified
homogeneous isotropic theorem is unaffected.
