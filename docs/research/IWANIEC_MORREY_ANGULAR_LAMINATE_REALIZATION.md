# Exact angular-laminate realization and effective uniform finite-depth approximation

24 November 2026. **Scope:** arbitrary finite-valued positively p-homogeneous
rank-one convex (RC) energies on real 2x2 matrices, p>1. No isotropy,
evenness, sign or polynomial assumption on the original integrand.

The previous [finite-ray envelope theorem](IWANIEC_MORREY_HOMOGENEOUS_RAY_ENVELOPES.md)
reduces the entire homogeneous problem to nonsmooth saturated envelopes.
Here we work on the law/laminate side of that reduction.

Three results:
1. For every finite angular configuration, Jensen for ALL p-homogeneous
   RC integrands is exactly membership in a closed convex set of
   angular p-moment vectors of finite laminates. Realization of the
   original gradient distribution is NOT required. A separating
   linear functional constructs a finite homogeneous RC counterexample
   to Jensen via its finite-ray envelope.
2. For rational p>1 and finite algebraic input data, the distance to
   this closed convex set is computable to arbitrary positive accuracy,
   with genuine two-sided finite certificates. This tests the entire
   homogeneous integrand cone for the given law, not one chosen energy.
3. With an arbitrarily small homogeneous convex strictification, there
   is a UNIFORM finite lamination-depth bound for approximating ALL
   ray envelopes to any prescribed positive accuracy. It is independent
   of the number, locations, and arrangement of the prescribed rays.
   For rational parameters the bound is effectively computable, though
   the procedure is extremely expensive. A robust coordinate-splitting
   construction transfers trees between nearby angular configurations
   without assuming persistence of rank-one connections between rays.

**Status:** these are hand proofs, with the elementary transfer gadget
checked by an actually executed exact rational script. No new Lean
proof or priority claim. The algorithms are specified and proved to
terminate, not implemented or benchmarked in this turn. They do not
decide exact zero distance, give a uniform exact lamination depth, or
prove that actual compatible gradients have angular-laminate
realizations. The homogeneous anisotropic Morrey gate remains OPEN.
No fixed ray-count enumeration is proposed as an exact solution.

## 1. The exact angular moment set

Use the Frobenius norm in V=R^(2x2). Let D={v_1,...,v_m} be a
finite set of unit directions. Include the directions of all 16
coordinate-cube vertices (entries +/-1, normalized to norm one).
These auxiliary directions may carry zero data-law weight. Their
purpose is to make every matrix the root of a finite laminate
with leaves on the prescribed positive rays.

A finite laminate is a finite binary tree of rank-at-most-one
splits with nonnegative child probabilities, preserving the mean
at every node. Mixing two trees with the same root is allowed
(a rank-zero split, equivalently a randomized finite laminate).

For a root A, define L_D,p(A) to be the set of vectors k in R^m
obtained from such trees with leaves X_i=t_i v_(j_i), t_i>=0,
and leaf probabilities theta_i, by setting

    k_j = sum_(i:j_i=j) theta_i t_i^p.

Zero leaves contribute nothing. This is a NONEMPTY CONVEX subset
of the nonnegative orthant. Nonemptiness follows by successively
splitting each coordinate of A into +/-max|A_ij|. After four
levels the nonzero leaves lie on the cube directions. Convexity
follows by randomizing between two trees at the same root.
Write C_D,p(A)=closure L_D,p(A) in ordinary finite-dimensional
Euclidean topology.

Let nu be any probability law supported on these rays with
finite p-th moment. In particular this includes any finite
gradient law after augmenting its directions with the cube
directions. Its angular vector is

    w_j = integral over {X=t v_j,t>0} of |X|^p dnu(X).

For every positively p-homogeneous finite energy F,

    integral F dnu = sum_j w_j F(v_j).

The law can have a zero atom. We do not need to assume any
gradient compatibility to establish the next theorem.

**Theorem A (exact angular realization).** For an arbitrary
root A,

$$
\boxed{
F(A)\le\int F\,d\nu\ \text{for every finite homogeneous RC }F
\quad\Longleftrightarrow\quad
w\in C_{D,p}(A).
}
\tag{1}
$$

In particular, the all-base homogeneous Morrey problem is
equivalent to the right-hand membership for every finite
compatible gradient law with mean A. This asks to realize
only angular p-moments. The leaf amplitudes and their
probabilities can be completely different from those of nu.

### Proof

For every finite laminate tree, RC Jensen gives
    F(A)<=sum_j k_j F(v_j).
Continuity of this finite-dimensional linear functional gives
the forward test for all k in C_D,p(A).

Conversely suppose w is outside this closed convex set.
Strict separation supplies f in R^m with

    f dot w < inf_(k in L_D,p(A)) f dot k = ell.

Here ell is finite: it is bounded below by the strict
separation and above by any one admissible tree. Define the
ray-data envelope at EVERY root B by

$$
E^f_D(B)=\inf_{k\in L_{D,p}(B)} f\cdot k.
$$

The data f need not initially come from any RC integrand.
The cube construction gives a finite upper bound everywhere.
Finiteness below at A implies finiteness below at EVERY B:
split each coordinate of A into the two values B_i and
2A_i-B_i with equal probability. The resulting four-level
product tree has a distinguished B leaf of mass 1/16.
Replace every other leaf by its finite cube tree. Append
any admissible tree at B to the distinguished leaf. The
cost at A is exactly 1/16 of that tree's cost at B plus a
fixed finite contribution independent of the choice at B.
A lower bound at A therefore gives a lower bound at B.
This argument permits repeated endpoints and rank-zero
splits, which merely label identical states.

Consequently E_D^f is a finite-valued function everywhere.
Concatenating near-minimizing trees under any rank-one split
proves RC; rescaling every matrix in a tree proves exact
positive p-homogeneity. At zero the trivial zero tree gives
an upper bound of zero, and finiteness plus homogeneity gives
equality. Finite RC implies local Lipschitz continuity.
The trivial tree at v_j gives E_D^f(v_j)<=f_j.

Taking F=E_D^f therefore gives

    F(A)=ell > f dot w >= sum_j w_j F(v_j)=integral F dnu.

This is the required strict violation. QED.

As an independent consequence, for arbitrary real data f,
finiteness of the envelope at ANY root is equivalent to
existence of a finite homogeneous RC minorant of the
prescribed ray data. The origin is one possible root; its
finite envelope value must be zero. At p=2 the earlier
degree-two origin theorem makes this particular feasibility
test completely finite: it is equivalent to existence of
a real c with f_j>=c det(v_j) for every j. This last test
concerns finiteness of the envelope, NOT interpolation of
every prescribed datum or Jensen at a nonzero base.

For actual homogeneous Morrey, finite-gradient witnesses
suffice by the smoothing/interpolation argument in the
[homogeneous regularization note](IWANIEC_MORREY_HOMOGENEOUS_REGULARIZATION.md).
Thus (1) has the full homogeneous quantifier. It is weaker
than asking that nu itself be a laminate. In particular,
at p=2 and root zero, only the correct determinant moment
is needed to pass all homogeneous RC tests, by the earlier
origin theorem, whereas arbitrary minors-compatible laws
need not be laminates.

## 2. A computable angular separation distance

Fix rational p>1, algebraic unit directions D containing
the cube directions, algebraic root A, and a nonnegative
algebraic vector w. All algebraic numbers are understood
with effective exact representations. Set

    d = dist_l1(w,C_D,p(A)).

**Theorem B.** For every rational epsilon>0, there is a
terminating procedure returning rational lower and upper
bounds on d with difference less than epsilon.

This is stronger than a one-sided enumeration of possible
counterexample integrands: it gives finite accuracy even
when d=0. It is not an algorithm deciding equality to zero.

### Upper certificates: finite trees

For fixed depth n, a full binary tree with rank-zero splits
permitted describes all trees of depth at most n by padding
with repeated states. Introduce real matrix variables at the
nodes, child probabilities in [0,1], mean equations and
the zero-determinant equation for each child difference.
A leaf is constrained by a finite disjunction to be t v_j
with t>=0. Write p=a/b for positive integers a,b.
The constraint r>=0, r^b=t represents t^p=r^a.
Product probabilities and the angular weights k_j are
therefore semialgebraic expressions with algebraic constants.
Absolute values in ||w-k||_1 can also be written by finite
polynomial inequalities/disjunctions.

For each rational U, existence of a tree of depth <=n with
||w-k||_1<U is decidable by real closed field quantifier
elimination. Such existence certifies d<U. As depth tends
to infinity the infimum of these finite-depth distances
tends to d by the definition of closure. Thus these upper
certificates approach d arbitrarily closely.

### Lower certificates: homogeneous RC polynomials

The elementary finite-dimensional convex distance duality is

$$
d=\sup_{\|f\|_\infty\le1}
   \left\{\inf_{k\in C_{D,p}(A)} f\cdot k-f\cdot w\right\}.
\tag{2}
$$

One inequality follows from duality of l1 and l-infinity
norms. For the other, strictly separate C_D,p(A) from
each open l1 ball about w of radius smaller than d, and
normalize the separator. The zero functional covers d=0.
No boundedness of C_D,p(A) is required. An inner infimum
of minus infinity simply contributes no useful lower bound.

Take any rational vector f with ||f||_infty<=1 and a function

    G(X)=|X|^p P(X/|X|) (X!=0),   G(0)=0,

where P is a rational polynomial. Verify exact global RC
by its rank-one Hessian on the two unit spheres, as in
the homogeneous regularization theorem. For rational p,
that Hessian formula is polynomial on the sphere. Since
p>1 the restrictions on lines through zero join convexly
if the Hessian condition holds off zero. Check the
finitely many algebraic inequalities G(v_j)<=f_j.
Then G(A)-f dot w is a valid lower bound on d by (2).
All these checks and values are algebraic.

These lower certificates converge to the full dual value.
Indeed choose a real f in (2) with finite infimum and
gap arbitrarily near d (for d>0). The preceding envelope
argument shows that E_D^f is finite globally and RC.
For 0<h<1, replace f by
    f'=(1-h) f+(h/2) 1.
This is strictly within the coordinate bounds [-1,1].
The RC function (1-h)E_D^f lies below f' on the rays
with a uniform slack h/2. Approximate f' rationally
within h/8, retaining the coordinate bounds, and
approximate (1-h)E_D^f by a rational homogeneous RC
angular polynomial within h/8 on the sphere, using
the exact homogeneous regularization and polynomial
approximation theorem. The slack ensures the finite
data inequalities for the approximant. Homogeneity
controls the error at A by (h/8)|A|^p. As h decreases
to zero the certified lower value tends to the original
dual value f. Hence rational certificates approach d.
When d=0 the zero bound suffices.

Dovetail the two certificate searches, maintaining the
best rational lower and upper bounds (algebraic values
can be rounded outward). Stop when the width is below
epsilon. The density arguments prove termination. QED.

Thus a strict homogeneous Jensen violation of a fixed
finite law can be certified without being given its
integrand; a finite tree is an upper certificate of
angular proximity. The method does NOT prove that the
distance is zero for a compatible gradient law.

### A related envelope-value oracle with strict slack

We will need an upper/lower approximation algorithm for
E_D^f(A) itself. Suppose algebraic f,D,A, rational p>1,
and a PROMISE that there is a finite homogeneous RC G
with G(v_j)<=f_j-eta for some eta>0. Then E_D^f is finite
by the lower support. For any prescribed positive accuracy,
finite tree costs give convergent upper certificates by
the same quantifier elimination argument.

For lower certificates enumerate rational angular RC
polynomials below f on D. They approach E_D^f(A):
the RC functions (1-h)E_D^f+hG converge to E_D^f and
have uniform slack h eta on the prescribed rays.
Homogeneous RC polynomial approximation with error
less than h eta preserves the data inequality. Thus
the two-sided search terminates to any positive accuracy
and, in particular, returns a finite depth with an upper
cost within that accuracy of the true envelope. This
oracle requires no numerical knowledge of G beyond the
promise; for the finite family constructed below the
promise is automatic.

## 3. A uniform ray transfer lemma

We now prove an approximation-depth result that is
uniform over arbitrary configurations, not just computability
for one fixed D.

Fix p>1, M>0 and eta>0. Consider arbitrary finite homogeneous
F with ||F||_{S^3}<=M and

    G=F-eta |X|^p  rank-one convex.

This is a strict convex margin in the homogeneous cone.
There is no smoothness assumption; any homogeneous RC F_0
can be brought into this form by adding eta |X|^p.
The original general implication is recovered by taking eta
to zero in an original-energy Jensen inequality if such an
inequality is proved for the strictified functions.

Allow D to be ANY closed subset of S^3 containing the cube
directions, not necessarily finite. E_D^F is the infimum of
finite laminate costs with leaves on D's rays and energies
from F. The same concatenation and cube argument proves
finiteness, RC, homogeneity and agreement with F on those rays.

For uniform estimates below use M_*>=M and also assume
||G||_{S^3}<=M_*; for instance M_*=M+eta+1 suffices
for a single class. Set

    K=2^p M_*,   B=(K+1+M_*)/eta,   L=4*2^p*K.

The global bound |E_D^F(X)|<=K|X|^p follows from the cube
tree and the minorant F. Hence E_D^F is L-Lipschitz on the
unit ball, by ordinary convex coordinate secant bounds using
unit steps and the angular bound on the radius-two ball.
The same L also bounds F there. At a unit root, every
tree of cost at most E_D^F(A)+1 satisfies

$$
\sum_i\theta_i |X_i|^p\le B,
\tag{3}
$$

because the cost equals sum theta_i G(X_i)+eta sum theta_i
|X_i|^p, and laminate Jensen for G bounds the first term
below by G(A)>=-M_*. This controls the p-moment even for
signed energies; it is not an assumption that F is positive.

### The robust replacement gadget

Suppose v,v' are unit directions with |v-v'|<=delta<=1/4.
We can replace any leaf X=t v, t>0, by a laminate with
a distinguished leaf Y=t v' carrying probability at least
1-4delta. In each of the four coordinate directions choose
one endpoint Y_i, the other Y_i+t sign(X_i-Y_i), taking
either sign if equal. Then X_i is between those endpoints,
and the probability of choosing the other endpoint is
|X_i-Y_i|/t<=delta. Successive coordinate rank-one splits
give a product tree of depth four; the probability alpha
of the all-Y branch is at least 1-4delta. All its vertices
have norm at most |Y|+2t=3t. Send the other vertices
to the cube directions by four further coordinate splits;
the final auxiliary leaf norms are at most 6t. This
gadget preserves the original root EXACTLY and does not
require any rank-one relation between the two rays.

Suppose F,F' are in the same strict-margin class, with
the common bounds M_*,K,B,L above, and

    ||F-F'||_{S^3}<=h,
    Hausdorff(D,D')<=delta.

Use the gadget at each original leaf, selecting a nearby
v' from D' and using the F' energies. The cost at that leaf
is at most

    t^p [F(v)+h+L delta+4delta M_*(1+6^p)].

This follows by writing alpha F'(v') as F'(v') minus
(1-alpha)F'(v'), and bounding both the lost signed primary
term and the auxiliary costs in absolute value. At t=0
use the zero atom. Set C=L+4M_*(1+6^p).

For an original near-optimal tree at a unit root, (3)
then gives a new tree with depth increased by at most
eight and cost increased by at most B(h+C delta).
Applying this to near-minimizers in both directions yields

$$
\boxed{
|E_D^F(A)-E_{D'}^{F'}(A)|\le B(h+C\delta),\quad |A|=1.
}
\tag{4}
$$

This is a uniform joint continuity result for signed
strictified ray envelopes. Crucially it does not assume
that the original rank-one splitting tree can be perturbed
by perturbing its directions.

There is also a base transfer: for unit A,A' with
|A-A'|<=delta, apply the same gadget to X=A,Y=A',
t=1, then attach a given tree at A' to the favored
branch. If that tree's cost has absolute value at most
K+2, this costs at most an additional C_0 delta, where
C_0=4(K+2+M_*6^p), and increases depth by at most eight.
The envelope value itself changes by at most L delta.

## 4. Uniform effective finite lamination depth at positive accuracy

**Theorem C.** For every p>1, M,eta,epsilon>0 there exists
an integer N(p,M,eta,epsilon) with the following property.
For EVERY finite homogeneous F satisfying ||F||_{S^3}<=M
and F-eta|X|^p RC, EVERY closed angular set D containing
the cube directions, and EVERY root A, there is a finite
laminate with leaves on D's rays and depth at most N,
whose cost is at most

$$
\boxed{E_D^F(A)+\epsilon |A|^p.}
\tag{5}
$$

The number of directions in D does not enter the bound.
For rational p,M,eta,epsilon, a finite procedure can compute
such an N. It is an existence/effectivity theorem, NOT
a practical numerical depth estimate.

### Uniform finite approximants

It suffices to treat unit roots and 0<epsilon<=1, by
homogeneity; at zero use the trivial zero tree.
Set M_*=M+2eta+2 for the common constants in Section 3.

The [uniform angular cone theorem](IWANIEC_MORREY_HOMOGENEOUS_UNIFORM_CONE.md)
gives a finite collection of homogeneous RC rational angular
polynomials approximating EVERY homogeneous RC G with
||G||_{S^3}<=M+eta, to any prescribed uniform error h<=1.
For clarity, that theorem's regularization/Bernstein
construction needs only the uniform angular bound to obtain
common Lipschitz, log-mollification, derivative and polynomial
degree estimates. Here use the bound M+eta directly instead
of the earlier Gaussian normalization. At rational p the
resulting finite list and its rank-one Hessian filter are
effective. One can further filter the list by
||G_j||_{S^3}<=M+eta+1 without removing necessary approximants.
For arbitrary real parameters, ordinary compactness and
the density theorem also give such a finite list.

For each G_j set F_j=G_j+eta |X|^p. The class of F_j contains
an approximation of every F under consideration within
angular error h. All F_j and G_j meet the common bounds
M_*, and all F_j have the SAME margin eta.

Choose rational h>0 and delta>0 small enough that
h<=1, delta<=1/4 and

    2B(h+C delta)+(C_0+L)delta < epsilon/2.

For rational parameters these choices are effective using
outward bounds for the constants. Take a finite delta-net V
of unit directions including the cube directions; normalized
integer vectors suffice and are algebraic. Every closed D
can be replaced by a subset D' of V containing the cube
directions at Hausdorff distance <=delta, by taking nearest
net points. Every unit A has a net point A' within delta.

There are now only FINITELY MANY auxiliary triples
(F_j,D',A'), allowing ALL subsets D' of V containing the
cube directions. All of their ray data have a strict RC
minorant G_j, with slack eta, so the envelope-value oracle
in Section 2 is guaranteed to terminate for each of them.
For each triple obtain a finite tree with cost within
epsilon/4 of its exact envelope value, and record its depth.
For rational parameters these triples have algebraic data
and the oracle yields these depths effectively. For general
real parameters choose such trees by the definition of infimum.
Take N to be the maximum of the finitely many depths plus 16.

### Transfer back to arbitrary original data

Given F,D,A, choose the approximating auxiliary triple.
First transfer its finite tree from D' to D, with the
original F data, at fixed root A'. The original tree is
within epsilon/4 of its envelope, hence has moment <=B.
Its cost increases by at most B(h+C delta).
Then transfer the root from A' to A. The transferred tree
has absolute cost at most K+2 by the bounds and the chosen
small errors; the root transfer costs at most C_0 delta.
The depth has increased by at most 16.
Finally the envelope comparison (4) and base Lipschitz
bound show

    E_{D'}^{F_j}(A') <= E_D^F(A)+B(h+C delta)+L delta.

Thus the final cost at A is at most

    E_D^F(A)+epsilon/4+2B(h+C delta)+(C_0+L)delta
    < E_D^F(A)+epsilon.

Scale the tree to an arbitrary nonzero root to get (5).
QED.

The proof supplies a single depth across the entire
bounded angular class with the fixed margin eta, including
arbitrarily many prescribed rays and arbitrarily close
rank-one incidences. It does not estimate N efficiently,
and leaves may have arbitrarily large radii (the finite
depth decision problems use unbounded real variables).
It does not justify a bound uniform as eta or epsilon
decreases to zero. This is NOT an exact finite classification.

## 5. What the remaining general gate is now

The original ray-envelope maximality compared only
rank-one tree costs. It did not compare actual gradient
costs to those trees. Equation (1) pinpoints the missing
property: angular p-moment membership for ALL finite
compatible laws, all roots and all p>1. A proof of this
membership would settle the full homogeneous anisotropic
problem, and need not realize the original law.

For finite algebraic configurations, there are now
two-sided certificates for angular distance; no unknown
integrand needs to be supplied. The uniform depth theorem
goes beyond the earlier finite angular approximation on
the integrand side by bounding lamination complexity at
positive accuracy across arbitrary ray configurations,
under arbitrarily small strictification. However, neither
the finite distance computations nor the finite-depth
bound prove the missing spatial membership. In particular
there is still no uniform finite bound for exact Jensen.
We did not enumerate the very large auxiliary families or
run the two-sided real-algebraic algorithm. The general
homogeneous anisotropic gate remains open.

Verification: [ray_transfer_exact.py](../../research/audit/ray_transfer_exact.py)
was actually executed in the working container:

    243 exact product-split, mass, determinant and radius controls passed.
    Exact root embedding identity passed.

These are checks of the elementary coordinate-tree geometry,
not computational verification of the analytic theorems,
the effectiveness proof, or the general Morrey implication.
