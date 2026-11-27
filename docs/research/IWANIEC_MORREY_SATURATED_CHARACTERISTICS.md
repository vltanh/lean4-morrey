# Global straight characteristics of smooth saturated rank-one convex integrands

24 November 2026. **Structural advance for the entire homogeneous
anisotropic cone, not a prescribed symmetry, polynomial family,
or finite-wave subclass.** We study its extremal elements using
the compact normalization established in
[HOMOGENEOUS_UNIFORM_CONE](IWANIEC_MORREY_HOMOGENEOUS_UNIFORM_CONE.md).

For arbitrary C³ rank-one convex F on the punctured planar matrix
space, assume that its minimum rank-one Hessian curvature is zero
at every point. We prove a global characteristic theorem: a
maximal-rank stratum contains unbounded straight rank-one affine
half-lines. If its Hessian kernel contains a regular determinant-null
direction, the corresponding characteristic is a whole line.
The argument handles arbitrary multiplicities of the curvature
degeneracy and does not assume a unique null direction.

Consequences for positively p-homogeneous F, p>1:
* Every such smooth saturated F has a zero rank-one trace direction.
* At p=2, **every smooth saturated F is a convex function plus one
  constant determinant term**, globally. No sign or isotropy
  assumption. In particular every C³ extremal degree-two profile
  in the full normalized signed cone is polyconvex and QC.
* For every NONINTEGER p>1, if the saturated integrand is C³ and
  C^(ceil p) off zero, it is identically zero. Thus every nonzero
  smooth homogeneous RC integrand of noninteger degree has a
  region of strict rank-one curvature. Every extreme point of the
  normalized cone at these degrees necessarily lacks the stated
  smoothness.

**Important limit:** this does NOT establish that arbitrary extreme
points are smooth; indeed the noninteger conclusion shows that
they are not. Exact homogeneous regularization preserves RC, but
does not preserve extremality or everywhere saturation. The full
homogeneous anisotropic Morrey implication remains OPEN. These are
analytic hand proofs, with an actually executed exact symbolic
checker for the cofactor, Schur, and continuation identities.
No new Lean verification, referee review, or priority claim.
The previously verified signed homogeneous isotropic theorem is
unaffected. The classical compact-base extremal method is discussed
in Guerra, *Extremal rank-one convex integrands and a conjecture of
Šverák*, Calc. Var. 58 (2019), 201,
https://doi.org/10.1007/s00526-019-1646-5 .

## 1. Hessian multiplier and the null-direction geometry

Identify matrix space with V=R^4, using the Frobenius product.
Let C:V->V be the linear cofactor map. In entry coordinates

    C(a,b,c,d)=(d,-c,-b,a).

It is symmetric, C²=I, its signature is (2,2), and

    det H = (1/2) H:C H.

Let F be finite-valued RC, C³ on V\{0}, and suppose

    min_{|H|=1, det H=0} D²F(X)[H,H]=0

for every X!=0. Call this the saturated condition. Write Q(X)=D²F(X)
as a symmetric operator.

By planar quadratic polyconvexity there is a scalar lambda(X)
such that

$$
P(X)=Q(X)-\lambda(X)C\ \succeq\ 0.
\tag{1}
$$

For completeness, the existence of this scalar follows directly
from the degree-two origin argument in
[ANISOTROPIC_ORIGIN_RECTIFIED](IWANIEC_MORREY_ANISOTROPIC_ORIGIN_RECTIFIED.md).
The quadratic q(H)=(1/2)H:QH is RC since Q is nonnegative on
rank-one directions. For any opposite-determinant pair U,V,
choose t>0 such that det(U-tV)=0. Along their rank-one segment,
the determinant-balanced mean is rank deficient and q there
is nonnegative. Quadratic homogeneity cancels t² from the
weighted energy, giving
    q(U)/det U >= q(V)/det V.
The interval of determinant multipliers between the two ratios
is nonempty. Any lambda in that interval gives q>=lambda det,
equivalently (1).

At every unit null rank-one direction R of Q, the PSD property
and R:CR=0 imply

$$
P R=0,\qquad Q R=\lambda C R.
\tag{2}
$$

Since CR!=0, the multiplier lambda is UNIQUE whenever saturation
holds. Conversely every rank-one vector in ker P is a null
direction of Q. The multiplier is continuous: on a compact
neighborhood its value is bounded by testing (1) on unit
eigenvectors of C with eigenvalues +/-1. Any convergent sequence
of matrices has multiplier cluster points satisfying (1) at
the limit; uniqueness identifies the cluster point.

A second crucial identity is

$$
D^3F(X)[W,R,R]=0\quad\text{for every }W\in V
\tag{3}
$$

at a null rank-one direction R at X. Indeed the C¹ function
Y -> D²F(Y)[R,R] is nonnegative and vanishes at X. Its first
derivative is zero. R is held FIXED in this differentiation.
This uses global RC in a neighborhood, not an assumed smooth
choice of minimizers of the rank-one curvature.

Write K_X=ker P(X). We will use two kinds of null directions
in that kernel:
* regular nulls: unit R in K with R:CR=0 and CR not orthogonal
  to K;
* radical nulls: unit R in K with CR orthogonal to K, i.e.
  R in the radical of the restriction of the symmetric form C
  to K.

If C restricted to K is indefinite, regular nulls exist and
span K, even if the restricted form has a radical. This follows
by diagonalizing the form: positive and negative eigenvectors
give two opposite combinations that are regular nulls and span
those directions, while adding a radical vector to a regular
null preserves regularity and recovers the radical by subtraction.

If the restriction has no indefinite pair, K has dimension at
most two. Indeed a subspace on which a form of signature (2,2)
is nonnegative (or nonpositive) has dimension at most two.
Since saturation supplies a nonzero null, in this case the
restriction has rank zero or one and has a nontrivial radical.

## 2. Smoothness on rank strata, including the totally null case

On an open region where P has constant rank r>0, K is a
continuous bundle. The multiplier lambda is C¹ locally if
the restriction C|K is nonzero, or if that restriction is
identically zero throughout the region. Here is an explicit
proof, including the second case.

At a fixed base split V=K_0 plus K_0^perp, and in this fixed
decomposition write the blocks of Q(X)-kC as A(X,k),B(X,k),
B(X,k)^T,D(X,k). The block D is positive definite near
(X_0,lambda_0). Set

    S(X,k)=A-B D^(-1) B^T.

At the actual multiplier, the constant-rank condition is
S(X,lambda(X))=0. The kernel is the graph of the linear
map -D^(-1) B^T from K_0 to K_0^perp. If T denotes the
inclusion into this graph, differentiation in k gives
S_k=-T^T C T.

If C|K_0 is nonzero, choose v in K_0 with v:Cv!=0.
The scalar equation v:S(X,k)v=0 has nonzero k derivative
at the base. The implicit function theorem and continuity
of lambda prove the desired C¹ regularity.

If C|K=0 on the region, the actual multiplier also
satisfies S_k(X,lambda(X))=0. At the base B=0, and
    S_kk=-2 C_12 D^(-1) C_12^T.
This is negative definite on K_0: since C is invertible
and C|K_0=0, the map C from K_0 into K_0^perp is injective.
In particular the k derivative of tr S_k is strictly
negative. Apply the implicit function theorem to the scalar
equation tr S_k=0 instead. This proves C¹ regularity of
lambda also in the totally null case.

It follows that P and K are C¹ on these open regions.
If the rank of C|K is also constant, its radical forms
a C¹ subbundle.

## 3. Local straight characteristics

We use local C¹ sections of the kernel bundle and its regular
or radical null directions, as appropriate. Differentiating
P[R,S]=0 for two arbitrary kernel sections gives, at each
point and every direction W,

$$
D^3F[W,R,S]=D\lambda[W]\,(R:C S).
\tag{4}
$$

The derivatives of the sections do not contribute because
P annihilates both sections.

### 3.1 Regular nulls

If R is regular, take S in K with R:CS!=0. By (3) and (4)
with W=R,

    Dlambda[R]=0.

Moreover (3) now gives (D_R P)R=0. Thus the vector field
(X',R')=(R,0) is tangent to the bundle of regular unit nulls:
the derivative of the equation P(X)R=0 vanishes, and the
norm and determinant constraints of R are unchanged.

This is a genuine C¹ submanifold locally: K is a C¹ bundle,
and the determinant zero condition on its unit sphere is
regular precisely when CR is not orthogonal to K (its
radial derivative there is zero). A vector field tangent
to a C¹ submanifold admits a local integral curve there
by the ordinary local existence theorem in a chart.
The ambient equation (X',R')=(R,0) has a unique solution,
namely X(t)=X_0+tR_0, R(t)=R_0. Therefore the straight
line itself stays in the null bundle locally.
This argument does not assume that the minimizer R is
unique or that a selected null field has zero curl.

Along this characteristic lambda is constant and, by (2),

    DF(X+tR)=DF(X)+t lambda(X) CR.

### 3.2 Radical nulls

Work on a constant-rank region of P and C|K whose radical
is nontrivial. Choose a local C¹ unit radical section R.
Since det R=0, its derivative satisfies
    CR:D_R R=0.
Differentiate PR=0 in direction R. By (3),

    P D_R R=Dlambda[R] CR.

Taking the inner product with D_R R and using PSD gives
P D_R R=0. Since CR!=0, Dlambda[R]=0.

For ANY local kernel section S, equation (4) and the
radical property give D³F[W,R,S]=0 for all W. Differentiating
PS=0 in direction R then gives

    P D_R S=0.

Consequently D_R S is in K. In an orthonormal local frame
of K the derivatives in direction R have skew frame
coefficients, so the derivative of its orthogonal projector
is zero. In other words D_R K=0.

The same assertion holds for the radical subbundle N:
if T is a local radical section, D_R T is in K as just
proved; differentiating CT:S=0 for all kernel sections S,
and using D_R S in K, shows C D_R T orthogonal to K.
Thus D_R T is in N. Hence the derivative in direction R
of the orthogonal projector onto N is zero.

It follows that (X',R')=(R,0) is tangent to the bundle
of unit radical directions. This bundle is a C¹
submanifold by the constant-rank hypotheses. The same
local existence/ambient uniqueness argument gives straight
characteristics. Along them K AND lambda are constant,
and again DF(X+tR)=DF(X)+t lambda CR.

In both cases R is fixed along the straight line, has
rank one, and P annihilates it. Consequently F is affine
in t along the characteristic.

## 4. Global continuation, without assuming constant global rank

**Theorem A (unbounded affine-ray theorem).** Let F satisfy
the hypotheses of Section 1. Let U be either V\{0}, or a
nonempty open subset of the form
    U={X!=0:lambda(X) belongs to I}
where I is open in R. If the maximum of rank P on U is
positive, there exists a nonempty open stratum O in U with
the following property. Through EVERY invertible X in O
there is a straight rank-one affine characteristic of F
that is unbounded in at least one direction, with lambda
constant along it. If an indefinite kernel occurs at
the maximal rank in U, one can choose O with this
property and the characteristic is a whole straight line.

This formulation with a multiplier-level region U is
important for the degree-two theorem below. Characteristics
cannot leave U by changing the multiplier.

### 4.1 The exact continuation identity

Let r be the maximal rank on U. Its rank-r set is nonempty
and open in U, by continuity of P and maximality. If there
are indefinite kernels there, take the open subregion O
of such kernels. Otherwise K has dimension at most two,
and C|K has rank at most one. Choose O to be the region
where the rank of C|K attains its maximum on the rank-r
set (zero or one). This is again nonempty and open, and
the radical is nontrivial throughout O. Section 2 supplies
the needed C¹ regularity in either case.

At an invertible X in O choose a unit regular null
direction in the first case, or a unit radical direction
in the second. Let (t_-,t_+) be its maximal straight
characteristic interval in the corresponding bundle.
It is open and contains zero by Section 3. Invertibility
of X ensures the line X+tR never meets the origin,
since otherwise X is a scalar multiple of a rank-one R.

Choose a C¹ local section R(Y) of the same bundle through
the initial (X,R), and differentiate the exact gradient
identity along the characteristics:

    DF(Y+tR(Y))=DF(Y)+t lambda(Y) C R(Y).

For every fixed t in the characteristic interval this
identity holds on a neighborhood of the initial X.
Indeed the original compact segment from 0 to t lies
in the open regular stratum (or radical stratum), with
constant ranks; in the regular case its regularity
condition has a uniform positive margin on that segment.
Nearby initial directions and straight segments remain
in these neighborhoods and the local invariance from
Section 3 continues along the compact segment. Equivalently
one can use the local flow of the ambient tangent vector
field (R,0) on the C¹ bundle.

Write D_t=I+t DR(X). Differentiating in Y and subtracting
lambda(X) C D_t gives the exact operator identity

$$
\boxed{
 P(X+tR)D_t=P(X)+t(CR)\otimes D\lambda(X).
}
\tag{5}
$$

The expression (CR) tensor Dlambda means the rank-at-most-one
operator W -> (Dlambda[W]) CR. Importantly, (5) does NOT
require D_t to be invertible at a possible finite endpoint.
The identity passes to such an endpoint by continuity of
P and lambda, with the fixed finite D_t on the left.

### 4.2 Regular stratum: no finite endpoint

Every regular null direction in K annihilates Dlambda,
by Section 3.1. These directions span K, so Dlambda
annihilates K. Also CR is outside range P(X), since
range P(X)=K^perp.

Therefore the right side of (5) has kernel exactly K
for EVERY real t. Indeed if it annihilates W, then
P(X)W is a multiple of CR, so P(X)W=0; hence W is
in K and Dlambda[W]=0. The converse is immediate.
Its rank is r, and its range does not contain CR:
if its value on W were CR, the same argument gives
W in K and therefore value zero.

Suppose a finite endpoint t_* exists. The matrix X+t_*R
is nonzero, and lambda there equals its initial value by
continuity, so it belongs to U. At this endpoint (5)
forces rank P>=r; maximality gives equality. Its range
must be the range of the right side, which does not
contain CR. The limiting R is still a unit null kernel
direction by continuity and is still regular. In particular
the kernel restriction is indefinite (a null vector with a
nonzero pairing with some kernel vector generates an
indefinite two-dimensional restriction). Thus the endpoint
is in the same open regular stratum. Section 3.1 continues
the characteristic, a contradiction. Neither endpoint is
finite.

### 4.3 Radical stratum: at most one finite endpoint

Along the radical characteristic the entire kernel K
and lambda are constant, by Section 3.2. At a finite
endpoint the point still belongs to U. If the rank of
P is still r, continuity of the fixed-dimensional
kernel gives the same K; its restricted form has the
same rank as before. The maximal-rank definitions of
O make it open, and the fixed R is still radical there.
Section 3.2 would continue the characteristic.

Hence every finite endpoint must have rank P<r. But by
(5), rank of the right side can fall below r for at
MOST ONE t. To see this, fix a nonzero r-by-r minor
of P(X). Its value after the rank-one update
t(CR) tensor Dlambda(X) is an affine polynomial in t:
in its column expansion all terms using two or more
update columns vanish because these columns are proportional.
Its constant coefficient is nonzero. It has at most
one real root, and a rank drop requires that root.
Thus t_- and t_+ cannot both be finite. This proves
Theorem A, including all possible maximal kernel ranks
and degeneracies.

If the maximum rank on a multiplier-level open region
is zero, then Q=lambda C there. Symmetry of D³F gives
Dlambda[W](R:CS)=Dlambda[R](W:CS) for arbitrary W,R,S.
If Dlambda!=0 choose W with Dlambda[W]!=0 and nonzero
R in its kernel. This would imply CR=0, impossible.
Thus lambda is locally constant in that region. This
zero-rank case will be handled explicitly below.

## 5. Global consequences of positive homogeneity

Assume henceforth that F is positively p-homogeneous,
p>1. At any unbounded affine half-line from Theorem A,
reverse R if needed so the half-line is X+tH, t>=0.
Then homogeneity gives

    F(H)=lim_(t->infinity) t^(-p) F(X+tH)=0.

If P has maximal rank zero on the whole punctured space,
the last observation of Section 4 shows Q=lambda C with
constant lambda, since the punctured space is connected.
Thus F is a determinant term plus an affine function
there. Homogeneity and continuity imply F=c det for
p=2 and F=0 for other p>1. Such functions also have
unbounded rank-one affine lines. This completes the
rank-one trace conclusion in every case.

### 5.1 All smooth saturated degree-two profiles are polyconvex

**Theorem B.** If p=2, under the C³ and saturated hypotheses
of Section 1, there is a constant c such that F-c det is
globally convex. In particular F is polyconvex and QC.

By the earlier complete degree-two origin theorem, choose
a real c with G=F-c det>=0 globally. This shift preserves
homogeneity, RC, saturation, and C³ off zero. Apply the
notation Q,P,lambda of Section 1 to G itself (so the
multiplier here has changed by the determinant shift).

At a saturated point, Q is positive semidefinite if and
only if lambda=0. The reverse direction follows from
P>=0. For the forward direction use a null rank-one R:
if Q>=0 then R:QR=0 implies QR=0, and (2) forces lambda=0.

Suppose the open set U={X!=0:lambda(X)!=0} is nonempty.
If rank P is zero throughout U, lambda is locally constant
there by Section 4. Take a nonzero value lambda_0 in U.
Its level set is open by local constancy and closed by
continuity in the connected punctured matrix space.
Hence Q=lambda_0 C everywhere off zero. Integration and
degree-two homogeneity give G=lambda_0 det globally,
contrary to nonnegativity and lambda_0!=0.

Otherwise Theorem A gives an invertible X in U and an
unbounded rank-one affine half-line X+tH, t>=0, for G.
Its multiplier remains nonzero; this is why we chose
U using multiplier levels, rather than assuming maximal
rank in a single neighborhood would propagate globally.

We have G(H)=0. Since G>=0 and H!=0 is a smooth point,
DG(H)=0 and D²G(H) is positive semidefinite. For any Y,
Taylor's theorem and homogeneity give

$$
\lim_{t\to+\infty}G(Y+tH)
 =\lim_{t\to+\infty}t^2G(H+Y/t)
 =\tfrac12 D^2G(H)[Y,Y]=q_H(Y).
\tag{6}
$$

The rank-one restriction t -> G(Y+tH) is convex with a
finite limit at positive infinity. It is therefore
nonincreasing, so G(Y)>=q_H(Y) for EVERY Y. On the
affine half-line through X, the finite limit forces
that affine function to be constant, giving equality
G(X)=q_H(X). Thus G-q_H has a global minimum at the
smooth point X, and

    D²G(X) >= D²q_H = D²G(H) >= 0.

This contradicts X in U. Hence U is empty, Q is PSD
everywhere off zero, and G is ordinarily convex there
along each line avoiding zero. On lines through zero
homogeneity and local boundedness give derivative zero
from both sides at zero; the convex pieces join convexly.
Thus G is globally convex. Adding the constant determinant
term yields the asserted polyconvex representation. QED.

This result concerns the entire smooth saturated degree-two
cone, not merely quadratic polynomials or even profiles.
We have NOT shown that an arbitrary degree-two RC integrand
is a sum of such saturated smooth functions.

### 5.2 Noninteger-degree saturation rigidity

**Theorem C.** If p>1 is not an integer, and F is C³
and C^k off zero for k=ceil(p), then a globally saturated
homogeneous F is zero.

If maximal rank P is zero, this was proved above.
Otherwise use Theorem A on U=V\{0}. At every invertible
X in its nonempty open stratum, there is an affine
half-line F(X+tH)=a+bt for t>=0, H rank one and nonzero.
Taylor's formula at H gives

    F(X+tH)=t^p F(H+X/t)
            =sum_(j=0)^(k-1) t^(p-j) D^jF(H)[X^j]/j!
                +O(t^(p-k)).

The remainder tends to zero. All displayed exponents
p-j are positive and distinct, and none equals 1 or 0.
Comparing with the affine expression forces every
coefficient to vanish: first compare successively
the exponents above 1, then the coefficient of t,
then the remaining exponent in (0,1). The constant a
must also be zero by the vanishing remainder. Thus
F(X)=0 at every invertible point in the stratum. That is
a nonempty open set. On it Q=0, the unique PSD
multiplier is zero, and P=0, contradicting the
strictly positive maximal rank. This proves the theorem.

In particular for 1<p<2 the C³ assumption suffices.
For integer p the Taylor terms of order t or 1 can
occur, so the proof does not imply the same conclusion
there. Theorem B handles the special integer p=2
without a sign hypothesis.

## 6. Exact implication for the entire normalized extremal cone

Recall the compact convex base B_p from the previous
[uniform-cone theorem](IWANIEC_MORREY_HOMOGENEOUS_UNIFORM_CONE.md),
normalized by M(F)=1 and, when p=2, k_*(F)=0 for
the canonical determinant coefficient.

**Lemma (extremality forces saturation wherever smooth).**
Suppose F is an extreme point of B_p and C³ off zero.
If the minimum rank-one Hessian curvature is positive
at some nonzero matrix, continuity and homogeneity give
a small open angular patch on which it has a uniformly
positive lower bound at unit radius. Choose two
nontrivial disjointly supported smooth angular bumps
inside this patch, avoiding the finitely many directions
used in k_* when p=2. Extend them positively
p-homogeneously. A nonzero linear combination g of
them can be chosen with M(g)=0 (and automatically
k_*(g)=0 when p=2). Its Hessian is bounded on the
sphere and vanishes outside the patch. Thus for
sufficiently small eps>0, both F+eps g and F-eps g
retain nonnegative rank-one curvature off zero,
and are globally RC: on lines through zero their
derivatives join at zero by p>1 homogeneity.
They preserve the linear normalizations and are
distinct. This contradicts extremality.

Consequently every such smooth extreme satisfies the
global saturated hypothesis. Theorem B proves the QC
inequality at ALL bases for every C³ extreme of B_2.
For noninteger p>1 Theorem C excludes all extremes
of the stated smoothness, since M(F)=1 prevents F=0.
For all p>1 a C³ extreme has a null rank-one trace
direction by Theorem A, even if that direction is
not antipodally null.

This is an all-angular conclusion about extreme points
of the full normalized cone, not an assumed smoothness
or polynomial restriction on the original Morrey problem.
However, extremal points need not satisfy the smoothness
hypotheses. It is NOT legitimate to combine ordinary
smooth approximation of the cone with the claim that
its extreme points are smooth. Smooth approximants may
be decomposable and need not be saturated. In particular
a strict anisotropic degree-two Morrey violation, if
there is one, has an extremal witness that is not C³
off zero. For noninteger p the compact base has
extremal points, but none can have the stated regularity.

## 7. Verification and next target

The exact checker [saturated_characteristic_exact.py](../../research/audit/saturated_characteristic_exact.py)
was executed locally with Python/SymPy. Its output was

    Cofactor signature, Schur derivatives, and affine-minor identities passed.
    Characteristic derivative identity passed.
    Regular-null rank/transversality controls passed.

The cofactor signature, Schur complement and rank-one
update identities are algebraic checks, not verification
of analytic continuation or the theorem for nonsmooth
profiles. Sections 1--6 are the actual hand proofs.

**Remaining global gate:** extend the characteristic/
extremal rigidity argument to nonsmooth angular profiles
(or find a different universal quasiconvex calibration).
The smooth degree-two saturated cone is entirely
polyconvex, and smooth noninteger saturation is completely
excluded. This is a qualitative structural result, not
another list of specific angular functions or a finite
case ladder. No full anisotropic homogeneous Morrey
proof, new Lean verification, or completeness of the
previous gluing generators is claimed.
