# General homogeneous approximation, positive rank-one trace normalization, and affine-plane rigidity

24 November 2026. The main target remains arbitrary positively
homogeneous rank-one-convex integrands in real 2x2 matrices, without
isotropy. This note proves a regularization theorem for the ENTIRE
homogeneous cone, not just a special angular family, and two
independent structural theorems concerning rank-one traces.

**Results:**
1. For every fixed p>1, smooth-off-zero exactly p-homogeneous
   uniformly strongly RC integrands are locally uniformly dense
   in all finite p-homogeneous RC integrands. Ordinary mollification
   alone does not give this assertion. Logarithmic averaging over
   mollification radii supplies a uniform first-derivative estimate
   on the defect of Euler's identity. Exact radial homogenization
   then costs a vanishing amount of ellipticity.
2. Positive trace on the entire rank-one unit cone at p=2 implies
   coercivity after subtraction of a constant determinant, even
   without evenness or strict rank-one convexity. For even F the
   universal lower bound is half its rank-one trace lower bound,
   with a sharp factor at p=2. An opposite-ray comparison also
   gives a signed determinant-power support at every p>1 for
   even F, and a uniform estimate throughout 1<p<=2.
3. The preceding quadratic null-plane polyconvexity theorem
   needs NO homogeneity at all. An arbitrary finite RC function
   affine on a full common-factor rank-one plane is PC.

The arguments are hand proofs. Symbolic identities were checked
with an actually executed Python/SymPy script. No new Lean theorem,
independent review, or novelty clearance is claimed. In particular
these results do NOT prove general homogeneous anisotropic QC.
The attempted universal subtraction of a convex homogeneous term
until a null rank-one ray appears is not established. No such
decomposition is inferred from the coercive lower bounds.

## 1. Exact homogeneous regularization for all p>1

This theorem actually works in any finite matrix dimension.
We give the proof in the planar notation.

**Theorem A.** Let F:R^(2x2)->R be finite, positively
p-homogeneous, and RC, where p>1. There exist F_n, positively
p-homogeneous and smooth on matrix space minus zero, with
positive constants m_n, such that

    D²F_n(X)[V,V] >= m_n |X|^(p-2) |V|²

for every nonzero X and every rank-one V. They are globally
rank-one convex and converge locally uniformly to F.
Here and throughout this section |.| is the Frobenius norm.
If F is nonnegative, or is invariant under any group of
orthogonal linear transformations of matrix space, the
approximations preserve that property. In particular they
preserve evenness, left rotations, and/or right rotations
when these are present.

### 1.1 Logarithmic averaging removes the first-order Euler defect

Let rho be a nonnegative smooth radial mollifier, supported in
the unit ball and of total mass one. For t>0 put

    F_t(X)=int F(X-tY) rho(Y) dY.

Every F_t is smooth and RC. Fix 0<a<b<1/2, write
ell=log(b/a), and define

$$
H(X)=\frac1\ell\int_a^b F_t(X)\frac{dt}{t}.
$$

This is a smooth RC function. Finite RC functions are locally
Lipschitz, by separate convexity, so let L be a Lipschitz constant
of F on the radius-two ball. At all |X|=1, F_t and H are within
Lb of F, and |DF_t(X)|<=L. Smoothness of the scale-average
follows from a>0 and local boundedness of F and the derivatives
of the mollifier kernels.

Homogeneity of F gives F_t(sX)=s^p F_(t/s)(X) for s>0.
Differentiating at s=1 gives

    DF_t(X):X - p F_t(X) = -t partial_t F_t(X).

Consequently the scalar defect E(X)=DH(X):X-pH(X) satisfies
the exact telescoping identity

$$
\boxed{E(X)=(F_a(X)-F_b(X))/\ell.}
\tag{1}
$$

Thus at every point on the unit sphere

$$
|E|\le L(b-a)/\ell,\qquad |DE|\le 2L/\ell.
\tag{2}
$$

The second estimate is the important one. A single arbitrarily
small smoothing radius does not directly make the derivative
of the homogeneity defect small at a nonsmooth angular point.

### 1.2 Exact radial rehomogenization and its Hessian

Define

    G(X)=|X|^p H(X/|X|)   (X!=0),   G(0)=0.

Fix a unit X and decompose any V as V=w+alpha X with w:X=0,
alpha=X:V. The differential identities for the homogeneous
extension are

    DG(X):w=DH(X):w,
    D²G(X)[w,w]=D²H(X)[w,w]-E(X)|w|²,
    D²G(X)[X,w]=(p-1)DH(X):w,
    D²G(X)[X,X]=p(p-1)H(X).

For example the tangential identity follows by taking two
derivatives of |X+t w|^p H((X+t w)/|X+t w|) at t=0.
The other two second-derivative identities follow by Euler's
identity for G. Differentiating E gives

    DE(X):v=D²H(X)[X,v]-(p-1)DH(X):v.

Subtracting the Hessian of H from that of G yields the exact
formula

$$
\boxed{\begin{aligned}
D^2G(X)[V,V]-D^2H(X)[V,V]
={}&-E|w|^2-2\alpha DE:w\\
 &-\alpha^2 DE:X-(p-1)\alpha^2E.
\end{aligned}}
\tag{3}
$$

In particular its absolute value is at most
    [max(1,p-1)|E|+2|DE|] |V|²,
using 2|alpha||w|+alpha²<=2(|w|²+alpha²).
By (2), set

$$
\epsilon_{a,b}
=\frac{L}{\ell}\{\max(1,p-1)(b-a)+4\}.
$$

The rank-one Hessian of H is nonnegative. Hence
D²G(X)[V,V]>=-epsilon_(a,b)|V|² for every rank-one V
at unit X. Homogeneity gives the same lower bound multiplied
by |X|^(p-2) at arbitrary nonzero X.

### 1.3 Repair with a vanishing homogeneous convex term

For p>1,

    D²(|X|^p)[V,V] >= p min(1,p-1)|X|^(p-2)|V|²

for X!=0. Choose b_n=1/(n+2), a_n=b_n exp(-n) for n>=1,
and put epsilon_n=epsilon_(a_n,b_n), and

    eta_n=(epsilon_n+1/n)/(p min(1,p-1)),
    F_n(X)=G_n(X)+eta_n |X|^p.

Then epsilon_n->0 and eta_n->0. The rank-one Hessian bound
holds with m_n=1/n at every nonzero matrix. On any rank-one
line not containing zero, convexity follows by the ordinary
second-derivative test. On a line through zero the function
is continuous there and the two one-sided derivatives at
zero both vanish, by p>1 and boundedness of its angular
profile. The convex restrictions on the two half-lines
therefore join convexly. Thus F_n is globally RC.

At unit X the error relative to F is at most L b_n+eta_n;
by positive homogeneity it is at most
R^p (L b_n+eta_n) on the radius-R ball. This proves the
asserted convergence. Nonnegativity and orthogonal invariance
are retained at every step, by the radial nonnegative
mollifier and the radial correction. QED.

The proof does not require prior smoothness of F or a
uniform ellipticity margin of F itself. In particular it is
not a perturbation argument restricted to already smooth
or strictly elliptic angular profiles. No analogous direct
repair at exactly p=1 is claimed: the radial Hessian bound
for |X| vanishes in the radial direction.

## 2. Consequences for the ENTIRE homogeneous gate

### 2.1 No separate degree-one case is necessary for a full theorem

The known Kirchheim--Kristensen theorem gives ordinary
convexity at the origin for every finite degree-one RC
integrand, and hence a linear lower support there:
[On rank-one convex functions that are homogeneous of degree one](https://arxiv.org/abs/1505.04654).
Given such an F, subtract this linear functional L.
Then F-L>=0 is degree-one and RC. Quasiconvexity at
any base is unchanged by adding or subtracting L.

For every eps>0, (F-L)^(1+eps) is RC by convex
nondecreasing composition and is positively homogeneous
of degree 1+eps. As eps decreases to zero it converges
locally uniformly to F-L. Thus a proof for all p>1
also proves the p=1 case. Equivalently, a strict
degree-one Jensen violation persists at some degree p>1.

The degree 0<p<1 case is already Lean verified without
isotropy. It also has an elementary proof from the null-line
theorem: convexity along both halves of each rank-one line
through zero forces F(H),F(-H)<=0, and convexity at zero
forces their sum>=0. Both vanish. The subquadratic
null-line theorem then gives invariance along every
rank-one H, so F is identically zero.

Together with Theorem A, this means that the whole
homogeneous anisotropic implication is equivalent to
the implication for smooth-off-zero homogeneous
strongly RC integrands of degrees p>1. No regularity
assumption on a hypothetical original counterexample
is needed.

### 2.2 An exact finite-description counterexample principle

There is an additional rigorous route to computer assistance.
It is a density/reduction theorem, NOT a uniform finite
degree bound or a proof of absence of counterexamples.

**Theorem B.** If the homogeneous anisotropic Morrey
implication fails, there is a strict counterexample of the
form

$$
F(X)=|X|^p P(X/|X|),\quad X\ne0,\qquad F(0)=0,
\tag{4}
$$

where p>1 is rational, P is a polynomial in the four
matrix entries with rational coefficients, and the
rank-one Hessian of F has a strictly positive lower
bound on the unit sphere. Its witnessing base A can
be rational and its periodic perturbation can be
piecewise affine on a finite rational triangulation,
with rational values at its nodes.

**Proof.** Any strict counterexample has a bounded compatible
test gradient, and hence survives sufficiently small locally
uniform changes of the integrand. By Section 2.1 and Theorem A
we may take p>1 and a smooth-off-zero strongly RC F.
Its smooth profile on the unit sphere can be approximated
in C² by restrictions of polynomials with rational coefficients.
For clarity, extend the profile smoothly to an annulus, use
a smooth compactly supported cutoff equal to one near the
sphere, convolve with a narrow Gaussian, approximate the
resulting entire function by a Taylor polynomial on a fixed
compact neighborhood, and approximate its finitely many
coefficients by rationals. Each step gives arbitrary C²
accuracy on the sphere. Exact radial extension as in Section
1.2 is continuous in this C² norm, so a sufficiently accurate
approximation retains strict rank-one ellipticity. The radial
extension and its unit-sphere Hessian depend continuously on
p; replacing p by a sufficiently close rational >1 preserves
ellipticity and the strict Jensen gap on the bounded test range.
All assertions include the point zero by homogeneity and
continuity as before.

For the test, periodize the original Lipschitz perturbation
if necessary, and smooth its periodic part by convolution.
Its gradients converge almost everywhere and are uniformly
bounded, so the energy gap converges by dominated convergence.
Approximate the smooth periodic function by continuous
piecewise-affine interpolation on a sufficiently fine
periodic rational triangulation of the unit square. The
gradient error tends uniformly to zero by C¹ smoothness
and shape regularity of a fixed grid subdivision. Approximate
its nodal values by rationals with error much smaller than
the mesh size, retaining periodic equality at identified
nodes. This makes both the values and the gradients
arbitrarily accurate, and the base can be approximated by
a rational matrix. The strict gap is retained. QED.

For any individual rational (p,P) in (4), the rank-one
Hessian test is an exact semialgebraic condition. On |X|=1
use formula (3) with H=P. Its terms, including alpha=X:V,
w=V-alpha X, E=DP:X-pP and
DE=D²P[X,.]-(p-1)DP, are polynomial in X,V with rational
coefficients. Rank-one test directions can be normalized
by |V|=1 and det V=0. Global RC is equivalent to
nonnegativity of that polynomial on these two unit
spheres with the determinant constraint (and convexity
through zero, automatic for p>1). Strict ellipticity is
equivalent to strict positivity there by compactness.
Real closed field decision procedures therefore verify
this condition for a candidate without a sampling gap.

Every witness value of (4) on rational matrices is a
real algebraic number, and every triangle has rational
area. Thus the strict finite-sum energy comparison
is decidable by exact algebraic arithmetic. This gives
finite verifiable descriptions of any possible
counterexample, if one exists. It does NOT bound the
polynomial degree, exponent denominator or triangulation
size, and no endless enumeration is proposed as a
completion strategy.

## 3. Strict rank-one trace controls the sign at degree two

For p>1, every finite homogeneous RC F satisfies F(H)>=0
on rank-one matrices, by convexity between 0 and H and
positive homogeneity. Suppose

    m=min{F(H): |H|=1, rank H=1}>0.

At p=2 the prior origin theorem shows that some determinant
shift makes F nonnegative. We strengthen it to global
coercivity without assuming any Hessian strictness.

### 3.1 Opposite determinant rays and orthogonal mixing

Take X,Y normalized to det X=1, det Y=-1. The quadratic
det(X-tY) has exactly one positive root t>0 and one
negative root -1/t, since its leading coefficient is -1
and constant is 1. Define

    U=(tX+Y)/sqrt(1+t²),
    V=(X-tY)/sqrt(1+t²).

Both U,V are rank one, since
det(X-tY)=0 implies cof X:Y=(1-t²)/t, hence det(tX+Y)=0.
Neither is zero (otherwise X,Y would have the same
determinant sign). The pair transformation is orthogonal,
so |U|²+|V|²=|X|²+|Y|².

The rank-one segment joining X and tY has the
determinant-zero point

    C=(t² X+tY)/(1+t²)=(t/sqrt(1+t²)) U.

At p=2, rank-one Jensen gives

    F(X)+F(Y) >= F(U) >= m|U|².

Using X=(tU+V)/sqrt(1+t²), the determinant relation gives
    1=t cof U:V/(1+t²).
Since the cofactor preserves the Frobenius norm in 2x2,
|U||V|>=t+1/t>=2. In particular

$$
F(X)+F(Y)\ge\frac{4m}{|X|^2+|Y|^2}.
\tag{5}
$$

This holds for arbitrary signed, not necessarily even F.

### 3.2 Quantitative coercive determinant shift for every positive trace

**Theorem C.** Let F be finite, degree-two homogeneous,
and RC with m>0 as above. Let M=max_(|X|=1)|F(X)|,
and L be a Lipschitz constant on the radius-two ball.
Both are positive. Put

$$
\tau=\min\{1/4,\ m/(4\sqrt2 L),\ m/(16M)\}.
$$

Then there exists c in R such that

$$
\boxed{F(X)\ge c\det X+m\tau^2|X|^2\quad\forall X.}
\tag{6}
$$

To prove this, write the extrema

    A_+=inf_(det X>0) F(X)/|det X|,
    A_-=inf_(det X<0) F(X)/|det X|.

By homogeneity we may take unit X in each infimum.
At |X|=1 let H be its leading rank-one singular-value
component, with |H|>=1/sqrt(2). Its distance to X is
the smaller singular value, at most sqrt(2)|det X|.
Thus if |det X|<=tau,
    F(X)>=m/2-L sqrt(2) tau>=m/4.
The ratio F(X)/|det X| on that region is at least
m/(4tau)>=4M. But testing at I/sqrt(2) and
diag(1,-1)/sqrt(2) gives both infima <=2M.
Consequently the extrema are attained on the compact
regions |X|=1, |det X|>=tau. Normalize their attaining
matrices to determinant +1 and -1 respectively.
Their squared norms are <=1/tau. Equation (5) gives
    A_++A_->=2m tau.
In particular both A_+,A_- belong to [-2M,2M].
Take c=(A_+-A_-)/2, so |c|<=2M. For all X,

    F(X)-c det X >= ((A_++A_-)/2)|det X|.

On the unit sphere with |det X|>=tau this is at least
m tau². On the remainder the previous rank-one
approximation bound gives
    F(X)-c det X>=m/4-2M tau>=m/8>=m tau².
Scale by positive homogeneity to get (6). QED.

No evenness or differentiability is needed. The
constant determinant shift preserves rank-one convexity
and Jensen differences at EVERY base, and the resulting
integrand is genuinely coercive. Thus, after adding an
arbitrarily small Frobenius quadratic if necessary,
the full degree-two anisotropic Morrey problem may
be posed on globally coercive integrands without sign
ambiguity. Inequality (6) does NOT imply that subtracting
the coercivity term from F-c det preserves RC.

## 4. Stronger even-function comparison, all exponents

**Theorem D.** Suppose F is even, positively p-homogeneous
and RC for p>1, with nonnegative rank-one trace minimum m.
There is c in R such that

$$
F(X)\ge c\,\operatorname{sgn}(\det X)|\det X|^{p/2}
\quad\forall X.
\tag{7}
$$

For 1<p<=2 the stronger uniform estimate holds:

$$
\boxed{
F(X)\ge (m/2)|X|^p
       +c\,\operatorname{sgn}(\det X)|\det X|^{p/2}.
}
\tag{8}
$$

At p=2 the factor 1/2 in (8) is sharp over all such
integrands, as a universal multiple of m. At p>2, if
m>0, a positive (possibly smaller, integrand-dependent)
coercivity coefficient in (8) exists as well.

**Proof.** Use the same opposite determinant normalization
and orthogonal mixing as Section 3.1. The first rank-one
segment now gives, with k=t^(p-2),

    F(X)+k F(Y) >= m k (1+t²)^(1-p/2)|U|^p.

The second rank-one segment, joining X and -Y/t, has
determinant-zero point V/sqrt(1+t²).
Evenness gives F(-Y)=F(Y), and Jensen gives

    F(X)+k^(-1)F(Y) >= m(1+t²)^(1-p/2)|V|^p.

Take the convex combination of the two inequalities
with weights 1/(1+k) and k/(1+k). The coefficient of
F(Y) becomes exactly one. Hence

$$
F(X)+F(Y)\ge
m\frac{k(1+t^2)^{1-p/2}}{1+k}
       (|U|^p+|V|^p).
\tag{9}
$$

The right side is nonnegative for every p>1, proving
the opposite-determinant ratio ordering for (7)
after determinant normalization. The endpoints of the
interval of allowable c's are finite, by comparison
with any fixed matrix of the opposite sign.

For 1<p<=2, put a=(2-p)/2>=0. The prefactor in (9)
equals (1+t²)^a/(1+t^(2a)), which is at least
2^(a-1)=2^(-p/2) by concavity of the a-power (with
a=0 immediate). Also
    |U|^p+|V|^p >= (|U|²+|V|²)^(p/2)
                  >=2^(p/2-1)(|X|^p+|Y|^p).
It follows that

    F(X)+F(Y)>=(m/2)(|X|^p+|Y|^p).

Apply the same ratio argument to F-(m/2)|X|^p:
after normalization by determinant, its two infima
sum to a nonnegative number, so there is a real c
with (8). The rank-one matrices obey (8) directly.

For p>2 and m>0, continuity and positive trace make
the infima of F(X)/|det X|^(p/2) attained away from
the rank-one cone on the unit sphere: the ratios tend
uniformly to positive infinity near that cone.
At the determinant-normalized minimizing pair, (9)
is strictly positive. The midpoint choice of c
therefore gives a strict positive gap on each
determinant sign. By positive trace at the cone and
compactness of the unit sphere, F minus the signed
determinant power is bounded below by a positive
multiple of |X|^p. QED.

At p=2 sharpness follows from F(X)=||X||op²:
m=1, F(I)=F(diag(1,-1))=1, and the two matrices both
have squared Frobenius norm two. Any coefficient
larger than 1/2 in (8) fails upon adding the two
inequalities, independently of c.

A further p=2 consequence of the orthogonal mixing:
if q is ANY quadratic form nonnegative on rank-one
matrices and F(H)>=q(H) there, evenness gives
F(X)+F(Y)>=max(q(U),q(V))>=(q(X)+q(Y))/2 at the
normalized opposite pair. Thus F>=q/2+c det globally
for some c (depending on q). This permits fully
anisotropic quadratic lower calibrations based on the
rank-one trace. Again it is a lower bound, NOT an RC
decomposition of F.

The signed determinant power in (7)--(8) is a null
Lagrangian only at p=2. For p!=2 the determinant
mean identity does not control its mean signed power.
No unconditional origin QC for those exponents,
or all-base QC at degree two, is inferred from this
theorem. The point of (9) is the exact cancellation
of the two reciprocal rescaling weights, exploiting
evenness without rotational symmetry.

## 5. Affine rank-one plane rigidity WITHOUT homogeneity

The previous note
[RANKONE_NULL](IWANIEC_MORREY_RANKONE_NULL.md)
proved the degree-two null-plane result using a recession
calculation. A simpler geometric proof eliminates the degree
restriction entirely.

**Theorem E.** Let F be an arbitrary finite RC function on
real 2x2 matrices, and suppose its restriction to some
affine two-dimensional common-factor rank-one plane is
affine. Then F is globally polyconvex. In the normalized
case F([a,0])=0 for every a in R², there exists a finite
convex G:R² x R -> R with

$$
\boxed{F([a,b])=G(b,\det[a,b]).}
\tag{10}
$$

No homogeneity, sign, differentiability, or rotational
symmetry is required. The general affine case follows
by translating the matrix variable, subtracting an
extension of the affine restriction, and making a
rank-preserving linear coordinate change (possibly
transposition) to normalize the plane. These operations
preserve polyconvexity: the determinant of a translated
matrix is affine in the original matrix and determinant,
and the invertible linear coordinate changes rescale
the determinant. We prove the normalized assertion.

### 5.1 Invariance under shear

A finite convex function g on R^k that is constant on
the whole line R h is invariant under addition of h.
Indeed, for 0<theta<1, by convexity

    g(x+u h) <= (1-theta)g(x/(1-theta))
                         +theta g((u/theta)h).

Let theta decrease to zero and use continuity to get
g(x+u h)<=g(x); reverse the shift for the other
inequality. This elementary observation replaces
the previous homogeneous recession computation.

Fix b!=0. On the common-left-factor rank-one plane
{[alpha b,beta b]}, F is ordinary convex and vanishes
when beta=0. The observation implies
    F([alpha b,b])=F([0,b]).
For fixed second column b, a -> F([a,b]) is convex
and constant along the whole line R b. Apply the
observation a second time to obtain
    F([a+t b,b])=F([a,b])  for all a,t.
Thus F depends on a only through det[a,b].

With J the counterclockwise quarter-turn, put

    G(b,d)=F([-d J b/|b|²,b])  for b!=0.

This is continuous on the punctured lifted space,
and F([a,b])=G(b,det[a,b]) there.

### 5.2 Joint convexity and removable missing axis

Given independent b1,b2 and any d1,d2, choose a
common first column a satisfying det[a,b_i]=d_i
for i=1,2. These are two independent linear
equations. The rank-one segment between [a,b1]
and [a,b2] has affine determinant, and its second
column never vanishes. Rank-one Jensen therefore
gives the lifted convexity inequality for G on
that segment. In particular G is convex on every
line whose b-coordinate line avoids zero and
has nonconstant b-coordinate; any two distinct
b-coordinates on such a line are independent.
Vertical lines at fixed nonzero b are also convex
by varying a in its rank-one column plane.

We must prove that G extends finitely across
b=0; a priori the representative first column
in its definition can diverge there. Here is a
direct removable-axis argument, with no growth
estimate for the original F.

For |b|<=1, b!=0, choose a unit e perpendicular
to b. The b-line b+t e avoids zero. Convexity on
this lifted line implies

    G(b,d) <= (G(b+e,d)+G(b-e,d))/2,
    G(b,d) >= 2G(b+e,d)-G(b+2e,d).

If d ranges over any fixed compact interval,
all the displayed right-side points have
1<=|b+k e|<=3 for k in {-1,1,2}.
They lie in a compact set of the punctured domain.
Thus G is uniformly bounded above and below near
the missing axis on every bounded lifted range.
Away from the axis continuity gives the same
local bounds.

Fix a lifted radius R. If two lifted points
in the radius-R ball have independent b
coordinates, extend the line segment by unit
length beyond both endpoints. This extended line
still avoids the axis and stays in radius R+1.
If M_R bounds |G| there, the usual secant slope
comparison for a convex function on that line
bounds its absolute slope between the original
endpoints by 2M_R. Approximate any two nonzero
b-coordinate endpoints by independent endpoints,
using continuity and, if needed, a common bound
on the radius R+2 ball. This proves a uniform
Lipschitz estimate on every punctured lifted
ball. Hence G has a unique finite continuous
extension to the entire lifted space.

Approximate arbitrary lifted endpoints, now
including b=0, by endpoints with independent
b coordinates. Pass to the limit in the lifted
Jensen inequality. This proves convexity of
the extension everywhere. Since
G(b,0)=F([0,b]) for b!=0 and F(0)=0,
its value at (0,0) is zero. Thus (10) holds
also when b=0, since the physical determinant
then vanishes. The right side is a finite convex
function of a column and the independent
determinant variable, proving PC. QED.

In particular the null-plane classification now covers ALL
positive homogeneous degrees, including p>2, and indeed all
nonhomogeneous integrands with an affine rank-one plane.
For 0<p<2, in the normalized homogeneous case, the lifted
extension satisfies G(tb,t²d)=t^p G(b,d) by continuity.
Hence G(0,d) is a finite convex positively p/2-homogeneous
function of d and must be zero: degree below one forces
nonpositive values on the two rays, while convexity at zero
forces their sum nonnegative. The line-invariance observation
then shows G is independent of d. Thus for p<2 a null-plane
integrand is just a convex function of its other column.

This theorem does not remove the need for a genuinely
spatial argument for arbitrary strictly positive rank-one
trace. It provides an exact structural statement of the
flat-plane boundary case, with no additional symmetry,
rather than an asserted decomposition of arbitrary F
into such functions.

## 6. Checks and status

The companion [homogeneous_log_regularization_exact.py](../../research/audit/homogeneous_log_regularization_exact.py)
was executed locally with Python/SymPy. It checked (3),
the derivative formulas for radial extension, the determinant
of the orthogonal mixing, and the reciprocal power weights
in (9). Output:

    Homogeneous Hessian defect identity: passed
    Radial-extension derivative controls: passed
    Opposite-ray orthogonal mixing and reciprocal power weights: passed

The approximation, compactness, and affine-plane proofs
are analytic, not inferred from finite algebra checks.

**Main advance:** we now have a rigorous smooth, exactly
homogeneous strictification/density reduction of the whole
homogeneous anisotropic gate, and not just ordinary smoothing
that destroys homogeneity. The positive-trace case at p=2
has a fully quantitative coercive normalization modulo
the determinant. For even subquadratic profiles there is
a uniform signed determinant-power lower calibration,
with arbitrary angular dependence. The affine-plane
theorem supersedes the earlier degree-two restriction.

**Not established:** a universal RC decomposition into
the flat-plane or previously proved null-line families,
quasiconvexity of arbitrary smooth homogeneous strongly
elliptic integrands, or closure of the all-base homogeneous
anisotropic gate. The finite-description result provides
exact access to any hypothetical strict counterexample;
there is no uniform finite complexity cutoff. Do not
replace the main proof problem by an unbounded exponent,
polynomial-degree or triangulation enumeration. No new
Lean theorem. The signed homogeneous isotropic result
remains formally CLOSED.
