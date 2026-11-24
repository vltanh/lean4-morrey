# Homogeneous angular Jensen: compact positive curvature stresses and a finite moment optimization

24 November 2026. We continue the homogeneous anisotropic attack.
The earlier angular realization theorem uses finite rank-one trees
with arbitrary depth and freely chosen radii. This note replaces
that description by ONE bounded positive-semidefinite measure on
the compact angular sphere and an explicit linear differential
equation. No choice of ray count or lamination depth enters the
continuous formulation.

**What is proved.** For every p>1 and every finite p-moment law,
Jensen against the ENTIRE signed homogeneous RC cone is equivalent
to existence of a positive angular curvature stress. Its total
mass is bounded explicitly by the ordinary convex p-power Jensen
gap. The positive stress is rank-one generated exactly when its
cofactor trace vanishes as a measure. Ordinary straight Taylor
interpolation gives a spatially induced PSD stress solving the
equation but not, in general, the cofactor constraint.

There is also a constructive computational consequence: for
arbitrary finite angular data, one finite moment optimization
at an explicitly selectable polynomial degree computes distance
to the closed angular-laminate hull to prescribed relative
accuracy. Unlike the preceding two-sided certificate search,
the degree can be selected before the configuration or its
distance is known, and no unknown tree depth is needed.

**Status:** these are exact hand reductions and a positive-accuracy
algorithm, not a proof of general homogeneous anisotropic Morrey.
We have NOT established the cofactor-free positive stress for
all compatible gradient fields. The algorithm is proved below
but not implemented as a quantifier-elimination solver or
benchmarked. The elementary symbolic identities and 85 rational
order-unit bounds were actually checked in the container.
No new Lean verification or publication-priority claim.
The verified signed homogeneous isotropic theorem remains closed.

## 1. The angular rank-one curvature operator

Identify matrix space with V=R^4 using the Frobenius inner product.
Write S=S^3, and let R be the compact set of unit rank-one matrices.
Let C be the symmetric linear cofactor operator, so

    C(a,b,c,d)=(d,-c,-b,a),
    det X = X:C X/2,    C^2=I.

For a C^2 scalar function f on S, its homogeneous extension is

    F_f(X)=|X|^p f(X/|X|) for X!=0, F_f(0)=0.

Set K=S x R and define the linear continuous-function-valued operator

    L_p f(u,H)=D^2 F_f(u)[H,H],    (u,H) in K.

To be explicit, let alpha=u:H and h=H-alpha u be the tangential
part of H. In intrinsic sphere notation,

$$
L_p f(u,H)=
 \nabla_S^2 f(u)[h,h]+p f(u)|h|^2
 +2(p-1)\alpha\,\nabla_S f(u)\cdot h
 +p(p-1) f(u)\alpha^2 .
\tag{1}
$$

If f is the restriction of a polynomial P in ambient coordinates,
an equivalent polynomial expression is

$$
L_p P=
 D^2P(u)[h,h]+(pP(u)-DP(u):u)|h|^2
 +2(p-1)\alpha DP(u):h+p(p-1)P(u)\alpha^2 .
\tag{2}
$$

These follow by differentiating the radial extension, or by
Euler's identity for the radial and mixed Hessian entries and
the second derivative on a great circle for the tangential entry.

For p>1, F_f is globally RC if and only if L_p f>=0 on K.
Indeed the Hessian scales by |X|^(p-2) and gives convexity on
rank-one lines not meeting zero; on lines through zero the
derivatives of the two half-line restrictions join at zero
because p>1 and f is bounded.

There is a strictly positive order unit, namely the constant
angular function 1, corresponding to the convex energy |X|^p:

$$
\ell_p(u,H)=L_p1=p(1+(p-2)\alpha^2),\qquad
c_p:=p\min(1,p-1)\le\ell_p\le p\max(1,p-1).
\tag{3}
$$

The lower constant c_p is positive. At p=2 the restriction
of det to S is in the kernel of L_p. We do not divide by
this null Lagrangian or impose an artificial invertibility
assumption on L_p.

## 2. Exact positive angular curvature representation

Let sigma be any finite signed Radon measure on S, and set
J(f)=int f d sigma. The measure of interest for a probability
law nu with finite p-moment and barycenter A is

    sigma = (X -> X/|X|)_# (|X|^p nu)
                - |A|^p delta_(A/|A|).

Zero-weight terms involving X=0 or A=0 are omitted. More
generally we allow any finite signed sigma, including angular
moments of finite trees.

**Theorem A.** The following are equivalent.

(a) J(f)>=0 whenever F_f is finite-valued positively
    p-homogeneous RC (f need only be continuous).

(b) There exists a finite nonnegative Radon measure mu on K
    such that, for EVERY f in C^2(S),

$$
\boxed{J(f)=\int_K L_p f(u,H)\,d\mu(u,H).}
\tag{4}
$$

Every such measure has total mass at most

$$
\boxed{\mu(K)\le \sigma(S)/c_p.}
\tag{5}
$$

In the probability-law application, sigma(S) =
E|X|^p-|A|^p is the ordinary convex Jensen gap.

**Proof of necessity.** On the linear subspace of C(K) consisting
of functions L_p f / ell_p, define

    T(L_p f / ell_p)=J(f).

This is well-defined: if L_p f=0 then both F_f and -F_f
are RC, so (a) implies J(f)=0. It is positive on nonnegative
members of the subspace, by the smooth RC criterion. By (3)
the subspace contains the constant 1 and T(1)=J(1)=sigma(S).
Thus for every member g,

    |T(g)|<=T(1)||g||_infinity,

by applying positivity to the two functions ||g||_infinity +/- g.
In particular T has norm T(1), including the possible zero case.
Extend T to C(K) with the same norm by Hahn--Banach.
This extension remains positive: for nonnegative g, 0<=g<=M
with M=||g||_infinity, the bound on T(M-g) implies T(g)>=0.
The Riesz representation theorem gives a finite nonnegative
measure gamma with total mass T(1). Set dmu=d gamma/ell_p.
This proves (4) and (5).

**Proof of sufficiency.** For C^2 angular profiles with RC
extension, (4) gives J>=0 directly. For arbitrary finite
homogeneous RC F use the exact homogeneous regularization
from [HOMOGENEOUS_REGULARIZATION](IWANIEC_MORREY_HOMOGENEOUS_REGULARIZATION.md):
logarithmically average ordinary mollifications, then
rehomogenize and repair the Hessian by a vanishing convex
multiple of |X|^p. This gives globally RC smooth-off-zero
approximants, of the SAME degree p, uniformly converging on S.
Since sigma is finite, J passes to the limit. QED.

Thus the infinitely many homogeneous rank-one convex Jensen
tests are exactly a positive-measure representation problem
on a fixed compact space. This does not assert that every
law has the representation.

## 3. Eliminate the rank-one direction variable: a positive stress on S^3

A symmetric matrix-valued Radon measure M on S is called PSD
if its contraction against every constant vector outer product
is a nonnegative scalar measure. We use tr M as its positive
trace measure; such an M has a PSD matrix density relative to
tr M almost everywhere.

Theorem A is equivalent to existence of M satisfying

$$
\boxed{
M\succeq0,\quad C:M=0\ \text{as a measure},\qquad
J(f)=\int_S D^2F_f(u):dM(u)\quad\forall f\in C^2(S).
}
\tag{6}
$$

The trace mass obeys tr M(S)<=sigma(S)/c_p.

Indeed from (4) take M by integrating H tensor H over the
rank-one directions above u. This gives PSD, and H:CH=0
gives the cofactor constraint, with trace equal to mu(K).
Conversely, at every point and for every smooth homogeneous
RC F_f, planar quadratic polyconvexity writes D^2F_f=P+lambda C
with P>=0. Its contraction against the density of M is
nonnegative, since the density is PSD and has zero C trace.
This proves all smooth Jensen tests, and the regularization
argument gives all continuous RC profiles. The multiplier
need not be constant: the cofactor constraint in (6) is a
measure identity, so the contraction vanishes pointwise
relative to tr M.

There is also an elementary algebraic reason why this is exactly
the rank-one covariance constraint. Every PSD symmetric matrix B
on V with tr(CB)=0 admits a representation as a sum of H_i tensor
H_i with det H_i=0. Write B=U U^T and consider the symmetric
traceless matrix U^T C U. It admits an orthonormal basis with
all diagonal entries zero: choose a unit vector with zero
quadratic value by continuity between positive and negative
eigenvectors (or any vector if the matrix is zero), then
restrict to its orthogonal complement, which is again traceless,
and induct. The columns Ue_i in this basis have zero determinant
and their outer products sum to B. There is no additional
algebraic constraint on a PSD cofactor-free covariance.

### 3.1 Explicit second-order equation on the sphere

Let Pi_u=I-u tensor u. Decompose M into measures

    a=u:M u,
    b=Pi_u M u,
    K_t=Pi_u M Pi_u,

where a is scalar, b tangent-vector-valued, and K_t a tangent
symmetric tensor. Thus

    M=a u tensor u+u tensor b+b tensor u+K_t.

Products with the smooth sphere coordinates are understood
as products of measures. By (1), the last equality in (6)
is precisely the distributional equation on S

$$
\boxed{
\operatorname{div}_S^2 K_t
 -2(p-1)\operatorname{div}_S b
 +p\,\operatorname{tr}K_t+p(p-1)a=\sigma .
}
\tag{7}
$$

Here the double divergence is defined by testing against
the intrinsic Hessian, and the single divergence by minus
the gradient. The cofactor constraint is the separate
linear measure identity

$$
(u:C u)a+2(Cu)\cdot b+C:K_t=0 .
\tag{8}
$$

The positivity constraint remains the PSD block condition
on M, not separate positivity of arbitrary components.
Testing (7) with 1 gives the exact mass identity

    p tr K_t(S)+p(p-1)a(S)=sigma(S),

and hence the stated trace bound. Equations (7),(8) with
M>=0 are a single compact, bounded-mass positive
distributional problem. There is no discrete tree depth,
number of obstacles, or angular regularity assumption.

## 4. What actual gradient interpolation supplies

Let X=A+Dphi be a bounded periodic compatible gradient
field, normalized to probability measure, or more generally
any finite p-moment law with E X=A. Put H=X-A, and Y_t=A+tH.
The ordinary Taylor remainder induces the measure

$$
M_0=\mathbb E\int_0^1(1-t)|Y_t|^{p-2}
         (H\otimes H)\,\delta_{Y_t/|Y_t|}\,dt.
\tag{9}
$$

Omit points Y_t=0 of zero time measure, and set the
contribution to zero when H=0. This is well-defined even
for 1<p<2. Along a straight line passing through zero,
the second derivative of a smooth angular homogeneous
extension is O(|t-t_0|^(p-2)), which is integrable.
In general the trace integral in (9) is bounded by
(E|X|^p-|A|^p)/c_p by Taylor's formula for the convex
energy |X|^p, whose Hessian is bounded below by
c_p |Y_t|^(p-2) I. This also justifies averaging for
arbitrary finite p-moment laws.

For every smooth angular f, subtract its affine first jet
at A (the derivative at zero is zero for p>1) and integrate
the straight-line Taylor formula. The affine term has
mean zero and homogeneity scales the Hessian. Thus

    J(f)=int_S D^2F_f(u):dM_0(u).

So M_0 is PSD and solves (7) with precisely the required
mass bound. It does NOT in general satisfy (8). Its
cofactor-trace measure is explicitly

$$
C:M_0
=2\mathbb E\int_0^1(1-t)|Y_t|^{p-2}
            \det H\,\delta_{Y_t/|Y_t|}\,dt.
\tag{10}
$$

At p=2 actual gradient compatibility gives the total
mass of (10) equal to E det H=0. This is not the same
as zero as a measure, which is what (8) requires.
At other exponents even that particular total-mass
identity is weighted by |Y_t|^(p-2).

The direct spatial task is now precise: replace M_0 by a
PSD measure M with the SAME right-hand side in (7) and
with zero cofactor trace as a measure. Equivalently add
a symmetric tensor-valued distributional gauge in the
kernel of the operator in (7), with prescribed cofactor
trace and retaining PSD. The ordinary determinant moment
cannot by itself justify such a gauge. We have not proved
its existence for arbitrary actual compatible gradients.
This is not a proof of universal homogeneous Jensen,
nor an assertion that (9) is already a rank-one stress.
It is an exact formulation that avoids trying to realize
a whole gradient law or choose a common martingale filtration.

## 5. Finite moment optimization with a uniform accuracy guarantee

We now use (4) to improve the effective law-side reduction
from [ANGULAR_LAMINATE_REALIZATION](IWANIEC_MORREY_ANGULAR_LAMINATE_REALIZATION.md).
Let D={v_1,...,v_m} be unit directions, including the
16 normalized coordinate cube vertices, and write
C_D(A) for the closed convex set of angular p-weight
vectors of finite laminates rooted at A. That theorem
gives the exact separation criterion for C_D(A).

For n>=0 define C_n(A) as the set of k in R^m, k>=0,
for which there is a nonnegative finite measure mu on
S x R satisfying

$$
\int L_p P\,d\mu
  =\sum_{j=1}^m k_j P(v_j)-|A|^p P(A/|A|)
\quad\text{for all polynomials }P,\ \deg P\le n .
\tag{11}
$$

The zero-base term is omitted if A=0. Include the
constant polynomial 1 in each test list. These are
closed convex outer approximations:

    C_D(A) subset C_(n+1)(A) subset C_n(A).

For closedness, if k_i converge, (3) bounds the
corresponding mu_i uniformly in total mass, and weak
compactness on K gives a measure for the limit.
The inclusion follows from Theorem A applied first
to finite laminate angular vectors and then by closure.

In fact

$$
\bigcap_{n\ge0} C_n(A)=C_D(A).
\tag{12}
$$

For fixed k in the intersection the finite moment
conditions have a common mass bound from the constant
test. The corresponding closed subsets of this compact
measure ball are nested and nonempty, hence have a
common measure. Polynomial restrictions are C^2-dense
among smooth angular profiles (smooth extension on
an annulus, mollification, polynomial approximation in
C^2). Formula (11) then holds for every C^2 f.
Theorem A proves every homogeneous RC Jensen test for
k. The angular separation theorem implies k in C_D(A):
its proof applies to any nonnegative vector k, not just
one already given as the angular weights of a probability
law, since it uses only nonnegative weights and separation
from C_D(A). This proves (12).

### 5.1 A single finite-dimensional optimization at each degree

Given w>=0, put d=dist_l1(w,C_D(A)) and
d_n=dist_l1(w,C_n(A)). The cube tree at A has angular
mass at most 2^p|A|^p, so

    0<=d_n<=d<=D_0:=||w||_1+2^p|A|^p.

In computing d_n one can impose ||k-w||_1<=D_0.
Then k is bounded; the trace bound (5), using (11)
for the constant polynomial, gives a common compact
set of feasible positive measures. In particular the
minimum defining d_n is attained.

Let N be the number of monomials of degree <=n in
four variables, including the constant. The moment
vector of any such mu is its mass times a point in
the convex hull of the compact evaluation set
{(L_p P_i(u,H))_(i=1)^N : (u,H) in S x R}.
By the elementary finite-dimensional Caratheodory
theorem it can be represented by a measure on at
most N+1 points. The zero measure is included.
This bound depends on degree, NOT on tree depth
or the number of ray constraints.

For rational p and algebraic inputs v_j,A,w,
formula (2) is polynomial in u,H, with rational
coefficients on the two unit spheres. Hence d_n
is the minimum of an explicit finite semialgebraic
optimization: nonnegative k and at most N+1 atom
weights, unit u,H, det H=0, and the N equalities
in (11). Absolute values in the objective use
ordinary slack variables. All constants are
algebraic. One can compute its value by exact real
closed field methods (or certified rational bounds
on it). The new variables are angular curvature
atoms; no unknown laminate depth appears in the
decision problem.

### 5.2 Uniform a priori degree selection for relative accuracy

**Theorem B.** Fix p>1 and 0<delta<=1. There is a finite
degree n(p,delta), independent of D, A and w, such that

$$
\boxed{
d_n\le d\le(1+\delta)d_n+
                 \delta(|A|^p+\|w\|_1)
}
\tag{13}
$$

for every n>=n(p,delta). In particular

$$
0\le d-d_n\le
\delta\left((2^p+1)|A|^p+2\|w\|_1\right).
\tag{14}
$$

For rational p,delta this degree can be selected
effectively from the earlier uniform homogeneous
polynomial approximation. It is not asserted to
be numerically small.

**Proof.** Finite-dimensional convex distance duality gives

    d=sup_(||f||_infinity<=1)
            [inf_(k in C_D(A)) f dot k - f dot w].

It follows by separating the open l1 balls about w
from the closed convex set; the zero functional handles
d=0. For a useful separator with finite infimum,
the earlier angular realization theorem constructs the
finite, globally RC, homogeneous ray envelope E^f_D
of those data. It satisfies F(v_j)<=f_j for F=E^f_D
and F(A)=inf_C_D(A) f dot k.

Crucially all these envelopes have a common angular
bound, even when f has negative entries. The cube
tree gives F(X)<=2^p |X|^p. To bound the other side,
split zero independently in each coordinate into
the two signed values +/-X_i, with probability 1/2.
The sixteen leaves all have norm |X|, and one
distinguished leaf is X. Since F(0)=0 by finite
positive homogeneity, rank-one Jensen and the upper
bound at the other fifteen leaves give

    F(X)>=-15*2^p |X|^p.

Thus the uniform angular norm is at most 15*2^p,
independently of the separator, rays and root.

The proof of the
[uniform homogeneous approximation theorem](IWANIEC_MORREY_HOMOGENEOUS_UNIFORM_CONE.md)
uses only a uniform angular bound to control
Lipschitz constants, logarithmic mollification,
and polynomial degree. Apply it with angular
bound 15*2^p rather than the normalized Gaussian
bound. It supplies n(p,delta) and, for every such F,
a globally RC homogeneous G with angular polynomial
degree at most n and

    |G(X)-F(X)|<=delta |X|^p.

The constructive degree selection there uses common
mollifier radii and Bernstein approximation with
a rational coefficient grid and a vanishing
homogeneous convex correction. At rational
parameters all degree bounds are effective.

Now for any k in C_n(A), its positive stress in
(11) tests the angular polynomial of G, whose
rank-one Hessian is nonnegative. Therefore

    (f+delta*1) dot k
       >= sum_j k_j G(v_j)
       >= G(A)
       >= F(A)-delta|A|^p.

Subtract (f+delta*1) dot w, and use
||f+delta*1||_infinity<=1+delta to obtain

    (1+delta)||k-w||_1
      >= F(A)-f dot w-delta(|A|^p+||w||_1).

Take the infimum over k, then the supremum over
separating f. This proves (13). Equation (14)
follows using the uniform upper bound D_0. QED.

Consequently for any prescribed relative accuracy one
finite angular moment optimization suffices to bound
the distance, with an a priori degree independent
of the configuration and without a tree-depth search
or a dovetailed search for separating integrands.
This strengthens the previous effectivity theorem,
which did not give a single predetermined finite
optimization. It does NOT give a fixed finite degree
for exact zero distance, and does not say d_n=0 for
every compatible gradient law.

## 6. Verification and disposition

The companion
[angular_stress_exact.py](../../research/audit/angular_stress_exact.py)
was executed locally using Python/SymPy. After changing a
rational-expression check from expansion to cancellation,
the final run printed:

    Exact radial Hessian, determinant, and tensor-decomposition identities passed.
    Exact balanced covariance rotation identities passed.
    Exact finite-degree distance inequality and 85 order-unit bounds passed.

The measure duality, positive-stress characterization, and
uniform-distance proof are analytic. These algebra checks
do not certify a positive stress for arbitrary gradients.
The finite moment optimization has not been run on a
collection of gradient witnesses.

**Next gate:** use actual compatibility to construct the
positive cofactor-free stress (6)-(8) for every law.
The unconstrained stress (9) solves the equality and
positivity conditions exactly, but its cofactor trace
need not vanish direction by direction. This is the
remaining mathematical issue; there is no reason to
enumerate increasing tree depths or treat additional
special exponents as a substitute for it. No closure
of general homogeneous anisotropic Morrey is claimed.
