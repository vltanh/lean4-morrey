# Gate 1: positive directional marginal correction and exact affine-frame stresses

24 November 2026. We continue the positivity step of Gate 1. The
previous [heat exchange](IWANIEC_MORREY_HEAT_STRESS_EXCHANGE.md)
gives a signed cofactor-free stress with the correct source, but
its negative part has not been absorbed.

This turn establishes two spatial mechanisms that preserve positivity,
and an exact polar decomposition for arbitrary smooth tests. In
addition we test whether mixing the directional constructions can
solve the entire gate. There is a rigorous actual-gradient example
showing that it cannot. This prevents an invalid conclusion based
on independently cancelling different projections of a measure.

**Status: GATE 1 IS OPEN.** The new positive constructions are
proved below, not a general solution or a finite exhaustive reduction.
The full positivity problem for arbitrary gradients is not settled.
Hand proofs; the accompanying exact algebra script was executed
locally. No Lean verification or priority claim.

## 1. Positive directional stresses with exact column-marginal cancellation

Let X=A+Dphi be a bounded compatible gradient on the flat two-torus,
with normalized area measure, and fix ANY spatial unit vector e.
Write m for a perpendicular unit vector. First flow by
exp(s partial_ee), then flow the limiting field by exp(s partial_mm).
The two flows commute with derivatives and preserve the mean.
The first limit exists in L^q for every finite q: by Fourier
expansion it is projection onto modes k with k dot e=0.
If e is irrational relative to the torus, this projection is
already the mean. Otherwise the remaining field is constant in
direction e, and the second flow takes it to A. Smooth approximation
and L^q contraction justify the limits for Lipschitz phi.

For either stage write Y for the evolving full gradient and H for
its derivative in the heat direction. In the full matrix space
define the PSD measure

    M_e = sum over the two stages int_0^infinity int
                            (H tensor H) delta_Y dx ds.

Here the second stage starts at the first limit. For every C²
integrand F, ordinary heat differentiation and integration by
parts give

    int D²F:dM_e = int F(X)-F(A).

In particular tr M_e = (int |X|²-|A|²)/2, so the measure is finite.
For initially nonsmooth gradients one can first smooth the data;
the heat energy identity and contraction, or the same identity
on every positive heat time, give the stated limits. The support
is bounded by the essential gradient range radius, since heat
averages the initial data.

**Theorem A (positive marginal correction).** For every e, this
positive stress has exact vanishing cofactor marginal

$$
\boxed{(Y\mapsto Ye)_\#(C:M_e)=0.}
\tag{1}
$$

This is equality of signed measures on R², not just zero total
cofactor trace.

Proof. In the first stage, set psi=Y e=Ae+partial_e phi_s.
Compatibility implies H=Dpsi. For any smooth scalar g on R²,
the pullback g(psi) dpsi_1 wedge dpsi_2 is exact: use the primitive
G(y)d y_2, with G(y)=int_0^{y_1} g(t,y_2)dt. Periodic integration
gives

    int g(Y e) det H dx =0.

Since C:(H tensor H)=2 det H, this proves zero marginal at every
positive time in that stage. If the initial data are only Lipschitz,
the degenerate heat flow is smooth in its heat direction and
H=Dpsi exists in L² for almost every time. One can use additional
ordinary periodic convolution at fixed time and pass in L² for
H and bounded convergence for g(Y e); determinants converge in
L¹. Equivalently apply the pullback identity to the periodic
W^(1,2) map psi by this approximation. Smooth g, then continuous g
by uniform approximation on the bounded range, suffice to identify
the zero signed marginal. In the second stage H e=0, so H has rank
at most one. This proves (1), including its Borel test version.
QED.

For p>1 push the same two-stage construction to S³ with weight
|Y|^(p-2), as in the previous heat exchange. It is PSD, has the
correct angular source, and its trace mass is bounded by
J_p/[p min(1,p-1)], by applying the heat identity to |Y|^p.
For 1<p<2 the regularized radial energy proves integrability
exactly as in the previous note; the weighted derivative is
set to zero a.e. on Y=0. It annihilates every angular cofactor
test whose (p-2)-homogeneous extension has the form g(Y e),
whenever that test is integrable. In particular the cancellation
does not require the angular profile F to be isotropic.

**Global energy consequence.** Suppose F is smooth and has a
feasible quadratic determinant multiplier depending only on
one column:

    D²F(Y)-g(Y e) C >=0  for all Y.

Then Jensen holds for EVERY compatible gradient and EVERY base.
Use M_e, (1), and the PSD remainder. This also holds for merely
measurable multipliers when the contraction is integrable.
In the smooth-off-zero homogeneous setting the same conclusion
follows if the multiplier is bounded on the unit sphere and
homogeneous of degree p-2; the weighted stress gives the
necessary integrability. This does not require a curvature
contrast bound. No homogeneity is needed for the full-matrix
version with a bounded multiplier on each bounded range.

The positive correction in (1) is a family indexed by e, not
one stress asserted to annihilate all these marginals at once.

## 2. Why averaging all directional sweeps is not a universal repair

We checked this possible continuation before trying to infer
simultaneous cancellation. Even at p=4 and zero affine base,
a single continuous angular cofactor test can have strictly
positive value for EVERY directional sweep. The source is a
genuine compatible gradient, not a minor-matching artificial law.

### 2.1 Exact radial Gaussian calculation on the plane

On R² take phi(x)=x exp(-|x|²/2). This is a gradient of a radial
scalar potential (up to a constant and sign). For e=(1,0),
directional heat gives, with a=(1+2s)^(-1),

    phi_s(x,y)=sqrt(a) (a x,y) exp(-(a x²+y²)/2).

Write Y=Dphi_s and H=partial_x Y. Use the angular test
lambda(u)=det u at degree p=4. Its contraction with the
angular cofactor trace is

    int lambda d(C:M_e) = 2 int ds int det Y det H dx dy,

since |Y|² det(Y/|Y|)=det Y. At fixed a write
Y=sqrt(a) exp(-(a x²+y²)/2) V, where

    V=[[a-a²x², -a x y],[-a x y,1-y²]],
    H=sqrt(a) exp(-(a x²+y²)/2) (partial_x V-a x V).

The Gaussian moment evaluation is

    E[det V det(partial_x V-a x V)] = a³/8,

where the expectation uses independent centered normals of
variances 1/(4a) and 1/4. Thus

    int_R² det Y det H = pi a^(9/2)/16.

With ds=-da/(2a²), the full cofactor pairing is exactly

$$
\boxed{2\int_0^\infty\int_{\mathbb R^2}
                  \det Y\,\det H\,dx\,ds=\pi/56>0.}
\tag{2}
$$

This calculation is checked in the companion exact script.
Radial covariance phi(Qx)=Q phi(x) for proper rotations Q,
and rotation invariance of det, give the SAME value for every
direction e. Directional heat on the plane tends to zero
in L⁴ here, so no second stage is needed.

### 2.2 Compact support and genuine periodic counterexample to this method

For clarity, (2) survives in the periodic problem uniformly
over all sweep directions. First cut off phi by smooth radial
cutoffs with radii tending to infinity. On every finite time
interval the resulting directional heat gradients and their
directional derivatives converge in L⁴ (and are bounded in
L⁴), by convolution contraction of the Schwartz data and their
derivatives. The quartic determinant product converges in L¹
in space and time. These estimates are uniform in e by rotation.

The absolute value of the time tail after T, for either the
Gaussian or cut-off data, is bounded by

    (1/2) int_T^infinity int |Y|²|H|²
       <= (1/8) int |Y_T|⁴,

using |det Z|<=|Z|²/2 and the heat identity for |Y|⁴.
The Gaussian tail tends to zero; cut-off gradients approximate
it in L⁴ at T uniformly in e. Consequently choose one compact
smooth radial phi for which the pairing remains strictly
positive for every e on R².

Periodize this compact phi in a torus of side L, with L large.
For finite 0<=s<=T, the periodized directional heat equals
the sum of translates of the plane directional heat.
If the support radius is R, outside radius 2R its gradient and
the gradient's directional derivative are bounded by constants
times exp(-(|x|-R)²/(4T)), uniformly over e and s<=T:
use the one-dimensional Gaussian convolution kernel and the
fact that a contributing displacement has magnitude at least
|x|-R. The constants can use the initial gradient and Hessian
sup norms. The same estimates control the translated tails
uniformly in a fundamental square as L tends to infinity.
It follows that the space-time integral up to T and the
unweighted L⁴ integral at T converge to their plane values,
uniformly over e (use Hölder and the Gaussian tail bound).

The first-stage torus tail is bounded by the same L⁴ energy
estimate after T, and the second-stage cofactor trace is
identically zero. Choose T and then L so the tail and
approximation errors are smaller than the positive pairing
margin. The normalization by L² only changes the pairing by
a positive factor. Rescaling the large torus to the unit torus
with the corresponding affine scaling of phi preserves the
sign, since gradients are unchanged and heat time and derivative
squares scale inversely.

Thus for an actual smooth periodic compatible gradient at p=4,

    int det(u) d(C:M_e) > 0 for every e,

with a uniform positive lower bound. No convex combination,
even a weak limit of convex combinations of these particular
positive two-stage stresses, can have zero cofactor trace.

This is NOT a counterexample to Gate 1. In fact the radial
Gaussian itself admits a different positive stress by the
affine-frame construction below. The example specifically
rules out treating the one-marginal cancellations as a
universal positive correction by averaging the sweep direction.

## 3. A fully positive stress from rank-one fields of affine frames

The next mechanism does not use heat dissipation. It constructs
a cofactor-free PSD stress DIRECTLY, and applies to arbitrary
spatially varying affine frames subject to a differential
rank-one condition. It requires no homogeneity, sign, isotropy,
or bounds on the acoustic curvature contrast.

**Theorem B.** Let Omega be a disk (or a simply connected
Lipschitz domain with connected boundary). Let B:Omega->R^(2x2)
and b:Omega->R² be Lipschitz, constant equal to A,b_0 in a
collar of the boundary. Suppose the combined frame map

    q=(B,b):Omega->R^6

satisfies rank Dq<=1 almost everywhere. Define

    u(x)=B(x)x+b(x),
    R_i(x)=(partial_i B)x+partial_i b,
    R=[R_1,R_2].

Then Du=B+R and rank R<=1 a.e. For every C² F,

$$
\boxed{
\int_\Omega F(Du)-|\Omega|F(A)
=\int_\Omega\int_0^1 (1-t)D^2F(B+tR)[R,R]\,dt\,dx .
}
\tag{3}
$$

In particular every finite rank-one convex F satisfies Jensen
for such u, and the right side of (3) is represented by one
positive cofactor-free full-matrix stress, independent of F.

Proof. The rank constraint on Dq means the two derivatives of
the pair (B,b) are linearly dependent a.e.; their images R_i
under the linear map (M,v)->Mx+v are dependent as well.

For a C² F, introduce the matrix and vector valued spatial
one-forms

    P_i=DF(B)^T partial_i B,
    k_i=DF(B)^T partial_i b.

They have zero distributional curl. For example the curl of
P is the difference
    D²F(B)[partial_1 B]^T partial_2 B
       - D²F(B)[partial_2 B]^T partial_1 B,
which vanishes by dependence of the two derivatives of B.
For k, the analogous expression is
    D²F(B)[partial_1 B]^T partial_2 b
       - D²F(B)[partial_2 B]^T partial_1 b,
which vanishes by dependence of the combined derivatives.
The distributional product identities follow by mollifying
B,b locally and passing using convergence in W^(1,q) for
finite q and boundedness; the chain rule for C¹ functions
on bounded ranges gives the displayed curls.

By the Poincare lemma for closed bounded one-forms on the
simply connected domain, there are Lipschitz potentials K,l
with partial_i K=P_i, partial_i l=k_i. One may prove the weak
version by local smoothing and path integration, then glue
potentials on simply connected neighborhoods; zero periods
give the global potential. Both are constant in the boundary
collar. Normalize K there to F(A) I/2. Since
tr P_i=partial_i F(B), we have tr K=F(B) throughout.
The vector field Z(x)=K(x)x+l(x) then satisfies

    div Z=F(B)+DF(B):R.

Its boundary flux is |Omega|F(A), by the divergence theorem
for the affine field given by its collar values. Apply
Taylor's formula to F(B+R), integrate, and use this flux
identity. This proves (3). QED.

The PSD stress is explicitly

$$
M_{\rm frame}=\int_\Omega\int_0^1
       (1-t)(R\otimes R)\delta_{B+tR}\,dt\,dx .
$$

All its generating directions have rank at most one.
The identity for arbitrary finite RC F follows from ordinary
mollification on the bounded matrix range. For homogeneous
p>1 one can push this stress onto S³ with the weight
|B+tR|^(p-2), using (3) for the convex radial energy to bound
its mass. If R=0 the contribution is zero; along any other
rank-one segment a possible zero has integrable power p-2>-1.
This gives exact Gate 1 positivity for these fields.

**Important geometric scope.** Every scalar-parameter affine
frame u(x)=B(s(x))x+b(s(x)), with s Lipschitz and constant in
the boundary collar, satisfies the hypothesis for C¹ bounded
frame paths. The level sets of s may have arbitrary shapes,
and B(t),b(t) are unrestricted along the path. This includes
every radial affine-shell map with arbitrary matrix and
translation profiles, not merely a scalar radial stretch.
The rank-one differential formulation is more general than
assuming a single global smooth parameter. These stresses can
also be used for disjoint local replacements in affine regions.

However arbitrary smooth u has not been shown to admit such
a frame, or to be approximable in gradient p-moment by these
maps. Taking B=Du, b=u-Du x generally gives rank Dq=2,
not rank one. That does not establish the missing
closed-one-form identities. We do not infer universality.

## 4. Exact polar stress for an arbitrary smooth gradient

The frame construction motivates an exact decomposition for
ALL smooth compactly supported perturbations. It exhibits
where nonradial dependence enters without imposing any
special Fourier mode or homogeneity on F.

Choose a disk of radius R_0, centered at a point outside
the compact support of the perturbation, large enough to
contain the support strictly. Translate the origin to its
center (constant affine translations are harmless).
Write u(x)=Ax+phi(x), with phi zero near the center and
outer boundary. Let n=(cos theta,sin theta), m=dn/dtheta,
and put

    w(r,theta)=u(r n)/r,
    Y=w tensor n+w_theta tensor m,
    xi=r w_r,
    zeta=w+w_thetatheta.

Then the exact gradient and angular derivative identities are

    Du=Y+xi tensor n,
    Y_theta=zeta tensor m.

Both indicated differences/directions are rank at most one.
For every C² F, define the nonnegative-for-RC radial
Taylor remainder

    T_F= int_0^1 (1-t) D²F(Y+t xi tensor n)
                               [xi tensor n,xi tensor n] dt.

**Theorem C (universal polar identity).**

$$
\boxed{
\int_\Omega [F(Du)-F(A)] =
 \int_\Omega T_F +
 \frac12\int_0^{R_0}\int_0^{2\pi}
    r\,D^2F(Y)[\xi\otimes m,\zeta\otimes m]\,d\theta\,dr .
}
\tag{4}
$$

Here the first integral on the right is in ordinary area.
To verify, differentiate E(r)=int F(Y(r,theta)) dtheta.
Since Y_r=w_r tensor n+w_rtheta tensor m, integration
by parts in theta gives

    E'(r)=int [2 DF(Y)n dot w_r
                 -D²F(Y)[w_r tensor m,zeta tensor m]] dtheta.

Indeed partial_theta(DF(Y)m) =
D²F(Y)[Y_theta] m - DF(Y)n. Differentiate r² E(r)/2,
and compare with Taylor's formula along xi tensor n.
The boundary value at R_0 is pi R_0² F(A), and that at
zero is zero. This proves (4).

The second term in (4) is a signed stress, but it is
pointwise cofactor-free because both factors have the same
right factor m. The only remaining sign is the target
bilinear pairing between xi and zeta in the acoustic
matrix for the direction m. For all affine first-harmonic
shells w=B(r)n, zeta=0 and the whole stress is positive,
consistent with Theorem B. For general w it is not
legitimate to replace that mixed pairing by a square
or to assume its integral nonnegative.

Thus (4) is a new exact spatial decomposition for the
full smooth test class, with an already positive radial
part and an explicit signed angular residual. Compactly
supported smooth tests suffice to establish QC, and
smoothing would remove smoothness afterwards. At this
point we have NOT proved absorption of the angular residual
for arbitrary compatible gradients. For the general identity
we use C² integrands on the full bounded range; it already
covers a dense class after ordinary smoothing. We do not
assert an additional singular weighted-stress estimate for
the mixed polar term at p<2.

## 5. Gate 1 ledger

* The heat stress exchange from the previous turn cancels
  the complete cofactor trace, but may introduce negativity.
* The new directional sweep preserves positivity and the
  full source, and annihilates an entire column marginal
  exactly. Combining these particular sweeps is NOT a
  general solution, by the actual periodic Gaussian
  localization above.
* The affine-frame theorem constructs a completely positive
  cofactor-free stress for arbitrary rank-one differential
  fields of affine frames. No approximation theorem putting
  arbitrary compatible gradients in this class is proved.
* The polar identity provides a direct rank-one radial
  source plus a signed cofactor-free residual for every
  smooth compact perturbation. Controlling that residual,
  or finding a different full positive spatial construction,
  is the missing step.

The exact checker in research/audit/gate1_directional_frame_exact.py
was actually executed. It printed:

    Polar rank-one and mixed cofactor identities passed.
    One-parameter affine calibration contraction identities passed.
    Gaussian sweep cofactor defect/pi = 1/56

These checks verify the algebra, not the distributional or
analytic arguments. In particular no solver or checker
proved the missing positivity. Gate 1 and the general
homogeneous anisotropic implication remain open.
