# Vector-valued operator-ball projection: exact boundary selection and full-matrix QC calibrations

24 November 2026. **Hand proof of an analytic extension of the scalar
projection mechanism.** The new ingredient is Kirszbraun's Euclidean
Lipschitz extension theorem. No independent review, Lean formalization,
or publication-level novelty claim. **General nonhomogeneous isotropic
Morrey remains open.** The signed homogeneous audit/formalization is
separate. Nothing in this note depends on the candidate signed theorem.

The earlier [projection-max theorem](IWANIEC_MORREY_NONHOMOG_PROJECTION_MAX.md)
uses independent scalar projections. Here we can truncate an entire
compatible vector gradient in one operation, with the same exact
boundary-or-original selection property. This is not a fixed number
of scalar constraints: the whole operator-norm ball is imposed at once.
The construction works for vector maps in arbitrary finite dimensions.

## 1. Full-vector projection theorem

Let A be a real m-by-n matrix, let R>0 with ||A||op<=R,
and let u(x)=Ax+phi(x), where phi is a Lipschitz Z^n-periodic
map with values in R^m. Let v(x)=Ax+zeta(x), where zeta minimizes
the squared L2 distance to phi on the unit torus among periodic
Lipschitz zeta with
$$
\|A+D\zeta\|_{\rm op}\le R\quad\text{a.e.}
$$
All norms in the domain and target are Euclidean; the norm on
linear maps is the corresponding operator norm.

**Theorem A.** The minimizer exists uniquely as an L2 projection
and has the Lipschitz representative described above. Its
gradient satisfies
$$
\boxed{Dv=Du\quad\text{or}\quad\|Dv\|_{\rm op}=R
       \quad\text{a.e.}}
\tag{1}
$$
In fact, at every differentiability point of v where
||Dv||op<R, one has v=u. For EVERY domain direction e,
$$
\boxed{\int (Dv)e\cdot(Du-Dv)e\ge0.}\tag{2}
$$
Equivalently the integral of the symmetric part of
(Dv)^T(Du-Dv) is positive semidefinite. In particular
$$
\int |(Dv)e|^2+\int |(Du-Dv)e|^2\le\int |(Du)e|^2,
\quad
\int Dv:(Du-Dv)\ge0.
\tag{3}
$$
This simultaneously controls all spatial directions; no
independently projected scalar rows are required.

### 1.1 Existence and the projection inequality

The admissible set C is nonempty (zeta=0), convex, and closed
in L2(T^n;R^m). To see closedness, an L2-convergent sequence
in C has uniformly bounded L2 norms and a uniform Lipschitz
bound R+||A|| for its periodic parts. On the torus, bounded
means and the common Lipschitz bound give uniform sup bounds.
Arzela--Ascoli gives a uniformly convergent subsequence whose
limit is the given L2 limit. The affine-plus-periodic maps
of the sequence are globally R-Lipschitz on R^n: this follows
from their gradient bound, for example by convolution and
integration on segments. The limit is therefore R-Lipschitz
and admissible. Hilbert projection proves existence, uniqueness,
and the variational inequality
$$
\int (u-v)\cdot(w-v)\le0
\tag{4}
$$
for every admissible affine-plus-periodic w with the same A.
Here w-v and u-v are periodic.

### 1.2 Boundary selection by an inner-ball replacement

We give explicit constants in dimension n=2, the intended
application. The identical proof in general n uses
inner volume (1-tau)^n and outer annulus volume at most n tau
times the ball volume.

Suppose v is differentiable at x0, B=Dv(x0),
||B||op<R, but h0=u(x0)-v(x0) is nonzero.
Set
$$
\Delta=R-\|B\|_{\rm op}>0,\qquad
e_0=h_0/|h_0|,\qquad
\tau=\Delta/(320R)\le1/320.
$$
Let rho>0 be small enough that the ball B_rho(x0)
embeds in the flat torus (rho<1/4 suffices). Set
epsilon=Delta tau rho/4. Differentiability and continuity
allow rho to be chosen so that throughout this ball
$$
\begin{aligned}
|v(x)-\ell(x)|&\le\epsilon/4,\qquad
\ell(x)=v(x_0)+B(x-x_0),\\
|(u-v)(x)-h_0|&\le|h_0|/4 .
\end{aligned}
\tag{5}
$$
The first follows because epsilon/rho is a fixed positive
number after B and tau are fixed.

Prescribe a competitor on the union of the closed inner ball
of radius (1-tau)rho and the outer sphere of radius rho:
$$
w(x)=\ell(x)+\epsilon e_0\quad\text{in the inner ball},\qquad
w(y)=v(y)\quad\text{on the outer sphere}.
$$
The prescribed function is R-Lipschitz. Pairs within either
set have this bound. For a cross pair,
|x-y|>=tau rho, and by (5)
$$
|w(x)-w(y)|\le (R-\Delta)|x-y|+5\epsilon/4
              \le R|x-y|,
$$
because 5epsilon/4<Delta tau rho.
Kirszbraun's theorem now extends these prescribed values
to the intervening annulus with the SAME Lipschitz constant R.
This is precisely the Euclidean vector-valued extension step
missing from a coordinatewise min/max argument. A standard
reference is Azagra, Le Gruyer and Mudarra, *Kirszbraun's theorem
via an explicit formula*, Canadian Mathematical Bulletin 64
(2021), 142--153, [doi:10.4153/S0008439520000314](https://doi.org/10.4153/S0008439520000314).

Put w=v outside the ball, and repeat the modification on all
integer translates with the corresponding affine increment A k.
The balls are disjoint. This yields an affine-plus-periodic
w with base A and global Lipschitz constant R. For the latter,
partition any line segment at its intersections with the
finitely many modified balls it meets, and add the Lipschitz
inequalities on the resulting pieces. Thus w is admissible.

On the inner ball, (5) implies
$$
(u-v)\cdot(w-v)\ge |h_0|\epsilon/4.
$$
Indeed its epsilon e0 term is at least 3|h0|epsilon/4
and the error has absolute value at most
(5|h0|/4)(epsilon/4). The inner ball has area at least
pi rho²/2. On the annulus, choose the nearest outer sphere
point y. Since both maps are R-Lipschitz and agree at y,
|w-v|<=2R tau rho. Hence the integrand is at least
-(5/2)|h0|R tau rho on the annulus, whose area is at most
2 tau pi rho². Summing,
$$
\begin{aligned}
\int (u-v)\cdot(w-v)
&\ge \pi|h_0|\rho^3
       \left(\frac{\Delta\tau}{32}-5R\tau^2\right)\\
&=\frac{\pi|h_0|\rho^3\Delta^2}{20480 R}>0 .
\end{aligned}
$$
This contradicts (4). Thus v=u at every differentiability
point of v with gradient strictly inside the operator ball.
On the set {v=u}, the gradient of the Lipschitz map u-v
vanishes almost everywhere (apply the usual scalar zero-set
derivative lemma to its components). Rademacher now proves (1).

For general n choose tau small enough that (1-tau)^n>=1/2
and (5/2)n R tau<Delta/32. The volume comparison gives the
same strict contradiction. The proof is valid for every
finite target dimension m. It does not assert such a local
selection principle for arbitrary non-Euclidean gradient
constraints, which need not have the requisite extension property.

### 1.3 Directional quadratic sign

For every h in R^n the periodic competitor
(zeta(x+h)+zeta(x-h))/2 is admissible, since the constraint
is convex and translation invariant. By (4),
$$
\int (\phi-\zeta)\cdot
       (\zeta(x+h)+\zeta(x-h)-2\zeta(x))\le0 .
$$
Periodic change of variables changes the left side into
$$
-\int ((\phi-\zeta)(x+h)-(\phi-\zeta)(x))
         \cdot(\zeta(x+h)-\zeta(x)).
$$
Take h=t e, divide by t² and let t tend to zero.
Lipschitz difference quotients converge in L2 to the
corresponding directional derivatives (also bounded by
the Lipschitz constants). This proves
int D_e zeta dot D_e(phi-zeta)>=0.
Adding the constant Ae to the first factor does not change
the integral, because the second factor has mean zero.
Thus (2) holds. Expanding the squared norm of
(Du)e=(Dv)e+(Du-Dv)e proves (3). QED.

The scalar nonlinear sign for arbitrary convex gradient
potentials used a scalar comparison principle. We do NOT
infer its full vector-valued counterpart from (2).
This is an important distinction.

## 2. Full-matrix projection-max theorem

For planar matrices define the compact choice set
$$
\mathcal Z_R(X)=\{Z:\|Z\|_{\rm op}=R\}
                 \cup\big(\{X\}\text{ if }\|X\|_{\rm op}\le R\big).
$$
Let P be any finite continuous polyconvex function on R^(4x2)
(or any finite continuous QC function on that matrix space
whose Jensen inequality is already known).
Let B be any symmetric positive semidefinite 2-by-2 matrix.
Define
$$
\boxed{
G(X)=\max_{Z\in\mathcal Z_R(X)}
 \left[P\left(\begin{bmatrix}X\\ Z\end{bmatrix}\right)
       +\operatorname{tr}(B Z^T(X-Z))\right].
}
\tag{6}
$$

**Theorem B.** G is finite, continuous, and globally QC.
This uses the actual full-vector compatibility of Z,
not an independent projection of its rows.

The maximum exists by compactness. The choice sets vary
continuously in the Hausdorff metric: the extra interior
choice X merges into the fixed sphere at the boundary.
Thus continuity follows by uniform continuity on compacts.

At a base A choose a maximizing Z0. If ||Z0||op=R, choose
Z(x)=Z0 constant. Otherwise Z0=A and ||A||op<R, so use
the operator-ball projection of Section 1 for u=Ax+phi.
Equation (1) gives Dv(x) in Z_R(X(x)) a.e., where X=Du.
In both cases Z(x) is a compatible gradient with mean Z0,
and the full stack [X;Z] is a compatible 4x2 gradient
with mean [A;Z0]. Its mixed two-row minors therefore
have the prescribed means. Polyconvex Jensen for P
(or its assumed QC) applies to this whole stack.
For a fixed Z0 the integral of the correction term equals
its base value. For the projected Z the base correction
is zero and its integral is nonnegative by (2), after
diagonalizing B with nonnegative eigenvalues. Pointwise
maximization and integration prove Jensen for G.

The theorem also allows a fixed center C in the operator
constraint, by projecting u-Cx and adding back Cx. In the
correction the projected matrix can be replaced by Z-C,
since the extra constant term has zero average when Z
is a projection. The same proof permits fixed invertible
changes of target and domain coordinates (with the
corresponding Euclidean metrics in the projection).
Independent copies may be stacked with the original
gradient if mixed-minor calibrations require them.
No universal support-completeness assertion is made.

## 3. A global extension theorem for entire QC cores

There is a useful version not requiring P to be globally
QC on all matrices. Let Q be a continuous function on the
closed operator ball B_R. Assume its Jensen inequality
holds for every compatible gradient field whose values
are in that ball, at its mean. This is a *localized*
QC hypothesis on Q, not an assumption outside B_R.

For lambda>=0 and c real define the exterior convex function
$$
C_R(X)=\max_{\|Z\|_{\rm op}=R}
       [Q(Z)-c\det Z+\lambda Z:(X-Z)].
$$
Then the following is globally QC:
$$
G_R(X)=c\det X+
\begin{cases}
\max(Q(X)-c\det X,C_R(X)),&\|X\|_{\rm op}\le R,\\
C_R(X),&\|X\|_{\rm op}>R .
\end{cases}
\tag{7}
$$
The branches agree on the boundary because Z=X is an
allowed boundary choice. To prove QC, if the maximizing
base choice is boundary, use convex Jensen for C_R and
the null Lagrangian. If the base interior choice is
Q(A), project the whole vector map to B_R. Its gradient
Z belongs to the pointwise choice set (1), so
$$
G_R(X)\ge Q(Z)+c(\det X-\det Z)+\lambda Z:(X-Z).
$$
The localized Jensen hypothesis for Q applies to Z;
the determinant terms integrate to zero and the correction
has nonnegative integral by (2). This proves the claim.

Thus a QC core on a compact matrix ball admits a specific
QC extension with a convex-plus-determinant exterior.
It is not necessary to assume a homogeneous or polyconvex
core. If Q is isotropic and lambda,c are constants, the
extension is isotropic as well. One can use the already
proved homogeneous integrands as cores, even though the
extension is no longer homogeneous. More general stacked
calibrations as in (6) are available when their core
Jensen inequality can be established.

**Concrete criterion for arbitrary nonhomogeneous F.**
To prove QC at a prescribed base A for a bounded gradient
range, it suffices to find R>||A||op, such a localized QC
core Q with Q<=F on B_R and Q(A)=F(A), and lambda>=0,c
such that
$$
Q(Z)+c(\det X-\det Z)+\lambda Z:(X-Z)\le F(X)
\quad\text{for all relevant X and all }\|Z\|_{\rm op}=R.
\tag{8}
$$
Then (7) supplies the touching QC minorant on the entire
test range. This separates the core Jensen question from
the exterior boundary calibration. It is a sufficient
mechanism, not a proof that every RC F admits (8).

## 4. Explicit spectral calibration and exact checks

For illustration, a simple mixed-minor choice in (6) is
$$
P([X;Z])=\gamma\det Z+\eta\,\operatorname{cof}Z:X,\qquad
B=\lambda I,\quad\lambda>0.
$$
This is polyaffine on the stacked space: cof Z:X is a
sum of two mixed two-row determinants. The scalar
coefficients gamma,eta may be arbitrary real numbers.
An additional multiple of det X is harmless.

Write s=||X||op, delta=det X/s (zero at s=0),
x=(s+delta)/2 and y=(s-delta)/2. Put
$$
a=|\lambda+\eta|,\quad b=|\lambda-\eta|,\quad
q=a x-b y+\gamma R.
$$
The boundary maximum in (6) has the exact formula
$$
C(s,\delta)=R(a x+b y)-\lambda R^2
             +q t_*-\lambda t_*^2,\qquad
t_*=\min(R,\max(-R,q/(2\lambda))).
\tag{9}
$$
Indeed a boundary matrix Z has signed spectral coordinates
(R,t), |t|<=R. Its conformal and anticonformal moduli are
(R+t)/2 and (R-t)/2. In conformal coordinates,
cof Z negates the anticonformal part and leaves the
conformal part unchanged. Independent optimization over
the two phases of Z gives
$$
a(R+t)x+b(R-t)y+\gamma R t-\lambda(R^2+t^2).
$$
The remaining scalar concave quadratic is maximized at
the clamped value t_* in (9). The full QC profile is
$$
G(s,\delta)=
\begin{cases}
\max\big((\gamma+2\eta)s\delta,C(s,\delta)\big),&s\le R,\\
C(s,\delta),&s>R.
\end{cases}
$$
This is a closed form genuinely two-variable
nonhomogeneous calibration; no claim is made that this
simple parameter family alone exceeds all the earlier
shifted scalar projection constructions.

The checker [vector_projection_exact.py](../../research/audit/vector_projection_exact.py)
was actually executed in the working container.
It checked the strict local comparison constants and 792
exact rational boundary maximum/contact controls with both
signs of mixed-minor coefficient. Output:
    Exact local comparison constants: passed
    Exact boundary maximum and interface contact: 792 rational controls passed
These finite algebra checks do not replace the analytic
Kirszbraun or Jensen proofs.

## 5. Remaining research goal

The full-vector projection supplies the missing ability
to clip the OPERATOR NORM of an entire compatible gradient
without destroying its spatial compatibility and with the
exact selection (1). This is a qualitative advance over
independent scalar rows. It can be combined with arbitrary
polyconvex stacked calibrations, or the proved QC cores of
Section 3, without any count of modes or amplitudes.

The unresolved step is an energy-decreasing use of this
projection for arbitrary isotropic RC F. In particular (1)
does not imply that Du-Dv has rank one, and rank-one
convexity alone does not justify a pointwise tangent
inequality along that difference. The quadratic sign (2)
does not justify weighted determinant or general
matrix-potential signs. We have not proved (8) for
arbitrary F or global completeness of (6). Do not present
the vector selection theorem as solving Morrey.

The exact objective remains arbitrary finite-valued
isotropic RC => QC, with no homogeneity. No fixed-wave,
fixed-exponent, separated-curvature or scalar-row-count
ladder is resumed. The next proof attempt should exploit
the full-vector spectral boundary and the mixed-minor
calibrations, or obtain a direct energy comparison
between a gradient and its vector projection.
