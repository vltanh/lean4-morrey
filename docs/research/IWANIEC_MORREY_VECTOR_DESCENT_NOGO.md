# Operator-ball projection: exact energy-descent obstruction and the variable-coefficient heat-flow criterion

24 November 2026. The objective remains RC => QC for every finite-valued
isotropic integrand on real 2x2 matrices, without homogeneity.

**Result:** the direct proposed energy-decreasing use of the L²
full-vector operator-ball projection is false, even for a smooth
convex isotropic quartic. More generally, universal energy descent
under this projection forces a restrictive PDE on every C³
isotropic integrand. We prove this with actual periodic compatible
gradients and an exact normal-cone certificate, not a spectral law
or numerical experiment. The earlier boundary selection and
projection-max extension theorems are unaffected.

We also record the all-profile exact-two-form heat-flow criterion
below, motivated by Bruno--Pasqualotto, *Quasiconvexity for the
Dacorogna--Marcellini Energy*, arXiv:2608.06367. Local algebraic
feasibility follows from planar quadratic polyconvexity. Global
integrability of the correcting form remains unresolved. This is
a possible direct analytic attack, NOT a new universal proof.

Hand arguments; the exact algebra checker was executed locally.
No new Lean theorem, novelty clearance, independent referee review,
or solution of general isotropic Morrey is claimed. The signed
homogeneous audit/formalization is separate.

## 1. Normal stresses certify actual projections

Let C_R be the closed convex set of periodic vector maps v on the
unit flat two-torus with ||Dv||op<=R almost everywhere. The affine
base here is zero. Its L² metric projection is P_R, as in
[the vector projection theorem](IWANIEC_MORREY_NONHOMOG_VECTOR_PROJECTION.md).

Suppose v is in C_R and is smooth on a small open patch U where
||Dv||op=R and the largest singular value is simple. Define the
matrix field n=D_A||A||op evaluated at A=Dv; it has rank one and
satisfies n:Dv=R and n:B<=R whenever ||B||op<=R.
Take any nonnegative smooth mu compactly supported in U, and put
S=mu n, h=-div S (rowwise divergence). For every w in C_R,

    int h·(w-v) = int S:(Dw-Dv) <= 0.

Thus h is an outward L² normal. For every eps>=0, put u_eps=v+eps h.
Expanding the squared distances shows

    ||u_eps-w||² - ||u_eps-v||²
       = ||w-v||² - 2 eps int h·(w-v) >= ||w-v||².

Consequently P_R u_eps=v exactly. No computation of a numerical
projection is involved. The displacement h has mean zero.

For any C³ energy F, its first variation along this ray is

$$
\left.\frac{d}{d\varepsilon}\int F(Du_\varepsilon)\right|_0
=\int DF(Dv):Dh
=-\int \mu\, n:D(\operatorname{div} DF(Dv)).
\tag{1}
$$

The integrations by parts are confined to the smooth patch.
Outside it, u_eps=v, so global smoothness of v is unnecessary.

In particular if the last integrand before the minus sign is
strictly positive near some point, choose a nonzero mu>=0 there.
Then the energy of u_eps is strictly smaller than that of its
projection for every sufficiently small eps>0.

## 2. Explicit convex quartic obstruction

Take R=1 and F(A)=||A||_F^4, an everywhere convex smooth isotropic
function. In a small Euclidean ball of radius rho=1/100 about
(1,0), use polar coordinates (r,theta) and prescribe

    v=(r-1, k theta),  k=4/5.

Use the local continuous branch of theta. In this ball r>=1-rho>k,
and the rows of Dv are the orthogonal vectors e_r and (k/r)e_theta.
Thus ||Dv||op=1, its smaller signed singular value is t=k/r in
(0,1), and n=e_1 tensor e_r, where e_1 is the first TARGET vector.

To extend this map to a periodic admissible v, translate the
local coordinate patch so its center lies at the center of a unit
fundamental square. On the closed rho-ball the prescribed map is
1-Lipschitz by integration on segments, and vanishes at its center.
On the exterior of the concentric 2rho-ball prescribe the constant
zero. These prescriptions on their union are 1-Lipschitz:
cross-pair distances are at least rho, while prescribed values on
the inner ball have norm at most rho. Kirszbraun's extension theorem
fills the annulus with the same Lipschitz constant. Repeat the
resulting map periodically. It is globally 1-Lipschitz, since it
vanishes outside the disjoint translated balls; partition a line
segment at the boundaries of the balls to verify this. This
construction preserves the exact smooth formula on the inner
patch.

Here DF(Dv)=4(1+t²)Dv. Its rowwise divergence has first component

    (div DF(Dv))_1 = 4(1-t²)/r,

because div e_r=1/r and t=k/r. Therefore

$$
n:D(\operatorname{div}DF(Dv))
=\frac{4(3k^2-r^2)}{r^4}>0
\tag{2}
$$

throughout the patch. Indeed 3k²>(1+rho)². The uniform rational
lower bound is 359960000/104060401 > 0.

Choose any nonzero smooth nonnegative bump mu supported in the
patch and use (1). This yields actual periodic Lipschitz u_eps
with P_1 u_eps=v and

$$
\boxed{\int\|D(P_1u_\varepsilon)\|_F^4
       >\int\|Du_\varepsilon\|_F^4}
$$

for all sufficiently small positive eps. This is an exact
counterexample to universal energy contraction under P_R.
It does NOT contradict quasiconvexity of the quartic (the
quartic is convex). It also does not contradict the vector
projection's directional quadratic sign.

## 3. General obstruction at every simple singular-value pair

The failure is not peculiar to the quartic.

**Theorem.** Let F be any C³ isotropic integrand, with signed
singular-value profile f(s,t)=F(diag(s,t)), s>|t|. Suppose for
EVERY R>0 and periodic Lipschitz u the following were true:

    int F(D(P_R u)) <= int F(Du).

Then necessarily, throughout the open spectral sector,

$$
\boxed{
f_{st}+\frac{t f_s-s f_t}{s^2-t^2}=0.
}
\tag{3}
$$

In fact if (3) fails at any (R,t), there is an exact counterexample
for that R, at zero affine base. The argument does not require
rank-one convexity of F. Even ordinary convexity does not imply
(3).

### 3.1 Realizing compatible third jets on the saturated sphere

Fix R>|t|. In a neighborhood of the origin prescribe the second
component

    v_2(x_1,x_2)=t x_2 + (a/2) x_1² x_2,

where a is an arbitrary real number. We construct an analytic
first component with Dv(0)=diag(R,t), all second derivatives of
both components zero at 0, and all third derivatives of v_1
zero at 0, while ||Dv||op=R throughout a neighborhood.

For a real matrix M with rows (p,q),(j,w), let

    H(p,q,j,w)=det(R² I - M^T M).

At (R,0,0,t), H=0, H_p=-2R(R²-t²) is nonzero, and all
three other first partial derivatives vanish. The analytic
implicit function theorem solves H=0 near this point as
p=h(q,j,w) with h(0,0,t)=R and Dh(0,0,t)=0.

The first-order analytic Cauchy problem

    ∂_1 v_1=h(∂_2 v_1, ∂_1 v_2, ∂_2 v_2),
    v_1(0,x_2)=0

has a local analytic solution by the classical
Cauchy--Kowalevski theorem (the displayed equation is solved
for the derivative transverse to the initial line). It
satisfies the required first jet. Differentiating once at
the origin, Dh=0 gives all second derivatives involving
x_1 zero; the remaining second derivative vanishes by
the initial condition. Differentiating a second time, the
first derivatives of all arguments of h vanish (they are
second derivatives of the components). With Dh=0, every
third derivative of v_1 involving x_1 also vanishes. The
pure x_2 derivative vanishes by the initial condition.

The eigenvalue condition H=0 and closeness to diag(R,t)
ensure that the other squared singular value is strictly
below R². Hence the top singular value is exactly R,
simple, on a sufficiently small neighborhood. This is
an actual compatible saturated local map, not merely
a prescribed matrix-valued jet.

Subtract its value at zero, restrict to a small closed
ball, extend by zero outside the double-radius ball
using Kirszbraun as in Section 2 (with Lipschitz constant
R), and periodize. This produces an admissible v with
the desired local analytic formula.

### 3.2 Exact forced PDE

At the origin n=e_1 tensor e_1, now using the two standard
first coordinate vectors in target and domain. All second
derivatives of v vanish, so the D³F terms in the derivative
of div DF vanish. The only relevant third derivative of v_2
is ∂_112 v_2=a and its permutations. Therefore

    n:D(div DF(Dv)) = a (F_{11,22}+F_{12,21})(diag(R,t)).

Here subscripts on F denote matrix-entry Hessian components.
The first term is f_st. For the second, write F=Phi(x,y)
in the conformal moduli x=(s+t)/2, y=(s-t)/2. Varying
entries A12,A21 varies the imaginary conformal and
anticonformal components by opposite and equal signs,
respectively. Direct differentiation at positive x,y gives

$$
F_{12,21}=\frac14(\Phi_y/y-\Phi_x/x)
          =\frac{t f_s-s f_t}{s^2-t^2}.
$$

If the bracket in (3) is nonzero, choose the sign of a
so the displayed normal contraction is strictly positive.
Continuity gives positivity on a smaller patch, and the
normal stress construction in Section 1 gives the strict
energy reversal. This proves the theorem.

Equivalently in the squared-modulus variables
u=x²,v=y², writing F=G(u,v), condition (3) becomes

    u G_uu = v G_vv.

This is an extra PDE, not a consequence of rank-one
convexity. For example f(s,t)=(s²+t²)² gives the left
side of (3) equal to 8st, nonzero for st!=0.

We do NOT assert the converse: satisfying (3) may not
suffice for contraction under P_R. The theorem gives
a complete obstruction whenever the PDE fails. It
precludes the last proposed universal descent step,
independently of the number of shells, any numerical
projection tolerance, or the signed homogeneous audit.

## 4. A direct all-profile heat-flow certificate (future construction)

The projection obstruction above does not rule out an
energy-dependent flow, or use of the valid projection-max
QC generators. A separate direct approach is the exact
two-form heat-flow technique of Bruno--Pasqualotto
(arXiv:2608.06367, Theorems 1--2 and Lemma 4).
Here is its explicit general-isotropic version, not
restricted to homogeneous polynomials.

Let F=Phi(x,y), where x=|z| and y=|w| in conformal
coordinates. Assume F smooth. At x,y>0 use rotations
to make z=x,w=y real. Put
A=Phi_xx, B=Phi_xy, C=Phi_yy, P=Phi_x/x, Q=Phi_y/y.
For a compatible gradient field denote
z_1=u+i a, z_2=v+i b,
w_1=p+i c, w_2=q+i d.
Equality of mixed derivatives of the underlying map is

    z_1+i z_2 = w_1-i w_2,

so c=a+v+q and d=u-p-b.

Seek two scalar potentials g(x,y),h(x,y) such that the
one-form

    alpha = g(x,y) d arg z + h(x,y) d arg w

extends smoothly to the axes and origin. One sufficient
regularity choice is g=x² G(x²,y²), h=y² H(x²,y²)
with smooth G,H. The integral of the pullback of d alpha
by any smooth periodic compatible gradient is zero.

The heat dissipation density plus this exact correction
is the sum of the following two 3-variable quadratic forms:

$$
\begin{aligned}
E_1={}& A u^2+2Bup+Cp^2+Pb^2+Q(u-p-b)^2\\
 &+\frac{g_x u+g_y p}{x}b
 +\frac{h_x u+h_y p}{y}(u-p-b),\\
E_2={}& A v^2+2Bvq+Cq^2+Pa^2+Q(a+v+q)^2\\
 &-\frac{g_x v+g_y q}{x}a
 -\frac{h_x v+h_y q}{y}(a+v+q).
\end{aligned}
\tag{4}
$$

This follows simply by differentiating the one-form
and using the displayed compatibility identity.
The two triples are independent. Rotational invariance
makes the test valid at every pair of phases: proper
rotations in the domain preserve the oriented two-form
pullback and the sum of the two heat-Hessian terms.

**Sufficient criterion:** if both 3x3 quadratic matrices
in (4) are positive semidefinite at every x,y>0, and the
form extends as stated, then F is quasiconvex.
Indeed for the componentwise periodic heat flow the
energy derivative is the negative integral of the
unmodified Hessian density. The exact-form integral is
zero by Stokes, so the energy is nonincreasing. The heat
flow tends to the affine map; smooth periodic tests
and then Lipschitz approximation prove QC. Smoothness
of the form and F gives the pointwise inequality on
the axes by continuity.

For any *fixed* pair x,y, rank-one convexity already
makes the matrix feasibility problem in (4) nonempty.
Use the quadratic polyconvexity theorem in 2x2:
the Hessian is a PSD quadratic plus
lambda(|dz|²-|dw|²), for some real lambda at that pair.
For compatible derivatives the latter quadratic summed
over spatial directions is
2 lambda (J_z+J_w), where

    J_z=u b-v a,  J_w=p d-q c.

Choose g_x/x=h_y/y=-2lambda and g_y=h_x=0 at this
single pair to cancel the determinant part exactly.
This verifies local feasibility, but not the global
existence of g,h: if lambda varies in both variables,
the proposed four first derivatives may be mutually
inconsistent. It is therefore invalid to choose
pointwise quadratic supports and integrate them as
if the resulting two-form were closed.

A universal positive result by this route would require
a **global** smooth pair satisfying both PSD inequalities,
or another exact integrated heat dissipation argument.
No such existence theorem is proved here. In particular
we do not infer heat-flow monotonicity of every RC
integrand from its rank-one Hessian inequality. This
criterion is a precise possible next investigation,
with two scalar unknown functions and no fixed degree,
homogeneity or wave count.

## 5. Verification and disposition

The checker [vector_descent_exact.py](../../research/audit/vector_descent_exact.py)
was executed with Python/SymPy. Output:

    Exact local quartic normal-stress obstruction: 359960000/104060401
    Exact implicit constraint jet and shear Hessian identities passed
    Exact heat-flow determinant cancellation passed

The analytic existence, normal-cone and Stokes arguments
supply the actual theorem; no numerical sampling of
projection outputs is used.

**Status:** no new general RC=>QC proof. The previously
proposed universal energy descent under the fixed L²
vector projection is refuted, even for convex energies;
do not continue that route with more radii. Preserve
the valid vector boundary-selection and QC-extension
theorems. General isotropic nonhomogeneous Morrey
remains open. No new Lean theorem.
