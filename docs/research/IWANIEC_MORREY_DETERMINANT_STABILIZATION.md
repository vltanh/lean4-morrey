# General isotropic Morrey: determinant-only polyconvexification and a global two-branch convex normal form

24 November 2026. **Positive all-integrand theorem and exact reduction
of the general isotropic gate.** No homogeneity, sign, separated-profile,
wave-count, or determinant-orientation assumption on the original
integrand. In contrast to the preceding exponential reparametrization,
we leave the energy unchanged except for a single convex quadratic
function of the determinant, with an explicit bound on its coefficient.
The resulting stabilized energy is polyconvex, not merely QC, on
each compact test ball. We also prove the unmodified integral Jensen
inequality for every constant-determinant test, without smoothness.

The new reduction is independent of the signed homogeneous candidate
under separate audit, the truncated-determinant theorem, and the
transition-layer arguments. All proofs are elementary. The exact
checker was run in the working container; no Lean proof, external
referee review, or novelty clearance is claimed.

**General isotropic Morrey remains OPEN:** determinant stabilization
is not an integral Jensen inequality for the original F if the
determinant fluctuates. We do not send its coefficient to zero without
a proof. The global normal form at the end preserves the full general
problem and identifies a concrete next gate, rather than a family
indexed by homogeneous degrees.

## 1. Coordinates and constant-Jacobian convexity

Identify a real 2x2 matrix X with its complex conformal and
anticonformal parts z,w, so
    X v = z v + w conjugate(v).
Write x=|z|, y=|w|, d=det X=x²-y², and s=||X||op=x+y.
Then |X|_F²=2(x²+y²). A direction with complex parts (a,b)
has rank at most one exactly when |a|=|b|.
Independent rotations of the two complex parts are induced by the
proper left/right rotations. Thus every isotropic F can be written
    F(X)=f(x,y),
where f(x,y)=F(diag(x+y,x-y)) on x,y>=0, and the same formula on
real x,y extends the profile evenly in each variable.

**Lemma (all determinant fibers).** Let F be any finite-valued
isotropic rank-one convex integrand, with no differentiability
hypothesis. For d>=0 put
$$
g_d(t)=f(\sqrt{d+t^2},|t|)\quad(t\in\mathbb R).
$$
Then g_d is even and convex on R. Indeed it is the restriction
of F to the rank-one line whose conformal coordinates are
    z=sqrt(d)+i t,  w=t.
The direction (i,1) has rank one and squared Frobenius norm 4.
The determinant is identically d on this line.
Hence g_d is nondecreasing on t>=0, and the function
    w -> g_d(|w|)
on the complex plane (identified with R²) is convex: use the
triangle inequality followed by monotonicity and scalar convexity.
It agrees with F(X) on the entire determinant-d fiber.
For d<=0 reflect X by J=diag(1,-1), which exchanges z,w and
negates d. There the convex extension depends on z instead.

Consequently, for EVERY compact probability law of matrices
with mean A and det X=det A almost surely,
$$
\boxed{F(A)\le \int F(X)\,d\nu(X).}
\tag{1}
$$
The proof is ordinary convex Jensen in w when det A>=0, or
in z when det A<=0. No gradient compatibility beyond the
mean matrix is needed under the constant-determinant hypothesis.
In particular this is an unmodified integral QC inequality
for every affine-boundary or periodic test with constant Jacobian,
at every base including rank-deficient and both orientations.

This is related to the planar incompressible convexity result of
Ghiba et al., *Rank-one convexity implies polyconvexity in
isotropic planar incompressible elasticity*, J. Math. Pures Appl.
116 (2018), 88--104. We do not claim priority for the fiber lemma.
Our purpose is to use its elementary shear proof quantitatively
for arbitrary determinant variation and the full nonhomogeneous
gate.

## 2. Main quantitative determinant-stabilization theorem

Let F be C⁴, isotropic, and uniformly strongly rank-one convex
on the closed operator-norm ball B_(3R), R>0. Write the uniform
Legendre--Hadamard bound as
$$
D^2 F(X)[H,H]\ge m|H|_F^2,\quad m>0,
$$
for rank-one H and ||X||op<=3R.
This is stronger than merely strict convexity on each rank-one
line; invariant smoothing and adding epsilon|X|_F² give this
hypothesis without loss for any strict Jensen violation of
the general finite-valued problem.

Let M3 and M4 be the finite bounds on the nonnegative spectral
triangle x+y<=3R:
$$
M_3=\sup\max(|f_{xxy}|,|f_{xyy}|),\qquad
M_4=\sup\max(|f_{xxxx}|,|f_{yyyy}|).
$$
Define
$$
L=M_3/2+R M_4/6,\qquad
\boxed{C_R=M_4/24+L^2/(4m).}
\tag{2}
$$

**Theorem A.** F+C_R det² admits a polyaffine supporting function
on B_R at EVERY base A in B_R, hence is the restriction of a
finite globally polyconvex isotropic integrand. Each support
can be chosen to use just ONE of the two complex linear
coordinates, in addition to the determinant:
* if det A>=0, use w and det X;
* if det A<=0, use z and det X.

More precisely, writing d0=det A, there are a real linear
functional l on the indicated complex coordinate v and a real
number c such that for every X in B_R,
$$
\boxed{
F(X)-F(A)+C_R(d-d_0)^2
\ge l(v-v_A)+c(d-d_0)+m|v-v_A|^2.
}
\tag{3}
$$
Here v=w for the nonnegative determinant base, and v=z for the
nonpositive one. The determinant of X itself is allowed either
sign, irrespective of the base. The coefficient C_R is uniform
in the base and in X. Its explicit value is sufficient,
not asserted optimal.

### 2.1 Uniform strong convexity in one complex coordinate

Suppose d0>=0 (the negative case follows by reflection).
Use the rank-one line from Section 1. For |t|<=R its
operator norm is sqrt(d0+t²)+|t|<3R, since d0<=R².
The rank-one Hessian bound gives g_d0''(t)>=4m there.
In particular the even function g_d0(t)-2m t² is convex
and nondecreasing on [0,R]. The corresponding radial function
on the disk |w|<=R is convex. Thus h(w)=g_d0(|w|) satisfies
$$
h(w)\ge h(w_A)+Dh(w_A)\cdot(w-w_A)+2m|w-w_A|^2 .
\tag{4}
$$
It is differentiable even at w_A=0 by evenness and C⁴
regularity of the matrix integrand. The tangent inequality
also holds at the disk boundary by continuity, or by using
the strict margin between (sqrt(2)+1)R and 3R.

### 2.2 Taylor in the determinant, including a sign change

For y>=0 and d+y²>=0 define
$$
G(d,y)=f(\sqrt{d+y^2},y).
$$
This is smooth enough up to d+y²=0 for the following
estimates. In particular write B(u,y)=f(sqrt(u),y), u>=0.
Evenness in x and C⁴ regularity imply
$$
B_u(u,y)=\frac12\int_0^1 f_{xx}(t\sqrt u,y)\,dt ,
$$
and, for u>0,
$$
B_{uu}(u,y)=\frac14\int_0^1 t^2\int_0^1
                  f_{xxxx}(v t\sqrt u,y)\,dv\,dt.
$$
These follow by the fundamental theorem of calculus and
f_x(0,y)=f_xxx(0,y)=0. The right sides extend continuously
to u=0. Therefore
$$
|B_{uu}|\le M_4/12,\qquad |B_{uy}|\le M_3/2.
$$
All arguments needed below have 0<=y<=R, 0<=sqrt(u)<=sqrt(2)R,
so the derivative bounds on the triangle apply.
Since G(d,y)=B(d+y²,y),
$$
|G_{dd}|\le M_4/12,\quad
|G_{dy}|\le M_3/2+R M_4/6=L.
\tag{5}
$$

For any X in B_R, put y=|w| and d=det X. The segment
between d and d0 at this fixed y is admissible:
d+y²=x²>=0 and d0+y²>=0. On that segment the indicated
bounds apply. Thus the determinant Taylor inequality gives
$$
F(X)=G(d,y)\ge G(d_0,y)+G_d(d_0,y)(d-d_0)
                  -\frac{M_4}{24}(d-d_0)^2.
$$
Choose c=G_d(d0,|w_A|). By (5),
$$
|G_d(d_0,y)-c|\le L\,|y-|w_A||\le L|w-w_A|.
$$
Apply (4) to G(d0,y)=h(w). Absorb the cross term with
    L |w-w_A| |d-d0| <= m|w-w_A|² + L²(d-d0)²/(4m).
This is exactly (3), with l=Dh(w_A).
For det A<0 the proof applies to the reflected F,
using the derivative bounds with x and y interchanged;
the determinant sign change is accounted for by negating
the resulting determinant coefficient c. The same C_R
works for both. QED.

### 2.3 Polyconvexity on the entire compact ball

Expand C_R(d-d0)² in (3). Dropping the nonnegative
quadratic term on the right gives the supporting inequality
$$
F(X)+C_R d^2\ge F(A)+C_R d_0^2+
                  l(v-v_A)+(c+2C_Rd_0)(d-d_0).
\tag{6}
$$
The right side is affine in (X,det X), and equality
holds at X=A. Its coefficients are uniformly bounded for
A in B_R by the smoothness and compactness bounds used above.
Take the supremum of all these lifted affine functions
on R^(2x2) x R. The supremum is finite everywhere and
convex, and equals F+C_R det² along the minors graph in
B_R. Its composition with (X,det X) is a globally finite
polyconvex integrand agreeing with the stabilized energy
on the full test ball.

One can symmetrize the supremum over rotations, preserving
both inequalities and equality on B_R. In fact each l
comes from a radial convex h, so for nonzero v_A it
points in the same direction as v_A with a nonnegative
length; at v_A=0 it is zero. Optimizing the rotation of
each base yields a nonnegative coefficient times |v|.
Consequently the global polyconvex extension can be
chosen of the explicit form
$$
\boxed{
P(X)=\max\{p_+(|w|,d),p_-(|z|,d)\},
}
\tag{7}
$$
where p_+,p_- are finite convex functions of (r,d) in
[0,infinity) x R, nondecreasing in their first argument.
Each is a supremum of affine functions alpha+beta r+gamma d
with beta>=0 and bounded coefficients. Use bases with
det>=0 to construct p_+, and det<=0 to construct p_-.
Both families are nonempty. At a base with det>=0 the
first branch already equals F+C_R d² on B_R, and at a
base with det<=0 the second branch does. Thus in the
respective orientation each branch agrees with the whole
stabilized F, not merely the maximum, on this ball.

## 3. Unmodified integral Jensen with an explicit determinant variance cost

Let X=A+Dphi be any bounded periodic compatible gradient with
values in B_R, or any compact law in B_R with the correct
matrix and determinant moments. Its mean A also belongs to B_R.
Because det(X-A)=det X-det A-cof A:(X-A), the determinant
and matrix moments give
    int det(X-A)=0,
hence
$$
\int |z-z_A|^2=\int |w-w_A|^2
                     =\tfrac14\int|X-A|_F^2 .
$$
Integrating (3) kills the two linear terms. This gives
$$
\boxed{
\int F(X)-F(A)\ \ge\
\frac{m}{4}\int |X-A|_F^2
     - C_R\int (\det X-\det A)^2 .
}
\tag{8}
$$
This applies at EVERY base, to an arbitrary smooth strongly
RC isotropic F and every test law within the fixed radius.
Unlike the previous weighted Jensen theorem, it has
coefficient 1 for the ORIGINAL energy; the cost is a single
explicit quadratic determinant fluctuation.
In particular (8) proves the original unamplified Jensen
inequality on the entire gradient class satisfying
$$
C_R\int(\det X-\det A)^2\le \frac m4\int|X-A|_F^2 .
$$
There is no smallness assumption on the matrix amplitude
itself. For constant determinant the full nonsmooth assertion
(1) applies, and for strong RC one even obtains the larger
margin m/2 from (4) without the cross-term absorption.

The desired zero-cost result for arbitrary determinant
fluctuation is not proved. In particular (8) is a consequence
of local polyconvexification, so it holds even for abstract
minors-compatible laws; known isotropic non-PC examples
show that some genuine compatibility information beyond
those moments must still enter any complete proof.

## 4. Exact global normal-form reduction of the full general isotropic gate

The preceding compact-ball result gives a genuine reduction
of the WHOLE unrestricted isotropic problem to the following
single structural form, with one fixed coefficient on the
concave term:
$$
\boxed{
W(X)=\max\{p_+(|w|,\det X),\ p_-(|z|,\det X)\}
               -(\det X)^2 .
}
\tag{9}
$$
The two p functions are arbitrary finite convex functions
on [0,infinity) x R, nondecreasing in their modulus argument.
W must be globally rank-one convex. No bound on their
complexity, degree, or number of linear support pieces is
asserted.

**Theorem B.** The finite-valued planar isotropic Morrey
implication is true if and only if every globally rank-one
convex W of form (9) is quasiconvex.

The forward implication is immediate: the displayed form is
isotropic and finite, so the general theorem would apply.
We prove the reverse implication, taking care that the
extension retains global rank-one convexity rather than just
the compact-ball Hessian inequality.

Suppose an arbitrary finite isotropic RC F violates Jensen
at some A with a bounded test gradient in B_R, R>0.
Invariant convolution and adding a sufficiently small positive
Frobenius quadratic preserve the strict violation, by local
uniform approximation. We may therefore assume F is smooth
and uniformly strongly RC on all compact balls (indeed on
the whole matrix space). Keep the notation F for this
strictly violating approximation.

Apply Theorem A on B_S, S=5R. Choose its determinant penalty
C>=max(C_S,1) (increasing the coefficient preserves all
the support arguments, with the appropriate determinant
slope). Construct the finite globally polyconvex extension
P as in (7), agreeing with F+C det² throughout B_S.
So P-C det² equals the original F on B_S, but we do NOT
assume it rank-one convex outside that ball.

Put r=|X|_F, a=2R, b=C+1, and introduce the convex
nonnegative radial repair
$$
\rho(X)=b(r^2-a^2)_+^2.
$$
It vanishes on B_R because |X|_F<=sqrt(2)R<2R there.
For r>a its Hessian equals
    4b(r²-a²) I + 8b X tensor X.
For r>=2a=4R this is bounded below by 3b r² I.
Along a rank-one direction H the determinant is affine in
the line parameter, so
$$
D^2(C\det^2)(X)[H,H]=2C(\operatorname{cof}X:H)^2
                            \le2C r^2 |H|_F^2 .
$$
Thus rho-C det² is locally strongly rank-one convex on
r>4R, by 3b>2C. The sum with globally polyconvex P has
the same local rank-one convexity there, even if P is
nonsmooth. On r<5R the equality with F on B_S gives
P+rho-C det²=F+rho, rank-one convex. These two open sets
cover the entire matrix space. Local convexity of a
continuous restriction to each real rank-one line
implies convexity on that whole line. Hence
    G=P+rho-C det²
is globally rank-one convex and isotropic, and it agrees
exactly with the violating F on B_R.

The repair also preserves the two-branch form of P.
Indeed
    r²=4|w|²+2d=4|z|²-2d.
Add the convex functions
    b(4r_mod²+2d-a²)_+² to p_+(r_mod,d),
    b(4r_mod²-2d-a²)_+² to p_-(r_mod,d).
Each is convex and nondecreasing in r_mod>=0 by
convexity and the convex nondecreasing outer square of
the positive part. Both evaluate to the same rho on the
physical matrix variables. Thus P+rho is still of form
(7), and G/C is exactly of form (9) with rescaled convex
branches. Its rank-one convexity and its strict Jensen
violation are preserved by positive scaling.

This proves the reverse implication. The reduction works
for every original finite-valued F, not just the smooth
strongly RC class, and modifies F only outside the
test ball after the arbitrarily small strictification.
There is no use of an unproved global extension
principle for locally RC functions. QED.

## 5. Exact checks and status

The script [determinant_stabilization_exact.py](../../research/audit/determinant_stabilization_exact.py)
was actually executed in Python/SymPy. After replacing a
structural symbolic equality by expansion, it printed:

    Symbolic two-orientation profiles, lift shift, and radial repair Hessians passed.
    4050 exact rational compact-ball support controls passed for C=2517/2.

The controls use the known globally RC signed quartic
||X||_F^4-(9/4)||X||_F² det X plus ||X||_F², on a
radius-2 ball with m=2. In determinant coordinates
the two profiles are respectively
    -d²/2+7d y²+16y⁴+2d+4y²,
    17d²/2+25d y²+16y⁴+2d+4y²,
where d is the determinant of the chosen orientation and
y is the corresponding minor complex modulus.
The derivative bounds and inequality (3) are checked
with both orientations and opposite phases. These
finite controls check algebra only; the proofs above
supply the full functional quantifiers.

**Next main gate:** prove QC of (9) under its global
rank-one convexity hypothesis. The two branches are
ordinary convex functions in a modulus and the
determinant, and all possible nonconvex behavior is
confined to the one FIXED negative determinant-square
term. A proof must use actual gradient compatibility
to compensate that term, not merely correct determinant
means (which only give polyconvex Jensen). This is a
global normal-form reduction, not a bounded enumeration.
No claim of closing the general isotropic gate is made.

The key new unamplified result is (1), plus the
all-base quantitative estimate (8); the positive
polyconvexification theorem (6) and the exact global
reduction (9) isolate the missing part. The user's
signed homogeneous audit/formalization remains separate.
