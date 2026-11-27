# Nonhomogeneous isotropic attack: failure of unshifted shell supports and a generalized row projection theorem

23 November 2026. Hand proofs, exact rational checker executed locally.
**General isotropic Morrey remains open.** The affine-shell theorem in
[NONHOMOG_SHELL_AFFINE](IWANIEC_MORREY_NONHOMOG_SHELL_AFFINE.md)
is unaffected, but its proposed universal support property is FALSE,
even for a smooth, strictly rank-one convex, nonnegative, already
quasiconvex isotropic integrand. We give an exact three-spectral-atom
separator, then develop a more flexible positive construction using the
scalar projection theorem directly. This work does not use the candidate
signed homogeneous proof under separate audit. No new Lean verification,
independent review or priority claim.

Analytic input: the pinned lean4-iwaniec dependency at 972c0127,
[Agazzi.quasiconvex_integrandL](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Quasiconvex.lean),
and its
[scalar projection Lemma 4](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Proof/ScalarProjection/Main.lean).
The underlying theorem and lemma are from Agazzi et al.,
[arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311v2).

## 1. Exact one-sided simplification of the entire affine-shell test family

In conformal coordinates write x=|z|, y=|w|, s=x+y, delta=x-y,
D=det X=s delta. Recall the QC generators
$$
K_r^e(s,\delta)=(s-r)_+(r+e\delta),\qquad e=\pm1,\ r>0.
$$
At a base (s0,delta0), suppose a probability law of spectral pairs
satisfies E x>=x0, E y>=y0 and E D=D0.

**Lemma.** Every kernel Jensen inequality for 0<r<=s0 follows
automatically from those three conditions. For a finitely supported
spectral law, all remaining kernel tests are equivalent to checking
the finitely many radii consisting of s0 and its support radii above s0.

Indeed, when s<=r, r+e delta>=0. Thus
$$
K_r^e(s,\delta)\ge(s-r)(r+e\delta)
$$
everywhere, with equality at the base if r<=s0. Taking expectations,
subtracting the base, and using the determinant identity gives the
lower bound
$$
r(E s-s_0-e(E\delta-\delta_0))\ge0.
$$
For r>=s0 the base kernel is zero. On an interval between successive
support radii the expectation of K_r^e is a quadratic in r with
second derivative minus twice the mass above r; hence it is concave.
Its minimum is at an endpoint. Beyond the last support radius
it vanishes identically. QED.

This is an exact finite verification rule for a given finite law,
not a bound on the size of laws needed for the general Morrey problem.

## 2. Shifted truncated determinants are genuinely stronger

For r>0 write the original scaled truncated determinant in conformal
moduli as
$$
L_r(x,y)=
\begin{cases}
x^2-y^2,&x+y\le r,\\
2rx-r^2,&x+y>r.
\end{cases}
$$
Its quasiconvexity is already formalized. At fixed y it is
nondecreasing in x, and at fixed x it is nonincreasing in y.
These facts follow from the piecewise derivatives and continuity.

**Theorem A.** For EVERY r>0 and a,b>=0, the function
$$
\boxed{F_{r,a,b}(X)=L_r(|z|+a,\ \big||w|-b\big|)}
\tag{1}
$$
is globally quasiconvex, isotropic, finite and continuous.
Reflection interchanges the two moduli. There is no homogeneity
assumption or restriction on gradient amplitudes or bases.

To prove this, take all constant matrix translations having conformal
modulus a and anticonformal modulus b. The phases of the two parts
can be chosen independently. Each translated L_r is QC: simply
translate the base in its Jensen inequality. The pointwise supremum
over this compact translation orbit equals (1). In fact the two
monotonicity properties above give an upper bound by (1) via the
triangle and reverse triangle inequalities, and independent aligned
and antialigned phases attain it. A pointwise supremum of QC
integrands is QC whenever finite and measurable; here continuity
is explicit. QED.

These generators have switching boundaries
$$
x+a+|y-b|=r.
$$
Thus their radial cutoffs need not be centered at the origin in
the (x,y)-sector. In particular on the two sides of y=b they
can depend affinely on DIFFERENT signed singular variables.
This extra freedom is not present in integrals of unshifted K_r^e.

## 3. Exact obstruction to every unshifted affine-shell support

Take r=1,a=0,b=1 in (1):
$$
F(X)=L_1(x,|y-1|).
$$
At the base A=J=diag(1,-1), (s0,delta0)=(1,-1), (x0,y0)=(0,1)
and F(A)=0.

Consider the following spectral law:
| s | delta | probability | x | y | F |
| --- | --- | --- | --- | --- | --- |
| 0 | 0 | 3/8 | 0 | 0 | -1 |
| 2 | -2 | 1/2 | 0 | 2 | -1 |
| 4 | 2 | 1/8 | 3 | 1 | 5 |

Its moments are
$$
E x=3/8\ge0,\quad E y=9/8\ge1,\quad E D=-1=D_0.
$$
For radii up to 1 the lemma in Section 1 gives both kernel tests.
For 1<=r<=2 the two expected kernels are
$$
E K_r^-=(2-r)(5r+4)/8\ge0,\qquad
E K_r^+=(-5r^2+18r-8)/8\ge0.
$$
The second expression is concave with endpoint values 5/8 and 1.
For 2<=r<=4 only the last atom contributes, with
E K_r^e=(4-r)(r+2e)/8>=0.
For r>=4 both kernels vanish. This proves ALL radius inequalities
exactly, not just the finite numerical checks.

Nevertheless
$$
\boxed{E F-F(A)=-1/4.}\tag{2}
$$
The spectral law lifts to an explicit matrix law with the correct
mean A and determinant mean det A: take the zero matrix of
mass 3/8, 2J of mass 1/2, and the four diagonal matrices
with real conformal/anticonformal pairs (z,w)=(+/-3,+/-1),
each of mass 1/32. Its mean pair is (0,1), and the expected
determinant is -1. Its spectral law is precisely the table.
This is NOT an actual gradient law, because F is QC by Theorem A.

**Corollary.** For every globally RC affine-shell G lying below
F, even if the inequality G<=F is imposed only on the operator
norm ball of radius 4, we have
$$
G(A)\le E G\le E F=-1/4<F(A).
$$
The first inequality follows from the exact representation in
NONHOMOG_SHELL_AFFINE and the verified kernel tests.
The same strict gap holds for the positive-sum, supremal,
convex-nondecreasing-composition and locally-uniform-limit
closure of these generators, including all polyconvex integrands
(the lifted matrix law has the correct minors). In fact Jensen
at this one fixed law is preserved by all of those operations.

Therefore the proposed universal obstacle/minorant statement is
false. Allowing nonsmooth contact curves, arbitrary mixtures of
the two kernel orientations, noncontact intervals, or arbitrarily
fine radial scales cannot fix it. This is a no-go for that
representation, not a counterexample to any QC conjecture.

**Robustness.** The gap survives smoothing F by a small isotropic
matrix mollifier, adding a constant to make the result positive,
and adding a small strictly convex quadratic. The law is fixed,
the matrix variance is 9/2, so even before smoothing an addition
|X|_F²/36 changes the gap only by 1/8. Choose the mollifier
small enough that the remaining gap stays strict, by local
uniform continuity on the finitely many atoms and base.
Averaging translations preserves QC, and the added quadratic
makes the smooth resulting integrand uniformly strongly RC.
Thus restricting to positive smooth coercive strictly RC
integrands does not save the affine-shell support approach.
The obstruction occurs also without relying on the signed
homogeneous candidate.

## 4. Positive new analytic construction: a nonlinear projection sign

The preceding obstruction motivates returning to the *proof* of
the formalized L theorem, rather than attempting a larger radial
ODE. There is a stronger sign identity for the scalar projection
used in that proof. It is valid for arbitrary convex potentials,
not just the quadratic potential in Lemma 4.

Let Q be the unit flat torus with normalized measure. Let K be
a nonempty compact convex subset of R², p in K, and eta a
periodic Lipschitz scalar function. Let zeta be its L² projection
onto
$$
\mathcal C=\{\xi\text{ periodic Lipschitz}:
                          p+D\xi\in K\text{ a.e.}\}.
$$
Existence and the local alternative
$$
p+D\zeta=p+D\eta\quad\text{or}\quad p+D\zeta\in\partial K
\quad\text{a.e.}
\tag{3}
$$
are the formalized scalar projection lemma.

**Theorem B (nonlinear sign).** For EVERY convex C¹ function
Phi on R²,
$$
\boxed{
\int_Q \nabla\Phi(p+D\zeta)\cdot(D\eta-D\zeta)\ge0.
}\tag{4}
$$
In particular no restriction that the boundary calibration be
linear in the projected gradient is necessary.

**Proof.** First suppose Phi is smooth, uniformly convex, and
has bounded Hessian, so it has at most quadratic growth. For
tau>0 let u_tau minimize over periodic H¹ functions
$$
\frac1{2\tau}\|u-\zeta\|_{L^2}^2+
                      \int_Q\Phi(p+Du).
\tag{5}
$$
Existence and uniqueness follow from the direct method
(coercivity from uniform convexity and the L² term, weak lower
semicontinuity, and strict convexity). Its Euler equation is
$$
\frac1\tau\int_Q (u_\tau-\zeta)v
       +\int_Q\nabla\Phi(p+Du_\tau)\cdot Dv=0
$$
for all periodic H¹ test functions v; the linear growth of the
gradient of Phi justifies this differentiation.

We claim that u_tau belongs to C, even though (5) is minimized
without a constraint. This uses the scalar comparison principle,
as follows. Let R_tau f denote the same resolvent with arbitrary
periodic L² input f. If f<=g a.e., test the difference of the
two Euler equations against (R_tau f-R_tau g)_+. The monotonicity
of the gradient of Phi gives a nonnegative derivative term,
whereas the first term is at least
tau^{-1}||(R_tau f-R_tau g)_+||². The right-hand input difference
is nonpositive, so R_tau f<=R_tau g. The resolvent commutes with
translations and with addition of constants, by uniqueness and
invariance of the functional.

Write H_K(h)=sup_{a in K} a·h. Since p+D zeta is in K,
the Lipschitz affine-plus-periodic function p·x+zeta(x)
satisfies
$$
\zeta(x+h)-\zeta(x)\le H_K(h)-p\cdot h.
\tag{6}
$$
For instance mollify it: the gradients remain in K by
convexity, integrate along the segment, and pass uniformly to
the limit. Apply the order-preserving resolvent, translation
invariance and constant addition equivariance to (6). It gives
the identical difference bound for u_tau, almost everywhere,
for each fixed h. For each direction from a countable dense
subset of R² take h tending to zero along that direction in
(6) and pass to the weak derivative (or use H¹ difference
quotients in L²). Thus
(p+D u_tau)·h<=H_K(h) a.e. simultaneously for the dense
directions. Continuity in h and separation of a compact convex
set give p+D u_tau in K a.e. This also gives a W^{1,infinity}
periodic Lipschitz representative. Hence u_tau in C.

The projection variational inequality now says
$$
\int_Q(\eta-\zeta)(u_\tau-\zeta)\le0.
$$
Use v=eta-zeta in the Euler equation to deduce
$$
\int_Q\nabla\Phi(p+Du_\tau)\cdot D(\eta-\zeta)\ge0.
\tag{7}
$$
The comparison with u=zeta in (5) gives u_tau->zeta in L²,
because the gradient energy is bounded below on K. The gradients
are bounded and converge weakly in L² to D zeta. Also the
gradient energy of u_tau is at most that of zeta. Uniform
convexity gives
$$
\int\Phi(p+Du_\tau)
\ge\int\Phi(p+D\zeta)
+\int\nabla\Phi(p+D\zeta)\cdot(Du_\tau-D\zeta)
+\frac{\mu}{2}\|Du_\tau-D\zeta\|_2^2.
$$
The linear term tends to zero by weak convergence, so the
gradients converge strongly in L². The bounded Hessian
now allows passing to the limit in (7), proving (4).

Finally take an arbitrary convex C¹ Phi. Fix a closed ball
with K in its interior. The supremum of the supporting
affine functions of Phi at points in a slightly larger
closed ball is convex, globally Lipschitz, and equals Phi
on that larger ball. Its smooth convolutions have globally
bounded Hessians and their gradients converge uniformly
on K to grad Phi. Add a vanishing positive quadratic to
make them uniformly convex. Apply the preceding proof
to each and pass to the limit in (4), using bounded gradients
of eta,zeta and uniform convergence on K. QED.

Only the scalar order structure is used. This is not a claim
that such a resolvent comparison works for vector-valued maps
or arbitrary constraints in full matrix space. The new sign
extension is a hand proof independent of the homogeneous
characteristic construction.

## 5. A generalized truncated determinant for arbitrary convex row constraints

Write a,b for the two row vectors of a real 2x2 matrix.
For K as above, any convex C¹ Phi on R² and ANY real c, define
the globally convex boundary function
$$
C_{K,\Phi,c}(a,b)=\sup_{z\in\partial K}
\left[c\det(z,b)+\nabla\Phi(z)\cdot(a-z)\right].
\tag{8}
$$
Each entry of the supremum is affine in (a,b), and the
parameter set is compact, so the function is finite,
convex and continuous. Define
$$
\boxed{
L_{K,\Phi,c}(a,b)=
\begin{cases}
\max(C_{K,\Phi,c}(a,b),c\det(a,b)),&a\in K,\\
C_{K,\Phi,c}(a,b),&a\notin K.
\end{cases}}
\tag{9}
$$
The branches agree on the boundary since taking z=a there
gives c det(a,b). This also proves continuity.

**Theorem C.** Every function (9) is quasiconvex on all planar
matrices. K and Phi are completely arbitrary within the stated
hypotheses; the determinant coefficient may have either sign.

**Proof.** If its value at the base A is the convex boundary
function, ordinary convex Jensen and L>=C prove the claim.
Otherwise A has first row p in K, and its value is c det A.
For an arbitrary periodic Lipschitz two-component test,
let eta be its first component and let zeta be the scalar
projection from Section 4. Write a=p+D eta, b=A²+D phi²,
z=p+D zeta. By (3), z=a in K or z is a boundary point.
Definition (9) gives pointwise in either case
$$
L_{K,\Phi,c}(a,b)
\ge c\det(z,b)+\nabla\Phi(z)\cdot(a-z).
$$
The average of det(z,b) equals det A because (z,b) is an
actual compatible gradient with the same affine base (replace
only the first scalar potential). The average of the other
term is nonnegative by Theorem B. This gives the desired
Jensen inequality, even for c<0. QED.

For the original L take K the centered unit disk,
Phi(z)=|z|²/2 and c=1; the boundary function is the
row representation used by Agazzi. Thus (9) genuinely
generalizes that QC proof, rather than assuming a new
quasiconvexity conjecture. An arbitrary convex potential
can yield nonlinear normal slopes along a curved boundary,
with no radial scale constraint.

One may add any affine function, any convex function and
any null Lagrangian, translate the matrix, and apply
invertible left/right matrix changes; these preserve QC.
Taking the supremum or normalized average over left/right
rotations gives finite isotropic nonhomogeneous QC functions
from this entire arbitrary-shape family. For the supremum
the compact rotation group gives finite continuous values;
for the average Fubini gives the Jensen inequality.
In particular no assumed isotropy of the row constraint
or calibration potential is needed before symmetrization.

## 6. Direct application to the actual remaining problem, and limits

Theorems A--C identify a more flexible *positive* construction
than the refuted affine-shell obstacle. In particular, the
following is a sufficient global calibration certificate for
an arbitrary finite-valued RC integrand F at any base A:

Choose an affine function ell on matrices, a compact convex
row constraint K containing the first row of A, a convex C¹
potential Phi, and a real c such that
$$
\begin{aligned}
F(a,b)&\ge \ell(a,b)+c\det(a,b) &&(a\in K,\ \text{all }b),\\
F(a,b)&\ge \ell(a,b)+c\det(z,b)+
                   \nabla\Phi(z)\cdot(a-z)
                   &&(\text{all }a,b,\ z\in\partial K),\\
F(A)&=\ell(A)+c\det A.
\end{aligned}\tag{10}
$$
Then ell+L_{K,Phi,c} is a global touching QC minorant,
by (8)--(9). This follows from the generalized projection
argument rather than an unproved minor-compatible measure
realization. For isotropic F the minorant can itself be
made isotropic by taking its rotational supremum: all
rotated minorants remain below F, and the identity
rotation gives contact.

**Remaining genuine construction problem:** obtain (10),
or another touching QC minorant using this enlarged
projection family and positive sums, for arbitrary
two-variable isotropic rank-one convex F. The existence
of K,Phi in (10) is NOT asserted. In particular separate
convexity in the two rows alone does not supply the
boundary inequality for all a,b; it would be a mistake
to assume such a calibration automatically exists.

Do not return to the now-refuted unshifted affine-shell
support problem, regardless of regularity or resolution
of its differential inclusion. Do not turn the larger
kernel family into an indefinite list of fixed examples.
A future affirmative result must prove a universal
construction of QC minorants or a direct all-gradient
inequality. The present progress is an exact exclusion
of an entire failed representation plus a general
analytic extension of the available projection mechanism.

## 7. Verification

The checker
[nonhomogeneous_shifted_shell_exact.py](../../research/audit/nonhomogeneous_shifted_shell_exact.py)
was executed locally:
    Exact three-radius witness: all moments, matrix lift, shifted-L gap -1/4, kernel polynomial identities, strictification: passed

It checks rational identities for the three-radius example,
the six-atom matrix lift, and the exact kernel quadratics.
The analytic proof supplies the all-radius and all-integrand
claims; the controls are not a substitute for them.
The nonlinear sign and generalized projection proofs are
at hand-proof level. They are not yet formalized, and no
full nonhomogeneous isotropic theorem is claimed.
