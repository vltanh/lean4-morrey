# Determinant transport across spectral scales: a universal logarithmic compatibility bound and multiscale integral Jensen

24 November 2026. Positive hand theorems, independent of the candidate
signed homogeneous proof under separate audit. The target is arbitrary
finite-valued isotropic rank-one convex F on real 2x2 matrices.
**The general isotropic Morrey gate remains OPEN.**

There are two complementary advances over the preceding
[SPECTRAL_GAP_JENSEN](IWANIEC_MORREY_SPECTRAL_GAP_JENSEN.md):

* Actual gradient compatibility controls the optimal transport of
  determinant-weighted mass in logarithmic spectral scale, uniformly
  over all compactly supported gradient distributions and all bases.
  This uses the formalized truncated determinant, not just minors
  means. It yields a direct unmodified Jensen deficit estimate for
  arbitrary smooth isotropic RC integrands at rank-deficient bases.
* An explicit all-base determinant-centered transport comparison:
  each pair may use its OWN spectral radius and may have either sign
  of determinant. It includes a bounded spectral inflation cost for
  nonoverlapping intervals, then an exact variance cancellation after
  averaging on the determinant fiber of the base. At zero the best
  radius cost for each pair has a closed form.

Neither theorem claims universal zero-cost transport. The new
compatibility bound is finite, not zero; it does not yet remove the
spectral inflation cost or the missing fiber modulus for every law.
No fixed atom or wave count, exponent ladder, or unproved gradient
realization is used. The algebra checker was actually executed.
No new Lean theorem or novelty claim.

## 1. A transport estimate that uses genuine gradient compatibility

Write s(X)=||X||op, d(X)=det X, delta(X)=d(X)/s(X), with delta(0)=0.
Let nu be a compactly supported gradient law with barycenter A;
write s0=s(A), d0=d(A). Then E d=d0. Define the two finite measures
on the real logarithmic radius axis
$$
\begin{aligned}
\mu_+&=(\log s)_\#(d_+\nu)+(-d_0)_+\delta_{\log s_0},\\
\mu_-&=(\log s)_\#(d_-\nu)+(d_0)_+\delta_{\log s_0},
\end{aligned}
$$
where d_+=max(d,0), d_-=max(-d,0). Omit all zero-weight terms,
including the undefined logarithm at zero. These measures have the
same mass. They have finite first moments, since |d|<=s² and
s² |log s| is bounded near zero. Let W1 denote the UNNORMALIZED
optimal cost of coupling these equal-mass measures with cost |t-u|.
When the common mass is zero, W1=0.

**Theorem A (all-base logarithmic determinant transport).**
$$
\boxed{
W_1(\mu_+,\mu_-)\le
 \tfrac12(E s^2-s_0^2)+(\log 2)(E|d|+|d_0|).
}
\tag{1}
$$
The theorem holds for any bounded compatible periodic or affine-boundary
gradient law. More generally only the two norm inequalities and the
truncated-determinant inequalities used in the earlier affine-shell
representation are needed. There is no bound on the number of different
spectral scales and no dependence on their largest ratio.

### 1.1 Construction of all Lipschitz transport tests

Let g:R->R be any 1-Lipschitz function, alpha=log 2, and define
$$
h(t)=\int_0^\infty e^{-u}g(t+\alpha-u)\,du .
$$
The integral exists by the Lipschitz growth bound. Differentiation
of the integral after writing it as an exponential times a primitive
gives
$$
h'=g(t+\alpha)-h(t),\qquad h'+h''=g'(t+\alpha)
$$
almost everywhere for the second identity. Thus |h'|<=1 and
|h'+h''|<=1. Moreover
$$
|g(t)-h(t)|\le\int_0^\infty e^{-u}|\alpha-u|\,du
=\alpha-1+2e^{-\alpha}=\log 2.
$$
The shift alpha is the median of the unit exponential distribution,
and minimizes this particular uniform approximation error.

Consider the two isotropic nonhomogeneous integrands
$$
G_\pm(X)=\tfrac12s(X)^2\ \pm\ d(X)h(\log s(X)),
\qquad G_\pm(0)=0 .
$$
They are continuous at zero. In the notation of
[NONHOMOG_SHELL_AFFINE](IWANIEC_MORREY_NONHOMOG_SHELL_AFFINE.md),
their intercept and slope are U(s)=s²/2 and V(s)=+/-s h(log s).
Direct differentiation gives
$$
s V''(s)=\pm(h'+h'')(\log s),\qquad
V-sV'=\mp s h'(\log s).
$$
Hence U''>=s|V''| and U'>=|V-sV'|. These are the exact sufficient
conditions in the affine-shell representation theorem. They give
global QC of both G_\pm by the nonnegative integral of the
formalized truncated-determinant kernels. All its regularity and
near-zero hypotheses hold: V is locally C¹ with locally absolutely
continuous derivative on positive radii, V tends to zero, and U
is smooth. The representation uses truncation at positive radii
and locally uniform limits, so it requires no convergence of V'
at zero. No new analytic QC conjecture is assumed.

Applying Jensen to G_+ and G_- gives
$$
\left|\int h\,d(\mu_+-\mu_-)\right|
\le \tfrac12(E s^2-s_0^2).
$$
The approximation error contributes at most
(log 2)(E|d|+|d0|). Taking the supremum over 1-Lipschitz g, by the
Kantorovich--Rubinstein duality on the real line, proves (1).
Equivalently the transport is the monotone quantile coupling, and
its cost is the integral of the absolute difference of the two
tail functions. Both formulations extend to finite equal-mass
measures by scaling; the zero-mass case is immediate. QED.

At d0=0 the two measures are exactly the positive and negative
determinant masses, with no base atom. For example, for a zero-base
gradient supported on conformal and anticonformal matrices,
s²=|d| almost surely. If the determinant mass on either sign
is nonzero, (1) gives the normalized average logarithmic radius
distance at most 1+2 log 2. This is independent of scale ratios,
and does not assert that the two radius distributions are equal.

### 1.2 Unmodified Jensen bound at rank-deficient bases

Suppose F is C² isotropic and D²F[H,H]>=m||H||_F² for rank-one H
in the operator ball B_R containing the law, with m>=0. Let
f(s,t)=F(diag(s,t)), on s>=|t|, and put
$$
a(s)=f(s,0),\quad b(s)=f_t(s,0),\quad
L_R=\sup_{0<s\le R}|b'(s)-b(s)/s|.
$$
Here b(0)=0 by isotropy F(-X)=F(X), and C² gives finiteness of L_R.
The function g(log s)=b(s)/s has Lipschitz constant L_R on
(-infty,log R], by differentiation. Extend it constantly to the
right, if necessary, to apply transport duality. Rank-one convexity
along diag(s,t), strengthened by m, yields
$$
F(X)\ge a(s)+d\,g(\log s)+\tfrac m2\delta^2.
$$
The function a(s)-m s²/2 is even convex in s and nondecreasing
on s>=0, by the rank-one line diag(s,0). Since E s>=s0,
$$
E a(s)-a(s_0)\ge\tfrac m2(E s^2-s_0^2).
$$
If det A=0, a(s0)=F(A) and ||A||_F²=s0². The transport dual
inequality and the mean matrix therefore give
$$
\boxed{
E F(X)-F(A)\ \ge\ \tfrac m2 E\|X-A\|_F^2
                    -L_R W_1(\mu_+,\mu_-).
}
\tag{2}
$$
Combine (1) and (2) for a completely explicit estimate, valid
without homogeneity. In particular if L_R W1<=m E||X-A||²/2,
the original, unamplified Jensen inequality follows. At zero,
s²+delta²=||X||_F² also gives
$$
W_1\le c_* E\|X\|_F^2,\qquad
c_*=\frac{1+\sqrt{1+4(\log 2)^2}}4,
$$
by the maximum eigenvalue bound on the quadratic form
s²/2+(log 2)s|delta|. Thus the zero-base estimate closes
whenever 2 c_* L_R<=m. These are sufficient quantitative
conditions, not restrictions assumed in the general Morrey gate.

There is also a more selective version of (1): in the above
construction replace U(s)=s²/2 by
    U_g(s)=integral_0^s (s-r)|g'(log r+alpha)| dr.
Then U_g''=s|V''|, and
s h'(log s)=integral_0^s g'(log r+alpha) dr, so the angular
condition still holds. This uses only the radial curvature at the
scales where g changes. The resulting inequality is
$$
\begin{aligned}
\left|\int g\,d(\mu_+-\mu_-)\right|
\le{}&\int_0^\infty
  [E(s-r)_+-(s_0-r)_+]\,|g'(\log r+\alpha)|\,dr\\
 &+\int |g-h|\,d|\mu_+-\mu_-|.
\end{aligned}
$$
This can be used directly with the actual shell tangent slope
g of F, rather than its uniform Lipschitz constant. The nonnegative
norm gap in brackets follows from convexity of X->(||X||op-r)_+.
It does not by itself ensure that the first and second terms are
paid for by the positive parts of (2) for every RC profile.

## 2. Determinant-centered pairing for arbitrary base and law

Let nu be any compact law with the correct matrix and determinant
means, all matrices in B_R. In this section no other compatibility
assumption is needed. Put d0=det A and
$$
\nu_+=(d-d_0)_+\nu,\qquad \nu_-=(d_0-d)_+\nu .
$$
They have equal mass. Couple them by ANY finite measure pi with
these marginals. Keep the original restriction nu_0 to d=d0.
If the common mass is zero, no pairing is needed and the
constant-determinant Jensen theorem applies.

For a pair (X_+,X_-) let a=d(X_+)-d0>0, b=d0-d(X_-)>0, and set
$$
\theta=\frac b{a+b},\qquad d\lambda=(1/a+1/b)\,d\pi .
$$
Then lambda is the law of pairs with total mass 1-nu_0(matrix
space). Its marginals weighted by theta and 1-theta are the
original restrictions of nu to d>d0 and d<d0, respectively.
Indeed (1/a+1/b)theta=1/a and the reflected identity holds.
The weighted determinant of each pair is exactly d0. This is
determinant CENTERED at the base; unlike opposite-orientation
pairing, it works also for two positive or two negative determinants.

For each pair choose a measurable radius r satisfying
$$
\max(|d(X_+)|,|d(X_-)|)/R\le r\le R,\qquad r>0.
$$
Define the spectral inflation of either member by
$$
\eta_r(X)=[r^2+d(X)^2/r^2-\|X\|_F^2]_+ .
$$
Replace the pair members by
$$
Y_r(X)=
\begin{pmatrix}
r & \sqrt{[\|X\|_F^2-r^2-d(X)^2/r^2]_+}\\
0 & d(X)/r
\end{pmatrix}.
$$
Each has the same determinant and squared norm N(X)+eta_r(X).
When r is in the singular-value interval I(X)=[|delta|,s],
the inflation is zero and this is a proper-rotation equivalent
representative. Otherwise it is the diagonal matrix with first
entry r, whose larger singular value is max(r,|d|/r)<=R.
Thus ALL replacement matrices remain in B_R, even for arbitrary
scale ratios.

Form the pair mean Z=theta Y_r(X_+)+(1-theta)Y_r(X_-).
This is a rank-one averaging step (common first column),
with determinant d0 and op norm <=R. Use the original members
of nu_0 as additional output atoms. This gives a probability
law of matrices Z all on the determinant-d0 fiber, NOT a claim
that they are actual gradient fields with barycenter A.

Let j(Z) be the smaller conformal/anticonformal modulus on that
fiber, namely j(Z)=sqrt(N(Z)-2|d0|)/2. Define
$$
\bar j=E j(Z),\qquad
j_A=\sqrt{\|A\|_F^2-2|d_0|}/2,\qquad
I_{\rm cost}=\int[\theta\eta_r(X_+)+(1-\theta)\eta_r(X_-)]\,d\lambda .
$$

**Theorem B (all-base multiscale Jensen comparison).**
If I_cost=0 and bar j>=j_A, then the ORIGINAL integral Jensen
inequality holds for EVERY finite-valued isotropic RC integrand.
No smoothness or sign requirement.

If instead F is C², with lower and upper rank-one Hessian bounds
0<=m<=M on B_R, then without any assumption on these two costs,
$$
\boxed{
E F(X)-F(A)\ge \tfrac m2 E\|X-A\|_F^2
-\tfrac{M-m}{2}
\big[I_{\rm cost}+4(j_A^2-\bar j^2)_+\big].
}
\tag{3}
$$
Here pi and the radius choice are completely arbitrary, subject
only to the conditions above. Thus (3) can be optimized over a
single determinant transport coupling with pair-dependent radii.
There is no fixed-cardinality or single-shell requirement.

**Proof.** At fixed determinant d, write the energy as g_d(j),
where g_d is the even convex restriction to the shear line
z=sqrt(d)+it,w=t for d>=0, and the reflected line for d<0.
This was established in the determinant stabilization note.
For all moduli within B_R, the rank-one Hessian bounds give
4m<=g_d''<=4M. Since g_d'(0)=0, the increase under spectral
inflation is bounded by
$$
F(Y_r(X))-F(X)\le 2M[j(Y)^2-j(X)^2]
                           =\tfrac M2\eta_r(X).
$$
Rank-one strong Jensen for each pair gives
$$
\theta F(Y_+)+(1-\theta)F(Y_-)
\ge F(Z)+\tfrac m2[
\theta N(Y_+)+(1-\theta)N(Y_-)-N(Z)] .
$$
Integrate using the weighted marginals, including the unpaired
nu_0 restriction with equality. It follows that
$$
E F(X)\ge E F(Z)+\tfrac m2[E N(X)-E N(Z)]
                               -\tfrac{M-m}{2}I_{\rm cost}.
$$
All Z have determinant d0. The even function
g_d0(j)-2m j² is convex on the relevant radial range. Ordinary
Jensen on this fiber gives
$$
E F(Z)\ge g_{d_0}(\bar j)+2m(E j(Z)^2-\bar j^2).
$$
Finally
$$
g_{d_0}(\bar j)-g_{d_0}(j_A)\ge
2m(\bar j^2-j_A^2)-2(M-m)(j_A^2-\bar j^2)_+ .
$$
Use N(Z)=2|d0|+4 j(Z)² and N(A)=2|d0|+4j_A². The fiber
variance terms cancel exactly. Since E X=A, E N(X)-N(A)=
E||X-A||². This proves (3). For the nonsmooth assertion,
when inflation vanishes each pair step is ordinary rank-one
Jensen, and the final scalar function g_d0 is even convex
and nondecreasing on j>=0. This proves the asserted inequality
when bar j>=j_A. QED.

### 2.1 Optimal rank-one averaging with unmodified spectra

When the two singular-value intervals overlap, rank-one
connected representatives exist (rotate their columns to
the same value of an allowed column norm). One can maximize
the resulting fiber modulus without selecting a common radius
in advance. Let x_i,y_i be the conformal and anticonformal
moduli of each member. Set
    k=max(|x_+-x_-|,|y_+-y_-|).
The rank-one condition is equality of the two complex-coordinate
differences in modulus. Each difference can take every value
between the difference and sum of its endpoint moduli by
choosing relative phases. Therefore overlap is equivalent to
k<=min(x_++x_-,y_++y_-), and k is the minimal possible common
difference modulus for a rank-one connection. For a join with
common difference k, the squared modulus of the pair mean is
$$
j(Z)^2=\theta v_+^2+(1-\theta)v_-^2
                         -\theta(1-\theta)k^2 ,
$$
where v=y if d0>=0 and v=x if d0<0 (v_i need not be the
smaller coordinate at the input). This is the largest possible
j(Z)^2 among all rank-one joins of the given two spectra,
because the subtracted square increases with the common
difference. Independent phase rotations realize the minimum k.
These joins also remain in B_R and the same proof of (3)
applies with zero inflation for such pairs. This gives the
optimal shear budget for the two-step determinant-balanced
pair construction; no universality of that construction is
asserted.

### 2.2 Closed form for minimum pair inflation at zero

At A=0, j_A=0, so the second loss in (3) vanishes for every
choice of pair radii. The optimal inflation cost for each
pair can be computed exactly. If I(X_+) and I(X_-) intersect,
it is zero. Otherwise label them low and high, with
s_low<ell_high (ell denotes the unsigned smaller singular value).
Set u=r² and
$$
L=\max(s_{\rm low}^2,(\max_i|d_i|/R)^2),\qquad H=\ell_{\rm high}^2 .
$$
Then L<=H. The scalar function to minimize is
$$
J(u)=\theta[u+d_+^2/u-N_+]_+
     +(1-\theta)[u+d_-^2/u-N_-]_+ .
$$
On radii below the gap, increasing u toward the gap never
increases J; both summands are either decreasing or zero
there. Above the gap, decreasing u toward the gap never
increases J, by the analogous monotonicity. On the gap both
inner expressions are nonnegative, so J(u)=u+E_pair(d²)/u
-E_pair N. The optimum is at
$$
u_*=\min(H,\max(L,\sqrt{\theta d_+^2+(1-\theta)d_-^2})).
$$
At zero the weighted second moment in this formula is
|d_+ d_-|. This gives an exact pair cost, including the
bound that inflated matrices stay in B_R. Multiply it by
(1/a+1/b) and integrate against pi, then infimize over
all couplings of determinant mass. The resulting number T_R
gives the all-law estimate
$$
E F(X)-F(0)\ge \tfrac m2 E\|X\|_F^2
                              -\tfrac{M-m}{2}T_R .
$$
The cost is finite for any bounded law: choosing r equal to
the higher lower endpoint in disjoint pairs bounds each
inflation by a constant times R², and lambda is a subprobability
measure. This is a genuine multiscale improvement over requiring
one shared radius: for a mixture of arbitrarily many shells,
each with balanced determinant mass at its own radius,
T_R=0 even if no common radius exists. This conclusion extends
to rank-deficient nonzero bases when the fiber modulus budget
from the pairs suffices.

The log-transport bound (1) constrains how far determinant
mass must move between spectral scales, independently of F.
It does not control the inflation cost T_R sharply enough
to assert Jensen for every law: (3) can involve stronger
scale-ratio costs than logarithmic distance. In particular
do not equate a finite W1 bound with zero inflation, or infer
the required shear budget solely from determinant balance.

## 3. Verification and status

The script [weighted_spectral_transport_exact.py](../../research/audit/weighted_spectral_transport_exact.py)
was actually executed locally using Python/SymPy. It printed:

    Symbolic log-kernel derivatives, transport marginal/determinant identities and variance cancellation passed.
    64 exact rational pair inflation/merging controls passed.

The checks verify the algebra of the logarithmic calibration,
the centered determinant-pair weights, and the cancellation of
the intermediate variance in (3). The analytic proofs provide
the all-profile and all-law quantifiers. The numerical checks
are not a proof of a universally feasible transport plan.

**Next target:** exploit actual gradient compatibility to control
the energy-dependent cost of transporting determinant mass,
not simply its logarithmic displacement. The fixed normal form
from the determinant stabilization theorem remains open.
The work above improves the previous multiscale comparison
at ALL bases and obtains a separate, genuinely spatially
justified compatibility estimate for arbitrary laws. It does
not settle unmodified isotropic Morrey; no new Lean theorem.
