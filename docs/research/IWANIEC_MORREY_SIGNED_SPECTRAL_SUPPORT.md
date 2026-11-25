# Signed homogeneous problem: explicit spectral half-space supports for both exponent ranges

23 November 2026. Hand proof, with exact rational regression controls executed locally.
**This is an unconditional restricted Jensen theorem for all signed isotropic homogeneous integrands. It is not a solution of the full signed problem.** No novelty clearance, Lean verification, or independent human review is claimed. The theorem uses rank-one convexity directly, not the quasiconvexity of Burkholder or the 2026 truncated-determinant preprint. The earlier conditional full-gradient results in [SIGNED_SCALE_MAX](IWANIEC_MORREY_SIGNED_SCALE_MAX.md) remain applicable.

## 1. Statement

Suppose F is a finite-valued isotropic, positively p-homogeneous rank-one convex function on R^(2x2), p>1, p!=2, taking a negative value. By a reflection if needed, orient F so that the negative values occur for det<0. For A let
    sigma(A)=||A||_op, delta(A)=det A / sigma(A) for A!=0,
and put delta(0)=0. Thus delta is the signed smaller singular value. Every nonzero base A has an explicit polyaffine minorant P_A touching F at A with the following domain of validity:
$$
\begin{array}{c|c}
1<p<2 & F(X)\ge P_A(X)\quad\hbox{whenever }\delta(X)\le\sigma(A),\\
p>2 & F(X)\ge P_A(X)\quad\hbox{whenever }\delta(X)\ge-\sigma(A).
\end{array} \tag{1}
$$
In particular Jensen holds for every compact matrix law with the correct barycenter and determinant moment and supported in the indicated region. This includes all actual bounded gradient perturbations staying in that region, with no restriction on the number of waves, the gradient amplitudes, or the spatial domain.

For the previously missing signed bases (negative energy for p<2, positive energy for p>2), this shows that a counterexample must visit the **expansive opposite-energy-orientation cone**: both singular values larger than the base operator norm, with positive determinant for p<2 and negative determinant for p>2. This is a necessary condition, not a claim that these visits are impossible.

The proof also gives a homogeneous scaled extension of each support and a global quantitative lower bound on the Jensen gap (Section 6).

## 2. Profile facts and normalization

Use conformal coordinates (z,w) in C²: A acts by z times the complex input plus w times its conjugate. Write x=|z|, y=|w|, sigma=x+y, delta=x-y, d=det A=x²-y². Rank-one directions have equal lengths in the two complex coordinates.

By isotropy and homogeneity, normalize the nonzero base to E_t=diag(1,t), -1<=t<=1. Its coordinates are x0=(1+t)/2, y0=(1-t)/2. Let h(t)=F(E_t), so F(X)=sigma^p h(delta/sigma). The profile is convex and Lipschitz, including finite one-sided slopes at the endpoints, since finite-valued rank-one convex functions are locally Lipschitz. At differentiability points write H=h(t), m=h'(t). The even rank-one line (x0+i tau,y0+i tau) gives the Baker--Ericksen inequality
    C=pH-2tm>=0.
It holds with the limiting one-sided slopes at both endpoints. At t=0, h(0)>=0 follows from rank-one convexity on the rank-one line through the origin. A negative value at some t<0 implies h(-1)<0 by monotonicity along the fixed negative-determinant hyperbola. The same applies by reflection on t>0. Convexity prevents negative values on both sides. After orientation, h(-1)<0, and the endpoint Baker--Ericksen inequality gives h'_+(-1)>=-p h(-1)/2>0. Consequently all slopes m are positive.

Let a=|p-2|/p and ell(s)=H+m(s-t). The elementary signed-profile facts used here are as follows.

* For 1<p<2, ell(-a)>=0 at every nonnegative-energy base. Indeed, for t>=-a the tangent value at -a decreases with t, and at 1 it is >=0 by the endpoint slope inequality and 1+a=2/p. For t<-a with H>=0, the mirrored endpoint argument gives ell(a)>=0, and affine interpolation between t and a gives ell(-a)>=0.
* For p>2, ell(-a)>=0 at every nonpositive-energy base: the negative endpoint tangent satisfies ell_-1(-a)>=0 by h'_+(-1)>=-p h(-1)/2; then h(-a)>=0, every nonpositive-energy base has t<=-a, and tangents evaluated at -a increase with t on this range. In particular if ell(-a)<0 and H>0, then t>-a.

At an easy base ell(-a)>=0, use h>=ell to obtain the homogeneous global lower bound
$$
F(X)\ge m B_p(X)+\eta\sigma(X)^p,\qquad
B_p(X)=\sigma^p(a+\delta/\sigma),\quad
\eta=H-m(t+a)\ge0.
\tag{2}
$$
Equality holds at the base. We prove restricted supports for this bound directly, without invoking any quasiconvexity theorem.

## 3. Elementary signed Burkholder support (all base ratios)

For p<2 set
    q_B(X)=-(p-1)a+2(2-p)x+(p-1)d,
and for p>2 set
    q_B(X)=-(p-1)a+2(p-2)y+(p-1)d.
Both touch B_p on the entire normalized shell sigma=1.

For either exponent range, put
$$
K(r)=r^{p-1}-(p-1)r+(p-2).
$$
Convexity or concavity of r^(p-1) gives K>=0 for p>2, K<=0 for p<2. Direct substitution yields
$$
B_p-q_B=a(r^p+p-1)-|p-2|r+\delta K(r),\qquad r=\sigma.
$$
For p<2 and delta<=1 the minimum over allowed delta lies at min(1,r). If r<=1 the difference there is
$$
(2/p)r^p-(p-1)r^2-2(2-p)r+(p-1)a.
$$
It vanishes at 1 and its derivative is 2K(r)<=0, so is nonnegative. If r>=1 the difference is
$$
a r^p+r^{p-1}-r-a.
$$
Its value and first derivative vanish at 1 and its second derivative is
(2-p)(p-1)r^(p-3)(r-1)>=0. Thus it is nonnegative.

For p>2 and delta>=-1 the minimum lies at max(-1,-r). If r<=1 the difference is
$$
-(2/p)r^p+(p-1)r^2-2(p-2)r+(p-1)a,
$$
with derivative -2K(r)<=0 and value zero at 1. For r>=1 it is
$$
a r^p-r^{p-1}+r-a,
$$
with value and derivative zero at 1 and second derivative
(p-2)(p-1)r^(p-3)(r-1)>=0. This proves the asserted domains.

In the easy case (2), combine m q_B with the convex minorant
eta(1+p(sigma-1)) of eta sigma^p. The result has the form
$$
q(X)=\alpha+\beta |z|+\gamma |w|+c\det X,\qquad
\beta,\gamma\ge0,
\tag{3}
$$
touches at E_t, and is below F on the desired region. Replacing moduli by real parts gives an actual polyaffine support. This proof of the easy case, even at a negative-energy base, does not need the 2026 Burkholder result.

## 4. Subquadratic hard bases: the stationary scale maximum works on the negative-determinant half-space

Now 1<p<2 and ell(-a)<0. The profile facts force H<0 and t<0. At an interior differentiability point define
$$
c=\frac{(1+t)m-pH}{1-t},\qquad
\beta=\frac{2C}{1-t},\qquad
\alpha=ct-(p-1)H,\qquad
q(X)=\alpha+\beta x+cd.
\tag{4}
$$
Here c>0, beta>=0 and
$$
\alpha=-\frac{(1+t)C+(p-2)(1-t)H}{2(1-t)}<0.
$$
The equalities
$$
\alpha+\beta x_0+ct=H,\quad
p\alpha+(p-1)\beta x_0+(p-2)ct=0,\quad
\beta/2+c=m
\tag{5}
$$
are immediate by substitution. In particular q equals the tangent profile ell on sigma=1. The crucial direction parameter is
$$
\mu=\frac{(p-1)\beta}{(2-p)c}\in[0,2].
\tag{6}
$$
The upper bound is equivalent to
(p-1)C<=(2-p)((1+t)m-pH), i.e. H<=m(t+a). This is exactly the hard-case condition (including equality). The lower bound is immediate.

Consider
$$
\psi(\lambda)=\lambda^p q(X/\lambda)
=\alpha\lambda^p+\beta x\lambda^{p-1}+cd\lambda^{p-2},\quad \lambda>0.
$$
If d<0 it tends to minus infinity at BOTH ends, since p<2 and alpha<0. Thus it attains a maximum at lambda*. This works even if the maximum is negative: no nonnegativity assumption on F is needed. The stationarity equation, after subtracting (5), reads
$$
d^*=t+\mu(x^*-x_0),\qquad
x^*=x/\lambda^*,\ d^*=d/(\lambda^*)^2.
$$
Choose a rank-one line through E_t on which z moves radially and w at a fixed angle:
    z=x0+tau, w=y0+tau exp(i theta).
Its determinant slope ranges over [2t,2], since it is 2x0-2y0 cos theta. The number mu in (6) belongs to this interval. On this line the rank-one tangent at zero is
    H+(beta+c mu) tau = alpha+beta(x0+tau)+c(t+mu tau).
This follows either by the chain rule for Phi(x,y)=F(z,w) at x0,y0, or from Phi_x=beta+2c x0, Phi_y=-2c y0. Taking tau=x*-x0 gives z=x*>=0 and the required determinant d*, hence the same conformal moduli as X/lambda*. Rank-one convexity, isotropy, and homogeneity give
$$
F(X)\ge \psi(\lambda^*)\ge \psi(1)=q(X).
\tag{7}
$$
So q is a global minorant on d<0, and by continuity on d<=0. This proves in particular that EVERY missing subquadratic negative-energy base has a restricted poly-affine support throughout the orientation-reversing half-space.

We now extend this to every positive-determinant X with delta<=1, regardless of its largest singular value.

If sigma>=1 and 0<delta<=1, use the same rank-one line but choose its slope depending on X. With tau=x-x0>0 the determinant must be between t+2t tau and t+2 tau. The lower bound is 2tx-t²<0<d. The upper bound is 2x-1, and
$$
d-(2x-1)=(\sigma-1)(\delta-1)\le0.
$$
The slope therefore exists. The tangent proof gives F(X)>=q(X) at lambda=1.

If sigma<=1 and d>0, write s=delta/sigma>0, u=lambda/sigma. The derivative of psi has the sign of
$$
-k u^2+\tfrac12\mu(1+s)u-s,\qquad k=\mu x_0-t
=\mu/2+t(\mu/2-1)\ge\mu/2 .
\tag{8}
$$
Indeed divide the derivative by the positive factor
(2-p)c lambda^(p-3) sigma², using (5).
At u=1 the expression is (mu/2-1)(s-t)<=0. Its derivative with respect to u is <=0 for u>=1, since k>=mu/2 and (1+s)/2<=1. Thus psi is nonincreasing for lambda>=sigma, and
$$
q(X)=\psi(1)\le\psi(\sigma)=\sigma^p\ell(s)\le F(X).
$$
This completes the full subquadratic safe-region proof, with no upper bound on sigma outside the positive expansion cone.

## 5. Superquadratic hard bases: the complementary spectral restriction

Now p>2 and ell(-a)<0, so H>0 and t>-a. At an interior differentiability point define
$$
c=\frac{pH+(1-t)m}{1+t},\qquad
\gamma=\frac{2C}{1+t},\qquad
\alpha=ct-(p-1)H,\qquad
q(X)=\alpha+\gamma y+cd.
\tag{9}
$$
These are the hard-case coefficients from the provisional nonnegative theorem, but we do NOT assume nonnegativity. Here c>0, gamma>=0 and
$$
\alpha=-\frac{(1-t)C+(p-2)(1+t)H}{2(1+t)}<0.
$$
They satisfy
$$
\alpha+\gamma y_0+ct=H,\quad
p\alpha+(p-1)\gamma y_0+(p-2)ct=0,\quad
c-\gamma/2=m.
$$
Put
$$
b=\frac{(p-1)\gamma}{2(p-2)c},\qquad
k=b(1-t)+t=-p\alpha/((p-2)c).
$$
We have 0<=b<1, because the difference between the denominator and numerator in the expression b=(p-1)C/((p-2)(pH+(1-t)m)) is -p ell(-a)>0. Also k>0. The identity pH=gamma y0+2ct and H>0 imply b>=-t, and in fact
$$
-b(1-t)-2t\le0
$$
(with the inequality automatic for t>=0 and strict for t<0). Thus the slope -2b lies in [-2,2t].

First, F(X)>=q(X) for all X with F(X)>=0. If q(X)<=0 there is nothing to prove. Otherwise the scaled expression
$$
\psi(\lambda)=\alpha\lambda^p+\gamma y\lambda^{p-1}+cd\lambda^{p-2}
$$
has a positive maximum at lambda*>0 (it tends to 0 at zero and minus infinity at infinity). Stationarity gives
    d*=t-2b(y*-y0).
Choose the rank-one line on which w moves radially and z at a fixed angle, with determinant slope -2b. As in Section 4, its tangent is exactly q on the line, and the chosen point has the conformal moduli of X/lambda*. Homogeneity gives F(X)>=psi(lambda*)>=q(X).

Now suppose F(X)<0, and put s=delta/sigma. By Section 2, s<-a<t. For sigma<=1 the derivative of psi at lambda>=sigma has the sign of
$$
f(u,s)=-k u^2+b(1-s)u+s,\qquad u=\lambda/\sigma.
$$
At s=-1, f=-k u²+2bu-1<=0 for every u, because
k-b²=(1-b)(b+t)>=0 and k>0. At s=t, f(1,t)=0, and the derivative with respect to u at 1 is -b(1-t)-2t<=0. Thus f(u,t)<=0 for u>=1. Since f is affine in s, f(u,s)<=0 throughout [-1,t] and u>=1. We again conclude
$$
q(X)=\psi(1)\le\psi(\sigma)=\sigma^p\ell(s)\le F(X).
$$

Finally, suppose sigma>=1 and delta>=-1 while F(X)<0. Then delta=s sigma<=s<t, and tau=y-y0>0. A rank-one line with w radial has available determinant slopes [-2,2t]. The two required inequalities for its endpoint follow from
$$
d-(t-2\tau)=(\sigma-1)(\delta+1)\ge0,\qquad
d-(t+2t\tau)=(\sigma+t)(\delta-t)\le0.
$$
So an appropriate angle exists and the rank-one tangent gives F(X)>=q(X), exactly as before. This proves the entire region delta>=-1, and, in fact, also covers all nonnegative-energy matrices irrespective of delta. The exceptional sector can only consist of negative-energy matrices with delta<-1.

## 6. Endpoints, actual polyaffine supports, and the global deficit bound

For any interior nonsmooth profile point, take differentiability points tending to it. The above coefficients are continuous in (t,H,m) within each case, and h' converges to the corresponding one-sided derivative. If needed take a subsequence in a single case. At t=-1 the subquadratic hard formula has denominator 1-t, which stays away from zero; at t=1 the superquadratic hard formula has denominator 1+t, which stays away from zero. The opposite endpoints cannot be hard by the sign facts. Easy-case coefficients are bounded by Lipschitz continuity of the profile. Thus the limiting q remains a minorant on the *same fixed* safe region and touches at the limiting base. Replace |z|,|w| by their real parts in (3), (4), or (9) to obtain P, since the norm coefficients are nonnegative. At E_t there is equality. Transport by rotations and the positive scaling sigma(A) to obtain (1) at every nonzero base.

For any compact matrix law with correct minors, q itself obeys Jensen (convex norms plus determinant). Thus (1) gives the promised restricted result. This proof is a pointwise support proof, not an inference from tests of special gradient fields.

There is also an explicit global estimate with no support restriction. Normalize the base as before. Let E be the exceptional set delta>1 (p<2) or delta<-1 (p>2), respectively, and put r=|delta| on E. Then X/r is in the safe region, so
$$
F(X)\ge r^p q(X/r)\quad(X\in E).
$$
For a compact minors-compatible law nu this yields
$$
F(E_t)-\int F\,d\nu
\le \int_E\big[q(X)-r^p q(X/r)\big]_+\,d\nu(X).
\tag{10}
$$
This is uniform in the number of atoms, frequencies, and the integrand profile, once the explicit base support is fixed. A strict negative Jensen gap forces a positive measure of the exceptional set and a strictly positive integral on the right. In the superquadratic hard case, one may intersect E with {F<0}, by Section 5.

**Limit:** no argument here compensates the right side of (10) for arbitrary actual gradient laws. The signed homogeneous conjecture is still open. In particular neither the determinant null Lagrangian nor the norm convexity alone prevents excursions to the exceptional cones. The global signed task is now to control such excursions, potentially using the full family of truncated determinant inequalities L_r from the 2026 preprint. A failure of one proposed calibration is not a counterexample.

The exact regression checker [iwaniec_signed_spectral_exact.py](../../research/audit/iwaniec_signed_spectral_exact.py) was executed locally. It checked 160 rational scaling-polynomial controls, 27 rank-one interval controls, the subquadratic boundary cases mu=0,2, and superquadratic negative and positive base ratios. The analytic proof, not the finite controls, supplies all real p and profile quantifiers.
