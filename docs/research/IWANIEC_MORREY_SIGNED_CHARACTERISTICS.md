# The signed homogeneous isotropic theorem: characteristic integration of truncated determinants

23 November 2026. **Candidate complete hand proof of the signed homogeneous
isotropic problem for every p>0.** The new argument below is not yet
formalized or independently refereed. It uses the already formalized
quasiconvexity of the truncated determinant L. No sign assumption remains
in the proposed theorem. Isotropy and homogeneity remain essential
hypotheses; unrestricted planar Morrey is NOT claimed.

## 0. Verified baseline and analytic input

The separate [homogeneous-isotropic branch](https://github.com/vltanh/lean4-morrey/tree/f70d7e9253ecf59ea6c862893d1fdd3fb60cffa9)
already contains Lean proofs of the nonnegative theorem for every
p>0, the signed p=2 polyconvexity theorem, the p=1 convexity theorem,
and the 0<p<1 zero theorem. In particular its
[Lean Action CI and axiom audit](https://github.com/vltanh/lean4-morrey/actions/runs/45323677832)
completed successfully at f70d7e9253ecf59ea6c862893d1fdd3fb60cffa9.
The previous research-ledger descriptions of that theorem as merely
provisional or conditional on an unformalized Burkholder result are
outdated.

The exact dependency in lake-manifest.json is lean4-iwaniec commit
972c01272b2a573ae58fb43fac47c97196db2cbb. Its
[Agazzi/Quasiconvex.lean](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Quasiconvex.lean)
contains quasiconvex_integrandL and quasiconvex_burkholderB, for the
truncated determinant and all p>1 Burkholder exponents, respectively.
These implement Theorem 1 and Corollary 2 of
[Agazzi et al., arXiv:2609.28311v2](https://arxiv.org/html/2609.28311v2).
We take those formalized theorems as the analytic input, rather than
assuming a new conjecture.

**Proposed theorem.** Every finite-valued isotropic, positively
p-homogeneous, rank-one convex integrand F on R^(2x2), for every
real p>0, is quasiconvex, with NO assumption that F>=0.

Only 1<p<2 and p>2 with a negative value require a new proof.
The main construction is a nonhomogeneous, globally quasiconvex
minorant touching F at any prescribed nonzero base. It combines
one of the previously established restricted supports with an
adaptive nonnegative integral of scaled L inequalities. The
weight is constructed explicitly by a scalar ODE on supporting
slopes. The sign of the weight follows from monotonicity of
supporting planes, not from an unproved comparison of profiles.

## 1. Coordinates, sign orientation, and the hard bases

Use conformal coordinates z,w in C²: A acts as
z times its complex input plus w times the conjugate of the input.
Write x=|z|, y=|w|, s=x+y, delta=x-y, d=x²-y²=s delta.
For A!=0 define its ratio t=d/s²=delta/s.
By isotropy and homogeneity,
$$
F(A)=s^p h(t),\qquad h(t)=F(E_t),\quad E_t=\operatorname{diag}(1,t).
$$
The profile h on [-1,1] is convex and Lipschitz: it is the
restriction of the finite convex function F(diag(1,t)) on R.
Finite-valued rank-one convex F is continuous.

At an interior t and for ANY supporting slope m in partial h(t),
put H=h(t) and C=pH-2tm. The Baker--Ericksen inequality C>=0
follows at differentiability points by considering the even
rank-one line (x0+i tau,y0+i tau), x0=(1+t)/2, y0=(1-t)/2.
Along this line determinant stays fixed and s increases.
At a nondifferentiability point take the two one-sided limits
from differentiability points; C is affine in m. The endpoint
limits give
$$
p h(1)-2h'_-(1)\ge0,\qquad
p h(-1)+2h'_+(-1)\ge0.
$$
Rank-one convexity along a rank-one line through 0 gives h(0)>=0
(F(0)=0 by homogeneity and isotropy gives F(-A)=F(A)).

A negative value for t<0 implies h(-1)<0: start the same even
rank-one line from (0,sqrt(-t)) and increase both moduli to
(x0,y0). It gives h(t)>=(-t)^(p/2)h(-1). The reflected assertion
holds on t>0. By convexity and h(0)>=0 the profile cannot take
negative values on both sides. Reflect A on the right by
diag(1,-1) if necessary. Thus assume h(-1)<0. The endpoint slope
inequality implies h'_+(-1)>=-p h(-1)/2>0. ALL supporting slopes
at interior t are therefore strictly positive.

Set e=-1 if 1<p<2 and e=+1 if p>2, and a=|p-2|/p=e(p-2)/p.
For an interior base t and slope m let
$$
g=H-(t+a)m.
$$
This is the value of the supporting line at -a.

* If g>=0, the global minorant
  m s^p(a+delta/s)+g s^p
  touches F at E_t. Its terms are the appropriate positive
  multiple/reflection of the formalized Burkholder integrand
  and a convex norm power. Thus it is QC.
* In the subquadratic case, g<0 forces t<-a and H<0.
  For t>=-a, supporting lines evaluated at -a decrease as t
  increases. Their endpoint value h(1)-(1+a)h'_-(1)>=0, since
  1+a=2/p. In particular h(-a)>=0. For t<-a, H>=0 and m>0
  would imply g>=0.
* In the superquadratic case, g<0 forces t>-a and H>0.
  For t<=-a, supporting lines evaluated at -a increase as t
  increases. The left endpoint value
  h(-1)+(1-a)h'_+(-1)>=0, since 1-a=2/p. In particular
  h(-a)>=0; strict increase of h gives H>0 when t>-a.

We need a global construction only at these hard bases g<0.

## 2. Restricted supports, including arbitrary supporting slopes

We give the details needed from the preceding
[SIGNED_SPECTRAL_SUPPORT](IWANIEC_MORREY_SIGNED_SPECTRAL_SUPPORT.md)
proof, since its hand-level validity is important to the new
argument. The stronger exceptional-cone result in that note is
not needed here.

At a hard interior base let
$$
c=\frac{e pH+(1-e t)m}{1+e t},\qquad
v=\frac{2C}{1+e t},\qquad
\alpha=ct-(p-1)H,\qquad
q(X)=\alpha+v\,r_e(X)+c\,d(X),
\tag{1}
$$
where r_e=x for e=-1 and r_e=y for e=+1. Here c>0, v>=0,
alpha<0. Indeed c>0 by the sign of H in either regime and m>0;
v>=0 by BE. For e=-1,
alpha=-[(1+t)C+(p-2)(1-t)H]/[2(1-t)]<0, and for e=+1,
alpha=-[(1-t)C+(p-2)(1+t)H]/[2(1+t)]<0.

Writing r0=(1-e t)/2 for the base modulus, the identities
$$
\begin{gathered}
q(E_t)=H,\quad c-e v/2=m,\quad
\alpha+v/2=H-tm,\\
p\alpha+(p-1)v r_0+(p-2)ct=0
\end{gathered}
\tag{2}
$$
follow by substitution.

**Lemma (the required restricted supports).**
In the subquadratic hard case q<=F on ALL matrices with d<=0
and on ALL matrices with s<=1. In the superquadratic hard
case q<=F on ALL matrices where F>=0 and on ALL matrices
with s<=1. All assertions hold for every supporting slope m
at the interior base, without differentiability of h.

### 2.1 The rank-one tangent, even at a kink of h

The function s^p[H+m(delta/s-t)] is a differentiable lower
bound of F near E_t (the two base moduli are positive),
with equality at E_t. Its differential in x,y there is
$$
u\,dx+\widetilde u\,dy,\qquad
u=pH+(1-t)m,\quad
\widetilde u=pH-(1+t)m.
$$
Restrict to ANY rank-one line through E_t. The convex
restriction of F has a differentiable lower support at the
base, so the derivative of that lower support is a supporting
slope of the convex restriction. This supplies the full
rank-one tangent inequality, also for a nondifferentiable h.
Equivalently, for e=-1, u=v+2cx0 and tilde u=-2cy0.
The rank-one line
z=x0+tau, w=y0+tau exp(i theta)
has determinant slope b in [2t,2], and its tangent inequality is
$$
F(z,w)\ge \alpha+v(x_0+\tau)+c(t+b\tau).
\tag{3}
$$
For e=+1, u=2cx0 and tilde u=v-2cy0. Use the line
w=y0+tau, z=x0+tau exp(i theta), whose determinant slope b
ranges over [-2,2t]. The same inequality holds with y0
in place of x0. These statements follow by the chain rule
for the differentiable lower bound, followed by convexity
of the restriction of F.

### 2.2 Subquadratic hard case

Put mu=(p-1)v/((2-p)c). We have 0<=mu<2: the upper inequality
is equivalent to (p-1)C<(2-p)[(1+t)m-pH]; the difference of the
right and left sides is -p g>0. Thus mu lies in [2t,2].

For d(X)<0 consider
$$
\psi(\lambda)=\lambda^p q(X/\lambda)
=\alpha\lambda^p+v x\lambda^{p-1}+cd\lambda^{p-2}.
$$
It tends to minus infinity at both ends of (0,infinity), and
therefore attains a maximum at a positive lambda*. The stationary
equation and (2) give, with x*=x/lambda*, d*=d/lambda*²,
$$
d^*=t+\mu(x^*-x_0).
$$
In (3) select slope b=mu and tau=x*-x0. The resulting z=x*>=0,
and the determinant determines the other modulus to be
y/lambda*. By isotropy this matrix has energy F(X/lambda*).
Multiplication by lambda*^p proves F(X)>=psi(lambda*)>=q(X).
Continuity includes d=0.

For d>0 and s<=1, set eta=d/s²>0, u0=lambda/s, and
k=mu x0-t>=mu/2. The sign of psi'(lambda) is the sign of
$$
-k u_0^2+\tfrac12\mu(1+\eta)u_0-\eta.
$$
This follows by dividing by the positive
(2-p)c lambda^(p-3)s² and using (2). At u0=1 its value is
(mu/2-1)(eta-t)<=0. Its derivative in u0 is nonpositive
for u0>=1 because k>=mu/2 and eta<=1.
Thus psi(1)<=psi(s)=s^p[H+m(eta-t)]<=F(X).
The case X=0 follows by continuity. This proves the lemma
in the subquadratic range.

### 2.3 Superquadratic hard case

Put b=(p-1)v/[2(p-2)c] and k=b(1-t)+t=-p alpha/[(p-2)c].
We have 0<=b<1 (the numerator/denominator difference
in the inequality is again -p g>0) and k>0.
The identity pH=v y0+2ct>0 implies b(1-t)+2t>0 and b>=-t,
so -2b lies in [-2,2t]. In particular
k-b²=(1-b)(b+t)>=0.

For F(X)>=0, if q(X)<=0 the bound is immediate.
Otherwise
psi(lambda)=alpha lambda^p+v y lambda^(p-1)+cd lambda^(p-2)
has a positive maximum at an interior lambda*, because its
limits at zero and infinity are 0 and minus infinity.
Stationarity gives d*=t-2b(y*-y0), where y*=y/lambda*.
The rank-one tangent with w radial and slope -2b gives, exactly
as above, F(X)>=psi(lambda*)>=q(X).

For F(X)<0 and s<=1, the ratio eta=d/s² lies below -a<t.
The sign of psi'(lambda) for u0=lambda/s is the sign of
$$
f(u_0,\eta)=-k u_0^2+b(1-\eta)u_0+\eta.
$$
At eta=-1 this is nonpositive for all u0, by k>=b² and k>0.
At eta=t its value at u0=1 is zero, and its derivative
there is -b(1-t)-2t<=0. The quadratic is concave in u0,
hence nonpositive for u0>=1 at eta=t. By affinity in eta,
it is nonpositive for all eta in [-1,t] and u0>=1.
Again psi(1)<=psi(s)=s^p[H+m(eta-t)]<=F(X). QED.

### 2.4 The key monotonicity consequence

By homogeneity, the corresponding support at an arbitrary
positive scale s and hard ratio t is
$$
s^p\alpha+s^{p-1}v\,r_e(X)+s^{p-2}c\,d(X).
\tag{4}
$$
It touches F at s E_t and has the same domain of validity
d<=0 (subquadratic) or F>=0 (superquadratic), respectively.

Consequently for ANY two scaled hard bases, with coordinate
pairs (r_1,d_1),(r_2,d_2) and coefficients (V_1,C_1),(V_2,C_2)
of (4), we have
$$
(V_2-V_1)(r_2-r_1)+(C_2-C_1)(d_2-d_1)\ge0.
\tag{5}
$$
Indeed both points belong to the region where both supports
are valid. Add the two supporting inequalities. This is the
monotonicity of supporting planes in two variables. It is
valid even at kinks and does not require the corresponding
two-variable function to be globally convex on an unrestricted
domain. This precise inequality is what will enforce positivity
of the scale-integration weight.

## 3. Nonnegative weight construction: follow a supporting slope

It suffices first to treat strongly convex profiles h.
For an arbitrary signed F, approximate by
F_epsilon=F+epsilon ||A||_F^p for epsilon>0 small.
This is isotropic, p-homogeneous and rank-one convex because
the added norm power is convex. It remains signed for small
epsilon if F is negative somewhere. Its profile is strongly
convex on [-1,1], because the second derivative of
(1+t²)^(p/2) is
p(1+t²)^(p/2-2)[1+(p-1)t²]>0.
Quasiconvex inequalities pass to the limit on every bounded
gradient test. Strong convexity is all that will be used:
no smoothing through the rank-one cone is required.

For a strongly convex h define, for m real,
$$
T(m)=\operatorname{argmin}_{t\in[-1,1]}(h(t)-mt),
\qquad k(m)=h(T(m))-mT(m).
$$
The minimizer is unique, T is nondecreasing and Lipschitz
(by strong monotonicity of the subgradient of the strongly
convex function on the interval, including the normal cone
at its endpoints), and k is C¹ with k'(m)=-T(m).
For the last statement, compare the minimizing values
at m and m+epsilon using each other's minimizer and
let epsilon tend to zero. Continuity of T suffices.
When T(m) is interior, m is a supporting slope at T(m).

Fix the prescribed hard interior base t0 and a supporting
slope m0 with h(t0)-(t0+a)m0<0.
Let s>=1 be the scale variable. Solve the single scalar ODE
in log s:
$$
\boxed{
\frac{dm}{d\log s}
=\frac{p[k(m)-a m]}{T(m)+e},\qquad m(1)=m_0.
}
\tag{6}
$$
Write t(s)=T(m(s)), H(s)=h(t(s)).

**Global existence in the hard region.** In the subquadratic
case t0<-a; choose a supporting slope at -a, which by strong
convexity exceeds m0. There k(m)-a m=h(-a)>=0. Between m0
and that slope take the first zero of k(m)-a m. The vector
field in (6) is locally Lipschitz near the segment up to
that zero: T stays between t0 and -a, away from either
endpoint, and T-1 stays away from zero. It points toward
the zero, and is zero there. Uniqueness prevents crossing
or reaching the equilibrium in finite log s. The solution
exists for all s>=1 and has k(m(s))-a m(s)<0 at every finite
s. (Existence follows by the usual ODE existence theorem and
continuation on this compact segment.)
In the superquadratic case t0>-a, the same proof chooses a
supporting slope at -a smaller than m0, uses the last zero
before m0, and the vector field is negative with denominator
T+1 bounded away from zero. Again the entire finite trajectory
is hard. This argument also handles a plateau of T at a kink.
No assertion of a smooth profile derivative is necessary.

At s=1 use coefficients alpha0,v0,c0 from (1) for t0,m0.
At each subsequent scale write c(t,H,m),v(t,H,m) for the
same expressions (1), and define
$$
\begin{aligned}
M(s)&=s^{p-1}m(s),\\
c_s&=s^{p-2}c(t(s),H(s),m(s)),\\
V_s&=s^{p-1}v(t(s),H(s),m(s)),\\
r_s&=s(1-e t(s))/2,\qquad d_s=s^2t(s).
\end{aligned}
$$
All these functions are locally Lipschitz. The ODE and (1),(2)
give the exact identities
$$
M'(s)=c_s,\qquad M(s)=s c_s-e V_s/2.
\tag{7}
$$
For the first, (6) gives
(p-1)m+p(k-a m)/(t+e)=c(t,H,m).
This is a direct algebraic identity for both signs of e.

Differentiate the second equation in (7) almost everywhere,
use the first, and obtain V_s'=2e s c_s'.
On the other hand (5), applied to pairs of points on this
trajectory, gives at almost every s
$$
0\le V_s' r_s'+c_s' d_s'
=c_s'(2e s r_s'+d_s')=s(t(s)+e)c_s'.
$$
Here the derivative of t(s) cancels exactly. Since t(s) is
interior, t(s)+e has sign e. Thus
$$
e c_s'\ge0\quad\text{almost everywhere}. \tag{8}
$$
This is the decisive sign theorem. It follows purely from
rank-one convexity, homogeneity and the restricted supports.

Define
$$
D(s)=e[M(s)-c_0 s]+v_0/2,\qquad s\ge1.
$$
Equations (2),(7) give D(1)=D'(1)=0 and D'=e(c_s-c0).
By (8), D' is nondecreasing. It is locally Lipschitz,
so the locally integrable weight
$$
w(s)=D''(s)=e c_s'\ge0
\quad\text{a.e.}
\tag{9}
$$
satisfies the exact reconstruction
$$
D(s)=\int_1^s(s-r)w(r)\,dr.
\tag{10}
$$
One may redefine w to be zero at points where the derivative
is undefined. The integral is over finite radii for every
fixed bounded set of matrices. No asymptotic control of w at
infinity is needed.

## 4. The truncated-determinant minorant closes both exceptional cones

For r>0 use L_r(X)=r² L(X/r), which is QC by the formalized
Agazzi theorem. In conformal coordinates it is d when
s<=r and 2rx-r² when s>r. Let J=diag(1,-1).
Define the following globally QC kernel functions:
$$
K_r^e(X)=
\begin{cases}
L_r(X)-d(X),&e=-1,\\
L_r(XJ)+d(X),&e=+1.
\end{cases}
$$
The reflection preserves QC; adding/subtracting determinant
does too, by the null-Lagrangian identity.
Both kernels have the same expression
$$
K_r^e(X)=
\begin{cases}
0,&s(X)\le r,\\
(s(X)-r)(r+e\delta(X)),&s(X)>r.
\end{cases}
\tag{11}
$$
In particular K_r^e(E_t0)=0 for every r>=1. The kernels may
take either sign; it is their nonnegative weighted Jensen
inequality, not pointwise positivity, that is important.

**Global touching minorant.** Define
$$
\boxed{
G(X)=\alpha_0+v_0 r_e(X)+c_0 d(X)
       +\int_1^\infty w(r)K_r^e(X)\,dr.
}
\tag{12}
$$
This is a globally QC function. The first terms are a convex
norm multiple plus a constant and the determinant null
Lagrangian. The integrand in the integral is QC for every r
and w>=0. On any fixed bounded matrix set the integrand is
zero for all sufficiently large r, and |K_r^e| is uniformly
bounded on the remaining compact range of r and X. Local
integrability of w thus justifies Fubini and continuity on
bounded sets, with no convergence hypothesis on its infinite
tail. In particular for any bounded periodic gradient test at
ANY base, integrate the QC inequalities. This proves QC of G.

For s<=1, (11) makes G=q_0<=F by the lemma, with equality
at E_t0. It remains to prove the global bound for all s>=1,
including the exceptional expansive matrices.

Put
$$
E(s)=\int_1^s r(s-r)w(r)\,dr
=sD(s)-2\int_1^s D(r)\,dr.
$$
The second equality follows from (10) by integration or
Fubini. Thus E'=sD'-D.
Equation (11) makes (12) at fixed s affine in delta:
$$
G(X)=I(s)+M(s)\delta(X),\qquad
I(s)=\alpha_0+v_0s/2+E(s).
\tag{13}
$$
Indeed its coefficient of delta is
c0 s-e v0/2+e D(s)=M(s). Further,
$$
I'(s)=v_0/2+sD'(s)-D(s)=e[sM'(s)-M(s)].
\tag{14}
$$
Now define the desired intercept of the evolving supporting
line by I_*(s)=s^p k(m(s)).
The envelope derivative k'=-T=-t and (6) give
$$
\begin{aligned}
I_*'(s)
&=s^{p-1}[p k(m(s))-s\,t(s)m'(s)]\\
&=e\,s^{p-1}[(p-2)m(s)+s m'(s)]
=e[s M'(s)-M(s)].
\end{aligned}
$$
In the second equality use p a=e(p-2) and
p(k-a m)=(t+e)s m'. At s=1, equation (2) gives
I(1)=alpha0+v0/2=H(1)-t0 m0=I_*(1).
Thus I=I_* at ALL s>=1. Substituting into (13) gives the
exact pointwise identity
$$
\boxed{
G(X)=s(X)^p\big[h(t(s(X)))+
 m(s(X))(\delta(X)/s(X)-t(s(X)))\big]\le F(X)
\quad(s(X)\ge1).
}
\tag{15}
$$
The inequality is convexity of h: the expression in brackets
is its supporting line with slope m(s).
This proves the global minorant without a remaining cone,
orientation, amplitude, or frequency exception.

Since G(E_t0)=F(E_t0), quasiconvexity of G yields quasiconvexity
of F at the given hard base. In particular for every bounded
periodic phi,
$$
F(E_{t_0})=G(E_{t_0})
\le\fint G(E_{t_0}+D\phi)
\le\fint F(E_{t_0}+D\phi).
$$
This is the full Jensen inequality, not an asymptotic or
small-gradient version. QED for every hard interior base.

## 5. Remove the auxiliary restrictions and assemble the theorem

The constructed G is isotropic. At any nonzero A with interior
ratio, first normalize its operator norm to one, construct G
at E_t, and use isotropy to obtain contact at the normalized A.
Rescale G by sigma(A)^p G(X/sigma(A)); this preserves QC,
the global minorant, and contact at A.
The easy bases in Section 1 already have global QC minorants.
If the negative values of F originally occur for positive
determinants, reflect with J (which preserves QC, also on the
periodic torus). Conformal and anticonformal endpoints and
A=0 follow by continuity in the base of the QC inequality
for each fixed bounded gradient, approximating by bases with
interior ratio. No assumption about endpoint differentiability
is needed.

Finally let the strong-convexity perturbation epsilon tend
to zero; on bounded sets F_epsilon converges uniformly to F.
The argument covers arbitrary finite-valued signed profiles,
including nonsmooth and affine pieces. If F is nonnegative,
use the formalized nonnegative theorem on homogeneous-isotropic.
For p=2 the formalized signed polyconvexity theorem applies;
p=1 is convex and 0<p<1 gives zero, also formalized.
This completes the proposed all-p signed theorem.

## 6. Verification, significance, and next work

The accompanying
[symbolic and exact characteristic checker](../../research/audit/iwaniec_signed_characteristic_check.py)
was actually run in Python with SymPy. It checks 14 symbolic
identities in the two regimes (jet, ODE, intercept, and
derivative cancellation), and exact piecewise-slope controls
at two kinks, one for each exponent range. The kink tests
use a determinant-power branch and an affine Burkholder
branch, verifying the sign of e M'' on an entire plateau
rather than a sample of t values. The analytic proof above,
not finite controls, gives the global theorem.

**Why this is different from the previous scale-maximal
generator route:** the weight is chosen from the actual profile
via the ODE. There is no need to show that a prescribed family
of homogeneous generators spans all signed rank-one convex
profiles, and no need to handle one exponent, one frequency
tuple, or one support size at a time. The affine line at scale
s is exactly a supporting line of h, and the derivative
cancellation in (8) ensures the coefficient of every scaled
quasiconvex truncated determinant is nonnegative.

**Formalization task:** port Sections 1--2 (arbitrary supporting
slopes and restricted supports), the strongly convex profile
regularization and scalar Legendre slope inverse, the scalar
ODE with compact invariant interval, the monotonicity
calculation (5)--(9), and the nonnegative weighted integral
identity (10)--(15) into the homogeneous-isotropic branch.
The analytic L theorem, coordinates, null Lagrangian,
profile tangents, poly-affine machinery and Burkholder
quasiconvexity already exist in the verified dependencies.
An independent logical audit of this new signed argument is
also warranted; this commit does not contain a new Lean proof.

**Status:** a complete candidate hand proof of signed isotropic
homogeneous quasiconvexity for every p>0. The preceding
nonnegative results are Lean-formalized and passed CI/axiom
audit; the signed extension is at hand-proof level.
Unrestricted planar Morrey, and removing homogeneity from
isotropic integrands, are still open. Polyconvexity in the
signed superquadratic class is false, consistent with this
quasiconvexity conclusion.
