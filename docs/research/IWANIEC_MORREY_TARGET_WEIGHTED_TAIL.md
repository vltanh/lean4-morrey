# Exact profile-dependent determinant-tail budget and spatially weighted entropy inequalities

24 November 2026. The general isotropic Morrey implication remains open.
This note improves the weighted spectral-transport estimate in two ways:
the first removes the log-smoothing error by using the actual curvature
of the angular supporting line; the second supplies genuinely spatial
constraints by composing with arbitrary target maps. Neither proves the
universal compensation inequality requested in the preceding note.

The results use the formalized truncated determinant L from the pinned
lean4-iwaniec dependency
[Agazzi.quasiconvex_integrandL](https://github.com/vltanh/lean4-iwaniec/blob/972c01272b2a573ae58fb43fac47c97196db2cbb/Agazzi/Quasiconvex.lean).
They do not depend on the candidate signed homogeneous theorem under
separate audit. Hand proofs, no new Lean proof, referee review, or
novelty claim. The exact symbolic checker was actually executed.

## 1. Exact curvature budget for the original arbitrary smooth F

For X write s=||X||op, delta=det X/s (zero at zero), d=s delta.
Let nu be a compact compatible gradient law with mean A, write
s0=s(A), delta0=delta(A), d0=det A, and let R bound its radii.

Define the two continuous tail functions for r>=0
$$
N(r)=E(s-r)_+-(s_0-r)_+,\qquad
T(r)=E[(s-r)_+\delta]-(s_0-r)_+\delta_0.
$$
They vanish for r>=R. Ordinary convexity gives N>=0.
The formalized truncated-determinant theorem implies Jensen for
both kernels K_r^e=(s-r)_+(r+e delta), e=+/-1. Equivalently,
$$
\boxed{|T(r)|\le rN(r).}\tag{1}
$$
We retain T itself, rather than replacing it by an estimate of the
optimal logarithmic transport distance.

Let F be any C³ isotropic rank-one-convex integrand. Define its
signed diagonal profile f(s,t)=F(diag(s,t)) for real s,t.
On the physical sector |t|<=s this is the representation of F.
Choose ANY C² path z:[0,R]->R satisfying |z(s)|<=s and
z(s0)=delta0 (when s0=0 the latter is automatic).
For example z(s)=delta0*s/s0 for s0>0, or z(s)=0 at zero.
Define
$$
V(s)=f_t(s,z(s)),\quad U(s)=f(s,z(s))-z(s)V(s),\quad
Q(s,t)=f(s,t)-U(s)-V(s)t.
$$
Rank-one convexity on the diagonal line with fixed s gives Q>=0.
Also Q(s0,delta0)=0. Isotropy implies F(-X)=F(X), so DF(0)=0.
Consequently U'(0)=0, V(0)=0. The functions U,V are C².

**Theorem A (exact original-energy identity).**
$$
\boxed{
E F(X)-F(A)=E Q(s,\delta)
 +\int_0^R [U''(r)N(r)+V''(r)T(r)]\,dr .
}\tag{2}
$$
In particular, an explicit sufficient condition for unmodified
Jensen is
$$
E Q+\int_0^R [U''-r|V''|]_+N\,dr
\ \ge\ \int_0^R [r|V''|-U'']_+N\,dr .
\tag{3}
$$
The proof of (2) is Taylor's formula with integral remainder:
for any C² scalar W, W(s)=W(0)+sW'(0)+
int_0^R (s-r)_+ W''(r)dr. Apply it first to U and then V,
multiplying the latter by delta. The constants cancel,
the U'(0), V(0) terms vanish, and the V'(0) term cancels
by E d=d0. Subtract the base value using Q(s0,delta0)=0.
This proves (2) by Fubini. Equation (1) then proves (3).

This gives an energy-dependent radial budget without replacing the
actual supporting slope by an exponential smoothing of its
logarithmic profile, without estimating its derivatives by a single
global constant, and without imposing a homogeneous degree.

At EVERY rank-deficient base the path z(s)=0 is available. Write
a(s)=f(s,0), b(s)=f_t(s,0). Then the formula becomes
$$
E F-F(A)=E[f(s,\delta)-a(s)-b(s)\delta]
 +\int_0^R [a''(r)N(r)+b''(r)T(r)]\,dr .
$$
Here a''>=0 by rank-one convexity, and the bracket outside the
integral is nonnegative. If the rank-one Hessian bound is m>0 on
B_R, that bracket is at least m delta²/2. The loss that needs
paying in (3) is the specific integral of
(r |b''(r)|-a''(r))_+ against N, not the global logarithmic
Lipschitz constant times a transport distance.

For a moving contact path, a direct derivative computation gives
$$
U''(r)+z(r)V''(r)=f_{ss}(r,z(r))
                       -f_{tt}(r,z(r))z'(r)^2 .
$$
Where N>0 write q=T/N, so |q|<=r. The integrand in (2) is
$$
N\{ f_{ss}-f_{tt}z'^2+(q-z)V''\}.
$$
This is a precise law-adapted version of the earlier contact
calibration problem, weaker than the requirement that the same
minorant satisfy the affine-shell curvature criterion for all laws.
But (1) alone is not a proof that one can choose a path making
(3) hold for every F, or that its angular remainder automatically
pays the loss. The earlier affine-shell separator at a nonzero
rank-one base rules out any universal proof based only on (1)
and the minor/norm tests. More spatial input is needed.

## 2. A direct entropy calibration, including its behavior at zero

The functions
$$
G_\pm(X)=\tfrac12s(X)^2\pm\det X\log s(X),\quad G_\pm(0)=0
\tag{4}
$$
are QC. This also follows from the previous affine-shell theorem,
but there is a short explicit representation avoiding any
differentiability assumption at zero.

For the plus sign, fix epsilon>0 and put
$$
G_\epsilon(X)=\epsilon(s-\delta)-\epsilon^2/2
 +(\log\epsilon+1)d
 +\int_\epsilon^\infty K_r^+(X)\frac{dr}{r}.
$$
The initial term epsilon(s-delta)=2 epsilon |w| is convex,
and the determinant term is a null Lagrangian. The integral is
QC by positive weights and the formalized QC of every K_r^+.
On any fixed bounded test range the integral is over a finite
interval bounded away from zero, so Fubini is immediate.
If s>=epsilon, integration gives
$$
\int_\epsilon^s (s-r)(r+\delta)\frac{dr}{r}
=(s-\epsilon)^2/2+\delta[s\log(s/\epsilon)-(s-\epsilon)],
$$
and hence G_epsilon=G_+. For s<=epsilon the integral vanishes,
and the starter and G_+ are uniformly O(epsilon²(1+|log epsilon|))
as epsilon tends to zero. Thus locally uniform convergence
proves QC of G_+. Reflecting the matrix gives G_-.

Consequently for every bounded compatible gradient law,
$$
|E(d\log s)-d_0\log s_0|\le (E s^2-s_0^2)/2,
\tag{5}
$$
using zero for a zero determinant/log product. We now use (5)
on compositions of maps to obtain information not contained
in the law of (s,delta) alone.

## 3. Spatially weighted determinant cancellation

Let u:T²->R² be ANY periodic Lipschitz map, with the torus
measure normalized to one, and X=Du. Thus the affine base is
zero. For every bounded Borel scalar q on the image of u,
$$
\boxed{\int q(u(x))\det Du(x)\,dx=0.}\tag{6}
$$
For smooth q, define the target map
S(y_1,y_2)=(int_0^(y_1) q(t,y_2)dt, y_2).
Then det DS=q, S composed with u is periodic Lipschitz, and
the determinant null-Lagrangian identity gives (6).
Approximate continuous functions on the compact image by smooth
functions uniformly. The finite signed pushforward
u_#(det Du dx) is consequently zero, so the equality extends
to bounded Borel functions. In particular the positive and
negative determinant-weighted measures have exactly the same
pushforward to the TARGET, not just the same total mass.

## 4. Arbitrary target transformations

Let T:R²->R² be any C¹ map and B(x)=DT(u(x)).
Set kappa(B)=sigma_max(B)/sigma_min(B) for invertible B.
In all products involving |det B| log kappa(B), use zero
when B is singular; this is a continuous extension on bounded
sets of matrices (a b log(a/b) tends to zero as b tends to zero,
for bounded a>=b>=0).

**Theorem B (spatial compatibility).** For EVERY such u,T,
$$
\boxed{
\left|\int \det B(x)\det Du(x)\log s(Du(x))\,dx\right|
\le \frac12\int s(B(x)Du(x))^2\,dx
 +\frac12\int |\det B(x)\det Du(x)|\log\kappa(B(x))\,dx .
}\tag{7}
$$
The left side permits a signed, spatially varying determinant
multiplier induced by an arbitrary target transformation.
No assumption of invertibility or positive determinant on T
or u is needed.

Proof: v=T composed with u is periodic Lipschitz (DT is bounded
on a compact ball containing the image), with Dv=B Du almost
everywhere by the chain rule. Apply (5) at zero to v. If B is
invertible and X=Du is nonzero,
$$
\sigma_{\min}(B)s(X)\le s(BX)\le\sigma_{\max}(B)s(X).
$$
Hence
$$
\left|\log s(BX)-\log s(X)-\tfrac12\log|\det B|\right|
 \le\tfrac12\log\kappa(B).
$$
Multiply by det B det X, integrate, and use (6) on the continuous
target function (det DT)log|det DT|, extended by zero at singular
DT. Its contribution vanishes. The last inequality and (5)
give (7). At singular B, or d(X)=0, the log products with
det(BX) vanish; the norm term is still nonnegative. All products
are integrable since the fields are bounded and a²log a tends
to zero as a tends to zero. QED.

### 4.1 Zero-distortion analytic weights

Identify the target with C. Take any holomorphic polynomial h
and choose a holomorphic primitive T, so T'=h. Then B is a
conformal matrix, det B=|h(u)|², and s(BX)=|h(u)|s(X).
There is no distortion cost. Thus (7) gives
$$
\boxed{
\left|\int |h(u)|^2\,d\log s\right|
\le\tfrac12\int |h(u)|^2 s^2 .
}\tag{8}
$$
The same proof works for any holomorphic function admitting a
primitive on a neighborhood of a ball containing the image.

The inequality holds for all such polynomials simultaneously.
By polarization one obtains the associated bilinear bound
$$
\left|\int \overline{h(u)}k(u)\,d\log s\right|
\le\tfrac12
  \left(\int |h(u)|^2s^2\right)^{1/2}
  \left(\int |k(u)|^2s^2\right)^{1/2}.
$$
Indeed the signed integral defines a Hermitian form on the
polynomials, and (8) bounds its diagonal relative to the
nonnegative norm on the right. Normalize nonzero vectors,
choose the relative complex phase so the cross term is real,
and take the difference of the diagonal bounds on their sum
and difference. Null-norm vectors have zero cross terms as
well, by scaling the same argument.

This is a target-weighted compatibility inequality, not an
unweighted spectral-law calculation. It supplies all the
holomorphic cross-moments at once. It does NOT imply that
arbitrary nonnegative target weights can be substituted in (8):
squared moduli of holomorphic functions do not give arbitrary
local weights. Formula (7) gives general target compositions
but retains their distortion cost.

## 5. Verification and exact status

The script [exact_tail_check.py](../../research/audit/exact_tail_check.py)
was run with Python and SymPy. It printed:

    Exact truncated-log identity and moving-ray derivative identity passed.
    15 exact full-moment integrated tail identities passed at signed, rank-deficient and conformal bases.

These are exact symbolic/rational checks of the algebra in (2)
and (4), not evidence of a universally feasible supporting path.
The composition theorem (7) is the analytic proof above.

No numerical inference is used to assert the general isotropic
gate. The exact radial deficit budget (2) keeps all the angular
remainder and the true signed determinant tail. The genuinely
new spatial constraints (6)--(8) go beyond those radius-only
data. We have not proved that they imply (3) for arbitrary F,
nor derived a general unmodified integral Jensen inequality.
The original determinant-square normal-form gate remains open.
No new Lean proof or assertion of solving Morrey.
