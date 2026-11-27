# Signed isotropic homogeneous problem: new scale-maximal QC generators and precise remaining bases

23 November 2026. Hand proofs with locally executed exact rational checks.
**Conditional on Theorem 1 of Agazzi et al. (2026),
[Sharp Higher Integrability Theory, Part I, v2](https://arxiv.org/html/2609.28311v2).**
No independent human review, novelty clearance, Lean verification or
claim of the full signed theorem. We use the *truncated determinant
integrand itself*, not just the Burkholder corollary. The research
direction is signed, isotropic, positively homogeneous quasiconvexity
for all p>1 and every base, not a fixed-wave or degree hierarchy.

Notation: a matrix acts on C as zeta -> z zeta+w conjugate(zeta);
x=|z|, y=|w|, sigma=x+y=operator norm, d=det A=x²-y²,
t=d/sigma². For A nonzero, any isotropic positively p-homogeneous
F has F(A)=sigma^p h(t), h(t)=F(diag(1,t)).
The reflection A -> AJ, J=diag(1,-1), interchanges x,y and negates d,t.

## 1. Exact global signed-base coverage

For any finite-valued isotropic positively p-homogeneous rank-one
convex F, p>1, its profile is convex and locally Lipschitz (including
finite one-sided endpoint slopes). It satisfies the Baker--Ericksen
inequality
    p h(t)-2t h'(t)>=0,
with the corresponding one-sided inequalities at t=+/-1.
The proof by an even rank-one line in conformal coordinates is in
[the main p>=2 note](IWANIEC_MORREY_PGE2_POLYCONVEXITY.md).
In particular h(0)>=0 by rank-one convexity on a line through 0.
A negative value on t<0 forces h(-1)<0: along a fixed negative
determinant hyperbola the conformal/anticonformal endpoint minimizes
F, giving h(t)>=(-t)^(p/2) h(-1). The positive-side mirror is identical.
By convexity there cannot be negative values on both sides.
If h(-1)<0, the endpoint slope bound gives
h'_+(-1)>=-p h(-1)/2>0; hence h is strictly increasing.

Let a=|p-2|/p. The Burkholder profile a+t and its reflection are
quasiconvex by Corollary 2 of the cited preprint, or the scale
integrals below. Any supporting affine profile ell(s)=c+ms
with ell(-a),ell(a)>=0 is a nonnegative linear combination of
a+s and a-s, hence provides a global quasiconvex lower support
touching F at the base defining ell. This observation is independent
of the sign of F away from that base.

**Subquadratic signed theorem (new base coverage).**
For 1<p<2, every signed isotropic p-homogeneous rank-one convex F
is quasiconvex at *every* matrix where F(A)>=0, including A=0.
In particular if F is negative on the left, any still-unproved
base has t<-a and h(t)<0.

Proof: let ell_t be the tangent at t, using a one-sided derivative
where necessary. For t>=-a, the function ell_t(-a) is nonincreasing
in t by convexity, and
ell_1(-a)=h(1)-(1+a)h'_-(1)>=0 since 1+a=2/p.
Similarly ell_t(a)>=0 whenever t<=a by the mirrored endpoint
argument. If t<-a and h(t)>=0, then -a lies between t and a,
and ell_t(-a)>=0 by affine interpolation. For t>a use the
mirror. This proves both required inequalities at every h(t)>=0.
At t=0 they hold because h(0)>=0, so the homogeneous support
through that ray also touches F at the zero matrix. It follows
as well that h(-a),h(a)>=0 even without a sign condition.
QED.

**Superquadratic signed base coverage (including all zero bases).**
For p>2, orient a sign-changing profile so h(-1)<0.
Put k=p|h(-1)|/2. Convexity and the endpoint slope inequality give
h(s)>=k(a+s) for all s. Hence F is quasiconvex at A=0, and
h(t)<=0 implies t<=-a. For t<=-a the tangent evaluated at -a
is at least ell_-1(-a)>=0 (tangents move upwards at any point
to their right); its slope is positive, so ell_t(a)>=0 too.
Thus all nonpositive-energy bases are covered, and all remaining
positive-energy bases with ell_t(-a)>=0 are also covered.
With this orientation the missing bases are precisely the ones
not covered by the tangent-support argument, h(t)>0 and
ell_t(-a)<0 (the derivative is positive). No claim that those
bases actually violate quasiconvexity is made.

The already established p=2 hand proof allows arbitrary sign;
p=1 is classical convexity under isotropy; for 0<p<1 any
finite-valued rank-one convex positively p-homogeneous function
is zero: its convex restriction to every rank-one line has
sublinear growth in both directions. Thus there is no exponent
ladder below 1.

## 2. New mechanism: take maxima BEFORE integrating scales

The cited Theorem 1 asserts that the following L is quasiconvex:
    L(A)=det A if sigma<=1, and L(A)=2x-1 if sigma>1.
For r>0 put L_r(A)=r² L(A/r); equivalently
    L_r(A)=d if sigma<=r, and 2rx-r² if sigma>r.
Write L_r^-(A)=L_r(AJ), which equals -d inside and 2ry-r² outside.

Let g be ANY finite continuous convex isotropic function on matrices,
with at most linear absolute growth, and g(0)<0. The following
functions are globally quasiconvex, isotropic, and positively
p-homogeneous:
$$
\begin{aligned}
G_{p,g}^{<}(A)
&=(p-1)(2-p)\int_0^\infty
r^{p-3}\max\{L_r(A),r^2 g(A/r)\}\,dr,\qquad 1<p<2,\\
G_{p,g}^{>}(A)
&=(p-1)(p-2)\int_0^\infty
r^{p-3}\left[d+\max\{L_r^-(A),r^2 g(A/r)\}\right]\,dr,
\qquad p>2 .
\end{aligned}
\tag{1}
$$
One may also use finite maxima of the convex competitors, or
nonnegative sums and finite pointwise suprema of the resulting
homogeneous integrands when these remain finite. There is no
restriction on the size of the affine base or test gradient.

**Proof.** For each r, a maximum of quasiconvex integrands is
quasiconvex; the scaled convex competitor is quasiconvex, and in
the second formula adding the determinant is permitted because
it is a null Lagrangian. For completeness convergence and
integration of the inequalities require no sign assumption on
the integrands. On every fixed matrix ball and for small r,
the maximum in either formula is O(r+r²), uniformly, since
g has at most linear growth. The first integral therefore
converges near zero for p>1. The second also has the bounded
determinant term and converges there for p>2. For sufficiently
large r (uniformly on a fixed ball), sigma<=r and
r²g(A/r) <= -epsilon r² < -|d| for some epsilon>0.
Thus the first integrand inside the weight is exactly d at
large r, integrable since p<2; the second is zero there.
This supplies an absolute integrable majorant for bounded
gradients and bases, justifying Fubini of each quasiconvexity
inequality and continuity. Homogeneity follows from r=lambda s
in the scale integral, giving the factor lambda^p, and isotropy
is immediate. QED.

Without the convex competitor, the first and second integrals
give exactly the normalized Burkholder integrand sigma^p(a+t):
split at r=sigma, integrate the affine-in-r and constant
pieces, and multiply by the displayed normalizing constants.
Taking maxima AFTER these integrals merely gives the usual
Burkholder generator cone. Taking them BEFORE integration can
give strictly new profiles. In particular a convex competitor
can be inactive on an entire prescribed cone yet active on
another sector, so we need not add a positive homogeneous
integrand on the negative-energy cone.

## 3. For EVERY p>2: exact Burkholder extensions on a prescribed cone

Fix b in (0,1), and choose g(A)=2b x-1, convex since x is
the norm of the conformal projection. Put c=(1-b)/(1+b).
Then the new function in (1) has the explicit signed profile
$$
h_b(t)=
\begin{cases}
a+t,& -1\le t\le c,\\
s(t)^{p-2}\big[t+a s(t)^2\big],&c<t\le1,
\end{cases}
\quad
s(t)=\frac{b(1+t)}2+\sqrt{\frac{b^2(1+t)^2}{4}+t}.
\tag{2}
$$
In particular h_b(-1)=a-1<0 and h_b(t)>a+t for every t>c.
This proves quasiconvexity for an explicit signed family for
every exponent p>2 with an arbitrary transition point c in (0,1),
at ALL bases. Reflection gives the other orientation.

Proof: by homogeneity assume sigma=1. If b x<=y, then
2br x-r²<=2r y-r²<=L_r^-(A) for all r. The last inequality
inside r>=1 follows from
-d-(2ry-r²)=(r-1)(r+t)>=0.
Hence the baseline is unchanged. If b x>y, then t>c>0.
For r<1 the competitor strictly dominates the outside piece.
For r>=1, it dominates -d exactly up to the unique positive
root s=b x+sqrt(b²x²+d)>1 of d+2br x-r²=0.
The integrand in (1) is thus d+2br x-r² on [0,s], and
zero thereafter. Integration gives
$$
(p-1)(p-2)\left(\frac{d\,s^{p-2}}{p-2}
+\frac{2b x\,s^{p-1}}{p-1}-\frac{s^p}{p}\right)
=s^{p-2}(d+a s^2),
$$
using the defining quadratic for s. Strict increase over the
baseline follows already from strict domination on (0,1).
QED.

This directly addresses the obstruction in
[BURKHOLDER_CONE_LIMITS](IWANIEC_MORREY_BURKHOLDER_CONE_LIMITS.md):
signed integrands that agree with Burkholder on a cone but rise
outside cannot in general be supported using just polyconvex
additions to the known homogeneous Burkholder function.
Here (2) is an actual quasiconvex extension with exactly that
previously problematic geometry, rather than a conjecture or
numerically sampled RC spline. For example p=4,b=5/12 gives
c=7/17 and h_b(1)=153/32, compared with the Burkholder value 3/2.
It is important not to claim that every RC extension of
Burkholder on that cone has the form (2).

## 4. For EVERY 1<p<2: exact generators reaching previously open negative bases

Choose g(A)=-c with c in (0,1). Then (1) gives a signed
quasiconvex clipped-scale profile
$$
h_c(t)=
\begin{cases}
a+t,& t\ge-c,\\[2pt]
\displaystyle
a\,\frac{(1+t)^p}{(1-c)^{p-1}}
-(1-a)c^{1-p/2}(-t)^{p/2},
&-1\le t<-c ,
\end{cases}
\tag{3}
$$
where a=(2-p)/p. The new term is obtained by clipping the
negative tail of L_r at -c r², NOT clipping the final
homogeneous integrand at zero. The result remains signed.

Proof: take sigma=1. For t>=-c no clipping is active, since
L_r+c r²>=0 for all r (check r<=1 and r>=1 separately).
For t<-c the maximum equals L_r on [0,r0], the constant
- c r² on [r0,r1], and d on [r1,infinity), where
r0=(1+t)/(1-c)<1 and r1=sqrt(-t/c)>1.
The weighted integral is
$$
\frac{(1+t)^p}{p(p-1)(1-c)^{p-1}}
-\frac{2c^{1-p/2}(-t)^{p/2}}{p(2-p)}.
$$
Indeed the first term integrates the positive excess
L_r+c r² on [0,r0], and the second sums the integral
of -c r² up to r1 and of t beyond r1.
Multiplication by (p-1)(2-p) gives (3). QED.

In particular h_c(-1)=-(1-a)c^{1-p/2}<0 and
h'_c(-1)=-(p/2)h_c(-1). Its unique one-sided tangent at -1
satisfies
$$
\ell_{-1}(-a)=h_c(-1)+h'_c(-1)(1-a)
=(2-p)h_c(-1)<0.
$$
Consequently *no affine Burkholder-type lower support*
with c0>=a|m| can touch this generator at its negative
conformal base. More generally the strict inequality of
tangents persists near -1. The endpoint assertion about
absence of an affine support uses that a supporting affine
line at the left endpoint must have slope at most the
right derivative; a smaller slope only decreases its value
at -a. Nevertheless the entire function is quasiconvex by
(1). Thus (3) actually covers negative-energy bases beyond
the previous method for every subquadratic exponent.
For p=3/2 and c=1/16 the negative endpoint value is -1/3,
its derivative is 1/4, and the tangent gap at -a=-1/3
is -1/6, exactly.

## 5. Verification and next research target

The standard-library checker
[research/audit/iwaniec_signed_scale_exact.py](../../research/audit/iwaniec_signed_scale_exact.py)
was executed in the working container with Python 3:
    Exact signed-scale checks passed: p=3/2 clipping and negative tangent gap -1/6; p=4,6,8 active radii and integral identities.

This verifies explicit rational controls and integrations
at rational radii; the hand proofs, not these controls,
give all real exponent and parameter quantifiers.

The positive advance is the new global QC mechanism (1),
not an equivalent reformulation of Morrey. It yields
signed profiles inaccessible to the former affine support
argument, and for p>2 it realizes the previously missing
Burkholder-cone extensions. But it is **not a proof that
an arbitrary signed rank-one convex profile is in the
supremal/positive closure of this new family**, nor that
such a representation must hold. In particular (2) and
(3) are proved examples, not an exhaustive classification.

**Next main task:** for an arbitrary signed homogeneous
rank-one convex profile, construct a lower support from
(1), or prove a direct Jensen inequality, at every missing
base in Section 1. The new degree of freedom is the
convex competitor g inside the scale maximum. A support
must touch F and lie below it globally, not merely pass
a finite profile grid. No fixed-exponent, fixed-wave,
martingale-trap or atom-count hierarchy is needed for the
proposed attack. If (1) is not universal, do not interpret
failure of its representation as failure of quasiconvexity.

**Status:** signed p<2 nonnegative-energy bases closed,
signed p>2 nonpositive-energy bases closed (conditional on
the cited 2026 input); arbitrary opposite-sign bases still
open. The already provisional nonnegative homogeneous
isotropic theorem is unchanged. Unrestricted Morrey is open.
