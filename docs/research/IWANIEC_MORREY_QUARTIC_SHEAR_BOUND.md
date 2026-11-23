# Uniform shear bound and the entire high-coupling isotropic quartic cone

Date: 23 November 2026. **Evidence:** direct rank-one shear argument,
exact invariant polynomial algebra, and the classical polyconvex
Dacorogna–Marcellini endpoint. Not Lean-checked or externally reviewed;
do not claim publication novelty. This is a global positive result for
an infinite parameter class, **not** the full p>2 Guerra–Kristensen
question.

## Theorem (necessary bounds for ALL isotropic quartic polynomial integrands)

Let
\[
  s(A)=\|A\|_F^2,\quad d(A)=\det A,\qquad
  F(A)=a\,s(A)^2+b\,s(A)d(A)+c\,d(A)^2
\]
with real a,b,c. Every SO(2)×SO(2)-invariant
homogeneous quartic polynomial has precisely this form.
If F is globally rank-one convex on real 2×2 matrices, then

\[
\boxed{\quad a\ge0,\qquad |b|\le4a.\quad} \tag{1}
\]

If a>0, then in addition
\[
\boxed{\quad c\ge\frac{3b^2}{8a}-2a.\quad} \tag{2}
\]
If a=0, rank-one convexity forces b=0 and c≥0, and F
is polyconvex.

**Proof of (1).** On the rank-one ray \(A=tE_{11}\),
\(F(A)=at^4\), hence rank-one convexity forces a≥0.
Take the rank-one shear H=E₁₂. At I+tH we have
s=2+t² and d=1, so the second derivative at t=0
is \(8a+2b\ge0\). At D+tH, D=diag(1,-1), the
determinant is -1 and the second derivative is
\(8a-2b\ge0\). Thus |b|≤4a. If a=0 then b=0;
restricting \(c\,d^2\) to the rank-one line
diag(1,t) forces c≥0.

**Proof of (2).** For
\(h(r)=F(\operatorname{diag}(1,r))\), rank-one convexity
implies ordinary convexity on the entire interval
[-1,1]. Direct differentiation gives
\[
h''(r)=4a+12ar^2+6br+2c
=12a\left(r+\frac b{4a}\right)^2+
4a+2c-\frac{3b^2}{4a}.
\]
Because |b|≤4a, its minimum occurs at
r=−b/(4a) inside [-1,1]. Nonnegativity of
h'' there gives (2). **These are necessary
constraints; they are not claimed sufficient
for global rank-one convexity.**

## The entire high-coupling sector is polyconvex

Assume in addition F≥0 globally and
\[
                 a>0,\qquad 2a\le |b|\le4a .
\]
Let \(g=|b|/(2a)\in[1,2]\) and
\(e=-\mathrm{sign}(b)\in\{-1,1\}\), so that
\(b=-2eag\).

**Theorem.** In this *entire sector*,
\[
\boxed{
 F\ge0 \ \Longleftrightarrow\
 c\ge2|b|-4a
 \ \Longrightarrow\ F\text{ is globally polyconvex}.
}                                                         \tag{3}
\]

Necessity of the scalar bound follows by evaluating
F at I if e=1 or D if e=-1: at the corresponding
conformal matrix, s=2,d=e, and
\(F=4a-2|b|+c\).

For sufficiency and global polyconvexity, put
\[
 Q_e(A)=s(s-2ed),\quad R_e(A)=(s-2ed)^2,\quad D_2(A)=d^2.
\]
The quartic Q_e is a *known globally polyconvex*
Dacorogna–Marcellini endpoint (see Rindler,
Introduction to the Modern Calculus of Variations,
Example 4.2). The quadratic \(s-2ed\) is
a nonnegative sum of two squares of linear matrix
entries, so its square R_e is **convex**.
D₂ is **polyconvex**.

The following identity is exact:
\[
\boxed{
 F=a(2-g)Q_e+a(g-1)R_e+
       [c-4a(g-1)]\,D_2 .
}                                                         \tag{4}
\]
Every coefficient is nonnegative because
1≤g≤2 and \(c\ge4a(g-1)=2|b|-4a\).
Thus F is polyconvex and nonnegative everywhere.
This proves the equivalence and implication in (3).

There is **no need to handle any \(g>2\) case**:
the global rank-one shear inequalities (1) show
that such coefficients cannot be rank-one convex.

## Uniform power extension

For every real p≥4,
\[
                  F_p(A)=F(A)^{p/4}
\]
is a finite, nonnegative, isotropic, positively
p-homogeneous, globally **polyconvex** integrand
for each F in (3). Indeed a polyconvex
representative G(A,z), convex in (A,z), can be
composed with the convex nondecreasing function
\(x\mapsto(x_+)^{p/4}\).
This covers the entire continuum p≥4,
not just integer degrees or fixed tests.

## The remaining low-coupling sector

Only \(|b|<2a\) remains for an attempt to prove
global PC of **all nonnegative isotropic RC
quartic polynomials** by these elementary
coefficient arguments. Conditions (1)–(2)
and nonnegativity are necessary but the
decompositions above are not yet known to
cover this whole low-coupling region.

More importantly, even a complete quartic
classification would still be a **restricted
polynomial result**; it does not settle
arbitrary p>2 nonpolynomial isotropic
rank-one-convex integrands.

The earlier [quartic stabilization note](IWANIEC_MORREY_QUARTIC_STABILIZATION.md)
proved polyconvexity under 1≤g≤2; the substantive
new bookkeeping here is that **rank-one
convexity itself rules out g>2**, and
therefore closes the entire allowed
nonnegative high-coupling sector.
The necessary parabolic bound (2)
excludes another global coefficient
region without arbitrary finite searches.
