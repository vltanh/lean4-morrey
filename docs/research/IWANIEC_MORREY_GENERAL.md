# Toward unrestricted planar Morrey: a hybrid Burkholder–polyconvex support hierarchy

Research date: 22 November 2026. **Status:** new mathematical hand deductions, an
independently checked exact example, and open universal gates. None of the new claims
has been formalized in Lean or independently refereed. The claims using global
Burkholder quasiconvexity are **conditional on** Agazzi et al.,
[arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311v2), Corollary 2.
No general 2×2 rank-one-convex→quasiconvex proof or counterexample is claimed.

This note extends [the p<2 proof](IWANIEC_MORREY_UNIVERSAL.md) to a useful
all-p certificate scheme, explains **why a single certificate type fails for
p>2**, derives a global quasiconvex *envelope lower bound*, and records
what is and is not transferred to nonisotropic/nonhomogeneous integrands.
The goal is one global cone-completeness gate, **not** to close finitely
many special p or a fixed degree.

## 1. Signed-singular one-variable reduction

Fix p>2 and define q=p/2>1 and \(\kappa=1-2/p=1-1/q>0\).
Let \(F:\mathbb R^{2\times2}\to[0,\infty)\) be finite-valued,
SO(2)×SO(2)-invariant, positively p-homogeneous and rank-one convex.
For \(A\ne0\), let \(a=\|A\|_{\rm op}\) and
\(r=\det A/a^2\in[-1,1]\). Signed SVD yields

\[
 F(A)=a^p h(r),\quad h(r):=F(\operatorname{diag}(1,r)).
 \tag{1}
\]

The profile \(h:[-1,1]\to[0,\infty)\) is convex because its
diagonal slice is a rank-one line. The p<2 theorem works because
**every** supporting affine line to h lies in a certain
two-generator quasiconvex cone. At p>2 this implication fails:
for \(h(r)=(r_+)^q\) the tangent has a negative intercept,
although \((\det A)_+^q\) is polyconvex.

## 2. Two quasiconvex generators for every p>2

Define for \(A\ne0\)

\[
 B_p^{\pm}(A)=a^p(\kappa\pm r)
             =\kappa a^p\pm a^{p-2}\det A,\qquad B_p^{\pm}(0)=0.
 \tag{2}
\]

For p≥2, the Burkholder integrand \(B_p^{2026}\) in the 2026
paper obeys \(B_p^{2026}=(p/2)B_p^-\); reflection by
\(D=\operatorname{diag}(1,-1)\) swaps B_p^- and B_p^+.
Therefore **both** \(B_p^\pm\) are globally quasiconvex,
assuming Corollary 2 of that preprint.

For every \(c\ge0\) and \(m\in\mathbb R\), define

\[
 P_{c,m,q}(A)=(c\,a^2+m\det A)_+^q.
 \tag{3}
\]

This is **polyconvex unconditionally**: its representative
\((X,d)\mapsto(c\|X\|_{\rm op}^2+md)_+^q\)
is convex, since \(c\|X\|_{\rm op}^2+md\)
is convex and \(t\mapsto(t_+)^q\) is convex nondecreasing.
The formula makes sense for all p>2, not only even integers.
Every nonnegative linear combination or finite pointwise
maximum of these building blocks is quasiconvex.

## 3. A canonical one-dimensional certificate envelope (new deduction)

Let \(\mathcal C_p\) be the set of finite profile sums

\[
 g(r)=\alpha(\kappa+r)+\beta(\kappa-r)
       +\sum_{j=1}^N\gamma_j(c_j+m_jr)_+^q
 \tag{4}
\]

where \(N\ge0\), \(\alpha,\beta,\gamma_j,c_j\ge0\)
and \(m_j\in\mathbb R\). The empty sum and zero function
are permitted. Every \(g\in\mathcal C_p\) defines a
globally quasiconvex, isotropic, p-homogeneous matrix
integrand \(G(A)=a^pg(r)\).

For any nonnegative profile h define

\[
 (\mathcal E_p h)(r)
 =\sup\{g(r):g\in\mathcal C_p,\ g(t)\le h(t)
                          \text{ for every }t\in[-1,1]\}.
 \tag{5}
\]

Then \(0\le\mathcal E_ph\le h\). Define \(\widehat F(0)=0\) and
\(\widehat F(A)=a^p(\mathcal E_ph)(r)\) for \(A\ne0\).

**Theorem 3.1 (conditional on Burkholder).**
\[
\boxed{\widehat F \text{ is globally quasiconvex},\qquad
       0\le\widehat F\le F.}                             \tag{6}
\]
Consequently, for **every** base \(A\), every admissible
periodic or zero-boundary gradient field, and every p>2,

\[
 \fint_QF(A+D\varphi)\,dx
 \ge\widehat F(A)
 =a^p(\mathcal E_ph)(r),                                \tag{7}
\]
and the maximum possible Jensen deficit obeys
\[
 0\le F(A)-QF(A)\le
 a^p\big[h(r)-(\mathcal E_ph)(r)\big].                    \tag{8}
\]

Here \(QF\) is the quasiconvex envelope at A defined
by the infimum over admissible gradients, *not* the
quadratic form notation.

**Proof.** By (2)–(3), each profile g gives a quasiconvex
matrix G. The global constraint g≤h is exactly G≤F.
The pointwise supremum of any family of quasiconvex
integrands is quasiconvex whenever it is finite and
locally bounded: at each A and each test field,
\(G(A)\le\fint G(A+D\varphi)\le
\fint\sup_GG(A+D\varphi)\), and take the supremum
over G at the left. Since \(0\le\widehat F\le F\)
and F is continuous and finite, \(\widehat F\)
is locally bounded and measurable. Therefore the argument
applies and proves (6)–(8). QED.

**Update (22 November 2026): THIS COMPLETENESS GATE IS FALSE.** The [exact p=4 global no-go](IWANIEC_MORREY_HYBRID_NOGO.md) constructs a nonnegative isotropic globally rank-one-convex profile h for which the envelope at r=0 lies a strictly positive exact rational amount below h(0). The certificate is checked by rational Bernstein positivity. The scalar envelope remains a sound lower bound, but **not a complete certificate hierarchy**. The following paragraph records the original target for historical clarity.

The **single scalar completeness gate** for this method is

\[
 \forall p>2,\ \forall h \text{ arising from a nonnegative isotropic
 RC p-hom F},\qquad \mathcal E_ph=h.                   \tag{G_p}
\]

Had this gate been true, it would have settled the whole p>2 isotropic class. It is now **REFUTED** for the specified generator family by the exact p=4 no-go; this does not refute Morrey.

## 4. Two closed-form pointwise acceptance tests

Let \(r_0\in(-1,1)\).

**Burkholder-line test (uses Iwaniec 2026).**
If \(m\in\partial h(r_0)\) and
\[
c=h(r_0)-r_0m\ge\kappa |m|,                              \tag{9}
\]
then
\(\alpha=\tfrac12(c/\kappa+m)\),
\(\beta=\tfrac12(c/\kappa-m)\) are nonnegative;
\(g(r)=\alpha(\kappa+r)+\beta(\kappa-r)=c+mr\)
lies below h and touches at r₀. Hence
\(\mathcal E_ph(r_0)=h(r_0)\) and F is quasiconvex
at **every** A with ratio r₀. This is a genuinely
nonconformal statement, universal over F.

**Convex-root test (does NOT use Iwaniec 2026).**
If \(h(r_0)=0\), the zero function already touches.
Otherwise let \(v=h^{1/q}\).
If there is an affine support \(\ell(r)=c+mr\)
with \(c\ge0\), \(\ell\le v\) on [-1,1], and
\(\ell(r_0)=v(r_0)>0\), then
\(g(r)=(c+mr)_+^q\le h(r)\)
touches at r₀ and produces a **polyconvex**
support for F at the base.

A convenient **all-r C² sufficient criterion** for
globally polyconvex F is, when h>0:
\[
 h h''\ge(1-2/p)(h')^2,\qquad
 (p/2)h-rh'\ge0 \quad(-1<r<1),                           \tag{10}
\]
together with the corresponding endpoint/support limits.
Indeed the first inequality makes \(v=h^{2/p}\)
convex; the second makes the intercept
\(v-rv'\) nonnegative. Its tangent support at each
r lifts to \(P_{c,m,q}\), so (6) gives global
polyconvexity; directly, the supremum of the convex
minor extensions remains convex. The second inequality
is closely related to the 2D Baker–Ericksen
monotonicity in Guerra–Kristensen (2022).

In particular, for p=2 the root is h itself;
rank-one convexity yields h convex, and the
endpoint-slope argument in the earlier note gives
nonnegative intercepts, recovering the proposed
global polyconvexity result for nonnegative isotropic
2-homogeneous F. The p=2 proof is logically separate
from the p>2 conditional result.

## 5. An exact example showing the OR of the two tests is NOT complete

Take p=6, q=3, \(\kappa=2/3\), and

\[
 h(r)=1+r+(1+r)^3,\qquad r\in[-1,1].
 \tag{11}
\]

The corresponding matrix function is

\[
 F(A)=\|A\|_{\rm op}^6+\|A\|_{\rm op}^4\det A
              +(\|A\|_{\rm op}^2+\det A)^3.
 \tag{12}
\]

Since \(\|A\|_{\rm op}^2+\det A\ge0\),
the last term is the polyconvex generator
\(P_{1,1,3}\). The first two terms decompose exactly as

\[
 1+r=\frac54(\frac23+r)+\frac14(\frac23-r),
\]
so the whole function is a nonnegative combination
of the generators (2)–(3). Hence it is globally
quasiconvex **assuming the 2026 Burkholder theorem**
(and rank-one convex). Its exact profile identity
is verified by symbolic expansion, with no solver
or numerical tolerance.

Yet at the strictly nonconformal ratio \(r_0=0\),
\[
 h(0)=2,\quad h'(0)=4,\quad
 c=h(0)-0h'(0)=2 <\kappa h'(0)=8/3.
\]
Thus the **Burkholder-line test fails**.
The root \(v=h^{1/3}\) has
\(v(0)=2^{1/3}\) and
\(v'(0)=4/(3\,2^{2/3})\). Its unique
tangent line at r₀=0 has at r=-1 the value

\[
v(0)-v'(0)=2^{1/3}/3>0=v(-1).
\]
So it is **not** a global affine minorant:
the **convex-root test also fails**.

This is an exact **counterexample to completeness
of the disjunction of the two simple tests**, NOT
a Morrey counterexample. It explains why a
**hybrid, nonnegative sum** of both types is
essential: the full certificate envelope
already returns \(\mathcal E_6h=h\) for this h.

## 6. Power-lifting: all p>2 from one lower exponent when possible

**Theorem 6.1 (conditional if the intermediate exponent is <2).**
Let p>2 and suppose F is nonnegative, isotropic,
rank-one convex and positively p-homogeneous.
If for **some** \(s\in(1,2]\) the fractional power

\[
                  H=F^{\,s/p}                           \tag{13}
\]

is again rank-one convex, then **F is quasiconvex
everywhere**. If s=2, F is in fact polyconvex.

Proof: H is nonnegative, isotropic, s-homogeneous.
For 1<s<2, the preceding all-matrix p<2 theorem,
conditional on the 2026 Burkholder result, makes H
quasiconvex. For s=2, the separately derived
global 2-homogeneous theorem makes H polyconvex.
Since the power \(t\mapsto t^{p/s}\) is convex,
nondecreasing on [0,∞), its composition with
nonnegative quasiconvex H is quasiconvex (Jensen).
In the s=2 case, compose a polyconvex extension
with the convex function \(t\mapsto(t_+)^{p/2}\)
to obtain a polyconvex extension of F. QED.

This is a genuine **all-exponent** criterion but
not an automatic reduction: fractional powers
generally do **not** preserve rank-one convexity.
A failure of (13) is an obstruction to this route,
not evidence that F is non-quasiconvex.

## 7. Leaving isotropy and homogeneity: a global closure theorem

Start with **any** collection of certified globally
quasiconvex integrands from Sections 3–6 (possibly
different exponents). For invertible 2×2 L,R
and a base shift A₀, the function

\[
          A\longmapsto F\big(L(A-A_0)R\big)              \tag{14}
\]
is also quasiconvex: left changes of target variables
and right changes of domain variables preserve the
gradient class, after a linear domain change. This
requires *full* quasiconvexity of F, not a statement
only at conformal matrices.

Nonnegative sums, finite pointwise maxima,
locally bounded pointwise suprema and locally
uniform limits of these functions are also
quasiconvex. Consequently, the generated class
contains functions which are **anisotropic,
nonhomogeneous and not parametrized by any fixed p**,
with arbitrary numbers of terms, arbitrary base
matrices, and no fixed test-grid or polynomial
mesh restriction in the stated certificate class.

This does **not** say that every rank-one-convex
2×2 integrand is in the generated class or its
closure. In particular, **transpose is not
included as a generic quasiconvexity-preserving
operation**; rank-one convexity and
quasiconvexity must not be conflated here.

## 8. What remains of unrestricted Morrey

| Direction | Exact gate | What this note proves |
| --- | --- | --- |
| All p>2, isotropic p-homogeneous | Universal identity \(\mathcal E_ph=h\) | Explicit QC minorant, scalar profile bound; identity OPEN |
| Nonisotropic and nonhomogeneous | Density of the GL-translated/positive-generator cone in all global 2×2 rank-one-convex functions **with correct supporting values** | Global positive examples; density OPEN and not suggested by simple symmetrization |
| Counterexample route | A continuous globally rank-one-convex f and actual planar gradient with strict negative Jensen gap | None; generator failure is not a counterexample |
| Lean | Formalize source Burkholder QC, signed SVD, profile-envelope construction, preserving QC under sup and coordinate change, and exact univariate polynomial certificates | All documented, not formalized |
| Original planar Morrey | Universal Jensen or one certified planar counterexample | OPEN |

A single univariate profile certificate can be checked exactly in
finite time **for specified data**. For even integral p, if h
and the chosen supports are polynomial/rational, divide
[-1,1] at finitely many thresholds \(-c_j/m_j\).
Verify each resulting polynomial inequality by exact
rational algebra, a Sturm chain, interval Bernstein
basis or a univariate SOS representation. This avoids
sampling directions or a spatial gradient mesh
for the *positive* certificate. It is NOT a
uniform finite-degree complete algorithm for all F.

**Prior-art warning:** Guerra–Kristensen (2022) already
proved the conformal cases; Bruno–Pasqualotto
[arXiv:2608.06367](https://arxiv.org/abs/2608.06367)
proved RC↔QC for isotropic quartic polynomials,
a different class-wide benchmark. Their theorems
are not superseded by a proof restricted to these
generators. Novelty of the hierarchy or the
general deductions has not been independently
established. The unrestricted conjecture is
not solved.
