# An all-matrix isotropic Morrey theorem from Iwaniec and Burkholder

Research date: 22 November 2026. **Status: candidate complete hand proof, not independently reviewed
or formalized in Lean.** The p∈(1,2) conclusion assumes the global Burkholder quasiconvexity
asserted in Agazzi et al., [arXiv:2609.28311v2](https://arxiv.org/pdf/2609.28311),
Corollary 2. The independent endpoint cross-check is Theorem 4.2 of Guerra–Kristensen,
[arXiv:2112.10563](https://arxiv.org/pdf/2112.10563). Neither originality nor
published status of the new consequence is claimed. These stronger statements require
independent review, especially because Guerra–Kristensen's published headline
only asserts quasiconvexity **at conformal matrices**.

## Main results (proposed)

**Theorem A.** Let 1<p<2. Assume the Burkholder integrand b_p defined below is
quasiconvex on all real 2×2 matrices. Every finite-valued, nonnegative,
SO(2)×SO(2)-invariant (isotropic), positively p-homogeneous, globally
rank-one-convex F:ℝ²ˣ²→[0,∞) is **quasiconvex at every base matrix**.
More precisely, for every A≠0 there exist α_A,β_A≥0 such that

\[
 G_A(X)=\alpha_A b_p(X)+\beta_A b_p(DX)\le F(X)
 \quad\text{for all X},\qquad G_A(A)=F(A),
 \tag{A}
\]
where D=diag(1,-1). Each G_A is quasiconvex. At A=0 take G_0=0.

**Theorem B.** If p=2, the same assumptions on F imply that F is
**globally polyconvex**, with at every A a supporting polyconvex integrand
\(G_A(X)=c_A\|X\|_{\rm op}^2+m_A\det X\), \(c_A\ge0\).
This result uses only Guerra–Kristensen's extremality bound / elementary
rank-one convexity, not Iwaniec 2026.

Neither conclusion solves unrestricted 2×2 Morrey: the three restrictions
nonnegativity, isotropy and positive homogeneity remain essential to the proof.

## 1. One-dimensional representation

For X≠0 set a=σ₁(X)=||X||op>0 and r=det(X)/a²∈[-1,1].
By the signed singular-value decomposition and SO(2)×SO(2) invariance,

\[
 F(X)=a^p h(r),\qquad h(r)=F(\operatorname{diag}(1,r)).
 \tag{1}
\]

The function h is nonnegative and convex on [-1,1], because
diag(1,r)-diag(1,s) has rank at most one. It is continuous there
because finite-valued globally rank-one-convex functions are continuous.

For 1<p≤2 set k=2/p-1∈[0,1). Define the 2022 convention

\[
 b_p(X)=(k\|X\|_{\rm op}^2+\det X)\|X\|_{\rm op}^{p-2}
      =a^p(k+r),\quad b_p(0)=0.
 \tag{2}
\]

The 2026 convention in its 1<p<2 branch obeys the direct identity

\[
 B_p^{2026}(X)=\frac{p}{2(p-1)}\,b_p(X).
 \tag{3}
\]

Thus the 2026 Corollary 2 implies global quasiconvexity of b_p.
Left multiplication by D flips det while preserving operator norm and
preserves quasiconvexity, so b_p(D·) is also globally quasiconvex.

## 2. Endpoint slopes from 2022 extremality

Theorem 4.2 of Guerra–Kristensen, normalized at I and at D, implies

\[
 F(X)\ge\frac p2F(I)b_p(X),\qquad
 F(X)\ge\frac p2F(D)b_p(DX) \quad\text{for all X}.
 \tag{4}
\]

When F(I)=0 (or F(D)=0) the corresponding bound is immediate from F≥0.
For a positive endpoint, apply Theorem 4.2 to
(p/2)F(endpoint)^{-1} times F (or F(D·)). This preserves all hypotheses.

Restricting (4) to diag(1,r) gives affine barriers

\[
 h(r)\ge \frac p2h(1)(k+r),\qquad
 h(r)\ge \frac p2h(-1)(k-r).                    \tag{5}
\]

Each is an equality at the respective endpoint, because 1+k=2/p.
Consequently, the convex one-sided slopes obey

\[
 s_+:=h'_-(1)\le \frac p2h(1),\qquad
 s_-:=h'_+(-1)\ge-\frac p2h(-1).                \tag{6}
\]

They are finite: convex secant slopes are bounded from one side by the
affine barriers and from the other by interior secants. In fact (6) admits a **direct, self-contained proof** that does not require
the 2022 extremality theorem. Since diag(1+t,1) and
diag(1-t,1) lie on a rank-one line with midpoint I,
for 0<t<1 rank-one convexity gives

\[
 2h(1)=2F(I)\le
 F(\operatorname{diag}(1+t,1))
 +F(\operatorname{diag}(1-t,1)).
\]

By positive p-homogeneity and isotropy (which allows switching
the two diagonal entries by SO(2) rotations), the right-hand side is

\[
 (1+t)^p h((1+t)^{-1})+h(1-t).
\]

Subtract 2h(1), divide by t>0, and let t↓0. Convexity and
finiteness of h ensure existence of the endpoint one-sided slope.
If that slope were +∞, the resulting inequality would contradict
rank-one convexity, so it is finite. The limit gives
\(0\le p h(1)-2h'_-(1)\), proving the first bound.
Apply the same argument to \(X\mapsto F(DX)\), whose diagonal
slice is \(r\mapsto h(-r)\), to obtain the second bound.
Thus (6) and the entire 1-D cone proof have **no need for (4)**
or any other substantive 2022 extremality theorem; (4) remains
a valuable independent cross-check.

## 3. Exact supporting-line cone lemma

**Lemma.** Let 1<p≤2, k=2/p-1, and let nonnegative convex
h:[-1,1]→ℝ satisfy (6). For each interior r₀ and subgradient
m∈∂h(r₀), write c=h(r₀)-r₀m. Then

\[
                  \boxed{c\ge k|m|.}         \tag{7}
\]

**Proof.** Convexity gives s_-≤m≤s_+ and the endpoint-support bounds

\[
h(r₀)\ge h(1)+s_+(r₀-1),\quad
h(r₀)\ge h(-1)+s_-(r₀+1).
\]

If m≥0 and r₀<-k then
c-km=h(r₀)-(r₀+k)m≥h(r₀)≥0.
If m≥0 and r₀≥-k, use m≤s_+ and r₀+k≥0 to obtain

\[
 c-km\ge h(1)-s_+(1-r₀)-(r₀+k)m
       \ge h(1)-(1+k)s_+\ge0.
\]

If m≤0 and r₀>k then
c+km=h(r₀)-(r₀-k)m≥h(r₀)≥0.
If m≤0 and r₀≤k, use m≥s_- and k-r₀≥0 to obtain

\[
 c+km\ge h(-1)+s_-(r₀+1)+(k-r₀)m
       \ge h(-1)+(1+k)s_-\ge0.
\]

This proves both signs; the case m=0 follows from h≥0.
No differentiability of h on the interior is assumed. At r₀=±1,
(5) directly provides a touching affine minorant with coefficients
satisfying the same cone constraint.

## 4. Proof of Theorem A

At any A≠0 with signed ratio r₀∈(-1,1), choose a subgradient m
of convex h; then the affine function ℓ(r)=c+mr supports h below
on the full interval, with ℓ(r₀)=h(r₀).
Since 1<p<2, k>0; define

\[
 \alpha=\tfrac12(c/k+m),\quad
 \beta=\tfrac12(c/k-m).                       \tag{8}
\]

By (7), α,β≥0. Since det(DX)=-det X and ||DX||op=||X||op,

\[
 \alpha b_p(X)+\beta b_p(DX)
 =\|X\|_{\rm op}^p
  \left[c+m\,{\det X\over\|X\|_{\rm op}^2}\right]
 =\|X\|_{\rm op}^p\ell(r_X)
 \le\|X\|_{\rm op}^ph(r_X)=F(X).              \tag{9}
\]

Equality holds at X=A. At X=0 both sides vanish.
At r₀=±1 use the endpoint barriers (5), or the zero function when
the relevant F endpoint value is zero. Thus (A) holds at every base.
The nonnegative linear combination G_A is quasiconvex by the 2026
Burkholder result. For every admissible periodic φ,

\[
F(A)=G_A(A)\le\fint_Q G_A(A+D\varphi)
                \le\fint_Q F(A+D\varphi).
\]

This proves global quasiconvexity for the entire class, **assuming the
source's global Burkholder claim**.

**Stronger representation:** F is the pointwise supremum of all
nonnegative Burkholder combinations lying below F,

\[
 F(X)=\sup_{\alpha,\beta\ge0,\ \alpha b_p+\beta b_p(D\cdot)\le F}
                  [\alpha b_p(X)+\beta b_p(DX)].         \tag{10}
\]

This is a structural cone-generation theorem, independent of the
new quasiconvexity theorem (it uses only rank-one convexity of the
Burkholder generators plus the extremality/endpoint bound).
The new theorem changes those generators from merely rank-one convex
to quasiconvex, enabling the conclusion for all X.

## 5. Proof of Theorem B (p=2)

When p=2, k=0. The same supporting-line lemma yields c≥0
for every interior touching support (and endpoint supports from (5)).
For each such support define

\[
 G_A(X)=c\|X\|_{\rm op}^2+m\det X.
\]

This is polyconvex: the operator-norm square is convex and det is a
minor, linear in the polyconvex extension variable. The same h(r)
support gives G_A≤F globally and equality at A.
Hence F is the supremum of such polyconvex supports. The
supremum of their convex extensions on (X,d) is convex; the set
of coefficients is bounded because h is convex with finite endpoint
slopes, so this extension is finite everywhere. Its restriction to
d=det X equals F(X), proving global polyconvexity.

This p=2 deduction uses neither the 2026 preprint nor the 2022 extremality theorem, because (6) has the self-contained rank-one secant proof above. It needs a
separate independent audit before being treated as publication-level.

## 6. The precise p>2 obstruction

The same two-generator tangent-cone argument does **not** extend
mechanically to p>2, even if all p-Burkholder integrands are quasiconvex.
Take \(F(X)=(\det X)_+^{p/2}\), a nonnegative, isotropic,
p-homogeneous, **polyconvex** integrand.
Here \(h(r)=(r_+)^{p/2}\), and at any 0<r₀<1 its unique tangent is

\[
 m=(p/2)r₀^{p/2-1}>0,\qquad
 c=(1-p/2)r₀^{p/2}<0.
\]

Any nonnegative combination of the two p-Burkholder forms
\((|1-2/p|\|X\|_{\rm op}^2\pm\det X)\|X\|_{\rm op}^{p-2}\)
has a **nonnegative** intercept in the r-variable, so it cannot
match that tangent. This disproves completeness of *that particular
support cone* for p>2, NOT quasiconvexity of F. A p>2 extension
must include determinant-power or other additional globally
quasiconvex generators. Attack the generator cone, not individual
values of p one by one.

## 7. Near-conformal quantitative fallback (all p>1)

For the same nonnegative isotropic homogeneous RC F, let
\(\Delta_F(A)=F(A)-\inf_{\varphi}\fint_Q F(A+D\varphi)\).
The original one-sided Burkholder/convex support plus rank-one
interpolation between the conformal endpoints aI and aD implies,
for σ₁(A)=a≥b=σ₂(A),

\[
0\le\Delta_F(A)\le\frac{a^{p-1}(a-b)}2
\begin{cases}
F(D)+(p-1)F(I),&\det A\ge0,\\
F(I)+(p-1)F(D),&\det A<0.
\end{cases}
\]

For p≥2 use the older determinant-power polyconvex support and
\(r^{p/2}\ge1-(p/2)(1-r)\) on 0≤r≤1.
For 1<p<2, Theorem A makes the actual deficit zero
(assuming Iwaniec), so this older estimate is only a consistency
check. At A=0, set the bound to zero. This estimate alone is NOT
the new all-matrix closure.

## 8. Formal and literature gates

| Gate | Required work | Present status |
| --- | --- | --- |
| U1 | Formalize 1-D convex supporting-cone lemma, endpoints and kink slopes | Hand proof above; not Lean |
| U2 | Signed SVD plus SO(2)×SO(2) invariance and p-hom factorization | Classical; Lean integration missing |
| U3 | Endpoint slope estimate from rank-one midpoint/one-sided derivative | Self-contained proof above; not Lean |
| U4 | Global Burkholder quasiconvexity (2026 Corollary 2), including orientation and convention bridge | External preprint claim; not audited end-to-end |
| U5 | Build α,β and touching minorants, then use existing periodic/domain QC bridges | Explicit hand proof above |
| U6 | Separately check p=2 global polyconvex envelope | Hand proof above; independently review |
| U7 | Literature priority and outside mathematical review, including possibility this is known | Not completed |

This is a substantial *conditional class-wide theorem*: arbitrary
number of matrices, arbitrary periodic tests, every base, every
nonnegative isotropic positively p-homogeneous rank-one-convex F.
The unrestricted anisotropic and nonhomogeneous 2×2 implication
remains open. This note is a candidate research proof, **not** a
Lean theorem or a certified new publication result.
