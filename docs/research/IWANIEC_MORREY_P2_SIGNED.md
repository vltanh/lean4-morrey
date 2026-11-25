# Signed 2-homogeneous isotropic Morrey theorem and correction of a 2022 witness

Research date: 22 November 2026. **Status:** complete hand proofs and exact arithmetic
control, *not* independently reviewed or compiled in Lean. This is a class theorem, not a
solution of unrestricted Morrey. The signed p=2 argument below does **not** use the 2026
Iwaniec preprint and removes the nonnegativity hypothesis from the earlier p=2 note.

## Theorem: signed, global p=2 isotropic polyconvexity

**Theorem S2.** If \(F:\mathbb R^{2\times2}\to\mathbb R\) is finite-valued,
rank-one convex, invariant under \(SO(2)\times SO(2)\), and positively
2-homogeneous, then \(F\) is **globally polyconvex**, even if
\(F\) takes negative values.

More explicitly, there is a bounded set \(T\subset[0,\infty)\times\mathbb R\)
such that
\[
 F(A)=\sup_{(c,m)\in T}\left(c\|A\|_{\mathrm{op}}^2+m\det A\right)
 \qquad (A\in\mathbb R^{2\times2}).                 \tag{S2}
\]
This is a global polyconvex representation (not just a pointwise
minorant or a conformal-base result).

### Proof without an external extremality theorem

**(1) Signed singular-value reduction.** For every \(A\ne0\), set
\(a=\|A\|_{\rm op}>0\) and \(r=\det A/a^2\in[-1,1]\).
SO(2)×SO(2)-invariance and degree-two homogeneity give
\[
 F(A)=a^2h(r), \qquad h(r)=F(\operatorname{diag}(1,r)).
\]
The function \(h\) is convex on [-1,1]: its defining diagonal
line is a rank-one line. Finite rank-one convexity implies continuity.

**(2) Endpoints.** Put \(s_+=h'_-(1)\), \(s_-=h'_+(-1)\).
The one-sided derivatives exist as extended real values by convexity;
the inequalities below force them to be finite.
The rank-one midpoint inequality between
\(\operatorname{diag}(1+t,1)\) and
\(\operatorname{diag}(1-t,1)\) gives, for \(0<t<1\),
\[
 2h(1)\le (1+t)^2h((1+t)^{-1})+h(1-t).
\]
Divide by \(t\), subtract \(2h(1)\), let \(t\downarrow0\):
\[
              s_+\le h(1).
\]
Apply the same inequality to \(A\mapsto F(DA)\),
\(D=\operatorname{diag}(1,-1)\); its profile is \(h(-r)\).
Consequently
\[
 \boxed{s_+\le h(1),\qquad s_-\ge-h(-1).}           \tag{E}
\]
Finite convexity bounds \(s_+\) from below and \(s_-\) from
above by interior secants, so (E) makes both finite.

**(3) Rank-one normalization at zero.** Degree-two homogeneity
forces \(F(0)=0\). Left multiplication by \(-I\in SO(2)\)
gives \(F(-X)=F(X)\). For \(X=\operatorname{diag}(1,0)\),
the rank-one segment \([-X,X]\) therefore gives
\[
            0=F(0)\le\tfrac12(F(-X)+F(X))=h(0).
                                                               \tag{Z}
\]
Note that this is **only** positivity at the rank-one
slice \(r=0\); no global nonnegativity was assumed.

**(4) Every affine support has nonnegative intercept.**
For any \(r_0\in(-1,1)\), choose any slope
\(m\in\partial h(r_0)\) and put \(c=h(r_0)-r_0m\).
If \(0<r_0<1\), convexity and (E) imply
\[
\begin{aligned}
c&\ge h(1)-(1-r_0)s_+-r_0m\\
 &\ge h(1)-s_+\ge0,
\end{aligned}
\]
since \(m\le s_+\).
If \(-1<r_0<0\), use \(m\ge s_-\):
\[
 c\ge h(-1)+(r_0+1)s_--r_0m
  \ge h(-1)+s_-\ge0.
\]
If \(r_0=0\), then \(c=h(0)\ge0\) by (Z).
At \(r_0=1\), choose \(m=s_+\), giving \(c=h(1)-s_+\ge0\);
at \(r_0=-1\), choose \(m=s_-\), giving
\(c=h(-1)+s_-\ge0\). All the corresponding affine lines
\(c+mr\) lie below h on the whole interval and
touch h at their respective \(r_0\).

**(5) Global polyconvex extension.**
Let T be the pairs \((c,m)\) just constructed.
The slope set is bounded by the finite endpoint
slopes \(s_-\le m\le s_+\); since h is bounded on
[-1,1], the intercept set is bounded too.
Define a function on the independent matrix/minor variables:
\[
 \mathcal P(X,d)=\sup_{(c,m)\in T}
                   (c\|X\|_{\mathrm{op}}^2+md).
\]
Each expression is jointly convex in \((X,d)\)
because \(c\ge0\), the squared operator norm is
convex, and md is affine. The bounded coefficient
set ensures \(\mathcal P\) is finite everywhere,
and the supremum is convex. On the physical
minor graph \(d=\det X\), the supporting-line
representation of h gives
\[
 \mathcal P(X,\det X)=F(X)
\]
for every \(X\ne0\), and at \(X=0\) both sides
are zero. Hence \(F\) is polyconvex. QED.

This theorem is **stronger** than the nonnegative p=2
statement in [the universal isotropic note](IWANIEC_MORREY_UNIVERSAL.md).
It does not transfer to arbitrary anisotropic functions, as below.
Before declaring novelty, compare the theorem to the broader
literature on isotropic homogeneous integrands and spectral functions;
the limited search in this project did not establish priority.

## Exact correction: Guerra–Kristensen (2022), Proposition 3.7

Source: [arXiv:2112.10563v1](https://arxiv.org/pdf/2112.10563),
PDF page 9, Proposition 3.7. The article exhibits the
nonnegative, anisotropic rank-one-convex p-homogeneous energy
\[
 F_p\begin{pmatrix}a&b\\c&d\end{pmatrix}
 =\left(a_+d_++\tfrac12(b^2+c^2)\right)^{p/2},
 \qquad p\ge2,
\]
and claims it is not polyconvex at I.

**Printed arithmetic is false.** Its choice
\[
 A_1=\operatorname{diag}(-3,-3),\quad
 A_2=\operatorname{diag}(9,-3),\quad
 A_3=\operatorname{diag}(-3,9),\quad w_i=\tfrac13
\]
does give \(\sum_iw_iA_i=I\), but
\[
 \sum_iw_i\det A_i
 =\tfrac13(9-27-27)=-15
 \ne 1=\det I .
\]
Thus the printed triple is **not** a valid Jensen test
for polyconvexity.

**Corrected exact witness.**
\[
\begin{array}{c|c|c|c}
i&w_i&A_i&\det A_i\\ \hline
1&1/4&\operatorname{diag}(-2,-2)&4\\
2&3/8&\operatorname{diag}(4,0)&0\\
3&3/8&\operatorname{diag}(0,4)&0
\end{array}
\]
Then all weights are positive and add to one, and
\[
 \sum_iw_iA_i=I,\qquad
 \sum_iw_i\det A_i=1.
\]
Every \(F_p(A_i)=0\), while \(F_p(I)=1\).
If \(F_p\) were polyconvex at I, Jensen applied
in the lifted space \((A,\det A)\) would imply
\[
 1=F_p(I)\le\sum_iw_iF_p(A_i)=0,
\]
a contradiction. This **repairs the nonpolyconvexity
conclusion** of Proposition 3.7. Its separate
rank-one convexity proof is unchanged. The new
triple and the failure of the old triple are checked
by [exact rational arithmetic](../../research/audit/gk_prop37_exact.py).
The three atoms **are not claimed to form a gradient
Young measure or a laminate**, so they do **not**
disprove quasiconvexity or Morrey.

### Immediate global obstruction to the proposed generalization method

Every p=2 isotropic energy from Theorem S2 is
polyconvex. Precomposition with invertible
left/right changes of variables, matrix translations,
nonnegative sums, maxima and finite locally bounded
pointwise suprema preserves polyconvexity
(the minor transforms by a constant factor,
and translations of det A are affine functions
of A and det A). The same holds for pointwise
finite locally uniform limits. Thus **no such
closure of the signed isotropic p=2 family** can
produce this anisotropic F₂, because it is
rank-one convex but not polyconvex.

This gives a rigorous *no-go* for extending the
p=2 conclusion to unrestricted anisotropic
rank-one convexity by GL-orbit generation and
positive-cone closure alone. It does **not**
show F₂ is non-quasiconvex and does not settle Morrey.

## Consequences for the unrestricted research plan

1. The signed p=2 isotropic case is closed **at hand-proof
   level**. Nonnegativity is unnecessary; no Iwaniec input.
2. The 1<p<2 all-matrix isotropic result remains conditional
   on the 2026 quasiconvex Burkholder theorem and still uses
   global nonnegativity. Extending it to all signed
   p-homogeneous energies requires separate support analysis.
3. The all-p>2 [hybrid support hierarchy](IWANIEC_MORREY_GENERAL.md)
   remains a **sufficient** QC certificate cone; no universal
   completeness identity has been proved.
4. The nonisotropic case needs genuinely nonpolyconvex
   quasiconvex generators **or** an independent all-gradient
   argument. A failed minor-preserving Jensen test is not
   the same as a negative gradient witness.
5. Formalization gates: factor signed SVD, derive the
   two endpoint inequalities by rank-one midpoints,
   prove the convex-profile support intercept lemma,
   and construct the globally finite polyconvex
   extension. For the source correction, the rational
   control already establishes the stated numbers;
   verify the source's rank-one convexity argument
   separately when formalizing Proposition 3.7.

**Evidence:** Hand argument and exact rational
diagnostic. Not a Lean theorem. No external
mathematical review or journal acceptance.
