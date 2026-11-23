# Global p≥4 conjugate support criterion and finite-amplitude truncation

23 November 2026. **Status:** exact analytic reformulation and a
global tail bound, NOT proof of the universal polyconvexity or
quasiconvexity conjecture. These are elementary consequences of
the 1993 Dacorogna–Koshigoe diagonal supporting-plane criterion,
the [one-multiplier formula](IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md),
and Fenchel conjugation. The reformulations are not claimed novel.
No Lean check or independent review is asserted.

## 1. An equivalent SINGLE-amplitude inequality (every p≥4)

Let p≥4 be any real number. Let
\(F(A)=\|A\|_{\rm op}^p h(\det A/\|A\|_{\rm op}^2)\)
be a nonnegative isotropic, positively p-homogeneous,
globally rank-one-convex function, with h differentiable
at some \(t\in(-1,1)\). Write H=h(t), m=h'(t).
Since rank-one convexity makes h convex, define the
finite one-dimensional restricted Fenchel conjugate
\[
 h^*(q)=\sup_{s\in[-1,1]}\{q s-h(s)\}.
\]

For \(c\in\mathbb R\), define
\[
 L_t=\frac{(1+t)m-pH}{1-t},\qquad
 U_t=\frac{pH+(1-t)m}{1+t},\qquad
 q_{t,c}(a)=a^{1-p}[m+c(a-1)]\quad(a>0)
\]
and
\[
 R_{t,c}(a)=(p-1)H-apH+a m t+c(a-1)t.
\]

**Theorem 1 (exact global criterion).** F has a
global poly-affine minorant touching it at
\(E_t=\operatorname{diag}(1,t)\) if and only if
there exists a single \(c\in[L_t,U_t]\)
satisfying
\[
 \boxed{
 a^p h^*(q_{t,c}(a))\le R_{t,c}(a)
 \quad\text{for EVERY }a>0,
 }\tag{1}
\]
and the zero-amplitude condition
\[
                  (p-1)H-ct\ge0.                 \tag{2}
\]
Consequently the original **two-variable continuum**
\((a,s)\in[0,\infty)\times[-1,1]\)
has been reduced to a **single scalar
amplitude** \(a>0\), with h* a known
one-dimensional convex conjugate of the
given profile. This does **not**
make the universal inequality true.

**Proof.** The
[existing supporting-plane formula](IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md)
states that a global support exists iff c lies
in the orientation interval and for every
a≥0, s∈[-1,1],
\[
 P_{t,c}(a,s)
 =a^p h(s)+(p-1)H
 -a[pH+m(s-t)]+c(a-1)(t-a s)\ge0.
\]
For a>0, collect the coefficient of s:
\[
 P_{t,c}(a,s)
 =a^p\bigl[h(s)-q_{t,c}(a)s\bigr]+R_{t,c}(a).
\]
The infimum over s∈[-1,1] is exactly
\(R_{t,c}(a)-a^p h^*(q_{t,c}(a))\).
At a=0 the original formula reduces to
\((p-1)H-ct\), independent of s.
These steps are reversible, proving (1)–(2).
At a=1, equality holds automatically by
Fenchel equality \(h^*(m)=mt-H\).
The usual global support proves PC
(and hence QC) at the chosen base
for **all** admissible perturbations.

For rank-one-convex F the interval is nonempty,
since
\[
 U_t-L_t=\frac{2[ph(t)-2t h'(t)]}{1-t^2}\ge0.
\]
This is Baker–Ericksen monotonicity,
not a new all-matrix PC result.

## 2. An explicit GLOBAL tail cutoff for all p≥4

Assume \(h_*=\min_{[-1,1]}h>0\)
(strict positive profile). Fix t, H>0,
m and the bounded orientation interval
I=[L_t,U_t], and set
\[
 C_0=\max\{|L_t|,|U_t|\},\qquad
 M=pH+2|m|+C_0.
\]
Choose **any integer** R≥1 such that
\[
 \boxed{
 R^2\ge\frac{4C_0}{h_*},\qquad
 R^3\ge\frac{4M}{h_*}.
 }\tag{3}
\]
Then for **every** c∈I, every real s∈[-1,1]
and every amplitude a≥R,
\[
             \boxed{P_{t,c}(a,s)>0.}           \tag{4}
\]

**Proof.** For a≥1 and |t|,|s|≤1,
\[
\begin{aligned}
P_{t,c}(a,s)
&\ge h_*a^p-C_0a^2
     -[pH+2|m|+C_0]a+(p-1)H\\
&=h_*a^p-C_0a^2-Ma+(p-1)H .
\end{aligned}
\]
Since p≥4 and a≥R≥1, \(a^{p-2}\ge a^2\)
and \(a^{p-1}\ge a^3\).
Condition (3) implies
\(C_0a^2\le h_*a^p/4\) and
\(Ma\le h_*a^p/4\).
Therefore P≥\(h_*a^p/2+(p-1)H>0\).
Every step holds simultaneously for all
c in the orientation interval. QED.

Thus for any **fixed strictly positive profile**
the one-multiplier support problem has an
explicit compact amplitude range [0,R].
There is **no uniform R for all profiles**
because \(h_*\) may be arbitrarily close to zero,
the endpoint coefficients may be large,
and no universal bounds for h derivatives
have been supplied.

## 2A. NEW: zero amplitude is automatically safe, with a uniform gap

The separate zero-amplitude condition (2) is **redundant**
for every nonnegative globally rank-one-convex profile
and every p>2. More strongly:

**Theorem (all exponents p>2, all nonconformal bases).**
Let \(H=h(t)\ge0\), \(m=h'(t)\),
\(C= pH-2tm\ge0\), and
\(c\in[L_t,U_t]\) be any orientation-admissible
determinant multiplier. Then
\[
\boxed{(p-1)H-ct\ \ge\ \frac{p-2}{2}H.}\tag{5}
\]
If H>0, the support inequality therefore holds
**strictly at zero amplitude for every admissible c**.

**Exact proof.** If \(0\le t<1\), the worst c is
the upper endpoint U_t, and
\[
 (p-1)H-tU_t-\frac{p-2}{2}H
 =\frac{1-t}{2(1+t)}(pH-2tm)\ge0.
\]
If \(-1<t\le0\), the worst c is the
lower endpoint L_t, and
\[
 (p-1)H-tL_t-\frac{p-2}{2}H
 =\frac{1+t}{2(1-t)}(pH-2tm)\ge0.
\]
Both are exact algebraic identities, and
\(C\ge0\) is a necessary rank-one-convexity
condition from the acoustic tensor (or
the standard isotropic Baker–Ericksen inequality).
No appeal to the 2026 Iwaniec theorem is used.

**Explicit small-amplitude cutoff.** Suppose H>0.
Set \(C_0=\max(|L_t|,|U_t|)\) and
\(M_0=pH+2|m|+2C_0\).
For all \(c\in[L_t,U_t]\), all \(s\in[-1,1]\)
and \(0\le a\le1\), nonnegativity of h gives
\[
 P_{t,c}(a,s)\ge\frac{p-2}{2}H-aM_0.
\]
Therefore every amplitude
\[
 \boxed{0\le a\le
 \rho_t:=\min\left\{1,\frac{(p-2)H}{4M_0}\right\}}
 \tag{6}
\]
is automatically safe for **every** orientation-admissible c,
with \(P_{t,c}\ge(p-2)H/4>0\).
Here \(M_0>0\) when p>2,H>0.

Together with the earlier explicit large-amplitude
cutoff R (when \(\min h>0\)), this reduces
the support problem for each strictly positive
profile and base to a **compact annulus**
\[
 \boxed{\rho_t\le a\le R_t,\quad -1\le s\le1.}
\]
The same scalar multiplier c must work throughout
that annulus. This is not a finite list of
test points, and the universal existence
of c is **still unproved**. Both cutoffs
depend on the profile and base; no
uniform all-integrand cutoff is claimed.

The [exact symbolic control](../../research/audit/iwaniec_pge4_zero_amplitude_exact.py)
checks the endpoint identities and the elementary
small-amplitude bound algebra.

## 3. Reduction of the GLOBAL positive conjecture to h>0

This part **does not need C² smoothness**.

**Theorem 3.** Fix any p≥4. To prove global
polyconvexity of **every** nonnegative,
finite-valued, isotropic, p-homogeneous
rank-one-convex integrand, it suffices
to prove it for integrands whose signed
profile h satisfies \(\min h>0\).

**Proof.** For any target F and δ>0 define
\(F_\delta(A)=F(A)+\delta\|A\|_F^p\).
The added term is convex, nonnegative,
isotropic and p-homogeneous, so Fδ
retains all hypotheses. Its profile is
\(h_\delta(r)=h(r)+\delta(1+r^2)^{p/2}\ge\delta\).
By the proposed strictly-positive-case
theorem, Fδ is globally polyconvex.
Apply its four-atom diagonal Jensen
inequality to any fixed minor-compatible
finite law; let δ↓0. Its quartic/power
correction vanishes at every fixed atom
and base. Thus F satisfies all such
inequalities and is polyconvex by
Dacorogna–Koshigoe (1993). QED.

This is a **reduction of the universal
positive theorem**, not a proof of
the strictly positive case itself.
It does not smooth a nondifferentiable
profile, and the differentiable support
formula from §1 requires its own
regularity or subgradient formulation.

## 4. Combined global gate and its exact obstruction type

For differentiable strictly positive h,
the full p≥4 conjecture would follow if,
for **every** h satisfying the global
rank-one acoustic conditions and every
signed ratio t, the compact set of
c∈[L_t,U_t] obeying (1) on 0<a≤R
and (2) is nonempty.

For each fixed amplitude a, the constraint
in c is a **closed convex interval**
(a sublevel set of the convex function
\(c\mapsto a^p h^*(q_{t,c}(a))-R_{t,c}(a)\)).
By the 1D Helly property, a failure of
global support is witnessed by **at most
two amplitude constraints**, together
with the orientation interval and the
zero-amplitude endpoint. This sharpens
the previous two-(a,s)-test formulation
into a one-dimensional search.
The amplitude witness is still
**a polyconvexity obstruction**, not
an actual gradient-energy violation.

The [exact rational profile hierarchy](IWANIEC_MORREY_PGE4_EXACT_HIERARCHY.md)
can rigorously check any proposed smooth
p≥4 counterexample. The present
Legendre reformulation improves
the shape of the **positive proof gate**;
neither establishes it. In particular,
the 1993 four-atom moment criterion
and the 2026 diagonal polyconvexity
characterization already contain
the essential convex-analytic ingredients.

## 5. Reproduction

The [symbolic identity control](../../research/audit/iwaniec_pge4_conjugate_identity.py)
checks the algebra for all symbolic p,t,H,m,c,a,s
and evaluates the tail cutoff using exact
rational data. It does not certify the
unresolved universal amplitude inequality.
No finite degree/mesh classification or
Lean kernel proof is claimed.
