# Exact all-p>4 obstruction to reducing the isotropic conjecture to p=4

Research date: 23 November 2026. **Status: exact, elementary, all-exponent theorem.**
This is a no-go for a proposed *exponent-reduction operation*, not a
counterexample to the global p>4 polyconvexity conjecture or Morrey.
No publication-level novelty is claimed. No Lean compilation/CI.

## A universal test family already polyconvex

For each real p>4, define
\[
 F_p(A)=(\det A)_+^{p/2}.
\]
It is finite, nonnegative, SO(2)×SO(2)-isotropic, positively
p-homogeneous, and **globally polyconvex**: the scalar map
\(d\mapsto(d_+)^{p/2}\) is convex and \(\det A\) is a minor.
It is therefore rank-one convex.

Its signed-singular profile is \(h_p(r)=(r_+)^{p/2}\), since
\(F_p(A)=a^p h_p(\det A/a^2)\), \(a=\|A\|_{\rm op}\).

## Theorem: same-profile exponent demotion destroys even rank-one convexity

One tempting universal strategy was: establish every nonnegative
isotropic rank-one-convex **4-homogeneous** energy is polyconvex,
then treat **every p>4** by changing the homogeneity while
retaining its signed-singular profile.

This **cannot work**: for **each** real p>4, set
\[
 G_{p\to4}(A)=a^4 h_p(\det A/a^2),\quad G_{p\to4}(0)=0.
\]
Then \(G_{p\to4}\) is **not rank-one convex**.

**Exact proof, all p>4 at once.** Along the rank-one affine
line \(A_t=\operatorname{diag}(1,t)\), \(t>0\),
\[
G_{p\to4}(A_t)=
\begin{cases}
t^{p/2},&0<t\le1,\\
t^{4-p/2},&t\ge1.
\end{cases}
\]
This is continuous at t=1, with one-sided derivatives
\[
G'_{p\to4}(1^-)=p/2,\qquad
G'_{p\to4}(1^+)=4-p/2.
\]
Their difference is
\[
\boxed{G'_{p\to4}(1^+)-G'_{p\to4}(1^-)=4-p<0.}
\]
A convex function on a line cannot have a *downward*
derivative jump. Since the direction \(E_{22}\) has rank one,
this contradicts rank-one convexity. No sampling or
floating-point calculation is used. QED.

**Stronger parameter statement.** For any target exponent
q with \(0<q<p\), define \(G_{p\to q}(A)=a^q h_p(r)\).
The same rank-one line has left derivative p/2 and
right derivative q-p/2, giving a downward jump
\(q-p<0\). Thus **any strict decrease in homogeneity
holding this profile fixed fails rank-one convexity**,
even when the original function is polyconvex.

This is a sharp, entire-continuum obstruction:
failure occurs for every \(p>q>0\), not
just for finitely many exponents.

## Research implications

- The quartic result does **not** imply p>4 for general
  isotropic integrands by simple profile preservation.
  Even the proposed reduction \(\|A\|_{\rm op}^{4-p}F_p(A)\)
  can destroy rank-one convexity.
- This does **not** exclude more sophisticated exponent
  comparisons or p-independent global inequalities:
  a new operation could alter the profile as well as p.
- Every F_p in the example is itself globally
  polyconvex, so there is **no counterexample** to
  the Guerra–Kristensen p>4 claim or Morrey.
- The next substantive positive target remains
  a universal cross-level Jensen or global support
  theorem for all nonnegative isotropic p>=4 RC
  integrands, not a case-by-case exponent descent.
- The exact [regression checker](../../research/audit/iwaniec_exponent_demotion_exact.py)
  verifies the piecewise power profiles and the
  strict derivative jump for multiple rational
  exponent controls; the proof covers all real p>q.
