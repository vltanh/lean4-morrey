# Exact global-exponent obstruction to extending quartic PC by concave powers

23 November 2026. **Unconditional elementary calculus, independent
of Iwaniec 2026; no publication novelty claim.**
This is a *method obstruction*, NOT a rank-one-convex/nonquasiconvex
counterexample and NOT a solution of the p>2 question.

Let
\[
 s(A)=\|A\|_F^2,\quad d(A)=\det A,\qquad
 Q(A)=s(A)(s(A)-2d(A)).
\]
The quartic Q is globally **nonnegative and polyconvex**:
this is the classical Dacorogna–Marcellini
endpoint (also used in the
[high-coupling theorem](IWANIEC_MORREY_QUARTIC_SHEAR_BOUND.md)).
The earlier stabilization theorem proves that
\(Q^{p/4}\) is polyconvex for **every p≥4**,
because the outer power is then convex increasing.

**Theorem (exact entire exponent interval).**
For **every** real \(2<p<11/4\), the
finite nonnegative isotropic p-homogeneous integrand
\[
               F_p(A)=Q(A)^{p/4}
\]
is **not rank-one convex** on all 2×2 matrices.

**Proof.** Restrict to the rank-one affine line
\(A(t)=\operatorname{diag}(1,t)\):
\[
 Q(A(t))=(1+t^2)(1-t)^2=:g(t).
\]
At t=1/2, exact differentiation gives
\[
 g(1/2)=5/16,\quad
 g'(1/2)=-1,\quad g''(1/2)=1.
\]
For \(q=p/4>0\) and where g>0,
\[
 \frac{d^2}{dt^2}g(t)^q
 =q g(t)^{q-2}
 \big((q-1)(g'(t))^2+g(t)g''(t)\big).
\]
Therefore
\[
\boxed{
 \left.\frac{d^2}{dt^2}F_p(A(t))\right|_{t=1/2}
 =q(5/16)^{q-2}\left(q-\frac{11}{16}\right)<0
}
\]
for \(2<p<11/4\). Since the line direction
\(E_{22}\) has rank one, F_p cannot be
rank-one convex. QED.

A standard-library exact verifier checks the
rational derivative identities:
[checker](../../research/audit/iwaniec_fractional_power_no_go_exact.py).

**Interpretation.** One cannot extend the
high-coupling quartic PC theorem to all
\(2<p<4\) merely by applying the concave
power \(x^{p/4}\) to its nonnegative
polyconvex generators; the operation can
destroy **rank-one convexity itself**.
This identifies a genuine obstruction on
an **entire continuum of exponents**.

It does not assert that all fractional
powers fail for \(11/4\le p<4\);
nor does it refute the global p>2
Guerra–Kristensen conjecture, whose
hypotheses require rank-one convexity.
A successful all-p theorem needs a
different construction or a new
inequality for the full RC class.
