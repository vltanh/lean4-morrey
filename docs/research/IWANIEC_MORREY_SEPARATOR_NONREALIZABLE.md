# Exact nonrealizability of the p=4 hybrid-cone separator

Research date: 22 November 2026. **Unconditional exact result.**
This note corrects a potential misuse of the separator in
[the global hybrid no-go](IWANIEC_MORREY_HYBRID_NOGO.md).

The cone separator is the positive evaluation functional
\[
 \Lambda(h)=\tfrac54h(-1/3)+\tfrac7{20}h(1/3).
\]
For the chosen rank-one base \(E=\operatorname{diag}(1,0)\)
and \(p=4\), the masses represent
\(\|A\|_{\rm op}^4\)-weighted **profile** masses;
they are **not probability masses**. They satisfy
the sharp two Burkholder-moment inequalities
but cannot arise from an actual matrix probability law
with the required barycenter and determinant moment.

## Theorem: excluded even BEFORE gradient compatibility

Let \(\mu\) be any probability measure on real 2×2 matrices
with finite fourth operator-norm moment.
Put \(a(A)=\|A\|_{\rm op}\) and
\(r(A)=\det A/a(A)^2\) when a>0.
Assume
\[
\begin{gathered}
 \int A\,d\mu=E,\qquad
 \int\det A\,d\mu=0,\\
 r(A)\in\{-1/3,+1/3\}\quad\mu\text{-a.e. on }a>0,\\
 \int_{\{r=-1/3\}}a^4\,d\mu=\tfrac54,\qquad
 \int_{\{r=+1/3\}}a^4\,d\mu=\tfrac7{20}.
\end{gathered}                                          \tag{1}
\]
Then **no such \(\mu\) exists**.

**Exact proof.** For every real a≥0,
\[
 a\le\tfrac34+\tfrac13 a^2,
 \qquad
 a\le\tfrac34-\tfrac13 a^2+\tfrac23a^4,
\tag{2}
\]
because their right-minus-left differences are
\[
 \tfrac13(a-\tfrac32)^2,\qquad
 \tfrac23(a^2-\tfrac34)^2+\tfrac23(a-\tfrac34)^2,
\]
respectively. Apply the first inequality on
\(r=-1/3\), and the second on \(r=+1/3\).
At a=0 either applies; it contributes no
weighted moment and only a nonnegative constant.
The determinant-moment condition gives
\[
 \int_{r=-1/3}a^2\,d\mu
 =\int_{r=+1/3}a^2\,d\mu.
\]
Integrating (2) therefore yields
\[
 \int a\,d\mu\le
 \tfrac34+\tfrac23\cdot\tfrac7{20}
 =\boxed{\tfrac{59}{60}}<1.                 \tag{3}
\]
But convexity of the operator norm and the matrix
barycenter imply
\[
 1=\|E\|_{\rm op}
 \le\int\|A\|_{\rm op}\,d\mu
 =\int a\,d\mu.
\]
Contradiction. QED.

**More general forced moment inequality.**
For any such matrix probability law with
\(\int A=E,\int\det A=0\) and r restricted
to the two ratios ±1/3 (but no fixed fourth moments),
\[
 \boxed{
 \int_{\{r=+1/3\}}a^4\,d\mu\ge\tfrac38.
 }
\]
The cone separator uses \(7/20<3/8\),
so its weighted profile law is excluded.
The algebra is checked by the
[standard-library rational verifier](../../research/audit/iwaniec_separator_nonrealizable_exact.py).

This is stronger than observing that
\(\lambda_-+\lambda_+=8/5\ne1\):
weighted profile masses need not sum to one,
even for a legitimate gradient law.
The **actual obstruction** is the matrix
norm barycenter, the determinant null-Lagrangian,
and the two exact scalar inequalities (2).

## Why it matters

The previous strict hybrid-cone gap
\(h(0)>\Lambda(h)\) does **not** approximate
a genuine Jensen violation simply by
normalizing \(\Lambda\): the target profile
masses cannot even meet the basic matrix
and determinant moments at the intended base.
No gradient realization search based on that
exact two-ratio separator could succeed.

The [new global poly-affine support](IWANIEC_MORREY_RANKONE_SUPPORT.md)
goes further: it shows that **every** actual compatible
gradient field at this rank-one base satisfies
the Jensen inequality, regardless of the ratios,
amplitudes or frequencies involved.

**Not claimed:** the argument says nothing about
nonconformal full-rank base matrices or about
all p>2 integrands. Its main value is to
separate an artificial conic dual witness from
a legitimate gradient (or even matrix) law and
to redirect the search toward valid global
supports.
