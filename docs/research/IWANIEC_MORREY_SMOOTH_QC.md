# Smooth coercive strongly rank-one-convex planar energies from Iwaniec

Research date: 22 November 2026. **Status:** complete hand argument and a finite rational
minors witness, not yet independently peer reviewed or compiled in Lean.
**Quasiconvexity is conditional on the 2026 Iwaniec paper's claimed
Theorem 1**, [arXiv:2609.28311v2](https://arxiv.org/abs/2609.28311v2).
Nonpolyconvexity, coercivity, and strong rank-one convexity follow
directly from the displayed formulas, together with rank-one convexity of L
(which follows if the claimed QC theorem holds). No originality
or unrestricted Morrey solution is asserted.

This construction **resolves the regularity/coercivity side question**
for the Iwaniec generator: its nonpolyconvexity can be certified by
an *actual finite minors-moment law* and survives smooth mollification,
positive quadratic penalties, invertible affine transformations,
and a strict positive coefficient range.

## 1. The 2026 quasiconvex integrand and quadratic stabilization

In the paper, a real 2×2 matrix is represented by
\(Az=a_+(A)z+a_-(A)\bar z\). Define

\[
 L(A)=\begin{cases}
  \det A, & \|A\|_{\rm op}\le1,\\
  2|a_+(A)|-1,&\|A\|_{\rm op}>1.
 \end{cases}                                           \tag{1}
\]

We have \(L(A)\ge-1\) for every A:
inside the unit operator-norm ball, \(\det A\ge-1\);
outside, \(2|a_+|-1\ge-1\).
L is even, \(L(-A)=L(A)\), since det is even
in dimension two and the coefficient \(a_+\) changes sign.
Theorem 1 of the paper claims that L is globally
quasiconvex (hence rank-one convex).

For \(\varepsilon>0\) let
\[
 W_\varepsilon(A)=1+L(A)+\varepsilon\|A\|_F^2.            \tag{2}
\]
Then \(W_\varepsilon(A)\ge\varepsilon\|A\|_F^2\);
it is finite, continuous, nonnegative, quadratically
coercive and globally quasiconvex if L is.
It is strongly rank-one convex: if \(\operatorname{rank}H\le1\),
then for all A and t,
\[
 \frac{W_\varepsilon(A+tH)+W_\varepsilon(A-tH)}2
      -W_\varepsilon(A)\ge\varepsilon t^2\|H\|_F^2.
                                                             \tag{3}
\]
This is a **uniform margin in every rank-one direction**.
Do not confuse this with general uniform convexity, which
would imply polyconvexity and contradict the witness below.

## 2. Exact four-atom minors-preserving witness at zero

For each t>1 set \(D=\operatorname{diag}(1,-1)\) and
\[
 \begin{array}{c|c|c|c}
 &\text{matrix }A_i&\text{weight }w_i&\det A_i\\\hline
 1& D&t^2/[2(1+t^2)]&-1\\
 2&-D&t^2/[2(1+t^2)]&-1\\
 3&tI&1/[2(1+t^2)]&t^2\\
 4&-tI&1/[2(1+t^2)]&t^2
 \end{array}                                             \tag{4}
\]
All weights are nonnegative, sum to 1,
and the **full lifted mean** agrees with the base zero:
\[
 \sum_iw_iA_i=0,\qquad
 \sum_iw_i\det A_i=0=\det0.                              \tag{5}
\]
The values are
\(L(\pm D)=-1\), \(L(\pm tI)=2t-1\),
\(\|\pm D\|_F^2=2\), \(\|\pm tI\|_F^2=2t^2\).
Therefore the entire weighted energy difference
is the elementary exact identity
\[
 \sum_iw_iW_\varepsilon(A_i)-W_\varepsilon(0)
 =\frac{-(t-1)^2+4\varepsilon t^2}{1+t^2}.              \tag{6}
\]
For **every \(0<\varepsilon<1/4\)** one may
choose \(t>1/(1-2\sqrt{\varepsilon})\) to make
(6) strictly negative. If \(W_\varepsilon\)
were polyconvex, Jensen for its convex lifted
representative on the four points
\((A_i,\det A_i)\) would contradict (5)–(6).
Thus **W is nonpolyconvex throughout this open
parameter range**, with no support/subgradient
existence assumption.

**Completely rational fixed instance.**
Set \(\varepsilon=1/8\), \(t=4\). The atoms are
\[
 (D,8/17),\quad(-D,8/17),\quad
 (4I,1/34),\quad(-4I,1/34).                              \tag{7}
\]
Their matrix and determinant mean are both zero, and
\[
 \sum_iw_iW_{1/8}(A_i)-W_{1/8}(0)=-1/17<0.                \tag{8}
\]
The exact rational assertions are implemented in
[research/audit/iwaniec_L_strong_qc_exact.py](../../research/audit/iwaniec_L_strong_qc_exact.py).

These atoms are **not** asserted to be a
planar gradient law or finite laminate. Their
failure of polyconvex Jensen does **not**
refute quasiconvexity or the Morrey implication.

## 2A. The exact quadratic support threshold at the zero matrix

The upper bound \(\varepsilon<1/4\) in the witness is
**sharp** for pointwise *poly-affine supporting at zero*.
This yields a clean dichotomy **independent of the
2026 quasiconvexity theorem**:

\[
 \boxed{\begin{array}{ll}
 0\le\varepsilon<1/4:
  &W_\varepsilon\text{ is NOT polyconvex at zero
    (strict lifted Jensen violation);}\\[1pt]
 \varepsilon\ge1/4:
  & W_\varepsilon(A)\ge
       W_\varepsilon(0)+\tfrac12\det A
       \quad\text{for every }A.
 \end{array}}                                           \tag{10}
\]

In the second line the displayed determinant-affine
minorant is **globally valid** and touches W at zero.
It implies polyconvex Jensen at zero for every
probability measure matching matrix/determinant moments,
and quasiconvexity *at zero* by the determinant
null-Lagrangian identity. It does **not** show
global polyconvexity of W at ε≥1/4.

**Proof of the second line.** It suffices
to prove, for every real 2×2 matrix,
\[
       L(A)+\frac14\|A\|_F^2-\frac12\det A\ge0.            \tag{11}
\]
If \(\|A\|_{\rm op}\le1\), then L=det, and for
\(A=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\)
the left side is exactly
\[
 \frac14(\|A\|_F^2+2\det A)
 =\frac14[(a+d)^2+(b-c)^2]\ge0.                          \tag{12}
\]
If \(\|A\|_{\rm op}>1\), set
\(s=|a_+(A)|\ge0\), \(t=|a_-(A)|\ge0\),
so \(s+t>1\), \(\|A\|_F^2=2(s^2+t^2)\),
\(\det A=s^2-t^2\). The left side becomes
\[
                    2s-1+t^2.                           \tag{13}
\]
When \(s\ge1/2\) this is nonnegative.
When \(s<1/2\), \(t>1-s\), giving
\(2s-1+t^2>2s-1+(1-s)^2=s^2\ge0\).
This proves (11), hence the \(\varepsilon=1/4\)
support inequality. Larger ε only add
\((\varepsilon-1/4)\|A\|_F^2\ge0\).
The first line follows from (6) by choosing
\(t>1/(1-2\sqrt\varepsilon)\);
at ε=0 the choice t>1 is enough. QED.

**Precise scope:** The threshold is sharp for
*polyconvex Jensen at zero* and for this
determinant-affine support mechanism.
At ε≥1/4 nothing here asserts W is
polyconvex at every base matrix. The
statement is an elementary exact theorem
about one explicit family, not a global
Morrey theorem.

## 3. Smooth coercive strongly rank-one-convex examples

Choose a nonnegative even compactly supported
\(C^\infty\) probability mollifier \(\rho\)
on the 4-dimensional matrix space, and let
\(\rho_\delta(B)=\delta^{-4}\rho(B/\delta)\).
Define
\[
 W_{\varepsilon,\delta}(A)
 =\int_{\mathbb R^{2\times2}}
       W_\varepsilon(A-B)\rho_\delta(B)\,dB.             \tag{9}
\]

For each \(\varepsilon\in(0,1/4)\),
choose δ>0 sufficiently small.
The following properties hold simultaneously:

1. **Smooth:** standard convolution gives \(C^\infty\)
   regularity on the entire matrix space.
2. **Quasiconvex (conditional on the 2026 theorem):**
   each translation \(A\mapsto W_\varepsilon(A-B)\)
   is quasiconvex; average the Jensen inequality
   against the positive density \(\rho_\delta\).
3. **Strongly rank-one convex:** average (3) in B.
   The same exact margin \(\varepsilon t^2\|H\|_F^2\)
   survives convolution.
4. **Nonnegative and coercive:**
   \(W_{\varepsilon,\delta}(A)\ge
     \varepsilon\int\|A-B\|_F^2\rho_\delta(B)\,dB
     =\varepsilon(\|A\|_F^2+\int\|B\|_F^2\rho_\delta(B)\,dB)\),
   since the mollifier is even and has zero mean.
5. **Nonpolyconvex:** for the fixed witness (7)
   each of the five values
   \(W_{\varepsilon,\delta}(0)\) and
   \(W_{\varepsilon,\delta}(A_i)\)
   converges to its unmollified value
   as δ↓0. The strict finite Jensen deficit
   from (6) persists. At ε=1/8 and t=4,
   it suffices to make the absolute error in
   each of these finitely many values **less
   than 1/100**: the new deficit is at most
   \(-1/17+2/100<0\).
6. **Still not an unrestricted Morrey counterexample:**
   the witness (7) is only a minor-preserving
   probability law, not an admissible gradient law.

Thus, conditional on Theorem 1 of the 2026
preprint, one obtains smooth coercive
nonnegative *quasiconvex but nonpolyconvex*
integrands with uniform strict rank-one
convexity margins.

Finally, for any invertible U,V and any matrix C,
\(A\mapsto W_{\varepsilon,\delta}(U(A-C)V)\)
is again smooth, quasiconvex, quadratically
coercive and strongly rank-one convex, and
not polyconvex. QC preservation follows from
left and right changes of variables in gradients.
PC preservation holds in both directions
because the map on the five minor variables,
\((A,\det A)\mapsto
 (U(A-C)V,\det U\det V(\det A-\mathrm{cof}(A):C+\det C))\),
is an invertible affine map between lifted
graphs. For generic U,V the resulting
integrand is anisotropic; matrix translation
and quadratic perturbation remove homogeneity.

## 4. Completion gates and limitations

- **Closed at hand-proof level:** exact four-atom
  minors Jensen obstruction, its persistence
  after smoothing, coercivity and strong RC,
  and stability under all invertible affine
  input transforms. The finite witness can
  be checked by exact rational arithmetic.
- **External conditional input:** global
  quasiconvexity of L from Iwaniec 2026,
  including its claimed continuity/RC.
  This note does not independently
  formalize the operator-theoretic proof.
- **Open:** whether *every* rank-one-convex
  integrand can be globally supported by
  such smooth QC generators. The
  [L-cone no-go](IWANIEC_MORREY_CONE_NOGO.md)
  already disproves one broad positive-cone
  completeness conjecture. Smoothness and
  strong RC of particular examples do **not**
  establish universal Morrey.
- **Lean work:** introduce the finite rational
  minor-measure witness first; formalize
  exact energy at five matrices; prove the
  conditional convolution QC/RC lemmas and
  strict inequality stability; retain the
  2026 QC hypothesis explicitly until formalized.
- **Novelty caution:** the literature already
  contains quasiconvex nonpolyconvex examples
  in planar dimensions; no priority or
  independent publication claim is made
  for this particular stabilization.

**Bottom line:** Iwaniec supplies a new
explicit, robust **nonpolyconvex** QC family,
including smooth, coercive, strongly RC,
anisotropic and nonhomogeneous instances.
This is useful for stress-testing
an unrestricted calibration proof,
but it does not prove or refute the
unrestricted 2×2 Morrey question.
