# A five-variable exact global support-obstruction query for the p≥4 problem

Research date: 23 November 2026. **Status:** exact scalar interval/Helly reduction and executable SMT-LIB2 query generator, NOT the universal p≥4 polyconvexity theorem. The supporting-plane characterization comes from Dacorogna–Koshigoe (1993), Theorem 2.1; the formula is the project's earlier [one-multiplier reduction](IWANIEC_MORREY_GENERAL_SUPPORT_CRITERION.md). No claim of a new general convexity theorem or a Lean proof.

## 1. The theorem behind the query

Fix any rational p=m/n≥4, an arbitrary rational-polynomial h, and assume the corresponding isotropic p-homogeneous integrand F is **nonnegative and globally rank-one convex** (these premises can be independently checked by the direct [QF_NRA encoding](IWANIEC_MORREY_PGE4_INSTANCE_QE.md)). At a nonconformal normalized diagonal base E_t=diag(1,t), |t|<1, put H=h(t) and M=h'(t).

For a candidate determinant multiplier c, the global poly-affine support condition is

\[
  c\in[L_t,U_t],\quad A_t(a,s)+cK_t(a,s)\ge0
  \quad\forall a\ge0,\ s\in[-1,1],
\]
where
\[
\begin{aligned}
L_t&=\frac{(1+t)M-pH}{1-t},&
U_t&=\frac{pH+(1-t)M}{1+t},\\
A_t(a,s)&=a^p h(s)+(p-1)H-a[pH+M(s-t)],&
K_t(a,s)&=(a-1)(t-as).
\end{aligned}
\]

Because F is rank-one convex, \(pH-2tM\ge0\), and \(L_t\le U_t\). Each amplitude/ratio test restricts c to one closed half-line or all of R. The intersection with the compact orientation interval is empty if and only if **one or two** test points witness its emptiness. This is the one-dimensional Helly theorem, not a finite classification of all possible a,s.

## 2. Exact polynomial conditions for a failure

Let \(A_j=A_t(a_j,s_j)\), \(K_j=K_t(a_j,s_j)\), and

\[
 L_{\rm num}=(1+t)M-pH,\qquad
 U_{\rm num}=pH+(1-t)M .
\]

The support is **infeasible** at t precisely when at least one of the following occurs (after possibly relabeling the two test pairs):

1. \(K_1=0\) and \(A_1<0\).
2. \(K_1>0\) and \(-A_1(1+t)>K_1U_{\rm num}\).
3. \(K_1<0\) and \(-A_1(1-t)>K_1L_{\rm num}\).
4. \(K_1>0,\ K_2<0,\ A_1K_2>A_2K_1\).
5. The orientation interval is empty, equivalently \(pH-2tM<0\) (impossible under the verified rank-one-convexity premise, but included as a diagnostic).

This is an **existential formula in only five real variables**, \(t,a_1,s_1,a_2,s_2\), when p is an integer. For rational p=m/n with n>1, introduce nonnegative \(v_j\) satisfying \(v_j^n=a_j^m\); the formula then has **seven** real variables. There is no sampling of matrices, no degree cutoff on h, no finite amplitude bound, and all constraints have rational polynomial coefficients.

**Theorem (conditional only on the stated F premises and the published 1993/2022 results).** If the generated formula is **UNSAT** by a sound, complete exact real-algebraic decision procedure, F is globally polyconvex: nonconformal bases have global poly-affine supports; the zero base is trivial by nonnegativity; and conformal/anticonformal bases are covered by Guerra–Kristensen's 2022 theorem for p≥2. Conversely, **SAT** yields a mathematically exact failure of global polyconvexity at some nonconformal base. It is **not** automatically failure of quasiconvexity or Morrey.

## 3. Practical comparison and local solver controls

The [exact generator](../../research/audit/iwaniec_pge4_two_test_QE.py) writes the reduced formula. Run:

    python3 research/audit/iwaniec_pge4_two_test_QE.py research/audit/iwaniec_pge4_two_test_control.json /tmp/morrey-p4-fast.smt2

The input p=4,h=1 gives \(F(A)=\|A\|_{\rm op}^4\), which is convex. A local exact nonlinear-real solver (Z3 through the system libz3 interface) returned **UNSAT** for its five-variable reduced formula. For controls p=4,h=1-r² and p=4,h=1/2-r it returned **SAT**, consistent with direct failures; neither is a valid nonnegative globally RC counterexample to the p≥4 conjecture.

For p=9/2,h=2+2r²+r⁴, the **seven-variable** query was generated, but the local solver did not return a result within a 20-second test window. A separate full-matrix RC query for a simple convex control also timed out. **A timeout/unknown is not UNSAT**, and no nontrivial global p≥4 polyconvexity decision has been certified by these runs.

The original direct [four-atom query](IWANIEC_MORREY_PGE4_INSTANCE_QE.md) has many more variables but needs **no analytic supporting-plane theorem**. It should remain the independent fallback when verifying a proposed counterexample. The smaller query is a significant computational reduction for the **stronger polyconvexity** problem; it is not a replacement for a genuine gradient-law witness to nonquasiconvexity.

## 4. What remains global

The universal positive theorem is exactly the assertion that this reduced support-failure formula is UNSAT **for every nonnegative, isotropic, rank-one-convex p-homogeneous F and every p≥4**. Instance-by-instance SAT/UNSAT decisions cannot prove that universal assertion without an additional uniform mathematical argument. No such argument or counterexample was obtained in this work.

**Validation:** Generation and balanced-parenthesis tests succeeded; the three elementary p=4 reduced queries returned UNSAT/SAT/SAT on a local Z3 library; the p=9/2 query timed out. The proof of equivalence uses the stated previous mathematical theorems and algebraic cross multiplication. No formal Lean build, CI, external referee audit, or global conjecture completion is claimed.
