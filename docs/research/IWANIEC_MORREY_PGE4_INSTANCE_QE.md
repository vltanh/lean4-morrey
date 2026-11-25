# Exact per-integrand decision for rational p >= 4 isotropic polynomial profiles

Research date: 23 November 2026. **A decidability theorem and an exact encoder, not a proof of the universal p >= 4 conjecture.** The mathematical inputs are Tarski's decision procedure for real closed fields and the established Dacorogna–Koshigoe (1993) four-diagonal-atom characterization of isotropic polyconvexity. We do not claim the logical decidability itself as novel. No complete QE solver is installed or was run; no SAT or UNSAT certificate or Lean proof is claimed.

## The complete input-dependent statement

For **any particular rational** p=m/n >= 4 (reduced, positive) and **any rational polynomial** h of arbitrary finite degree, consider
\[
 F(0)=0,\qquad
 F(A)=\|A\|_{\rm op}^{p}
 h\left(\frac{\det A}{\|A\|_{\rm op}^{2}}\right),\quad A\ne0.
\]
Then all three global properties are **decidable in finite time in principle** by exact quantifier elimination over the reals:

1. F is nonnegative at every real 2x2 matrix;
2. F is rank-one convex on the **entire** real 2x2 space;
3. F is polyconvex on the **entire** real 2x2 space.

This is not a fixed-degree, fixed-exponent or finite-gradient-mesh result: polynomial degree and rational numerator/denominator are unrestricted **inputs**. It is also not a universal theorem for all p or all profiles: it addresses one specified semialgebraic integrand at a time. Arbitrary irrational p and nonpolynomial continuous h are outside this decision claim. Nothing here decides general quasiconvexity when polyconvexity fails.

## Polynomial encoding of the operator norm and real exponent

Write \(T=\|A\|_F^2,\ D=\det A,\ s=\|A\|_{\rm op}^2\). The largest squared singular value is characterized *exactly* by
\[
 s\ge0,\qquad s^2-Ts+D^2=0,\qquad 2s\ge T.
\]
Introduce \(r\in[-1,1]\) and \(v\ge0\) satisfying
\[
 sr=D,\qquad v^{2n}=s^m .
\]
The exact energy is \(v h(r)\). At s=0 the matrix is zero and v=0, so r can take any allowed value without changing the energy. This handles **all** singular and conformal matrices, without differentiating the operator norm or making an acoustic regularity assumption.

On the diagonal \(\operatorname{diag}(x,y)\), one can instead specify \(s=\max(x^2,y^2)\) using the Boolean-polynomial conditions
\[
s\ge x^2,\ s\ge y^2,\ (s=x^2\ {\rm or}\ s=y^2).
\]

All resulting constraints are polynomial equations/inequalities with rational coefficients. Consequently their existential satisfiability, including boundary cases, is decidable by real-closed-field quantifier elimination.

## Three generated existential QF_NRA problems

The standalone standard-library [generator](../../research/audit/iwaniec_pge4_complete_instance_QE.py) creates:

- **negative.smt2**: a signed ratio r with h(r)<0. SAT means F is not everywhere nonnegative; UNSAT means F>=0.
- **not_rank_one_convex.smt2**: two matrices A,B, a weight θ in [0,1], det(B-A)=0, and a *strict violation of the defining rank-one convex Jensen inequality*. SAT means F is not rank-one convex; UNSAT means F is globally rank-one convex. No Legendre–Hadamard theorem is assumed.
- **not_polyconvex.smt2**: arbitrary signed-diagonal base and **four** signed-diagonal atoms with nonnegative weights, exact total mass, x/y and determinant moments, and an energy mean **strictly below** its base value. SAT means F is not globally polyconvex; UNSAT means F is globally polyconvex, using [Dacorogna–Koshigoe (1993), Theorem 2.1](https://www.numdam.org/item/AFST_1993_6_2_2_163_0/). Zero weights allow smaller supports. This test needs no nonnegativity, rank-one convexity or C² hypothesis to be equivalent to polyconvexity of the isotropic F.

All three files use the SMT-LIB2 **QF_NRA** language and have *free real constants*. Satisfiability interprets those constants existentially. They can be handed to a **sound, complete** CAD/QE engine; a heuristic or an incomplete nonlinear SMT solver's timeout/unknown is not proof of anything. A successful algebraic witness to nonpolyconvexity under proven nonnegativity and rank-one convexity would refute the *stronger Guerra–Kristensen polyconvexity claim*. It would **not**, by itself, refute Morrey, which requires an actual compatible planar-gradient energy violation.

## Controls and evidence level

From the repository root, run:

    python3 research/audit/iwaniec_pge4_complete_instance_QE.py research/audit/iwaniec_pge4_qe_control.json /tmp/morrey-qe

The supplied example is p=9/2 and h(r)=2+2r²+r⁴. The locally tested encoder produced three finite, balanced formulas in this case. This is **generation/syntax evidence**, not an actual SAT/UNSAT solver run.

Two exact semantic checks that do not require CAD:
- At p=4, h(r)=1-r², take A=diag(1,-1/2), B=diag(1,1/2), θ=1/2. Both endpoint energies are 3/4 and the midpoint energy is 1. Hence the rank-one convexity failure query is SAT for that profile (an explicit rational model).
- At p=4, h(r)=1/2-r, the value at diag(1,1) is -1/2, hence the nonnegativity failure query is SAT.

For p=4, h(r)=1, F(A)=||A||op^4 is globally convex; mathematically all three failure formulas are UNSAT. **These expectations were not verified by CAD in this session.**

## Comparison with previous research and next global gate

The earlier [strict Bernstein-acoustic hierarchy](IWANIEC_MORREY_PGE4_EXACT_HIERARCHY.md) is a *negative semidecision for a smooth class*, capable of validating specific strict ellipticity and a rational negative minors law. This new real-algebraic encoding is **complete in both directions for a fixed rational-polynomial input**, even at Hessian degeneracies or zeros. It replaces a floating-point confidence score with a fully specified logical decision problem.

However, **Tarski decidability is not a solution of the universal conjecture.** It neither proves \(\forall p\ge4\ \forall h\) nor supplies a uniform degree/rational denominator/amplitude bound. For a meaningful unrestricted advance, one must prove a universal analytic Jensen/support inequality (or exhibit a validated global RC, nonnegative, nonpolyconvex profile and then separately address quasiconvexity). More finite-input tests alone cannot close the conjecture.

**Validation boundary:** Generator tested for formula production and balanced parentheses on the p=9/2 example; exact hand models given for two failure cases; no installed complete QE/CAD solver, formal Lean proof, general SAT/UNSAT certificate, or mathematical priority claim.
