# Global p≥4 counterexample-semid ecision: a strict rational certificate hierarchy

Research: 23 November 2026. Status: **global conditional reduction with an exact
checker**, not a proof or counterexample to Guerra–Kristensen's p≥4 polyconvexity
question and not a proof of Morrey. The word "global" concerns all matrices,
all rank-one directions, all p≥4, and unbounded polynomial degrees and atom
coordinates. The density implication stated below assumes a C² signed-singular
profile; **it is NOT proved for all continuous rank-one-convex profiles**.
The core diagonal/four-atom equivalence is Dacorogna–Koshigoe (1993), Theorem
2.1; the acoustic criterion is the classical Legendre–Hadamard reduction.
No independent novelty or publication-level status is asserted.

## 1. Exact rejection/acceptance gate, valid for arbitrary rational p≥4

For any rational p≥4 and any rational polynomial
\(h\in\mathbb Q[r]\), define
\[
F_{p,h}(0)=0,\quad
F_{p,h}(A)=\|A\|_{\rm op}^p
 h\left(\frac{\det A}{\|A\|_{\rm op}^2}\right)\ (A\ne0).
\]
Put, on -1≤r≤1,
\[
\begin{aligned}
 C&=ph-2rh', & V&=h'',\\
 U&=(p-1)C+r^2V,& E&=(p-2)h'-rV,\\
 P_+&=C+(1-r)E,& P_-&=C-(1+r)E,\\
 Q_+&=(1-r)^2UV-P_+^2,&
 Q_-&=(1+r)^2UV-P_-^2.
\end{aligned}
\]
The following **strict polynomial-sign certificate** is sufficient
for global nonnegativity and global rank-one convexity:
\[
 \boxed{h>0,\ C>0,\ V>0,\quad
        (P_+>0\ \vee\ Q_+>0),\quad
        (P_->0\ \vee\ Q_->0)
        \quad\text{on }[-1,1].}                   \tag{1}
\]
This is checked *for all real r*, not at sampled directions.
It follows from the exact acoustic tensor for distinct singular
values, positive corner jumps at conformal/anticonformal matrices
(C(±1)>0), and convexity along rank-one lines through zero.
For example, \(p=9/2\), \(h(r)=2+2r^2+r^4\)
passes after two rational Bernstein subintervals.

A finite rational Bernstein subdivision verifies (1)
without floating point. Strict positivity at every point of a
compact interval implies a finite such subdivision, so the
checker is a semidecision method for **this strict sufficient
certificate class**. Failure to certify within a search depth
is not proof of failure of rank-one convexity.

## 2. A fully rational certificate of failure of *polyconvexity*

The following additional data suffice to refute *global
polyconvexity* of the same F (without refuting quasiconvexity):

- k≤4, positive rational weights \(w_i\) with total mass 1;
- rational signed-diagonal atoms \((x_i,y_i)\);
- a rational base \(E_t=\operatorname{diag}(1,t)\),
  \(-1<t<1\), satisfying the **exact minor moments**
  \[
   \sum_iw_ix_i=1,\quad
   \sum_iw_iy_i=t,\quad
   \sum_iw_ix_iy_i=t;
  \]
- the **strict** average-energy inequality
  \[
   \sum_iw_i\max(|x_i|,|y_i|)^p
      h\left(\frac{x_iy_i}{\max(|x_i|,|y_i|)^2}\right)
      <h(t),                                          \tag{2}
  \]
  with zero atoms contributing zero.

For rational p=m/n in lowest terms, rational atoms and rational
polynomial h, all powers in (2) are nonnegative *real algebraic*
numbers. Dyadic rational bisection of \(z^n=a^m\) gives exact
upper/lower bounds; a strict upper gap below zero is therefore
finitely certifiable with no floating-point optimizer.
Dacorogna–Koshigoe (1993) proves the ≤4 diagonal-law
characterization of isotropic polyconvexity. Importantly,
a minors-preserving law need not be a **compatible gradient law**:
(1)+(2) would disprove the stronger polyconvexity conclusion,
NOT Morrey's quasiconvexity implication.

## 3. Density theorem: this counterexample hierarchy is complete for C² profiles

**Theorem (conditional negative-route completeness).**
Suppose for some *real* \(p_0\ge4\) there is a finite,
nonnegative, globally rank-one-convex, SO(2)×SO(2)-isotropic,
positively \(p_0\)-homogeneous integrand with a signed-singular
profile \(h_0\in C^2([-1,1])\) that is **not globally polyconvex**.
Then some **rational** \(p\ge4\), rational-coefficient polynomial
h satisfying the strict global certificate (1), and rational
≤4-atom signed-diagonal data satisfying (2) exist.
There is **no asserted upper bound** on the degree, rational
denominators or atom amplitudes.

**Proof.** A strict minors-Jensen violation with at most four
signed-diagonal atoms exists by the 1993 theorem. Because
F≥0 and p≥2, zero and conformal/anticonformal bases obey
polyconvex Jensen (zero trivially; conformals by
Guerra–Kristensen 2022, Theorem 1.3). Normalize the remaining
base by signed SVD and homogeneity to \(E_t\), |t|<1.

For ε>0 set
\[
 F_\varepsilon(A)=F_0(A)+\varepsilon\bigl(
        \|A\|_F^{p_0}+\|A\|_{\rm op}^{p_0}\bigr).
\]
Both added functions are convex, nonnegative, isotropic and
\(p_0\)-homogeneous. The finite strict negative Jensen gap
persists for all sufficiently small ε. On matrices of
operator norm one with distinct singular values,
the Frobenius term contributes a uniform strictly positive
rank-one Hessian margin; the operator-norm term gives strictly
positive conformal corner jumps. Equivalently,
\(h_\varepsilon=h_0+\varepsilon[
 (1+r^2)^{p_0/2}+1]\)
satisfies **strict** conditions (1), including all endpoint
cases: h and C are positive, V=h'' is positive from the
Frobenius contribution, and the strict acoustic gap gives
the disjunctive P/Q positivity. The latter can be seen by
\(B=C/(1-r^2)\), \(T=rB+E\), and the elementary identity
\(B\pm T=P_\pm/(1\mp r)\); the positive Hessian margin
also handles the finite limiting values at r=±1.

The five quantities whose strict signs matter,
\(h,C,V,\max(P_+,Q_+),\max(P_-,Q_-)\), are
continuous on the **compact** interval [-1,1] and have
a positive common minimum. Hence the conditions persist
under sufficiently small changes in p and in h in
the C² norm. Choose rational p≥4 close to p₀, and
approximate \(h_\varepsilon\) in C² by a polynomial with
rational coefficients. Such polynomials are C² dense,
e.g. approximate the second derivative and integrate
twice, approximating the two constants rationally.
This gives a globally certified strict RC, positive
rational-polynomial candidate.

Finally approximate the original finite diagonal law by
rational data *while preserving all moment equalities*:
the x coordinates cannot all be equal in a strict RC-Jensen
violation (that would be one rank-one diagonal line).
Choose nearby positive rational weights and rational x
coordinates, normalize their weighted x mean to one,
choose a nearby rational y base, and solve
\(\sum w_i(y_i-t)=\sum w_i(x_i-1)(y_i-t)=0\)
for the y coordinates in a nearby rational nullspace.
With k≥3 and nonconstant x the constraint matrix has rank
two; rational solutions are dense in its real nullspace.
The original strict energy gap survives every sufficiently
small perturbation. Rational exponents and atoms make the
strict gap exactly algebraically certifiable. QED.

The argument makes an **unbounded exhaustive negative
semidecision program** for the entire C²-profile
isotropic p≥4 problem:
enumerate rational p, polynomial h, and moment-compatible
≤4-atom laws; check exact global acoustic positivity and
the strict Jensen gap. If a smooth nonpolyconvex counterexample
exists, one such candidate must eventually pass.
No uniform finite cutoff, termination for positive cases,
or extension from C² to all finite-valued RC profiles is
proved. The unrestricted **quasiconvexity/Morrey** problem
still requires an actual planar gradient, not these atoms.

## 4. Implementation and checks

[Strict rational verifier](../../research/audit/iwaniec_all_p_rational_cert.py)
takes a JSON object with a rational exponent p, rational
monomial coefficients h, and optionally a diagonal law
of at most four triples (weight,x,y).
Its acoustic proof uses rational Bernstein subdivision
on the **entire** [-1,1]. If a proposed Jensen witness
is supplied, it checks exact minor moments and
interval-encloses rational powers; it reports
STRICT_NEGATIVE_DIAGONAL_MINORS_JENSEN only when a
strict rational upper bound proves (2).
It does NOT invent any counterexample.

Local positive controls: p=4,9/2,5,6,10 with
h(r)=2+2r²+r⁴ all passed in **two Bernstein leaves,
depth 1**. The one-atom affine law is correctly rejected
as a strict Jensen violation. No nonpolyconvex profile
or negative law was found by this control.

The separate [numerical survey](IWANIEC_MORREY_PGE4_NUMERIC_AUDIT.md)
is only exploratory. Neither sampled RC constraints nor
a solver status can substitute for this exact certificate.

**Status and next gate:** Complete the universal *positive*
rank-one-convex⇒polyconvex/ordinary-QC inequality for
every nonnegative isotropic p≥4 homogeneous integrand,
or discover a rational strict certificate above. Failure
to find one cannot settle the universal theorem.
