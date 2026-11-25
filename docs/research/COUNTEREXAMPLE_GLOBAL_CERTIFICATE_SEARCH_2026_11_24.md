# Globally constrained counterexample search — 24 November 2026

**No counterexample found.** The following searches replace sampled curvature constraints by sufficient polynomial or piecewise-quadratic certificates. They are finite numerical experiments and do not certify the absence of a counterexample, even within their respective sufficient cones.

## Smooth homogeneous angular search

Use the entire angular polynomial class of degree at most four:
`F(X)=sum_e c_e X^e |X|^(p-|e|)`, with |e|=3 or 4. Lower angular monomials are absorbed by the sphere identity. Odd coefficients are allowed. At p=2 fix one coefficient to remove the determinant gauge.

Set t=|X| and H=u tensor v. The numerator t^(8-p) D²F(X)[H,H] is polynomial modulo t²=sum X_i². For a monomial P=X^e of degree d, put q=p-d. Its contribution is

    t^(8-d) D²P[H,H]
      +2q t^(6-d)(X:H) DP:H
      +q t^(6-d)|H|² P
      +q(q-2)t^(4-d)(X:H)² P.

Use a 120-term Gram basis with monomials of degree three in (X,t), reduced to t exponent zero or one, multiplied by u_i v_j. Match all 1260 reduced numerator coefficients. A PSD Gram matrix with an exact identity proves global rank-one convexity; at p>1 the first derivative at zero joins rank-one line restrictions continuously.

Implementation: nonnegative square-weight LP with Gram-eigenvector column generation, followed by numerical full-Gram ADMM. The radial feasible Gram identities and 20 independently evaluated Hessian formulas per setup were checked. Gram trace is normalized to one. The same prior 72-triangle periodic laws are included; additional fields use periodic rational nodal seeds, sawtooth superpositions and near-single-direction fields. Some searches jointly optimize base and nodal field, with fixed gradient RMS and a small covariance diversity penalty excluded from the reported Jensen gap.

Completed actual-gradient runs:
- p=2: three LP iterations on previous field 2, one 1500-iteration full-Gram solve on previous field 8, and six alternating Gram/field steps from two starting configurations.
- p=3/2: six fixed-field Gram solves, 600 iterations each.
- p=3: six fixed-field Gram solves, 800 iterations each.

All final recorded gaps in these runs were positive. Lowest values within the corresponding runs were approximately 5.09e-6 (square-weight LP), 2.98e-7 (p=2 fixed full Gram), 2.29e-7 (p=2 joint), 5.21e-7 (p=3/2), and 3.49e-7 (p=3). These are attained values, not lower bounds. All Gram searches have finite iteration limits, and several field optimizations reached their iteration limits.

## Exact repair instead of relying on floating feasibility

Let R denote the exact coefficient residual between the numerator polynomial and a Gram square polynomial with rational factors. On unit X,u,v and t=1 every reduced monomial has absolute value at most one. Thus the rank-one curvature of F is bounded below by -||R||_1. Since the rank-one Hessian of |X|^p on the unit sphere has lower bound p min(1,p-1), the exact repaired function

    F + ||R||_1/[p min(1,p-1)] * |X|^p

is globally rank-one convex. The repair is rigorous when all coefficients and the residual are computed exactly; a floating residual diagnostic is not by itself a certificate.

An actual degree-two joint-search candidate was rounded to integer square factors with denominator 10^6 and rational coefficients with denominator 10^12. Its exact correction coefficient was 178097229/2000000000000. Rational periodic nodal values and the base were saved; their mean-gradient and determinant identities were checked exactly. Bounding square roots by integer square-root intervals certified its Jensen gap strictly between 89/10^6 and 90/10^6. The exact verifier was executed. This is a **positive-gap control**, not a counterexample.

## Nonsmooth angular search

Allow continuous piecewise-quadratic F in transformed orthants y=TX. T is invertible and need not preserve rank-one matrices. Use eight signed diagonal coefficients and 24 signed cross coefficients. Piecewise continuity follows by construction. Require each of the sixteen constant matrix Hessians to be PSD plus a determinant multiplier. Across y_i=0 require the derivative jump toward positive y_i to be nonnegative for every other sign pattern; these are linear constraints on cross coefficients, obtained by evaluating the linear jump on the face rays. The conditions imply global RC by convexity on each rank-one line, including lines in faces by continuity.

Numerical square-column generation and field optimization were run on four rational fans, two alternating steps each. No negative actual-gradient gap was obtained. Zero gaps occurred and several fields approached effectively one-directional degeneracies; the numerical runs do not rule out other fans.

## Adversarial selection from nonpolyconvex laws

To avoid selecting trivial zero or flat energies, optimize the fan integrand first against an abstract determinant-compatible law, then search actual gradients for the selected energy. The reference law at I is (-2I, diag(4,0), diag(0,4)) with weights (1/4,3/8,3/8). Its mean and determinant moment are correct. Use it and 23 randomly rationally transformed/translated versions with corresponding fans. These are not assumed to be gradients.

Only one abstract law gave a negative repaired numerical gap (approximately -1/16, the reference law). Three actual periodic field searches from that selected energy returned positive gaps approximately 5.54e-6, 6.62e-6 and 4.05e-6. The abstract gap is not a counterexample to Morrey.

## Disposition

This round has no negative actual-gradient candidate to certify. It does not justify declaring the conjecture true. The global Gram certificate/repair and fan conditions are sufficient classes, not a finite exact classification of the unrestricted homogeneous cone. The raw scripts, numerical records, previous input arrays and exact positive-gap control were bundled in the conversation attachment; this repository note records the methods and completed outcome. No new Lean verification, global optimization certificate, or claimed resolution.
