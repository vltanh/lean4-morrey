# Independent review of the global SOS search

Reviewed `../work_sos/sos_search.py` and `../work_sos/certify_control.py`.
No critical mathematical or indexing error was found.

- The coefficient map is the full Hessian contraction with H=u tensor v, with
  consistent row-major matrix indices. Degree-six uses all A-monomials through
  degree two in its Gram basis, enough for the degree-four Hessian coefficients.
- Positive-semidefinite Q and exact coefficient matching imply global
  rank-one convexity. Floating-point SDP feasibility is only candidate evidence.
- Removing quadratic minors by equating their two coefficients is a harmless
  choice of representative modulo null Lagrangians.
- An explicit nonzero base is not required for this search class: translating
  any degree-at-most-d polynomial preserves its degree and rank-one convexity;
  discarding the translated constant and linear terms preserves the Jensen gap.
- The periodic finite-element gradient is compatible across triangles and has
  zero mean. Its determinant average vanishes. The normalization uses its true
  mean squared norm, which is one after normalization.
- The covariance barrier derivative is correct, including the projection term
  introduced by gradient normalization. Independent finite-difference checks
  with degree-six polynomials and barriers 0.0001 and 0.01 had relative errors
  below 3.4e-11.
- The exact control has three target components and two domain dimensions.
  Its field is (sin x, sin y, sin(x+y)). The exact Fourier-moment computation
  and the rational positive-definite Gram verification establish a 3x2 example,
  not any 2x2 conclusion.
- Thirty independent exact physical Hessian evaluations used the five-point
  univariate polynomial formula, not the coefficient differentiation loop, and
  agreed with the exact Gram form in every case.

The SOS cone with a prescribed positive Gram margin is a sufficient subclass of
globally rank-one-convex polynomials. Unsuccessful local searches within it are
not a proof that the general class contains no counterexample. Covariance
barriers restrict numerical search paths; attained objective values are not
rigorous lower bounds.

Reproduce the independent checks with `python audit_sos.py`. The exact control
certificate itself is verified separately by `../work_sos/certify_control.py`.

## Literature checks

Dacorogna--Haeberly 1998 Example 3 explicitly gives the eigenvalue criteria used
for the degree-one integrands. It also records earlier numerical searches in
this family. The stronger matrix used here follows by setting M=N-I with
eigenvalues (3,5,5,9), making both stated rank-one-convexity thresholds equal to
one. Thus the parameter conclusion does not depend on the poor OCR of the 1996
corollary.

Primary source: https://www.numdam.org/item/M2AN_1998__32_2_153_0.pdf

Aubert's 1988 paper reproduces the 1987 counterexample in section 3. It is an
isotropic function of singular values on positive-determinant matrices,
extended by infinity outside that set. It differs from the finite-valued
anisotropic P_beta family. Exact-expression web searches found no occurrence
of P_beta, but no claim of novelty is justified by that limited negative result.

Primary source: https://www.numdam.org/item/M2AN_1988__22_1_5_0.pdf
