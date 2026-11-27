# A global obstruction to the proposed quartic-generator proof of Morrey's conjecture

21 November 2026. Mathematical research note; **not a proof of the Morrey conjecture**.

## 1. An explicit global family

For every real beta >= 5/2, and A = [[a,b],[c,d]], put

    P_beta(A) = (ad - 2bc)^2 + beta (b^2 + c^2 + d^2)^2.

### Theorem 1

P_beta is a globally rank-one-convex homogeneous quartic, is the sum of two squares of quadratic polynomials, and P_beta(t E_11)=0 for every t. Yet P_beta is not polyconvex for any finite beta >= 5/2.

### Proof of rank-one convexity

For H = [[A,B],[C,D]] with det H=AD-BC=0, let

    y=(b,c,d), z=(B,C,D), L=cB+bC,
    T=aD-2L, S=dA.

A direct Hessian expansion gives the exact identity (valid even without det H=0)

    1/2 D^2 P_beta(M)[H,H]
    = T^2 +(S-2L)^2 -4L^2 +4bcBC
      + beta [2|y|^2|z|^2+4(y.z)^2]
      +4 det(H) det(M).

For rank-one H, the last term disappears. By Cauchy-Schwarz,

    L^2 <= (b^2+c^2)(B^2+C^2) <= |y|^2 |z|^2,
    4bcBC >= -(b^2+c^2)(B^2+C^2) >= -|y|^2 |z|^2.

Consequently,

    1/2 D^2 P_beta(M)[H,H]
    >= T^2 +(S-2L)^2+(2beta-5)|y|^2 |z|^2
       +4beta(y.z)^2 >=0.

The Legendre-Hadamard condition implies global rank-one convexity for a C^2 function.

### Proof of nonpolyconvexity

A globally finite polyconvex C^1 function f has, at each F, a supporting affine function in (A,det A). Equivalently there exists lambda such that

    f(F+X)-f(F)-Df(F)[X] >= lambda det X            (1)

for every X, because det(F+X)-det F-Ddet(F)[X]=det X.

Choose F=diag(M,1). Since P_beta(t E11)=0 for every real t, putting X=tE11-F in (1) and sending t to both positive and negative infinity forces lambda=2M (the a-derivative of P_beta at F is 2M).

Choose X=[[0,1],[1,0]]. Direct calculation gives

    P_beta(F+X)-P_beta(F)-DP_beta(F)[X]
        = -4M+4+8 beta,
    lambda det X = -2M.

The difference is -2M+4+8beta, which is negative when M>2+4beta. Therefore no polyconvex support exists at such F, and P_beta is not polyconvex. E.g. beta=3, M=20 gives -12.

### An explicit *finite* three-atom nonpolyconvexity witness

For beta=3, F=diag(20,1), take the probability measure with rational weights and support

| weight | matrix |
|---|---|
| 1/2 | [[20,1],[1,1]] |
| 1/41 | [[-20,0],[0,0]] |
| 39/82 | [[860/39,-41/39],[-41/39,41/39]] |

Exact calculation gives both minors constraints

    sum_i w_i A_i = F,     sum_i w_i det(A_i) = det F = 20,

but the strict inequality

    sum_i w_i P_3(A_i) - P_3(F) = -156317/59319 < 0.

Every globally polyconvex integrand satisfies Jensen's inequality for any finite
probability measure with these two minors constraints, so this provides an
independent, finite rational proof of nonpolyconvexity, not relying on existence
of a convex subgradient.

This is an obstruction to *polyconvexity*, not a counterexample to quasiconvexity: whether P_beta is quasiconvex at every F is not established by this note. At F=0 the quartic is nonnegative, so the Jensen inequality holds.

## 2. The known Dacorogna--Marcellini orbit is insufficient even after closure

For t in [-1,1] define

    W_t(A) = s(A)^2 +4t s(A) det A+(6t^2-2)(det A)^2,
    s(A)=|A|^2.

Write R4 for the cone of globally rank-one-convex homogeneous quartics, and PC4 for the cone of homogeneous quartics that are polyconvex. Define

    C_known = PC4 + cone{ W_t(L A R) : |t|<=1, L,R in GL_2(R)}.

The cited Bruno--Pasqualotto theorem makes all the displayed W_t quasiconvex. In fact the following structural obstruction does not require the details of their quasiconvexity proof.

### Theorem 2

    P_beta not in closure(C_known)

for every beta>=5/2 (closure in the ordinary 35-dimensional quartic coefficient topology).

### Proof, Step 1: compact base for the rank-one-convex quartic cone

Define the linear functional

    Lambda(P) = integral_{A in S^3} integral_{u,v in S^1}
                     D^2 P(A)[u tensor v,u tensor v] du dv dA,

with normalized spherical measures. For P in R4, the integrand is everywhere nonnegative. If Lambda(P)=0 then, by continuity, every rank-one directional second derivative vanishes for every A. In particular the pure second partial derivatives for the four matrix coordinates vanish identically. Since P is homogeneous quartic, this forces P(A)=c abcd. Applying the zero-Hessian condition at A=(1,1,1,1) and rank-one H=(1,1;1,1) gives c=0. Thus Lambda(P)>0 for every nonzero P in R4.

As R4 is a closed finite-dimensional cone, its base {P in R4:Lambda(P)=1} is compact. Indeed an unbounded sequence in this base would, after normalizing the coefficients, produce a nonzero Q in R4 with Lambda(Q)=0, impossible.

### Proof, Step 2: limits of orbit generators vanishing at E11 are convex

Let Q_n=alpha_n W_{t_n}(L_n A R_n) converge coefficientwise to Q, where alpha_n>=0, t_n in [-1,1] and L_n,R_n invertible. Absorb alpha_n^(1/4) into L_n, so write Q_n=W_{t_n}(T_n(A)), with T_n(A)=L_n A R_n. Define S_n(A)=|T_n(A)|^2 and delta_n=det L_n det R_n. Then

    Q_n(A)=S_n(A)^2 +4t_n delta_n S_n(A)det A
                   +(6t_n^2-2)delta_n^2(det A)^2.

For any rank-one matrix B, Q_n(B)=S_n(B)^2. If Q(E11)=0, then S_n(E11) ->0. Since Q_n(Eij) is bounded for each matrix unit Eij, S_n(Eij) and therefore the coefficients of the linear maps T_n are bounded. Passing to a subsequence, T_n converges to some linear map T. Hadamard's inequality gives

    |delta_n|^2 <= S_n(E11) S_n(E22) ->0.

Consequently Q(A)=|T(A)|^4=(|T(A)|^2)^2. This is convex as a function of A: |T(A)|^2 is convex and nonnegative, and x->x^2 is convex increasing on [0,infinity).

### Proof, Step 3: exposed face at a rank-one zero

Suppose for contradiction P_beta is in closure(C_known). Choose P_n in C_known converging coefficientwise to P_beta. By conic Caratheodory in dimension 35, write

    P_n = G_n + Q_{n,1}+ ... +Q_{n,35},

where G_n in PC4 and Q_{n,i} is either zero or a nonnegative multiple of an orbit generator.

Every summand lies in R4, hence Lambda>=0. Since Lambda(P_n) stays bounded, all summands stay in a common compact truncated base {Q in R4: Lambda(Q)<=C}. Taking subsequences, obtain coefficientwise limits G and Q_i.

Every homogeneous quartic R4 polynomial is nonnegative on rank-one matrices: P(sB)=s^4 P(B) convex in s forces P(B)>=0. Since P_beta(E11)=0, the values of *every* summand at E11 tend to zero. By Step 2, each Q_i is convex, hence polyconvex.

The cone PC4 is closed in coefficient space: polyconvexity is equivalent to finite-point Jensen inequalities for measures preserving the first-order entries and determinant; each such inequality is closed under coefficient convergence. Therefore G is polyconvex. Hence P_beta=G+sum_i Q_i is polyconvex, contradicting Theorem 1.

Thus P_beta lies outside the closed cone generated by all polyconvex quartics and all the known W_t transforms. QED.

## 3. Consequences for the Morrey research program

1. The previous proposal to prove all quartics by a positive representation using only polyconvex polynomials and the Bruno--Pasqualotto GL_2 x GL_2 orbit is mathematically impossible, **even with an arbitrary number of terms and coefficientwise closure**.
2. This obstruction is not due to finite-grid artifacts: it is in the entire infinite-dimensional class of periodic test maps and in the finite-dimensional *full* quartic coefficient cone.
3. A sufficient generator family for all rank-one-convex quartics must include genuinely new quasiconvex integrands with rank-one zeros that are **nonpolyconvex**. The family P_beta supplies concrete candidates, but this note has **not** proved their global quasiconvexity.
4. Even a complete proof for all quartics would not settle Morrey for all integrands. The original unrestricted conjecture and Pedregal's Theorems 1.1/1.2 remain open.

## Verification

Run `python morrey_rankone_zero_nonpolyconvex_verify.py` to check the exact polynomial Hessian identity and nonpolyconvex-support witness. The cone-closure argument above is a hand proof; it is not Lean-certified.

## Prior art

Global rank-one convexity without polyconvexity in 2x2 is well known (e.g. G. Aubert 1987, Dacorogna--Marcellini; later homogeneous examples). **Novelty of this specific rank-one-zero quartic family and of the cone-separation argument has not been established.** Existing quasiconvex generators: G. Bruno and F. Pasqualotto, arXiv:2608.06367 (2026).
