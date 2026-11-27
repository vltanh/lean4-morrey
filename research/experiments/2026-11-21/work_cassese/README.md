# Cassese planar counterexample searches

**Outcome:** no validated counterexample to Morrey's 2×2 implication. These are numerical searches, not proofs that the tested families are quasiconvex.

## 1. Inherited rank-one convexity

Source: Gabriele Cassese, *A solution to Morrey's problem in R^(2×m)*, arXiv:2608.03488v3, https://arxiv.org/abs/2608.03488v3 . The associated public source https://github.com/Gabriele-Cassese/MorreyTwoComponentsLean/blob/main/Morrey2x3.lean states `h_rankOneConvex_small_delta`. The downloaded definitions were inspected; Lean was **not recompiled** here.

For a 2×3 matrix with rows (a,b,c),(d,e,f), set

- x=((a−c−e)/2,(b+d+f)/2), y=(d−f,e), u=(b,−a−c), z=((a−c+e)/2,(b−d−f)/2);
- q=(y∧u)^2−4(x∧u)(x∧y);
- L=2|x|²+|y|²+|u|², P=2|z|²;
- h=q+δ(L+Λ²P)^2, Λ=22/δ, 0<δ≤1.

The source's global rank-one convexity theorem passes to every f(A)=h(M+AB), B∈R^(2×3). No sampled rank-one constraints are needed for this inherited family.

### Corrected search method

Use eight integer Fourier directions (1,0),(0,1),(1,1),(1,−1),(2,1),(1,2),(2,−1),(1,−2), both phases, and two output amplitudes per phase. Normalize the mean weighted gradient energy, rather than separate raw parameter norms that permit a zero effective field. Whiten each mode using the positive definite quadratic L+Λ²P. Search orthonormal planes and nonorthonormal planes whose two characteristic light-cone directions almost coincide.

For any homogeneous quartic h and mean-zero gradient G,

J(M)=mean h(G)+mean Dh(G)·M + (1/2) Mᵀ(mean D²h(G))M.

This minimizes the base over **all six ambient entries**, rather than fixing the base at zero. The coefficient gradient follows from the envelope formula. The quartic Fourier integrals are exact on a 16×16 grid in exact arithmetic; floating computations were checked independently on a 27×27 grid using the original coordinate formula and stable quartic polarization.

Completed: 84 runs (12 variable-plane, 36 fixed-plane, 36 nearly tangent-plane), δ∈{1,.1,.01,.001}, tangent angles down to .001. All recorded gaps were positive. In the normalization mean(L+Λ²P)(G)=1, the smallest J/δ was approximately 0.999999996. This is far from a negative candidate. Original-formula verification disagreed by at most 1.3×10⁻¹¹, and mean gradients were below 7×10⁻¹⁷. Of 84 runs, 75 had an optimizer success flag; several variable-plane runs hit limits. None of these outcomes proves absence of other minima or counterexamples.

Files: `search.py`, `fixed_planes.py`, `tangent_planes.py`, `validate_results.py`, `validation_summary.json`, and their JSON records.

## 2. New planar SOS penalty search

To avoid the large inherited penalty, restrict q,L,P to A↦AB and optimize

f(A)=±q(AB)+αL(AB)^2+βL(AB)P(AB)+γP(AB)^2.

Global rank-one convexity is **not inherited automatically** after changing these coefficients. Instead, a floating SDP imposes the complete coefficient identity

D²f(A)[u⊗v,u⊗v] = z(A,u,v)ᵀQz(A,u,v), Q⪰0,

with the 16 monomials A_i u_j v_k. An exact identity with exact PSD Q would prove rank-one convexity. The floating SDP outputs in this folder are not exact certificates.

Alternate penalty optimization with normalized periodic continuous piecewise affine maps on a 5×5 triangulation, minimizing the planar base exactly at each field evaluation. The field derivative passed a finite-difference check with absolute error 4.9×10⁻¹².

### Recorded results and limitations

- Nonnegative α,β,γ: 80 completed alternating rounds across four planes, four starts, five rounds. No negative gap. The planned fifth, nearly singular plane failed in Clarabel and is excluded. The smallest raw gap +4.75×10⁻⁷ came with Gram minimum eigenvalue −8.34×10⁻⁵ and is **not an acceptable PSD result**. Among 60 records with coefficient residual≤10⁻⁸ and Gram eigenvalue≥−10⁻⁸, the smallest gap was +1.0476×10⁻⁵. Even this filter is numerical, not a certificate.
- Allow β free, both signs of q, and a 4×4 gradient-covariance log-determinant barrier: 96 completed rounds. Twenty-four rounds in plane 0 are excluded from meaningful minima because that family can cancel to the zero polynomial. Among the remaining 72, the smallest gap was +0.00289313; 55 pass the numerical diagnostic filter above. No negative candidate.

Files: `penalty_sos.py`, `penalty_barrier.py`, `lh_sos_core.py`, their logs/JSON records, and `penalty_summary.json`. `penalty_sos_best.npz` is the lowest **raw, unvalidated** first-pass record; `penalty_barrier_best.npz` is a **degenerate zero-integrand** record. Neither is a Morrey candidate.

## 3. Exact explanations of spurious promising minima

For B=[[1,0,0],[0,1,0]], exact symbolic identities are

q + (1/4)L² − LP + (3/4)P² ≡ 0,

−q − (1/2)LP + (3/2)P² = 4(det A)².

Consequently fixing the coefficient of q does not normalize the free-β family in that plane. Also, a positive definite covariance of the four entries of Du does not exclude rank-one-valued fields with det Du=0. Such fields can make the determinant-square Jensen gap zero while the entry covariance is well conditioned.

`exact_degeneracy.py` checks these identities in exact rational symbolic arithmetic, and verifies that the four polynomial generators have ranks [3,4,4,4,4] for the five proposed planes. These are explanations of search degeneracy, not new quasiconvexity results.

A general search should normalize the integrand (e.g. Gram trace) and control the covariance of entries **and quadratic monomials**, not only entries. Such controls should be relaxed before drawing any conclusion, since they change the numerical search objective.

## Reproduction

Python dependencies: numpy, scipy, sympy, cvxpy, clarabel. Run from this directory:

```
python search.py 0.1 6
python search.py 0.01 6
python fixed_planes.py
python tangent_planes.py
python validate_results.py
python penalty_sos.py
python penalty_barrier.py
python exact_degeneracy.py
```

The scripts use fixed random seeds. Exact floating values and SDP status can vary with solver versions. The last two SDP searches must never be described as exact rank-one-convex certificates without rational reconstruction and independent PSD/identity verification.
