# Morrey 2×2 counterexample search — 21 November 2026

## Outcome

**No valid 2×2 counterexample was found.** The target remains a finite-valued,
globally rank-one-convex integrand f and an actual periodic gradient Du such that

    mean f(F+Du) - f(F) < 0.

The computations below search for this inequality. Positive attained values
are not rigorous lower bounds, and failure to find a counterexample does not
prove quasiconvexity. No Lean proof of Morrey's implication was produced.

## Completed work

| Route | Scope | Result |
|---|---|---|
| Anisotropic quartic P_beta=(ad−2bc)^2+beta(b²+c²+d²)^2 | Sharp admissible beta=2; 190 Fourier/FEM starts; all constant bases eliminated analytically | No negative gap |
| Dacorogna–Haeberly anisotropic degree-one energies | Two families; 472 periodic FEM optimizations on grids 4,8,16; 424 use fixed full-rank or conditioned bases | No negative gap |
| Cassese's inherited quartic family restricted to planar gradients | 84 Fourier optimizations; delta=1,.1,.01,.001; six ambient base entries eliminated analytically; nearly tangent planes included | No negative gap |
| New polynomial synthesis using global LH sum-of-squares constraints | Nonhomogeneous degree 4 and degree 6; 42 restarts and 222 alternating SDP/field steps | No negative gap |
| Additional planar Cassese penalty synthesis | 176 exploratory alternating rounds; numerical-feasibility and zero-integrand exclusions recorded | No validated candidate |

The counts refer to this round only. Restarts, alternating steps and parameter
families are different quantities and should not be summed into a purported
number of independent tests.

## Exact mathematical result used to strengthen the search

For the quartic already under investigation,

    P_beta(A)=(ad−2bc)^2+beta(b²+c²+d²)^2,

the exact rank-one-convexity threshold is beta>=2. The earlier sufficient
bound 5/2 was not sharp. The proof completes a square in the rank-one Hessian
and reduces the remainder to a 3×3 matrix with positive leading minors on the
chart H22!=0. Every minor is explicitly a positive sum of even monomials;
density covers H22=0. Adding (beta−2)(b²+c²+d²)^2 preserves convexity along
rank-one lines.

Sharpness is witnessed by

    M_t = [[2(t²−1), −1/t], [1, 2/t]],
    H_t = [[t³, t²], [t, 1]],  det H_t=0,

for which

    (1/2) D²P_beta(M_t)[H_t,H_t]
      = (2beta−4)t⁴+(12beta+4)t²+12beta+26beta/t².

For beta<2 this becomes negative for large t. The complete algebra, proof and
exact symbolic checker are in `work_pb/README.md` and `beta2_certificate.py`.
This is not a nonquasiconvexity result. Its priority has not been established.

At beta=2, the search normalized the transverse gradient energy
mean(b²+c²+d²)=1, because normalization of the full gradient allowed collapse
onto the flat E11 axis. The best recorded values were near 2. Ten cases,
including severely ill-conditioned base minimizations, were reevaluated at
60 digits with independent direct energy evaluation. None became negative.
The observed value 2 is not a proved lower bound.

## Global polynomial certificates and their limits

The synthesis searches for an exact-form identity

    D²f(A)[u tensor v,u tensor v] = z(A,u,v)^T Q z(A,u,v),   Q>=0,

where z consists of monomials in A multiplied by u_i v_j. An exact identity
and an exact PSD Gram matrix prove rank-one convexity for every A,u,v; a finite
list of sampled rank-one inequalities would not suffice.

Degree4 uses a 20×20 Gram matrix and degree 6 a 60×60 matrix. The models include
all nonaffine monomials up to their degree, subject to this sufficient SOS
condition. They do not cover every globally rank-one-convex function. The
search fixes trace Q=1 and a small positive Gram margin. Many solver returns
are marked `optimal_inaccurate`; the stored matrices are floating candidates,
not exact certificates. No negative 2×2 candidate was available to certify.

Periodic nodal maps are continuous and affine on equal-area triangles. Their
integrals are finite averages without spatial quadrature error. Fourier
searches use grids resolving all quartic frequencies; floating arithmetic
remains numerical.

The initial quartic optimizations found small positive gaps by concentrating
fields in degenerate sets. An entry-covariance barrier was insufficient:
det(Du)=0 can hold pointwise even with full 4×4 covariance. The final searches
therefore used covariance of entries and all quadratic monomials, with cubic
monomials added for degree 6. These barriers guide exploration; they are not
mathematical restrictions from which a universal conclusion is drawn.

## Exact known higher-dimensional control

The same synthesis on 3×2 matrices detects the standard Šverák mechanism with

    w(x,y)=(sin x,sin y,sin(x+y)).

The resulting polynomial and Gram matrix were reconstructed over the rationals.
An independent standard-library verifier checks the full coefficient identity,
positive definiteness of its42×42 Gram matrix by exact LDL decomposition, and
the exact negative average

    −103817049981/8000000000000.

Run `python work_sos/certify_control.py`. This is a control in the already-known
3×2 setting. It validates the computation; it is not a 2×2 counterexample.
The established higher-dimensional mechanism is described in the references
below, including the 1998 numerical paper's Example 4 and Section 6.4.

## Rejected or uninformative outputs

All are retained and labeled in the branch reports:

- Near-zero gaps from vanishing effective fields or rank-one-base affine rays.
- A planar Cassese family whose generators cancel to the zero polynomial.
- Determinant-square wells despite well-conditioned entry covariance.
- Several Cassese SDP outputs with negative Gram eigenvalues, and one solver
  failure at a nearly singular plane.
- Positive values from iterations that did not converge. These are attained
  values only, not certified local or global minima.

The Cassese branch's two raw `*_best.npz` files are explicitly unvalidated or
degenerate. They are not counterexample candidates. Its inherited-family
parameter bounds come from the source preprint and public formalization;
that Lean project was inspected but not rebuilt here.

## Prior work checked

These methods and candidate classes have substantial prior literature. This
package makes no novelty claim for numerical Morrey searches, Hessian-based
parameter optimization, or Fourier/finite-element tests.

1. Dacorogna–Haeberly, *On convexity properties of homogeneous functions of
   degree one*, Proc. Roy. Soc. Edinburgh126A(1996),947–956.
   https://doi.org/10.1017/S0308210500023180
   Primary text: https://doc.rero.ch/record/290415/files/S0308210500023180.pdf
   Supplies the anisotropic degree-one RC parameter conditions.
2. Dacorogna–Haeberly, *Some numerical methods for the study of the convexity
   notions arising in the calculus of variations*, M2AN32(1998),153–175.
   https://www.numdam.org/item/M2AN_1998__32_2_153_0.pdf
   Already tests these families numerically and recovers the 3×2 control.
3. Bandeira–Pedregal, *Finding new families of rank-one convex polynomials*,
   Ann. IHP AN26(2009),1621–1634.
   https://www.numdam.org/item/10.1016/j.anihpc.2008.08.002.pdf
   Already develops the homogeneous-quartic Hessian/generalized-eigenvalue
   reduction. Its displayed families do not include P_beta above.
4. Aubert, *Quelques remarques sur les notions de1-rang convexité et de
   polyconvexité en dimensions2 et3*, M2AN22(1988),5–28, Section 3.
   https://www.numdam.org/item/M2AN_1988__22_1_5_0.pdf
   Its isotropic positive-determinant example differs from P_beta.
5. Guerra–Teixeira da Costa, *Numerical evidence towards a positive answer
   to Morrey's problem*.
   https://arxiv.org/abs/2006.09063
   Prior numerical work on periodic-wave/laminate methods.
6. Cassese, *A solution to Morrey's problem in R^(2×m)*, v3,16 September 2026.
   https://arxiv.org/html/2608.03488v3
   Source for the 2×3 quartic construction; its 2×2 case is left open.
   Public formalization inspected:
   https://github.com/Gabriele-Cassese/MorreyTwoComponentsLean/blob/main/Morrey2x3.lean

Exact-expression searches did not locate P_beta's threshold in prior work,
but that is not an exhaustive novelty clearance. No claim of a publishable
new theorem's priority follows from this search.

## Archive layout and reproducibility

- `work_pb/`: sharp quartic certificate,190 searches, high-precision checks.
- `work_lit/`: two degree-one families,472 searches, independent SOS audit.
- `work_cassese/`: inherited-family and exploratory penalty searches, exclusions.
- `work_sos/`: global polynomial synthesis, raw records, exact3×2 control.

Branch READMEs give commands and normalization details. `requirements.txt`
lists dependencies. `manifest.json` records file digests. The exact3×2 verifier
needs only Python's standard library. Re-running numerical optimizers can
change floating values across solver versions.

**Research status:** better tested search machinery and a sharper parameter
boundary, but no proof or counterexample settling Morrey's 2×2 problem.
