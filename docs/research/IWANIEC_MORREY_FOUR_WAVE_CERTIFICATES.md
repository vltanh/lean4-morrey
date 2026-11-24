# Four-wave sawtooth laws in 2x2: resonance classification and first exact laminate certificates

**Status.** AI-produced (Claude), unreviewed, not formalised in Lean, novelty not verified against the literature.
**This note does not prove Morrey's conjecture in 2x2 and does not prove the four-wave case.** It proves
statements about explicit instances, each by a finite list of rank-one convexity inequalities that can be
checked by hand, and it records which four-wave laws a proof would have to handle.

Companion notes: [`IWANIEC_MORREY_FOUR_WAVE_CASES.md`](IWANIEC_MORREY_FOUR_WAVE_CASES.md),
[`IWANIEC_MORREY_FOUR_WAVE_PARITY_THEOREM.md`](IWANIEC_MORREY_FOUR_WAVE_PARITY_THEOREM.md),
[`IWANIEC_MORREY_GENERAL_LOGIC_DIRECTIONS.md`](IWANIEC_MORREY_GENERAL_LOGIC_DIRECTIONS.md).

## 0. Summary

1. (Section 2, proved.) For four pairwise non-parallel integer frequencies, at most two of the four triples
   carry a three-wave resonance; if two do, there is no four-wave resonance. So a four-wave sign law has at
   most two non-zero Walsh coefficients beyond the constant. Apart from product laws, three-wave laws and
   pure four-wave parity laws (the subject of the parity note), exactly two families remain: **type D** (two
   resonant triples) and **type TQ** (one resonant triple plus a four-term resonance).
2. (Section 2, proved.) The corner law D with both triple moments equal to 1/2 in modulus occurs for exactly
   one frequency quadruple up to linear change of variables, `(1,0),(0,1),(1,1),(1,-1)`, at quarter phases. It
   is the gradient law of an explicit map, so it is a necessary case of Morrey's conjecture. The version of
   (D) "for arbitrary rank-one quadruples" is stronger than what the conjecture needs.
3. (Section 3, proved; hand-checkable.) At the equal-amplitude Hessian quadruple both corner laws are
   laminates. Consequently, for all phases `c3, c4`, the map `grad psi`,
   `psi = T(x) + T(y) + T(x+y+c3) + T(x-y+c4)`, satisfies the quasiconvexity inequality for every rank-one
   convex integrand.
4. (Section 4, computed with exact arithmetic.) The same holds at five further amplitude choices; one corner
   type is certified at seven more; a realised TQ-type law that lies outside everything obtainable from the
   three-wave theorem by conditioning is a laminate at equal amplitudes. One amplitude choice was left
   unresolved by the small search (no conclusion either way).
5. (Section 5.) Polynomial tests of degree at most 6 are too weak to be informative here, and the laminate
   range of three-wave parity laws is strictly larger than the range realised by sawtooth maps for an
   unbalanced triple.

## 1. Setting

`s` is the 1-periodic sawtooth with `s' = sigma`, `sigma = +1` on `[0,1/2)`, `-1` on `[1/2,1)`; `T' = s`.
An N-wave map is `phi(x) = sum_i a_i s(n_i.x + c_i)` with `a_i in R^2`, `n_i in Z^2`. Its gradient is
`sum_i eps_i H_i`, `H_i = a_i (x) n_i`, `eps_i = sigma(n_i.x + c_i)`, so the gradient distribution is a
probability law `p` on the vertices of the cube `{sum e_i H_i}`, with Walsh coefficients
`C_S = E[prod_{i in S} eps_i]`:

    p(e) = 2^{-N} sum_S C_S e_S.

Guerra and Teixeira da Costa (arXiv:2006.09063, Rev. Mat. Iberoam. 38 (2022)) reduce quasiconvexity to these
laws (N-wave quasiconvexity for all N); the case N = 3 in 2x2 is the theorem of Sebestyen and Szekelyhidi
(J. Convex Anal. 24 (2017), arXiv:1504.06516); N >= 4 is, to my knowledge, open. As of the preprints I could find (Cassese,
arXiv:2608.03488v3, Sept. 2026, which gives rank-one convex non-quasiconvex integrands on `R^{2x3}`), the 2x2
problem itself is still open.

**Lemma 1 (certificate).** Let `p` be a finitely supported probability measure on `R^{2x2}` with barycentre
`A`. Suppose there are finitely many splits `P_k = w_k A_k + (1-w_k) B_k`, `0 < w_k < 1`,
`rank(A_k - B_k) <= 1`, and masses `x_k >= 0` with

    sum_k x_k ( w_k delta_{A_k} + (1-w_k) delta_{B_k} - delta_{P_k} ) = p - delta_A .

Then `E_p f >= f(A)` for every `f` that is rank-one convex on the convex hull of the points.

*Proof.* Multiply `f(P_k) <= w_k f(A_k) + (1-w_k) f(B_k)` by `x_k` and add. QED

A table of splits with masses is therefore a complete proof; no tree structure is needed. Convex combinations
of certified measures with the same barycentre are certified.

**Hessian model.** If `a_i = r_i n_i` then `phi = grad psi`, `psi = sum r_i T(n_i.x + c_i)`, and all
gradients are symmetric. A symmetric matrix `[[s+d, h],[h, s-d]]` is written `(s,d,h)`; its determinant is
`s^2 - d^2 - h^2`, and a segment is rank-one iff its direction `(Ds,Dd,Dh)` satisfies `Ds^2 = Dd^2 + Dh^2`.
For the frequencies `(1,0),(0,1),(1,1),(1,-1)`:

    n1 (x) n1 = (1/2, 1/2, 0),  n2 (x) n2 = (1/2, -1/2, 0),  n3 (x) n3 = (1, 0, 1),  n4 (x) n4 = (1, 0, -1).

The maps `(s,d,h) -> (s,-d,h)`, `(s,d,-h)`, `(-s,d,h)`, `-(s,d,h)` preserve the determinant, hence map
certificates to certificates.

## 2. Which four-wave laws occur

Write `nu_ij = n_i x n_j` (2D cross product) and `v(.)` for the 2-adic valuation. Since
`sigma(t) = sum_{k odd} (2/(pi i k)) e^{2 pi i k t}`,

    C_S = sum over odd integers (k_i)_{i in S} with sum k_i n_i = 0 of prod (2/(pi i k_i)) e^{2 pi i k_i c_i}.

For pairwise non-parallel frequencies `C_i = C_ij = 0`. Three vectors of `Z^2` have one primitive relation
`kappa_i n_i + kappa_j n_j + kappa_k n_k = 0`, and `C_ijk != 0` requires all three `kappa` odd, i.e.
`v(nu_ij) = v(nu_ik) = v(nu_jk)` (an *odd triple*). Summing the series (`sum_{m odd} sin(m x)/m^3 =
pi x (pi - x)/8`) gives

    C_ijk = -(4 / (kappa_i kappa_j kappa_k)) g(theta),  theta = sum kappa_l c_l,
    g(t) = t(1-2t) on [0,1/2],  g(t + 1/2) = -g(t),

so `|C_ijk| <= 1/(2 |kappa_i kappa_j kappa_k|) <= 1/2`, every value in between is attained, and `1/2` is
attained only for `kappa = (+-1,+-1,+-1)` at `theta = +-1/4`.

**Lemma 2.** Let `n_1..n_4 in Z^2` be pairwise non-parallel.
(a) At most two of the four triples are odd.
(b) If `{1,2,3}` and `{1,2,4}` are odd, there is no relation `sum k_i n_i = 0` with all four `k_i` odd; hence
`C_1234 = 0`, and also `C_134 = C_234 = 0`.

*Proof.* (a) Two distinct triples share two indices, so let `{1,2,3}` and `{1,2,4}` be odd, `v = v(nu_12) = v(nu_13) = v(nu_23) = v(nu_14) = v(nu_24)`.
The Pluecker relation `nu_12 nu_34 = nu_13 nu_24 - nu_14 nu_23` has a right side of valuation `> 2v`
(difference of two numbers of valuation exactly `2v`), so `v(nu_34) > v` and neither `{1,3,4}` nor `{2,3,4}`
is odd. (b) Cross the relation with `n_2`: `k_1 nu_12 + k_3 nu_32 + k_4 nu_42 = 0`. Each term has valuation
exactly `v`, and a sum of three such numbers has valuation exactly `v`, so it is not zero. QED

**Corollary 3 (the list).** A four-wave sign law with pairwise non-parallel frequencies is one of:

| type | non-zero coefficients | status |
|---|---|---|
| product | none | laminate (iterated rank-one splits) |
| one odd triple, no four-term resonance | `C_123` | laminate (three-wave theorem and one more split) |
| four-term resonance only | `C_1234` | pure parity law; see the parity note |
| **D** | `C_123`, `C_124` (every point of the rectangle given by the two bounds above) | open |
| **TQ** | `C_123`, `C_1234` | open |

The law is affine in its coefficients, so in type D it is enough to treat the four corners of the rectangle.
Conditioning on one sign and using the three-wave theorem gives only the diamonds
`|C_123| + |C_124| <= 1/2`, resp. `|C_123| + |C_1234| <= 1/2`.

**Corollary 4 (where the corner law lives).** Both triple moments reach modulus `1/2` iff both primitive
relations have coefficients `+-1`, i.e. `{n_3, n_4} = {+-(n_1+n_2), +-(n_1-n_2)}`. After a linear change of
variables this is `(1,0),(0,1),(1,1),(1,-1)` (the four directions form a harmonic quadruple), with phases
`c_1 + c_2 - c_3 = +-1/4`, `c_1 - c_2 - c_4 = +-1/4` mod 1. For instance

    phi = a_1 s(x) + a_2 s(y) + a_3 s(x+y+1/4) + a_4 s(x-y+1/4)   has   (C_123, C_124) = (-1/2, +1/2)

(checked exactly: twelve gradients, four of weight 1/8 and eight of weight 1/16). Hence:

* the corner inequality (D) for `H_i = a_i (x) n_i` with these four directions and arbitrary `a_i` is
  **necessary** for Morrey's conjecture;
* for other odd configurations (for example `n_4 = n_1 - 3 n_2`) only the smaller rectangle is needed
  (`|C_124| <= 1/6`), which is still outside the diamond;
* (D) for *arbitrary* rank-one quadruples, as stated in the four-wave cases note, is a sufficient target that
  Morrey's conjecture does not imply. I do not know whether it is true for non-harmonic direction quadruples.

Similarly, for the frequencies `(1,0),(0,1),(1,1),(2,-2)` and phases `(0,0,1/4,1/4)` one gets exactly
`(C_123, C_1234) = (-1/2, 1/4)`: conditional on `eps_4 = -1` the three-wave parity is `-3/4`.

## 3. The equal-amplitude Hessian quadruple

Take `H_1 = (1/2,1/2,0)`, `H_2 = (1/2,-1/2,0)`, `H_3 = (1,0,1)`, `H_4 = (1,0,-1)` and the points

    P1 = (3,0,0)   P2 = (1,0,0)   P3 = (-2,1,0)   P4 = (-2,-1,0)
    E = (1,0,2)    E' = (1,0,-2)  W = (-1,0,2)    W' = (-1,0,-2)
    N = (0,1,2)    N' = (0,1,-2)  S = (0,-1,2)    S' = (0,-1,-2).

The corner law with `(C_123, C_124) = (1/2, 1/2)` is

    D++ = 1/8 on P1, P2, P3, P4  and  1/16 on E, E', W, W', N, N', S, S'.

**Theorem 5.** `D++` satisfies `E f >= f(0)` for every rank-one convex `f`. The same holds for the corner law
`D-+` with `(C_123, C_124) = (-1/2, 1/2)`, hence (apply `X -> -X`) for all four corners.

*Proof for `D++`.* Three steps; every segment used is rank-one (`Ds^2 = Dd^2 + Dh^2`).

*Step 1 (a planar laminate with barycentre P2).* Let `G = (2,0,-1)`. Then `P2 = (1/3) W + (2/3) G`
(direction `(3,0,-3)`) and `G = (1/2) P1 + (1/2) E'` (direction `(2,0,2)`), so
`m1 = (1/3)(delta_W + delta_P1 + delta_E')` is a laminate with barycentre `P2`; so is its mirror image under
`h -> -h`, `m2 = (1/3)(delta_W' + delta_P1 + delta_E)`. Put

    L_A = (1/4) delta_P2 + (3/8) m1 + (3/8) m2 = { P1: 1/4, P2: 1/4, E, E', W, W': 1/8 each }.

*Step 2 (a laminate from 0 on seven points).* Let `A = (1/3) P3 + (2/3) N = (-2/3, 1, 4/3)` and
`A' = (1/3) P3 + (2/3) N' = (-2/3, 1, -4/3)`; `P3N` and `P3N'` are rank-one segments, and `P2 - A =
(5/3, -1, -4/3)` is rank-one. Define

    X1 = (4/5) P2 + (1/5) A  = (2/3, 1/5, 4/15),     Y1 = (2/11) P3 + (9/11) A' = (-10/11, 1, -12/11),
    X2 = (2/5) P2 + (3/5) A  = (0, 3/5, 4/5),        Y2 = (4/7) P3 + (3/7) A'   = (-10/7, 1, -4/7).

`X1 - Y1` is proportional to `(65,-33,56)` and `X2 - Y2` to `(25,-7,24)`; both are rank-one
(`65^2 = 33^2 + 56^2`, `25^2 = 7^2 + 24^2`). Moreover

    Z1 := (45/56) X1 + (11/56) Y1 = (5/14, 5/14, 0),      Z2 := (5/12) X2 + (7/12) Y2 = (-5/6, 5/6, 0).

Splitting `Z1 -> X1, Y1 -> P2, A, P3, A' -> P2, P3, N, N'` gives a laminate with barycentre `Z1`,

    mu1 = { P2: 9/14, P3: 1/7, N: 3/28, N': 3/28 },   and likewise   mu2 = { P2: 1/6, P3: 1/2, N: 1/6, N': 1/6 }

with barycentre `Z2`. Let `*` denote the mirror image under `d -> -d` (it swaps `P3,P4`, `N,S`, `N',S'` and
fixes `P2`). Since `0 = (7/10) Z1 + (3/10) Z2*` along the rank-one direction `(1,1,0)`,

    L = (7/10) mu1 + (3/10) mu2* = { P2: 1/2, P3: 1/10, N, N': 3/40, P4: 3/20, S, S': 1/20 }

is a laminate with barycentre 0, and so is `L*`. Their average is

    sigma = { P2: 1/2, P3: 1/8, P4: 1/8, N, N', S, S': 1/16 each }.

*Step 3.* Replacing the atom at `P2` in `sigma` by `L_A` gives exactly `D++`. By Lemma 1 (or directly, by
adding the inequalities of steps 1 and 2), `E_{D++} f >= E_sigma f >= f(0)`. QED

*Proof for `D-+`.* By the 28-row certificate of Appendix A and Lemma 1. (In the coordinates above `D-+` has
weight 1/8 on `(1,0,-2), (-1,0,-2), (0,1,2), (0,-1,2)` and 1/16 on `(+-3,0,0), (+-1,0,0), (+-2,+-1,0)`.) QED

**Corollary 6.** Let `psi(x,y) = T(x) + T(y) + T(x+y+c3) + T(x-y+c4)`. For all `c3, c4`, every symmetric `A`
and every rank-one convex `f`,

    integral over the torus of f(A + D^2 psi) >= f(A).

*Proof.* The law of `D^2 psi` is `(1/16)(1 + C_123 e_123 + C_124 e_124)` with `(C_123, C_124)` in
`[-1/2,1/2]^2` (Lemma 2 and the formula for `C_ijk`), a convex combination of the four corner laws. Changing
the signs of amplitudes is a change of phases by 1/2. QED

Remarks. (i) Weights in step 2 are forced: a measure on those seven points that is symmetric under
`d -> -d`, `h -> -h`, has barycentre 0 and integrates the determinant to 0 must be `sigma`. (ii) The
construction follows the method of Sebestyen and Szekelyhidi: `Z1` and `Z2*` are the points where the rank-one
line through 0 in the direction of wave 1 meets the doubly ruled surface through the rank-one quadrilateral
`P2, A, P3, A'` and its mirror image. (iii) None of the reductions to the three-wave theorem that I tried
produces `D++` (conditioning on a sign creates a pair correlation; collapsing a wave by Jensen leaves a four-point law
with non-zero mean determinant).

## 4. Further certified instances (exact arithmetic, computed)

Amplitudes `(r1,r2,r3,r4)` mean `H_i = r_i n_i (x) n_i`. "++" is the corner `(1/2,1/2)`; "+-" is the corner
`(1/2,1/2)` at amplitudes `(r1,r2,r3,-r4)`, i.e. the corner `(1/2,-1/2)`; together with `X -> -X` these give
all four corners. Each entry is the number of splits in
a certificate in the sense of Lemma 1 whose mass balance was re-solved and checked in rational arithmetic.

| amplitudes | ++ | +- |
|---|---|---|
| (1,1,1,1) | Theorem 5 | 28 (Appendix A) |
| (2,1,1,1) | 38 | 9 (below) |
| (1,1,2,1) | 31 | 36 |
| (1,1,2,2) | 29 | 32 |
| (2,2,1,1) | 31 | 12 |
| (1,2,3,1) | 26 | 34 |
| (3,1,2,1) | not found by the small search | 38 |
| (3/4,1,1,1), (7/8,1,1,1), (9/8,1,1,1), (5/4,1,1,1), (3/2,1,1,1), (1,1,1,3) | 53, 56, 50, 56, 50, 36 | not attempted |

So Corollary 6 holds for `psi = sum r_i T(...)` with each of the first six amplitude vectors. "Not found" is not evidence of failure:
the same search first missed `(2,1,1,1)++` and `(2,2,1,1)++` and found them once more candidate points were
allowed.

*How they were found.* Candidate points: the support, the points of rank-one edges that are rank-one
connected to a support point, and the points where ruled surfaces through rank-one quadrilaterals with
determinants of opposite sign on the diagonals meet rank-one lines through 0; then one linear programme for
the masses; then the exact check. Only the tables below are reproduced here; the others are available.

**Example (amplitudes (2,1,1,1), corner +-): nine splits.** Here `H_1 = (1,1,0)`, `H_2 = (1/2,-1/2,0)`,
`H_3 = (1,0,1)`, `H_4 = (-1,0,1)`; the law has weight 1/8 on `(3/2,1/2,2), (-3/2,-1/2,2), (1/2,3/2,-2),
(-1/2,-3/2,-2)` and 1/16 on `(7/2,1/2,0), (-1/2,1/2,0), (1/2,-1/2,0), (-7/2,-1/2,0), (5/2,3/2,0),
(-3/2,3/2,0), (3/2,-3/2,0), (-5/2,-3/2,0)`.

| # | mass | point P | A (weight) | B (weight) |
|---|---|---|---|---|
| 1 | 1/2 | (0, 0, 0) | (-1/2, 1/2, 0) (1/2) | (1/2, -1/2, 0) (1/2) |
| 2 | 3/8 | (-1/2, 1/2, 0) | (7/6, 3/2, -4/3) (1/2) | (-13/6, -1/2, 4/3) (1/2) |
| 3 | 3/8 | (1/2, -1/2, 0) | (13/6, 1/2, 4/3) (1/2) | (-7/6, -3/2, -4/3) (1/2) |
| 4 | 1/4 | (0, 0, 0) | (-1/2, 1/2, 0) (3/4) | (3/2, -3/2, 0) (1/4) |
| 5 | 1/4 | (0, 0, 0) | (-3/2, 3/2, 0) (1/4) | (1/2, -1/2, 0) (3/4) |
| 6 | 3/16 | (-13/6, -1/2, 4/3) | (-3/2, -1/2, 2) (2/3) | (-7/2, -1/2, 0) (1/3) |
| 7 | 3/16 | (-7/6, -3/2, -4/3) | (-5/2, -3/2, 0) (1/3) | (-1/2, -3/2, -2) (2/3) |
| 8 | 3/16 | (7/6, 3/2, -4/3) | (5/2, 3/2, 0) (1/3) | (1/2, 3/2, -2) (2/3) |
| 9 | 3/16 | (13/6, 1/2, 4/3) | (3/2, 1/2, 2) (2/3) | (7/2, 1/2, 0) (1/3) |

Rows 1, 4, 5 split 0 along wave 2; rows 2, 3 use the new direction `(5,3,+-4)`, i.e. the matrix
`(2,+-1) (x) (2,+-1)`; rows 6 to 9 are along waves 3 and 4.

**A realised TQ-type law.** At equal amplitudes the law `(1/16)(1 + e_123(-1/2 + e_4/4))`, which is the
gradient law of `grad [ T(x) + T(y) + T(x+y+1/4) + (1/4) T(2x-2y+1/4) ]`, has a 62-split certificate
(Appendix B); its sign variant `(1/2, 1/4)` has a 63-split certificate (not reproduced). The corner
`(-1/2, 1/2)` of the TQ square was not found by the same search; I do not know whether any map realises it.

## 5. Remarks and limits

1. **Low-degree polynomial tests are weak.** I minimised `E_p f - f(0)` over polynomials of degree at most
   6 on symmetric matrices that are rank-one convex on a ball containing the support (sum-of-squares
   certificate with one multiplier). For the three-wave parity law at equal amplitudes the minimum is 0 for
   parity 0.5, 0.55, 0.6, 0.75 and negative at parity 1. I do not know the true laminate threshold for this
   triple, so this proves nothing by itself; but the earlier "no quartic violation" observations should not
   be read as evidence.
2. **Laminates reach beyond the sawtooth range.** Sawtooth maps realise three-wave parity at most 1/2 for
   every triple (Section 2). For the Hessian triple with amplitudes (2,1,1), i.e.
   `(d12,d13,d23) = (2,2,1)`, the parity law with parity 3/5 has an exact 10-split certificate (computed, not
   reproduced). So the constant 1/2 of the three-wave theorem is not the laminate threshold for unbalanced
   triples, and a conditional parity above 1/2 (as in the TQ-type law) is not automatically an obstruction.
3. **What is not proved.** (D) for general amplitudes, even in the Hessian model; anything for
   non-symmetric amplitude vectors `a_i` (a four-dimensional problem; the harmonic Hessian model is the
   codimension-one subfamily where the directions of the `a_i` also form a harmonic quadruple); type TQ in
   general; all N >= 5. The certificates change combinatorially with the amplitudes and I have no uniform
   construction.
4. **Computations used.** A few dozen small linear programmes and semidefinite programmes (most take
   seconds, the largest about six minutes; two attempts were abandoned after ten minutes), plus exact rational
   verification of every certificate quoted. No certificate depends on floating point.

## References

* A. Guerra, R. Teixeira da Costa, Numerical evidence towards a positive answer to Morrey's problem,
  Rev. Mat. Iberoam. 38 (2022), arXiv:2006.09063.
* G. Sebestyen, L. Szekelyhidi Jr., Laminates supported on cubes, J. Convex Anal. 24 (2017), arXiv:1504.06516.
* G. Cassese, A solution to Morrey's problem in R^{2xm}, arXiv:2608.03488 (v3, Sept. 2026).
* P. Pedregal, Laminates and microstructure, European J. Appl. Math. 4 (1993).

## Appendix A. Certificate for the corner law `D-+` at equal amplitudes

Target: 1/8 on `(1,0,-2), (-1,0,-2), (0,1,2), (0,-1,2)`; 1/16 on `(3,0,0), (1,0,0), (2,1,0), (2,-1,0),
(-3,0,0), (-1,0,0), (-2,1,0), (-2,-1,0)`. Each row: `P = w_A A + w_B B` with `A - B` rank-one, carrying the
stated mass. Mass balance: for every point, (mass arriving) - (mass leaving) equals its target weight, and
equals -1 at `(0,0,0)`.

| # | mass | point P | A (weight) | B (weight) |
|---|---|---|---|---|
| 1 | 5/21 | (0, 0, 0) | (-3/4, 3/4, 0) (1/2) | (3/4, -3/4, 0) (1/2) |
| 2 | 5/21 | (0, 0, 0) | (-3/4, -3/4, 0) (1/2) | (3/4, 3/4, 0) (1/2) |
| 3 | 13/96 | (0, 0, 0) | (3/2, 0, -3/2) (56/143) | (-28/29, 0, 28/29) (87/143) |
| 4 | 13/96 | (0, 0, 0) | (-3/2, 0, -3/2) (56/143) | (28/29, 0, 28/29) (87/143) |
| 5 | 85/672 | (0, 0, 0) | (-1/2, 0, -1/2) (56/85) | (28/29, 0, 28/29) (29/85) |
| 6 | 85/672 | (0, 0, 0) | (1/2, 0, -1/2) (56/85) | (-28/29, 0, 28/29) (29/85) |
| 7 | 29/231 | (-28/29, 0, 28/29) | (39/158, 143/158, 140/79) (237/754) | (-143/94, -39/94, 28/47) (517/754) |
| 8 | 29/231 | (28/29, 0, 28/29) | (143/94, -39/94, 28/47) (517/754) | (-39/158, 143/158, 140/79) (237/754) |
| 9 | 5/42 | (-3/4, -3/4, 0) | (6/5, 0, -9/5) (1/4) | (-7/5, -1, 3/5) (3/4) |
| 10 | 5/42 | (-3/4, 3/4, 0) | (6/5, 0, -9/5) (1/4) | (-7/5, 1, 3/5) (3/4) |
| 11 | 5/42 | (3/4, -3/4, 0) | (-6/5, 0, -9/5) (1/4) | (7/5, -1, 3/5) (3/4) |
| 12 | 5/42 | (3/4, 3/4, 0) | (-6/5, 0, -9/5) (1/4) | (7/5, 1, 3/5) (3/4) |
| 13 | 5/56 | (-7/5, -1, 3/5) | (0, -1, 2) (3/10) | (-2, -1, 0) (7/10) |
| 14 | 5/56 | (-7/5, 1, 3/5) | (0, 1, 2) (3/10) | (-2, 1, 0) (7/10) |
| 15 | 5/56 | (7/5, -1, 3/5) | (0, -1, 2) (3/10) | (2, -1, 0) (7/10) |
| 16 | 5/56 | (7/5, 1, 3/5) | (0, 1, 2) (3/10) | (2, 1, 0) (7/10) |
| 17 | 47/546 | (-143/94, -39/94, 28/47) | (0, -1, 2) (39/94) | (-13/5, 0, -2/5) (55/94) |
| 18 | 47/546 | (143/94, -39/94, 28/47) | (0, -1, 2) (39/94) | (13/5, 0, -2/5) (55/94) |
| 19 | 1/12 | (-1/2, 0, -1/2) | (1, 0, -2) (1/4) | (-1, 0, 0) (3/4) |
| 20 | 1/12 | (1/2, 0, -1/2) | (-1, 0, -2) (1/4) | (1, 0, 0) (3/4) |
| 21 | 5/84 | (-6/5, 0, -9/5) | (-1, 0, -2) (9/10) | (-3, 0, 0) (1/10) |
| 22 | 5/84 | (6/5, 0, -9/5) | (1, 0, -2) (9/10) | (3, 0, 0) (1/10) |
| 23 | 25/462 | (-13/5, 0, -2/5) | (-1, 0, -2) (1/5) | (-3, 0, 0) (4/5) |
| 24 | 25/462 | (13/5, 0, -2/5) | (1, 0, -2) (1/5) | (3, 0, 0) (4/5) |
| 25 | 7/132 | (-3/2, 0, -3/2) | (-1, 0, -2) (3/4) | (-3, 0, 0) (1/4) |
| 26 | 7/132 | (3/2, 0, -3/2) | (1, 0, -2) (3/4) | (3, 0, 0) (1/4) |
| 27 | 79/2002 | (-39/158, 143/158, 140/79) | (0, 1, 2) (143/158) | (-13/5, 0, -2/5) (15/158) |
| 28 | 79/2002 | (39/158, 143/158, 140/79) | (0, 1, 2) (143/158) | (13/5, 0, -2/5) (15/158) |

## Appendix B. Certificate for the realised TQ-type law at equal amplitudes

Target: `(1/16)(1 + e_123(-1/2 + e_4/4))` on the sixteen points `sum e_i H_i`.

| # | mass | point P | A (weight) | B (weight) |
|---|---|---|---|---|
| 1 | 73/218 | (0, 0, 0) | (-3/4, 0, -3/4) (1/2) | (3/4, 0, 3/4) (1/2) |
| 2 | 405/1744 | (0, 0, 0) | (-3/2, 0, -3/2) (1/3) | (3/4, 0, 3/4) (2/3) |
| 3 | 199/872 | (0, 0, 0) | (-3/4, 0, 3/4) (2/3) | (3/2, 0, -3/2) (1/3) |
| 4 | 189/872 | (-3/4, 0, 3/4) | (-8/9, 1/9, 2/3) (45/56) | (-2/11, -5/11, 12/11) (11/56) |
| 5 | 1215/6976 | (-8/9, 1/9, 2/3) | (-13/9, -4/9, 2/3) (4/9) | (-4/9, 5/9, 2/3) (5/9) |
| 6 | 893/5232 | (3/4, 0, 3/4) | (2/11, 5/11, 12/11) (11/16) | (2, -1, 0) (5/16) |
| 7 | 169/1308 | (0, 0, 0) | (-3/4, 0, 3/4) (1/2) | (3/4, 0, -3/4) (1/2) |
| 8 | 14/109 | (-3/4, 0, -3/4) | (-8/9, 1/9, -2/3) (45/56) | (-2/11, -5/11, -12/11) (11/56) |
| 9 | 9823/83712 | (2/11, 5/11, 12/11) | (-1, 0, 0) (3/11) | (5/8, 5/8, 3/2) (8/11) |
| 10 | 45/436 | (-8/9, 1/9, -2/3) | (-9/7, 0, -2/7) (7/9) | (1/2, 1/2, -2) (2/9) |
| 11 | 675/6976 | (-4/9, 5/9, 2/3) | (-20/11, -1/11, -6/11) (11/27) | (1/2, 1, 3/2) (16/27) |
| 12 | 155/1744 | (3/2, 0, -3/2) | (1, 0, -2) (3/4) | (3, 0, 0) (1/4) |
| 13 | 893/10464 | (5/8, 5/8, 3/2) | (0, 1, 2) (3/4) | (5/2, -1/2, 0) (1/4) |
| 14 | 35/436 | (-9/7, 0, -2/7) | (-2, 0, -1) (2/7) | (-1, 0, 0) (5/7) |
| 15 | 135/1744 | (-3/2, 0, -3/2) | (-3, 0, 0) (1/4) | (-1, 0, -2) (3/4) |
| 16 | 135/1744 | (-13/9, -4/9, 2/3) | (-13/5, 0, -2/5) (5/9) | (0, -1, 2) (4/9) |
| 17 | 781/10464 | (-2/11, -5/11, 12/11) | (-5/8, -5/8, 3/2) (8/11) | (1, 0, 0) (3/11) |
| 18 | 63/872 | (-3/4, 0, -3/4) | (-8/9, -1/9, -2/3) (45/56) | (-2/11, 5/11, -12/11) (11/56) |
| 19 | 61/872 | (3/4, 0, 3/4) | (0, -3/5, 6/5) (5/8) | (2, 1, 0) (3/8) |
| 20 | 405/6976 | (-8/9, -1/9, -2/3) | (-13/9, 4/9, -2/3) (4/9) | (-4/9, -5/9, -2/3) (5/9) |
| 21 | 25/436 | (1/2, 1, 3/2) | (0, 1, 2) (3/4) | (2, 1, 0) (1/4) |
| 22 | 71/1308 | (-5/8, -5/8, 3/2) | (-5/2, 1/2, 0) (1/4) | (0, -1, 2) (3/4) |
| 23 | 131/2616 | (3/4, 0, -3/4) | (2/11, -5/11, -12/11) (11/16) | (2, 1, 0) (5/16) |
| 24 | 131/2616 | (3/4, 0, 3/4) | (2/11, -5/11, 12/11) (11/16) | (2, 1, 0) (5/16) |
| 25 | 87/1744 | (0, 0, 0) | (-3/4, 0, -3/4) (2/3) | (3/2, 0, 3/2) (1/3) |
| 26 | 305/6976 | (0, -3/5, 6/5) | (-2/11, -5/11, 12/11) (11/15) | (1/2, -1, 3/2) (4/15) |
| 27 | 75/1744 | (-13/5, 0, -2/5) | (-3, 0, 0) (4/5) | (-1, 0, -2) (1/5) |
| 28 | 275/6976 | (-20/11, -1/11, -6/11) | (-5/2, -1/2, 0) (8/11) | (0, 1, -2) (3/11) |
| 29 | 1441/41856 | (2/11, -5/11, -12/11) | (-1, 0, 0) (3/11) | (5/8, -5/8, -3/2) (8/11) |
| 30 | 1441/41856 | (2/11, -5/11, 12/11) | (-1, 0, 0) (3/11) | (5/8, -5/8, 3/2) (8/11) |
| 31 | 225/6976 | (-4/9, -5/9, -2/3) | (-20/11, 1/11, 6/11) (11/27) | (1/2, -1, -3/2) (16/27) |
| 32 | 55/1744 | (3/4, 0, 3/4) | (-1/2, 1, 3/2) (1/10) | (8/9, -1/9, 2/3) (9/10) |
| 33 | 1/32 | (-5/2, -1/2, 0) | (-3, 0, 0) (1/2) | (-2, -1, 0) (1/2) |
| 34 | 99/3488 | (8/9, -1/9, 2/3) | (-1/2, -1/2, 2) (2/9) | (9/7, 0, 2/7) (7/9) |
| 35 | 145/5232 | (-5/2, 1/2, 0) | (-3, 0, 0) (1/2) | (-2, 1, 0) (1/2) |
| 36 | 45/1744 | (-13/9, 4/9, -2/3) | (-13/5, 0, 2/5) (5/9) | (0, 1, -2) (4/9) |
| 37 | 67/2616 | (0, 0, 0) | (-3/2, 0, 3/2) (1/2) | (3/2, 0, -3/2) (1/2) |
| 38 | 11/436 | (-2/11, -5/11, -12/11) | (-5/8, -5/8, -3/2) (8/11) | (1, 0, 0) (3/11) |
| 39 | 131/5232 | (5/8, -5/8, -3/2) | (0, -1, -2) (3/4) | (5/2, 1/2, 0) (1/4) |
| 40 | 131/5232 | (5/8, -5/8, 3/2) | (0, -1, 2) (3/4) | (5/2, 1/2, 0) (1/4) |
| 41 | 5/218 | (-2, 0, -1) | (-3, 0, 0) (1/2) | (-1, 0, -2) (1/2) |
| 42 | 5/218 | (1/2, 1/2, -2) | (0, 1, -2) (1/2) | (1, 0, -2) (1/2) |
| 43 | 29/1308 | (5/2, -1/2, 0) | (2, -1, 0) (1/2) | (3, 0, 0) (1/2) |
| 44 | 77/3488 | (9/7, 0, 2/7) | (1, 0, 0) (5/7) | (2, 0, 1) (2/7) |
| 45 | 25/1308 | (1/2, -1, -3/2) | (0, -1, -2) (3/4) | (2, -1, 0) (1/4) |
| 46 | 2/109 | (-5/8, -5/8, -3/2) | (-5/2, 1/2, 0) (1/4) | (0, -1, -2) (3/4) |
| 47 | 29/1744 | (3/2, 0, 3/2) | (1, 0, 2) (3/4) | (3, 0, 0) (1/4) |
| 48 | 25/1744 | (-13/5, 0, 2/5) | (-3, 0, 0) (4/5) | (-1, 0, 2) (1/5) |
| 49 | 99/6976 | (-2/11, 5/11, -12/11) | (-5/8, 5/8, -3/2) (8/11) | (1, 0, 0) (3/11) |
| 50 | 275/20928 | (-20/11, 1/11, 6/11) | (-5/2, 1/2, 0) (8/11) | (0, -1, 2) (3/11) |
| 51 | 67/5232 | (-3/2, 0, 3/2) | (-3, 0, 0) (1/4) | (-1, 0, 2) (3/4) |
| 52 | 131/10464 | (5/2, 1/2, 0) | (2, 1, 0) (1/2) | (3, 0, 0) (1/2) |
| 53 | 61/5232 | (1/2, -1, 3/2) | (0, -1, 2) (3/4) | (2, -1, 0) (1/4) |
| 54 | 9/872 | (-5/8, 5/8, -3/2) | (-5/2, -1/2, 0) (1/4) | (0, 1, -2) (3/4) |
| 55 | 41/5232 | (3/4, 0, -3/4) | (-1/2, 1, -3/2) (1/2) | (2, -1, 0) (1/2) |
| 56 | 35/5232 | (3/4, 0, -3/4) | (2/11, 5/11, -12/11) (11/16) | (2, -1, 0) (5/16) |
| 57 | 11/1744 | (-1/2, -1/2, 2) | (-1, 0, 2) (1/2) | (0, -1, 2) (1/2) |
| 58 | 11/1744 | (2, 0, 1) | (1, 0, 2) (1/2) | (3, 0, 0) (1/2) |
| 59 | 385/83712 | (2/11, 5/11, -12/11) | (-1, 0, 0) (3/11) | (5/8, 5/8, -3/2) (8/11) |
| 60 | 41/10464 | (-1/2, 1, -3/2) | (-2, 1, 0) (1/4) | (0, 1, -2) (3/4) |
| 61 | 35/10464 | (5/8, 5/8, -3/2) | (0, 1, -2) (3/4) | (5/2, -1/2, 0) (1/4) |
| 62 | 11/3488 | (-1/2, 1, 3/2) | (-2, 1, 0) (1/4) | (0, 1, 2) (3/4) |
