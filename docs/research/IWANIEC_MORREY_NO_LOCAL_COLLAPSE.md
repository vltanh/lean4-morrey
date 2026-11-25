# Decisive test of local collapse: a six-atom laminate with no compatible collapse on at most four atoms

24 November 2026. Stop-rule experiment following [R24](IWANIEC_MORREY_LH_COMPACTNESS_JET_REPAIR.md). We test ONE specific proposed law-modification lemma instead of developing another framework:

> Every nontrivial compact planar gradient Young measure has a non-Dirac gradient Young sublaw supported on a rank-one pair or T4 whose replacement by its barycenter preserves gradient compatibility.

**FALSE, even for a six-atom diagonal laminate.** More strongly, the example below has no compatible collapse of ANY non-Dirac gradient Young sublaw supported on at most four atoms, with any positive removable mass. Its whole law is a laminate and can be collapsed. Thus this is not a counterexample to Morrey, to the existence of some nonlocal collapse, or to a lemma specifically restricted to hypothetical minimizing laws of uniformly strongly rank-one-convex energies. It refutes a universal bounded-local-move mechanism based only on the planar compactness theorem. The counterexample is exact and its finite algebra can be independently replayed without a solver.

## 1. Limited audit of the preceding rigidity input

Checked the actual statements of Faraco and Székelyhidi, *Tartar's conjecture and localization of the quasiconvex hull in R2x2*, Acta Math. 200 (2008), 279--305, [DOI](https://doi.org/10.1007/s11511-008-0028-1), Theorem 6 and Corollary 2. The former proves connectedness of the rank-one convex hull of the support of a compactly supported homogeneous gradient Young measure; the latter excludes non-Dirac measures on compact sets with neither rank-one connections nor T4 configurations. This supports the minimum-set argument in R23/R24: a compact subset of the global zero set of a nonnegative strongly RC function supports no nontrivial laminate, hence has neither type of configuration and supports no nontrivial gradient law. It does NOT say that a pair or T4 in a support can be removed from a given law. We have not independently audited all the other analytical and effective-computability proofs in R11--R24.

The second published input is S. Müller, *Rank-one convexity implies quasiconvexity on diagonal matrices*, IMRN 1999(20), 1087--1095, [DOI](https://doi.org/10.1155/S1073792899000598), [preprint](https://www.mis.mpg.de/publications/preprint-repository/article/1999/issue-29). Theorems 1--2 and Corollary 3 give the separate-convex Jensen property of compact diagonal gradient Young measures. In particular for a nonnegative separately convex test of at most quadratic growth, a bounded generating sequence on the diagonal has its off-diagonal entries tending to zero in L2, so the two relevant derivatives in Theorem 1 tend to zero in H^-1. We use exactly this known diagonal case, not an assumed global planar Morrey inequality.

## 2. The single move and the exact falsifier

Identify (x,y) with diag(x,y). If nu is a probability law, mu a probability gradient Young law, and 0<alpha with alpha mu<=nu as measures, the proposed collapse is
    nu' = nu-alpha mu+alpha delta_(mean mu).
It preserves the mean matrix and determinant moment, and if mu is a laminate, it decreases the average of every strongly RC energy by at least m alpha Var(mu)/2 for LH margin m. The issue is whether nu' remains a gradient Young measure.

Take the following six endpoints X_i and the six rank-one cycle vertices P_i, in cyclic order. The index 7 denotes 1. Each X_i=P_i+kappa_i(P_(i+1)-P_i) with kappa_i>1.

| i | P_i | X_i | kappa_i | 485 nu_i |
| --- | --- | --- | ---: | ---: |
| 1 | (5,2) | (-15,2) | 4 | 9 |
| 2 | (0,2) | (0,-22) | 2 | 36 |
| 3 | (0,-10) | (32,-10) | 4 | 24 |
| 4 | (8,-10) | (8,-2) | 2 | 96 |
| 5 | (8,-6) | (2,-6) | 2 | 192 |
| 6 | (5,-6) | (5,26) | 4 | 128 |

Starting at P_1, split backwards around the cycle using P_(i+1)=(1-1/kappa_i)P_i+X_i/kappa_i. After six splits the residual mass at P_1 is 27/512. Repeat on this mass. The bounded finite-tree measures converge to the displayed probability weights. Thus nu is an actual compact laminate and hence homogeneous gradient Young measure with mean P_1. This construction, not just the minor identities, establishes compatibility.

All six x and y coordinates of the endpoints are distinct. The support has NO rank-one pair.

### 2.1 Exact separately convex exposed-face test

Use the grid
    x = (-15,0,2,5,8,32), y = (-22,-10,-6,-2,2,26).
The following table gives 48960 f(x,y), with x indexing rows.

| x / y | -22 | -10 | -6 | -2 | 2 | 26 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| -15 | 48960 | -6243 | -18944 | -31645 | -44346 | 48960 |
| 0 | -48960 | -47328 | -46784 | -46240 | -45696 | -26048 |
| 2 | -42840 | -47430 | -48960 | -48186 | -45876 | -32016 |
| 5 | -33660 | -47583 | -47872 | -47009 | -46146 | -40968 |
| 8 | -24480 | -47736 | -46784 | -45832 | -44880 | -39168 |
| 32 | 48960 | -48960 | -38080 | -27200 | -16320 | 48960 |

Adjacent divided differences in each row and column are nondecreasing (the companion verifies every exact inequality). Piecewise bilinear interpolation on the rectangle is therefore separately convex: at any fixed value of the other coordinate the slopes are positive affine averages of the corresponding slopes on neighboring grid lines. All values lie in [-1,1] and all coordinate slopes have absolute value at most one. Let I,J be the coordinate intervals of the rectangle. Extend by
    g(x,y)=1+f(clamp_I(x),clamp_J(y))+dist(x,I)+dist(y,J).
This is globally nonnegative, separately convex (outside each interval the slopes are -1 and +1, consistent with the interior endpoint slopes), and of at most linear growth. On the rectangle it agrees with f+1. Every compact diagonal gradient law must obey Jensen for g by Müller's theorem.

Each of the original six cycle splits has EXACT zero Jensen gap for f. Thus int g dnu=g(P_1). No optimizer output is used in the verification of this equality.

### 2.2 Exhaust all T4 configurations, not just one choice

Every T4 with these diagonal endpoints has diagonal cycle vertices: the backward cycle splits express each vertex as a convex combination of the four endpoints. Therefore its rank-one directions are coordinate axes. The four steps must alternate horizontal/vertical, because adjacent steps of the same axis would make two endpoints share a coordinate. Starting at a horizontal step, all possible configurations are given by an ordered quadruple (A,B,C,D) of distinct endpoints and vertices
    (D_x,A_y), (B_x,A_y), (B_x,C_y), (D_x,C_y).
Check the four strict extrapolation factors kappa>1. Enumeration of all ordered quadruples, identifying rotation by two steps, gives exactly three cycles:

| ordered endpoint indices | sum of the four split gaps for f | minimum corner-law gap | determinant of moment matrix |
| --- | ---: | ---: | ---: |
| (1,2,3,6) | 4/255 | 54/8585 | 436320 |
| (1,2,4,6) | 16/765 | 128/9129 | 85920 |
| (1,5,4,6) | 4/255 | 8/1145 | 21984 |

The split gap is (1-1/kappa_i)f(P_i)+f(X_i)/kappa_i-f(P_(i+1)). The corner law is the repeated backward splitting law based at that vertex, just as in the six-cycle proof. All entries, including every corner-law gap and the determinant of the four-by-four matrix with columns (1,x_i,y_i,x_i y_i), are checked exactly in the companion script. In particular each of the three moment matrices is invertible.

### 2.3 Why EVERY nontrivial compatible law on four endpoints is blocked

It would be insufficient to test just the displayed cycle weights. Here is the argument for all possible weights and barycenters.

After reflection of either coordinate, a diagonal T4 has the standard rectangle-and-arms geometry, with vertices (a,b),(c,b),(c,d),(a,d), a<c and b<d; right, top, left, bottom endpoints are respectively (r,b),(c,t),(l,d),(a,s) with r>c,t>d,l<a,s<b. Every gradient law on these endpoints has its barycenter in the rectangle and its four arms joining the adjacent corner to each endpoint. Indeed the eight nonnegative separately convex products
    (x-c)_+(y-b)_+, (x-c)_+(b-y)_+,
    (a-x)_+(y-d)_+, (a-x)_+(d-y)_+,
    (y-d)_+(x-c)_+, (y-d)_+(c-x)_+,
    (b-y)_+(x-a)_+, (b-y)_+(a-x)_+
vanish on the endpoints. By Müller's diagonal theorem they vanish at the barycenter. Together with coordinate bounds on the mean they restrict it to exactly the stated rectangle and arms. Reflections do not change the separate-convex Jensen property. This proves the needed hull inclusion directly.

Conversely for each rectangle point one can construct a laminate on the four endpoints by taking a two-stage product split to the corners and substituting the corner cycle laminates. For each arm point take a rank-one split between its endpoint and its rectangle corner, then substitute the corner law. All constructed laws have the matrix and determinant mean at that point. Since the moment matrix is invertible, these laws are the UNIQUE probability weights on the four endpoints with those prescribed moments. They therefore equal every compatible law at that mean.

For means in the rectangle, g Jensen is strict because each corner law has strictly positive gap, and separate convexity gives the rectangle product-split Jensen inequality. On an arm away from its endpoint the corner weight is positive, so the same strictness holds. At an endpoint the unique law is the Dirac measure. Hence every non-Dirac gradient law on any of the three T4s has strictly positive g Jensen gap.

For any other subset with at most four endpoints, Faraco--Székelyhidi's Corollary 2 excludes a non-Dirac gradient law, since it has neither a rank-one connection nor T4. This also covers two- and three-atom subsets. Thus EVERY possible non-Dirac gradient sublaw mu supported on at most four of the six endpoints satisfies
    int g dmu - g(mean mu)>0.
If alpha mu<=nu for any alpha>0, the collapsed law satisfies
    int g dnu' - g(P_1) = -alpha [int g dmu - g(mean mu)] < 0.
It remains diagonal, so cannot be a gradient Young measure. This proves the counterexample to the proposed universal local-collapse lemma, including partial masses and every possible T4 sublaw. The six-cycle itself remains a valid nonlocal collapse. No assertion of absence of five-atom collapses or of an unbounded necessary support size is made.

## 3. Additional exact control: even the existence of a rank-one pair does not help

The companion reverse_merge_exact.py gives a different ten-atom laminate with exactly one rank-one pair; EVERY positive partial merge of that pair fails. It uses the much simpler separately convex test g(x,y)=x_+ y_+ (nonnegative and of quadratic growth). Start at (1,1) and split by equal weights to (0,1),(2,1); split (2,1) to (2,0),(2,2); split (2,0) to (-1,0),(5,0). Replace (2,2) by the corner laminate from the T4 rectangle with lower-left (2,2), sides 1/10 and extrapolation factors all 2. Replace (-1,0) by the average of the four corner laminates of the rectangle with lower-left (-9/8,-2/3), sides (1/4,4/3), same factors 2. Its center is (-1,0), so averaging the corner laminates is a two-step laminate at that center.

The sole rank-one-connected pair is (-7/8,2) and (11/5,2), with masses 1/32 and 1/60. The original law has mean (1,1), determinant mean 1 and g average 1. Removing positive masses a,b at those two endpoints and merging them loses exactly 2 min(7a/8,11b/5) in g average, so all such partial merges are incompatible; the full merge loses 7/128. A mixed T4 with ordered endpoints (2,19/10),(19/10,21/10),(-7/8,2),(-5/8,-2/3) also has strict g Jensen gap at the lower-left base (-5/8,19/10). Every positive removable proportion of its canonical cycle law fails. Its two original nested T4s, however, can be collapsed. This control isolates the rank-one-pair failure, and is not needed for the stronger six-atom theorem.

## 4. Executed check and disposition

Run the two exact standard-library scripts:
    python3 research/audit/six_atom_no_local_collapse_exact.py
    python3 research/audit/reverse_merge_exact.py

The first passed the 6-cycle weights/minors, separate-convex slope inequalities, all 360 ordered quadruples (with cyclic symmetry reduction), three T4 configurations and their strict corner gaps and moment determinants. The second passed 100 exact partial pair merges and ten mixed T4 collapse controls. The all-positive-mass claims follow from the displayed algebraic inequalities, not from sampling. The six-cycle was discovered with a small SciPy HiGHS LP (random seed 20261124, 11 accepted rank-one-free cycle candidates); the exact rational table and checker are independent of that solver. SHA-256 of the executed scripts: ae03200568d46c748cdd5cf1b0dc59872b2f586dcfbb18a9d99a5380b059bf96 and c7ff347c83a7b6280eccc8a2a1584879d53d354c378620e4c9e03fc5b4b9d7e4.

**Stop rule:** abandon the proposed universal pair-or-T4 collapse lemma. This is a decisive falsification of a specific mathematical step, not another reduction counted toward the open conjecture. It does not preclude a special argument using actual optimality for a uniformly strongly RC F, but the examples are nontrivial laminates and therefore cannot themselves be minimizing laws of such F. The missing specialized lemma still has no proof. A valid next approach must exploit genuinely additional information about the minimizing law or a global compatible deformation; the planar support theorem alone does not furnish the desired step. Do not extend the experiment into an atom-count ladder. No proof of unrestricted Morrey, negative planar RC/QC pair, new Lean theorem, or comprehensive independent audit is claimed.
