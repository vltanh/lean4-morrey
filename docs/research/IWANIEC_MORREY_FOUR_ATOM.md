# Global four-diagonal-atom reduction for isotropic p>2 polyconvexity

Date: 22 November 2026. **Exact general finite-support reduction**, a direct
consequence of Wiedemann–Peter (2026) and elementary finite-dimensional
linear programming. **It does NOT prove the universal inequality and does
NOT settle Morrey.** The exact rational sparsifier accompanying this note
checks moment preservation and nonincreasing cost. The underlying reduction
is prior-art mathematics; no claim of novelty is made.

## 1. Universal statement with no fixed exponent, degree, or mesh

Let \(p>2\) be arbitrary and let
\(F:\mathbb R^{2\times2}\to[0,\infty)\) be any finite-valued,
SO(2)×SO(2)-isotropic, positively p-homogeneous,
rank-one-convex integrand. Let
\(f(x,y)=F(\operatorname{diag}(x,y))\).
The following are **equivalent**:

1. F is globally polyconvex.
2. For **every** \(t\in(-1,1)\), all \(k\le4\),
   every probability vector \(w_i\ge0\), and all
   \(u_i,v_i\in\mathbb R\) with
   \[
   \sum_iw_i u_i=\sum_iw_i v_i=
   \sum_iw_i u_iv_i=0,
   \]
   one has
   \[
   \boxed{\;
   \sum_{i=1}^k w_i
     f(1+u_i,t+v_i)\ge f(1,t).
   \;}                                                     \tag{A}
   \]

For this equivalence, the rank-one convexity, nonnegativity,
and p>2 assumptions are used only to exclude the
zero-base and conformal cases from the displayed
test range: rank-one convexity gives the two-atom
Jensen inequality, and Guerra–Kristensen (2022,
Theorem 1.3) proves polyconvexity at conformal
bases for nonnegative isotropic p-homogeneous RC
integrands when p≥2. More generally, **for any
finite-valued continuous isotropic F**, global
polyconvexity is equivalent to testing (A) for
all base matrices \(\operatorname{diag}(x,y)\)
(including zero and conformal), using k≤4.

This is a **uniform finite atom-count bound**;
the exponent p, profile h, continuous atom
coordinates, perturbation sizes, and value
of t are completely unrestricted.
There is NO reduction to finitely many
numerical cases, and (A) remains open for
the p>2 class.

## 2. Derivation from the published diagonal theorem

Wiedemann and Peter, *Characterization of
polyconvex isotropic functions* (2026),
[DOI](https://doi.org/10.1007/s00526-025-03222-z),
Theorem 1.4: for isotropic two-dimensional
integrands, global polyconvexity is equivalent
to a convex representative of the signed
diagonal restriction on the three coordinates
\[
                (x,y,xy)\in\mathbb R^3.
\]
For finite-valued continuous f≥0, define
\[
g(X,Y,Z)=\inf\bigg\{
   \sum_iw_i f(x_i,y_i):
   w_i\ge0,\ \sum_iw_i=1,\
   \sum_iw_i(x_i,y_i,x_iy_i)=(X,Y,Z)
   \bigg\}.                                                \tag{B}
\]
The infimum runs over **finite** probability
laws. It is always finite: two equally
weighted atoms
\[
 (X+1,Y+(Z-XY)),\qquad
 (X-1,Y-(Z-XY))
\]
have mean X,Y and product moment Z.
Thus g is finite, nonnegative and convex
by mixing finite probability laws.
A finite convex function on \(\mathbb R^3\)
is continuous and lower semicontinuous.

At every actual diagonal matrix (x,y),
\(g(x,y,xy)\le f(x,y)\) by the Dirac law.
Equality holds on the entire lifted
diagonal graph **if and only if** every
finite minors-preserving law obeys
Jensen for f. By Wiedemann–Peter,
such equality is equivalent to
global polyconvexity of F.

## 3. Why only FOUR atoms suffice, without limiting coordinates

Suppose an N-atom diagonal probability
law has prescribed moments and violates
Jensen strictly. Keep its N atoms
fixed and minimize \(\sum_iw_i f(x_i,y_i)\)
over the compact linear-programming polytope
\[
  w_i\ge0,\quad
  \sum_iw_i
       (1,x_i,y_i,x_iy_i)=(1,X,Y,Z).
\]
A cost-minimizing extreme point has at
most **four** positive entries: otherwise
the corresponding four-dimensional
moment columns are linearly dependent.
Moving a small amount of mass in the
resulting null direction while
preserving all four moments
contradicts extremality. The optimized
law has the **same moments**, no
higher energy, and at most four atoms;
hence retains the strict violation.
This argument needs neither smoothness
nor rational coefficients.

The accompanying
[exact rational sparsifier](../../research/audit/iwaniec_diagonal_four_atom.py)
implements the same null-direction elimination
without any floating-point LP solver.
It explicitly checks all four moments
and cost monotonicity.

## 4. Normalize every potential failure to E_t

For a nonzero base matrix A, signed SVD
and isotropy reduce the base to
\(\operatorname{diag}(a,at)\), a>0,
t∈[-1,1]. Positive homogeneity permits
division by a. The zero-base Jensen
inequality holds because F≥0 and F(0)=0.
Conformal and anticonformal bases
t=±1 satisfy polyconvex Jensen by
Guerra–Kristensen (2022), Theorem 1.3.
Therefore any global polyconvexity
failure within the target class must
occur at some t∈(-1,1), and by the
four-atom theorem is captured by (A).
The three displayed equalities are
exactly mean-x, mean-y and determinant
null-Lagrangian constraints relative to
the normalized base E_t.

## 5. Rank-one convexity automatically disposes of two atoms

For k=2 and 0<w<1, the moment identities
imply
\[
       w(1-w)(x_1-x_2)(y_1-y_2)=0.
\]
Hence either x₁=x₂ or y₁=y₂.
The two diagonal matrices are
rank-one connected. Rank-one convexity
gives Jensen automatically. One atom
is trivial. Thus **only k=3 or k=4**
can witness failure of polyconvexity
for a globally rank-one-convex f.

For k=3 and positive weights, center
\(u_i=x_i-X\), \(v_i=y_i-Y\).
If the u_i are not all zero, the
space of v satisfying both
\(\sum_i w_iv_i=0\) and
\(\sum_i w_iu_iv_i=0\) is
one dimensional. An exact
parameterization is
\[
\begin{aligned}
v_1&=\tau w_2w_3(u_2-u_3),\\
v_2&=\tau w_3w_1(u_3-u_1),\\
v_3&=\tau w_1w_2(u_1-u_2).
\end{aligned}                                             \tag{C}
\]
If all u_i vanish, all atoms lie on
a rank-one diagonal line and Jensen
holds. Thus (C) reduces every
nontrivial 3-atom case to three
weights, a mean-zero u-triple,
and **one** additional parameter.
For k=4, the corresponding
weighted orthogonal-complement
space of v has dimension two
when u is nonconstant. These are
continuous unrestricted parameter
families, not finite case lists.

## 5A. ALL three-atom laws with a rank-one pair are laminates

**Theorem (unconditional, no isotropy/homogeneity required).**
Let a three-atom probability law supported on
diagonal real 2×2 matrices satisfy
\[
 \sum_iw_iA_i=\bar A,\qquad
 \sum_iw_i\det A_i=\det\bar A.
\]
If any two distinct atoms are rank-one connected,
then the law is a **finite-order laminate**:
a two-stage sequence of rank-one splittings
realizes its barycenter and weights. Hence
it satisfies Jensen for **every** rank-one
convex F, in particular for every p>2
integrand in this project.

**Proof.** Relabel so
\(A_1=\mathrm{diag}(x_0,y_1)\),
\(A_2=\mathrm{diag}(x_0,y_2)\), and
\(A_3=\mathrm{diag}(x_3,y_3)\);
the case of two equal y coordinates is symmetric.
Assume all weights positive (zero weights
reduce to the two-atom case), and let
\(w_{12}=w_1+w_2\),
\(\bar y_{12}=(w_1y_1+w_2y_2)/w_{12}\).
The first two atoms rank-one split their
own barycenter
\(B=\mathrm{diag}(x_0,\bar y_{12})\).
The determinant identity for the whole
law reduces to
\[
  w_{12}w_3(x_0-x_3)(\bar y_{12}-y_3)=0.
\]
If \(x_0=x_3\), the matrices B,A3
are rank-one connected automatically;
otherwise the displayed identity forces
\(\bar y_{12}=y_3\), again giving a
rank-one connection. Split the total
barycenter into B and A3, then split B
into A1 and A2. Two rank-one Jensen
inequalities prove the claim. QED.

Thus any three-atom obstruction to
the **polyconvexity** conjecture must
have pairwise full-rank differences:
\[
  (x_i-x_j)(y_i-y_j)\ne0
  \quad\text{for every }i\ne j.
\]
These are sometimes called
three-atom unconnected or T3-type
moment configurations. This geometric
necessary condition is not sufficient
for an energy violation.

**Exact example showing the residual class exists.**
At normalized base E₀=diag(1,0), take
equal weights \(w_i=1/3\) and diagonal
coordinates
\[
 (x_i,y_i)=
 (0,-3/2),\quad(3/4,9/4),\quad
 (9/4,-3/4).
\]
One checks exactly
\[
 \sum w_ix_i=1,\quad
 \sum w_iy_i=0,\quad
 \sum w_ix_iy_i=0,
\]
while all three pairs have different
x and y coordinates. This is
**not** an actual compatible planar
gradient law and carries no assigned
negative energy gap. The exact rational
control is [here](../../research/audit/iwaniec_three_atom_geometry_exact.py).

This disposes of **every** connected-pair
three-atom configuration simultaneously,
not an arbitrary fixed-mesh family.
The remaining global gate concerns
pairwise rank-two-separated 3-atom
laws and unconstrained 4-atom laws
for every admissible p and F.

## 5B. Remove ALL rank-one edges from a minimal negative witness

**Global pruning theorem.**
For any finite-valued rank-one-convex integrand
\(F:\mathbb R^{2\times2}\to\mathbb R\)
and any minors-preserving signed-diagonal
probability law with at most four atoms,
a strict Jensen violation can always be
reduced to a strict violation on **three
or four atoms with every pairwise
difference of full rank**. This
does not require isotropy, homogeneity,
nonnegativity, or a fixed exponent.

**Proof.** Suppose two atoms \(A_i,A_j\)
have rank-one difference.
Merge them into a new atom
\(B=(w_iA_i+w_jA_j)/(w_i+w_j)\)
with weight \(w_i+w_j\).
Because determinant is affine
along a rank-one segment,
the matrix barycenter and determinant
moment of the entire law are unchanged.
Rank-one convexity gives
\[
 (w_i+w_j)F(B)\le
   w_iF(A_i)+w_jF(A_j).
\]
Thus merging the pair can only
**decrease** mean energy while
preserving the base and all
minors moments. A strict negative
gap therefore stays strictly
negative. Repeat merging any
rank-one-connected pair.
Each step reduces the number of
positive atoms by one.
The process cannot end with fewer
than three atoms, since one- and
two-atom minors-preserving laws
obey Jensen by rank-one convexity.
The final three-/four-atom strict
witness has **no** rank-one pair. QED.

Consequently, the entire
nonnegative isotropic p>2
polyconvexity question reduces to
two continuous types **T3** and
**T4**, each pairwise rank-two
separated and satisfying the
three exact normalized first-moment
and determinant constraints. This
is a structurally sharper statement
than merely bounding the atom count.

**Residual four-atom geometry is nonempty.**
For \(E_0=\mathrm{diag}(1,0)\),
take equal weights \(w_i=1/4\) at
\[
 (x_i,y_i)=(-2,-1),(0,3),(2,-3),(4,1).
\]
They have mean x=1, mean y=0,
mean xy=0, and every pair
has distinct x and distinct y.
The [exact rational verifier](../../research/audit/iwaniec_four_atom_geometry_exact.py)
checks those relations. No
energy violation is claimed;
the example simply establishes
that the residual T4 moment
geometry cannot be excluded
by the determinant identity alone.

**Stop rule:** This finishes the
*finite atom-count and rank-one-edge
elimination reduction*; do not
continue pruning ever-larger
fixed-size special lists.
To solve the universal conjecture
one must establish the Jensen
inequality for arbitrary
pairwise-unconnected T3 and T4
configurations, **simultaneously
over all p>2 and all admissible F**,
or exhibit a strict violation.
A violation would refute global
*polyconvexity*; an actual
compatible-gradient witness
would still be required to
disprove quasiconvexity.

## 6. Status and exactly what remains

This reduction is **global in the
quantifiers**: it covers all p>2,
every nonnegative isotropic RC
p-homogeneous F, and every base.
It gives a **finite-size witness if
the stronger polyconvexity conclusion
is false**. The only possible
counterexample to global polyconvexity
must exhibit 3 or 4 signed-diagonal
atoms with strict Jensen deficit
satisfying (A)'s three moment identities.

Such atoms do **not** automatically
constitute an actual planar gradient
Young measure; a polyconvexity
counterexample alone does not
disprove quasiconvexity or Morrey.
Conversely, proving (A) universally
for the remaining 3- and 4-atom
classes would settle the whole
nonnegative isotropic p>2
polyconvexity question—without
requiring a degree/grid cutoff.

The reduction is a hand derivation
of established convex-geometric
facts, accompanied by exact rational
regression controls. No Lean build,
CI or independent external review of
the implementation is claimed.
