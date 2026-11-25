# A universal level-one fixed point disproves proposed Theorems B and B1

**Status:** Exact finite combinatorial/algebraic certificate, independently checked by
`morrey_l1_mold_certificate.py`. The mathematical argument below is a hand proof,
*conditional only on the standard interpretation of parallel directions as zero
2×2 determinant (the interpretation appropriate for rank ≤1)*. It has not yet
been translated into the user's Lean project's precise mold structures.

## The level-one cube

Let \(\tau:\mathbb{R}\to\mathbb{R}\) be a 1-periodic triangular wave with
\(\tau'=+1\) on \((0,1/2)\) and \(-1\) on \((1/2,1)\). For any
\(u,v\in\mathbb P_1\), there are vectors \(a_1,a_2,a_3\in\mathbb R^2\)
such that the pair \((u,v)\), modulo additive constants, is
\(a_1\tau(x_0)+a_2\tau(x_1)+a_3\tau(x_0+x_1)\).

Write \(n_1=(1,0), n_2=(0,1), n_3=(1,1)\) and
\(C_i=a_i\otimes n_i\). The eight triangle gradients on the periodic
2×2 grid are exactly, each once,
\[G_s = s_1 C_1 + s_2 C_2 + s_3 C_3,\qquad s_i\in\{-1,+1\}.\]
All eight have equal triangle area \(1/8\).

Crucial geometric fact: the 12 interfaces of the periodic triangulation are
exactly the 12 edges of the 3-cube of sign vectors. An interface with normal
\(n_i\) joins two sign triples differing only in coordinate \(i\).

## A tri-dyadic mold S*

For each pair of distinct normal indices \(\{i,j\}\subset\{1,2,3\}\),
let \(k\) be the remaining index. This gives one of the three dyadic
sub-molds required by Definition 4.1.

1. At the first stage, include all four physical interfaces of type \(i\)
   and all four of type \(j\). They give eight first-stage merges of 16
   triangle occurrences (each of the eight triangles occurs twice).
2. Order those eight interfaces as follows. First the two type-\(i\)
   interfaces with \(s_k=+1\), then the two type-\(j\) interfaces with
   \(s_k=+1\); repeat for \(s_k=-1\). Within each pair, the two interfaces
   differ in the sign of the other selected coordinate.
3. At the second stage, merge consecutive first-stage means. This gives
   four nodes, each equal to \(s_k C_k\), with \(s_k=+1,+1,-1,-1\).
4. At the third stage, merge equal means: \(+C_k\) with \(+C_k\), and
   \(-C_k\) with \(-C_k\). Both differences are zero.
5. At the fourth stage, merge \(+C_k\) with \(-C_k\), obtaining zero.

Because the choice of first-stage interfaces is exactly the set of edges
with normals in \(\{i,j\}\), each physical interface occurs in exactly two
sub-molds, and each triangle occurs six times across all three sub-molds.
Choose uniformly \(t_\alpha=1/48\) for all 48 leaf occurrences. Then each
edge-pair has weight \(2/48=1/24\), as required by (5.5) for \(l=1\), and
each triangle has total weight \(6/48=1/8\), as required by (5.6).
Thus \(t\in\Theta_1\).

Every merge direction is zero or a scalar multiple of one of the rank-one
matrices \(C_i\). The three dyadic sub-molds end at zero, so the final two
tri-dyadic merges also have zero directions. Hence all decomposition
directions for the two components are parallel, and
\[t\in\mathbf T_{1,\mathscr S^*,u,v}(t)\]
**for every pair** \(u,v\in\mathbb P_1\).

## Concrete violation of B1

Take \(a_1=(1,0),a_2=(0,1),a_3=(1,1)\), corresponding to
\[u=\tau(x_0)+\tau(x_0+x_1),\quad
  v=\tau(x_1)+\tau(x_0+x_1).\]
Then
\[q=(a_1\times a_2,\;a_1\times a_3,\;a_3\times a_2)=(1,1,1),\]
so \(q_{12}q_{13}q_{23}=1\ne0\), yet the fixed point above exists.
This contradicts Theorem B1 as formulated in the research note.
Because \(\mathscr S^*\) admits a fixed point for **every** level-one input,
it also contradicts Theorem B (for \(l=1\)).

Theorem A is *not* refuted by this example: the distinguished uniform
\(t\) may itself lie in a proper algebraic slice even though all pairs
\((u,v)\) have a fixed point there.

## Scope, and next step

This argument is confined to \(l=1\). It shows that there can be an
exceptional mold not detected by sampling random mold orders and random
weights. It does *not* vindicate Pedregal's argument for all \(l\), and does
not establish the original Morrey conjecture. A meaningful universal-mold
obstruction must address at least \(l=2\) (or use a different invariant).

To make this proof fully trusted in the existing Lean project, translate
exactly the 48 leaf tags from the script into `TriDyadicMold 1`, establish
`S*` satisfies Definition 4.1, and verify the 23 determinant constraints
under the same collinearity convention as Definition 6.1.
