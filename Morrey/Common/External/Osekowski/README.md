# Osękowski: differential subordination characterizes Hilbert spaces

**Source.** A. Osękowski, *Sharp martingale and semimartingale inequalities*, Birkhäuser 2012,
Theorem 3.24.

**Statement.** Cassese quotes it as Proposition 2.6: a Banach space `X` in which differentially
subordinate martingales satisfy `‖X_n‖_{L^p} ≤ β_p ‖Y_n‖_{L^p}` is isomorphic to a Hilbert space
`H`, with Banach–Mazur distance `d (X, H) ≲_p β_p`. It is context only: no proof of the paper uses
it.

**Lean.** [`HilbertCharacterization.lean`](HilbertCharacterization.lean): the proposition
`External.Osekowski.HilbertCharacterization`, with no proof, a hypothesis of no statement.

**Who uses it.** Nobody. The results of Osękowski's book that the paper does use, Theorems 3.5 and
8.6 (Cassese's Theorem 2.3), are proved in [`../Burkholder`](../Burkholder).
