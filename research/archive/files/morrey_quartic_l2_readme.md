# Exact homogeneous quartic Jensen certificate for one level-two gradient law

**Claim.** Let `U,V` be the integer periodic nodal data from `morrey_level2_uniform_fixedpoint_obstruction.py`. Let `G_T` be the 32 integer matrices of nodal differences on the triangular cells. Then for **every** globally rank-one convex homogeneous quartic polynomial `P` in the four matrix entries,

`(1/32) Σ_(T) P(G_T) >= P(0) = 0`.

A verified rational identity stronger than the inequality is

`Σ_(T) P(G_T) = Σ_(j=1)^35 lambda_j * D²P(B_j)[a_j tensor n_j, a_j tensor n_j]`,

where each `B_j`, `a_j`, `n_j` is an **integer** vector, and each `lambda_j` is **strictly positive and rational**. The exact values are in `morrey_quartic_l2_dual_certificate.json`.

- `morrey_verify_quartic_l2_certificate.py` is an **independent verifier** that uses only the Python standard library and computes all 35 coefficient identities over `fractions.Fraction`. It verifies the 32 gradients, zero mean, zero mean determinant, positive weights, and rank-one directions.
- Recompute with `python3 morrey_verify_quartic_l2_certificate.py` in the same folder as the JSON certificate.

**Precise scope:** This proves positivity for a **single explicit gradient measure**, **homogeneous quartic** integrands, and **base point zero**. It does not prove Pedregal's Theorem 1.1(1), nor the full Morrey conjecture, nor arbitrary nonhomogeneous quartic integrands.

## Quantified robustness

The independent exact bound in `morrey_quartic_open_neighborhood.py` certifies the full 35-dimensional coefficient cone on an open neighborhood. If each of the 32 scalar nodal values changes by less than `2^-21` and the base matrix is sufficiently close to zero (e.g. each physical base entry `<2^-21` in absolute value), the entire Jensen inequality remains true for *every* globally rank-one-convex homogeneous quartic. The proof holds with arbitrary **real** nodal perturbations, although the center and certificate are rational. The proof uses `A^-1` over `Q` and a conservative polynomial Lipschitz bound. Output: `morrey_quartic_open_neighborhood.json`.

The positive decomposition weights are allowed to vary with the perturbation; the rank-one Hessian evaluation sites are fixed.
