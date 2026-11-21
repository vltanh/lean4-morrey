# Morrey's 2×2 problem: all-level polynomial certificate theorem and quartic experiments

**Date:** 21 November 2026. **Research status:** The unrestricted Morrey conjecture is **not proved**. Pedregal's nonemptiness lemma cannot be used because of the existing Lean counterexample. The results below are an exact all-level reduction for each polynomial degree, a simple exact separating witness showing that determinant moments alone are insufficient, and numerical exploration of the first difficult degree.

## 1. An exact theorem independent of dyadic resolution

Let `M = R^(2×2) ≅ R^4`. Fix a closed Euclidean ball `K` with nonempty interior. For a compactly supported probability measure `ν` in `int K`, set `F = ∫ A dν(A)` and `Lν(P) = ∫ P(A)dν(A)−P(F)`. Let `V_d` be the space of real polynomials on `M` of total degree at most `d >= 2` and `R1 = {H: rank H=1, |H|=1}`. Define

    S_(K,d) = { P ↦ D²P(B)[H,H] on V_d : (B,H)∈K×R1 }.

**Theorem 1 (exact finite-degree equivalence and bounded certificate size).** The following are equivalent:

1. `Lν(P) >= 0` for every polynomial `P ∈ V_d` whose rank-one Hessian is nonnegative for every point of `K` and rank-one direction.
2. There are `r <= C(d+4,4)-6`, points `B_j ∈ K`, unit rank-one matrices `H_j`, and numbers `λ_j>=0` such that for *every* polynomial `P∈V_d`, simultaneously,

       Lν(P) = Σ_(j=1)^r λ_j D²P(B_j)[H_j,H_j].

This is an **if-and-only-if duality**, not a claim that condition 1 always holds for gradient measures.

**Proof.** The compact set `S_(K,d) ⊂ V_d*` has a constant positive coordinate: for `P_0(A)=|A|²/2`, every `s∈S_(K,d)` satisfies `s(P_0)=1`. Therefore its conical hull is closed: bounded sequences in this cone have bounded total coefficient mass, and the normalized points lie in the compact convex hull of `S_(K,d)`. If `Lν` is outside this cone, finite-dimensional hyperplane separation supplies `P∈V_d` with `D²P(B)[H,H] >=0` on `K×R1`, but `Lν(P)<0`. Conversely every nonnegative sum of the displayed Hessian evaluations is nonnegative on this polynomial cone. Finally the linear span of `S_(K,d)` has dimension exactly `N_d = C(d+4,4)-6` (Lemma 2 below), because the annihilator is the 6-dimensional space of rank-one-affine polynomials. The normalized set lies in an affine hyperplane of dimension at most `N_d−1`, so Carathéodory expresses any point of its convex hull using at most `N_d` points. QED.

**Lemma 2 (exact kernel).** If a polynomial `Q` satisfies `D²Q(A)[H,H]=0` for every `A` in an open ball and every rank-one `H`, then

    Q(A)=c+L(A)+t det(A).

**Hand proof.** Write `A=(a,b,c,d)` by rows. Each coordinate direction `E11,E12,E21,E22` is rank-one, so the four pure second partial derivatives of `Q` vanish. Since `Q` is a polynomial, it is multiaffine. The four rank-one directions `E11+E12`, `E11+E21`, `E12+E22`, `E21+E22` force the four corresponding mixed derivatives (`∂ab,∂ac,∂bd,∂cd`) to vanish. Only the monomials `1,a,b,c,d,ad,bc` remain. The rank-one direction `E11+E12+E21+E22` forces the coefficients of `ad` and `bc` to sum to zero, hence the only nonlinear term is a multiple of `ad-bc=det A`. Polynomial vanishing on an open ball is global, so the argument applies to any ball. QED.

| Degree bound d | Dimension V_d | Exact Hessian-functional dimension N_d | Max certificate atoms |
|---:|---:|---:|---:|
| 2 | 15 | 9 | 9 |
| 3 | 35 | 29 | 29 |
| 4 | 70 | 64 | 64 |
| 5 | 126 | 120 | 120 |
| 6 | 210 | 204 | 204 |
| 8 | 495 | 489 | 489 |

This does not bound polynomial degree and therefore does not give a finite solution of Morrey. It **does** provide a bounded certificate size for each degree, independent of the number of triangles and test-map grid resolution.

## 2. What would finish the proof

For every dyadic periodic two-component piecewise affine map `w` and base matrix `F`, let `ν=(F+Dw)_#dx`. To establish unrestricted Morrey it would suffice to prove the feasibility in Theorem 1 for **every** degree and every such `ν`, on a fixed ball containing its support in the interior. Conversely, if the unrestricted Morrey conjecture holds, each fixed-degree feasibility condition follows (rank-one-convex polynomials on the ball can be approximated near the support by globally rank-one-convex polynomials, using a strict quadratic margin and high-degree radial stabilization).

A sequence of bounded positive measures representing all degrees admits a subsequential limit. Testing `P=|A|²/2` fixes the mass, and testing `|A-C|^{2k}` for all `k` prevents escape to infinity. The limit then represents the entire Jensen functional on `C²` test functions. This is the compactness passage from the previous research note; **the unproved step is feasibility for all degrees and all gradients**.

The desired global statement would be a *continuum compensated-compactness theorem for the full polynomial moment cone*, not one mold or one grid.

## 3. The determinant moment is nowhere near sufficient at quartic degree

It is tempting to replace 'gradient law' with the two null-Lagrangian constraints

    E[A]=0,             E[det A]=0.

This does NOT ensure Jensen positivity for all globally rank-one-convex polynomials, even in `2×2`, and even for a very classical quartic.

Take `γ=9/8` and

    fγ(A)=|A|⁴−2γ|A|² det(A).

For a unit rank-one direction, `SO(2)×SO(2)` symmetry allows us to take `H=E11`, and a direct computation with `A=[[a,b],[c,d]]` yields

    (1/4) D²fγ(A)[E11,E11]
      = 3a²+b²+c²+d²−(27/8)ad+(9/8)bc
      = 3(a−9d/16)²+13d²/256+(b+9c/16)²+175c²/256 ≥0.

Thus `fγ` is globally rank-one convex, with an explicit exact SOS certificate (no appeal to numerical tests).

Let `I=diag(1,1)`, `J=diag(1/5,−1/5)`, and put

    ν= (1/52)δ_I + (1/52)δ_{−I} + (25/52)δ_J + (25/52)δ_{−J}.

Then, by symmetry, `Eν[A]=0`, while `Eν[det A]=1/26−(25/26)(1/25)=0`. However `fγ(0)=0`, `fγ(I)=−1/2`, `fγ(J)=17/1250`, and hence

    Eν[fγ(A)]−fγ(0) = −2/325 < 0.

The 2026 Bruno–Pasqualotto theorem proves that this particular rank-one-convex `fγ` is quasiconvex, so `ν` cannot be a homogeneous gradient Young measure. This clean example shows why merely imposing the barycenter and determinant moments is insufficient already at the first difficult polynomial degree. Actual curl-free gradient microstructure is indispensable.

## 4. Exploratory quartic search: 16 random gradient laws

The independent source script `morrey_quartic_global_probe.py` constructs periodic two-component maps from random integer nodal data and tests **all polynomials of total degree at most four** simultaneously, via the exact 65 monomial coordinates (degrees 2, 3, 4). It samples 9,000 rank-one Hessian evaluation points (the samples are *not* exhaustive), and solves a nonnegative equality LP for the Jensen moment vector. All tested cases were numerically feasible:

- 9 random `4×4` periodic nodal grids (32 gradient atoms),
- 4 random `8×8` periodic nodal grids (128 gradient atoms),
- 3 random `16×16` periodic nodal grids (512 gradient atoms).

The solver returned 64 nonzero Hessian points in each case, exactly matching the theoretical upper bound; normalized equality residuals were below `7×10⁻¹⁴`. A separate integer monomial Hessian evaluator independently verified 2,340 individual derivative entries against the code. This is suggestive evidence for a **global all-quartic** statement, but is NOT a proof: the search samples finitely many Hessian points, the coefficients are floating-point, and the 16 gradient laws do not cover arbitrary gradient distributions.

**The next nonlocal mathematical target** is a symbolic inequality / positive Hessian representation for the *full fourth-order moment tensor of every periodic gradient*, with no restriction on grid size. One could then try to find a degree-raising mechanism; none has been found.

## 5. Explicit caution about scope and novelty

- The rank-one-affine kernel and the finite-dimensional conic/Carathéodory theorem are elementary consequences of established principles. They are a **newly completed gate in this research workflow**, not claimed as new mathematical literature.
- Existing independent work by Awi–Šverák (2023) already develops a global convex-optimization approach to Morrey; the above is an exact polynomial-moment specialization.
- Bruno–Pasqualotto (arXiv:2608.06367, August 2026) establishes the full bivariantly rotationally invariant homogeneous-quartic class, **not** arbitrary nonisotropic quartics.
- Pedregal's Proposition 7.1 and Corollary 7.2 remain false by the user's Lean audit. No variant of Kakutani's theorem fixes the missing nonemptiness.
- **Unrestricted Morrey remains open.** Neither the polynomial-degree hierarchy nor the numerical quartic results prove it.

## Files

- `morrey_rankone_kernel_exact_check.py` — pure-Python exact checks of the kernel counting and non-gradient moment witness.
- `morrey_quartic_global_probe.py` — reproducible exploratory linear programs (NumPy, SciPy).
- `morrey_quartic_probe_log.txt` — the main four experiment outputs.

Sources: Awi–Šverák, *Remarks on Morrey's quasi-convexity* (2023); Bruno–Pasqualotto, *Quasiconvexity for the Dacorogna–Marcellini Energy* (arXiv:2608.06367); Pedregal, arXiv:1905.06571v5.
