# Morrey 2×2 after the failure of Pedregal's nonemptiness lemma

**Research note, 21 November 2026.** This note proves two global reductions and closes the polynomial degree-≤3 case. It does **not** prove or disprove the unrestricted rank-one convexity versus quasiconvexity question. The code accompanying it gives exact algebraic checks and a sound sufficient SOS certificate format.

## 1. A complete rational-polynomial/dyadic reduction (negative direction)

Let `RC` be the finite-valued rank-one convex functions on `R^(2×2)`. For `l≥1`, let `P_l(Q)` denote continuous periodic maps from the 2-torus to `Q²`, affine on the `2·4^l` triangles of the Kuhn triangulation, and specified by rational values at the `2^l × 2^l` periodic grid vertices. Write

`ν_w = (1 / (2·4^l)) sum_(T) δ_(D w|_T)`.

**Theorem 1 (rational polynomial witnesses are complete).** The following statements are equivalent:

1. Every real-valued rank-one convex `f : R^(2×2) → R` is quasiconvex.
2. For every **rational-coefficient polynomial** `P : R^(2×2) → R` which is globally rank-one convex, every rational `F ∈ Q^(2×2)`, every `l≥1`, and every `w∈P_l(Q)`, the following finite rational inequality holds:

   `P(F) ≤ (1/(2·4^l)) Σ_T P(F + Dw|_T)`.

In particular, *if Morrey's implication is false, then there is a finite exact-arithmetic counterexample consisting of rational polynomial coefficients, rational base matrix, rational nodal data, and some dyadic level.* Global rank-one convexity of that rational polynomial is a decidable first-order formula over the real closed field (`∀ A, a, n : D²P(A)[a⊗n,a⊗n]≥0`), so failure has a finite, machine-verifiable certificate in principle.

### Lemma 1.1: global rank-one convex polynomials approximate every continuous rank-one convex integrand locally

For every `f∈RC`, every compact `K⊂R^(2×2)`, and every `ε>0`, there is a **rational-coefficient, globally strongly rank-one convex polynomial** `P` with `sup_K |P−f|<ε`.

**Proof.** Finite-valued rank-one convex functions are locally Lipschitz. Convolve `f` with a smooth nonnegative compactly supported mollifier. The resulting `f_δ` is smooth, remains rank-one convex (the segment inequality is preserved by translation and positive averaging), and converges uniformly to `f` on `K`.

Choose `0<η` small and put `g(A)=f_δ(A)+η|A|²`, so

`D²g(A)[H,H]≥2η |H|²` for every rank-one `H`.

Choose radii `0<r<R` with `K⊂B_r`. Using ordinary multivariate polynomial approximation in `C²(B_R)`, pick a polynomial `P0` with **rational coefficients** and

`sup_(B_R) ||D²(P0−g)||_op < η` and `sup_K |P0−g| < ε/3`.

Then `D²P0(A)[H,H]≥η|H|²` on `B_R` for rank-one `H`. Let `d=degree P0`, `k=max(d−2,0)`. There is a **rational** `M>0` such that

`||D²P0(A)||_op ≤ M(|A|/R)^k` whenever `|A|≥R`.

For any integer `m` with `2m−2≥k`, set

`Q_m(A)=c_m(|A|²/R²)^m`,  `c_m = (M+1)R²/(2m)`.

Choose rational `R` and rational `r` in this construction, so all coefficients are rational. Its Hessian satisfies for all `A,H`,

`D²Q_m(A)[H,H] ≥ (2m c_m/R²)(|A|/R)^(2m−2) |H|²`.

For `|A|≥R`, the right side dominates `(M+1)(|A|/R)^k |H|²`, so `D²(P0+Q_m)(A)[H,H] ≥ |H|²`, even for arbitrary `H`. On `B_R`, the positive semidefinite Hessian of `Q_m` preserves the *rank-one* lower bound `η|H|²`.

Finally, `sup_K Q_m ≤ c_m(r/R)^(2m) →0`. Take `m` large and set `P=P0+Q_m`. Since `f_δ` and `g` were made close to `f` on `K`, `P` is a globally strongly rank-one convex rational polynomial approximating `f` on `K` as closely as desired. □

**Important:** The proof provides no *uniform degree bound* in the required accuracy or in `f`. It is a completeness theorem for searches, not a finite one-shot solution.

### Lemma 1.2: exact dyadic reduction of quasiconvexity

Let `φ∈C_c^∞((0,1)²;R²)`. Its nodal affine interpolation `I_l φ` on the dyadic Kuhn triangulation converges in `W^{1,∞}` as `l→∞`:

`||D(I_lφ)−Dφ||_∞ ≤ C·2^(−l) ||D²φ||_∞`.

Indeed, on either half of a square of side `h`, the columns of `D(I_lφ)` are coordinate secant slopes of `φ` along horizontal and vertical edges. The mean-value formula and the Lipschitz continuity of `Dφ` give the estimate; for example, one may take `C=4` with a consistent operator norm. Since `φ` vanishes near the boundary, `I_lφ` is periodic. Approximate its nodal values by rationals to within `o(h)` so as not to disturb derivative convergence. Also approximate any fixed `F` by rational matrices.

The periodic quasiconvexity inequality for any rational polynomial thus passes to arbitrary smooth test maps. (The equivalence between compactly supported and periodic formulations follows by the standard large-square cutoff argument for bounded Lipschitz periodic test fields.)

### Theorem 1: proof of both implications

If Morrey holds, any globally rank-one convex polynomial is quasiconvex and satisfies the periodic inequality, hence the dyadic rational inequalities.

Conversely, suppose all rational polynomial/dyadic inequalities hold. Given any `f∈RC`, any base `F` and any compactly supported smooth `φ`, fix a compact ball containing `F`, `F+Dφ`, and all sufficiently fine interpolated gradients. Approximate `f` there by a rational globally rank-one convex polynomial via Lemma 1.1, apply the assumed dyadic inequalities to the rational interpolations, and pass to the limit using Lemma 1.2. The arbitrary uniform approximation error tends to zero. Thus `f(F)≤∫_(0,1)² f(F+Dφ)`, proving quasiconvexity. □

### Implication for computation

Enumerate rational tuples `(P,F,l,w)` and, for each `P`, decide the global rank-one convexity formula by real quantifier elimination. A strict rational violation is a definitive refutation of Morrey. There is **no known terminating positive procedure** for unrestricted Morrey, because neither the degree nor the dyadic level is uniformly bounded. Replacing quantifier elimination by the SOS Hessian check in the supplied script is **sound but incomplete**.

## 2. Complete theorem: degree at most three gives no counterexample

**Theorem 2 (cubic rigidity).** Let `P:R^(2×2)→R` be a polynomial of total degree at most three, globally rank-one convex. Then its homogeneous cubic part vanishes. In particular, `P` has total degree at most two and is quasiconvex.

**Hand proof of the cubic statement.** Write the four entries of a matrix as `(a,b,c,d)` by rows, and write `P=P3+P2+P1+P0` in homogeneous parts. For every rank-one direction `H`, rank-one convexity gives

`0≤ D²P(A)[H,H] = D²P3(A)[H,H] + D²P2[H,H]` for **all** `A∈R^4`.

The first summand is linear in `A`, while the second is constant. A globally nonnegative affine function has zero linear part, so

`D²P3(A)[H,H]=0` for all `A` and rank-one `H`.

Taking `H=E11,E12,E21,E22` shows `∂_aa P3=∂_bb P3=∂_cc P3=∂_dd P3=0`. Therefore the only possible cubic monomials are squarefree:

`P3=αabc+βabd+γacd+δbcd`.

The direction `E11+E12` is rank one, so `∂²_(a+b) P3=2(αc+βd)=0`, forcing `α=β=0`. The direction `E21+E22` is rank one, so `∂²_(c+d) P3=2(γa+δb)=0`, forcing `γ=δ=0`. Thus `P3=0`. □

**Why the remaining quadratic is quasiconvex.** A quadratic rank-one convex integrand has quadratic part `q` with `q(a⊗n)≥0` for all real `a,n`. By Fourier/Plancherel on the 2-torus, the average `∫q(Dφ)` of a periodic real vector field is a sum of nonnegative terms `q(Re(φ̂(k))⊗k)+q(Im(φ̂(k))⊗k)`, up to positive normalization factors. Its linear part integrates to zero because `∫Dφ=0`. Hence `∫P(F+Dφ)≥P(F)`, the quasiconvex inequality. □

**Independent exact checker:** `morrey_cubic_rigidity.py` expands all 20 cubic monomials, constructs the 24 × 20 coefficient matrix from only the six directions used in the hand proof, and verifies rank 20 exactly. It separately checks the generic rank-one identity as a 36 × 20 matrix of rank 20.

*Literature context:* rank-one convexity and quasiconvexity of quadratic integrands are classically equivalent. Recent 2026 work of Bruno–Pasqualotto addresses a nontrivial isotropic **quartic** family (arXiv:2608.06367). The above cubic rigidity is a convenient elementary prerequisite, not a claim of priority.

## 3. A new exact positive certificate for the explicit nontrivial level-two measure

**Theorem 3 (one fully certified nontrivial 32-atom test).** Take the integer-valued `4×4` nodal maps `U,V` used in the previous level-two obstruction certificate, with the Kuhn triangulation. Let `G_T = (1/4) D(U,V)|_T` (i.e. the integer nodal differences, not physical gradients), and let `P:R^(2×2)→R` be **any homogeneous quartic polynomial** which is globally rank-one convex. Then

`P(0) ≤ (1/32) Σ_T P(G_T)`.

The result holds for **all** 35 real coefficients of a homogeneous quartic simultaneously, not merely for an isotropic or SOS subclass.

**Exact proof certificate.** In the 35-dimensional vector space of homogeneous quartic polynomials, an exact rational linear-algebra computation found 35 integer base matrices `B_j`, 35 integer rank-one directions `H_j=a_j⊗n_j`, and 35 explicitly positive rational coefficients `λ_j` such that **as linear functionals on quartic polynomials**,

`Σ_(32 triangles T) P(G_T) = Σ_(j=1)^35 λ_j · D²P(B_j)[H_j,H_j]`.

This identity is verified coefficient-by-coefficient for every quartic monomial by the independent, standard-library-only checker `morrey_verify_quartic_l2_certificate.py`. Each right-hand term is nonnegative whenever `P` is globally rank-one convex. Since homogeneous quartic `P(0)=0`, the desired Jensen inequality follows. Homogeneity extends it to the true (four-times larger) physical gradients.

The exact sparse certificate is in `morrey_quartic_l2_dual_certificate.json` and the independent verifier passed. The identity is a bona fide **positive result for one 32-atom gradient law and the full homogeneous-quartic cone**, but, by itself, does not imply anything for other level-two gradient laws, nonhomogeneous quartics at arbitrary base matrices, or higher degrees. Section 3a extends it to a small open neighborhood. It is not a proof of Morrey.

**Theorem 3a (certified open neighborhood, not just one instance).** For the same fixed 35 Hessian evaluation functionals, the coefficient matrix `A∈Q^(35×35)` is invertible and the coefficients `λ=A^(-1)b(U,V,0)` are all **strictly positive**. Consequently, by continuity, the exact positive representation persists on a neighborhood in the 32 nodal values and the four entries of a base matrix `F`.

This is quantitative: the exact solver in `morrey_quartic_open_neighborhood.py` proves that if every scalar nodal value changes by less than `2^(-21)` and every entry of the *scaled* base matrix `F/4` changes by less than `2^(-21)` from zero, then

`P(F) ≤ (1/32) Σ_T P(F + Dw|_T)`

for **every globally rank-one-convex homogeneous quartic** `P`. Since the bound permits `|F|∞<2^(-21)` in physical units as a more conservative option, the result supplies an actual nonempty Euclidean-open family of `(U,V,F)` with Jensen positivity simultaneously for the full 35-dimensional homogeneous-quartic class.

The proof bounds the perturbation of every quartic moment coordinate by `(384·(K+3)^3 + 32)δ`, where `K=187` bounds all unperturbed *scaled* gradient coordinates, and compares this with `min(λ)/(2||A^(-1)||∞)` using exact rationals. The certified exponent is **21**. The output `morrey_quartic_open_neighborhood.json` preserves all the exact rational bounds.

**Computational caveat.** The certificate was discovered using a finite sampled Hessian linear program, but the proof uses only exact rational identities and nonnegative weights; it is not contingent on sampled global convexity. The initial vectorized differentiation code had a coefficient error, which was corrected and independently checked against 350 exact SymPy derivative evaluations before finding and verifying the final certificate.

**Next global target:** prove that *every* dyadic gradient law has a positive Hessian-quadrature representation for homogeneous quartics, or find a real counterexample. A general such representation would close an infinite family at once, rather than merely enumerate individual grid instances. The existing exact certificate offers a template for proposing and checking a structural identity.

## 4. Exact certificate checker

`morrey_polynomial_certificate.py`:

- Parses a rational-coefficient polynomial `P` on the four matrix entries.
- Computes the Legendre–Hadamard polynomial `D²P(A)[a⊗n,a⊗n]` symbolically.
- Verifies a proposed weighted sum-of-squares identity with **exact rational arithmetic**. Such an identity is a sufficient global rank-one convexity certificate; not every rank-one convex polynomial is assumed to admit one.
- Computes the rational Jensen gap on any dyadic periodic PL map directly from its rational grid values.
- Checks the two compulsory null-Lagrangian identities: average gradient zero and average determinant zero, for the supplied `4×4` example.

As a nonconvex rank-one convex sanity test it checks

`P(A)=|A|²+5det A`.

For a rank-one direction `a⊗n`, its Hessian equals `2|a|²|n|²`, an SOS. For the supplied integer `4×4` data it returns the strictly **negative** rational Jensen gap `−405772`. A negative definite quadratic provides a deliberate false-positive Jensen violation that the rank-one convexity checker rejects.

No polynomial violating the Morrey inequality was found or claimed. The checker demonstrates a verification route, not the solution.

## 5. Gates and recommended next mathematical attack

- [x] Pedregal's universal nonemptiness claim is refuted by the user's Lean formalization; cannot be repaired without changing its statement.
- [x] Replace the paper's informal density step by the explicit `C² → PL_l` approximation above, conditional on dyadic Jensen inequalities.
- [x] Reduce possible failure of Morrey to **rational globally rank-one convex polynomials and rational dyadic data**, providing finite negative certificates.
- [x] Exclude all polynomial degrees ≤3, uniformly over coefficients, base matrices, and dyadic levels.
- [x] Implement/test an exact symbolic SOS + rational-gradient checker.
- [x] Produce an independently verified exact 35-term positive Hessian-quadrature identity for all homogeneous quartic rank-one-convex integrands on the explicit nontrivial level-two example.
- [x] Extend the certificate to a quantified **open family of (nodal data, base matrices)** with radius `2^-21` by exact inverse and moment perturbation bounds.
- [ ] Attack **non-isotropic quartic** polynomials and higher-degree extremal rank-one convex integrands, *without* assuming SOS exhausts them.
- [ ] Alternatively, construct uniform approximate laminate representations for all dyadic gradient laws (positive direction).
- [ ] Either find a certified strict Jensen violation or prove the global Jensen inequality. This is the unresolved Morrey 2×2 question.

**Prior art:** Cassese (arXiv:2608.03488, Proposition 5.7) independently records the degree-≤3 rigidity phenomenon as folklore, so Theorem 2 is not claimed as novel. The new computation is the exact 35-term quartic identity for the specific 32-atom law; no broader novelty claim is made without verification.

**Scope warning:** The reduction proves that the **negative direction is recursively enumerable**, not that the conjecture is reducible to one bounded finite classification. Completing the unrestricted proof remains an unsolved problem.
