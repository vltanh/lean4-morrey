# Morrey 2×2: global proof reorientation (21 November 2026)

**Outcome:** The conjecture is **not proved** here. This note replaces Pedregal's failed fixed-point mechanism with an exact convex-duality target that works simultaneously at every dyadic level and every polynomial degree. It also proves an explicit no-go result for a tempting universal heat-flow proof mechanism.

## I. The correct unrestricted target: a closed cone of rank-one splitting defects

Identify the space of real 2×2 matrices with R^4. Fix a closed Euclidean ball K = {A: |A| ≤ R}, and write M(K) for the continuous dual of C(K), with weak-* topology. Define the positive splitting cone

C_K = weak-* closure of cone{ λ δ_B + (1−λ) δ_C − δ_{λ B+(1−λ)C} : B,C∈K, rank(B−C)≤1, 0≤λ≤1 }.

**Lemma (exact bipolar characterization).** For a probability measure ν on K with barycenter F∈K,

  ν − δ_F ∈ C_K

if and only if

  f(F) ≤ ∫ f(A) dν(A)

for every continuous rank-one-convex function f:K→R (convex on every rank-one segment contained in K).

**Proof.** Each continuous rank-one-convex f is nonnegative on the elementary split defects; thus on C_K. Conversely, if ν−δ_F lies outside C_K, Hahn–Banach separation of the weak-* closed convex cone gives a continuous function f on K that is nonnegative on every elementary split defect but negative on ν−δ_F. The first property says precisely that f is rank-one convex on K, and the second contradicts Jensen. QED.

**Global Morrey equivalence.** Let ν_w be the empirical gradient measure of an arbitrary rational periodic piecewise-affine two-component map on a dyadic Kuhn triangulation, with barycenter zero. The following assertions are equivalent:

1. Every finite-valued, globally rank-one-convex integrand on R^(2×2) is quasiconvex.
2. For every dyadic level, every such map w, and every closed ball K with ν_w's support strictly inside K, one has ν_w−δ_0∈C_K.

For 2⇒1, apply the bipolar lemma to the restriction of any globally rank-one-convex integrand, then dyadic density and rational interpolation. For 1⇒2, let f be continuous rank-one convex on K. Contract its argument slightly toward the center of K to define a rank-one-convex function on a neighborhood of K, mollify, and approximate it uniformly on K by a *globally* rank-one-convex polynomial: add ε|A|² to create a strictly positive Legendre–Hadamard margin on a larger ball, approximate in C² by a polynomial, and add a very high-degree positive radial polynomial to dominate its Hessian outside that ball while staying uniformly small on K. Global Morrey applied to the resulting polynomial gives Jensen for ν_w; let approximation error tend to zero. The bipolar lemma gives membership in C_K.

**Hessian interpretation of the same global cone.** Fix a rank-one chord with H=B−C and Z=C+λH. For every C² function f, the elementary Jensen defect has the exact Peano-kernel identity

  λf(B)+(1−λ)f(C)−f(Z) = ∫₀¹ k_λ(s) D²f(C+sH)[H,H] ds,

where k_λ(s)=(1−λ)s for 0≤s≤λ and k_λ(s)=λ(1−s) for λ≤s≤1. The kernel is everywhere nonnegative. Hence any finite positive splitting flow provides a **nonnegative rank-one-Hessian quadrature formula** for the entire Jensen gap, simultaneously for all smooth integrands. Weak-* approximation extends this to limits of split defects. The prior exact 35-term quartic identity from a single dyadic example matches only 35 polynomial moments of this desired all-test-function identity; its positive weights do not establish the global cone membership. This pinpoints the *actual* additional work needed to upgrade a finite-degree certificate into a proof.

This is a *reformulation*, not a new proof. Its advantage is that C_K is an infinite-dimensional **convex cone**, defined without a dyadic mold, nonempty-valued set map, exact finite-order splitting tree, or overdetermined fixed-point equations. The single outstanding proof gate is the uniform inclusion ν_w−δ_0∈C_K, **for all** dyadic maps and levels. One can try to construct the positive splitting flow directly via the geometry of curl-free gradients. This formulation is closely related to the convex-optimization viewpoint of Awi–Šverák (2023) and the classic characterization of laminates by rank-one Jensen inequalities.

## II. A rigorous no-go theorem for a universal heat-flow monotonicity argument

A recent 2026 paper of Bruno and Pasqualotto proves quasiconvexity of the Dacorogna–Marcellini quartic and of all bi-rotationally invariant quartic homogeneous polynomials on 2×2 using monotonicity of energy under componentwise heat flow, plus an exact 2-form correction. **That heat-flow monotonicity cannot be deduced from rank-one convexity in general, not even for strongly rank-one-convex polyconvex integrands.**

On the 2π-periodic torus define

 u(x,y) = −2(cos x + cos y),
 v(x,y) = 5(cos(x+y)+cos(x−y)) + 2(cos(2x)+cos(2y)).

Let (u_t,v_t) = e^(tΔ)(u,v) and let A_t=D(u_t,v_t). Direct differentiation gives

 det A_t = (20e^(−3t) − 16e^(−5t)) sin x sin y (cos y − cos x).

The spatial mean of [sin x sin y (cos y−cos x)]² is 1/8, so

 ⟨(det A_t)²⟩ = (20e^(−3t) − 16e^(−5t))² / 8,

which has derivative **20** at t=0, strictly positive. Thus even f(A)=(det A)² (polyconvex) has an energy that *increases* initially under heat flow.

Moreover, for any η>0 let f_η(A)=(det A)² + η|A|². This f_η is polyconvex and has a uniform rank-one convexity margin:

 D² f_η(A)[a⊗n,a⊗n] = 2(cof(A):(a⊗n))² + 2η|a⊗n|² ≥ 2η|a⊗n|².

Exactly, ⟨|A_t|²⟩ = 4e^(−2t) + 50e^(−4t) + 16e^(−8t), with derivative −336 at t=0. Rescale the map by s>0. Then the derivative of the energy for f_η at zero is

 d/dt|_(t=0) ⟨f_η(sA_t)⟩ = 20s⁴ − 336ηs²,

which is **positive for s² > 84η/5**, regardless of the choice of η>0.

This is an all-energy-class obstruction to the universal heat-flow method, not a finite-grid example or a violation of Morrey. It establishes that global rank-one convexity plus arbitrarily strong uniform Legendre–Hadamard ellipticity is *insufficient to force this particular semigroup monotonicity*. Any heat-flow proof of unrestricted Morrey must include a nontrivial polyconvex correction or a different evolution.

## III. What remains and how to avoid finite-case rabbit holes

- **Established:** Pedregal's nonemptiness requirement is false, so Kakutani's argument cannot be reused as written (per the user's Lean counterexample). Rational-polynomial/dyadic reduction handles negative witnesses. The cone formulation above is an exact positive-side equivalence, not a proof.
- **Established in this session:** A precise and exact heat-flow no-go theorem for *strictly* rank-one-convex polyconvex energies, with a hand calculation and a reproducible symbolic check (`morrey_heatflow_no_go.py`).
- **Open — decisive global gate:** For every periodic dyadic gradient ν and ball K containing its support, construct a sequence of **nonnegative finite combinations of rank-one split defects** converging weak-* to ν−δ_0. This needs neither exact leaf masses nor prescribed mold structures. A positive construction valid for all data would close Morrey in one stroke.
- **Avoid:** Repeating grid-level feasibility searches, trying to make Pedregal's universally nonempty T, or demanding exact finite-order trees for each ν. Those are stronger and typically overconstrained targets.

**Status:** Neither a proof nor a counterexample to unrestricted Morrey has been obtained.
