# Morrey 2×2: Global SOS rigidity at a rank-one zero

**Status (21 November 2026):** Complete hand proof modulo the classical Hilbert theorem for nonnegative ternary quartics. Exact symbolic checks cover the normal-form identities. This result is **not** a proof of unrestricted Morrey and is **not** claimed novel without a full prior-art audit.

## Theorem

Let `P : R^(2×2) -> R` be a real homogeneous quartic polynomial, globally rank-one convex, and suppose `P(B)=0` for some nonzero rank-one matrix `B`. Then there are homogeneous quadratic polynomials `q_1,...,q_4` on the four matrix entries such that

`P(A)=q_1(A)^2+q_2(A)^2+q_3(A)^2+q_4(A)^2` for every A.

Some `q_i` may be zero. Consequently `P(A)>=0` for all matrices, and `P(0)<= ∫ P(Du)` holds for **every** periodic or compactly supported gradient field. No mesh or finite atom bound is assumed.

## Proof, step 1: global nonnegativity, without a polynomial degree bound on the test map

An invertible left-right transformation sends `B` to `E11` while preserving rank-one convexity and SOS status, so set `B=E11`. Homogeneity gives `P(s E11)=0` for all s. For any rank-one H let `h(s,t)=P(s E11 + tH)`. It is separately convex and `h(s,0)=0`.

**Elementary lemma:** If a C^1 function h is separately convex and zero on `t=0`, then `k(s)=∂_t h(s,0)` is affine: for each `t>0`, the function `h(s,t)/t` is convex in s; for each `t<0` it is concave. Both pointwise limits as t→0 equal k. Also by convexity in t, `h(s,t)>=t k(s)`.

For the quartic, `k(s)=s^3k(1)` by homogeneity. The only affine cubic in s is zero, so `h(s,t)>=0`. Every matrix `X=[[a,b],[c,d]]` with d≠0 decomposes exactly as

`X = (a-bc/d) E11 + d H`, `H = [[bc/d^2,b/d],[c/d,1]]`, `rank H=1`.

Thus P(X)≥0, and continuity covers d=0.

## Proof, step 2: a global polynomial normal form

Write P in the entries a,b,c,d. Since `P(a,0,0,0)=0`, the a^4 coefficient vanishes. Since P≥0 for all real a, the coefficient of a³ must vanish as well. Thus

`P(a,b,c,d)=a² Q₂(b,c,d)+a R₃(b,c,d)+S₄(b,c,d)`

with Q₂ a nonnegative quadratic form and S₄ a nonnegative ternary quartic.

The restriction `(a,b)↦P(a,b,0,0)` is convex because differences of matrices supported in the first row have rank at most one. It vanishes on the whole a-axis. A finite convex differentiable function that vanishes on a full line must be invariant under translations parallel to that line: its supporting-hyperplane inequality against arbitrary points on the line forces its directional derivative along the line to vanish everywhere. Therefore `Q₂(b,0,0)=0`. The same argument on the first-column plane gives `Q₂(0,c,0)=0`. Since Q₂ is nonnegative, its associated positive-semidefinite matrix has zero b and c rows and columns. Hence `Q₂(b,c,d)=α d²` for some α≥0.

At d=0 we have `P(a,b,c,0)=a R₃(b,c,0)+S₄(b,c,0)≥0` for every a; therefore `R₃(b,c,0)=0`. Polynomial divisibility gives `R₃=d T₂(b,c,d)`, where T₂ is homogeneous quadratic. We obtain the global normal form

`P(a,b,c,d)= α(ad)^2 + (ad) T₂(b,c,d)+S₄(b,c,d)`.

## Proof, step 3: SOS by Hilbert's ternary-quartic theorem

If α=0, varying a with d≠0 implies T₂≡0; therefore P=S₄(b,c,d), a nonnegative ternary quartic. Hilbert's theorem represents it as a sum of at most three squares of ternary quadratics.

If α>0, complete the square:

`P = α (ad + T₂/(2α))² + R₄(b,c,d)`, where `R₄=S₄−T₂²/(4α)`.

For d≠0, ad runs through all real numbers as a varies, so global nonnegativity of P implies R₄≥0. By continuity R₄≥0 also on d=0. The classical theorem of Hilbert (1888) states that every nonnegative real ternary quartic is the sum of at most three squares of homogeneous quadratic forms. Thus R₄ is a sum of at most three squares. Together with the first square this proves the theorem.

The change of coordinates returning from E11 to the arbitrary rank-one B preserves a representation as sums of squares of homogeneous quadratics.

## What this does and does not establish

- **Closed, globally:** the entire infinite class of homogeneous quartic rank-one convex integrands having a nonzero rank-one zero admits a four-square SOS representation; in particular it is quasiconvex **at zero**.
- **Not closed:** quasiconvexity at arbitrary base matrices for this class; all quartics strictly positive on the nonzero rank-one cone; degree-uniform Morrey.
- **Computer assistance:** `python morrey_rankone_zero_sos.py` checks the normal-form completion algebra and an exact Legendre–Hadamard SOS example. It does not implement a full verifier for Hilbert's theorem.
- **Prior art:** Pfister–Scheiderer, *An elementary proof of Hilbert's theorem on ternary quartics*, J. Algebra 371 (2012), 1–25, DOI 10.1016/j.jalgebra.2012.07.042. It is not known from this search whether the rank-one-zero consequence was previously observed.

## Next global gate

Determine whether rank-one convexity additionally forces the SOS quadratics in this normal form to generate a quasiconvex function **at every base matrix**. This is nontrivial: an SOS homogeneous quartic need not be rank-one convex, and a nonnegative quartic need not be quasiconvex away from zero. For the full Morrey problem, the class of quartics with no rank-one zeros remains, even if this gate is closed.
