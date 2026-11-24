# Integrands that vanish on an open set: what removing homogeneity or isotropy requires

Produced by Claude (Anthropic), 24 November 2026. Hand proofs and floating-point checks; not
formalized in Lean, not reviewed by a person. Neither generalization of the homogeneous isotropic
theorem is proved here. Whether rank-one convexity implies quasiconvexity on `ℝ^{2×2}` stays open
for isotropic integrands without homogeneity and for homogeneous integrands without isotropy.

The quasiconvexity of the truncated determinant `L` is claimed as Theorem 1 of Agazzi et al.,
[arXiv:2609.28311](https://arxiv.org/abs/2609.28311), and audited with a Lean formalization,
[lean4-iwaniec](https://github.com/vltanh/lean4-iwaniec) (`Agazzi.quasiconvex_integrandL`).
Theorem 6 below uses only the rank-one convexity of the functions it excludes.

## Summary

- The integrand `E` of Section 2 is isotropic, rank-one convex and not homogeneous. It vanishes
  on `U = {|z| − |w| ≥ 1}` and equals `−1/2` at `0`.
- At a matrix `A₀` in the interior of `U`, every quasiconvex function that lies below `E` on a ball
  and touches it at `A₀` vanishes on the interior of `U` in that ball (Corollary 5).
- No function in the class `𝔊` of Section 4 does this (Theorem 6). `𝔊` is built from `L`, its
  generalizations by row projection, convex functions and null Lagrangians. The
  minorants in the proof of the homogeneous isotropic theorem are among these functions, so that
  proof cannot give the quasiconvexity of `E` in the interior of `U`.
- `E` has a polyaffine support at every matrix with `|z| − |w| = 1` (Proposition 2).
- For gradient test maps `φ = ∇η`, Jensen's inequality for `E` holds at every symmetric `A₀ ⪰ I`
  (Theorem 7). The proof uses the contact set of a convex envelope, a mechanism that the functions
  of Theorem 6 do not have.
- The blow-up `E₂` of `E` at `I` is positively 2-homogeneous, rank-one convex and not isotropic
  (Section 6). At `I` it has the same rigidity and is not polyconvex. It is polyconvex at `0`, and
  Jensen's inequality at `I` holds for gradient test maps. If `E` is quasiconvex at the matrices
  `sI` with `s > 1` close to `1`, then `E₂` is quasiconvex at `I`.
- A local finite-element search found no test map with negative energy for `E` or `E₂`
  (Section 7).
- The missing step, without homogeneity and without isotropy alike, is a contact-set argument for
  vector-valued maps (Section 8).

## 1. Notation

Identify `ℝ²` with `ℂ` and write a matrix `X` as `ζ ↦ zζ + wζ̄`. Put

- `x = |z|`, `y = |w|`, `σ = x + y`, `δ = x − y`.

Then `|X| = σ` is the operator norm and `det X = x² − y² = σδ`. The number `δ` is the smaller
singular value with the sign of `det X`. A matrix with coordinates `(α, β)` has rank one if and
only if `|α| = |β| ≠ 0`. Write `B_R = {|X| < R}`. A function is *polyaffine* if it has the form
`κ + ⟨B, X⟩ + c det X`.

Let `f(x, y)` be of class `C²` near a point with `x, y > 0`, and rotate so that `z, w > 0`. Along
the rank-one line `τ ↦ (z + τα, w + τβ)` with `|α| = |β| = 1`, the second derivative of
`f(|z + τα|, |w + τβ|)` at `τ = 0` is

```text
Q(c₁, c₂) = f_xx c₁² + 2 f_xy c₁c₂ + f_yy c₂² + (f_x/x)(1 − c₁²) + (f_y/y)(1 − c₂²),
```

where `c₁ = Re α` and `c₂ = Re β` range independently over `[−1, 1]`. With `c₁ = p + q` and
`c₂ = p − q` the square becomes the diamond `|p| + |q| ≤ 1`, and the Hessian part of `Q` is
`4 f_σσ p² + 8 f_σδ pq + 4 f_δδ q²`.

## 2. The integrand

```text
E(X) = 0                            if |z| − |w| ≥ 1        (region U),
       2|w|² − ½ (1 − |z| − |w|)²   if ||z| − |w|| ≤ 1      (region S),
       2(|w|² − |z|²)               if |w| − |z| ≥ 1        (region V).
```

Equivalent forms:

- on `S`, `E = (1 − δ)(σ − (1 + δ)/2)`;
- on `V`, `E = −2 det X`;
- everywhere, `½ + det X + E(X) = ½ min(δ², 1) + σ max(1, |δ|)`.

The right side of the last identity is affine in `σ` on each line `δ = const`. Up to rotations
these are the rank-one lines `t ↦ diag(t, δ)`, `t ≥ |δ|`.

`E` is negative exactly on `D = {|z| + 3|w| < 1}`, and `D ⊂ B₁`. Indeed, on `S`, `E < 0` means
`2y < |1 − σ|`. If `σ ≥ 1` this says `δ > 1`, which is not in `S`, and if `σ < 1` it says
`x + 3y < 1`. On `V`, `y ≥ x + 1` gives `E ≥ 0`. In particular `E(0) = −1/2` and
`E(sI) = −(1 − s)²/2` for `0 ≤ s ≤ 1`.

**Proposition 1.** `E` is isotropic, continuous and rank-one convex. It is not positively
homogeneous of any degree.

*Proof.* `E` depends only on `|z|` and `|w|`. The formulas agree where `δ = ±1`: both vanish at
`δ = 1`, and both equal `2σ` at `δ = −1`. Since `E(I) = 0` and `E(I/2) = −1/8`, `E` is not
homogeneous. Rank-one convexity follows in three steps.

(a) *Interior points of the regions, with `z, w ≠ 0`.* On `U`, `E = 0`. On `V`, `E = −2 det X` is
affine along rank-one lines. On `S`,

- `f_σσ = 0`, `f_σδ = −1`, `f_δδ = 1`, `f_x = 1 − σ`, `f_y = 4y + 1 − σ`.

Put `g₁ = (1 − σ)/x` and `g₂ = (4y + 1 − σ)/y`. Then

```text
Q = −8pq + 4q² + g₁ (1 − (p + q)²) + g₂ (1 − (p − q)²),     g₁ + g₂ = (σ − δ²)/(xy) ≥ 0,
```

because `σ ≥ |δ| ≥ δ²` on `S`. The coefficient of `p²` is `−(g₁ + g₂) ≤ 0`, so for fixed `q` the
minimum over the diamond is on its boundary. On the edge `c₁ = 1`, with `p ∈ [0, 1]` and
`r = 1 − p`,

```text
Q = 4r((g₂ − 2)p + r) = 4r((1 − δ)p/y + r) ≥ 0.
```

On the edge `c₂ = −1`, with `p' = −p ∈ [0, 1]` and `r = 1 − p'`,

```text
Q = 4r((2 + g₁)p' + r) = 4r((1 + δ)p'/x + r) ≥ 0.
```

The other two edges follow from `Q(−c₁, −c₂) = Q(c₁, c₂)`.

(b) *Points with `z = 0` or `w = 0`.* Such points lie in `S`, or in `V` (if `z = 0`), or in `U`
(if `w = 0`). A point of `S` with `w = 0` has `x ≤ 1`, and there `∂E/∂y = 1 − x ≥ 0`. A point of
`S` with `z = 0` has `y ≤ 1`, and there `∂E/∂x = 1 − y ≥ 0`. So along a rank-one line through such
a point the one-sided derivatives jump upwards. On `V`, `E = 2|w|² − 2|z|²` is smooth.

(c) *The interfaces `δ = ±1`.* On `S`, `∂_σE = 1 − δ` and `∂_δE = δ − σ`; on `U` both vanish; on
`V`, `∂_σE = −2δ` and `∂_δE = −2σ`. So at `δ = 1` and at `δ = −1` the gradient of `E` jumps by
`(σ − 1)∇δ` in the direction of increasing `δ`, and `σ ≥ 1` there. At a transversal crossing the
one-sided derivatives along a rank-one line therefore jump upwards. Where `δ` is not smooth on an
interface, at `(x, y) = (1, 0)` and at `(0, 1)`, the gradient of `E` in `(x, y)` is the same from
both sides, `(0, 0)` and `(0, 4)`, and its component along the vanishing modulus is `0`, so `E`
is differentiable there. Along a rank-one line
`|z|² − |w|²` is affine in `τ`, say `d₀ + d₁τ`. So `|z| = 1 + |w|` becomes
`d₀ − 1 + d₁τ = 2|w(τ)|`, which after squaring is a polynomial equation of degree at most two
in `τ`. The same holds for `|w| = 1 + |z|`. A rank-one line therefore meets each interface in at
most two points, or lies in it on intervals, where the adjacent formulas agree.

The restriction of `E` to a rank-one line is thus continuous and convex on finitely many closed
intervals that cover the line, and its one-sided derivatives do not decrease at their common
endpoints. So it is convex. ∎

**Proposition 2 (supports on the boundary of `U`).** For every `X`,

```text
E(X) ≥ q(X) := 2|z| − 1 − det X,
```

with

- `E − q = ½(1 − δ)²` on `S`;
- `E − q = (δ − 1)(σ − 1)` on `U`;
- `E − q = y² − (x + 1)² + 2 ≥ 2` on `V`.

At every `X₀` with `|z₀| − |w₀| = 1`, the polyaffine function
`ℓ(X) = 2 Re(z z̄₀)/|z₀| − 1 − det X` satisfies `ℓ ≤ q ≤ E` and `ℓ(X₀) = E(X₀) = 0`. So `E` is
polyconvex, hence quasiconvex, at `X₀`. At `X₀ = I`, `ℓ(X) = −det(X − I)`; in particular
`E(X) ≥ −det(X − I)` for every `X`.

*Proof.* The three differences are direct computations. On `U` and on `V` use `x ≥ y + 1` and
`y ≥ x + 1` respectively. Next, `ℓ ≤ q` because `Re(z z̄₀)/|z₀| ≤ |z|`, with equality at `z₀`.
Note `z₀ ≠ 0`, since `|z₀| = 1 + |w₀|`. At `I`, `2 Re z = tr X` and
`det(X − I) = det X − tr X + 1`. ∎

## 3. The shadow of `U` and rigidity

**Lemma 3.**

- (a) If `|X| < 1`, every matrix on a rank-one line through `X` has smaller singular value at most
  `|X|`. In particular no rank-one line through `X` meets `U`.
- (b) If `|X| > 1`, some rank-one line through `X` meets the interior of `U`.

*Proof.* (a) Let `R` have rank one, and let `v` be a unit vector with `Rv = 0`. Then
`(X + tR)v = Xv`, so the smaller singular value of `X + tR` is at most `|Xv| ≤ |X| < 1`. On `U`
it is `δ ≥ 1`. (b) Write `X = Q₁ diag(σ₁, σ₂) Q₂` with `Q₁, Q₂ ∈ SO(2)` and `σ₁ = |X| > 1`. For
large `t`, `Q₁ diag(σ₁, σ₂ + t) Q₂` has positive determinant and both singular values above `1`. ∎

So the set `D`, where `E` is negative, lies in `B₁`, which rank-one lines do not connect to `U`.
This is how `E` can be rank-one convex, vanish on `U` and be negative at `0`.

Fix `A₀` in the interior of `U` and `R > |A₀|`, and put

```text
W = {|z| − |w| > 1} ∩ B_R.
```

`W` is open and connected: it is the image of `SO(2) × {1 < σ₂ ≤ σ₁ < R} × SO(2)` under
`(Q₁, σ, Q₂) ↦ Q₁ diag(σ₁, σ₂) Q₂`.

**Lemma 4 (rigidity).** Let `G` be rank-one convex and `ℓ` polyaffine, with `G ≤ ℓ` on `W` and
`G(X₁) = ℓ(X₁)` for some `X₁ ∈ W`. Then `G = ℓ` on `W`.

*Proof.* `G − ℓ` is rank-one convex, because `ℓ` is affine along rank-one lines. It is continuous,
because a finite rank-one convex function is separately convex in the entries and hence locally
Lipschitz. The set `Z = {X ∈ W : G(X) = ℓ(X)}` is nonempty and relatively closed. It is also open.
Let `X ∈ Z`, and let `ε > 0` be such that the Frobenius ball of radius `3ε` around `X` lies in `W`.
For `|Y − X|_F < ε`, go from `X` to `Y` in four steps along `E₁₁`, `E₁₂`, `E₂₁`, `E₂₂`. Each step
starts at a point `X'` within `ε` of `X`, and the segment from `X' − εE_jk` to `X' + εE_jk`, which
contains the step, lies in `W`. On it `G − ℓ` is convex, nonpositive and zero at the midpoint
`X'`, hence zero. So each step ends in `Z`. Since `W` is connected, `Z = W`. ∎

**Corollary 5.** If `G` is quasiconvex, `G ≤ E` on `B_R` and `G(A₀) = E(A₀)`, then `G = 0` on
`W`. In particular `E` is not polyconvex at `A₀`: a polyaffine support at `A₀` would vanish on
`W`, hence everywhere, while `E(0) < 0`.

A proof of the quasiconvexity of `E` at `A₀` by a touching minorant therefore needs a quasiconvex
function that vanishes on `W` and is at most `E`, so negative on `D`.

## 4. What the known quasiconvex functions cannot do

The touching minorants used so far for isotropic integrands are built from three kinds of blocks.

- (B1) Convex functions on `ℝ^{2×2}`.
- (B2) Polyaffine functions, of either sign.
- (B3) `X ↦ L_{K,Φ,c}(M₁XM₂ + C)` for `M₁, M₂ ∈ GL(2)`, `C ∈ ℝ^{2×2}`, a nonempty compact convex
  `K ⊂ ℝ²`, a convex `C¹` function `Φ` on `ℝ²` and `c ∈ ℝ`. For a matrix `Y` with rows
  `Y¹, Y²`,

  ```text
  C_{K,Φ,c}(Y) = sup_{ζ ∈ ∂K} [ c det(ζ, Y²) + ∇Φ(ζ)·(Y¹ − ζ) ],
  L_{K,Φ,c}(Y) = max(C_{K,Φ,c}(Y), c det Y)   if Y¹ ∈ K,
                 C_{K,Φ,c}(Y)                  otherwise.
  ```

  These are quasiconvex by Theorem C of the
  [row-projection note](IWANIEC_MORREY_NONHOMOG_ROW_PROJECTION.md), a hand proof that extends the
  projection argument of Agazzi et al. The truncated determinant is `L_{K,Φ,1}` with `K` the
  closed unit disc and `Φ = |·|²/2`. Its dilations, rotations, reflections and translations are
  of this form.

Let `𝔊` be the smallest class that contains the blocks and is closed under the following
operations.

- (C1) Nonnegative linear combinations, finite or as integrals `∫ G_θ dμ(θ)`, where
  `θ ↦ G_θ(X)` is measurable and `μ`-integrable for every `X`.
- (C2) Pointwise suprema of families whose supremum is attained at every matrix, for instance
  compact families on which `G_θ(X)` is continuous in `(θ, X)`.
- (C3) Compositions `h ∘ G` with `h : ℝ → ℝ` convex and nondecreasing.

Every member of `𝔊` is quasiconvex if the blocks are, and is rank-one convex. Affine changes of
variables `X ↦ M₁XM₂ + C` pass through (C1)–(C3) to the blocks, so `𝔊` is invariant under them.
`𝔊` contains:

- the kernels `K_r^-(X) = r²L(X/r) − det X` and `K_r^+(X) = r²L(XJ/r) + det X`, `J = diag(1, −1)`, of the
  [affine-shell note](IWANIEC_MORREY_NONHOMOG_SHELL_AFFINE.md), and their integrals over `r`;
- the radial functions `Ψ^e_N` of the
  [homogeneous isotropic paper](https://github.com/vltanh/lean4-morrey/blob/main/docs/HomogeneousIsotropic/README.md)
  (its Proposition 6.8) for convex `N` with `N(0) ≤ 0` and finite `N'(0⁺)`. Writing
  `N(r) = N(0) + N'(0⁺)r + ∫ (r − ρ)₊ dN'(ρ)`, `Ψ^e_N` is a convex function plus a multiple of
  `det` plus `∫ K_ρ^e(X) dN'(ρ)`. This covers the touching minorants `α₀ + Ψ^e_N` in the proof
  of its Theorem A, and the Burkholder functions `B_p` for `p ≥ 2`;
- the Burkholder functions `B_p` for `1 < p < 2`: with `ν = −N_p''` for `N_p(r) = r^{p−1}`,
  `B_p(X) = ∫ ρ²L(X/ρ) dν(ρ)`;
- the shifted truncated determinants `L_r(|z| + a, ||w| − b|)` of the row-projection note,
  suprema over compact orbits of translates;
- every polyconvex function, the supremum of its polyaffine supports.

**Theorem 6.** No `G ∈ 𝔊` satisfies `G ≤ E` on `B_R` and `G(A₀) = E(A₀)`.

*Proof.* Say that a rank-one convex `G` has property (P) if, for every polyaffine `ℓ` with
`G ≤ ℓ` on `W` and `G = ℓ` somewhere on `W`, we have `G ≥ ℓ` on `B₁`. A `G ∈ 𝔊` as in the
theorem has `G ≤ 0` on `W` and `G(A₀) = 0`. Property (P) with `ℓ = 0` would give `G(0) ≥ 0`,
while `G(0) ≤ E(0) = −1/2`. It is therefore enough to show that every member of `𝔊` has (P). In
each case Lemma 4 first gives `G = ℓ` on `W`. Two facts are used repeatedly.

- A polyaffine function that is convex on an open set has no determinant term, because `det` is
  an indefinite quadratic form. A convex function that equals an affine function on an open set
  lies above it everywhere.
- A continuous function that is affine along every rank-one segment of a connected open set is
  polyaffine there. Locally it is affine in each row, so it has the form `α + β·a + γ·b + aᵀNb` in
  the rows `a, b`. Along the rank-one direction with rows `(u₁v, u₂v)` the coefficient of `t²` is
  `u₁u₂ vᵀNv`, so `N` is skew and `aᵀNb = c det(a, b)`. Polyaffine functions that agree on an open
  set coincide.

(B1) `ℓ` is convex on the open set `W`, so it is affine, and `G ≥ ℓ` everywhere.

(B2) `G = ℓ` everywhere.

(B3) Write `ψ(X) = M₁XM₂ + C`, and let `a(X)` be the first row of `ψ(X)`, an affine map onto
`ℝ²`. Three cases.

- `W` contains a point with `a(X) ∉ K`. On the open set `W ∩ {a ∉ K}`, `G = C_{K,Φ,c} ∘ ψ`,
  which is convex and equals `ℓ`. So `ℓ` is affine and `C_{K,Φ,c} ∘ ψ ≥ ℓ` everywhere. Since
  `G ≥ C_{K,Φ,c} ∘ ψ` everywhere, `G ≥ ℓ`.
- `a(W) ⊂ K` and `C_{K,Φ,c} ∘ ψ > c det ∘ ψ` somewhere on `W`. The same argument applies on that
  open set.
- Otherwise `G = c det ∘ ψ` on `W`, so `ℓ = c det ∘ ψ`, and `G ≥ ℓ` wherever `a(X) ∈ K`. It
  remains to show `a(B₁) ⊂ K`. Write `a(X) = vᵀXM₂ + a₀`, where `vᵀ ≠ 0` is the first row of
  `M₁`. For `1 < s < R` and `Q ∈ SO(2)`, `sQ ∈ W` and `a(sQ) = s(vᵀQ)M₂ + a₀`, where `vᵀQ` runs
  over the circle of radius `|v|`. Since `K` is convex, it contains `a₀ + {uM₂ : |u| < R|v|}`. For
  `|X| < 1`, `|vᵀX| < |v|`, so `a(X) ∈ K`.

(C1) Let `G = Σ λ_i G_i` with `λ_i > 0`. On a rank-one segment of `W`,
`λ_i G_i = ℓ − Σ_{j≠i} λ_j G_j` is concave as well as convex. So `G_i` equals a polyaffine `ℓ_i`
on `W`, `Σ λ_i ℓ_i = ℓ`, and (P) for each `G_i` gives `G ≥ ℓ` on `B₁`. For an integral, on each
rank-one segment of `W` the convexity defects
`λG_θ(X') + (1 − λ)G_θ(X'') − G_θ(λX' + (1 − λ)X'')` are nonnegative and integrate to `0`, so
they vanish for almost every `θ`. Taking a countable dense family of segments and rational `λ`,
and using continuity, almost every `G_θ` is affine on every rank-one segment of `W`. Each `ℓ_θ` is
determined by finitely many values `G_θ(X_k)`, `X_k ∈ W`, so its coefficients are integrable and
`∫ ℓ_θ dμ = ℓ`.

(C2) If `G = sup_θ G_θ`, let `θ₁` attain the supremum at a point `X₁ ∈ W` where `G = ℓ`. Then
`G_{θ₁} ≤ ℓ` on `W` and `G_{θ₁}(X₁) = ℓ(X₁)`, so `G ≥ G_{θ₁} ≥ ℓ` on `B₁`.

(C3) Let `G = h ∘ G'`. If `h` is constant there is nothing to prove. Otherwise let
`t* = sup{t : h(t) = min h} ∈ [−∞, ∞)`; `h` is constant on `(−∞, t*]` and strictly increasing on
`[t*, ∞)`. The function `G'' = max(G', t*)` (or `G'` if `t* = −∞`) has (P) by (B2) and (C2), and
`G = h ∘ G''`. On `W`, `G'' = h⁻¹ ∘ ℓ` with `h⁻¹` concave and nondecreasing, so along each
rank-one segment of `W` the convex function `G''` is also concave. Hence `G''` equals a
polyaffine `ℓ''` on `W`, and `h ∘ ℓ'' = ℓ` there.

- If `ℓ''` is a constant `t₀`, (P) for `G''` gives `G'' ≥ t₀` on `B₁`, so `G ≥ h(t₀) = ℓ`.
- Otherwise `h` is affine, `h(t) = κt + β`, on the interval `ℓ''(W)`, because `h ∘ ℓ''` is affine
  along every rank-one segment on which `ℓ''` is not constant. So `ℓ = κℓ'' + β`. On `B₁`,
  `G = h(G'') ≥ h(ℓ'') ≥ κℓ'' + β = ℓ`, by the monotonicity and the convexity of `h`. ∎

Remarks.

- Local uniform limits are not covered. A probability measure with barycenter `A₀` that satisfies
  Jensen's inequality for every block but not for `E` would extend Theorem 6 to limits; none is
  constructed here.
- The [row-projection note](IWANIEC_MORREY_NONHOMOG_ROW_PROJECTION.md), Section 3, excludes for
  the quasiconvex integrand `L₁(|z|, ||w| − 1|)` the minorants that are affine on operator-norm
  spheres. Theorem 6 excludes all of `𝔊` for `E`, an integrand whose quasiconvexity is not known.
- With `V` and `E + 2 det X` in place of `U` and `E`, the same arguments apply at the interior
  points of `V`: on `V` the smaller singular value is also at least `1`, and the matrices `sQJ`,
  `J = diag(1, −1)`, play the role of `sQ`.

## 5. Gradient test maps: a contact-set argument

**Theorem 7.** Let `A₀` be symmetric with `A₀ − I` positive semidefinite. For every
`ℤ²`-periodic `η ∈ C^{1,1}(ℝ²)`,

```text
∫_{(0,1)²} E(A₀ + D²η) dx ≥ 0 = E(A₀).
```

*Proof.*

- *A pointwise bound.* `E(X) ≥ −det(X − I)` for every `X`, by Proposition 2.
- *Where `E` vanishes.* If `X` is symmetric and `X − I ⪰ 0`, then `z = tr X/2` is real,
  `|z| − |w|` is the smaller eigenvalue of `X`, which is at least `1`, and `E(X) = 0`.
- *The total mass.* Let `v(x) = ½ xᵀ(A₀ − I)x + η(x)`, so that `A₀ + D²η = I + D²v`. Expanding
  `det(A₀ − I + D²η)` and using `∫ D²η = 0` and `∫ det D²η = 0` for periodic `η`,
  `∫_{(0,1)²} det D²v = det(A₀ − I)`.
- *The degenerate case.* If `det(A₀ − I) = 0`, the pointwise bound gives
  `∫ E(I + D²v) ≥ −∫ det D²v = 0`.
- *The contact set.* Otherwise `A₀ − I` is positive definite. Let `Γ` be the convex envelope of
  `v` and `C = {v = Γ}`, a closed `ℤ²`-invariant set. For each `p ∈ ℝ²`, `v(x) − p·x` tends to
  `+∞` at infinity, so it attains its minimum at some `x_p ∈ C`, where `∇v(x_p) = p`. Since
  `∇v(x + k) = ∇v(x) + (A₀ − I)k` for `k ∈ ℤ²`, `∇v` maps `C ∩ [0, 1)²` onto `ℝ²` modulo the
  lattice `(A₀ − I)ℤ²`, whose cell has area `det(A₀ − I)`. At the points of `C` where `v` is twice
  differentiable, almost all of them, `D²v ⪰ 0`. The area formula for the Lipschitz map `∇v` gives
  `∫_{C ∩ (0,1)²} det D²v ≥ det(A₀ − I)`.
- *Conclusion.* `E(I + D²v) = 0` almost everywhere on `C`, and off `C` the pointwise bound
  applies:

  ```text
  ∫ E(I + D²v) ≥ −∫_{(0,1)² ∖ C} det D²v = −det(A₀ − I) + ∫_{C ∩ (0,1)²} det D²v ≥ 0.  ∎
  ```

By isotropy the same holds at `Q₁A₀Q₂` for the test maps with gradients `Q₁D²ηQ₂`,
`Q₁, Q₂ ∈ SO(2)`.

The polyaffine function `−det(X − I)` lies below `E` everywhere, but touches it only on the
boundary of `U` (Proposition 2). The contact set supplies what is missing at the interior points.
On it `E` vanishes, and it carries the whole mass `det(A₀ − I)` of `det D²v`. This is a
projection of the scalar potential `v` onto convex functions; Theorem 6 shows that the functions
of `𝔊` cannot replace it.

## 6. The blow-up at the identity: the same question without isotropy

For a matrix `H` with coordinates `(z, w)`, put

```text
E₂(H) = 0                                   if Re z ≥ |w|,
        −½ (Re z)² − (Re z)|w| + (3/2)|w|²   if Re z < |w|.
```

Then `E(I + tH) = t² E₂(H) + O(t³)` as `t → 0⁺`, uniformly for `H` in bounded sets. Indeed
`|1 + tz| = 1 + t Re z + O(t²)` and `δ − 1 = t(Re z − |w|) + O(t²)`. On `S`,
`E = 2t²|w|² − ½t²(Re z + |w|)² + O(t³)`. Near `Re z = |w|` both sides are `O(t³)`.

In terms of the eigenvalues `λ₁ ≤ λ₂` of the symmetric part of `H`, `Re z = (λ₁ + λ₂)/2` and
`|w| = (λ₂ − λ₁)/2`, so

```text
E₂(H) = 0 if λ₁ ≥ 0,     E₂(H) = ½ λ₁² − λ₁λ₂ if λ₁ < 0.
```

**Proposition 8.**

- (a) `E₂` is positively 2-homogeneous and rank-one convex, as a limit of the rank-one convex
  functions `t⁻²E(I + t·)`. It depends only on the symmetric part of `H` and is invariant under
  `H ↦ QHQᵀ`, `Q ∈ O(2)`. It is not isotropic: `E₂(I) = 0`, while `E₂(−I) = −1/2` and `−I` is
  `I` rotated by `π`.
- (b) `E₂` is polyconvex at `0`. The function
  `M(H) = −det H + (Im z)² + ½((Re z − |w|)₋)²` is polyconvex, `M ≤ E₂` with equality where
  `Re z ≤ |w|`, and `M(0) = 0`.
- (c) `E₂` vanishes on the open convex cone `𝒞 = {sym H ≻ 0}`. If `sym H ≺ 0`, no rank-one line
  through `H` meets `{sym H ⪰ 0}`: for `R = a ⊗ b` and `v ⊥ a`,
  `⟨sym(H + tR)v, v⟩ = ⟨(sym H)v, v⟩ < 0`. With `W' = 𝒞 ∩ B_R`, the rigidity of Lemma 4 holds:
  a quasiconvex `G ≤ E₂` on `B_R` that touches at `I` vanishes on `W'`. Since `E₂(−I) < 0`, `E₂`
  is not polyconvex at `I`.
- (d) For gradient test maps, Jensen's inequality holds at every symmetric `A₀ ⪰ 0`:
  `∫ E₂(A₀ + D²η) ≥ 0 = E₂(A₀)` for periodic `η ∈ C^{1,1}`. The proof of Theorem 7 applies with
  `I` replaced by `0`. For symmetric `S`, `E₂(S) + det S` equals `½λ₁²` if `λ₁ < 0` and `det S`
  if `S ⪰ 0`, so `E₂(S) ≥ −det S`, and `E₂ = 0` on the positive semidefinite cone.
- (e) If `E` is quasiconvex at `sI` for all `s` in an interval `(1, 1 + ε)`, then `E₂` is
  quasiconvex at `I`. For a test map `φ`, `(1 + t)I + tDφ = I + t(I + Dφ)`, so
  `∫ E((1 + t)I + tDφ) = t² ∫ E₂(I + Dφ) + O(t³)`.

*Proof of (b).* Where `Re z < |w|`,
`M = −(Re z)² + |w|² + ½(Re z − |w|)² = E₂`. Where `Re z ≥ |w|`, `M = |w|² − (Re z)² ≤ 0 = E₂`.
`M` is polyconvex: `−det H` is a null Lagrangian, `(Im z)²` is convex, and `t ↦ ½(t₋)²` is convex
and nonincreasing, composed with the concave function `Re z − |w|`. ∎

So removing isotropy from the homogeneous theorem meets the same question as removing
homogeneity: `E₂` is positively homogeneous and rank-one convex, quasiconvex at `0`, and its
quasiconvexity at `I` needs a minorant that vanishes on `W'` and is negative near `−I`.

The proof of Theorem 6 does not transfer to `E₂` at `I`. In its third case for (B3), the image
`a(W')` lies in a half-plane, and `a(−I)` need not lie in `K`. Whether `E₂` has a touching
minorant in `𝔊` at `I` is open.

## 7. Numerical checks

The script [`research/experiments/2026-11-24/flat_region.py`](../../research/experiments/2026-11-24/flat_region.py)
has two parts; its [README](../../research/experiments/2026-11-24/README.md) gives the commands
and the recorded output.

- `checks` samples the pointwise statements: rank-one convexity of `E` and `E₂` by second
  differences, Proposition 2, `E ≥ −det(X − I)`, the set where `E < 0`, `M ≤ E₂`,
  `E₂(S) ≥ −det S`, the blow-up limit and Lemma 3 (a). All passed within rounding.
- `search` minimizes the mean of `E(A₀ + Dφ)` over periodic piecewise-affine maps `φ` on a
  `32 × 32` grid with two triangles per cell. For such maps the mean is computed exactly, so a
  negative value would be a test map violating Jensen's inequality, up to rounding. L-BFGS-B
  started from smooth random fields and from radial compressions of a disc.
  - `E` at `sI`, `s ∈ {1, 1.05, 1.2, 1.6}`, 8 starts each.
  - `E₂` at `I`, 16 starts.
  - All 48 runs ended at mean energies between `0` and `4.5·10⁻⁴`.

This is local, nonexhaustive evidence that `E` and `E₂` are quasiconvex at these bases, not a
proof.

## 8. What is missing

- *A contact set for maps.* For `u = A₀x + φ` with `A₀` symmetric and `A₀ − I ≻ 0`, a set
  `C ⊂ (0, 1)²` with `E(Du) ≥ 0` and `det(Du − I) ≥ 0` on `C` and
  `∫_C det(Du − I) ≥ det(A₀ − I)` would give `∫ E(Du) ≥ 0`, exactly as in Theorem 7. By isotropy
  this covers every `A₀` in the interior of `U`. The analogue with `I` replaced by `0` would give
  the quasiconvexity of `E₂` at `I`. The set where `det(Du − I) > 0` does not do: `Du = 0` gives
  `det(Du − I) = 1` and `E(0) = −1/2`. The contact set of Theorem 7 excludes such points because
  there `D²v ⪰ 0`.
- *The projection family at `E₂`.* Whether a member of `𝔊`, for instance a combination of
  generalized truncated determinants, touches `E₂` from below at `I`.
- *Limits.* A measure as in the first remark after Theorem 6, which would show that no local
  uniform limit of members of `𝔊` touches `E` at `A₀`.
