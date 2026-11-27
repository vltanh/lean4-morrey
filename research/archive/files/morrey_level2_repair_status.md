# Morrey 2×2: exact level-two obstruction and what is required to repair Pedregal's method

**Status:** A *new restricted obstruction* is proved by the accompanying exact-integer certificate. The original Morrey 2×2 conjecture is **not proved or disproved**. In particular, the certificate does not exclude adaptive nonuniform weights or repeated leaves.

## Theorem 1: A fixed pair rules out the uniform weight vector for every tri-dyadic mold at level two

On the periodic grid with four subdivisions in each direction, let two continuous piecewise-affine, 1-periodic scalar maps `u,v` be defined by nodal values (rows indexed by `a`, columns by `b`, 0..3):

```
u = [[ 70,  28,   2, -46],
     [-39, -92, -85, -97],
     [-65,  63,  30,  83],
     [  1,  21,  95,  46]]

v = [[ 27,   9,  12,  87],
     [-45,  63,  34,-100],
     [-21,  72,  11, -94],
     [ 53,  46,  70, -65]]
```

The squares are split along the diagonal from `(a+1,b)` to `(a,b+1)`. Write `g_u(T)=∇u|_T / 4` and `g_v(T)=∇v|_T / 4` for the integer-scaled gradients.

Each physical interface `e` consists of two adjacent triangles `T_e^+` and `T_e^-`. Define the integer sum

`S_e(u) = g_u(T_e^+) + g_u(T_e^-)`, and similarly `S_e(v)`.

There are exactly `3·4²=48` distinct physical interfaces: 16 diagonal, 16 vertical, and 16 horizontal. The certificate proves, using **exact integer arithmetic**, that for every two distinct interfaces `e≠f`,

`det( S_e(u)-S_f(u), S_e(v)-S_f(v) ) ≠ 0`.

It checks all `48 choose 2 = 1128` cases and records a minimum absolute determinant of 7 (in the integer-scaled convention).

For uniform leaf weights `t₀=1/192` on each of the 192 leaves of a level-two tri-dyadic mold, every first-level mass point is the average of the two triangle gradients at a physical interface. In every sub-mold, the next level of the binary splitting tree merges **two distinct interfaces**. If `t₀∈T_{2,S,u,v}(t₀)`, that merger must have rank-at-most-one direction for the joint two-row gradient. This would make one of the above 1128 determinants zero, a contradiction. Therefore

`∀ S, t₀ ∉ T_{2,S,u,v}(t₀)`.

This is a **mold-independent and fully exact** obstruction at a *specific candidate weight vector*, NOT a statement that `T_{2,S,u,v}` lacks some other fixed point.

### Genericity

Each determinant above is polynomial in the nodal coordinates of `(u,v)`. Because the displayed rational/integer pair makes all of them nonzero, the product is a nonzero polynomial. Consequently the same conclusion holds on a nonempty Zariski-open, Euclidean-open dense set of pairs `(u,v)∈P₂²`.

## Theorem 2: For this pair, no finite-order splitting tree can use each of the 32 atoms exactly once

The 32 triangle-gradient matrices of the displayed pair are all distinct, and each has mass `1/32`. A *single-use* binary lamination tree is one with precisely those 32 leaves, each occurring once with its prescribed mass.

An internal node with two singleton leaves must be a rank-one-connected pair. The certificate checks that the only rank-one-connected pairs among the 32 gradients are the 48 physical interfaces: all 448 non-interface pairs have nonzero determinant, and adjacent atoms are distinct.

Consider the lowest node in any proposed tree containing at least three leaves. Its children each contain one or two leaves. It has either:

* **3 leaves** (an interface pair plus a singleton), or
* **4 leaves** (two disjoint interface pairs).

For all 1440 interface-pair-plus-singleton cases, the determinant between their barycenters is nonzero; for all 1032 disjoint-interface-pair cases, the same is true. The certificate checks these statements exactly, proving that **no such smallest node exists**.

Hence no single-use 32-leaf finite-order laminate tree exists for this pair. The same conclusion holds for a generic pair of level-two maps.

**Limit:** This does not refute Pedregal's Theorem 1.1(1): `H_n` trees may use more than 32 leaves and repeat a triangle-gradient atom with split masses. In particular, the author's tri-dyadic mold repeats triangle occurrences. Such trees are *not* covered by Theorem 2.

## What the false Proposition 7.1 / Corollary 7.2 actually require

The already-formalized exact counterexample to Corollary 7.2 is decisive against the published argument. The present two results reinforce that there is no simple replacement with uniform weights, or with a generic predetermined single-use lamination tree.

A possible valid weaker target is:

> For each l and each pair (u,v) in P_l², its homogeneous periodic gradient measure ν_l is a **weak-* limit of finite-order laminates** with bounded support.

That implication would be sufficient for Morrey, because every continuous rank-one-convex function satisfies Jensen's inequality on each finite-order laminate, and the inequality passes to uniformly supported weak-* limits. However, establishing this weaker target for all `l` is essentially the unresolved original problem; the statement here is a reduction, not its proof.

**Not closed:** Theorem 1.1(1) for `l≥2`; the existence of any fixed point at level two for all pairs and molds; weak-* laminate approximability for all level-two gradient measures; the unrestricted 2×2 Morrey conjecture.

## Reproducibility

Run `python3 morrey_level2_uniform_fixedpoint_obstruction.py`. It uses only the Python standard library, no floating point and no external dependencies. For a full Lean integration, connect the 4×4 nodal arrays with `PL 2`, show the declared 48 edges coincide with `Iface 2`, then prove the 1128 integer determinants nonzero by finite enumeration (e.g. `decide`/`norm_num`).

## Theorem 3: The uniform-weight obstruction holds generically at every dyadic level `l≥2`

Let `n=2^l`. Express an interface-average gradient operator on a **scalar** periodic PL nodal function as a 2-vector of linear functionals. Divide the gradient by `n` and multiply the interface average by 2 to obtain integer stencils (relative to base cell `(a,b)`):

| Type | Relative nodal positions and coefficient 2-vectors |
|---|---|
| Diagonal (`D`) | `(0,0):(-1,-1)`, `(1,0):(1,-1)`, `(0,1):(-1,1)`, `(1,1):(1,1)` |
| Vertical (`V`) | `(0,0):(-1,-2)`, `(1,0):(1,0)`, `(0,1):(1,2)`, `(-1,1):(-1,0)` |
| Horizontal (`H`) | `(0,0):(-2,-1)`, `(1,0):(2,1)`, `(0,1):(0,1)`, `(1,-1):(0,-1)` |

**Lemma.** For every `n=2^l≥4` and distinct physical interfaces `e,f`, the linear map `L_e-L_f : P_l -> R²` has rank 2.

**Proof by bounded exact cases.** Each individual stencil already has rank 2. When supports are disjoint, the difference has rank 2 because it contains all the coefficients of the first stencil. For `n≥8`, if the stencils overlap modulo `n`, their base cell offsets may be represented by `dx,dy∈[-2,2]`. The union's coordinate span is at most 4, hence modulo `n` produces no additional identifications. There are exactly **84** nonidentical type/offset configurations with overlapping support. In all 84, exact coefficient arithmetic gives rank 2. For `n=4`, handle periodic identifications separately: direct exact enumeration gives rank 2 for all **1128** pairs. Both claims are checked in `morrey_all_levels_uniform_obstruction.py`, requiring only the Python standard library.

The determinant `det((L_e-L_f)u,(L_e-L_f)v)` is a **nonzero polynomial** in the scalar nodal values because `L_e-L_f` is onto `R²`. There are finitely many interface pairs. Their determinant product is therefore a nonzero polynomial in the nodal values `(u,v)`. On the nonvanishing Zariski-open set, every two interface midpoint matrices are rank-two separated. Every level-two merger in every tri-dyadic mold joins two *different* interface midpoints; it cannot be rank-one compatible. Hence **for generic `(u,v)` and for every mold `S`, `t_unif∉T_{l,S,u,v}(t_unif)`**.

The argument is valid at **all** dyadic levels `l≥2`. This is a bounded finite-case proof, not an enumeration whose size grows with `l`.

## Theorem 4: An explicit forbidden neighborhood at `l=2`

For the concrete `4×4` nodal pair in Theorem 1, every interface `e` has two triangle-gradient matrices `A_e,B_e` (using gradients divided by 4). Its barycenter at relative first-level weight `alpha_e` is

`M_e(alpha_e) = (A_e+B_e)/2 + (alpha_e-1/2)*(A_e-B_e)`.

Since `A_e-B_e` has rank at most one, `det(M_e(alpha_e)-M_f(alpha_f))` is **separately affine** in the two variables `alpha_e,alpha_f`: the squared terms vanish. Such a bilinear function on a rectangle equals the convex bilinear interpolation of its four corner values.

Choose `delta=1/8192`. The companion exact certificate evaluates all `4×1128=4512` corner determinants at `alpha_e,alpha_f=1/2±delta` and checks each has the same strict sign as the center determinant. Therefore, for **every** assignment of relative first-level weights satisfying

`|alpha_e-1/2| ≤ 1/8192` for each interface occurrence,

the resulting first-level mass points at distinct interfaces are never rank-one connected. Thus **no tri-dyadic mold has a fixed point with first-level relative weights this close to `1/2`** for the displayed pair. This is a mold-independent open neighborhood excluding fixed points, but **weights farther from the center are not excluded**.

## Current completion status

- [x] Formal audit in the user-supplied project refutes the published Proposition 7.1/Corollary 7.2.
- [x] Exact all-level generic obstruction to the uniform-weight replacement (`84` local cases plus `1128` periodic cases).
- [x] Explicit level-two pair and nonuniform forbidden neighborhood (`4512` exact corner checks).
- [x] Exact restricted obstruction to any 32-leaf *single-use* laminate tree for the explicit pair.
- [ ] Establish a fixed point with **adaptive, potentially nonuniform** weights, or replace the mold fixed-point strategy altogether.
- [ ] Prove weak-* laminate approximability (or Jensen's inequality) for **all** `P_l` gradient measures, uniformly in `l`.
- [ ] Complete the density/approximation argument from the discrete statement to full quasiconvexity.

The first two unchecked items are not local technicalities: they encompass the unresolved `2×2` Morrey problem. There is no completed proof to certify or formalize at present.

## Theorem 5: Generic single-use lamination fails at **every** `l≥2`

The restricted single-use obstruction of Theorem 2 extends uniformly to all levels (while still **not** excluding trees with repeated atoms).

Use triangle gradient stencils:

- Lower triangle `L`: `(0,0):(-1,-1)`, `(1,0):(1,0)`, `(0,1):(0,1)`.
- Upper triangle `R`: `(1,1):(1,1)`, `(0,1):(-1,0)`, `(1,0):(0,-1)`.

For `n>=8`, a pair of triangle gradient functionals has rank-one difference identically in scalar nodal data *only* when the triangles share an edge. There are 24 overlapping local relative configurations, and exactly six oriented adjacencies among them. Otherwise the difference has rank 2. Moreover, averaging an interface pair and comparing with a third, nonmember triangle gives a rank-two scalar linear map: 42 local overlapping cases, all full rank. The n=4 torus has the same properties, as checked in 6 adjacency classes and 90 interface-plus-third relative cases. Theorem 3 supplies the remaining four-leaf comparison: two **disjoint** physical interface pairs have average-gradient difference of rank 2.

Thus for generic `(u,v)` no nonadjacent singleton pair is rank-one connected, and no two-leaf interface average can be merged with a third singleton or a distinct two-leaf interface average. Any binary tree on at least three distinct leaves has a *lowest* subtree with three or four leaves. It must be a pair+singleton or pair+pair, neither of which can be rank-one-compatible for the generic input. Hence an equal-mass binary splitting tree using each triangle exactly once is impossible for a generic pair of level-`l` maps, at every `l>=2`.

This does not refute the actual Theorem 1.1(1), whose finite-order trees may repeat the same atom many times with different weights. A solution must use that flexibility, or weaker weak-* limits.

**Complete finite check:** `morrey_all_levels_uniform_obstruction.py` performs all local and exceptional periodic checks, using exact integers. The bound on its case count is independent of `l`.
