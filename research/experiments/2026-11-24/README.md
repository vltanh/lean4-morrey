# Checks for the integrands `E` and `E₂` (24 Nov 2026)

Target: the isotropic rank-one convex integrand `E` and its blow-up `E₂` at the identity, from
[the flat-region note](../../../docs/research/IWANIEC_MORREY_FLAT_REGION.md). The script uses
NumPy and SciPy only. Floating-point evidence, not a proof.

## Commands

From the repository root:

```sh
python3 research/experiments/2026-11-24/flat_region.py checks
python3 research/experiments/2026-11-24/flat_region.py search 32
```

`checks` takes about a minute. `search` runs 48 local optimizations on a `32 × 32` grid and takes
a few minutes.

## What `checks` samples

- Rank-one convexity of `E` and `E₂`: second differences along 2·10⁵ random rank-one lines.
- Proposition 2: `E ≥ 2|z| − 1 − det X`, and the two closed forms of the difference.
- `E(X) ≥ −det(X − I)`, the pointwise bound of Theorem 7.
- `E < 0` exactly where `|z| + 3|w| < 1`.
- `M ≤ E₂`, the polyconvex minorant at `0`, and `E₂(S) ≥ −det S` on symmetric matrices.
- The blow-up limit `t⁻²E(I + tH) → E₂(H)`.
- Lemma 3 (a): `|z| − |w| < 1` along rank-one lines through matrices of norm below `1`.

Recorded output (seed 0):

```text
min second difference / h^2 of E  along rank-one lines: -1.1368683772161603e-09
min second difference / h^2 of E2 along rank-one lines: 0.0
Proposition 2, min of E - (2|z| - 1 - det X): 4.509281836817536e-12
Proposition 2, formula on S, max error: 3.982925100842749e-14
Proposition 2, formula on U, max error: 3.552713678800501e-14
E(X) >= -det(X - I), min difference: 9.692092410525793e-06
E < 0 exactly on |z| + 3|w| < 1, mismatches: 0
E2 >= M (polyconvex minorant at 0), min difference: -5.684341886080802e-14
E2(S) >= -det S on symmetric S, min difference: 1.73749903353837e-14
blow-up at I, t = 0.01: max |E(I + tH)/t^2 - E2(H)| = 0.06369508086673514
blow-up at I, t = 0.001: max |E(I + tH)/t^2 - E2(H)| = 0.006407024466140054
Lemma 3 (a): max of |z| - |w| on rank-one lines through |X| < 1: 0.9881619066804106
```

The blow-up error decreases linearly in `t`, as the `O(t³)` remainder predicts.

## What `search` does

A periodic map `φ` is given by its values at the nodes of an `N × N` grid on the unit torus and
is affine on the two triangles of each cell. The mean of `F(A₀ + Dφ)` over the torus is then an
exact finite sum, so a negative value of `mean F(A₀ + Dφ) − F(A₀)` would be a test map violating
Jensen's inequality, up to rounding. The script minimizes this mean with L-BFGS-B and analytic
gradients (checked against central differences). The starting maps are:

- every fourth start, a radial compression `−(s + 1)x b(|x|)` of a disc of random radius, with
  `b` a smooth bump, plus a small random field;
- the other starts, smooth random fields with up to 12 Fourier modes per component and random
  amplitude.

Recorded runs (seed 1, `N = 32`):

| Integrand | Base | Starts | Smallest final mean energy |
| --- | --- | --- | --- |
| `E` | `I` | 8 | `4.6·10⁻⁸` |
| `E` | `1.05 I` | 8 | `6.0·10⁻¹⁰` |
| `E` | `1.2 I` | 8 | `0` |
| `E` | `1.6 I` | 8 | `0` |
| `E₂` | `I` | 16 | `0` |

All 48 runs ended at mean energies between `0` and `4.5·10⁻⁴`, and the base value is `0` in each
case. No run found a test map with negative energy. The search is local and nonexhaustive.
