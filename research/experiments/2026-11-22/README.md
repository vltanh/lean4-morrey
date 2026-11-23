# Periodic piecewise-affine gradient witness diagnostic (22 Nov 2026)

Target: the **exact** nonnegative isotropic rank-one-convex p=4
integrand in [the global hybrid no-go](../../../docs/research/IWANIEC_MORREY_HYBRID_NOGO.md).

The separator in that note is **not a gradient Young measure**.
This script seeks an **actual compatible periodic gradient** with
\(J_F(A,u)=\fint_QF(A+Du)-F(A)<0\), which would be a
potential Morrey counterexample and require a separate exact
global rank-one convexity / integral verification (the RC part
already has a rational certificate).

## Parametrization and checks

A periodic n×n nodal map has 2n² real nodal values and is linearly
interpolated over the two triangles per square, with periodic
wraparound. The script evaluates **both actual 2×2 gradient
matrices** (rows are displacement components, columns are
spatial derivative directions) and their **exact PL energy
formula** (average over the 2n² equal-area triangles).
For a random field on each n, it checks
normalized mean gradient zero and mean determinant zero to
machine precision before searching.

Optimization is *local* PyTorch-autograd/SciPy L-BFGS-B,
max 200 iterations, fixed NumPy seed 209,
initial nodal deviations with standard deviations
(0.05,0.2,0.4,0.7,1,2)/n repeated cyclically.
No numerical result is called a certified inequality.

## Recorded searches

- At base \(A=\operatorname{diag}(1,0)\): **25 starts each**
  on n=3,4,6.
- At bases \(A=\operatorname{diag}(1,r)\) for
  r=−0.6,−0.3,0.3,0.6: **9 starts each**
  on n=4,6.

All recorded local runs returned no energy below
their respective affine-base energy. Best gap
relative to the constant perturbation was **0**
to displayed precision. This is negative experimental
evidence only; random initializations, finite
meshes and local solvers are not exhaustive.
No strict negative gradient Jensen gap has been
found for the p=4 candidate.

**Run**:
\`\`\`bash
python research/experiments/2026-11-22/iwaniec_hybrid_pl_search.py
\`\`\`

Dependencies: Python 3, NumPy, SciPy, PyTorch (CPU).
The research code does not establish Lean theorems or
validate any Iwaniec preprint result.

Do not conflate the exact **cone** gap, which is proved,
with this still-**open gradient** gap.
