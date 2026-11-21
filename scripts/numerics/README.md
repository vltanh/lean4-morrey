# Numerical checks of the report

Python 3 with NumPy, SciPy and SymPy. Run each with `python3 -I <script>` from any directory.
These are floating-point or exact rational computations, not Lean proofs; `REPORT.md` says which
of its claims rest on them.

| Script | What it checks | Report |
| --- | --- | --- |
| `model.py`, `exact.py` | the paper's construction for `l = 1, 2`: `τ_l`, gradients from nodal values, tri-dyadic molds, `Θ_l`, the linear conditions of `𝐓(t)` (floating point and exact) | — |
| `random_instances.py` | `𝐓(t) = ∅` for 40 random `(u, v, t)` and random molds at `l = 1` and `l = 2`; the dimension of `Θ_l` and the number of conditions | E13 |
| `every_mold.py` | for one generic instance at `l = 1`, `𝐓(t) = ∅` for every one of the `315³` triples of sub-mold shapes | E13 |
| `step2.py` | how often one sub-mold alone (the summary of Step 2) is feasible, with and without the start from `𝕌_j` | E14 |
| `fixedpoint_exact.py` | the fixed point of `𝐓` for the counterexample pair, in exact arithmetic | E13 |
