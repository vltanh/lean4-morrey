# Morrey 2×2 research progress — 2026-11-21

**Status:** Not a solution of Morrey's conjecture. Pedregal's universal nonemptiness assertion is refuted. These files record a rational-polynomial reduction, polynomial degree ≤3 rigidity (previously known), an exactly verified quartic Jensen identity for an explicit nontrivial level-two gradient measure, and a rigorous open-neighborhood extension.

## Main files

- `morrey_polynomial_reduction.md`: mathematical statements, proofs, limits, roadmap, and prior art.
- `morrey_quartic_l2_readme.md`: concise description of the exact positive 35-term Hessian-quadrature identity.
- `morrey_quartic_l2_dual_certificate.json`: exact 35×35 rational dual certificate; 32-atom input data, 35 Hessian evaluations, and strict positive rational weights.
- `morrey_verify_quartic_l2_certificate.py`: **independent exact verifier** using only Python's standard library.
- `morrey_quartic_open_neighborhood.py` and `.json`: independent exact computation certifying a jointly open neighborhood of node arrays and base matrices, radius 2^-21.
- `morrey_cubic_rigidity.py`: exact symbolic check of degree ≤3 rigidity, using SymPy. The mathematical fact is **not novel**.
- `morrey_polynomial_certificate.py`: exact rational SOS Hessian positivity checker and dyadic Jensen calculation, using SymPy.

## Reproduce

Run from this directory:

```sh
python3 morrey_verify_quartic_l2_certificate.py
python3 morrey_quartic_open_neighborhood.py
python3 morrey_cubic_rigidity.py
python3 morrey_polynomial_certificate.py
```

The first checker needs **no external dependencies**. The last two need `sympy`; the neighborhood calculation needs `sympy` for exact inversion.

No `lean` binary was available in the computational environment and no Lean theorem was added to the source repository. The certificate itself is an exact proof of the **stated restricted Jensen inequality**, conditional on the correctness of its small standard-library verifier. It is not an independent Lean proof and does not establish the unrestricted conjecture.
